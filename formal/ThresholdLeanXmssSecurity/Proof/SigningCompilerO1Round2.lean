import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Round1
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Codeword
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealLog
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1BuildOnce

/-! # Round 2 of the O1 coupling

- `realAfter` and `compAfter` are the two handlers of round 2 after the tree step. `real_round2`,
  `round2X_eq` and `comp_round2` split each handler into the guard, the tree step and this rest.
- `record_mid` states that the release record on both sides keeps the relation inside the handler,
  with the record state as the core and the timing state.
- `chains_sync` couples the chain parts of a signer. Each chain records its digit, releases a
  covered chain at a key with `t` signers, and runs the chain part of the signer.
- `tail_sync` couples the chain parts, the release of the key and the release record after a
  successful codeword search. It widens the timing state to the record state first. A failed
  search keeps the timing state without the record, so the widening comes only here.
- `after_sync` couples the rest of round 2 after a successful tree step. It runs the own part of
  the signer and the codeword search.
- `step_round2` is the step contract of round 2.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Round2
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerSyncBackend
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind Queries
-- Port of SigningCompilerO1Slack.withRecord, which this import closure lacks.
/-- The signing state after the release record of signer `i` at key `e`. -/
abbrev withRecord (sig : TsigState C) (e : KeyIndex) (message : Message) (i : C.Party) :
    TsigState C :=
  { sig with released := sig.released ++ [(e, message, i)] }

-- Port of SigningCompilerO1Slack.signersAt_withRecord_subset, which this import closure lacks.
theorem signersAt_withRecord_subset (st : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) (f : KeyIndex) (m : Message) :
    signersAt st f m ⊆ signersAt (withRecord st e message i) f m := by
  intro j hj
  simp only [signersAt, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_append] at hj ⊢
  rcases hj with hj | ⟨r, ⟨hr, hc⟩, rfl⟩
  · exact Or.inl hj
  · exact Or.inr ⟨r, ⟨Or.inl hr, hc⟩, rfl⟩

-- Port of SigningCompilerO1Slack.releasedBound_withRecord, which this import closure lacks.
theorem releasedBound_withRecord (st : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) (h : SigningGuessProof.ReleasedBound st) (hb : st.bound e = some message) :
    SigningGuessProof.ReleasedBound (withRecord st e message i) := by
  intro f m j hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact h f m j hold
  · have ht : (f, m, j) = (e, message, i) := List.mem_singleton.mp hnew
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj ht
    obtain ⟨rfl, _⟩ := Prod.mk.inj hrest
    exact hb

/-- The signer sets read only the corrupt set and the release records. -/
theorem signersAt_congr (st st' : TsigState C) (hcorrupt : st.corrupt = st'.corrupt)
    (hreleased : st.released = st'.released) : signersAt st = signersAt st' := by
  unfold signersAt
  rw [hcorrupt, hreleased]

/-- The signing state after round 2. A successful round adds the release record. -/
def recordOn {α : Type} (sig : TsigState C) (e : KeyIndex) (message : Message) (i : C.Party) :
    Option α → TsigState C
  | none => sig
  | some _ => withRecord sig e message i

/-- The real handler of round 2 after the tree step. -/
def realAfter (dealt : Dealt C (OracleComp (WorldSpec C))) (i : C.Party) (J : C.Quorum)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) (tree : BottomTree) :
    OracleComp (WorldSpec C) (Option (ChainIndex → Option Digest)) := do
  let own ← dealt.part i J (.randomizer bottomLayer e) message
  signRound2With (fun oa => SigningCoreProof.honestLift oa) (fun p => dealt.part i J p message)
    dealt.parameter J (tree.commitment e) e message (Function.update parts i own)

/-- The compiler step of round 2 at one chain point. It records the digit, releases a covered chain
and runs the part of the signer. -/
def chainX (prims : Primitives) (x : Keys3 C) (atThreshold : Bool) (i : C.Party) (J : C.Quorum)
    (message : Message) (p : Point) : SourceMXO1 C Digest := do
  match p with
  | .chain _ key l pos =>
      recordStartX key l pos
      if atThreshold then sourceReleaseCoveredX x.1 x.2.1 key l
  | _ => pure ()
  liftBaseX (sourcePartX prims x i J p message)

/-- The compiler handler of round 2 after the tree step. -/
def compAfter (prims : Primitives) (x : Keys3 C) (st : TsigState C) (i : C.Party) (J : C.Quorum)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) (tree : DeferredBottomTree) :
    SourceMXO1 C (Option (ChainIndex → Option Digest)) := do
  let own ← liftBaseX (sourcePartX prims x i J (.randomizer bottomLayer e) message)
  let some values ← signRound2With (fun oa => liftBaseX (sourceRoProgramX prims x.1 x.2.1 oa))
      (chainX prims x (roundTwoReleased st e message i) i J message)
      x.1 J (tree.commitment e) e message (Function.update parts i own) | pure none
  if roundTwoReleased st e message i then sourceReleaseKeyX x.1 x.2.1 e
  modify fun (s : SourceStateO1 C) => { s with base := { s.base with signing :=
    { s.base.signing with released := s.base.signing.released ++ [(e, message, i)] } } }
  pure (some values)

/-- The compiler tail of round 2 after the chains. It releases the key at `t` signers and appends
the release record. -/
def compTail (x : Keys3 C) (atThreshold : Bool) (e : KeyIndex) (message : Message) (i : C.Party)
    (values : ChainIndex → Option Digest) : SourceMXO1 C (Option (ChainIndex → Option Digest)) :=
  (if atThreshold then sourceReleaseKeyX x.1 x.2.1 e else pure ()) >>= fun _ =>
    modify (fun (s : SourceStateO1 C) => { s with base := { s.base with signing :=
      { s.base.signing with released := s.base.signing.released ++ [(e, message, i)] } } }) >>=
      fun _ => pure (some values)

/-- Round 2 of the compiler is the guard, the tree step and the rest. -/
theorem round2X_eq (prims : Primitives) (x : Keys3 C) (top : TopTree) (i : C.Party)
    (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    sourceTsigO1X prims x top (.round2 i J e message parts) = (do
      let st := (← get).base.signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else do
        let some tree ← liftBaseX (sourceBottomOnceX x.1 x.2.1 top (treeOf e)) | pure none
        compAfter prims x st i J e message parts tree) :=
  rfl

section Round2
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real handler of round 2. A failed guard returns `none`. Else the tree step runs on the
signing state of the handler, and the rest runs at a successful tree. The carried state gets the
signing state at the return. -/
theorem real_round2 (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (a : RealState C) :
    (realOracles prims x s pads u rest top (.inr (.round2 i J e message parts))).run a =
      if i ∈ (realSigning a).corrupt ∨ i ∉ J.1 ∨ (realSigning a).bound e ≠ some message then
        pure (none, a)
      else (simulateQ (realWorld prims x s pads u rest)
          ((bottomOnce (SigningJointEagerProof.dealtOf x top) (treeOf e)).run (realSigning a))).run a
            >>= fun z => match z.1.1 with
        | none => pure (none, withCarried z.2 ((z.1.2, a.1.2.1.2), a.1.2.2))
        | some tree => (fun v => (v.1, withCarried v.2
            ((recordOn z.1.2 e message i v.1, a.1.2.1.2), a.1.2.2))) <$>
          (simulateQ (realWorld prims x s pads u rest)
            (realAfter (SigningJointEagerProof.dealtOf x top) i J e message parts tree)).run z.2 := by
  have ht : ∀ st : TsigState C, (tsigOracles (m := OracleComp (WorldSpec C))
      (fun oa => SigningCoreProof.honestLift oa) (SigningJointEagerProof.dealtOf x top)
        (.round2 i J e message parts)).run st =
      (if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure (none, st) else
        (bottomOnce (SigningJointEagerProof.dealtOf x top) (treeOf e)).run st >>= fun z =>
          match z.1 with
          | none => pure (none, z.2)
          | some tree => (fun v => (v, recordOn z.2 e message i v)) <$>
              realAfter (SigningJointEagerProof.dealtOf x top) i J e message parts tree :
        OracleComp (WorldSpec C) (Option (ChainIndex → Option Digest) × TsigState C)) := by
    intro st
    split_ifs with hg
    · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
      rw [if_pos hg]
      rfl
    · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
      rw [if_neg hg, StateT.run_bind]
      refine bind_congr fun z => ?_
      rcases z with ⟨_ | tree, st'⟩
      · rfl
      · dsimp only
        rw [StateT.run_bind]
        simp only [realAfter, liftM, monadLift, MonadLift.monadLift, StateT.run_lift, bind_assoc,
          pure_bind, map_bind]
        refine bind_congr fun own => ?_
        rw [StateT.run_bind]
        simp only [StateT.run_lift, bind_assoc, pure_bind]
        refine bind_congr fun v => ?_
        rcases v with _ | v <;> rfl
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (realImpl x (gOf s pads u) rest)
    ((rawTraceFlatWith prims x (openingOracles x (SigningJointEagerProof.dealtOf x top))
      (.inr (.round2 i J e message parts))).run a.1)).run a.2 = _
  simp only [rawTraceFlatWith, openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk, ht]
  split_ifs
  · rfl
  · simp only [Functor.map_map, simulateQ_map, StateT.run_map]
    have hfuse : ∀ {ι κ : Type} {spec : OracleSpec ι} {mid : OracleSpec κ} {σ₁ σ₂ α : Type}
        (inner : QueryImpl spec (StateT σ₁ (OracleComp mid))) (outer : QueryImpl mid (StateT σ₂ ProbComp))
        (oa : OracleComp spec α) (s : σ₁) (c : σ₂),
        (simulateQ outer ((simulateQ inner oa).run s)).run c =
          (fun w => ((w.1, w.2.1), w.2.2)) <$>
            (simulateQ (SigningCompilerUntil.fuse inner outer) oa).run (s, c) := by
      intro ι κ spec mid σ₁ σ₂ α inner outer oa s c
      rw [← SigningCompilerUntil.simulateQ_fuse, Functor.map_map]
      exact (id_map _).symm
    rw [hfuse, Functor.map_map, simulateQ_bind, StateT.run_bind, map_bind]
    refine bind_congr fun z => ?_
    rcases z with ⟨⟨_ | tree, st'⟩, a'⟩
    · simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · dsimp only
      simp only [simulateQ_map, StateT.run_map, Functor.map_map]
      rfl

/-- The compiler handler of round 2 sets the mark and runs round 2 on the O1 source state. -/
theorem comp_round2 (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (b : SourceStateO1 C × CompState C) :
    (compOracles prims x q s pads u rest noise top (.inr (.round2 i J e message parts))).run b =
      (fun r => (r.1.1, (r.1.2, r.2))) <$>
        runXO1 (compBackend x q s pads u rest noise)
          (sourceTsigO1X prims x top (.round2 i J e message parts))
          b.1 ((b.2.1.1, b.1.base.hiddenFlag), b.2.2) := by
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> runXO1 (compBackend x q s pads u rest noise)
      (sourceOraclesO1X prims x top (.inr (.round2 i J e message parts))) b.1 b.2 = _
  simp only [sourceOraclesO1X]
  rw [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_get, pure_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1SyncHandlers.runXO1_mark, pure_bind,
    SigningCompilerO1ChainRelease.runXO1_bind]
  simp only [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_modify,
    SigningCompilerO1ChainRelease.runXO1_pure, pure_bind, map_bind, map_pure]
  rw [← bind_pure_comp]
  rfl

/-- A real run keeps the carried state. -/
theorem realWorld_carried {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) :
    r.2.1.2 = a.1.2 := by
  refine SeedHitProof.support_simulateQ_inv (realWorld prims x s pads u rest)
    (fun st : RealState C => st.1.2 = a.1.2) (fun t st hst z hz => ?_) _ a rfl r hr
  rw [← hst]
  change z ∈ support ((_root_.ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) t).run st) at hz
  simp only [_root_.ThresholdLeanXmssSecurity.fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
      rawCarriedLogged, simulateQ_map, simulateQ_bind, StateT.run_map, StateT.run_bind,
      support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hz
  obtain ⟨_, ⟨_, ⟨_, ⟨_, -, rfl⟩, ⟨_, -, rfl⟩⟩, rfl⟩, rfl⟩ := hz
  rfl

/-- The stop of the real side persists over a real run. -/
theorem realWorld_stop {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) :
    RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r hr) _ a h r hr

/-- The release record on both sides moves the core of the relation inside the handler to the
record state. No other clause reads the release records of the source. -/
theorem record_mid (top : TopTree) (sig : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncMid prims x top s pads noise (gOf s pads u) rest sig (withRecord sig e message i) a b) :
    SyncMid prims x top s pads noise (gOf s pads u) rest (withRecord sig e message i)
      (withRecord sig e message i) a
      ({ b.1 with base := { b.1.base with signing := { b.1.base.signing with
        released := b.1.base.signing.released ++ [(e, message, i)] } } }, b.2) := by
  obtain ⟨⟨⟨hf, hc⟩, hcount⟩, hx, htop⟩ := hs
  have hrel :
      b.1.base.signing.released ++ [(e, message, i)] = sig.released ++ [(e, message, i)] := by
    rw [hf.released]
    rfl
  refine ⟨⟨⟨?_, hc⟩, hcount⟩, ?_, ⟨htop.topRows, htop.topRun⟩⟩
  · exact
      { corrupt := hf.corrupt, bound := hf.bound, released := hrel, exposed := hf.exposed
        candidates := hf.candidates, flag := hf.flag, reveal := hf.reveal
        releasedPending := hf.releasedPending
        opening := ⟨hf.opening.actualValue, hf.opening.released⟩
        pendingValid := hf.pendingValid
        allocated := hf.allocated, virtualSeen := hf.virtualSeen, compilerBound := hf.compilerBound
        trace := hf.trace, bad := hf.bad, share := hf.share, restAgree := hf.restAgree
        restFree := hf.restFree, realPrivate := hf.realPrivate, frontier := hf.frontier
        candidatesPaid := hf.candidatesPaid, doneCached := hf.doneCached }
  · exact
      { treeRows := hx.treeRows
        storedTrees := hx.storedTrees
        storedTopDigit := hx.storedTopDigit
        startsTreed := hx.startsTreed
        boundTreeRevealed := hx.boundTreeRevealed
        revealedReleased := hx.revealedReleased
        revealedCovered := hx.revealedCovered
        revealedTop := hx.revealedTop
        candidatesPaid := hx.candidatesPaid
        openingFresh := hx.openingFresh
        staleFree := hx.staleFree
        noEarlyGuess := hx.noEarlyGuess
        guessFree := hx.guessFree
        treeTerms := hx.treeTerms
        treeStarts := hx.treeStarts
        treeValues := hx.treeValues
        baseTraced := hx.baseTraced
        logAgreement := hx.logAgreement
        storedRuns := hx.storedRuns
        startsTraced := hx.startsTraced
        corruptBound := hx.corruptBound
        releasedBound := hx.releasedBound
        prfSeen := hx.prfSeen
        bottomSeen := hx.bottomSeen }

/-- One chain of round 2 on both sides. The compiler records the digit, releases a covered chain
at a key with `t` signers, and runs the chain part of the signer. -/
theorem chain_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sigCore sigTime : TsigState C) (atThreshold : Bool) (i : C.Party) (J : C.Quorum)
    (e : KeyIndex) (message : Message) (l : ChainIndex) (d : Digit) (dtree : DeferredBottomTree)
    (receipt : SigningGuessProof.Round2Receipt C) (hkey : receipt.key = e)
    (hbound : sigTime.bound e = some receipt.message) (henc : receipt.encoding l = d)
    (htime : sigTime.bound = sigCore.bound)
    (hcov : atThreshold = true →
      ∃ m, sigTime.bound e = some m ∧ C.t ≤ (signersAt sigTime e m).card)
    (hd : d.val < chainLength - 1) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top ((sigCore, a.1.2.1.2), a.1.2.2)
      ((sigTime, a.1.2.1.2), a.1.2.2) a b)
    (hmark : b.2.1.2 = false) (ha : ¬RealStop q a)
    (htree : b.1.base.trees (treeOf e) = some (some dtree))
    (hrun : SigningGuessProof.ReceiptRuns prims x top (realLog a) receipt)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
      ((SigningJointEagerProof.dealtOf x top).part i J (.chain bottomLayer e l d) message)).run a))
    (rb : (Digest × SourceStateO1 C) × CompState C)
    (hrb : rb ∈ support (runXO1 (compBackend x q s pads u rest noise)
      (chainX prims x atThreshold i J message (.chain bottomLayer e l d)) b.1 b.2)) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (ra.1 = rb.1.1 ∧
        SyncIn prims x s pads u rest noise top ((sigCore, a.1.2.1.2), a.1.2.2)
          ((sigTime, a.1.2.1.2), a.1.2.2) ra.2 (rb.1.2, rb.2) ∧
        ra.2.1.2 = a.1.2 ∧ rb.2.1.2 = false ∧ rb.1.2.base.signing = b.1.base.signing ∧
        rb.1.2.base.trees = b.1.base.trees ∧ realLog a ≤ realLog ra.2) := by
  obtain ⟨hmid, hpads⟩ := syncMid_of_syncIn prims x s pads u rest noise top sigCore sigTime a b hs
  have hrec := SigningCompilerO1ChainRelease.recordStart_mid prims x s pads u rest noise top sigCore
    sigTime e l d a b hmid ⟨dtree, htree⟩ ⟨receipt, hkey, hbound, henc, hrun⟩
  simp only [chainX, SigningCompilerO1ChainRelease.runXO1_bind, recordStartX,
    SigningCompilerO1ChainRelease.runXO1_modify, pure_bind] at hrb
  have hpre : ∃ bm : SourceStateO1 C × CompState C,
      (Stop bm.2 ∨ (SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a bm ∧
        bm.2.1.2 = false ∧ bm.1.base.signing = b.1.base.signing ∧
        bm.1.base.trees = b.1.base.trees)) ∧ PadsFixed x pads bm.2 ∧
      rb ∈ support (runXO1 (compBackend x q s pads u rest noise)
        (liftBaseX (sourcePartX prims x i J (.chain bottomLayer e l d) message)) bm.1 bm.2) := by
    cases atThreshold
    · exact ⟨(_, b.2), Or.inr ⟨hrec, hmark, rfl, rfl⟩, hpads, by simpa using hrb⟩
    · rw [if_pos rfl, SigningCompilerO1ChainRelease.runXO1_bind, mem_support_bind_iff] at hrb
      obtain ⟨mid, hmid', hrb⟩ := hrb
      refine ⟨(mid.1.2, mid.2), ?_, backend_padsFixed x q s pads u rest noise _ b.2 hpads mid hmid',
        hrb⟩
      rcases SigningCompilerO1ChainRelease.releaseCovered_mid prims x q s pads u rest noise hkeys top
          sigCore sigTime e l a _ hrec hmark (hcov rfl) mid hmid' with h | ⟨h1, -, h3, h4, h5⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h5, h3, h4⟩
  obtain ⟨bm, hbm | ⟨hsm, hmm, hsgm, htrm⟩, hpm, hrb⟩ := hpre
  · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ bm.1
      bm.2 hbm rb hrb))
  by_cases hbm : Stop bm.2
  · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ bm.1
      bm.2 hbm rb hrb))
  have hin := syncIn_of_syncMid prims x s pads u rest noise top sigCore sigTime a bm hsm hpm
  rw [runXO1_liftBaseX, support_map] at hrb
  obtain ⟨r, hr, rfl⟩ := hrb
  have hrows : ∀ d' : XmssSecurity.ChainStep, (dataOf x bm.2).pending (.bottom e l d') ≠ none := by
    intro d'
    have h0 := (hin.2.1.rest.treeRows (treeOf e) (by rw [htrm, htree]; exact Option.some_ne_none _)
      ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ l d').2
    rwa [bottomKey_treeOf] at h0
  rcases SigningCompilerO1Part.part_sync prims x q s pads u rest noise hkeys top _ _ i J e l d message
      a bm hin htime hd hrows ha hbm hmm ra hra r hr with h | h | ⟨⟨hv, -⟩, hsync, hsg, htr, -, -, hm,
        hcar, hlog⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hv, hsync, hcar, hm, hsg.trans hsgm, htr.trans htrm, hlog⟩)

/-- The chains of round 2 on both sides, in order. -/
theorem chains_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sigCore sigTime : TsigState C) (c : Carried C) (atThreshold : Bool) (i : C.Party)
    (J : C.Quorum) (e : KeyIndex) (message : Message) (encoding : Encoding)
    (dtree : DeferredBottomTree) (receipt : SigningGuessProof.Round2Receipt C)
    (hkey : receipt.key = e) (hbound : sigTime.bound e = some receipt.message)
    (henc : receipt.encoding = encoding) (htime : sigTime.bound = sigCore.bound)
    (hcov : atThreshold = true →
      ∃ m, sigTime.bound e = some m ∧ C.t ≤ (signersAt sigTime e m).card)
    (n : ℕ) (g : Fin n → ChainIndex) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top ((sigCore, c.1.2), c.2) ((sigTime, c.1.2), c.2) a b)
    (hcar : a.1.2 = c) (hmark : b.2.1.2 = false) (ha : ¬RealStop q a) (hb : ¬Stop b.2)
    (htree : b.1.base.trees (treeOf e) = some (some dtree))
    (hrun : SigningGuessProof.ReceiptRuns prims x top (realLog a) receipt)
    (ra : (Fin n → Option Digest) × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
      (Concrete.sequenceFin fun j => if (encoding (g j)).val < chainLength - 1 then
        some <$> (SigningJointEagerProof.dealtOf x top).part i J
          (.chain bottomLayer e (g j) (encoding (g j))) message
      else pure none)).run a))
    (rb : ((Fin n → Option Digest) × SourceStateO1 C) × CompState C)
    (hrb : rb ∈ support (runXO1 (compBackend x q s pads u rest noise)
      (Concrete.sequenceFin fun j => if (encoding (g j)).val < chainLength - 1 then
        some <$> chainX prims x atThreshold i J message (.chain bottomLayer e (g j) (encoding (g j)))
      else pure none) b.1 b.2)) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (ra.1 = rb.1.1 ∧
        SyncIn prims x s pads u rest noise top ((sigCore, c.1.2), c.2) ((sigTime, c.1.2), c.2) ra.2
          (rb.1.2, rb.2) ∧
        ra.2.1.2 = c ∧ rb.2.1.2 = false ∧ rb.1.2.base.signing = b.1.base.signing ∧
        rb.1.2.base.trees = b.1.base.trees ∧ realLog a ≤ realLog ra.2) := by
  induction n generalizing a b with
  | zero =>
    simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra
    simp only [Concrete.sequenceFin, SigningCompilerO1ChainRelease.runXO1_pure,
      mem_support_pure_iff] at hrb
    subst hra hrb
    exact Or.inr (Or.inr ⟨funext fun j => j.elim0, hs, hcar, hmark, rfl, rfl, le_rfl⟩)
  | succ n ih =>
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hra
    simp only [Concrete.sequenceFin, SigningCompilerO1ChainRelease.runXO1_bind,
      SigningCompilerO1ChainRelease.runXO1_pure, mem_support_bind_iff, mem_support_pure_iff] at hrb
    obtain ⟨ra1, hra1, ra2, hra2, rfl⟩ := hra
    obtain ⟨rb1, hrb1, rb2, hrb2, rfl⟩ := hrb
    subst hcar
    have hhead : RealStop q ra1.2 ∨ Stop rb1.2 ∨
        (ra1.1 = rb1.1.1 ∧
          SyncIn prims x s pads u rest noise top ((sigCore, a.1.2.1.2), a.1.2.2)
            ((sigTime, a.1.2.1.2), a.1.2.2) ra1.2 (rb1.1.2, rb1.2) ∧
          ra1.2.1.2 = a.1.2 ∧ rb1.2.1.2 = false ∧ rb1.1.2.base.signing = b.1.base.signing ∧
          rb1.1.2.base.trees = b.1.base.trees ∧ realLog a ≤ realLog ra1.2) := by
      by_cases hd : (encoding (g 0)).val < chainLength - 1
      · rw [if_pos hd, simulateQ_map, StateT.run_map, support_map] at hra1
        rw [if_pos hd, map_eq_bind_pure_comp, SigningCompilerO1ChainRelease.runXO1_bind,
          mem_support_bind_iff] at hrb1
        obtain ⟨w, hw, rfl⟩ := hra1
        obtain ⟨r, hr, hrb1⟩ := hrb1
        rw [Function.comp_apply, SigningCompilerO1ChainRelease.runXO1_pure,
          mem_support_pure_iff] at hrb1
        subst hrb1
        rcases chain_sync prims x q s pads u rest noise hkeys top sigCore sigTime atThreshold i J e
            message (g 0) (encoding (g 0)) dtree receipt hkey hbound (by rw [henc]) htime hcov hd a b
            hs hmark ha htree hrun w hw r hr with h | h | ⟨hv, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨congrArg some hv, h⟩)
      · rw [if_neg hd, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra1
        rw [if_neg hd, SigningCompilerO1ChainRelease.runXO1_pure, mem_support_pure_iff] at hrb1
        subst hra1 hrb1
        exact Or.inr (Or.inr ⟨rfl, hs, rfl, hmark, rfl, rfl, le_rfl⟩)
    rcases hhead with h | h | ⟨hv1, hs1, hcar1, hm1, hsg1, htr1, hlog1⟩
    · exact Or.inl (realWorld_stop prims x q s pads u rest _ _ h ra2 hra2)
    · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ h
        rb2 hrb2))
    by_cases ha1 : RealStop q ra1.2
    · exact Or.inl (realWorld_stop prims x q s pads u rest _ _ ha1 ra2 hra2)
    by_cases hb1 : Stop rb1.2
    · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
        hb1 rb2 hrb2))
    rcases ih (fun j => g j.succ) ra1.2 (rb1.1.2, rb1.2) hs1 hcar1 hm1 ha1 hb1 (htr1 ▸ htree)
        (SigningGuessProof.ReceiptRuns.mono prims x top hlog1 receipt hrun) ra2 hra2 rb2 hrb2
      with h | h | ⟨hv2, hs2, hcar2, hm2, hsg2, htr2, hlog2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨?_, hs2, hcar2, hm2, hsg2.trans hsg1, htr2.trans htr1,
      hlog1.trans hlog2⟩)
    funext j
    cases j using Fin.cases with
    | zero => exact hv1
    | succ j => exact congrFun hv2 j

/-- The tail of round 2 after a successful codeword search, on both sides. The chains run with the
timing state widened to the record state. Then the compiler releases the key at `t` signers, and
both sides append the release record. -/
theorem tail_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sig st0 : TsigState C) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (dtree : DeferredBottomTree) (ρ : Digest) (randomness : Randomness) (encoding : Encoding)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top ((sig, a.1.2.1.2), a.1.2.2)
      ((sig, a.1.2.1.2), a.1.2.2) a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (htree : b.1.base.trees (treeOf e) = some (some dtree))
    (hbound : sig.bound e = some message) (hcorrupt : st0.corrupt = sig.corrupt)
    (hreleased : st0.released = sig.released)
    (hres : DeterministicSigning.Resolves (realLog a)
      (SigningCompilerO1RealLog.codewordForest x.1 (dtree.commitment e) e message ρ)
      (some (randomness, encoding)))
    (ra : (ChainIndex → Option Digest) × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
      (Concrete.sequenceFin fun l => if (encoding l).val < chainLength - 1 then
        some <$> (SigningJointEagerProof.dealtOf x top).part i J
          (.chain bottomLayer e l (encoding l)) message
      else pure none)).run a))
    (rb1 : ((ChainIndex → Option Digest) × SourceStateO1 C) × CompState C)
    (hrb1 : rb1 ∈ support (runXO1 (compBackend x q s pads u rest noise)
      (Concrete.sequenceFin fun l => if (encoding l).val < chainLength - 1 then
        some <$> chainX prims x (roundTwoReleased st0 e message i) i J message
          (.chain bottomLayer e l (encoding l))
      else pure none) b.1 b.2))
    (rb : (Option (ChainIndex → Option Digest) × SourceStateO1 C) × CompState C)
    (hrb : rb ∈ support (runXO1 (compBackend x q s pads u rest noise)
      (compTail x (roundTwoReleased st0 e message i) e message i rb1.1.1) rb1.1.2 rb1.2)) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (some ra.1 = rb.1.1 ∧
        SyncO1 prims x top s pads noise (gOf s pads u) rest
          (withCarried ra.2 ((withRecord sig e message i, a.1.2.1.2), a.1.2.2)) (rb.1.2, rb.2) ∧
        PadsFixed x pads rb.2) := by
  obtain ⟨hmid, hpads⟩ := syncMid_of_syncIn prims x s pads u rest noise top sig sig a b hs
  have hst : sig.trees (treeOf e) = some (some (interpretTree s (treeOf e) dtree)) := by
    have h := hmid.2.1.storedTrees (treeOf e)
    rw [htree] at h
    exact h
  let receipt : SigningGuessProof.Round2Receipt C :=
    { party := i, quorum := J, key := e, message := message, randomness := randomness,
      encoding := encoding, candidate := ρ, commitment := dtree.commitment e,
      values := fun _ => none }
  have hrun : SigningGuessProof.ReceiptRuns prims x top (realLog a) receipt := by
    obtain ⟨start, result, hsupp, hout, hle⟩ := hmid.2.1.storedRuns (treeOf e) _ hst
    obtain ⟨m, hm⟩ := SigningCompilerO1RealLog.resolves_countRun prims _ (realLog a) _ hres 0
    rw [SigningCompilerO1RealLog.hashEmbed_codewordForest] at hm
    exact ⟨_, start, result, (realLog a, 0), (some (randomness, encoding), (realLog a, m)), hsupp,
      hout, hle, rfl, hm, rfl, le_rfl⟩
  have hwide := SigningCompilerO1ChainRelease.syncMid_widen prims x s pads u rest noise top sig sig
    (withRecord sig e message i) a b hmid rfl rfl rfl
    (fun f m => signersAt_withRecord_subset sig e message i f m)
    (releasedBound_withRecord sig e message i hmid.2.1.releasedBound hbound)
  have hin := syncIn_of_syncMid prims x s pads u rest noise top sig (withRecord sig e message i) a b
    hwide hpads
  have hcov : roundTwoReleased st0 e message i = true → ∃ m, (withRecord sig e message i).bound e =
      some m ∧ C.t ≤ (signersAt (withRecord sig e message i) e m).card := by
    intro h
    refine ⟨message, hbound, ?_⟩
    have h' := of_decide_eq_true h
    rwa [signersAt_congr { st0 with released := st0.released ++ [(e, message, i)] }
      (withRecord sig e message i) hcorrupt (by simp only [hreleased])] at h'
  rcases chains_sync prims x q s pads u rest noise hkeys top sig (withRecord sig e message i) a.1.2
      (roundTwoReleased st0 e message i) i J e message encoding dtree receipt rfl hbound rfl rfl hcov
      _ (fun l => l) a b hin rfl hmark ha hb htree hrun ra hra rb1 hrb1
    with h | h | ⟨hv, hs1, hcar1, hm1, hsg1, htr1, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ h
      rb hrb))
  rw [← hcar1] at hs1
  obtain ⟨hmid1, hpads1⟩ := syncMid_of_syncIn prims x s pads u rest noise top sig
    (withRecord sig e message i) ra.2 (rb1.1.2, rb1.2) hs1
  unfold compTail at hrb
  rw [SigningCompilerO1ChainRelease.runXO1_bind, mem_support_bind_iff] at hrb
  obtain ⟨bm, hbm, hrb⟩ := hrb
  have hpre : (Stop bm.2 ∨ (SyncMid prims x top s pads noise (gOf s pads u) rest sig
      (withRecord sig e message i) ra.2 (bm.1.2, bm.2) ∧ bm.2.1.2 = false)) ∧
      PadsFixed x pads bm.2 := by
    refine ⟨?_, backend_padsFixed x q s pads u rest noise _ rb1.2 hpads1 bm hbm⟩
    cases hT : roundTwoReleased st0 e message i
    · rw [hT, if_neg (by decide), SigningCompilerO1ChainRelease.runXO1_pure,
        mem_support_pure_iff] at hbm
      subst hbm
      exact Or.inr ⟨hmid1, hm1⟩
    · rw [hT, if_pos rfl] at hbm
      rcases SigningCompilerO1ChainRelease.releaseKey_mid prims x q s pads u rest noise hkeys top sig
          (withRecord sig e message i) e ra.2 _ hmid1 hm1 (hcov hT) bm hbm with h | ⟨h, -, -, -, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hm⟩
  obtain ⟨hbm' | ⟨hmidm, hmm⟩, hpm⟩ := hpre
  · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
      hbm' rb hrb))
  rw [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_modify,
    pure_bind, SigningCompilerO1ChainRelease.runXO1_pure, mem_support_pure_iff] at hrb
  subst hrb
  have hrec := record_mid prims x s pads u rest noise top sig e message i ra.2 (bm.1.2, bm.2) hmidm
  have hfin := syncIn_of_syncMid prims x s pads u rest noise top (withRecord sig e message i)
    (withRecord sig e message i) ra.2 _ hrec hpm
  rw [hcar1] at hfin
  refine Or.inr (Or.inr ⟨congrArg some hv,
    (syncO1_iff_syncIn prims x s pads u rest noise top _ _).2 ?_⟩)
  dsimp only at hfin ⊢
  obtain ⟨hcore, hx, htop, hp⟩ := hfin
  exact ⟨hcore, hx, ⟨htop.topRows, htop.topRun⟩, hp⟩

/-- The rest of round 2 after a successful tree step, on both sides. The real side returns the real
state of the run. The relation at the return has the signing state with the release record after a
successful round. -/
theorem after_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sig st0 : TsigState C) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (dtree : DeferredBottomTree) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top ((sig, a.1.2.1.2), a.1.2.2)
      ((sig, a.1.2.1.2), a.1.2.2) a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (htree : b.1.base.trees (treeOf e) = some (some dtree))
    (hbound : sig.bound e = some message) (hreal : (realSigning a).bound = sig.bound)
    (hsig : st0 = b.1.base.signing) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        (realAfter (SigningJointEagerProof.dealtOf x top) i J e message parts
          (interpretTree s (treeOf e) dtree))).run a)
      (runXO1 (compBackend x q s pads u rest noise)
        (compAfter prims x st0 i J e message parts dtree) b.1 b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧
          SyncO1 prims x top s pads noise (gOf s pads u) rest
            (withCarried ra.2 ((recordOn sig e message i ra.1, a.1.2.1.2), a.1.2.2)) (rb.1.2, rb.2) ∧
          PadsFixed x pads rb.2)) := by
  simp only [realAfter, compAfter, simulateQ_bind, StateT.run_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, runXO1_liftBaseX, bind_map_left]
  have hpart : (SigningJointEagerProof.dealtOf x top).part i J (.randomizer bottomLayer e) message =
      SigningSecurityProof.liftFree (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J
        (.randomizer bottomLayer e) message) := rfl
  rw [hpart]
  refine relTriple_bind (R := fun (p : Digest × RealState C)
      (w : (Digest × SourceState C) × CompState C) =>
    InPost prims x q s pads u rest noise top ((sig, a.1.2.1.2), a.1.2.2) ((sig, a.1.2.1.2), a.1.2.2)
      a b (fun rb => rb.1.2.revealed) (fun va vb => va = vb) p w) ?_ ?_
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro p hp w hw
    exact SigningCompilerO1Part.part_frame prims x q s pads u rest noise hkeys top _ _ i J
      (.randomizer bottomLayer e) message a b hs rfl (constrained_bottom_randomizer e)
      (fun _ _ _ h => by cases h) ha hb hmark p (by with_reducible exact hp) w hw
  intro p w hpw
  rcases hpw with h | h | ⟨hv, hsync, hsg, htr, -, -, hm, hcar, -⟩
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    exact Or.inl (realWorld_stop prims x q s pads u rest _ p.2 h ra (by with_reducible exact hra))
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    rw [mem_support_bind_iff] at hrb
    obtain ⟨r1, hr1, hrb⟩ := hrb
    exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
      (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ h r1 hr1) rb hrb))
  rw [hv]
  simp only [signRound2With, simulateQ_bind, StateT.run_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, runXO1_liftBaseX, bind_map_left, bind_assoc]
  by_cases ha1 : RealStop q p.2
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    rw [mem_support_bind_iff] at hra
    obtain ⟨r1, hr1, hra⟩ := hra
    exact Or.inl (realWorld_stop prims x q s pads u rest _ _
      (realWorld_stop prims x q s pads u rest _ p.2 ha1 r1 (by with_reducible exact hr1)) ra
      (by with_reducible exact hra))
  by_cases hb1 : Stop w.2
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    rw [mem_support_bind_iff] at hrb
    obtain ⟨r1, hr1, hrb⟩ := hrb
    rw [mem_support_bind_iff] at hrb
    obtain ⟨r2, hr2, hrb⟩ := hrb
    exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
      (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
        (SigningCompilerO1Programs.runX_compStop x q s pads u rest noise _ w.1.2 w.2 hb1 r1
          (by with_reducible exact hr1)) r2 hr2)
      rb hrb))
  have hcoreBound : b.1.base.signing.bound = sig.bound := hs.1.1.1.bound
  have hopen : w.1.2.revealed (.opening bottomLayer e) ≠ none :=
    hsync.2.1.rest.boundTreeRevealed e (by
      change w.1.2.signing.bound e ≠ none
      rw [hsg, hcoreBound, hbound]
      exact Option.some_ne_none _) (by
      change w.1.2.trees (treeOf e) ≠ none
      rw [htr, htree]
      exact Option.some_ne_none _)
  refine relTriple_bind (SigningCompilerO1Codeword.codeword_sync prims x q s pads u rest noise hkeys
    top w.1.2.revealed
    ((sig, a.1.2.1.2), a.1.2.2) ((sig, a.1.2.1.2), a.1.2.2) (dtree.commitment e) e message
    (combine J (Function.update parts i w.1.1)) p.2 ({ base := w.1.2, starts := b.1.starts }, w.2)
    hsync (by rw [hcar]; exact hreal) rfl hbound hopen ha1 hb1 hm) ?_
  intro c d hcd
  apply TreeCheckKernelCoupling.relTriple_of_support
  intro ra hra rb hrb
  rw [mem_support_bind_iff] at hrb
  obtain ⟨r, hr, hrb⟩ := hrb
  rcases hcd with h | h | ⟨⟨hv2, hbase, hres⟩, hsync2, -, -, -, -, hm2, hcar2, -⟩
  · exact Or.inl (realWorld_stop prims x q s pads u rest _ c.2 h ra (by with_reducible exact hra))
  · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
      (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ h r hr) rb hrb))
  rcases c with ⟨_ | ⟨rnd, enc⟩, a2⟩ <;> rcases d with ⟨⟨v, src2⟩, st2⟩ <;>
    dsimp only at hv2 hbase hres hsync2 hm2 hcar2 hra hr <;> subst hv2 hbase
  · rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra
    rw [SigningCompilerO1ChainRelease.runXO1_pure, mem_support_pure_iff] at hr
    subst hra hr
    rw [SigningCompilerO1ChainRelease.runXO1_pure, mem_support_pure_iff] at hrb
    subst hrb
    refine Or.inr (Or.inr ⟨rfl, (syncO1_iff_syncIn prims x s pads u rest noise top _ _).2 ?_⟩)
    dsimp only at hsync2 ⊢
    obtain ⟨hcore, hx, htop, hp⟩ := hsync2
    exact ⟨hcore, hx, ⟨htop.topRows, htop.topRun⟩, hp⟩
  · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hra
    obtain ⟨rv, hrv, hra⟩ := hra
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra
    subst hra
    dsimp only at hr
    rw [SigningCompilerO1ChainRelease.runXO1_bind, mem_support_bind_iff] at hr
    obtain ⟨rb1, hrb1, hr⟩ := hr
    rw [SigningCompilerO1ChainRelease.runXO1_pure, mem_support_pure_iff] at hr
    subst hr
    have hrb' : rb ∈ support (runXO1 (compBackend x q s pads u rest noise)
        (compTail x (roundTwoReleased st0 e message i) e message i rb1.1.1) rb1.1.2 rb1.2) := by
      revert hrb
      cases roundTwoReleased st0 e message i <;> intro hrb <;>
        simpa only [compTail, Bool.false_eq_true, if_false, if_true, pure_bind] using hrb
    have hcar' : a2.1.2 = a.1.2 := hcar2.trans hcar
    by_cases ha2 : RealStop q a2
    · exact Or.inl (realWorld_stop prims x q s pads u rest _ a2 ha2 rv (by with_reducible exact hrv))
    by_cases hb2 : Stop st2
    · exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
        (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ hb2 rb1 hrb1) rb
        hrb'))
    rw [← hcar'] at hsync2 ⊢
    have hcor : st0.corrupt = sig.corrupt := by rw [hsig]; exact hs.1.1.1.corrupt
    have hrel : st0.released = sig.released := by rw [hsig]; exact hs.1.1.1.released
    exact tail_sync prims x q s pads u rest noise hkeys top sig st0 i J e message dtree
      (combine J (Function.update parts i w.1.1)) rnd enc a2
      ({ base := w.1.2, starts := b.1.starts }, st2)
      hsync2 ha2 hb2 hm2 (by rw [htr]; exact htree) hbound hcor hrel hres rv hrv rb1 hrb1 rb hrb'

/-- A stop of a real run stays when the carried state of the handler replaces its carried state. -/
theorem realStop_withCarried (a : RealState C) (c : Carried C) (hc : c.1.2 = a.1.2.1.2)
    (h : RealStop q a) : RealStop q (withCarried a c) := by
  unfold RealStop at h ⊢
  rw [← hc] at h
  exact h

/-- Round 2, with the tree step, the recorded digits and the guarded release. -/
theorem step_round2 (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    StepO1' prims x q s pads u rest noise top (.inr (.round2 i J e message parts)) := by
  intro a b hs ha hb
  have hflag : b.1.base.hiddenFlag = false := by
    have h1 : b.1.base.hiddenFlag = realFlag a := hs.1.1.1.1.1.flag
    have h2 : realFlag a = false := by
      unfold RealStop at ha
      simpa using (not_or.mp ha).1
    rw [h1, h2]
  have hcorr : b.1.base.signing.corrupt = (realSigning a).corrupt := hs.1.1.1.1.1.corrupt
  have hbound : b.1.base.signing.bound = (realSigning a).bound := hs.1.1.1.1.1.bound
  have hguard : (i ∈ b.1.base.signing.corrupt ∨ i ∉ J.1 ∨ b.1.base.signing.bound e ≠ some message) ↔
      (i ∈ (realSigning a).corrupt ∨ i ∉ J.1 ∨ (realSigning a).bound e ≠ some message) := by
    rw [hcorr, hbound]
  have hmarked :
      SyncO1 prims x top s pads noise (gOf s pads u) rest a (b.1, (b.2.1.1, false), b.2.2) :=
    SigningCompilerO1SyncHandlers.syncO1_mark prims x s pads u rest noise top a b hs.1 false
  rw [real_round2, comp_round2, round2X_eq, hflag, SigningCompilerO1ChainRelease.runXO1_bind,
    SigningCompilerO1ChainRelease.runXO1_get, pure_bind]
  by_cases hg : i ∈ (realSigning a).corrupt ∨ i ∉ J.1 ∨ (realSigning a).bound e ≠ some message
  · rw [if_pos hg, if_pos (hguard.2 hg), SigningCompilerO1ChainRelease.runXO1_pure, map_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hmarked, hs.2⟩))
  rw [if_neg hg, if_neg (fun h => hg (hguard.1 h)), SigningCompilerO1ChainRelease.runXO1_bind,
    runXO1_liftBaseX, bind_map_left, map_bind]
  have hin : SyncIn prims x s pads u rest noise top ((realSigning a, a.1.2.1.2), a.1.2.2)
      ((realSigning a, a.1.2.1.2), a.1.2.2) a (b.1, (b.2.1.1, false), b.2.2) :=
    (syncO1_iff_syncIn prims x s pads u rest noise top a _).1 ⟨hmarked, hs.2⟩
  have hbe : (realSigning a).bound e = some message := by
    by_contra h
    exact hg (Or.inr (Or.inr h))
  refine relTriple_bind (SigningCompilerSyncLocalRead.relTriple_supported
    (SigningCompilerO1BuildOnce.bottomOnce_sync prims x q s pads u rest noise hkeys top (realSigning a) (treeOf e) a
      (b.1, (b.2.1.1, false), b.2.2) hin ha hb rfl)) ?_
  rintro z y ⟨hzy, hz, -⟩
  have hcz : z.2.1.2 = a.1.2 :=
    realWorld_carried prims x s pads u rest _ a z (by with_reducible exact hz)
  rcases hzy with h | h | ⟨hval, hsyn, hm, hsg, -, -, htr, -, hbd, -, -, -, -⟩
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    left
    rcases hz1 : z.1.1 with _ | tree <;> rw [hz1] at hra
    · rw [mem_support_pure_iff] at hra
      subst hra
      exact realStop_withCarried q _ _ (by rw [hcz]) h
    · rw [support_map] at hra
      obtain ⟨v, hv, rfl⟩ := hra
      have hcv : v.2.1.2 = a.1.2 :=
        (realWorld_carried prims x s pads u rest _ z.2 v (by with_reducible exact hv)).trans hcz
      exact realStop_withCarried q _ _ (by rw [hcv])
        (realWorld_stop prims x q s pads u rest _ z.2 h v (by with_reducible exact hv))
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    rw [support_map] at hrb
    obtain ⟨r, hr, rfl⟩ := hrb
    exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ h
      r hr))
  obtain ⟨⟨zt, zs⟩, za⟩ := z
  dsimp only at hval hsyn hbd hcz ⊢
  rcases hy : y.1.1 with _ | dtree <;> rw [hy] at hval htr <;>
    simp only [Option.map_none, Option.map_some] at hval <;> subst hval <;> dsimp only
  · rw [SigningCompilerO1ChainRelease.runXO1_pure, map_pure]
    refine relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, (syncO1_iff_syncIn prims x s pads u rest noise
      top _ _).2 ?_⟩))
    dsimp only at hsyn ⊢
    obtain ⟨hcore, hx, htop, hp⟩ := hsyn
    exact ⟨hcore, hx, ⟨htop.topRows, htop.topRun⟩, hp⟩
  · by_cases ha2 : RealStop q za
    · apply TreeCheckKernelCoupling.relTriple_of_support
      intro ra hra rb hrb
      rw [support_map] at hra
      obtain ⟨v, hv, rfl⟩ := hra
      have hcv : v.2.1.2 = a.1.2 :=
        (realWorld_carried prims x s pads u rest _ za v (by with_reducible exact hv)).trans hcz
      exact Or.inl (realStop_withCarried q _ _ (by rw [hcv])
        (realWorld_stop prims x q s pads u rest _ za ha2 v (by with_reducible exact hv)))
    by_cases hb2 : Stop y.2
    · apply TreeCheckKernelCoupling.relTriple_of_support
      intro ra hra rb hrb
      rw [support_map] at hrb
      obtain ⟨r, hr, rfl⟩ := hrb
      exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _
        hb2 r hr))
    rw [← hcz] at hsyn
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine relTriple_bind (SigningCompilerSyncLocalRead.relTriple_supported
      (after_sync prims x q s pads u rest noise hkeys top zs b.1.base.signing i J e message parts
        dtree
        za ({ base := y.1.2, starts := b.1.starts }, y.2) hsyn ha2 hb2 hm htr
        (by rw [hbd]; exact hbe) (by show za.1.2.1.1.bound = zs.bound; rw [hcz, hbd])
        hsg.symm)) ?_
    rintro v r ⟨hpost, hv, -⟩
    have hcv : v.2.1.2 = a.1.2 :=
      (realWorld_carried prims x s pads u rest _ za v (by with_reducible exact hv)).trans hcz
    apply relTriple_pure_pure
    rw [hcz] at hpost
    rcases hpost with h | h | h
    · exact Or.inl (realStop_withCarried q _ _ (by rw [hcv]) h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end Round2

end ThresholdLeanXmssSecurity.SigningCompilerO1Round2

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.signersAt_withRecord_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.signersAt_withRecord_subset

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.releasedBound_withRecord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.releasedBound_withRecord

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.signersAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.signersAt_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.round2X_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.round2X_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.real_round2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.real_round2

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.comp_round2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.comp_round2

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.realWorld_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.realWorld_carried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.realWorld_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.realWorld_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.record_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.record_mid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.chain_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.chain_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.chains_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.chains_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.tail_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.tail_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.after_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.after_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.realStop_withCarried' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.realStop_withCarried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round2.step_round2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round2.step_round2
