import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Reads
import ThresholdLeanXmssSecurity.Proof.SigningGuessLink

/-! # The verification of the O1 coupling

`verify_sync` couples the verification calls of the real world with the verification handler of
the compiler. Each call is a hash read that is no slot and no bottom base input, so
`ordinaryRead_sync` couples it. Both sides add the same candidates of the call.

- `syncCore_candidates` states that new candidates on both sides keep `SyncCore` when each new
  candidate that carries its secret has a revealed key.
- `real_query_bind` and `comp_query_bind` split one call from the two runs.
- `verify_call` couples one call with its candidates.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Verify
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Reads SigningCompilerSyncLocalRead
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

section Verify
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The verification handler of the compiler, at the signing state and the trees of the snapshot. -/
def verifyImplO1 (st : SourceState C) : QueryImpl HashSpec (SourceMXO1 C) := fun input => liftBaseX (do
  let value ← sourceHashX x.1 x.2.1 (.hash input)
  modify fun (s : SourceState C) => { s with candidates :=
    s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
  pure value : SourceMX C HashOutput)

/-- The post of a verification prefix. Both sides give the same value, and the real side gives the
candidates of its calls. -/
def VerifyPost (top : TopTree) {α : Type} (ra : (α × List (HiddenKey × Digest)) × RealState C)
    (rb : (α × SourceStateO1 C) × CompState C) : Prop :=
  RealStop q ra.2 ∨ Stop rb.2 ∨
    (ra.1.1 = rb.1.1 ∧
      (SyncO1 prims x top s pads noise (gOf s pads u) rest
        (withCandidates ra.2 (ra.2.1.2.2.2 ++ ra.1.2)) (rb.1.2, rb.2) ∧ PadsFixed x pads rb.2) ∧
      rb.2.1.2 = false)

/-- New candidates on both sides keep `SyncCore` when each new candidate that carries its secret
has a revealed key. -/
theorem syncCore_candidates (g : C.Term × CPoint → HashOutput) (a : RealState C)
    (src : SourceState C) (st : CompState C) (new : List (HiddenKey × Digest))
    (h : SyncCore x s pads noise g rest a (src, st))
    (hpaid : ∀ c ∈ new, c.2 = s c.1 → src.revealed c.1 ≠ none) :
    SyncCore x s pads noise g rest (withCandidates a (a.1.2.2.2 ++ new))
      ({ src with candidates := src.candidates ++ new }, st) := by
  obtain ⟨⟨hf, hc⟩, hn⟩ := h
  refine ⟨⟨{ hf with
    candidates := congrArg (· ++ new) hf.candidates
    opening := ⟨hf.opening.actualValue, hf.opening.released⟩
    candidatesPaid := ?_ }, hc⟩, hn⟩
  · intro c hcm he
    rcases List.mem_append.1 hcm with hcm | hcm
    · exact hf.candidatesPaid c hcm he
    · exact hpaid c hcm he

/-- A candidate of a call is the hidden candidate of its input, and it is not released. -/
theorem mem_callCandidates (P : PublicParameter) (sig : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (input : HashInput) (c : HiddenKey × Digest) :
    c ∈ SigningGuessLinkProof.callCandidates P sig trees input ↔
      hiddenCandidate P input = some c ∧ ¬Released sig trees c.1 := by
  simp [SigningGuessLinkProof.callCandidates, List.mem_filter, Option.mem_toList]

/-- The real run of a logged verification splits its first call. -/
theorem real_query_bind (sig : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    {α : Type} (input : HashInput) (next : HashOutput → OracleComp HashSpec α)
    (vlog : List (HiddenKey × Digest)) (a : RealState C) :
    (simulateQ (realWorld prims x s pads u rest)
      (SigningCoreProof.honestLift ((simulateQ (SigningGuessLinkProof.logImpl x.1 sig trees)
        (liftM (HashSpec.query input) >>= next)).run vlog))).run a =
      (readCall prims x s pads u rest false (.inl (.hash input))).run a >>= fun r =>
        (simulateQ (realWorld prims x s pads u rest)
          (SigningCoreProof.honestLift ((simulateQ (SigningGuessLinkProof.logImpl x.1 sig trees)
            (next r.1)).run (vlog ++ SigningGuessLinkProof.callCandidates x.1 sig trees input)))).run
          r.2 := by
  have hlift : ∀ {β : Type} (ob : OracleComp (RoSpec C) β),
      SigningCoreProof.honestLift ob = SigningSecurityProof.liftFree ob := fun _ => rfl
  have hlog : (simulateQ (SigningGuessLinkProof.logImpl x.1 sig trees)
      (liftM (HashSpec.query input) >>= next)).run vlog =
        hashQuery (.hash input) >>= fun v =>
          (simulateQ (SigningGuessLinkProof.logImpl x.1 sig trees) (next v)).run
            (vlog ++ SigningGuessLinkProof.callCandidates x.1 sig trees input) := by
    simp [simulateQ_bind, SigningGuessLinkProof.logImpl, StateT.run_bind]
  simp only [hlift]
  rw [hlog, SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind,
    StateT.run_bind]
  have hq : (simulateQ (realWorld prims x s pads u rest)
      (free ((hashQuery (C := C) (.hash input)).liftComp (LocalSpec C)))).run a =
        (readCall prims x s pads u rest false (.inl (.hash input))).run a := by
    rw [readCall, if_neg Bool.false_ne_true, hashQuery, free]
    erw [liftComp_query, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    erw [id_map]
    rfl
  rw [hq]
  rfl

/-- The compiler run of a verification splits its first call. -/
theorem comp_query_bind (st : SourceState C) {α : Type} (input : HashInput)
    (next : HashOutput → OracleComp HashSpec α) (src : SourceStateO1 C) (cst : CompState C) :
    runXO1 (compBackend x q s pads u rest noise)
        (simulateQ (verifyImplO1 x st) (liftM (HashSpec.query input) >>= next)) src cst =
      runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 (.inl (.hash input)))
          src.base cst >>= fun r =>
        runXO1 (compBackend x q s pads u rest noise) (simulateQ (verifyImplO1 x st) (next r.1.1))
          ⟨{ r.1.2 with candidates := r.1.2.candidates ++
            SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }, src.starts⟩ r.2 := by
  have hbind : ∀ {β : Type} (oa : SourceMXO1 C HashOutput) (f : HashOutput → SourceMXO1 C β),
      runXO1 (compBackend x q s pads u rest noise) (oa >>= f) src cst =
        runXO1 (compBackend x q s pads u rest noise) oa src cst >>= fun r =>
          runXO1 (compBackend x q s pads u rest noise) (f r.1.1) r.1.2 r.2 := by
    intro β oa f
    simp only [runXO1, StateT.run_bind, simulateQ_bind]
  rw [simulateQ_bind, simulateQ_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [hbind, verifyImplO1, runXO1_liftBaseX, runX_bind]
  simp only [runX_bind, runX_modify, runX_pure, pure_bind, map_bind, bind_assoc, map_pure]
  rfl

/-- One verification call with its candidates. -/
theorem verify_call (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (input : HashInput) (hbase : ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (vlog : List (HiddenKey × Digest)) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest
      (withCandidates a (a.1.2.2.2 ++ vlog)) b ∧ PadsFixed x pads b.2)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((readCall prims x s pads u rest false (.inl (.hash input))).run a)
      (runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 (.inl (.hash input)))
        b.1.base b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧ ra.2.1.2 = a.1.2 ∧
          (SyncO1 prims x top s pads noise (gOf s pads u) rest
            (withCandidates ra.2 (ra.2.1.2.2.2 ++ (vlog ++
              SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input)))
            (⟨{ rb.1.2 with candidates := rb.1.2.candidates ++
              SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input },
              b.1.starts⟩, rb.2) ∧ PadsFixed x pads rb.2) ∧
          rb.2.1.2 = false)) := by
  obtain ⟨hcore, hx, htop, hp⟩ := (syncO1_iff_syncIn prims x s pads u rest noise top _ b).1 hs
  have hread := ordinaryRead_sync prims x q s pads u rest noise hkeys false
    (a.1.2.1, a.1.2.2.1, a.1.2.2.2 ++ vlog) (.inl (.hash input)) (not_isSlot_hash x input)
    (fun i hi => by cases hi; exact hbase) a b.1.base b.2 hcore ha hb hmark
  refine relTriple_post_mono (relTriple_supported hread) ?_
  rintro ra ⟨⟨vb, srcb⟩, stb⟩ ⟨hpost, -, hrb⟩
  rcases hpost with h | h | ⟨⟨hv, hval⟩, hsync, hf, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  obtain ⟨hsrc, hrev⟩ := hval input rfl
  subst hsrc
  have hpaid : ∀ c ∈ SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input,
      c.2 = s c.1 → b.1.base.revealed c.1 ≠ none := by
    intro c hc he
    refine hrev c.1 ?_
    rw [← he]
    exact (mem_callCandidates x.1 _ _ input c).1 hc |>.1
  have hfresh : ∀ c ∈ SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input,
      ∀ lay e, c.1 = .opening lay e → c.2 ≠ s c.1 := by
    intro c hc lay e hk he
    have hmem := (mem_callCandidates x.1 _ _ input c).1 hc
    have hr := hpaid c hc he
    rw [hk] at hr
    exact hmem.2 (hk ▸ hx.rest.revealedReleased lay e hr)
  have hx' := ExtraOpen.frame prims x top s (fun query => query = .hash input) (fun _ _ => False)
    (fun _ _ => False) b.1.base.revealed b.1.base.revealed (a.1.2.1, a.1.2.2.1, a.1.2.2.2 ++ vlog)
    a ra.2 b (⟨b.1.base, b.1.starts⟩, stb) hx hf rfl (fun _ h => h) (fun _ h => Or.inl h)
    (fun e ρ message h => hbase e ρ message (Query.hash.inj h).symm)
    (fun p hr _ h => by
      have hk := PendingInput.hiddenCandidate x.1 p (s p.key)
      rw [Query.hash.inj h] at hk
      exact hrev p.key hk hr)
    (fun _ _ h => by cases h) (fun _ _ _ _ h => by cases h) (fun _ _ h => h)
  have hx'' := ExtraOpen.candidates prims x top s (fun _ _ => False) b.1.base.revealed _ _
    (SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input) hx' hpaid
    hfresh
  have ht := TopO1.frame prims x top _ a ra.2 b (⟨b.1.base, b.1.starts⟩, stb)
    ⟨htop.topRows, htop.topRun⟩ hf
  have hA : withCandidates ra.2 (ra.2.1.2.2.2 ++ (vlog ++
      SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input)) =
      withCandidates (withCarried ra.2 (a.1.2.1, a.1.2.2.1, a.1.2.2.2 ++ vlog))
        ((a.1.2.2.2 ++ vlog) ++
          SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input) := by
    simp only [withCandidates, withCarried, hf.carried, List.append_assoc]
  refine Or.inr (Or.inr ⟨hv, hf.carried, ?_, hm⟩)
  rw [hA]
  have hc := syncCore_candidates x s pads rest noise (gOf s pads u) _ _ _
    (SigningGuessLinkProof.callCandidates x.1 (realSigning a) (realExposed a) input) hsync hpaid
  have hpads := backend_padsFixed x q s pads u rest noise _ b.2 hp _ hrb
  exact (syncO1_iff_syncIn prims x s pads u rest noise top _ _).2
    ⟨hc, hx'', ⟨ht.topRows, ht.topRun⟩, hpads⟩

/-- `verify_sync` with the signing state and the trees of the log handler fixed. -/
theorem verify_sync_aux (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (st : SourceState C) {α : Type} (oa : OracleComp HashSpec α)
    (hbase : Queries (fun input => ∀ e ρ message,
      input ≠ randomizerInput x.1 bottomLayer e ρ message) oa) :
    ∀ (vlog : List (HiddenKey × Digest)) (a : RealState C) (b : SourceStateO1 C × CompState C),
      st.signing = realSigning a → st.exposed = realExposed a →
      SyncO1 prims x top s pads noise (gOf s pads u) rest
        (withCandidates a (a.1.2.2.2 ++ vlog)) b ∧ PadsFixed x pads b.2 →
      ¬RealStop q a → ¬Stop b.2 → b.2.1.2 = false →
      RelTriple
        ((simulateQ (realWorld prims x s pads u rest)
          (SigningCoreProof.honestLift ((simulateQ
            (SigningGuessLinkProof.logImpl x.1 st.signing st.exposed) oa).run vlog))).run a)
        (runXO1 (compBackend x q s pads u rest noise) (simulateQ (verifyImplO1 x st) oa) b.1 b.2)
        (VerifyPost prims x q s pads u rest noise top) := by
  induction oa using OracleComp.inductionOn with
  | pure v =>
    intro vlog a b _ _ hs _ _ hmark
    have hl : (simulateQ (realWorld prims x s pads u rest)
        (SigningCoreProof.honestLift ((simulateQ
          (SigningGuessLinkProof.logImpl x.1 st.signing st.exposed)
            (pure v : OracleComp HashSpec α)).run vlog))).run a = pure ((v, vlog), a) := by
      simp only [simulateQ_pure, StateT.run_pure]
      rfl
    have hr : runXO1 (compBackend x q s pads u rest noise)
        (simulateQ (verifyImplO1 x st) (pure v : OracleComp HashSpec α)) b.1 b.2 =
          pure ((v, b.1), b.2) := by
      simp [runXO1]
    rw [hl, hr]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hs, hmark⟩))
  | query_bind input next ih =>
    intro vlog a b hsig hexp hs ha hb hmark
    have hq := (isQueryBound_query_bind_iff ..).mp hbase
    have hstep := verify_call prims x q s pads u rest noise hkeys top input hq.1 vlog a b hs ha hb
      hmark
    rw [← hsig, ← hexp] at hstep
    rw [real_query_bind, comp_query_bind]
    refine relTriple_bind hstep ?_
    rintro ⟨va, a'⟩ ⟨⟨vb, srcb⟩, stb⟩ (h | h | ⟨hv, hcar, hsync, hm⟩)
    · exact relTriple_of_support_left fun c hc _ => Or.inl
        (simulateQ_sticky (realWorld prims x s pads u rest) (RealStop q)
          (fun t st h r hr => realStop_world prims x (gOf s pads u) rest q t st h r hr) _ a' h c hc)
    · exact relTriple_of_support_right fun c hc _ => Or.inr (Or.inl
        (simulateQ_sticky _ Stop (backendT_stop x.1 x.2.1 x.2.2 q s pads (tauOf s pads)
          (gOf s pads u) noise rest) _ stb h c hc))
    · change va = vb at hv
      subst hv
      change a'.1.2 = a.1.2 at hcar
      by_cases ha' : RealStop q a'
      · exact relTriple_of_support_left fun c hc _ => Or.inl
          (simulateQ_sticky (realWorld prims x s pads u rest) (RealStop q)
            (fun t st h r hr => realStop_world prims x (gOf s pads u) rest q t st h r hr) _ a' ha'
              c hc)
      by_cases hb' : Stop stb
      · exact relTriple_of_support_right fun c hc _ => Or.inr (Or.inl
          (simulateQ_sticky _ Stop (backendT_stop x.1 x.2.1 x.2.2 q s pads (tauOf s pads)
            (gOf s pads u) noise rest) _ stb hb' c hc))
      exact ih va (hq.2 va) _ a' _ (hsig.trans (congrArg (fun c => c.1.1) hcar.symm))
        (hexp.trans (congrArg (fun c => c.2.1) hcar.symm)) hsync ha' hb' hm

/-- The verification calls, each with its candidates. The computation makes no bottom base call. -/
theorem verify_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    {α : Type} (oa : OracleComp HashSpec α)
    (hbase : Queries (fun input => ∀ e ρ message,
      input ≠ randomizerInput x.1 bottomLayer e ρ message) oa)
    (st : SourceState C)
    (vlog : List (HiddenKey × Digest)) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hsig : st.signing = realSigning a) (hexp : st.exposed = realExposed a)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest
      (withCandidates a (a.1.2.2.2 ++ vlog)) b ∧ PadsFixed x pads b.2)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        (SigningCoreProof.honestLift ((simulateQ
          (SigningGuessLinkProof.logImpl x.1 (realSigning a) (realExposed a)) oa).run vlog))).run a)
      (runXO1 (compBackend x q s pads u rest noise) (simulateQ (verifyImplO1 x st) oa) b.1 b.2)
      (VerifyPost prims x q s pads u rest noise top) := by
  have h := verify_sync_aux prims x q s pads u rest noise hkeys top st oa hbase vlog a b hsig hexp
    hs ha hb hmark
  rwa [hsig, hexp] at h

end Verify

end ThresholdLeanXmssSecurity.SigningCompilerO1Verify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.syncCore_candidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.syncCore_candidates

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.mem_callCandidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.mem_callCandidates

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.real_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.real_query_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.comp_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.comp_query_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.verify_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.verify_call

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.verify_sync_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.verify_sync_aux

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Verify.verify_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Verify.verify_sync
