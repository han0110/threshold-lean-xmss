import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1ChainRelease
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling

/-! # The corruption handler of the O1 coupling

`step_corrupt` states that the corruption handler keeps `SyncO1` or stops one side. The real side
makes no call. The compiler side inserts the operator and releases each key that crosses the
threshold.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerSyncSuffix SigningCompilerO1Sync SigningCompilerO1ChainRelease
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real corruption handler makes no call. It inserts the operator when the guard passes. -/
theorem real_corrupt (top : TopTree) (i : C.Party) (a : RealState C) :
    (realOracles prims x s pads u rest top (.inr (.corrupt i))).run a =
      if C.t - 1 < (insert i (realSigning a).corrupt).card then pure (none, a) else
        pure (some (dealtKeys x.1 x.2.1 x.2.2 i),
          withSigning a { realSigning a with corrupt := insert i (realSigning a).corrupt }) := by
  have ht : ∀ st : TsigState C, (tsigOracles (m := OracleComp (WorldSpec C))
      (fun oa => SigningCoreProof.honestLift oa) (SigningJointEagerProof.dealtOf x top) (.corrupt i)).run st =
      if C.t - 1 < (insert i st.corrupt).card then pure (none, st) else
        pure (some (dealtKeys x.1 x.2.1 x.2.2 i), { st with corrupt := insert i st.corrupt }) := by
    intro st
    split_ifs with hg
    · simp [tsigOracles, StateT.run_bind, StateT.run_get, hg]
    · simp [tsigOracles, StateT.run_bind, StateT.run_get, hg]
      rfl
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (realImpl x (gOf s pads u) rest)
    ((rawTraceFlatWith prims x (openingOracles x (SigningJointEagerProof.dealtOf x top))
      (.inr (.corrupt i))).run a.1)).run a.2 = _
  simp only [rawTraceFlatWith, openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk, ht]
  split_ifs <;> simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> rfl

/-- A mark sets the mark of the compiler state and changes nothing else. -/
theorem runXO1_mark (m : Bool) (src : SourceStateO1 C) (st : CompState C) :
    runXO1 (compBackend x q s pads u rest noise) (liftM (markQ (C := C) m)) src st =
      pure (((), src), (st.1.1, m), st.2) := by
  simp [runXO1, markQ]
  rw [SigningCompilerSyncBackend.backendT_mark capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest m st]
  rfl

/-- The release of the keys of a list, each with `t` signers at the timing state. -/
theorem releaseKeys_mid (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sig : TsigState C) (a : RealState C) :
    ∀ (keys : List KeyIndex), (∀ e ∈ keys, ∃ m, sig.bound e = some m ∧ C.t ≤ (signersAt sig e m).card) →
      ∀ (b : SourceStateO1 C × CompState C),
      SyncMid prims x top s pads noise (gOf s pads u) rest sig sig a b → b.2.1.2 = false →
      ∀ r ∈ support (runXO1 (compBackend x q s pads u rest noise)
        (keys.mapM (sourceReleaseKeyX x.1 x.2.1)) b.1 b.2),
      Stop r.2 ∨ (SyncMid prims x top s pads noise (gOf s pads u) rest sig sig a (r.1.2, r.2) ∧
        r.2.1.2 = false) := by
  intro keys
  induction keys with
  | nil =>
    intro _ b hs hmark r hr
    rw [List.mapM_nil, runXO1_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Or.inr ⟨hs, hmark⟩
  | cons e keys ih =>
    intro hcov b hs hmark r hr
    rw [List.mapM_cons, runXO1_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    rw [runXO1_bind, mem_support_bind_iff] at hr
    obtain ⟨next, hnext, hr⟩ := hr
    rw [runXO1_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rcases releaseKey_mid prims x q s pads u rest noise hkeys top sig sig e a b hs hmark
        (hcov e List.mem_cons_self) mid hmid with hstop | ⟨hs', -, -, -, hm⟩
    · exact Or.inl (runXO1_stop x q s pads u rest noise _ mid.1.2 mid.2 hstop next hnext)
    exact ih (fun e' he' => hcov e' (List.mem_cons_of_mem e he')) (mid.1.2, mid.2) hs' hm next hnext

/-- A change of the mark keeps the relation. -/
theorem syncO1_mark (top : TopTree) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b) (m : Bool) :
    SyncO1 prims x top s pads noise (gOf s pads u) rest a (b.1, (b.2.1.1, m), b.2.2) := by
  obtain ⟨⟨⟨⟨hf, hcache⟩, hcount⟩, hx⟩, htop⟩ := hs
  exact ⟨⟨⟨⟨hf.mark x s pads noise (gOf s pads u) rest a b.1.base b.2 m, hcache⟩, hcount⟩,
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
      bottomSeen := hx.bottomSeen }⟩, ⟨htop.topRows, htop.topRun⟩⟩

/-- After a passed corruption guard, both sides insert the operator, and the relation inside the
handler holds with the new signing state as the core and the timing state. -/
theorem syncMid_corrupt (top : TopTree) (i : C.Party) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b)
    (hg : ¬C.t - 1 < (insert i (realSigning a).corrupt).card) :
    SyncMid prims x top s pads noise (gOf s pads u) rest
      { realSigning a with corrupt := insert i (realSigning a).corrupt }
      { realSigning a with corrupt := insert i (realSigning a).corrupt } a
      (⟨{ b.1.base with signing :=
          { b.1.base.signing with corrupt := insert i (realSigning a).corrupt } }, b.1.starts⟩, b.2) := by
  obtain ⟨⟨⟨⟨hf, hcache⟩, hcount⟩, hx⟩, htop⟩ := hs
  have hsub : ∀ e m, signersAt (realSigning a) e m ⊆
      signersAt { realSigning a with corrupt := insert i (realSigning a).corrupt } e m := by
    intro e m
    unfold signersAt
    exact Finset.union_subset_union (Finset.subset_insert _ _) subset_rfl
  refine ⟨⟨⟨?_, hcache⟩, hcount⟩, ?_, ⟨htop.topRows, htop.topRun⟩⟩
  · exact
      { corrupt := rfl
        bound := hf.bound, released := hf.released, exposed := hf.exposed,
        candidates := hf.candidates, flag := hf.flag, reveal := hf.reveal,
        releasedPending := hf.releasedPending,
        opening := ⟨hf.opening.actualValue, hf.opening.released⟩,
        pendingValid := hf.pendingValid, allocated := hf.allocated, virtualSeen := hf.virtualSeen,
        compilerBound := hf.compilerBound, trace := hf.trace, bad := hf.bad, share := hf.share,
        restAgree := hf.restAgree, restFree := hf.restFree, realPrivate := hf.realPrivate,
        frontier := hf.frontier, candidatesPaid := hf.candidatesPaid, doneCached := hf.doneCached }
  · exact
      { treeRows := hx.treeRows
        storedTrees := hx.storedTrees
        storedTopDigit := hx.storedTopDigit
        startsTreed := hx.startsTreed
        boundTreeRevealed := hx.boundTreeRevealed
        revealedReleased := hx.revealedReleased
        revealedCovered := fun e l p h => by
          obtain ⟨m, hm, hc, hd⟩ := hx.revealedCovered e l p h
          exact ⟨m, hm, hc.trans (Finset.card_le_card (hsub e m)), hd⟩
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
        corruptBound := not_lt.mp hg
        releasedBound := hx.releasedBound
        prfSeen := fun hfl T p hv => (hx.prfSeen hfl T p hv).imp_left
          (TprfSecurityProof.revealed_mono (Finset.subset_insert _ _))
        bottomSeen := fun hfl T e l d hv => (hx.bottomSeen hfl T e l d hv).imp_left
          (TprfSecurityProof.revealed_mono (Finset.subset_insert _ _)) }

/-- Corruption, with the sweep of the crossed keys. -/
theorem step_corrupt (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (i : C.Party) : StepO1 prims x q s pads u rest noise top (.inr (.corrupt i)) := by
  intro a b hs ha hb
  have hflag : b.1.base.hiddenFlag = false := by
    have h1 : b.1.base.hiddenFlag = realFlag a := hs.1.1.1.1.flag
    have h2 : realFlag a = false := by
      unfold RealStop at ha
      simpa using (not_or.mp ha).1
    rw [h1, h2]
  have hcorr : b.1.base.signing.corrupt = (realSigning a).corrupt := hs.1.1.1.1.corrupt
  have hcomp : (compOracles prims x q s pads u rest noise top (.inr (.corrupt i))).run b =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> runXO1 (compBackend x q s pads u rest noise)
        (sourceOraclesO1X prims x top (.inr (.corrupt i))) b.1 b.2 := rfl
  rw [real_corrupt, hcomp]
  simp only [sourceOraclesO1X, sourceTsigO1X, runXO1_bind, runXO1_get, pure_bind, runXO1_mark, hflag,
    hcorr]
  split_ifs with hg
  · simp only [runXO1_pure, pure_bind, runXO1_modify, map_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, syncO1_mark prims x s pads u rest noise top a b hs false⟩))
  · simp only [runXO1_modify, pure_bind, runXO1_bind, runXO1_pure, map_bind]
    have hbound : b.1.base.signing.bound = (realSigning a).bound := hs.1.1.1.1.bound
    have hreleased : b.1.base.signing.released = (realSigning a).released := hs.1.1.1.1.released
    have hcov : ∀ e ∈ crossedKeys b.1.base.signing
        { b.1.base.signing with corrupt := insert i (realSigning a).corrupt },
        ∃ m, (realSigning a).bound e = some m ∧
          C.t ≤ (signersAt { realSigning a with corrupt := insert i (realSigning a).corrupt } e m).card := by
      intro e he
      have hfilter := (List.mem_filter.mp he).2
      cases hm : b.1.base.signing.bound e with
      | none => simp [hm] at hfilter
      | some m =>
        simp only [hm, decide_eq_true_eq] at hfilter
        refine ⟨m, hbound ▸ hm, ?_⟩
        have hsigners : signersAt { b.1.base.signing with corrupt := insert i (realSigning a).corrupt } e m =
            signersAt { realSigning a with corrupt := insert i (realSigning a).corrupt } e m := by
          unfold signersAt
          rw [hreleased]
        rw [← hsigners]
        exact hfilter.2
    apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb hrb
    rw [support_pure, Set.mem_singleton_iff] at hra
    subst hra
    rw [mem_support_bind_iff] at hrb
    obtain ⟨w, hw, hrb⟩ := hrb
    rw [mem_support_bind_iff] at hw
    obtain ⟨r, hr, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    rw [map_pure, support_pure, Set.mem_singleton_iff] at hrb
    subst hrb
    have hmid := syncMid_corrupt prims x s pads u rest noise top i a (b.1, (b.2.1.1, false), b.2.2)
      (syncO1_mark prims x s pads u rest noise top a b hs false) hg
    rcases releaseKeys_mid prims x q s pads u rest noise hkeys top _ a _ hcov _ hmid rfl r hr with
      hstop | ⟨hm, -⟩
    · exact Or.inr (Or.inl hstop)
    · exact Or.inr (Or.inr ⟨rfl, ⟨hm.1, hm.2.1⟩, ⟨hm.2.2.topRows, hm.2.2.topRun⟩⟩)

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.real_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.real_corrupt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.runXO1_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.runXO1_mark

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.releaseKeys_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.releaseKeys_mid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.syncO1_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.syncO1_mark

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.syncMid_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.syncMid_corrupt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.step_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SyncHandlers.step_corrupt
