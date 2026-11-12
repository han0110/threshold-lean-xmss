import ThresholdLeanXmssSecurity.Proof.SigningLinkPaid
import ThresholdLeanXmssSecurity.Proof.SigningPartnerCompare
import ThresholdLeanXmssSecurity.Proof.SigningPrefixBottom

/-!
# Transport of released signing selections

The cache frame of the actual cached-randomizer trigger preserves logged answers
and every tracked entry outside bottom-message trials. Successful round-two
receipts identify selections under compatible cache extensions.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.SigningReleasedTransferProof

open SigningCacheLogProof SigningPartnerCompareProof SigningFlatProof SigningFlatEagerProof
open SigningHitLaneProof SigningJointEagerProof SigningOneRunProof

variable {C : Committee} (prims : Primitives)

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- The actual cached trigger adds only bottom-message trial entries. -/
theorem cachedExtra_frame (seeds : C.Term → HashOutput) (P : PublicParameter)
    (p : FlatState C) (t : (WorldSpec C).Domain) (p' : FlatState C) z
    (hz : z ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (SigningR1FixedProof.cachedExtra seeds P p t p')).run p'.1.1.1)) :
    p'.1.1.1 ≤ z.2 ∧ ∀ q, OutsideTrials P q → z.2 q = p'.1.1.1 q := by
  classical
  unfold SigningR1FixedProof.cachedExtra at hz
  split at hz
  · with_reducible exact grindExtra_cache_frame P (SigningGuessProof.cachedRandomizer seeds p.1.1.1) p t p' z hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨le_rfl, fun _ _ => rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- The same cache frame holds with the joint opening state carried alongside it. -/
theorem jointCachedExtra_frame (seeds : C.Term → HashOutput) (P : PublicParameter)
    (p : FlatJointState C) (t : (WorldSpec C).Domain) (p' : FlatJointState C) z
    (hz : z ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (jointCachedExtra seeds P p t p')).run p'.1.1.1)) :
    p'.1.1.1 ≤ z.2 ∧ ∀ q, OutsideTrials P q → z.2 q = p'.1.1.1 q :=
  by
    unfold jointCachedExtra at hz
    with_reducible exact cachedExtra_frame seeds P (p.1, p.2.1) t (p'.1, p'.2.1) z hz

set_option backward.isDefEq.respectTransparency false in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- One world call preserves the frame, including the extra cached grind. -/
theorem jointWorld_logAgreement (seeds : C.Term → HashOutput) (P : PublicParameter)
    (t : (WorldSpec C).Domain) (ht : ¬IsProgram t) (p : FlatJointState C)
    (hp : LogAgreement P p.1) z
    (hz : z ∈ support ((eagerWorld prims (jointCachedExtra seeds P) t).run p)) :
    LogAgreement P z.2.1 := by
  simp only [eagerWorld, carry, StateT.run_mk, support_bind, support_map,
    Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hz
  dsimp only at hy ⊢
  have hlog := logAgreement_step prims P t ht p.1 hp w hw
  have hf := jointCachedExtra_frame seeds P p t (w.2, p.2) y (by with_reducible exact hy)
  exact ⟨hlog.1.trans hf.1, fun q hq => (hf.2 q hq).trans (hlog.2 q hq)⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- A logged-state invariant holds through setup, adaptive signing and verification. -/
theorem jointGame_inv
    (W : QueryImpl (WorldSpec C) (StateT (FlatJointState C) ProbComp))
    (Inv : LoggedState C → Prop)
    (hW : ∀ t, ¬IsProgram t → ∀ s, Inv s.1 → ∀ z ∈ support ((W t).run s), Inv z.2.1)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (s : FlatJointState C) (hs : Inv s.1) z
    (hz : z ∈ support ((jointGame W A x).run s)) : Inv z.2.1 := by
  have hsetup : SigningHitProof.ProgramFree (referenceTree
      (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    with_reducible exact SigningHitProof.programFree_liftFree _
  unfold jointGame jointGameWith at hz
  dsimp only at hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨r, hr, hz⟩ := hz
  have hi := support_programFree_inv W (fun p => Inv p.1) hW _ (by with_reducible exact hsetup) s hs r (by with_reducible exact hr)
  rcases r with ⟨_ | (top | tree), p⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hi
  · simp only [StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
      mem_support_bind_iff] at hz
    obtain ⟨a, ha, w, hw, hz⟩ := hz
    have ha' := SeedHitProof.support_simulateQ_inv _ (fun p : FlatJointState C => Inv p.1)
      (flatWith_inv W Inv hW _ (programFree_openingOracles x top)) _ p hi a ha
    have hw' := support_programFree_inv W (fun p => Inv p.1) hW _
      (programFree_tsigFinishLogged x top _ _) a.2 ha' w hw
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hw'
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hi

set_option backward.isDefEq.respectTransparency false in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Every supported outcome of the actual one run satisfies the cache frame. -/
theorem oneRun_logAgreement (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (oneRun prims A x)) : LogAgreement x.1 z.2.1 := by
  unfold oneRun at hz
  exact jointGame_inv _ (LogAgreement x.1) (jointWorld_logAgreement prims x.2.1 x.1)
    A x jointInit (by
      constructor
      · intro q output h
        simp [jointInit, loggedInit, logCache] at h
      · intro q _
        rfl) z (by with_reducible exact hz)

set_option backward.isDefEq.respectTransparency false in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Forgetting only the monitor preserves the actual split-run cache frame. -/
theorem splitRun_logAgreement (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (splitRunAt prims A x)) : LogAgreement x.1 z.2.1.1.1 := by
  apply oneRun_logAgreement prims A x (z.1, (z.2.1.1.1, z.2.2))
  rw [← splitRunAt_oneRun, support_map]
  exact ⟨z, (by with_reducible exact hz), rfl⟩

/-- The released row reconstructed entirely from the observable result and log. -/
def LoggedReleasedRow (x : SigningSecurityProof.Keys3 C)
    (r : JointResult C × ℕ × QueryLog (WorldSpec C)) : Prop :=
  SigningLinkPaidProof.ReleasedPartnerRow prims x (r.1, (logCache r.2.2, r.2.1), r.2.2)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- The observable law moves the released row to the current split one run. -/
theorem releasedPartner_eq_split_log (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[SigningLinkPaidProof.ReleasedPartnerRow prims x |
      SigningUnchargedLoggedProof.jointRun prims A x] =
      Pr[fun z => LoggedReleasedRow prims x (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2) |
        splitRunAt prims A x] := by
  have hj : Pr[SigningLinkPaidProof.ReleasedPartnerRow prims x |
      SigningUnchargedLoggedProof.jointRun prims A x] =
      Pr[fun z => LoggedReleasedRow prims x (z.1, z.2.1.2, z.2.2) |
        SigningUnchargedLoggedProof.jointRun prims A x] := by
    apply probEvent_ext
    intro z hz
    have hl : (z.1.1, z.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
      rw [← SigningUnchargedLoggedProof.jointRun_logged, support_map]
      exact ⟨z, (by with_reducible exact hz), rfl⟩
    exact and_congr (SigningPartnerTransferProof.lazyPartnerRow_congr prims x z.1.1 z.1.2
      z.2.1.2 z.2.2 (loggedRun_cacheFromLog prims A x (z.1.1, z.2) (by with_reducible exact hl))) Iff.rfl
  rw [hj, ← probEvent_oneRun prims A x (LoggedReleasedRow prims x),
    ← splitRunAt_oneRun, probEvent_map]
  rfl

open SigningGuessProof SigningDescentProof SigningCacheProof

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- A successful receipt fixes the entire selected replay on both compatible caches. -/
theorem receipt_selected_extension (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (receipt : Round2Receipt C)
    {a b : HashCache C} (hle : a ≤ b)
    (hr : ReceiptRuns prims x top a receipt)
    (he : receipt.key = forgery.signature.leafIndex)
    (hb : state.bound receipt.key = some receipt.message)
    (hc : receipt.candidate = D prims (answersOf a)
      (prfValue x.2.1 (.randomizer bottomLayer receipt.key)))
    (hprf : cachedRandomizer x.2.1 a receipt.key = cachedRandomizer x.2.1 b receipt.key) :
    (FinalState.mk x top state forgery a false).selected prims =
      (FinalState.mk x top state forgery b false).selected prims := by
  have hc' : receipt.candidate = D prims (answersOf b)
      (prfValue x.2.1 (.randomizer bottomLayer receipt.key)) := by
    calc
      _ = cachedRandomizer x.2.1 a receipt.key := hc.trans (cachedRandomizer_eq prims _ _ _)
      _ = cachedRandomizer x.2.1 b receipt.key := hprf
      _ = _ := (cachedRandomizer_eq prims _ _ _).symm
  exact (ReceiptRuns.selected prims (FinalState.mk x top state forgery a false) receipt hr he hb hc).trans
    (ReceiptRuns.selected prims (FinalState.mk x top state forgery b false) receipt
      (ReceiptRuns.mono prims x top hle receipt hr) he hb hc').symm

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- A threshold release supplies one canonical receipt from the actual verification prefix. -/
theorem verifyRun_released_receipt (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C)
    (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) (message : Message)
    (hb : state.bound forgery.signature.leafIndex = some message)
    (ht : C.t ≤ (signersAt state forgery.signature.leafIndex message).card)
    (hn : ¬OpeningMatch prims x (r.1.1, r.2)) :
    ∃ receipt : Round2Receipt C, ReceiptRuns prims x top r.2.1 receipt ∧
      receipt.key = forgery.signature.leafIndex ∧
      state.bound receipt.key = some receipt.message ∧
      receipt.candidate = D prims (answersOf r.2.1)
        (prfValue x.2.1 (.randomizer bottomLayer receipt.key)) := by
  obtain ⟨q, v, hpre⟩ := SigningGuardedFlagProof.verificationPrefix_exists prims A x r (by with_reducible exact hr)
    top state forgery hm
  obtain ⟨top', p, f, hp, hp1, hq, hv, hf, rfl⟩ := hpre
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  have hqf : q.2.1 ≤ f.2.1 := (countRun_grows prims _ _ v hv).trans
    (countRun_grows prims _ _ f hf)
  obtain ⟨q', hq', _, hstate, hcache⟩ := SigningReleasedProof.openingRun_receipts prims x _ _
    SigningCoreProof.tsigInit false p.2 q hq
  obtain ⟨receipt, _, he, hmessage, hruns⟩ := SigningReleasedProof.receiptRun_released prims x top' _
    p.2 q' hq' q.1.1.signature.leafIndex message (by rw [hstate]; exact ht)
  rw [hcache] at hruns
  have hfinal := ReceiptRuns.mono prims x top' hqf receipt hruns
  have htop : TopFacts prims (answersOf f.2.1) x.2.1 x.1 top' := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _] at hp
    have hval := run_liftFree prims _ _ p (by with_reducible exact hp) (answersOf f.2.1)
      (agrees_answersOf ((countRun_grows prims _ _ q hq).trans hqf))
    rw [hp1] at hval
    obtain ⟨generated, hgen, hchain, hroot⟩ :=
      D_refTop (prims := prims) (h := answersOf f.2.1) x.1 x.2.1 emptyTop
    have heq : generated = top' := TreeOutput.top.inj
      (Option.some.inj (hgen.symm.trans hval.symm))
    rw [← heq]
    exact ⟨hchain, hroot⟩
  refine ⟨receipt, hfinal, he, ?_, ?_⟩
  · rw [he, hmessage]
    exact hb
  · exact (ReceiptRuns.canonical prims x
      (((v.1.1 && f.1, q.1.2.1.2), some (top', q.1.2.1.1, q.1.1)), f.2)
      top' q.1.2.1.1 q.1.1 rfl htop receipt hfinal he hn).1

/-- Keep the source's unlogged stream keys while taking all tracked entries from the destination. -/
def completeCache (source destination : HashCache C) : HashCache C :=
  fun q => if Tracked q then destination q else source q

/-- A tracked cache extension extends to a full cache extension. -/
theorem le_completeCache {source logged destination : HashCache C}
    (hlog : ∀ q, Tracked q → source q = logged q) (hle : logged ≤ destination) :
    source ≤ completeCache source destination := by
  intro q answer ha
  by_cases hq : Tracked q
  · simp only [completeCache, if_pos hq]
    exact hle (by rw [← hlog q hq]; exact ha)
  · simpa only [completeCache, if_neg hq] using ha

/-- The completed cache reads every tracked query exactly as the destination does. -/
theorem completeCache_tracked (source destination : HashCache C) (q : Query C) (hq : Tracked q) :
    completeCache source destination q = destination q := by
  simp only [completeCache, if_pos hq]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Canonical receipts transport selection through the actual logged-cache frame. -/
theorem receipt_selected_frame (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (receipt : Round2Receipt C)
    {source logged destination : HashCache C}
    (hlog : ∀ q, Tracked q → source q = logged q)
    (hle : logged ≤ destination)
    (houtside : ∀ q, OutsideTrials x.1 q → destination q = logged q)
    (hr : ReceiptRuns prims x top source receipt)
    (he : receipt.key = forgery.signature.leafIndex)
    (hb : state.bound receipt.key = some receipt.message)
    (hc : receipt.candidate = D prims (answersOf source)
      (prfValue x.2.1 (.randomizer bottomLayer receipt.key))) :
    (FinalState.mk x top state forgery logged false).selected prims =
      (FinalState.mk x top state forgery destination false).selected prims := by
  have hout : ∀ q, OutsideTrials x.1 q →
      source q = completeCache source destination q := by
    intro q hq
    rw [completeCache_tracked _ _ q hq.1, hlog q hq.1, houtside q hq]
  have hprf := congrFun (cachedRandomizer_eq_of_outside x.2.1 x.1 hout) receipt.key
  calc
    _ = (FinalState.mk x top state forgery source false).selected prims :=
      (SigningPartnerTransferProof.selected_eq prims x top state forgery hlog).symm
    _ = (FinalState.mk x top state forgery (completeCache source destination) false).selected prims :=
      receipt_selected_extension prims x top state forgery receipt
        (le_completeCache hlog hle) hr he hb hc hprf
    _ = _ := SigningPartnerTransferProof.selected_eq prims x top state forgery
      (completeCache_tracked source destination)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Each split outcome has a lazy source with the same observable result, counter and log. -/
theorem splitRun_source (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (splitRunAt prims A x)) :
    ∃ w ∈ support (SigningUnchargedLoggedProof.jointRun prims A x),
      w.1 = z.1 ∧ w.2.1.2 = z.2.1.1.1.1.2 ∧ w.2.2 = z.2.1.1.1.2 := by
  have hone : (z.1, (z.2.1.1.1, z.2.2)) ∈ support (oneRun prims A x) := by
    rw [← splitRunAt_oneRun, support_map]
    exact ⟨z, (by with_reducible exact hz), rfl⟩
  have ho : (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2) ∈ support
      ((fun y => (y.1, y.2.1.1.2, y.2.1.2)) <$> oneRun prims A x) := by
    rw [support_map]
    exact ⟨_, (by with_reducible exact hone), rfl⟩
  have hl : (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2) ∈ support
      ((fun w => (w.1, w.2.1.2, w.2.2)) <$> SigningUnchargedLoggedProof.jointRun prims A x) := by
    with_reducible exact (mem_support_iff_of_evalDist_eq (evalDist_oneRun prims A x) _).mp ho
  rw [support_map] at hl
  obtain ⟨w, hw, he⟩ := hl
  exact ⟨w, (by with_reducible exact hw), congrArg Prod.fst he, congrArg (fun y => y.2.1) he,
    congrArg (fun y => y.2.2) he⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Released lazy partners remain partners in the actual eager cache. -/
theorem splitRun_released_partner (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (splitRunAt prims A x))
    (hlazy : LoggedReleasedRow prims x (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2)) :
    z.1.1.1 = (true, false) ∧
      SigningPartnerLinkProof.BottomPartnerCase prims x (z.1.1, z.2.1.1.1.1) ∧
      SigningLinkPaidProof.ReleasedAt z.1.1.2 ∧
      ¬AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 := by
  obtain ⟨w, hw, hresult, hcount, hlog⟩ := splitRun_source prims A x z (by with_reducible exact hz)
  have hs : (w.1.1, w.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
    rw [← SigningUnchargedLoggedProof.jointRun_logged, support_map]
    exact ⟨w, (by with_reducible exact hw), rfl⟩
  have hc : ∀ q, Tracked q → w.2.1.1 q = logCache z.2.1.1.1.2 q := by
    intro q hq
    rw [← hlog]
    exact loggedRun_cacheFromLog prims A x (w.1.1, w.2) (by with_reducible exact hs) q hq
  have hrow : SigningLinkPaidProof.ReleasedPartnerRow prims x w := by
    have he := SigningPartnerTransferProof.lazyPartnerRow_congr prims x w.1.1 w.1.2
      w.2.1.2 w.2.2 (loggedRun_cacheFromLog prims A x (w.1.1, w.2) (by with_reducible exact hs))
    apply (and_congr he Iff.rfl).mpr
    simpa only [LoggedReleasedRow, SigningLinkPaidProof.ReleasedPartnerRow,
      hresult, hcount, hlog] using hlazy
  have hframe := splitRun_logAgreement prims A x z (by with_reducible exact hz)
  have hselected : ∀ top state forgery, z.1.1.2 = some (top, state, forgery) →
      (FinalState.mk x top state forgery (logCache z.2.1.1.1.2) false).selected prims =
        (FinalState.mk x top state forgery z.2.1.1.1.1.1 false).selected prims := by
    intro top state forgery hm
    obtain ⟨top', state', forgery', hm', message, hb, ht⟩ := hrow.2
    rw [hresult, hm] at hm'
    simp only [Option.some.injEq, Prod.mk.injEq] at hm'
    obtain ⟨rfl, rfl, rfl⟩ := hm'
    have hn : ¬OpeningMatch prims x (w.1.1, w.2.1) := by
      intro hopen
      exact hrow.1.2.1 (Or.inr (Or.inl (openingMatch_alternativeCommitment prims x _ hopen)))
    obtain ⟨receipt, hr, he, hb', hcanon⟩ := verifyRun_released_receipt prims A x (w.1, w.2.1)
      (by with_reducible exact SigningUnchargedLoggedProof.mem_verifyRun_of_joint prims A x w hw) top state forgery
      (by rw [hresult]; exact hm) message hb ht hn
    exact receipt_selected_frame prims x top state forgery receipt hc hframe.1 hframe.2
      hr he hb' hcanon
  refine ⟨hlazy.1.1, bottomPartnerCase_of_selected_eq prims x z.1.1 _ hframe.1 hselected
    hlazy.1.2.2, hlazy.2, ?_⟩
  intro halt
  exact hlazy.1.2.1 (Or.inr (Or.inl
    ((alternativeCommitment_congr_of_outside x.2.1 x.1 hframe.2).mp halt)))

set_option linter.constructorNameAsVariable false in
/-- The original released-transfer inequality holds on the actual cache-derived one run. -/
theorem releasedTransfer : SigningLinkPaidProof.ReleasedTransfer prims (C := C) := by
  intro A q x _ _ _ _
  rw [releasedPartner_eq_split_log]
  exact probEvent_mono (fun z hz h => splitRun_released_partner prims A x z (by with_reducible exact hz) h)

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.cachedExtra_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cachedExtra_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.jointWorld_logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointWorld_logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.jointGame_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointGame_inv

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.oneRun_logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oneRun_logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.splitRun_logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRun_logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.releasedPartner_eq_split_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms releasedPartner_eq_split_log

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.receipt_selected_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms receipt_selected_extension

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.verifyRun_released_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyRun_released_receipt

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.receipt_selected_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms receipt_selected_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.splitRun_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRun_source

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.splitRun_released_partner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRun_released_partner

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedTransferProof.releasedTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms releasedTransfer

end ThresholdLeanXmssSecurity.SigningReleasedTransferProof
