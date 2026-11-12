import ThresholdLeanXmssSecurity.Proof.SigningAssembly
import ThresholdLeanXmssSecurity.Proof.SigningCacheLog

/-!
The lazy partner row and the cache reconstructed from the joint call log.

1. Prove tracked-cache congruence for the selected pair, the honest key, the
   bottom partner, and all three charged events.
2. Reconstruct the entire lazy row from `logCache` of `SigningCacheLog` on `jointRun`.
3. Move that event to `splitRunAt` with the exact eager observable law.
4. Reduce `PartnerTransfer` to `PartnerCacheComparison`, on one split execution.

`PartnerCacheComparison` is equivalent to `PartnerTransfer`.
Its two events read different caches: `logCache` and the final eager cache.
Cache extension alone does not prove equality of the replayed selection:
an eager read may fill an earlier absent trial of the default-zero replay.

The eager sampling law holds for every fixed randomizer function. None of these
proofs uses the false fixed-randomizer `R1Link` or changes its trigger.
-/

open OracleComp OracleSpec
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningPartnerTransferProof

open LeanXmss ThresholdLeanXmss SigningAssemblyProof SigningCacheLogProof
open SigningFlatProof SigningFlatEagerProof SigningDescentProof SigningCacheProof

variable {C : Committee} (prims : Primitives)

attribute [local instance] Classical.propDecidable

/-- The tracked agreement of A1 includes every tweakable-hash cache entry. -/
theorem thView_eq {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) : thView a = thView b := by
  funext input
  exact h _ (tracked_hash input)

theorem tweakable_eq {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) {α : Type} (p : OracleComp HashSpec α) :
    D prims (answersOf a) (tweakable p) = D prims (answersOf b) (tweakable p) := by
  rw [D_tweakable, D_tweakable]
  congr 1
  funext input
  exact congrArg (fun v => v.getD 0) (h _ (tracked_hash input))

theorem prfValue_eq {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) (seeds : C.Term → HashOutput) (point : Point) :
    D prims (answersOf a) (prfValue seeds point) =
      D prims (answersOf b) (prfValue seeds point) := by
  simp only [prfValue, D_bind, D_mapM, D_pure, prf, D_map, D_hashQuery]
  congr 1
  apply List.map_congr_left
  intro T _
  rw [answersOf, answersOf, h _ (tracked_prf (seeds T) point)]

/-- The dealer's bottom-tree replay reads only hashes and PRF entries. -/
theorem bottomTree_eq (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (st : TsigState C) (forgery : Forgery) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    (FinalState.mk x top st forgery a false).bottomTree prims =
      (FinalState.mk x top st forgery b false).bottomTree prims := by
  unfold FinalState.bottomTree FinalState.dealt dealtWith
  dsimp only [FinalState.key, FinalState.answers]
  have hhash : (fun {α : Type} (p : OracleComp HashSpec α) =>
      D prims (answersOf a) (tweakable p)) =
      (fun {α : Type} (p : OracleComp HashSpec α) => D prims (answersOf b) (tweakable p)) := by
    funext α p
    exact tweakable_eq prims h p
  have hprf : (fun p => D prims (answersOf a) (prfValue x.2.1 p)) =
      (fun p => D prims (answersOf b) (prfValue x.2.1 p)) := by
    funext p
    exact prfValue_eq prims h _ p
  change (fun | some (.bottom tree) => some tree | _ => none)
      (referenceTree (m := Id) (fun p => D prims (answersOf a) (tweakable p))
        (fun p => D prims (answersOf a) (prfValue x.2.1 p)) x.1 top (.bottom (treeOf forgery.signature.leafIndex))) = _
  rw [hhash, hprf]
  rfl

/-- Replay of the selected pair is a function of the tracked cache. -/
theorem selected_eq (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (st : TsigState C) (forgery : Forgery) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    (FinalState.mk x top st forgery a false).selected prims =
      (FinalState.mk x top st forgery b false).selected prims := by
  simp only [FinalState.selected, bottomTree_eq prims x top st forgery h]
  congr 1
  funext message
  congr 1
  funext tree
  dsimp only [FinalState.answers, FinalState.key]
  change (D prims (answersOf a) (signCodeword x.1 (tree.commitment forgery.signature.leafIndex)
      forgery.signature.leafIndex message
      (D prims (answersOf a) (prfValue x.2.1 (.randomizer bottomLayer forgery.signature.leafIndex)))) >>= fun v =>
        pure (message, v.1)) = _
  rw [prfValue_eq prims h]
  unfold signCodeword
  rw [tweakable_eq prims h]
  rfl

/-- Every field of the replayed honest key ignores stream-key cache entries. -/
theorem honestKey_eq (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (st : TsigState C) (forgery : Forgery) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    (FinalState.mk x top st forgery a false).honestKey prims =
      (FinalState.mk x top st forgery b false).honestKey prims := by
  have hs : (FinalState.mk x top st forgery a false).chainStarts prims =
      (FinalState.mk x top st forgery b false).chainStarts prims := by
    funext lay key l
    exact prfValue_eq prims h _ _
  simp only [FinalState.honestKey, selected_eq prims x top st forgery h,
    bottomTree_eq prims x top st forgery h, hs]
  congr 1 <;> funext i <;> simp only [thView_eq h]

theorem bottomPartnerCase_congr (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (n : ℕ) {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    SigningPartnerLinkProof.BottomPartnerCase prims x (r, a, n) ↔
      SigningPartnerLinkProof.BottomPartnerCase prims x (r, b, n) := by
  unfold SigningPartnerLinkProof.BottomPartnerCase
  simp only [SigningCostProof.finalOf, honestKey_eq prims x _ _ _ h,
    thView_eq h]

theorem alternativeCommitment_congr (seeds : C.Term → HashOutput) (P : PublicParameter)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    SigningGuessProof.AlternativeCommitment seeds P a ↔
      SigningGuessProof.AlternativeCommitment seeds P b := by
  have hr : SigningGuessProof.cachedRandomizer seeds a = SigningGuessProof.cachedRandomizer seeds b := by
    funext e
    unfold SigningGuessProof.cachedRandomizer
    congr 1
    apply List.map_congr_left
    intro T _
    rw [h _ (tracked_prf _ _)]
  simp only [SigningGuessProof.AlternativeCommitment, SigningGuessProof.RandomizerCached,
    hr, h _ (tracked_prf _ _), h _ (tracked_hash _)]
  rw [hr]

def TrackedOnly {α : Type} (p : OracleComp (Query C →ₒ HashOutput) α) : Prop :=
  IsQueryBoundP p (fun q => ¬Tracked q) 0

theorem forestHash_tracked {α : Type} (p : OracleComp HashSpec α) :
    TrackedOnly (SigningHitProof.forestHash (C := C) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [TrackedOnly, SigningHitProof.forestHash]
  | query_bind q k ih =>
    simp only [SigningHitProof.forestHash, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map] at ⊢
    change IsQueryBoundP _ _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (not_not.mpr (tracked_hash q)), fun a => by
      simpa only [TrackedOnly, SigningHitProof.forestHash,
        if_neg (not_not.mpr (tracked_hash q))] using ih a⟩

theorem forestValue_tracked (seeds : C.Term → HashOutput) (point : Point) :
    TrackedOnly (SigningHitProof.forestValue seeds point) := by
  unfold SigningHitProof.forestValue TrackedOnly
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · apply SigningHitProof.mapM_bound_zero
    intro T
    simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun h => False.elim (h (tracked_prf _ _))
  · intro _ _; simp

theorem referenceJob_tracked (x : SigningSecurityProof.Keys3 C) (job : Job) :
    TrackedOnly (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 job) := by
  unfold referenceJob TrackedOnly
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · apply SigningHitProof.mapM_bound_zero
    intro p
    exact forestValue_tracked _ p
  · intro values _
    cases job.kind with
    | chainEnd e l => exact (isQueryBoundP_map_iff _ _ _).mpr (forestHash_tracked _)
    | chainValue e l p => exact (isQueryBoundP_map_iff _ _ _).mpr (forestHash_tracked _)
    | commitment e => exact (isQueryBoundP_map_iff _ _ _).mpr (forestHash_tracked _)
    | randomizer => simp
    | chainRow e l =>
      apply isQueryBoundP_bind (n := 0) (m := 0) (forestHash_tracked _)
      intro _ _
      apply isQueryBoundP_bind (n := 0) (m := 0) (forestHash_tracked _)
      intro _ _
      apply isQueryBoundP_bind (n := 0) (m := 0) (forestHash_tracked _)
      intro _ _; simp

theorem canonicalTopAfterJobs_tracked (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (outputs : List (List Bit)) (levels : ℕ) :
    TrackedOnly (SigningGuessProof.canonicalTopAfterJobs x key outputs levels) := by
  unfold SigningGuessProof.canonicalTopAfterJobs TrackedOnly
  apply isQueryBoundP_bind (n := 0) (m := 0) (forestHash_tracked _)
  intro root _
  apply isQueryBoundP_bind (n := 0) (m := 0) (forestHash_tracked _)
  intro _ _; simp

theorem canonicalTopSetup_tracked (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (jobs : List Job) (levels : ℕ) :
    TrackedOnly (SigningGuessProof.canonicalTopSetupForJobs x key jobs levels) := by
  unfold SigningGuessProof.canonicalTopSetupForJobs TrackedOnly
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · apply SigningHitProof.mapM_bound_zero
    intro job
    exact referenceJob_tracked x job
  · intro outputs _
    exact canonicalTopAfterJobs_tracked x key outputs levels

theorem canonicalTopGrind_tracked (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) : TrackedOnly (SigningGuessProof.canonicalTopGrind x key) := by
  unfold SigningGuessProof.canonicalTopGrind SigningGuessProof.topGrindAfter TrackedOnly
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · exact canonicalTopSetup_tracked x key _ _
  · intro pair _
    exact (isQueryBoundP_map_iff _ _ _).mpr (forestHash_tracked _)

/-- Cache replay of a tracked program ignores every untracked entry. -/
theorem resolves_tracked {α : Type} {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) {p : OracleComp (Query C →ₒ HashOutput) α}
    {v : α} (hp : TrackedOnly p) (hr : DeterministicSigning.Resolves a p v) :
    DeterministicSigning.Resolves b p v := by
  induction hr with
  | pure value => exact .pure value
  | query input answer ha next value tail ih =>
    rw [TrackedOnly, isQueryBoundP_query_bind_iff] at hp
    have ht : Tracked input := Classical.not_not.mp (hp.1.resolve_right (by omega))
    apply DeterministicSigning.Resolves.query input answer ((h input ht) ▸ ha) next value
    apply ih
    simpa only [TrackedOnly, if_neg (not_not.mpr ht)] using hp.2 answer

theorem resolvedTopPartner_congr (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    SigningGuessProof.ResolvedTopPartner x key a ↔ SigningGuessProof.ResolvedTopPartner x key b := by
  have hr (v) : DeterministicSigning.Resolves a (SigningGuessProof.canonicalTopGrind x key) v ↔
      DeterministicSigning.Resolves b (SigningGuessProof.canonicalTopGrind x key) v :=
    ⟨resolves_tracked h (canonicalTopGrind_tracked x key),
      resolves_tracked (fun q hq => (h q hq).symm) (canonicalTopGrind_tracked x key)⟩
  simp only [SigningGuessProof.ResolvedTopPartner, hr, h _ (tracked_hash _)]

theorem hit_congr (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex) (hk : HonestKey)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) : Hit a P e hk ↔ Hit b P e hk := by
  unfold Hit bottomStep topStep bottomStepCached bottomLeafCached bottomNodeCached
    topStepCached topLeafCached topNodeCached
  rw [thView_eq h]

theorem chargedOutput_congr (x : SigningSecurityProof.Keys3 C) (r : Result C) (n : ℕ)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    SigningGuessProof.ChargedOutput prims x (r, a, n) ↔
      SigningGuessProof.ChargedOutput prims x (r, b, n) := by
  simp only [SigningGuessProof.ChargedOutput, SigningCostProof.WinHit, SigningCostProof.finalOf,
    honestKey_eq prims x _ _ _ h, hit_congr _ _ _ h, alternativeCommitment_congr _ _ h,
    resolvedTopPartner_congr _ _ h]

/-- The complete lazy row, including its charged-event exclusions, depends only
on tracked entries. No monotonicity of the selected pair is asserted. -/
theorem lazyPartnerRow_congr (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (candidates : List (SigningOpeningProof.HiddenKey × Digest)) (n : ℕ)
    (log : QueryLog (WorldSpec C)) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    LazyPartnerRow prims x ((r, candidates), (a, n), log) ↔
      LazyPartnerRow prims x ((r, candidates), (b, n), log) := by
  simp only [LazyPartnerRow, Win, Charged, chargedOutput_congr prims x r n h,
    bottomPartnerCase_congr prims x r n h]

/-- The lazy row reconstructed from the observable result, count and world log. -/
def LoggedPartnerRow (x : SigningSecurityProof.Keys3 C)
    (r : Result C × ℕ × QueryLog (WorldSpec C)) : Prop :=
  LazyPartnerRow prims x ((r.1, []), (logCache r.2.2, r.2.1), r.2.2)

/-- A1 supplies the exact cache reconstruction on the original joint run. -/
theorem jointRun_lazyPartner_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[LazyPartnerRow prims x | SigningUnchargedLoggedProof.jointRun prims A x] =
      Pr[fun z => LoggedPartnerRow prims x (z.1.1, z.2.1.2, z.2.2) |
        SigningUnchargedLoggedProof.jointRun prims A x] := by
  apply probEvent_ext
  intro z hz
  have hl : (z.1.1, z.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
    rw [← SigningUnchargedLoggedProof.jointRun_logged, support_map]
    exact ⟨z, hz, rfl⟩
  exact lazyPartnerRow_congr prims x z.1.1 z.1.2 z.2.1.2 z.2.2
    (loggedRun_cacheFromLog prims A x _ hl)

/-- A1 and the eager observable law move the original lazy row to the split run,
where it still reads the cache reconstructed from the original call log. -/
theorem lazyPartner_eq_split_log (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[LazyPartnerRow prims x | SigningUnchargedLoggedProof.jointRun prims A x] =
      Pr[fun z => LoggedPartnerRow prims x (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2) |
        splitRunAt prims ρ A x] := by
  rw [jointRun_lazyPartner_eq]
  have hj : Pr[fun z => LoggedPartnerRow prims x (z.1.1, z.2.1.2, z.2.2) |
        SigningUnchargedLoggedProof.jointRun prims A x] =
      Pr[fun z => LoggedPartnerRow prims x (z.1, z.2.1.2, z.2.2) |
        SigningCostProof.loggedRun prims A x] := by
    rw [← SigningUnchargedLoggedProof.jointRun_logged, probEvent_map]
    rfl
  rw [hj]
  have he := probEvent_congr'
    (p := LoggedPartnerRow prims x) (q := LoggedPartnerRow prims x)
    (fun _ _ => Iff.rfl) (evalDist_flatEagerRun_logged prims x.1 (ρ x) A x)
  simp only [probEvent_map, Function.comp_def] at he
  rw [← he]
  rw [splitRunAt, ← monitoredRun_forget, probEvent_map,
    ← splitRun_forget, probEvent_map]
  rfl

/-- Exact remaining A26 comparison, now on one split execution. The left event
uses the logged cache; the right uses the eager cache. The selected pair must
not be assumed monotone under cache extension. -/
def PartnerCacheComparison (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[fun z => LoggedPartnerRow prims x (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2) |
      splitRunAt prims ρ A x] ≤
    Pr[fun z => EagerPartner prims x z ∧
      ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 |
      splitRunAt prims ρ A x]

/-- The remaining comparison is equivalent to the original target, with no
additional hypotheses and no change to either event. -/
theorem partnerTransfer_iff_comparison (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) :
    PartnerTransfer prims ρ ↔ PartnerCacheComparison prims ρ := by
  unfold PartnerTransfer PartnerCacheComparison
  simp only [lazyPartner_eq_split_log prims ρ]

/-- The original target follows once its remaining same-run cache comparison is proved. -/
theorem partnerTransfer_of_comparison (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (h : PartnerCacheComparison prims ρ) : PartnerTransfer prims ρ :=
  (partnerTransfer_iff_comparison prims ρ).mpr h

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.selected_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.honestKey_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honestKey_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.resolvedTopPartner_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resolvedTopPartner_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.lazyPartnerRow_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lazyPartnerRow_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.jointRun_lazyPartner_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointRun_lazyPartner_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.lazyPartner_eq_split_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lazyPartner_eq_split_log

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.partnerTransfer_iff_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partnerTransfer_iff_comparison

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerTransferProof.partnerTransfer_of_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partnerTransfer_of_comparison

end SigningPartnerTransferProof
end ThresholdLeanXmssSecurity
