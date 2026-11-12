import ThresholdLeanXmssSecurity.Proof.LifetimeTailRefresh

/-!
# The flag estimate for a lawful state-dependent tail

The actual setup prefix and tail share one path budget. The reference program
chooses supported free setup answers, preserving that budget. Protected prefix
inputs, protected tail inputs and hidden stream keys each use one copy of Q;
the refresh collision terms retain the original 256-bit denominator.

The probability and budget arguments specialize `LifetimeJointHop`,
`LifetimePathCount` and `LifetimeReferenceBudget` to the driver's actual tail.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeTailFlagBound
open LifetimeTailKernel LifetimeTailRefresh
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (T : TailDriver C E A.State) (x : C.Party → Keys C) (z : Aux)
variable (lawful : T.Lawful D)

abbrev Early (A : Adversary C E (Keys C) PEmpty PEmpty) :=
  A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)

def prefixHitG (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (u : KeygenFresh C) : ℝ≥0∞ :=
  Pr[fun r => ∃ v ∈ r.2, AimedPrefixCell D parts u v |
    simulateQ (prssLocalAt prims h) (keygenHashLog (aimedEarlyProgram D A x z h parts))]

def tailLogG (h : Query C → HashOutput) (keys : KeyName C × HashOutput → Digest)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) :
    ProbComp (Bool × List (Query C)) := do
  let r ← simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts)
  simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
    (referenceTailG K circuits settings D T prims h normal parts r)))

def referenceErrorG (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) : ℝ≥0∞ :=
  aimedMean ($ᵗ (KeygenFresh C)) (prefixHitG prims D A x z h parts) +
  aimedMean (simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts)) (fun r =>
    aimedMean ($ᵗ (KeygenFresh C)) (tailHitG prims K circuits settings D T h normal parts r))

def finishG (h : Query C → HashOutput) (parts : C.Party → Parts C) (r : Early A) : ℝ≥0∞ :=
  finishProbabilityG prims K circuits settings D T h
    (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)

def actualProbabilityG (h : Query C → HashOutput) (parts : C.Party → Parts C) : ℝ≥0∞ :=
  aimedMean (simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts))
    (finishG prims K circuits settings D A T h parts)

omit [Fintype E] [DecidableEq E] in
theorem actualProbability_le_oneG (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    actualProbabilityG prims K circuits settings D A T x z h parts ≤ 1 :=
  aimedMean_le_const _ _ _ (fun _ => probEvent_le_one)

omit [Fintype E] [DecidableEq E] in
theorem actualProbability_refreshG (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S) (hc : ¬ KeygenClash D parts) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      actualProbabilityG prims K circuits settings D A T x z (prssExtend S a) parts) =
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      aimedMean ($ᵗ (S → HashOutput)) (fun echo =>
        actualProbabilityG prims K circuits settings D A T x z
          (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts))) := by
  unfold actualProbabilityG finishG finishProbabilityG
  simp only [aimedMean_probEvent]
  apply probEvent_congr_evalDist
  exact evalDist_aimedRefresh D S parts hmem hc _

theorem actualProbability_prefix_leG (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) :
    let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
    actualProbabilityG prims K circuits settings D A T x z h parts ≤
      aimedMean (simulateQ (prssLocalAt prims (prssExtend S a))
        (aimedEarlyProgram D A x z (prssExtend S a) parts)) (finishG prims K circuits settings D A T h parts) +
      prefixHitG prims D A x z (prssExtend S a) parts u := by
  dsimp only
  unfold actualProbabilityG finishG finishProbabilityG prefixHitG
  rw [aimedRefresh_early prims]
  simp only [aimedMean_probEvent, aimed_prssLocalAt_eq]
  exact probEvent_aimedPrefix_swap_le prims _ _ (AimedPrefixCell D parts u)
    (aimedRefresh_off prims D S parts hmem a echo u) _ _ _

def flagProgramG : OracleComp (WorldSpec C)
    ((A.State × Option (RevealRows C)) × (Bool × Bool)) := do
  let r ← setupPrefix D A x z
  (fun y => (r, y)) <$> (simulateQ (aimedFlagQueries D (rowsOf r.2))
    (T.tail K circuits settings r)).run false

include lawful in
omit [Fintype E] [DecidableEq E] in
theorem flagProgramG_noProgram :
    IsQueryBoundP (flagProgramG K circuits settings D A T x z) AimedProgramCall 0 := by
  apply qb0_bind (aimed_noProgram_setupPrefix D A x z)
  intro r
  rw [map_eq_bind_pure_comp]
  exact qb0_bind (aimed_noProgram_flag D (rowsOf r.2) _
    (tail_noProgram K circuits settings D T lawful r) false) (fun _ => by simp)

omit [Fintype E] [DecidableEq E] in
/-- The same eager setup computation, retaining the driver's entire state. -/
theorem flagProgramG_at (keys : KeyName C × HashOutput → Digest) (h : Query C → HashOutput) :
    simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
      (flagProgramG K circuits settings D A T x z)) = (do
      let st ← simulateQ (prssLocalAt prims h) (A.start (corruptInputs D x) z)
      let parts ← prssSampleParts D
      let r ← simulateQ (prssLocalAt prims h) (prssEarlyRounds D A st h parts)
      eagerFinishG prims K circuits settings D T keys h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)) := by
  simp only [flagProgramG, simulateQ_bind, simulateQ_map, aimedKeyLocal_setupPrefix,
    bind_assoc, setupEarly, pure_bind, prssInitialData_at,
    prssEarlyDataRounds_mask, prssEarlyDataRounds_at, aimedFixedBoundary_run, eagerFinishG]

/-- Port of TreeKeyAimed.evalDist_aimedFlagProgram_at_fullParts (3585). -/
theorem flagProgramG_fullParts (keys : KeyName C × HashOutput → Digest) (h : Query C → HashOutput) :
    𝒟[simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
      (flagProgramG K circuits settings D A T x z))] =
    𝒟[do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let r ← simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts)
      eagerFinishG prims K circuits settings D T keys h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)] := by
  simp only [aimedEarlyProgram, simulateQ_bind, bind_assoc]
  rw [flagProgramG_at]
  conv_rhs => rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro state
  rw [evalDist_bind, ← evalDist_aimedPartsMask D, ← evalDist_bind, bind_map_left]
  simp only [aimedPartsMask_early, aimedPartsMask_data]

theorem eagerProbability_eq (S : Finset (Query C)) :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true | (do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h)) (simulateQ (aimedKeyLocal prims D keys)
        (flagProgramG K circuits settings D A T x z)))] =
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbabilityG prims K circuits settings D A T x z (prssExtend S a) parts)) := by
  have he (keys : KeyName C × HashOutput → Digest) (a : S → HashOutput) :=
    probEvent_congr_evalDist (flagProgramG_fullParts prims K circuits settings D A T x z keys
      (prssExtend S a)) (fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true)
  simp only [← aimedMean_probEvent] at he ⊢
  simp_rw [he]
  rw [aimedMean_comm]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))]
  rw [aimedMean_comm]
  unfold actualProbabilityG finishG finishProbabilityG
  simp only [← aimedMean_probEvent]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (simulateQ (prssLocalAt prims _) (aimedEarlyProgram D A x z _ _))]

include lawful in
omit [Fintype E] [DecidableEq E] in
theorem flagProgramG_eager_cover (cover : Finset (Query C)) :
    ∃ S : Finset (Query C), cover ⊆ S ∧
    𝒟[(simulateQ (lazyKeyWorld prims D) (flagProgramG K circuits settings D A T x z)).run' (∅, ∅)] =
    𝒟[do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h)) (simulateQ (aimedKeyLocal prims D keys)
        (flagProgramG K circuits settings D A T x z))] := by
  let game := flagProgramG K circuits settings D A T x z
  have hg : IsQueryBoundP game AimedProgramCall 0 := flagProgramG_noProgram K circuits settings D A T x z lawful
  have hs : ∀ keys : KeyName C × HashOutput → Digest, ∃ S : Finset (Query C),
      PrssLocalCovered S (simulateQ (aimedKeyLocal prims D keys) game) :=
    fun keys => prssLocalCovered_exists _
  choose S hS using hs
  let T := cover ∪ Finset.univ.biUnion S
  refine ⟨T, Finset.subset_union_left, ?_⟩
  rw [show 𝒟[(simulateQ (lazyKeyWorld prims D) game).run' (∅, ∅)] =
      𝒟[($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅] by
      simpa only [tableExtending_empty] using evalDist_lazyKeyWorld prims D game ∅ ∅]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro keys
  rw [← simulateQ_aimedKeyLocal prims D keys game hg]
  exact evalDist_prssLocal_at prims T _ ((hS keys).mono fun q hq =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨keys, Finset.mem_univ _, hq⟩))


-- Ports of LifetimePathCount:403–490,550–669; the tail is the actual driver.
/-- A path budget on the fixed reference prefix and its selected continuation.
It places no condition on an adversary state outside that prefix's support. -/
def ReferenceBudgetG (Q : ℕ) : Prop :=
  ∀ (h : Query C → HashOutput) (normal : KeyName C → HashOutput) (parts : C.Party → Parts C),
    IsQueryBoundP (worldRoles.adversary (aimedEarlyProgram D A x z h parts) >>=
      referenceTailG K circuits settings D T prims h normal parts) WorldCounted Q

section PathBounds

variable (Q : ℕ) (budget : ReferenceBudgetG prims K circuits settings D A T x z Q)
include budget

omit [Fintype E] [DecidableEq E] in
theorem reference_early_boundG (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    IsQueryBoundP (aimedEarlyProgram D A x z h parts) Counted Q :=
  LifetimePathCount.counted_of_adversary _ Q (IsQueryBoundP.of_bind_left (budget h (fun _ => 0) parts))

omit [Fintype E] [DecidableEq E] in
theorem reference_tail_boundG (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (r : Early A)
    (hr : r ∈ support (aimedEarlyProgram D A x z h parts)) :
    IsQueryBoundP (referenceTailG K circuits settings D T prims h normal parts r) WorldCounted Q := by
  apply IsQueryBoundP.continuation_mono_of_mem_support WorldCounted _ _ Q (budget h normal parts) r
  rwa [LifetimeKeygenCapQuiet.support_adversary]

/-- Protected derivation inputs in the complete reference prefix cost `Q*m`. -/
theorem prefix_hit_boundG (h : Query C → HashOutput) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (KeygenFresh C)) (prefixHitG prims D A x z h parts)) ≤
      ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold prefixHitG
  rw [aimedMean_parts_event]
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by rw [aimedEarlyProgram_exposed]))
  intro parts r hr
  apply aimedSetupLog_length_le _ _ _ r (support_simulateQ_subset _ _ hr)
  apply IsQueryBoundP.of_imp (p' := Counted) _
    (reference_early_boundG prims K circuits settings D A T x z Q budget h parts)
  intro t ht
  rcases t with n | v | a
  · exact ht.elim
  · cases v <;> simp_all [aimedLocalSetup, aimedSetupQuery, Counted]
  · exact ht.elim

include lawful in
/-- The selected reference tail uses the budget of its own supported prefix. -/
theorem tail_log_boundG (h : Query C → HashOutput) (keys : KeyName C × HashOutput → Digest)
    (normal : KeyName C → HashOutput) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v | (do
      let r ← keygenPartsKernel (tailLogG prims K circuits settings D A T x z h keys normal)
      let u ← $ᵗ (KeygenFresh C)
      pure (r, u))] ≤ ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by
      simp only [tailLogG, aimedEarlyProgram_exposed, referenceTailG_exposed]))
  intro parts out hout
  simp only [tailLogG, support_bind, Set.mem_iUnion] at hout
  obtain ⟨r, earlyRun, hr⟩ := hout
  exact aimedSetupLog_length_le _ _
    (aimedKeyLocal_setup_bound prims D keys _ _
      (reference_tail_boundG prims K circuits settings D A T x z Q budget h normal parts r
        (support_simulateQ_subset _ _ earlyRun))
      (referenceTailG_noSetup K circuits settings D T prims lawful h
        normal parts r)) out (support_simulateQ_subset _ _ hr)

include lawful in
/-- The prefix and tail protection estimates each charge at most one full path. -/
theorem reference_error_boundG (h : Query C → HashOutput) (normal : KeyName C → HashOutput) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (referenceErrorG prims K circuits settings D A T x z h normal) ≤
      ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold referenceErrorG
  rw [aimedMean_add]
  apply add_le_add
  · exact prefix_hit_boundG prims K circuits settings D A T x z Q budget h
  · unfold tailHitG
    have hmove {α β γ : Type} (p : ProbComp α) (q : ProbComp β) (k : α → ProbComp γ)
        (f : α → γ → β → ℝ≥0∞) :
        aimedMean p (fun a => aimedMean (k a) (fun c => aimedMean q (f a c))) =
          aimedMean q (fun b => aimedMean p (fun a => aimedMean (k a) (fun c => f a c b))) := by
      simp_rw [aimedMean_comm (k _) q]
      rw [aimedMean_comm]
    simp_rw [aimedMean_comm ($ᵗ (KeygenFresh C)) ($ᵗ (KeyName C × HashOutput → Digest))]
    rw [hmove (p := Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (q := $ᵗ (KeyName C × HashOutput → Digest))]
    apply aimedMean_le_const
    intro keys
    have hb := tail_log_boundG prims K circuits settings D A T x z lawful Q budget h keys normal
    rw [← aimedMean_parts_event
      (tailLogG prims K circuits settings D A T x z h keys normal)
      (fun parts u out => ∃ v ∈ out.2, AimedPrefixCell D parts u v)] at hb
    unfold tailLogG at hb
    simp only [← aimedMean_probEvent] at hb
    simpa only [aimedMean_comm ($ᵗ (KeygenFresh C))] using hb

include lawful in
theorem parts_leG (S : Finset (Query C)) (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      actualProbabilityG prims K circuits settings D A T x z (prssExtend S a) parts) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    ((Q : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      referenceErrorG prims K circuits settings D A T x z
        (prssHashAt prims (prssExtend S a)) normal parts) := by
  rw [actualProbability_refreshG prims K circuits settings D A T x z S parts hmem hc,
    aimedMean_comm]
  rw [← aimedMean_const ($ᵗ (S → HashOutput))
    (((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
      ((Q : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256),
    ← aimedMean_add]
  apply aimedMean_mono
  intro a
  have hp := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => actualProbability_prefix_leG prims K circuits settings D A T x z S parts hmem a echo u))
  simp only [aimedMean_add, aimedMean_const] at hp
  let initial := simulateQ (prssLocalAt prims (prssExtend S a))
    (aimedEarlyProgram D A x z (prssExtend S a) parts)
  have hf := LifetimePathCount.mean_mono_support initial (fun r hr => refresh_finish_leG prims K circuits settings D T lawful S normal parts hmem hsk hc a r Q hni hn0
      (reference_tail_boundG prims K circuits settings D A T x z Q budget
        (prssHashAt prims (prssExtend S a)) normal parts r (by
          rw [aimedEarlyProgram_hashAt]
          exact support_simulateQ_subset _ _ hr)))
  simp only [aimedMean_add, aimedMean_const] at hf
  have hmove {f : KeygenFresh C → (S → HashOutput) → (Early A) → ℝ≥0∞} :
      aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput))
        (fun echo => aimedMean initial (f u echo))) =
      aimedMean initial (fun r => aimedMean ($ᵗ (KeygenFresh C))
        (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo => f u echo r))) := by
    simp_rw [aimedMean_comm ($ᵗ (S → HashOutput)) initial]
    rw [aimedMean_comm]
  rw [hmove] at hp
  unfold finishG at hp
  have hb := hp.trans (add_le_add hf le_rfl)
  unfold referenceErrorG prefixHitG
  unfold prefixHitG at hb
  simp only [aimedEarlyProgram_hashAt, aimed_prssLocalAt_hashAt]
  exact hb.trans_eq ((add_right_comm _ _ _).trans (add_assoc _ _ _))

include lawful in
theorem actual_total_leG (S : Finset (Query C)) (normal : KeyName C → HashOutput)
    (hmem : ∀ parts n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbabilityG prims K circuits settings D A T x z (prssExtend S a) parts)) ≤
      (((3 * Q) *
        prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let cost : ℝ≥0∞ :=
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    ((Q : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256
  have hp (parts : C.Party → Parts C) :
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbabilityG prims K circuits settings D A T x z (prssExtend S a) parts) ≤
      (if KeygenClash D parts then 1 else 0) + (cost + aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        referenceErrorG prims K circuits settings D A T x z
          (prssHashAt prims (prssExtend S a)) normal parts)) := by
    by_cases hc : KeygenClash D parts
    · rw [if_pos hc]
      exact (aimedMean_le_const _ 1 _ (fun a => actualProbability_le_oneG prims K circuits settings
        D A T x z _ parts)).trans (le_add_right le_rfl)
    · rw [if_neg hc, zero_add]
      exact parts_leG prims K circuits settings D A T x z lawful Q budget S normal parts
        (hmem parts) hsk hc hni hn0
  have hb := aimedMean_mono (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) hp
  simp only [aimedMean_add, aimedMean_const, aimedMean_event] at hb
  have hc : Pr[KeygenClash D | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] ≤
      (keygenClashCount C : ℝ≥0∞) / 2 ^ 256 := by
    simpa only [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using probEvent_keygenClash_le D
  have he : aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a => referenceErrorG prims K circuits settings
        D A T x z (prssHashAt prims (prssExtend S a)) normal parts)) ≤
      ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((Q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun a => reference_error_boundG prims K circuits settings D A T x z lawful Q budget
      (prssHashAt prims (prssExtend S a)) normal)
  refine (hb.trans (add_le_add hc (add_le_add le_rfl he))).trans ?_
  dsimp only [cost]
  simp only [← ENNReal.add_div]
  gcongr
  norm_cast
  have hb := aimed_boundary_zero_error_arith (C := C)
  rw [keygenFinish_card_pair]
  nlinarith


include lawful in
/-- The aimed-call estimate needs only the complete reference-path budget.
Its three uses of `Q` protect prefix derivation inputs, tail derivation inputs,
and the hidden stream keys. -/
theorem flagProgram_bound_pathG :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
      (simulateQ (lazyKeyWorld prims D) (flagProgramG K circuits settings D A T x z)).run' (∅, ∅)] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  by_cases hm : prssKeyCount C < 2 ^ 256
  · obtain ⟨normal, hni, hn0⟩ := aimed_normalTable_exists D hm
    obtain ⟨cover, hcanonical, hecho⟩ := aimedCover_exists (C := C)
    obtain ⟨S, hS, he⟩ := flagProgramG_eager_cover prims K circuits settings D A T x z lawful cover
    rw [probEvent_congr_evalDist he, eagerProbability_eq]
    exact actual_total_leG prims K circuits settings D A T x z lawful Q budget S normal
      (fun parts n _ => hS (hcanonical parts n)) (fun i j f => hS (hecho i j f)) hni hn0
  · have hm' : 2 ^ 256 ≤ prssKeyCount C := Nat.le_of_not_gt hm
    have hn : 2 ^ 256 ≤ 3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 := by
      nlinarith [Nat.zero_le (3 * Q * prssKeyCount C)]
    calc
      _ ≤ 1 := probEvent_le_one
      _ = (2 ^ 256 : ℝ≥0∞) / 2 ^ 256 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast hn) _

end PathBounds

/-- Port of LifetimeReferenceBudget.reference_bound (463), choosing actual free answers. -/
theorem reference_boundG (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (Q : ℕ)
    (budget : IsQueryBoundP (setupPrefix D A x z >>= T.tail K circuits settings) WorldCounted Q) :
    IsQueryBoundP (worldRoles.adversary (aimedEarlyProgram D A x z h parts) >>=
      referenceTailG K circuits settings D T prims h normal parts) WorldCounted Q := by
  simp only [setupPrefix, bind_assoc] at budget
  simp only [aimedEarlyProgram, LifetimeKeygenCapQuiet.adversary_bind, bind_assoc]
  apply LifetimeReferenceBudget.bound_bind_mono WorldCounted
    (worldRoles.adversary (A.start (corruptInputs D x) z)) _ _ (fun state n hs => ?_) Q budget
  have picked := LifetimeReferenceBudget.bound_after_free (prssInitialData D) _
    (prssDataMask D (prssDataAt h parts))
    (LifetimeReferenceBudget.initialData_supported D h parts) n hs
  simp only [prssEarlyDataRounds_mask, prssEarlyDataRounds_at] at picked
  apply LifetimeReferenceBudget.bound_bind_mono WorldCounted
    (worldRoles.adversary (prssEarlyRounds D A state h parts)) _ _ (fun r n hr => ?_) n picked
  rcases r with ⟨state', sent, _ | revealed⟩
  · exact isQueryBoundP_pure _ _ _
  · simp only [bind_assoc, pure_bind, LifetimeReferenceBudget.revealRows_mask, prssDataAt] at hr
    have chosen := LifetimeReferenceBudget.bound_after_free
      (prssRevealRows D (prssCommitActive D sent) parts
        (prssCommitInbox D (prssDataAt h parts) sent) revealed)
      (fun rows => T.tail K circuits settings (state', some rows))
      (LifetimeReferenceBudget.referenceRows prims D h normal (prssCommitActive D sent) parts sent revealed)
      (LifetimeReferenceBudget.referenceRows_supported prims D h normal (prssCommitActive D sent)
        parts sent revealed) n hr
    exact chosen

theorem referenceBudgetG (Q : ℕ)
    (budget : IsQueryBoundP (setupPrefix D A x z >>= T.tail K circuits settings) WorldCounted Q) :
    ReferenceBudgetG prims K circuits settings D A T x z Q :=
  fun h normal parts => reference_boundG prims K circuits settings D A T x z h normal parts Q budget

/-- The full setup cache is carried into the actual tail's lazy flag experiment. -/
def lazyBoundaryG : ProbComp
    (((A.State × Option (RevealRows C)) × HashCache C) × (Bool × ((HashCache C × KeyCache C) × Bool))) := do
  let r ← worldRun prims (setupPrefix D A x z)
  (fun y => (r, y)) <$> (simulateQ (lazyAimedImpl prims D (rowsOf r.1.2))
    (T.tail K circuits settings r.1)).run ((r.2, ∅), false)

omit [Fintype E] [DecidableEq E] in
/-- Port of LifetimeJointHop.flagProgram_projection (697); no boundary cache is discarded. -/
theorem flagProgramG_projection :
    𝒟[(simulateQ (lazyKeyWorld prims D) (flagProgramG K circuits settings D A T x z)).run' (∅, ∅)] =
    𝒟[(fun y => (y.1.1, (y.2.1, y.2.2.2))) <$>
      lazyBoundaryG prims K circuits settings D A T x z] := by
  simp only [flagProgramG, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, lazyBoundaryG]
  rw [evalDist_bind, evalDist_lazyKeyWorld_noFreeStream prims D _ (qb0_setupPrefix D A x z)]
  simp only [evalDist_map, bind_map_left, evalDist_bind, worldRun]
  congr 1
  funext r
  rw [run_aimedFlagQueries]
  simp only [evalDist_map, Functor.map_map, lazyAimedImpl]

include lawful in
/-- The numerical flag bound uses the original complete setup-and-tail path budget. -/
theorem flagBoundG (Q : ℕ)
    (budget : IsQueryBoundP (setupPrefix D A x z >>= T.tail K circuits settings) WorldCounted Q) :
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ y.2.2.2 = true |
      lazyBoundaryG prims K circuits settings D A T x z] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have h := flagProgram_bound_pathG prims K circuits settings D A T x z lawful Q
    (referenceBudgetG prims K circuits settings D A T x z Q budget)
  rw [probEvent_congr_evalDist (flagProgramG_projection prims K circuits settings D A T x z),
    probEvent_map] at h
  exact h

/-- The fixed selected ceremony recovers LifetimeReferenceBudget.flagProgram_bound
from the generic bound, with exactly its original joint-game budget. -/
theorem selected_flagProgram_bound (pre : LifetimeBridge.Selector C)
    (Z : Distinguisher C A.State TreeOutput) (Q : ℕ)
    (budget : IsQueryBoundP (LifetimeBridge.jointGame K circuits settings false D pre A Z)
      WorldCounted Q) :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
      (simulateQ (lazyKeyWorld prims D)
        (LifetimeJointHop.flagProgram K circuits settings D pre A Z)).run' (∅, ∅)] ≤
      ((3 * Q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let keys : C.Party → Keys C := dealtKeys 0 (fun _ => 0) (fun _ => 0)
  have hs := LifetimeJointHop.setup_eq_remember D pre A keys []
  have hb : IsQueryBoundP
      (setupPrefix D (LifetimeJointHop.remember D pre A) keys [] >>=
        (selectedDriver D A circuits settings Z).tail K circuits settings) WorldCounted Q := by
    rw [← hs, funext (selectedDriver_tail D A K circuits settings Z)]
    change IsQueryBoundP (LifetimeJointHop.setup D pre A >>=
      LifetimeJointHop.tail K circuits settings D A Z) WorldCounted Q
    rwa [← LifetimeJointHop.jointGame_eq_setup K circuits settings D pre A Z]
  have h := flagBoundG prims K circuits settings D (LifetimeJointHop.remember D pre A)
    (selectedDriver D A circuits settings Z) keys []
    (selectedDriver_lawful D A circuits settings Z) Q hb
  have he : lazyBoundaryG prims K circuits settings D (LifetimeJointHop.remember D pre A)
      (selectedDriver D A circuits settings Z) keys [] =
      LifetimeJointHop.lazyBoundary prims K circuits settings D pre A Z := by
    unfold lazyBoundaryG LifetimeJointHop.lazyBoundary
    rw [← hs]
    dsimp only [LifetimeJointHop.remember]
    simp only [selectedDriver_tail]
  rw [he] at h
  rw [probEvent_congr_evalDist (LifetimeJointHop.flagProgram_projection prims K circuits settings D pre A Z),
    probEvent_map]
  exact h

end ThresholdLeanXmssSecurity.LifetimeTailFlagBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagProgramG_fullParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagProgramG_fullParts

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.tail_log_boundG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.tail_log_boundG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.actual_total_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.actual_total_leG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagProgram_bound_pathG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagProgram_bound_pathG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.referenceBudgetG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.referenceBudgetG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagProgramG_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagProgramG_projection

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagBoundG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.flagBoundG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailFlagBound.selected_flagProgram_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailFlagBound.selected_flagProgram_bound
