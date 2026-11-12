import ThresholdLeanXmssSecurity.Proof.LifetimeJointKey

/-!
# Adaptive ceremony selection through the PRSS key hop

The selecting prefix and its chosen keys, top tree, tree and auxiliary input remain in one
experiment. Fresh PRSS parts are sampled independently, and the early reference program retains
the chosen input through both setup rounds. Its tail uses that same choice.

`jointKeyHopFrom` establishes `LifetimeBridge.JointKeyHopFrom` with `keySplit C`. The
selector may see every dealer key: the protected stream keys come from fresh ceremony PRSS.
The proof charges setup collisions, hits already in the prefix cache and later aimed calls.
It uses one reduction of the original joint run and the unchanged `q0 + q` budget.

For `LifetimeBridge.JointSimulationFromComponent`, the fixed-input simulation distance
does not supply a coupling that survives oracle-dependent selection. A contextual coupling must
retain the selector and cache in the simulation stages and the hash/check event estimates;
conditioning on selected metadata would not establish that argument. The D19 lifetime-reduction
and lifetime budget interfaces are separate from this selected-ceremony interface.

This extends the eager-refresh argument of `TreeKeyAimed`; it never conditions a fixed-tree
probability bound on the selector's output. The pinned and current leanVM bridge and adaptive
guessing modules were searched first; the existing threshold private-shift and refresh lemmas
cover the additional PRSS domains and are reused below. The lifetime scheduler is not part of this interface.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace ThresholdLeanXmssSecurity.LifetimeJointHop

open LifetimeBridge

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

abbrev Early (A : Adversary C E (Keys C) PEmpty PEmpty) :=
  A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)

/-- Actual adaptive selection, followed by the same adversary's two PRSS setup rounds. -/
def early (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) : OracleComp (LocalSpec C) (JointInput C × Early A) := do
  let input ← jointPrefix pre
  let r ← aimedEarlyProgram D A input.1 input.2.2.2 h parts
  pure (input, r)

theorem early_exposed (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) :
    early D pre A h (keygenExposedParts D parts) = early D pre A h parts := by
  simp only [early, aimedEarlyProgram_exposed]

theorem early_hashAt (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) :
    early D pre A (prssHashAt prims h) parts = early D pre A h parts := by
  simp only [early, aimedEarlyProgram_hashAt]

include prims in
theorem early_refresh (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) :
    early D pre A (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts =
      early D pre A (prssExtend S a) parts := by
  simp only [early, aimedRefresh_early prims]

theorem early_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (q0 start step : ℕ)
    (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (early D pre A h parts) Counted (q0 + start + 2 * step) := by
  unfold early
  refine (isQueryBoundP_bind (m := start + 2 * step + 0) hpre (fun input _ => ?_)).mono (by omega)
  refine isQueryBoundP_bind (m := 0) ?_ (fun r _ => isQueryBoundP_pure _ _ 0)
  exact isQueryBoundP_bind (hstart _ _) (fun state _ =>
    aimedEarlyRounds_bound D A state h parts step hround)

def prefixHit (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (u : KeygenFresh C) : ℝ≥0∞ :=
  Pr[fun r => ∃ v ∈ r.2, AimedPrefixCell D parts u v |
    simulateQ (prssLocalAt prims h) (keygenHashLog (early D pre A h parts))]

/-- The complete prefix allowance survives adaptive selection and both setup rounds. -/
theorem prefixHit_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (h : Query C → HashOutput)
    (q0 start step : ℕ) (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (KeygenFresh C)) (prefixHit prims D pre A h parts)) ≤
      (((q0 + start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold prefixHit
  rw [aimedMean_parts_event]
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by rw [early_exposed]))
  intro parts r hr
  apply aimedSetupLog_length_le _ _ _ r (support_simulateQ_subset _ _ hr)
  apply IsQueryBoundP.of_imp (p' := Counted) _
    (early_bound D pre A h parts q0 start step hpre hstart hround)
  intro t ht
  rcases t with n | v | a
  · exact ht.elim
  · cases v <;> simp_all [aimedLocalSetup, aimedSetupQuery, Counted]
  · exact ht.elim

def referenceTail (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : JointInput C × Early A) : OracleComp (WorldSpec C) Bool :=
  aimedReferenceTail prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z h normal parts r.2

def tailLog (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) : ProbComp (Bool × List (Query C)) := do
  let r ← simulateQ (prssLocalAt prims h) (early D pre A h parts)
  simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
    (referenceTail prims K circuits settings D A Z h normal parts r)))

/-- The adaptive reference tail is private-shift invariant. Its metadata need not be independent
of the public oracle; they are chosen inside the same invariant kernel. -/
theorem tailLog_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (h : Query C → HashOutput) (keys : KeyName C × HashOutput → Digest)
    (normal : KeyName C → HashOutput) (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v | (do
      let r ← keygenPartsKernel (tailLog prims K circuits settings D pre A Z h keys normal)
      let u ← $ᵗ (KeygenFresh C)
      pure (r, u))] ≤
      ((((ceremonyFuel circuits settings - 2) * step + final) * prssKeyCount C : ℕ) : ℝ≥0∞) /
        2 ^ 256 := by
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by
      simp only [tailLog, early_exposed, referenceTail, aimedReferenceTail_exposed]))
  intro parts out hout
  simp only [tailLog, support_bind, Set.mem_iUnion] at hout
  obtain ⟨r, _, hr⟩ := hout
  exact aimedSetupLog_length_le _ _
    (aimedKeyLocal_setup_bound prims D keys _ _
      (aimedReferenceTail_bound prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z h
        normal parts r.2 step final hround hfinal)
      (aimedReferenceTail_noSetup prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z h
        normal parts r.2)) out (support_simulateQ_subset _ _ hr)

def tailHit (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : JointInput C × Early A) (u : KeygenFresh C) : ℝ≥0∞ :=
  aimedTailHit prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z h normal parts r.2 u

def referenceError (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (h : Query C → HashOutput) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) : ℝ≥0∞ :=
  aimedMean ($ᵗ (KeygenFresh C)) (prefixHit prims D pre A h parts) +
  aimedMean (simulateQ (prssLocalAt prims h) (early D pre A h parts)) (fun r =>
    aimedMean ($ᵗ (KeygenFresh C)) (tailHit prims K circuits settings D A Z h normal parts r))

theorem referenceError_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (h : Query C → HashOutput) (normal : KeyName C → HashOutput) (q0 start step final : ℕ)
    (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (referenceError prims K circuits settings D pre A Z h normal) ≤
      (((q0 + start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      ((((ceremonyFuel circuits settings - 2) * step + final) * prssKeyCount C : ℕ) : ℝ≥0∞) /
        2 ^ 256 := by
  unfold referenceError
  rw [aimedMean_add]
  apply add_le_add
  · exact prefixHit_bound prims D pre A h q0 start step hpre hstart hround
  · unfold tailHit aimedTailHit
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
    have hb := tailLog_bound prims K circuits settings D pre A Z h keys normal step final hround hfinal
    rw [← aimedMean_parts_event
      (tailLog prims K circuits settings D pre A Z h keys normal)
      (fun parts u out => ∃ v ∈ out.2, AimedPrefixCell D parts u v)] at hb
    unfold tailLog referenceTail at hb
    simp only [← aimedMean_probEvent] at hb
    simpa only [aimedMean_comm ($ᵗ (KeygenFresh C))] using hb

def finish (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (r : JointInput C × Early A) : ℝ≥0∞ :=
  aimedFinishProbability prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z h
    (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r.2)

def actualProbability (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) : ℝ≥0∞ :=
  aimedMean (simulateQ (prssLocalAt prims h) (early D pre A h parts))
    (finish prims K circuits settings D A Z h parts)

theorem actualProbability_le_one (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    actualProbability prims K circuits settings D pre A Z h parts ≤ 1 :=
  aimedMean_le_const _ _ _ (fun _ => probEvent_le_one)

theorem actualProbability_refresh (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S) (hc : ¬ KeygenClash D parts) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts) =
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      aimedMean ($ᵗ (S → HashOutput)) (fun echo =>
        actualProbability prims K circuits settings D pre A Z
          (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts))) := by
  unfold actualProbability finish aimedFinishProbability
  simp only [aimedMean_probEvent]
  apply probEvent_congr_evalDist
  exact evalDist_aimedRefresh D S parts hmem hc _

theorem actualProbability_prefix_le (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) :
    let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
    actualProbability prims K circuits settings D pre A Z h parts ≤
      aimedMean (simulateQ (prssLocalAt prims (prssExtend S a))
        (early D pre A (prssExtend S a) parts)) (finish prims K circuits settings D A Z h parts) +
      prefixHit prims D pre A (prssExtend S a) parts u := by
  dsimp only
  unfold actualProbability finish aimedFinishProbability prefixHit
  rw [early_refresh prims]
  simp only [aimedMean_probEvent, aimed_prssLocalAt_eq]
  exact probEvent_aimedPrefix_swap_le prims _ _ (AimedPrefixCell D parts u)
    (aimedRefresh_off prims D S parts hmem a echo u) _ _ _

section PartsComparison

attribute [local irreducible] actualProbability finish referenceError tailHit prefixHit

/-- The pointwise tail estimate applies after the reference prefix has selected its metadata. -/
theorem actualProbability_parts_le (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (S : Finset (Query C)) (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (step final : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      referenceError prims K circuits settings D pre A Z
        (prssHashAt prims (prssExtend S a)) normal parts) := by
  rw [actualProbability_refresh prims K circuits settings D pre A Z S parts hmem hc,
    aimedMean_comm]
  rw [← aimedMean_const ($ᵗ (S → HashOutput))
    (((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
      (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256),
    ← aimedMean_add]
  apply aimedMean_mono
  intro a
  have hp := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => actualProbability_prefix_le prims K circuits settings D pre A Z S parts hmem a echo u))
  simp only [aimedMean_add, aimedMean_const] at hp
  let initial := simulateQ (prssLocalAt prims (prssExtend S a))
    (early D pre A (prssExtend S a) parts)
  have hf := aimedMean_mono initial (fun r => aimedRefresh_finish_mean_le prims K circuits settings
    r.1.2.1 r.1.2.2.1 D A r.1.1 Z S normal parts hmem hsk hc a r.2 step final hni hn0 hround hfinal)
  simp only [aimedMean_add, aimedMean_const] at hf
  have hmove {f : KeygenFresh C → (S → HashOutput) → (JointInput C × Early A) → ℝ≥0∞} :
      aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput))
        (fun echo => aimedMean initial (f u echo))) =
      aimedMean initial (fun r => aimedMean ($ᵗ (KeygenFresh C))
        (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo => f u echo r))) := by
    simp_rw [aimedMean_comm ($ᵗ (S → HashOutput)) initial]
    rw [aimedMean_comm]
  rw [hmove] at hp
  unfold finish at hp
  have hb := hp.trans (add_le_add hf le_rfl)
  unfold referenceError tailHit prefixHit
  unfold prefixHit at hb
  simp only [early_hashAt, aimed_prssLocalAt_hashAt]
  exact hb.trans_eq ((add_right_comm _ _ _).trans (add_assoc _ _ _))

end PartsComparison

/-- The complete adaptive eager aimed-call estimate, with the selector charged in the start. -/
theorem actualProbability_total_le (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (S : Finset (Query C)) (normal : KeyName C → HashOutput)
    (hmem : ∀ parts n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (q0 start step final : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts)) ≤
      (((q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) *
        prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let cost : ℝ≥0∞ :=
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256
  have hp (parts : C.Party → Parts C) :
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts) ≤
      (if KeygenClash D parts then 1 else 0) + (cost + aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        referenceError prims K circuits settings D pre A Z
          (prssHashAt prims (prssExtend S a)) normal parts)) := by
    by_cases hc : KeygenClash D parts
    · rw [if_pos hc]
      exact (aimedMean_le_const _ 1 _ (fun a => actualProbability_le_one prims K circuits settings
        D pre A Z _ parts)).trans (le_add_right le_rfl)
    · rw [if_neg hc, zero_add]
      exact actualProbability_parts_le prims K circuits settings D pre A Z S normal parts
        (hmem parts) hsk hc step final hni hn0 hround hfinal
  have hb := aimedMean_mono (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) hp
  simp only [aimedMean_add, aimedMean_const, aimedMean_event] at hb
  have hc : Pr[KeygenClash D | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] ≤
      (keygenClashCount C : ℝ≥0∞) / 2 ^ 256 := by
    simpa only [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using probEvent_keygenClash_le D
  have he : aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a => referenceError prims K circuits settings
        D pre A Z (prssHashAt prims (prssExtend S a)) normal parts)) ≤
      (((q0 + start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((((ceremonyFuel circuits settings - 2) * step + final) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun a => referenceError_bound prims K circuits settings D pre A Z
      (prssHashAt prims (prssExtend S a)) normal q0 start step final hpre hstart hround hfinal)
  refine (hb.trans (add_le_add hc (add_le_add le_rfl he))).trans ?_
  dsimp only [cost]
  simp only [← ENNReal.add_div]
  gcongr
  norm_cast
  simpa only [Nat.add_assoc] using
    aimed_total_error_arith (C := C) (q0 + start) step final (ceremonyFuel circuits settings)

/-- The original selected ceremony, with only the aimed-call flag added after PRSS derivation. -/
def flagProgram (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (WorldSpec C) ((A.State × Option (RevealRows C)) × (Bool × Bool)) := do
  let input ← worldRoles.adversary (jointPrefix pre)
  aimedFlagProgram K circuits settings input.2.1 input.2.2.1 D A input.1 input.2.2.2 Z

theorem flagProgram_noProgram (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (flagProgram K circuits settings D pre A Z) AimedProgramCall 0 :=
  qb0_bind (aimed_noProgram_adversary _) (fun input =>
    aimed_noProgram_flagProgram K circuits settings input.2.1 input.2.2.1 D A input.1 input.2.2.2 Z)

/-- Full parts can be sampled before the entire selecting prefix, while the prefix continues
to use the same eager oracle table as the selected ceremony. -/
theorem flagProgram_fullParts (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (keys : KeyName C × HashOutput → Digest) (h : Query C → HashOutput) :
    𝒟[simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
      (flagProgram K circuits settings D pre A Z))] =
    𝒟[do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let r ← simulateQ (prssLocalAt prims h) (early D pre A h parts)
      aimedEagerFinish prims K circuits settings r.1.2.1 r.1.2.2.1 D A r.1.1 Z keys h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r.2)] := by
  simp only [flagProgram, simulateQ_bind, aimedKeyLocal_adversary]
  trans 𝒟[do
    let input ← simulateQ (prssLocalAt prims h) (jointPrefix pre)
    let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
    let state ← simulateQ (prssLocalAt prims h) (A.start (corruptInputs D input.1) input.2.2.2)
    let r ← simulateQ (prssLocalAt prims h) (prssEarlyRounds D A state h parts)
    aimedEagerFinish prims K circuits settings input.2.1 input.2.2.1 D A input.1 Z keys h
      (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)]
  · apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro input
    exact evalDist_aimedFlagProgram_at_fullParts prims K circuits settings input.2.1 input.2.2.1
      D A input.1 input.2.2.2 Z keys h
  · rw [evalDist_bind_bind_swap]
    simp only [early, aimedEarlyProgram, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]

theorem eagerProbability_eq (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (S : Finset (Query C)) :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true | (do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h)) (simulateQ (aimedKeyLocal prims D keys)
        (flagProgram K circuits settings D pre A Z)))] =
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        actualProbability prims K circuits settings D pre A Z (prssExtend S a) parts)) := by
  have he (keys : KeyName C × HashOutput → Digest) (a : S → HashOutput) :=
    probEvent_congr_evalDist (flagProgram_fullParts prims K circuits settings D pre A Z keys
      (prssExtend S a)) (fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true)
  simp only [← aimedMean_probEvent] at he ⊢
  simp_rw [he]
  rw [aimedMean_comm]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))]
  rw [aimedMean_comm]
  unfold actualProbability finish aimedFinishProbability
  simp only [← aimedMean_probEvent]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (simulateQ (prssLocalAt prims _) (early D pre A _ _))]

/-- Eager sampling covers the full adaptive program, not a selected branch sampled anew. -/
theorem flagProgram_eager_cover (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (cover : Finset (Query C)) :
    ∃ S : Finset (Query C), cover ⊆ S ∧
    𝒟[(simulateQ (lazyKeyWorld prims D) (flagProgram K circuits settings D pre A Z)).run' (∅, ∅)] =
    𝒟[do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h)) (simulateQ (aimedKeyLocal prims D keys)
        (flagProgram K circuits settings D pre A Z))] := by
  let game := flagProgram K circuits settings D pre A Z
  have hg : IsQueryBoundP game AimedProgramCall 0 := flagProgram_noProgram K circuits settings D pre A Z
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

/-- The adaptive aimed-call estimate on the actual lazy key world. -/
theorem flagProgram_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 start step final : ℕ) (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
      (simulateQ (lazyKeyWorld prims D) (flagProgram K circuits settings D pre A Z)).run' (∅, ∅)] ≤
      (((q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) *
        prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  by_cases hm : prssKeyCount C < 2 ^ 256
  · obtain ⟨normal, hni, hn0⟩ := aimed_normalTable_exists D hm
    obtain ⟨cover, hcanonical, hecho⟩ := aimedCover_exists (C := C)
    obtain ⟨S, hS, he⟩ := flagProgram_eager_cover prims K circuits settings D pre A Z cover
    rw [probEvent_congr_evalDist he, eagerProbability_eq]
    exact actualProbability_total_le prims K circuits settings D pre A Z S normal
      (fun parts n _ => hS (hcanonical parts n)) (fun i j f => hS (hecho i j f))
      q0 start step final hni hn0 hpre hstart hround hfinal
  · have hm' : 2 ^ 256 ≤ prssKeyCount C := Nat.le_of_not_gt hm
    have hn : 2 ^ 256 ≤
        (q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) *
          prssKeyCount C + 4 * prssKeyCount C ^ 2 := by
      nlinarith [Nat.zero_le ((q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) *
        step + 3 * final) * prssKeyCount C)]
    calc
      _ ≤ 1 := probEvent_le_one
      _ = (2 ^ 256 : ℝ≥0∞) / 2 ^ 256 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast hn) _

/-- Keep the chosen metadata in the adversary state during setup. The supplied fixed inputs are
ignored by `start`; the actual dealer-and-selector prefix runs exactly once. -/
def remember (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) : Adversary C E (Keys C) PEmpty PEmpty where
  State := JointInput C × A.State
  start _ _ := do
    let input ← jointPrefix pre
    let state ← A.start (corruptInputs D input.1) input.2.2.2
    pure (input, state)
  round state sent := (fun r => ((state.1, r.1), r.2)) <$> A.round state.2 sent
  answer _ input := input.elim

def rememberedZ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    Distinguisher C (remember D pre A).State TreeOutput := fun r => Z (r.1.2, r.2)

theorem remember_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (fuel q0 q : ℕ) (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hq : IsQueryBounded A Z fuel q) :
    IsQueryBounded (remember D pre A) (rememberedZ D pre A Z) fuel (q0 + q) := by
  obtain ⟨start, step, final, ht, hs, hr, _, hz⟩ := hq
  refine ⟨q0 + start, step, final, by omega, ?_, ?_, ?_, ?_⟩
  · intro x z
    exact isQueryBoundP_bind hpre (fun input _ => by
      exact (isQueryBoundP_bind (m := 0) (hs (corruptInputs D input.1) input.2.2.2)
        (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega))
  · intro state sent
    exact (isQueryBoundP_map_iff _ _ _).mpr (hr state.2 sent)
  · intro state input
    exact input.elim
  · intro r
    exact hz _

theorem remember_rounds (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (input : JointInput C) (state : A.State)
    (data : C.Party → Parts C × List HashOutput) :
    prssEarlyDataRounds D (remember D pre A) (input, state) data =
      (fun r => ((input, r.1), r.2)) <$> prssEarlyDataRounds D A state data := by
  simp only [prssEarlyDataRounds, remember, bind_map_left, map_bind]
  apply bind_congr
  intro r
  split_ifs <;> simp only [map_pure, map_bind]

def setup (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) :
    OracleComp (WorldSpec C) ((JointInput C × A.State) × Option (RevealRows C)) := do
  let input ← worldRoles.adversary (jointPrefix pre)
  (fun r => ((input, r.1), r.2)) <$> setupPrefix D A input.1 input.2.2.2

theorem setup_eq_remember (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    setup D pre A = setupPrefix D (remember D pre A) x z := by
  unfold setup setupPrefix
  rw [show (remember D pre A).start (corruptInputs D x) z = (do
    let input ← jointPrefix pre
    let state ← A.start (corruptInputs D input.1) input.2.2.2
    pure (input, state)) from rfl]
  simp only [map_bind, adversary_bind, worldRoles_adversary_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro input
  apply bind_congr
  intro state
  apply bind_congr
  intro data
  rw [remember_rounds]
  simp only [map_eq_bind_pure_comp, Function.comp_def, adversary_bind,
    worldRoles_adversary_pure, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨st, sent, _ | revealed⟩ <;> simp only [bind_assoc, pure_bind]

theorem setup_noFreeStream (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) : IsQueryBoundP (setup D pre A) FreeStream 0 := by
  unfold setup
  refine qb0_bind (qb0_adversary _) fun input => ?_
  rw [map_eq_bind_pure_comp]
  exact qb0_bind (qb0_setupPrefix D A input.1 input.2.2.2) fun _ => by simp

/-- Boundary collisions retain the original component constant and the full prefix budget. -/
theorem setup_keysApart_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (hbatch : 0 < settings.batchSize)
    (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setup D pre A)]).toReal ≤
      streamKeyError C + (((q0 + q) * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256 := by
  rw [setup_eq_remember D pre A (dealtKeys 0 (fun _ => 0) (fun _ => 0)) []]
  exact treeKeysApartBound prims circuits settings hbatch D (remember D pre A) _ []
    (rememberedZ D pre A Z) (q0 + q) ⟨0, (fun _ => 0), (fun _ => 0), fun _ => rfl⟩
    (remember_bound D pre A Z _ q0 q hpre hq)

/-- Cached hidden stream-key hits at the actual adaptive setup boundary. -/
theorem setup_keyHit_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (q0 start step : ℕ)
    (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | worldRun prims (setup D pre A)] ≤
      ((2 * (q0 + start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [setup_eq_remember D pre A (dealtKeys 0 (fun _ => 0) (fun _ => 0)) []]
  apply treeKeyBoundaryHitBound prims D (remember D pre A) _ [] (q0 + start) step
  · exact isQueryBoundP_bind hpre (fun input _ => by
      exact (isQueryBoundP_bind (m := 0) (hstart (corruptInputs D input.1) input.2.2.2)
        (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega))
  · intro state sent
    exact (isQueryBoundP_map_iff _ _ _).mpr (hround state.2 sent)

def tail (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput)
    (r : (JointInput C × A.State) × Option (RevealRows C)) : OracleComp (WorldSpec C) Bool :=
  afterDerivation K circuits settings r.1.1.2.1 r.1.1.2.2.1 D A r.1.1.1 Z (r.1.2, r.2)

theorem jointGame_eq_setup (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    jointGame K circuits settings false D pre A Z =
      setup D pre A >>= tail K circuits settings D A Z := by
  simp only [jointGame, setup, bind_assoc, bind_map_left]
  apply bind_congr
  rintro ⟨keys, top, tree, z⟩
  exact treeRealGame_eq_split K circuits settings top tree D A keys z Z

def boundary (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :=
  worldRun prims (setup D pre A) >>= fun r => (fun y => (r, y)) <$>
    (simulateQ (jointKeyWorld prims D false) (tail K circuits settings D A Z r.1)).run
      (boundaryState r.2)

def lazyBoundary (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :=
  worldRun prims (setup D pre A) >>= fun r => (fun y => (r, y)) <$>
    (simulateQ (lazyAimedImpl prims D (rowsOf r.1.2)) (tail K circuits settings D A Z r.1)).run
      ((r.2, ∅), false)

theorem probBad_eq_boundary (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    probBad_streamKey prims D (jointGame K circuits settings false D pre A Z) =
      (Pr[fun y => y.2.2.bad = true | boundary prims K circuits settings D pre A Z]).toReal := by
  rw [probBad_streamKey_eq_ideal, jointGame_eq_setup, simulateQ_bind, StateT.run_bind,
    jointKeyWorld_false_simulate_eq prims D _ (setup_noFreeStream D pre A)
      keyJointInitial (fun _ => rfl), bind_map_left]
  simp only [boundary, probEvent_bind_eq_tsum, probEvent_map]
  rfl

theorem boundary_bad (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    ∀ y ∈ support (boundary prims K circuits settings D pre A Z), y.2.2.bad = true →
      ¬ KeysApart D (rowsOf y.1.1.2) ∨
        (KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash) := by
  intro y hy hbad
  simp only [boundary, support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hy
  obtain ⟨r, _, w, hw, rfl⟩ := hy
  by_cases hg : KeysApart D (rowsOf r.1.2)
  · right
    refine ⟨hg, ?_⟩
    have h := jointKeyWorld_run_inv prims D (rowsOf r.1.2) hg _
      (afterDerivationAllowed K circuits settings r.1.1.1.2.1 r.1.1.1.2.2.1 D A r.1.1.1.1 Z
        (r.1.1.2, r.1.2)) (boundaryState r.2) (jointInv_boundaryState D _ _) w hw
    exact h.1.2 hbad
  · exact Or.inl hg

theorem boundary_afterHit_le_flag (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧
        KeyHit D (rowsOf y.1.1.2) y.2.2.hash | boundary prims K circuits settings D pre A Z] ≤
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ y.2.2.2 = true |
      lazyBoundary prims K circuits settings D pre A Z] := by
  unfold boundary lazyBoundary
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _
  rw [probEvent_map, probEvent_map]
  by_cases hr : KeysApart D (rowsOf r.1.2) ∧ ¬ KeyHit D (rowsOf r.1.2) r.2
  · let game := tail K circuits settings D A Z r.1
    have hb : keyJointIdealProjection (boundaryState r.2) = (r.2, (∅ : KeyCache C)) := by
      simp only [keyJointIdealProjection, boundaryState, Prod.mk.injEq, true_and]
      funext y
      rfl
    rw [← hb, ← probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_aimedImpl_projection prims D (rowsOf r.1.2) game (boundaryState r.2) false),
      probEvent_map]
    rw [← probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_flagImpl_fst (jointKeyWorld prims D false)
        (fun t (_ : Unit) => AimedCall D (rowsOf r.1.2) t) () game (boundaryState r.2) false),
      probEvent_map]
    apply probEvent_mono
    intro y hy hhit
    refine ⟨hr.1, ?_⟩
    by_contra hf
    have h := aimedImpl_run_noKeyHit prims D (rowsOf r.1.2) hr.1 game
      (afterDerivationAllowed K circuits settings r.1.1.1.2.1 r.1.1.1.2.2.1 D A r.1.1.1.1 Z
        (r.1.1.2, r.1.2)) (boundaryState r.2) false y hy (Bool.eq_false_iff.mpr hf)
    exact h.2 hr.2 hhit.2.2
  · exact (probEvent_eq_zero (fun y _ hy => hr ⟨hy.1, hy.2.1⟩)).le.trans zero_le

theorem flagProgram_eq_setup (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    flagProgram K circuits settings D pre A Z = (do
      let r ← setup D pre A
      (fun y => ((r.1.2, r.2), y)) <$>
        (simulateQ (aimedFlagQueries D (rowsOf r.2)) (tail K circuits settings D A Z r)).run false) := by
  simp only [flagProgram, setup, aimedFlagProgram, bind_assoc, bind_map_left, tail]

theorem flagProgram_projection (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    𝒟[(simulateQ (lazyKeyWorld prims D) (flagProgram K circuits settings D pre A Z)).run' (∅, ∅)] =
    𝒟[(fun y => ((y.1.1.1.2, y.1.1.2), (y.2.1, y.2.2.2))) <$>
      lazyBoundary prims K circuits settings D pre A Z] := by
  simp only [flagProgram_eq_setup, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, lazyBoundary]
  rw [evalDist_bind, evalDist_lazyKeyWorld_noFreeStream prims D _ (setup_noFreeStream D pre A)]
  simp only [evalDist_map, bind_map_left, evalDist_bind, worldRun]
  congr 1
  funext r
  rw [run_aimedFlagQueries]
  simp only [evalDist_map, Functor.map_map, lazyAimedImpl]

theorem boundary_hit_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    (Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash |
      boundary prims K circuits settings D pre A Z]).toReal ≤
      ((3 * (q0 + q) * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  obtain ⟨start, step, final, hle, hstart, hround, -, hfinal⟩ := hq
  have hfuel : 2 ≤ ceremonyFuel circuits settings := by unfold ceremonyFuel setupRounds; omega
  generalize hP : boundary prims K circuits settings D pre A Z = P
  have h1 : Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P] ≤
      Pr[fun y => KeyHit D (rowsOf y.1.1.2) y.1.2 | P] +
        Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧
          KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P] :=
    le_trans (probEvent_mono fun y _ hy => by
      by_cases h : KeyHit D (rowsOf y.1.1.2) y.1.2
      · exact Or.inl h
      · exact Or.inr ⟨hy.1, h, hy.2⟩) (probEvent_or_le _ _ _)
  have h2 : Pr[fun y => KeyHit D (rowsOf y.1.1.2) y.1.2 | P] ≤
      Pr[fun r => KeyHit D (rowsOf r.1.2) r.2 | worldRun prims (setup D pre A)] := by
    rw [← hP]
    exact probEvent_pair_fst_le _ _
      (fun r : ((JointInput C × A.State) × Option (RevealRows C)) × HashCache C =>
        KeyHit D (rowsOf r.1.2) r.2)
  have hB := setup_keyHit_bound prims D pre A q0 start step hpre hstart hround
  have hA := boundary_afterHit_le_flag prims K circuits settings D pre A Z
  have he := probEvent_congr_evalDist (flagProgram_projection prims K circuits settings D pre A Z)
    (fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true)
  rw [probEvent_map] at he
  simp only [Function.comp_def] at he
  rw [← he] at hA
  have hF := flagProgram_bound prims K circuits settings D pre A Z q0 start step final
    hpre hstart hround hfinal
  have hAfter := hA.trans hF
  rw [hP] at hAfter
  have hsum : ((2 * (q0 + start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      (((q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) *
        prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((3 * (q0 + q) * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hFuel : (ceremonyFuel circuits settings - 2) * step + 2 * step =
        ceremonyFuel circuits settings * step := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hfuel]
    have hq2 : 2 * (q0 + start + 2 * step) +
        (q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) ≤
        3 * (q0 + q) := by
      have h3 : (3 * (ceremonyFuel circuits settings - 2) + 2) * step =
          3 * ((ceremonyFuel circuits settings - 2) * step) + 2 * step := by ring
      omega
    have hn : 2 * (q0 + start + 2 * step) * prssKeyCount C +
        ((q0 + start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) *
          prssKeyCount C + 4 * prssKeyCount C ^ 2) ≤
        3 * (q0 + q) * prssKeyCount C + 4 * prssKeyCount C ^ 2 := by
      nlinarith [Nat.mul_le_mul_right (prssKeyCount C) hq2]
    rw [← ENNReal.add_div, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (by exact_mod_cast hn) _
  have hE := (h1.trans (add_le_add h2 hAfter)).trans ((add_le_add hB le_rfl).trans hsum)
  have hr := ENNReal.toReal_mono
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)) hE
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
  exact hr

/-- The complete adaptive key-hop bad event, with one prefix budget. -/
theorem probBad_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (hbatch : 0 < settings.batchSize)
    (hpre : IsQueryBoundP (jointPrefix pre) Counted q0)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    probBad_streamKey prims D (jointGame K circuits settings false D pre A Z) ≤
      streamKeyError C + keySplit C (q0 + q) := by
  rw [probBad_eq_boundary]
  generalize hP : boundary prims K circuits settings D pre A Z = P
  have h1 : Pr[fun y => y.2.2.bad = true | P] ≤
      Pr[fun y => ¬ KeysApart D (rowsOf y.1.1.2) | P] +
        Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P] :=
    le_trans (probEvent_mono fun y hy hbad =>
      boundary_bad prims K circuits settings D pre A Z y (hP ▸ hy) hbad)
      (probEvent_or_le _ _ _)
  have h2 : Pr[fun y => ¬ KeysApart D (rowsOf y.1.1.2) | P] ≤
      Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setup D pre A)] := by
    rw [← hP]
    exact probEvent_pair_fst_le _ _
      (fun r : ((JointInput C × A.State) × Option (RevealRows C)) × HashCache C =>
        ¬ KeysApart D (rowsOf r.1.2))
  have hA := setup_keysApart_bound prims circuits settings D pre A Z q0 q hbatch hpre hq
  have hH := boundary_hit_bound prims K circuits settings D pre A Z q0 q hpre hq
  rw [hP] at hH
  have hsum : (((q0 + q) * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256 +
      ((3 * (q0 + q) * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 256 =
      keySplit C (q0 + q) := by
    unfold keySplit
    rw [← add_div]
    congr 1
    push_cast
    ring
  calc (Pr[fun y => y.2.2.bad = true | P]).toReal
      ≤ (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setup D pre A)] +
          Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P]).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
          (h1.trans (add_le_add h2 le_rfl))
    _ = (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setup D pre A)]).toReal +
          (Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P]).toReal :=
        ENNReal.toReal_add probEvent_ne_top probEvent_ne_top
    _ ≤ _ := by rw [← hsum]; linarith

theorem jointError_const (pre : Selector C) (e : ℝ) :
    jointError prims pre (fun _ => e) = e := by
  classical
  letI : DecidableEq (JointInput C × HashCache C) := Classical.decEq _
  simp only [jointError, selectedError, ← Finset.sum_mul]
  rw [← ENNReal.toReal_sum (fun _ _ => probOutput_ne_top),
    sum_finSupport_probOutput_of_liftM_PMF, ENNReal.toReal_one, one_mul]

/-- The exact adaptive key-table hop, for one reduction of the complete joint run. -/
theorem jointKeyHopFrom : JointKeyHopFrom prims K circuits settings (keySplit C) := by
  intro hb D pre A Z q0 q hpre hq
  rw [jointError_const, reductionReal, prfRealExp_prgReduction]
  exact (keyWorld_coupling prims D _).trans
    (probBad_bound prims K circuits settings D pre A Z q0 q hb hpre hq)

/-- With the adaptive simulation hop supplied, no separate key-hop hypothesis remains. -/
theorem jointTreeSecurityDistanceFrom_of_sim
    (hsim : JointSimulationHopFrom prims K circuits settings (keySplit C)) :
    JointTreeSecurityDistanceFrom prims K circuits settings :=
  jointTreeSecurityDistanceFrom_of_hops prims K circuits settings (keySplit C)
    (jointKeyHopFrom prims K circuits settings) hsim

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointHop.flagProgram_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flagProgram_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointHop.probBad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probBad_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointHop.jointKeyHopFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointKeyHopFrom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointHop.jointTreeSecurityDistanceFrom_of_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointTreeSecurityDistanceFrom_of_sim

end ThresholdLeanXmssSecurity.LifetimeJointHop
