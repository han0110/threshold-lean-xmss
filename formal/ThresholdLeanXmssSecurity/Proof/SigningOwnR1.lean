import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SeedHit

/-!
# The R1 monitor with a stop at a second opening

`stopRisk` is the risk of the R1 monitor until the cache holds a second opening of a commitment,
and `0` after it. A world call raises it by `2^-128` only at a keyed input that is not in the cache.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnR1

open SigningHitLaneProof SigningCostProof SigningFlatProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The R1 potential with a stop at the first second opening of a commitment. -/
def stopRisk (x : Keys3 C) (cache : HashCache C) (m : SigningPartnerBoundProof.Monitor) : ℝ≥0∞ :=
  if SigningGuessProof.AlternativeCommitment x.2.1 x.1 cache then 0 else m.risk

/-- The unit of a keyed world call on an input that is not in the cache. -/
def freshKeyedCost (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (cache : HashCache C) : (WorldSpec C).Domain → ℕ
  | .inl (.inl (.inr (.inl (.hash input)))) =>
      if (keyOf input).isSome ∧ cache (.hash input) = none then 1 else 0
  | .inr (.inr (.inl (.hash input))) =>
      if (keyOf input).isSome ∧ cache (.hash input) = none then 1 else 0
  | _ => 0

/-- A world call is a call of `H` on a cached input. -/
def CachedHashCall (cache : HashCache C) (t : (WorldSpec C).Domain) : Prop :=
  ∃ input, (t = .inl (.inl (.inr (.inl (.hash input)))) ∨ t = .inr (.inr (.inl (.hash input)))) ∧
    cache (.hash input) ≠ none

theorem keyedCost_le_freshKeyedCost (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (cache : HashCache C) (t : (WorldSpec C).Domain) (hc : ¬CachedHashCall cache t) :
    SigningPartnerBoundProof.keyedCost keyOf t ≤ freshKeyedCost keyOf cache t := by
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]
  · cases q with
    | hash input =>
      have hn : cache (.hash input) = none := Classical.byContradiction fun h => hc ⟨input, Or.inl rfl, h⟩
      simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost, hn]
    | _ => simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]
  · simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]
  · simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]
  · simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]
  · cases q with
    | hash input =>
      have hn : cache (.hash input) = none := Classical.byContradiction fun h => hc ⟨input, Or.inr rfl, h⟩
      simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost, hn]
    | _ => simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]
  · simp [SigningPartnerBoundProof.keyedCost, freshKeyedCost]

/-- `logged_query_risk_le` with the stop and with no charge at a cached input. -/
theorem logged_query_stopRisk_le (x : Keys3 C)
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (t : (WorldSpec C).Domain)
    (l : LoggedState C) (m : SigningPartnerBoundProof.Monitor)
    (hcov : SigningFlatEagerProof.CacheSeen l.1.1 m) (ht : ¬IsProgram t) :
    ∑' z, Pr[= z | (loggedImpl prims t).run l] * stopRisk x z.2.1.1
        (SigningFlatEagerProof.queryEntryStep keyOf m (SigningPartnerBoundProof.hashEntry ⟨t, z.1⟩)) ≤
      stopRisk x l.1.1 m + (2 ^ 128 : ℝ≥0∞)⁻¹ * (freshKeyedCost keyOf l.1.1 t : ℝ≥0∞) := by
  by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 l.1.1
  · refine (SigningPartnerBoundProof.tsum_probOutput_mul_le_of_const _ _ 0 fun z hz => ?_).trans zero_le
    have hle : l.1.1 ≤ z.2.1.1 := by
      simp only [loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact SigningCacheProof.countImpl_grows prims t l.1 y hy
    simp only [stopRisk, if_pos (SigningGuessProof.alternativeCommitment_mono _ _ _ _ hle halt), le_refl]
  rw [stopRisk, if_neg halt]
  have hpt : ∀ (cache : HashCache C) (n : SigningPartnerBoundProof.Monitor), stopRisk x cache n ≤ n.risk := by
    intro cache n
    unfold stopRisk
    split_ifs
    · exact zero_le
    · exact le_rfl
  refine (ENNReal.tsum_le_tsum fun z => mul_le_mul_right (hpt _ _) _).trans ?_
  by_cases hc : CachedHashCall l.1.1 t
  · obtain ⟨input, ht', hin⟩ := hc
    refine (SigningPartnerBoundProof.tsum_probOutput_mul_le_of_const _ _ m.risk fun z _ => ?_).trans le_self_add
    have hseen := hcov input hin
    rcases ht' with rfl | rfl <;>
      simp only [SigningPartnerBoundProof.hashEntry, SigningFlatEagerProof.queryEntryStep] <;>
      rw [SigningPartnerBoundProof.Monitor.step_of_seen _ _ _ hseen]
  · refine (SigningFlatEagerProof.logged_query_risk_le prims keyOf t l m hcov ht).trans ?_
    gcongr
    exact keyedCost_le_freshKeyedCost keyOf l.1.1 t hc

end SigningOwnR1

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnR1.keyedCost_le_freshKeyedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnR1.keyedCost_le_freshKeyedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnR1.logged_query_stopRisk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnR1.logged_query_stopRisk_le
