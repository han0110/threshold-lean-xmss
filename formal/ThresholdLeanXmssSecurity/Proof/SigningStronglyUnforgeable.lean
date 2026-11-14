import ThresholdLeanXmssSecurity.Proof.SigningOwnBudget

/-! # The signing claim in the form of leanXMSS

`stronglyUnforgeable` gives `ThresholdLeanXmssStronglyUnforgeable`
(`ThresholdLeanXmss/Statement/Signing.lean`) from `SigningOwnBudget.signingOwnBudget`.
`stronglyUnforgeable_iff` states that the two claims are equivalent. They differ in the form of the
budget, a cost function or a predicate, and in the form of the bound.
-/

open OracleComp OracleSpec LeanXmss ENNReal

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningStronglyUnforgeable

attribute [local instance] Classical.propDecidable

/-- A count by a predicate is a cost of one for each counted query. -/
theorem isQueryBoundP_iff_queryCostAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) :
    IsQueryBoundP oa p n ↔ QueryCostAtMost oa (fun t => if p t then 1 else 0) n := by
  have canQuery : (fun (t : ι) (b : ℕ) => ¬ p t ∨ 0 < b) = fun t b => (if p t then 1 else 0) ≤ b := by
    funext t b
    by_cases h : p t <;> simp [h, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  have cost : (fun (t : ι) (b : ℕ) => if p t then b - 1 else b) = fun t b => b - (if p t then 1 else 0) := by
    funext t b
    by_cases h : p t <;> simp [h]
  unfold IsQueryBoundP QueryCostAtMost
  rw [canQuery, cost]

variable {C : Committee}

/-- `adversaryCost` counts the queries of `SigningOwnCounted`. -/
theorem adversaryCost_eq :
    (adversaryCost : (LocalSpec C + TsigSpec C).Domain → ℕ) = fun t => if SigningOwnCounted t then 1 else 0 := by
  funext t
  rcases t with (_ | _) | (_ | _ | _ | _) <;> simp [adversaryCost, SigningOwnCounted]

/-- The two forms of the budget of the forger are equivalent. -/
theorem hasSigningOwnBound_iff (A : TsigAdversary C) (q : ℕ) :
    HasSigningOwnBound A q ↔ ∀ pk top, QueryCostAtMost (A pk top) adversaryCost q := by
  unfold HasSigningOwnBound
  rw [adversaryCost_eq]
  exact forall_congr' fun pk => forall_congr' fun top => isQueryBoundP_iff_queryCostAtMost _ _ _

/-- The two forms of the bound are equal. -/
theorem signingHashError_slack (q : ℕ) :
    signingHashError (q + signingSlack) = ((q : ℝ) + securitySlack) / 2 ^ 127 := by
  simp [signingHashError, signingSlack, securitySlack]

/-- The signing claim of the bundle is the claim with the budget `HasSigningOwnBound`. -/
theorem stronglyUnforgeable_iff (prims : Primitives) (C : Committee) :
    ThresholdLeanXmssStronglyUnforgeable prims C ↔ SigningOwnBudgetStatement prims C := by
  unfold ThresholdLeanXmssStronglyUnforgeable StronglyUnforgeable SigningOwnBudgetStatement
  constructor
  · intro h A q hq
    rw [signingHashError_slack]
    exact h q A ((hasSigningOwnBound_iff A q).mp hq)
  · intro h q A hq
    rw [← signingHashError_slack]
    exact h A q ((hasSigningOwnBound_iff A q).mpr hq)

/-- Threshold leanXMSS is strongly unforgeable. -/
theorem stronglyUnforgeable (prims : Primitives) (C : Committee) :
    ThresholdLeanXmssStronglyUnforgeable prims C :=
  (stronglyUnforgeable_iff prims C).mpr (SigningOwnBudget.signingOwnBudget prims C)

end SigningStronglyUnforgeable

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.stronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.stronglyUnforgeable
