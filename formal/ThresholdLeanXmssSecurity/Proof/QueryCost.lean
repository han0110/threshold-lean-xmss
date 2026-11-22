import ThresholdLeanXmss.Statement.RandomOracle

/-! # Query budgets with unit cost on a predicate -/

open OracleComp OracleSpec ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity.SigningStronglyUnforgeable

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

end ThresholdLeanXmssSecurity.SigningStronglyUnforgeable

/-- info: 'ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.isQueryBoundP_iff_queryCostAtMost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.isQueryBoundP_iff_queryCostAtMost
