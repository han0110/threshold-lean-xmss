import ThresholdLeanXmssSecurity.Base.Reductions

/-!
# The count of an execution

The bound on the counted queries of a run in the world.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

variable {C : Committee} (prims : Primitives)

/-- Every execution makes at most `q` counted queries. In an ideal run these are the calls of the
simulator, which runs the adversary, its programming queries, and the calls of the distinguisher. -/
def HasHashQueryBound {α : Type} (run : ProbComp (α × ℕ)) (q : ℕ) : Prop :=
  ∀ r ∈ support run, r.2 ≤ q

end ThresholdLeanXmss
