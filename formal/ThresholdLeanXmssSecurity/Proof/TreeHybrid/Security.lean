import ThresholdLeanXmssSecurity.Proof.TreeHybrid.Bottom

/-!
# One tree in the hybrid model of GS20

`treeHybridSecurity` gives `TreeHybridSecurityStatement` with the simulator `treeHybridSimulator`.
The count of the ideal run is `tree_queryBound`. The distance is `top_distance` for the top tree and
`bottom_distance` for a bottom tree.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The ceremonies of one tree securely compute `F_tree` with selective abort in the
`{F_mult, F_multVerify}`-hybrid model (GS20, Theorem 2). -/
theorem treeHybridSecurity (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    TreeHybridSecurityStatement prims K circuits settings := by
  intro hsize top tree D A
  refine ⟨treeHybridSimulator K circuits settings D A tree, fun x z Z q hx hq => ?_⟩
  obtain ⟨parameter, seeds, pairKeys, hx⟩ := hx
  have hfuel := treeFuel_claim circuits settings tree
  refine ⟨tree_queryBound prims K circuits settings D A hsize x z top tree Z _ q hfuel hq, ?_⟩
  cases tree with
  | top => exact top_distance prims K circuits settings D A hsize hx z top Z _ q hfuel hq
  | bottom b => exact bottom_distance prims K circuits settings D A hsize hx z top b Z _ q hfuel hq

end ThresholdLeanXmssSecurity
