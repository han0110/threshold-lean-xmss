import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.SeedShift
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CommitPad

/-!
# The pad does not change the seed generation

The module has the general lemma `getD_zipWith_parties` on the list of the parties.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof


noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The pad on the local oracles -/

/-! ## The commitments -/

theorem getD_zipWith_parties (h : C.Party → HashOutput → HashOutput) (r : List HashOutput)
    (hr : r.length = C.parties.length) (j : C.Party) :
    (List.zipWith h C.parties r).getD j.val 0 = h j (r.getD j.val 0) := by
  have hj : j.val < C.parties.length := by simp [Committee.parties]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
  congr 1
  simp [Committee.parties]

/-! ## The local step after round 2 -/

/-! ## The program -/

section Glue

variable [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

