import ThresholdLeanXmssSecurity.Base.SecureComputation
import ThresholdLeanXmss.Statement.DkgErrors

/-!
# The completeness of the seed generation

An honest seed generation gives the keys of `F_seedGen`, except when two derived keys collide.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- An honest seed generation gives the keys of `F_seedGen`, except when two derived keys collide. -/
def SeedGenCompletenessStatement (C : Committee) (E : Type) : Prop :=
  Completes prims (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) setupRounds noFunctionality
    (fun l => l.elim) FseedGen (fun _ => Finset.univ) (fun _ _ => True) (derivedKeyCollision C)

end ThresholdLeanXmss
