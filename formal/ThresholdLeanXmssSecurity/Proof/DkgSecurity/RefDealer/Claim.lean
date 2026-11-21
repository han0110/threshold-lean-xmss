import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Wrong
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.PassRest

/-!
# The hop to the reference dealer

`sharedRefDealer` proves `SharedRefDealer`. A wrong honest output of one run has a bad check in the
records of the run (`passWrongTop` for the top tree, `passBottomHead` and `passBottomRest` for a
bottom tree), so the outputs of a run with no bad check are the reference outputs, and the signing
phase couples with the phase of the dealer (`ghostCouple_of_step`).
-/

set_option autoImplicit false

open ThresholdLeanXmss ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `SharedRefDealer`. -/
theorem sharedRefDealer : SharedRefDealer prims K circuits settings runLimit := fun hsize hc =>
  sharedRefDealer_of_bottomRest prims K circuits settings runLimit
    (passBottomRest prims K circuits settings hsize) hsize hc

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer
