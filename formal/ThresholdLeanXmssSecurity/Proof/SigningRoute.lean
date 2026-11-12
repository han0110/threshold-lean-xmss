import ThresholdLeanXmssSecurity.Proof.SigningSelection
import ThresholdLeanXmssSecurity.Proof.SigningHybrid

/-!
# The signing coupling interface

`HiddenCoreAt` follows from `UnchargedFlagSoundCoupling` alone. `SigningSelection` proves the selection
classification, and `SigningHybrid` gives the route through the corrected flag.
-/

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

/-- `HiddenCoreAt` from the one open coupling of the uncharged lane. -/
theorem hiddenCoreAt_of_unchargedCoupling {C : Committee} (prims : Primitives)
    (hcouple : SigningHybridProof.UnchargedFlagSoundCoupling (C := C) prims) :
    SigningCoreProof.HiddenCoreAt prims C :=
  SigningHybridProof.hiddenCoreAt_of_soundCoupling prims
    (SigningSelectionProof.selectionClassification prims) hcouple

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.hiddenCoreAt_of_unchargedCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.hiddenCoreAt_of_unchargedCoupling
