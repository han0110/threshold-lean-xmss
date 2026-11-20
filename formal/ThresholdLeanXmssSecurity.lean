import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.SigningStronglyUnforgeable

/-! # The proofs of the signing claims

This library proves two fields of the bundle `Theorems` (`ThresholdLeanXmss/Statement/Theorems.lean`).

* `SigningStronglyUnforgeable.stronglyUnforgeable` (`Proof/SigningStronglyUnforgeable.lean`) gives
  the field `stronglyUnforgeable`, `ThresholdLeanXmssStronglyUnforgeable prims C`.
* `signingCorrectness` (`Proof/Signing.lean`) gives the field `signingCorrectness`,
  `SigningCorrectnessStatement prims C`.

The folder `Base/` holds the definitions that the proofs use and that the statement layer does not
hold. The proofs follow PRAWNS for the signing and reuse leanVM `formal/lean_xmss` for the hash
layer. -/

namespace ThresholdLeanXmssSecurity

/-! The build fails unless each of the two theorems depends only on `propext`, `Classical.choice`
and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.stronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningStronglyUnforgeable.stronglyUnforgeable

/-- info: 'ThresholdLeanXmssSecurity.signingCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCorrectness

end ThresholdLeanXmssSecurity
