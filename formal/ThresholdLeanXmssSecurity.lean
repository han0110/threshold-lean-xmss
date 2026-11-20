import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.Claim
import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.SigningStronglyUnforgeable

/-! # The proofs of the signing claims and of the completeness of the setup

This library proves three fields of the bundle `Theorems` (`ThresholdLeanXmss/Statement/Theorems.lean`).

* `SigningStronglyUnforgeable.stronglyUnforgeable` (`Proof/SigningStronglyUnforgeable.lean`) gives
  the field `stronglyUnforgeable`, `ThresholdLeanXmssStronglyUnforgeable prims C`.
* `signingCorrectness` (`Proof/Signing.lean`) gives the field `signingCorrectness`,
  `SigningCorrectnessStatement prims C`.
* `dkgCompleteness` (`Proof/DkgCompleteness/Claim.lean`) gives the field `dkgCompleteness`,
  `CircuitsCompute circuits prims.Th → DkgCompleteness prims K circuits settings runLimit`.

The folder `Base/` holds the definitions that the proofs use and that the statement layer does not
hold. The proofs follow PRAWNS for the signing and reuse leanVM `formal/lean_xmss` for the hash
layer. The proof of the completeness of the setup joins four hops on the honest run, and it uses
the claims of the building blocks and of one tree in `Proof/Tree.lean` and `Proof/Dealer.lean`. -/

namespace ThresholdLeanXmssSecurity

/-! The build fails unless each of the three theorems depends only on `propext`, `Classical.choice`
and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.stronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningStronglyUnforgeable.stronglyUnforgeable

/-- info: 'ThresholdLeanXmssSecurity.signingCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCorrectness

/-- info: 'ThresholdLeanXmssSecurity.dkgCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCompleteness

end ThresholdLeanXmssSecurity
