import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.Claim
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Claim
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.ReductionCost
import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.SigningStronglyUnforgeable

/-! # The proofs of the signing claims and of the correctness and the completeness of the setup

This library proves four fields of the bundle `Theorems` (`ThresholdLeanXmss/Statement/Theorems.lean`).

* `SigningStronglyUnforgeable.stronglyUnforgeable` (`Proof/SigningStronglyUnforgeable.lean`) gives
  the field `stronglyUnforgeable`, `ThresholdLeanXmssStronglyUnforgeable prims C`.
* `signingCorrectness` (`Proof/Signing.lean`) gives the field `signingCorrectness`,
  `SigningCorrectnessStatement prims C`.
* `dkgCompleteness` (`Proof/DkgCompleteness/Claim.lean`) gives the field `dkgCompleteness`,
  `CircuitsCompute circuits prims.Th → DkgCompleteness prims K circuits settings runLimit`.
* `dkgCorrectness` (`Proof/DkgCorrectness/Claim.lean`) gives the field `dkgCorrectness`,
  `CircuitsCompute circuits prims.Th → DkgCorrectness prims K circuits settings runLimit`.

The folder `Base/` holds the definitions that the proofs use and that the statement layer does not
hold. The proofs follow PRAWNS for the signing and reuse leanVM `formal/lean_xmss` for the hash
layer. The proof of the completeness of the setup joins four hops on the honest run, and it uses
the claims of the building blocks and of one tree in `Proof/Tree.lean` and `Proof/Dealer.lean`. The
proof of the correctness of the setup follows the game with hops. It cuts a run of a bottom tree into
two ceremonies, bounds the bad events of one ceremony, and pays the PRSS setups with a hybrid over the
setup slots. `Proof/DkgSecurity/ReductionCost.lean` proves the cost bound of the field
`dkgSecurityPreservation` (`DkgSecurityProof.dkgReduction_cost`).

The win bound of `dkgSecurityPreservation` has no proof in this library. The other files of
`Proof/DkgSecurity/` hold twelve hops of its chain on the game without the vote of
`Statement/DkgGame.lean`. They are not part of the build until they are on the game with the vote. -/

namespace ThresholdLeanXmssSecurity

/-! The build fails unless each of the five theorems below depends only on `propext`,
`Classical.choice` and `Quot.sound`. -/

/-- info: 'ThresholdLeanXmssSecurity.SigningStronglyUnforgeable.stronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningStronglyUnforgeable.stronglyUnforgeable

/-- info: 'ThresholdLeanXmssSecurity.signingCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCorrectness

/-- info: 'ThresholdLeanXmssSecurity.dkgCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCompleteness

/-- info: 'ThresholdLeanXmssSecurity.dkgCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCorrectness

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgReduction_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DkgSecurityProof.dkgReduction_cost

end ThresholdLeanXmssSecurity
