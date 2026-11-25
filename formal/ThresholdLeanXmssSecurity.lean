import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.Claim
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Claim
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Claim
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
setup slots. `Proof/DkgSecurity/ReductionCost.lean` proves the cost bound of the field `dkgSecurityPreservation`.
`Proof/DkgSecurity/Claim.lean` gives that field from the hop `SharedStep`, and `theorems_of_sharedStep`
gives the bundle from the same hop. -/

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss in
/-- The bundle `Theorems` from the hop `SharedStep` at the error `privacyStepError`. -/
theorem theorems_of_sharedStep {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
    (step : DkgSecurityProof.SharedStep prims K circuits settings runLimit (privacyStepError settings runLimit C)) :
    Theorems prims K circuits settings runLimit where
  stronglyUnforgeable := SigningStronglyUnforgeable.stronglyUnforgeable prims C
  signingCorrectness := signingCorrectness prims C
  dkgSecurityPreservation := DkgSecurityProof.dkgSecurityPreservation_of_leaves prims K circuits settings runLimit step
  dkgCorrectness := dkgCorrectness prims K circuits settings runLimit
  dkgCompleteness := dkgCompleteness prims K circuits settings runLimit

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

/-- info: 'ThresholdLeanXmssSecurity.theorems_of_sharedStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorems_of_sharedStep

end ThresholdLeanXmssSecurity
