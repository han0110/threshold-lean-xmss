import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Parts
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Close
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CountsWalk
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoLaw
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ListShiftLaw
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepCommitWalk
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepCommitMid

/-!
# The part `HitSeed` of the first hit

`hitSeed` gives `HitSeed` by `hitSeed_of_touch` from `SeedTouch` and `CompHit`. `seedTouch_of_steps`
gives `SeedTouch` from `partsStep` and `partsCount`. `compHit_of_steps` gives `CompHit` from
`echoCompare`, `listShift`, `listShiftStep_of_alias`, `listCount` and `compLog`.
-/

set_option autoImplicit false

open ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The part `HitSeed` of the first hit. -/
theorem hitSeed : HitSeed prims K circuits settings runLimit := by
  intro D A q h
  exact SeedCompare.hitSeed_of_touch prims K circuits settings runLimit
    (seedTouch_of_steps prims K circuits settings runLimit (partsStep prims K circuits settings runLimit)
      (partsCount prims K circuits settings runLimit))
    (compHit_of_steps prims K circuits settings runLimit (echoCompare prims K circuits settings runLimit)
      (listShift K circuits settings runLimit)
      (listShiftStep_of_alias prims K circuits settings runLimit
        (listAliasBound_of_shift prims (midShiftLaw_of_commit prims (midCommitLaw prims))))
      (listCount prims K circuits settings runLimit) (compLog prims K circuits settings runLimit)) D A q h

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.hitSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.hitSeed
