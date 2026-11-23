import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Clash
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Mismatch
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Claim
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Claim
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Claim
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.BadBound
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.End
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Search
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.RestCount
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.SeedGen
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Monitor.UsedHit
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Bottom
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomCosts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomEnds
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomFields
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Eager
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndCells
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndProvenance
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndWorld
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Param
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopCosts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopLaws

/-!
# The field `dkgSecurityPreservation` from the hops with the shared bad event

`dkgSecurityPreservation_of_leaves` is `dkgSecurityPreservation_of_shared` with the proved hops filled in. They are
`monitorErase`, the hop `UsedHitHop` at the error `setupHybridError` from the proof of
`dkgCorrectness`, `sharedStart`, `sharedRefDealer`, `sharedSeedBound`, `sharedSeedReal`,
`sharedSeedIdeal`, `sharedSearch`, `sharedEnd`, `tableHop`, `sharedBadBound` and `sharedHit`. The
premise is the hop `SharedStep`, as a proposition. `sharedHit` gives the hop `SharedHit` at the error
`privacyHitError` from the proved parts `hitSeed`, `hitSalt`, `hitClash` and `hitMismatch`. With the
errors `privacyHitError` and `privacyStepError` the error `sharedError` is `dkgError` by definition.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The hop `SharedHit` at the error `privacyHitError`. -/
theorem sharedHit : SharedHit prims K circuits settings runLimit (privacyHitError settings runLimit C) := by
  intro D A q bounded
  exact (sharedHit_of_parts prims K circuits settings runLimit (hitSeed prims K circuits settings runLimit)
    (hitSalt prims K circuits settings runLimit) (hitClash prims K circuits settings runLimit)
    (hitMismatch prims K circuits settings runLimit) D A q bounded).trans (hitError_eq settings runLimit C q).le

/-- The field `dkgSecurityPreservation` from the hop `SharedStep`, as a proposition. The error `dkgError` is
`sharedError` at `privacyHitError` and `privacyStepError` by definition. -/
theorem dkgSecurityPreservation_of_leaves
    (step : SharedStep prims K circuits settings runLimit (privacyStepError settings runLimit C)) :
    CircuitsCompute circuits prims.Th →
      ThresholdLeanXmss.DkgSecurityPreservation prims K circuits settings runLimit (dkgReduction K circuits settings runLimit) :=
  dkgSecurityPreservation_of_shared prims K circuits settings runLimit (privacyHitError settings runLimit C)
    (privacyStepError settings runLimit C)
    (monitorErase prims K circuits settings runLimit)
    (UsedHit.usedHitHop_of_reductions K circuits settings runLimit prims
      (UsedHit.topSlotPartCosts K circuits settings runLimit prims)
      (UsedHit.topLawReal K circuits settings runLimit prims) (UsedHit.topLawFresh K circuits settings runLimit prims)
      (UsedHit.bottomSlotPartCosts K circuits settings runLimit prims)
      (UsedHit.bottomLawReal K circuits settings runLimit prims)
      (UsedHit.bottomLawFresh K circuits settings runLimit prims)
      (UsedHit.endPointsAgree K circuits settings runLimit prims)
      (UsedHit.hybridEnd_of_statements prims K circuits settings runLimit
        (eagerDraw K circuits settings runLimit prims)
        (keyProvenance prims K circuits settings runLimit) (keyParametric K circuits settings runLimit)
        (cellsCount prims K circuits settings runLimit)))
    (sharedStart prims K circuits settings runLimit) (sharedBadBound prims K circuits settings runLimit)
    (sharedRefDealer prims K circuits settings runLimit) (sharedSeedBound K circuits settings runLimit prims)
    (sharedSeedReal K circuits settings runLimit prims) (sharedSeedIdeal K circuits settings runLimit prims)
    (sharedSearch prims K circuits settings runLimit)
    (sharedHit prims K circuits settings runLimit) step
    (sharedEnd prims K circuits settings runLimit)
    (tableHop prims K circuits settings runLimit) fun _ _ => le_refl _

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgSecurityPreservation_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dkgSecurityPreservation_of_leaves
