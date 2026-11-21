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
# The field `dkgSecurity` from the hops with the shared bad event

`dkgSecurity_of_leaves` is `dkgSecurity_of_shared` with the proved hops filled in. They are
`monitorErase`, the hop `UsedHitHop` at the error `setupHybridError` from the proof of
`dkgCorrectness`, `sharedStart`, `sharedSeedBound`, `sharedSeedReal`, `sharedSeedIdeal`,
`sharedSearch`, `sharedEnd`, `tableHop` and `sharedBadBound`. The premises are the three other hops
`SharedRefDealer`, `SharedHit` and `SharedStep`, as propositions, and the inequality between
`sharedError` and the approved `dkgError`.
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

omit [DecidableEq E] in
/-- The field `dkgSecurity` from the other hops with the shared bad event, as propositions, and from
the inequality between `sharedError` and the approved `dkgError`. -/
theorem dkgSecurity_of_leaves (hit : ℕ → ℝ) (slack : Tree → ℕ → ℝ)
    (ref : SharedRefDealer prims K circuits settings runLimit)
    (hits : SharedHit prims K circuits settings runLimit hit)
    (step : SharedStep prims K circuits settings runLimit slack)
    (gap : 0 < runLimit → ∀ q : ℕ, sharedError (E := E) circuits settings runLimit hit slack C q ≤
      dkgError (E := E) circuits settings runLimit C q) :
    CircuitsCompute circuits prims.Th →
      ThresholdLeanXmss.DkgSecurity prims K circuits settings runLimit (dkgReduction K circuits settings runLimit) :=
  dkgSecurity_of_shared prims K circuits settings runLimit hit slack
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
    (sharedStart prims K circuits settings runLimit) (sharedBadBound prims K circuits settings runLimit) ref (sharedSeedBound K circuits settings runLimit prims)
    (sharedSeedReal K circuits settings runLimit prims) (sharedSeedIdeal K circuits settings runLimit prims)
    (sharedSearch prims K circuits settings runLimit) hits step
    (sharedEnd prims K circuits settings runLimit)
    (tableHop prims K circuits settings runLimit) gap

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgSecurity_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dkgSecurity_of_leaves
