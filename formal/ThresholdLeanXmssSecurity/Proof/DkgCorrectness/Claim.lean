import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Hops
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutBounds
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutCheck.Budget
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutCheck.Tuples
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.Fresh
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.Interval
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HeadCut
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Cells
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Parts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Leaves
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.GameHidden
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Records.Keys
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RunsUnion
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Joint
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Eager
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndCells
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndWorld
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopCosts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopLaws

/-!
# The field `dkgCorrectness` from the leaves of the route

`dkgCorrectness_of_leaves` gives the field `dkgCorrectness` of `Theorems`,
`CircuitsCompute circuits prims.Th → DkgCorrectness prims K circuits settings runLimit`. Its premise
is the structure `UsedHitParts` of `Leaves.lean`. `ceremonyBad_of_parts`, `provenanceTreeRun_of_parts`,
`readyHopL_of_ends`, `UsedHit.usedHitHop_of_reductions`, `ceremonySupport_of_parts` with
`cutState_of_supports`, and `topCover_of_started` and `restCover_of_started` join their fields to the
statements of the route. `UsedHit.hybridEnd_of_statements` gives `HybridEnd`. The proved leaves
`cutDead`, `cutMonotone`, `headFuel`, `headCover`, `treePhaseProvenance`, `hiddenNames`,
`ledgerHidden`, `ceremonyProvenance`, `ledgerSplit`, `ledgerSalts`, `ledgerSound`, `ceremonyCounters`,
`zeroCheck`, `CutBudget.ceremonyBudget`, `CutBudget.ceremonyTupleInputs`, `freshOne`,
`ceremonyInterval`, `monitorProvenance`, `ceremonyStarted`, `ceremonyAbort`,
`Joint.ceremonyCoupling`, `CeremonyRecords.ceremonyMonitor`, `CeremonyRecords.ceremonyBatch`,
`CeremonyRecords.ceremonySync`, `EchoRound.ceremonyKeysAgree`, `CeremonyRecords.ceremonyOutputsAgree`,
`shortFuel`, `soundAtEnd`, `hiddenAtEnd`, `UsedHit.topSlotPartCosts`, `UsedHit.topLawReal`,
`UsedHit.topLawFresh`, `keyProvenance`, `cellsCount`, `eagerDraw`, `keyParametric`, `echoHop`, `reuseHop`, `copyHop` and `splitHop` and the
hops `flagFirstHop`, `seedsHop` and `runsUnionHop` give the rest. The error of `UsedHitHop` is
`setupHybridError`, and with it `part1Error` is `dkgCorrectnessError`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The field `dkgCorrectness` from the parts of the hop on the used keys. -/
theorem dkgCorrectness_of_leaves (usedHit : UsedHitParts K circuits settings runLimit) :
    CircuitsCompute circuits prims.Th → ThresholdLeanXmss.DkgCorrectness prims K circuits settings runLimit := by
  intro compute batch runs D A q bounded
  exact part1L_of_route K circuits settings runLimit (setupHybridError runLimit C)
    (fun prims => flagFirstHop prims K circuits settings runLimit)
    (fun prims => seedsHop prims K circuits settings runLimit)
    (fun prims => RunsUnion.runsUnionHop prims K circuits settings runLimit)
    (fun prims => readyHopL_of_ends prims K circuits settings runLimit
      (soundAtEnd prims K circuits settings runLimit) (hiddenAtEnd prims K circuits settings runLimit)
      (provenanceTreeRun_of_parts prims K circuits settings (treePhaseProvenance prims K circuits settings)
        (monitorProvenance prims (C := C))))
    (echoHop K circuits settings runLimit)
    (fun prims => UsedHit.usedHitHop_of_reductions K circuits settings runLimit prims
      (UsedHit.topSlotPartCosts K circuits settings runLimit prims)
      (UsedHit.topLawReal K circuits settings runLimit prims) (UsedHit.topLawFresh K circuits settings runLimit prims)
      (usedHit.bottomCost prims) (usedHit.bottomReal prims)
      (usedHit.bottomFresh prims) (usedHit.endPoints prims)
      (UsedHit.hybridEnd_of_statements prims K circuits settings runLimit
        (eagerDraw K circuits settings runLimit prims)
        (keyProvenance prims K circuits settings runLimit) (keyParametric K circuits settings runLimit)
        (cellsCount prims K circuits settings runLimit)))
    (reuseHop K circuits settings runLimit) (copyHop K circuits settings runLimit)
    (splitHop K circuits settings runLimit)
    (fun prims => ceremonyBad_of_parts prims K circuits settings runLimit
      (CeremonyRecords.ceremonyMonitor prims K circuits settings)
      (CeremonyRecords.ceremonyBatch prims K circuits settings) (ceremonyAbort prims K circuits settings)
      (freshOne prims K circuits settings) (hiddenNames (C := C))
      (CeremonyRecords.ceremonySync prims K circuits settings) (ceremonyInterval prims K circuits settings)
      (Joint.ceremonyCoupling prims K circuits settings) (EchoRound.ceremonyKeysAgree prims K circuits settings)
      (CutBudget.ceremonyBudget prims K circuits settings runLimit)
      (zeroCheck (C := C) (E := E)) (shortFuel prims K circuits settings) (CutBudget.ceremonyTupleInputs prims K circuits settings))
    (fun prims => topCover_of_started prims K circuits settings (ceremonyStarted prims K circuits settings))
    (headFuel circuits settings)
    (fun prims => headCover prims K circuits settings)
    (cutState_of_supports K circuits settings fun prims => ceremonySupport_of_parts prims K circuits settings
      (ceremonyCounters prims K circuits settings)
      (CeremonyRecords.ceremonyOutputsAgree prims K circuits settings)
      (ledgerSplit prims K circuits settings) (ledgerSound prims K circuits settings)
      (ledgerSalts prims K circuits settings) (ledgerHidden prims K circuits settings)
      (ceremonyProvenance prims K circuits settings))
    (fun prims => cutDead prims K circuits settings)
    (fun prims => cutMonotone prims K circuits settings)
    (fun prims => restCover_of_started prims K circuits settings (ceremonyStarted prims K circuits settings))
    batch runs prims compute D A q bounded

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.dkgCorrectness_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.dkgCorrectness_of_leaves
