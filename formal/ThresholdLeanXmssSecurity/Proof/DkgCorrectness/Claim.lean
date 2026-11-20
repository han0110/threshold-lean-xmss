import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Hops
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutBounds
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HeadCut
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Leaves
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RunsUnion
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndWorld

/-!
# The field `dkgCorrectness` from the leaves of the route

`dkgCorrectness_of_leaves` gives the field `dkgCorrectness` of `Theorems`,
`CircuitsCompute circuits prims.Th → DkgCorrectness prims K circuits settings runLimit`. Its premises
are the five structures of `Leaves.lean`. `ceremonyBad_of_parts`, `provenanceTreeRun_of_parts`,
`readyHopL_of_ends`, `UsedHit.usedHitHop_of_reductions`, and `ceremonySupport_of_parts` with
`cutState_of_supports` join their fields to the statements of the route.
`UsedHit.hybridEnd_of_statements` gives `HybridEnd`. The proved leaves `cutDead`, `cutMonotone`,
`headFuel`, `headCover`, `treePhaseProvenance`, `hiddenNames`, `ledgerHidden`, `ceremonyProvenance`,
`echoHop`, `reuseHop`, `copyHop` and `splitHop` and the hops `flagFirstHop`, `seedsHop` and
`runsUnionHop` give the rest. The error of `UsedHitHop` is `setupHybridError`, and with it
`part1Error` is `dkgCorrectnessError`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [DecidableEq E] in
/-- The field `dkgCorrectness` from the five groups of leaves. -/
theorem dkgCorrectness_of_leaves (ceremony : CeremonyParts K circuits settings runLimit)
    (support : SupportParts K circuits settings) (cut : CutStatements K circuits settings) (usedHit : UsedHitParts K circuits settings runLimit)
    (game : GameHops K circuits settings runLimit) :
    CircuitsCompute circuits prims.Th → ThresholdLeanXmss.DkgCorrectness prims K circuits settings runLimit := by
  intro compute batch runs D A q bounded
  exact part1L_of_route K circuits settings runLimit (setupHybridError runLimit C)
    (fun prims => flagFirstHop prims K circuits settings runLimit)
    (fun prims => seedsHop prims K circuits settings runLimit)
    (fun prims => RunsUnion.runsUnionHop prims K circuits settings runLimit)
    (fun prims => readyHopL_of_ends prims K circuits settings runLimit (game.sound prims) (game.hidden prims)
      (provenanceTreeRun_of_parts prims K circuits settings (treePhaseProvenance prims K circuits settings)
        (ceremony.monitorProvenance prims)))
    (echoHop K circuits settings runLimit)
    (fun prims => UsedHit.usedHitHop_of_reductions K circuits settings runLimit prims (usedHit.topCost prims)
      (usedHit.topReal prims) (usedHit.topFresh prims) (usedHit.bottomCost prims) (usedHit.bottomReal prims)
      (usedHit.bottomFresh prims) (usedHit.endPoints prims)
      (UsedHit.hybridEnd_of_statements prims K circuits settings runLimit (usedHit.eager prims)
        (usedHit.keyProvenance prims) usedHit.keyParametric (usedHit.cellsCount prims)))
    (reuseHop K circuits settings runLimit) (copyHop K circuits settings runLimit)
    (splitHop K circuits settings runLimit)
    (fun prims => ceremonyBad_of_parts prims K circuits settings runLimit (ceremony.monitor prims)
      (ceremony.batch prims) (ceremony.abort prims) (ceremony.fresh prims) (hiddenNames (C := C)) (ceremony.sync prims)
      (ceremony.interval prims) (ceremony.coupling prims) (ceremony.keysAgree prims) (ceremony.budget prims)
      ceremony.zero (ceremony.short prims) (ceremony.tupleInputs prims))
    cut.top (headFuel circuits settings) (fun prims => headCover prims K circuits settings)
    (cutState_of_supports K circuits settings fun prims => ceremonySupport_of_parts prims K circuits settings
      (support.counters prims) (support.outputsAgree prims) (support.split prims) (support.sound prims)
      (support.salts prims) (ledgerHidden prims K circuits settings) (ceremonyProvenance prims K circuits settings))
    (fun prims => cutDead prims K circuits settings)
    (fun prims => cutMonotone prims K circuits settings) cut.rest
    batch runs prims compute D A q bounded

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.dkgCorrectness_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.dkgCorrectness_of_leaves
