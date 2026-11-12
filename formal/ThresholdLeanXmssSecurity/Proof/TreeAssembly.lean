import ThresholdLeanXmssSecurity.Proof.TreeHashBudgetRun
import ThresholdLeanXmssSecurity.Proof.TreeTwinKinds
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom
import ThresholdLeanXmssSecurity.Proof.TreeLockstepReach
import ThresholdLeanXmssSecurity.Proof.TreeLockstepUse
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkHybrid
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltRepresentation
import ThresholdLeanXmssSecurity.Proof.TreeSaltPairsProof

/-!
# Conditional assembly of the tree simulation hop

The linked-stage certificate, counted tail sources, opaque salt normalization
and pair bounds on one shared two-stage split imply the original
`TreeSimulationHop`. Lockstep, opening agreement and the honest hash budget
are supplied by their existing theorems. Both pair variants use the original
budget-collision event and the unchanged check and hash errors.

The pinned and current leanVM proof trees were searched for these interfaces.
The assembly directly reuses the threshold ceremony lemmas.
-/

open LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeAssembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Linked rounds give the exact stage goal with the lockstep certificates supplied. -/
theorem stages_of_linked
    (linked : TreeTwinLinkedGoal prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_linked prims K circuits settings
    (treeLockstepStagesGoal_of_segments circuits prims K settings
      (treeLockstepSegments K circuits settings prims))
    (treeTwinDigestDrawsGoal circuits prims K settings) linked

/-- One source walk supplies the counted branch; opening agreement supplies the check link. -/
theorem branches_of_tailSources
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings) :
    TreeSimCheckSetupBranches3 prims K circuits settings :=
  treeSimCheckSetupBranches3_of_parts_proved prims K circuits settings
    (treeCheckCountedCutParts_of_tailSources prims K circuits settings sources)

/-- The original pair route with only linked rounds, tail sources, salt normalization
and the pair certificate on the given split as hypotheses. -/
theorem treeSimulationHop_of_pairs
    (linked : TreeTwinLinkedGoal prims K circuits settings)
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings)
    (normalization : TreeRawSaltRepresentationProof.CeremonyOpaqueNormalization
      prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_pairs3 prims K circuits settings
    (stages_of_linked prims K circuits settings linked)
    (treeSimHashHonestBudget K prims circuits settings)
    (TreeRawSaltRepresentationProof.rawSaltEstimate_of_opaque
      prims K circuits settings normalization)
    splits pairBounds (branches_of_tailSources prims K circuits settings sources)

/-- The guarded pair certificate on the same split gives the same simulation hop. -/
theorem treeSimulationHop_of_guardedPairs
    (linked : TreeTwinLinkedGoal prims K circuits settings)
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings)
    (normalization : TreeRawSaltRepresentationProof.CeremonyOpaqueNormalization
      prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairsGuarded splits) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_pairsGuarded prims K circuits settings
    (stages_of_linked prims K circuits settings linked)
    (treeSimHashHonestBudget K prims circuits settings)
    (TreeRawSaltRepresentationProof.rawSaltEstimate_of_opaque
      prims K circuits settings normalization)
    splits pairBounds (branches_of_tailSources prims K circuits settings sources)

/-- info: 'ThresholdLeanXmssSecurity.TreeAssembly.stages_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stages_of_linked

/-- info: 'ThresholdLeanXmssSecurity.TreeAssembly.branches_of_tailSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms branches_of_tailSources

/-- info: 'ThresholdLeanXmssSecurity.TreeAssembly.treeSimulationHop_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairs

/-- info: 'ThresholdLeanXmssSecurity.TreeAssembly.treeSimulationHop_of_guardedPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_guardedPairs

end ThresholdLeanXmssSecurity.TreeAssembly
