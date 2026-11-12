import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedFinal
import ThresholdLeanXmssSecurity.Proof.TreeCheckCountedCut

/-!
# Check and record links using opening agreement

`TreeLockstepOpenedFinal` supplies the opening and successful-record agreement theorems.
The check assemblies below therefore require only their original counted-cut
data; the uncounted estimate has no additional premise. The audited-record link
retains the original collision guard and successful-output hypotheses.

The pinned and current leanVM proof trees were searched for these interfaces.
They are specific to the threshold ceremony; these proofs instantiate the
existing local assemblies without copying their arguments.

This does not discharge the counted-cut data or the retained-prefix stage
schedule. In particular, the digest link's `TreeLockstepStagesGoal` is a
separate obligation, rather than a consequence of successful records.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Counted-cut parts need no additional record-agreement assumption. -/
theorem treeCheckCountedCut_of_parts_proved
    (parts : TreeCheckCountedCutParts prims K circuits settings) :
    TreeCheckCountedCut prims K circuits settings :=
  treeCheckCountedCut_of_parts prims K circuits settings
    (treeLockstepRecordsAgreeGoal prims K circuits settings) parts

/-- The two check branches from the counted cut, using proved agreement and
the existing uncounted-guess estimate. -/
theorem treeSimCheckSetupBranches3_of_cut_proved
    (cut : TreeCheckCountedCut prims K circuits settings) :
    TreeSimCheckSetupBranches3 prims K circuits settings :=
  treeSimCheckSetupBranches3_of_cut prims K circuits settings
    (treeLockstepRecordsAgreeGoal prims K circuits settings)
    (treeCheckUncountedGuess prims K circuits settings) cut

/-- The original parts assembly with its opening premise discharged. -/
theorem treeSimCheckSetupBranches3_of_parts_proved
    (parts : TreeCheckCountedCutParts prims K circuits settings) :
    TreeSimCheckSetupBranches3 prims K circuits settings :=
  treeSimCheckSetupBranches3_of_parts prims K circuits settings
    (treeLockstepOpenedGoal prims K circuits settings) parts

/-- Successful audited records agree on jobs and starting counters under the
original guard, without a separate agreement hypothesis. -/
theorem treeLockstepRecords_common_audited (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) (hx : DealtInputs D x)
    (run : (Bool × (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) ×
      TreeSimLog C)
    (hrun : run ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (good : ¬ TreeSimHashBudgetCollision run.2)
    (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) (vi vj : TreeOutput)
    (ri rj : List (TreeSimCheckBatchRecord C))
    (houti : run.1.2.2 i = some (vi, ri)) (houtj : run.1.2.2 j = some (vj, rj))
    (k : ℕ) (hki : k < ri.length) (hkj : k < rj.length) :
    ri[k].jobs = rj[k].jobs ∧ ri[k].start = rj[k].start :=
  treeLockstepRecords_common_of_agree prims K circuits settings hbatch
    (treeLockstepRecordsAgreeGoal prims K circuits settings)
    top tree D A x z Z hx run hrun good i j hi hj vi vj ri rj houti houtj k hki hkj

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCut_of_parts_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCut_of_parts_proved

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckSetupBranches3_of_cut_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckSetupBranches3_of_cut_proved

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckSetupBranches3_of_parts_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckSetupBranches3_of_parts_proved

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecords_common_audited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecords_common_audited

end ThresholdLeanXmssSecurity
