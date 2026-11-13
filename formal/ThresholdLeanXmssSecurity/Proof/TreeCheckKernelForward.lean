import ThresholdLeanXmssSecurity.Proof.TreeEvents4
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoupling

/-!
# The check kernel forward, and the check bound of an indexed check flag

* `kernel_alive_le_event` bounds the chance that an honest operator is not stopped after the check
  rounds, on a log with no budget collision, by the event of the hybrid check. It is the second half
  of `transport_of_kernel` with no bad event.
* `checkBound_of_branchesOf` gives the check bound of the events `treeSimEventsOf` with the check
  flag `∃ j, WrongAt j`. Each batch `j` has a counted branch and an uncounted branch. The proof is
  the one of `treeSimCheckBoundGoal3_of_indexedBounds3`, with `treeSimCheck_setup_accounting` for
  each batch and a union over the batches.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeCheckKernelForward

open ThresholdLeanXmssSecurity ThresholdLeanXmssSecurity.TreeEvents4

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The forward transport of the check kernel. With the kernel coupling, the chance that an honest
operator is not stopped after the check rounds, on a log with no budget collision, is at most the
event of the hybrid check. -/
theorem kernel_alive_le_event (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (rounds : ℕ) (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A)
    (h : TreeCheckHybrid C E)
    (coupling : RelTriple (TreeCheckWalkCoupling.checkKernel prims K circuits D A rounds b o)
      (TreeCheckWalkCoupling.hybridKernel prims K D h) (TreeCheckWalkCoupling.KernelRelation D A h)) :
    Pr[fun saved => ¬ TreeSimHashBudgetCollision saved.2.2 ∧ ∃ i, i ∉ D.1 ∧ saved.1.2 i ≠ .done none |
        TreeCheckWalkCoupling.checkKernel prims K circuits D A rounds b o] ≤ h.event prims K D := by
  apply probEvent_le_of_relTriple coupling
  intro saved out related accepted
  obtain ⟨good, i, honest, active⟩ := accepted
  obtain ⟨cacheGood, result⟩ := related good i honest active
  exact ⟨cacheGood, i, honest, result⟩

/-- The check bound of the events of a check flag `∃ j, WrongAt j` from the two branch bounds of
each batch. -/
theorem checkBound_of_branchesOf
    (WrongAt : (top : TopTree) → (tree : Tree) → C.Coalition →
      (A : Adversary C E (Keys C) PEmpty PEmpty) → (C.Party → Keys C) → Aux →
      Fin (treeBatches settings tree) → TreeSimLog C → Prop)
    (counted : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
      IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ WrongAt top tree D A x z j r.2 ∧
          ¬ TreeCheckUncounted D r.2 |
        treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
        ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E)
          (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q - 1)))
    (uncounted : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
      IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ WrongAt top tree D A x z j r.2 ∧
          TreeCheckUncounted D r.2 |
        treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
        ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256)) :
    TreeSimCheckBound circuits settings
      (treeSimTrace prims K circuits settings
        (treeSimEventsOf fun top tree D A x z log => ∃ j, WrongAt top tree D A x z j log)) := by
  letI : SampleableType E := SampleableType.ofFintype E
  intro hbatch top tree D A x z Z q hx hq hsmall
  let ε := checkErrorOf (E := E)
    (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
    (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q
  let run := treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)
  have batchBound : ∀ j : Fin (treeBatches settings tree),
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ WrongAt top tree D A x z j r.2 | run] ≤
        ENNReal.ofReal ε := fun j =>
    treeSimCheck_setup_accounting K run _ (fun r => TreeCheckUncounted D r.2) _ _ q
      ((probEvent_mono fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩).trans
        (uncounted hbatch top tree D A x z Z q hx hq hsmall j))
      ((probEvent_mono fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩).trans
        (counted hbatch top tree D A x z Z q hx hq hsmall j))
  have union : Pr[fun r => ¬ TreeSimHashBad3 D r.2 ∧ ∃ j, WrongAt top tree D A x z j r.2 | run] ≤
      ∑ j : Fin (treeBatches settings tree),
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ WrongAt top tree D A x z j r.2 | run] := by
    refine le_trans (probEvent_mono ?_) (probEvent_exists_finset_le_sum Finset.univ _ _)
    rintro r _ ⟨clean, j, wrong⟩
    exact ⟨j, Finset.mem_univ j, fun collision => clean (Or.inr collision), wrong⟩
  have sumBound : (∑ j : Fin (treeBatches settings tree),
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ WrongAt top tree D A x z j r.2 | run]) ≤
      (treeBatches settings tree : ℝ≥0∞) * ENNReal.ofReal ε := by
    calc
      _ ≤ ∑ _j : Fin (treeBatches settings tree), ENNReal.ofReal ε :=
        Finset.sum_le_sum fun j _ => batchBound j
      _ = _ := by simp
  have realBound := ENNReal.toReal_mono (by finiteness) (union.trans sumBound)
  simp only [treeSimTrace, probEvent_map, Function.comp_def, treeSimEventsOf, decide_eq_true_eq]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (checkErrorOf_nonneg K _ _ _), ε, treeCheckError] using realBound

end ThresholdLeanXmssSecurity.TreeCheckKernelForward

open ThresholdLeanXmssSecurity.TreeCheckKernelForward

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelForward.kernel_alive_le_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_alive_le_event

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelForward.checkBound_of_branchesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkBound_of_branchesOf
