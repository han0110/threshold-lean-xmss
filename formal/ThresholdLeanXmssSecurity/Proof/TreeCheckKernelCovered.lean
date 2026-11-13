import ThresholdLeanXmssSecurity.Proof.TreeCheckSeenCovered
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling

/-!
Every outcome of the check kernel at a supported walk checkpoint has its
collision-region cache entries covered by its log. The free first pass and
round scheduler cannot program the cache. This supplies coverage and the
start equation for lifting a real-run coupling to the original kernel relation.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckKernelCovered
open TreeCheckWalkRecipe TreeCheckWalkCoupling TreeCheckKernelCoupling
open TreeCheckSeenCovered
open ProgramQuiet (Programming qb0_bind' free_quiet)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

-- Port of TreeCheckSeenCovered.executeRounds_quiet, retaining pending steps.
theorem executeSteps_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (executeSteps worldRoles D A noFunctionality fuel state steps) Programming 0 := by
  induction fuel generalizing state steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ fuel ih =>
    rw [executeSteps]
    split
    · exact isQueryBoundP_pure _ _ _
    · exact qb0_bind' (stepRound_quiet D A state steps) fun r => ih r.1 r.2.1

/-- Coverage at a supported checkpoint survives any number of kernel rounds. -/
theorem kernel_covered (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun _ _ D A _ _ Z _ _ _ _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        ∀ rounds saved, saved ∈ support
          (checkKernel prims K circuits D A rounds (W.boundary c).batch o) →
          TreeSimCheckCacheCovered saved.2.1.1 saved.2.2 := by
  intro hb top tree D A x z Z q dealt bounded small j p hp c o run rounds saved hs
  have exclude : ∀ key, ¬ TreeSimHashDomain (C := C) (.streamKey key) := by
    intro key
    simp [TreeSimHashDomain]
  have coverage := walkCheckpoint_coveredOn prims exclude K circuits settings
  unfold AtWalk at coverage
  have covered := by
    with_reducible exact (coverage hb top tree D A x z Z q dealt bounded small j p hp c o run)
  unfold checkKernel at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨next, hn, hs⟩ := hs
  have nextCovered := run_covered prims exclude D _ (free_quiet _) o.2 next covered hn
  exact run_covered prims exclude D _ (executeSteps_quiet D A rounds _ _) next.2 saved
    nextCovered hs

/-- A real-run coupling at a supported checkpoint gives the original kernel coupling. -/
theorem kernel_of_realRun (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun _ _ D A _ _ Z _ _ _ _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        ∀ rounds (h : TreeCheckHybrid C E),
          let b := (W.boundary c).batch
          let P := fun i => (o.1.2 i).elim failure
            (fun row => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial row >>= b.k i)
          RelTriple (realRun prims D A rounds o.1.1 P o.2.1)
            (hybridKernel prims K D h) (Final D A) →
          RelTriple (checkKernel prims K circuits D A rounds b o)
            (hybridKernel prims K D h) (KernelRelation D A h) := by
  intro hb top tree D A x z Z q dealt bounded small j p hp c o run rounds h b P coupled
  have ho := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
        (W := _) (prims := prims) (K := K) (circuits := circuits) (settings := settings)
        (D := D) (Z := Z) (c := c) (o := o) run)
  have corrupt := corrupt_rows prims K D A circuits settings _ o ho
  have coverage := kernel_covered prims K circuits settings
  unfold AtWalk at coverage
  with_reducible exact (kernel_of_real prims K D A circuits h rounds b o P
    (kernel_start K D A circuits b o corrupt)
    (coverage hb top tree D A x z Z q dealt bounded small
      j p hp c o run rounds) coupled)

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCovered.executeSteps_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms executeSteps_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCovered.kernel_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms kernel_covered

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCovered.kernel_of_realRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms kernel_of_realRun

end ThresholdLeanXmssSecurity.TreeCheckKernelCovered
