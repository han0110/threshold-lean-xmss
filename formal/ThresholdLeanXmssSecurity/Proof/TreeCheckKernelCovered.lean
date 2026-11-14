import ThresholdLeanXmssSecurity.Proof.TreeCheckSeenCovered
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoupling

/-!
Every outcome of the check kernel at a supported walk checkpoint has its
collision-region cache entries covered by its log. The free first pass and
round scheduler cannot program the cache. This supplies coverage and the
start equation for lifting a real-run coupling to the original kernel relation.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section

namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-! ## The check kernel as a real execution

The declarations of this part are in the namespace `TreeCheckKernelCoupling`, and the module doc of
`TreeCheckKernelCoupling` describes them. -/

open TreeCheckWalkCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

-- The abort-persistence proofs of `TreeSimCheck`, as copied in `TreeCheckWalkCoupling`.
omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem step_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (r : A.State × (C.Party → Step C E (CallSpec I O) α) ×
      (C.Party → C.Party → Option (Msg E)))
    (h : r ∈ support (stepRound worldRoles D A F state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : r.2.1 i = .done a := by
  classical
  unfold stepRound at h
  split_ifs at h with hc
  all_goals
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨p, _, next, hn, rfl⟩ := h
    have hh := mem_support_sequenceFin_oc _ next hn i
    simpa only [hi, support_pure, Set.mem_singleton_iff] using hh

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem rounds_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (out : A.State × (C.Party → Option α))
    (h : out ∈ support (executeRounds worldRoles D A F fuel state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : out.2 i = a := by
  classical
  induction fuel generalizing state steps out with
  | zero =>
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at h
    subst out
    exact congrArg Step.output hi
  | succ fuel ih =>
    simp only [executeRounds] at h
    split_ifs at h with hd
    · cases h
      exact congrArg Step.output hi
    · simp only [support_bind, Set.mem_iUnion] at h
      obtain ⟨r, hr, ho⟩ := h
      exact ih r.1 r.2.1 out ho (step_done D A F state steps r hr i a hi)

section Kernel

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
  (A : Adversary C E (Keys C) PEmpty PEmpty)

omit [Fintype E] [DecidableEq E] in
/-- The check kernel without its log and hidden cache is a real execution. -/
theorem kernel_erase (circuits : Circuits) (rounds : ℕ) (b : TreeCheckBatchBoundary A)
    (o : TreeCheckTailCheckpoint A)
    (P : C.Party → PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))
    (start : free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))) = startSteps worldRoles D P) :
    (fun s : KernelState A => (s.1, s.2.1.1)) <$> checkKernel prims K circuits D A rounds b o =
      realRun prims D A rounds o.1.1 P o.2.1 := by
  unfold checkKernel realRun
  rw [start]
  have whole := treeSimLoggedWorld_erase prims D
    (startSteps worldRoles D P >>= fun steps =>
      executeSteps worldRoles D A noFunctionality rounds o.1.1 steps) o.2.1 o.2.2
  rw [← whole]
  simp only [simulateQ_bind, StateT.run_bind, Functor.map_map, map_bind]

omit [Fintype E] [DecidableEq E] in
/-- The checkpoint rows of the corrupt operators are empty. -/
theorem corrupt_rows (circuits : Circuits) (settings : Settings) (b : TreeCheckTailBoundary A)
    (o : TreeCheckTailCheckpoint A) (run : o ∈ support (b.pre prims K circuits settings D)) :
    ∀ i ∈ D.1, o.1.2 i = none := by
  have raw := treeCheck_logged_support prims D _ _ run
  unfold executePhase at raw
  rw [mem_support_bind_iff] at raw
  obtain ⟨steps, started, rounds⟩ := raw
  intro i hi
  have start : steps i = .done none := by
    have h := mem_support_sequenceFin_oc _ steps started i
    simpa [hi] using h
  exact rounds_done D A noFunctionality _ b.batch.state steps o.1 rounds i none start

omit [Fintype E] [DecidableEq E] in
/-- The first local pass of the kernel starts the checkpoint rows. -/
theorem kernel_start (circuits : Circuits) (b : TreeCheckBatchBoundary A)
    (o : TreeCheckTailCheckpoint A) (corrupt : ∀ i ∈ D.1, o.1.2 i = none) :
    free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))) =
      startSteps worldRoles D (fun i => (o.1.2 i).elim failure
        (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, continueStep, free_pure]
  · cases he : o.1.2 i <;> simp [hi, he, continueStep, worldRoles, free_pure, advance_pure]

/-- The covered real cache and the hybrid cache inside it give the kernel relation. -/
theorem kernelRelation_of_final (h : TreeCheckHybrid C E) (saved : KernelState A)
    (out : (h.adversary.State × (C.Party → Option Unit)) × HashCache C)
    (covered : TreeSimCheckCacheCovered saved.2.1.1 saved.2.2)
    (final : Final D A (saved.1, saved.2.1.1) out) : KernelRelation D A h saved out := by
  intro good i hi alive
  obtain ⟨le, accept⟩ := final i hi alive
  refine ⟨fun collision => good ?_, accept⟩
  obtain ⟨q, r, u, v, hne, hq, hr, huv⟩ := treeSimCheck_domain_collision_mono le collision
  have huv' : u = v := eq_of_heq huv
  subst v
  have sq : TreeSimHashDomain q := by
    by_contra hn
    simp [splitRegionCache, hn] at hq
  have sr : TreeSimHashDomain r := by
    by_contra hn
    simp [splitRegionCache, hn] at hr
  exact ⟨q, r, u, treeSimHash_domain_budget q sq, treeSimHash_domain_budget r sr, hne,
    covered q u sq (by simpa [splitRegionCache, sq] using hq),
    covered r u sr (by simpa [splitRegionCache, sr] using hr)⟩

/-- A real execution coupled to the hybrid adapter gives the kernel coupling,
once the kernel's final hash cache is covered by its log. -/
theorem kernel_of_real (circuits : Circuits) (h : TreeCheckHybrid C E) (rounds : ℕ)
    (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A)
    (P : C.Party → PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))
    (start : free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))) = startSteps worldRoles D P)
    (covered : ∀ saved ∈ support (checkKernel prims K circuits D A rounds b o),
      TreeSimCheckCacheCovered saved.2.1.1 saved.2.2)
    (coupled : RelTriple (realRun prims D A rounds o.1.1 P o.2.1) (hybridKernel prims K D h)
      (Final D A)) :
    RelTriple (checkKernel prims K circuits D A rounds b o) (hybridKernel prims K D h)
      (KernelRelation D A h) := by
  rw [← kernel_erase prims K D A circuits rounds b o P start] at coupled
  have strong := relTriple_support_left (relTriple_of_map_left coupled) covered
  exact relTriple_post_mono strong fun saved out related =>
    kernelRelation_of_final D A h saved out related.2 related.1

end Kernel

end ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.kernel_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.kernel_of_real

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
