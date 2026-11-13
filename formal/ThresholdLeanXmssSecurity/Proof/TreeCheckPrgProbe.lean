import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgClock
import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestLog
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkPositions

/-! # PRG-label probes for decoded checkpoints

One actual first pass supplies both a hidden-cache transfer and the floor bound
forced by the first check coin's PRG read. The decoded source retains that witness.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgProbe
open TreeCheckPrgClock TreeCheckHonestLog TreeCheckWalkState TreeCheckWalkRecipe
open TreeCheckHonestDisc TreeSimHashCount
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}

-- Ports of TreeCheckSigningProbe's predicate-generic floor extraction.
private theorem floor_left {limit : ℕ} {p : PartyM C E RealSpec α}
    {k : α → PartyM C E RealSpec β} (h : PrgFloor limit (p >>= k).run) :
    PrgFloor limit p.run := by
  exact IsQueryBoundP.of_bind_left h

private theorem floor_right {limit : ℕ} {p : PartyM C E RealSpec α}
    {k : α → PartyM C E RealSpec β} (h : PrgFloor limit (p >>= k).run)
    (a : α) (ha : some a ∈ support p.run) : PrgFloor limit (k a).run := by
  exact XmssSecurity.OracleComp.IsQueryBoundP.bind_right_of_mem_support h (some a) ha

/-- A successful timed prefix exposes the continuation of the same suspended step. -/
theorem suspended_prgFloor {limit n : ℕ}
    {allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop} (step : Step C E RealSpec α)
    (timed : TreeSimCheckTimedStep (n + 1) step) (k : α → PartyM C E RealSpec β)
    (a : α) (replay : TreeSimCheckStepAllowed allowed step a)
    (floor : ∀ inbox, PrgFloor limit (resumed (suspendStep k step) inbox)) :
    PrgFloor limit (k a).run := by
  cases step with
  | done out =>
    have stopped : out = none := timed
    have live : out = some a := replay
    rw [stopped] at live
    cases live
  | wait out resume =>
    obtain ⟨inbox, run⟩ := replay
    exact floor_right (floor inbox) a run.choose_spec.1.mem_support
  | call impossible resume => exact impossible.elim

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

variable (prims : Primitives) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings)

-- Port of SigningProbe.boundary_probe, with the same started witness and
-- PrgWindow.boundary_pre_futureEmpty's retained-round transfer.
/-- The same first pass supports the PRG-label probe and hidden-cache transfer. -/
theorem boundary_prg_probe (Z : Distinguisher C A.State TreeOutput)
    (b : TreeCheckTailBoundary A)
    (self : ∀ i, (b.batch.ctx i).self = i)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (nonzero : tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) ≠ 0)
    (o : TreeCheckTailCheckpoint A) (preRun : o ∈ support (b.pre prims K circuits settings D))
    (r : TreeCheckTailResult A)
    (contRun : r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o))
    (i : C.Party) (honest : i ∉ D.1)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C)) (accepted : r.1.2.2 i = some actual) :
    ∃ out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world),
      (TreeSimFutureEmpty (b.batch.initial.1 + depth
        (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1) out.2.1.2 →
       TreeSimFutureEmpty (b.batch.initial.1 + depth
        (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1) o.2.1.2) ∧
      ∀ limit, (∀ inbox, PrgFloor limit (resumed (out.1 i) inbox)) →
        limit ≤ b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1 := by
  let p := fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial
  let k := fun i data => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs
    b.batch.initial data >>= b.batch.k i
  have timed i : TreeSimCheckTimed
      (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds + 1)
      (p i).run := treeLockstep_localPrelude_timed _ _ _ (by
        simpa only [parameter i] using treeSimCheckBatchPrefix_timed K circuits settings
          (b.batch.ctx i) b.batch.jobs b.batch.initial)
  have start := treeSimCheckTimed_start D
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds)
    p k timed
  have same : (b.program K circuits settings) = fun i => p i >>= k i := by
    funext i
    simp only [TreeCheckTailBoundary.program, treeSimCheckBatchAudit_run_prefix, bind_assoc, p, k]
  have run := preRun
  unfold TreeCheckTailBoundary.pre executePhase at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  let out := ((fun i => suspendStep (k i) (started.1 i)), started.2)
  have firstRun : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world) := by
    rw [same, start, simulateQ_map, StateT.run_map, support_map]
    exact ⟨started, hs, rfl⟩
  refine ⟨out, firstRun, ?_, ?_⟩
  · intro fresh
    apply TreeCheckPrgWindow.rounds_futureEmpty prims D
      (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1)
      _ _ started.1 _ started.2 fresh o run
    intro h
    have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) h
    by_cases hh : h ∈ D.1
    · simp only [if_pos hh, mem_support_pure_iff] at each
      rw [each]
      trivial
    · simp only [if_neg hh, worldRoles] at each
      apply TreeCheckPrgWindow.prelude_advance_quiet
        (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1)
        _ _ _ _ (treeSimCheck_support_free _ each)
      simpa only [parameter h] using
        TreeCheckPrgWindow.batchPrefix_window K circuits settings (b.batch.ctx h)
          b.batch.jobs b.batch.initial
  · intro limit floor
    obtain ⟨data, present, localRun⟩ := TreeCheckWalkRecipe.batchCont_local_support
      prims K circuits D A Z b.batch o r contRun i honest actual accepted
    have replay := treeSimCheck_rounds_replay D A noFunctionality _ _ _
      started.1 o.1 (treeLockstep_logged_run_allowed prims D _ _ o run) i honest data present
    have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) i
    simp only [if_neg honest, worldRoles] at each
    have pending := (timed i).advance_mem _ (treeSimCheck_support_free _ each)
    have finishFloor := suspended_prgFloor (started.1 i) pending (k i) data replay floor
    have counts := b.counts prims K circuits settings D Z self parameter o preRun r contRun
      ⟨i, actual, accepted⟩ i honest
    obtain ⟨data', present', history, label, tag, counts, modes⟩ := counts
    have eq : data' = data := Option.some.inj (present'.symm.trans present)
    subst data'
    have dataNonzero : (data.2.1.2.map (·.count)).sum ≠ 0 := by
      rw [counts, TreeCheckBatchWalk.counts_sum]
      exact nonzero
    simp only [k, treeSimCheckBatchFinish, treeSimCheckAfterVerify, bind_assoc] at finishFloor
    have le := check_prg_floor_label K (b.batch.ctx i) (held_term _) data.2.2 data.2.1.2
      dataNonzero limit (floor_left finishFloor)
    exact label ▸ le

/-- The decoded source retains an actual first pass whose live future floor
cannot exceed the label of the fixed hybrid. -/
theorem source_prg_probe (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (dealt : DealtInputs D x) (z : Aux) (j : Fin (treeBatches settings tree))
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup.1.2 j.val))
    (o : TreeCheckTailCheckpoint A)
    (preRun : o ∈ support (((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).boundary c).pre
      prims K circuits settings D))
    (r : TreeCheckTailResult A)
    (contRun : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r)
    (i : C.Party) (honest : i ∉ D.1)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C)) (accepted : r.1.2.2 i = some actual) :
    ∃ out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D c.1.1.program)).run c.1.1.world),
      (TreeSimFutureEmpty
        ((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).hybrid c o).label
        out.2.1.2 → TreeSimFutureEmpty
        ((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).hybrid c o).label
        o.2.1.2) ∧
      ∀ limit, (∀ inbox, PrgFloor limit (resumed (out.1 i) inbox)) →
        limit ≤ ((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).hybrid c o).label := by
  let b := (sourceWalk prims K D A circuits settings top tree x j.val Z step setup).boundary c
  have self h : (b.batch.ctx h).self = h := rfl
  have parameter h : (b.batch.ctx h).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, keys⟩ := dealt
    change (x h).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [keys h, keys (refHolder D K.publicTerm)]
    rfl
  have nonzero := TreeCheckWalkPositions.source_count_ne_zero prims K D A circuits settings
    top tree x z j Z step setup c o r contRun bad
  obtain ⟨out, supported, fresh, probe⟩ := boundary_prg_probe K prims D A circuits settings
    Z b self parameter nonzero o preRun r contRun i honest actual accepted
  refine ⟨out, ?_, fresh, probe⟩
  have fits := decode_sound prims K D A circuits settings top tree x setup.1.2 j.val c
  rw [fits.2.2]
  exact supported

end TreeCheckPrgProbe
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgProbe.suspended_prgFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgProbe.suspended_prgFloor

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgProbe.boundary_prg_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgProbe.boundary_prg_probe

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgProbe.source_prg_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgProbe.source_prg_probe
