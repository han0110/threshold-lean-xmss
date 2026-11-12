import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedFinal
import ThresholdLeanXmssSecurity.Proof.TreeTwinFields

/-!
# Encoding agreement on retained bottom-tree prefixes

`treeLockstepEncodingLateBottom` proves the exact late-bottom goal. The existing
early/top reductions give `TreeLockstepEncodingGoal`, then
`TreeLockstepSegmentsGoal`, with no additional premise.

Successful final records do not cover aborted prefixes. A bounded local snapshot
instead retains the actual pending step after its local head, preserves earlier
aborts, and makes no further query. This supplies a common first-run output and
selection witness even when the ceremony later aborts. One actual retained trace
is split at that boundary; its complete log and pending programs keep the common
encoding through every later round, including rejection. A key-free schedule
transfers this fact to the arbitrary setup witness quantified by the target.

The pinned and current leanVM libraries were searched; their single-party trace
lemmas do not supply this synchronous network boundary. No protocol, target, or
collision guard is changed.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E α : Type}

-- A71_ARBITRARY_SETUP_TRANSFER

section ArbitrarySetupTransfer

variable (circuits : Circuits) (settings : Settings)

/-- The part of a salt schedule independent of the operator and its keys. -/
def TreeLateScheduleShape (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (enc : Encoding) (j label : ℕ) : Prop :=
  ∃ k, k < (lockstepChunks settings enc (.bottom b)).length ∧
    batchCount circuits parameter ((lockstepChunks settings enc (.bottom b)).getD k []) ≠ 0 ∧
    label = lockstepSaltLabel circuits parameter (lockstepChunks settings enc (.bottom b)) k ∧
    j = lockstepSaltRound circuits settings.mode parameter (lockstepChunks settings enc (.bottom b)) k

/-- Intersect two certificates for the same local segment. -/
theorem treeLate_segmentSalts_and {P Q : PrgInput C → Prop}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)}
    (left : SegmentSalts P p) : SegmentSalts Q p → SegmentSalts (fun y => P y ∧ Q y) p := by
  induction left with
  | pure out => intro _; exact .pure out
  | queryLocal q k hp h ih =>
    intro right
    cases right with
    | queryLocal _ _ hq rest =>
      exact .queryLocal q k (fun y hy => ⟨hp y hy, hq y hy⟩) (fun value => ih value (rest value))
  | round out k => intro _; exact .round out k

/-- The original witness supplies the holder/key fields; the actual reached
run supplies the common encoding's batch, label and exchange index. -/
theorem treeLate_schedule_transfer (x : C.Party → Keys C) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (enc : Encoding) (keysOf : C.Party → Option (PrssKeys C))
    (i : C.Party) (sameParameter : (x i).parameter = parameter) (oldIndex newIndex : ℕ)
    (T : C.Term) (key : HashOutput) (label : ℕ)
    (old : OpSchedule circuits settings x (.bottom b) keysOf i oldIndex T key label)
    (shape : TreeLateScheduleShape circuits settings parameter b enc newIndex label) :
    OpScheduleEnc circuits settings x (.bottom b) enc keysOf i newIndex T key label := by
  obtain ⟨prss, present, oldEnc, keyEq, held, _⟩ := old
  refine ⟨prss, present, keyEq, held, ?_⟩
  simpa only [TreeLateScheduleShape, sameParameter] using shape

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Transfer a common actual schedule to any setup witness admitted by the
original target. No identification of that witness with the reached setup is
needed. Non-salt PRG inputs retain their vacuous `SaltRead` certificate. -/
theorem treeLate_scheduleAt_transfer (x : C.Party → Keys C) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (enc : Encoding) (keysOf : C.Party → Option (PrssKeys C))
    (D : C.Coalition) (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (n : ℕ) (steps : C.Party → Step C E RealSpec α) (fullLog setupLog log : TreeSimLog C)
    (logs : fullLog = setupLog ++ log)
    (hsteps : ∀ i, i ∉ D.1 →
      SegmentsStep (OpSchedule circuits settings x (.bottom b) keysOf i) (n + 1) (steps i))
    (hlog : ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
      ∃ i, i ∉ D.1 ∧ ∃ j ≤ n, SaltRead (OpSchedule circuits settings x (.bottom b) keysOf i j) y)
    (fullShape : ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ fullLog →
      ∀ T key label g, y = (.term T, key, label, 2, g) →
        ∃ j ≤ n, TreeLateScheduleShape circuits settings parameter b enc j label)
    (nextShape : ∀ i, i ∉ D.1 → SegmentSaltsStep
      (fun y => ∀ T key label g, y = (.term T, key, label, 2, g) →
        TreeLateScheduleShape circuits settings parameter b enc (n + 1) label) (steps i)) :
    TreeEncodingScheduleAt circuits settings x (.bottom b) keysOf D n steps log := by
  refine ⟨enc, ?_, ?_⟩
  · intro y bit mem
    obtain ⟨i, hi, oldIndex, oldBound, oldRead⟩ := hlog y bit mem
    by_cases salt : ∃ T key label g, y = (.term T, key, label, 2, g)
    · obtain ⟨T, key, label, g, rfl⟩ := salt
      have fullMem := logs ▸ List.mem_append_right setupLog mem
      obtain ⟨j, bound, shape⟩ := fullShape _ bit fullMem T key label g rfl
      refine ⟨i, hi, j, bound, ?_⟩
      intro T' key' label' g' eq
      have labels : label = label' := congrArg (fun y : PrgInput C => y.2.2.1) eq
      exact treeLate_schedule_transfer circuits settings x parameter b enc keysOf i
        (parameters i hi) oldIndex j T' key' label'
        (oldRead T' key' label' g' eq) (labels ▸ shape)
    · exact ⟨i, hi, oldIndex, oldBound,
        fun T key label g eq => (salt ⟨T, key, label, g, eq⟩).elim⟩
  · intro i hi
    have old := hsteps i hi
    have shaped := nextShape i hi
    revert old shaped
    cases steps i with
    | done out => intro _ _; trivial
    | call input resume => exact input.elim
    | wait out resume =>
      intro old shaped inbox
      have localOld := (old inbox).segmentSalts (fun _ h => h)
      exact (treeLate_segmentSalts_and localOld (shaped inbox)).mono
        (fun y h T key label g eq => treeLate_schedule_transfer circuits settings x parameter b enc keysOf i
          (parameters i hi) (n + 1) (n + 1) T key label
          (h.1 T key label g eq) (h.2 T key label g eq))

/-- info: 'ThresholdLeanXmssSecurity.treeLate_scheduleAt_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLate_scheduleAt_transfer

end ArbitrarySetupTransfer

-- A71_ARBITRARY_SETUP_TRANSFER_END

-- A71_REACHED_HASH_HELPER
section ReachedHashWitness

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Padding preserves the entire observed log of a retained prefix. Thus one
total hash function explains every recorded hash answer, even after an abort.
This is the exact-log argument of `treeStages_outputWitness_padded`, without
discarding the log equality or imposing a final-output or fuel bound. -/
theorem treeLate_reached_hashes (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (fuel : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (ha : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) fuel a) :
    ∃ hash, Good prims hash ∧
      ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ a.2.2 →
        TreeSimCheckWorldHashes hash t u := by
  let out := (a.1.1, fun i => (a.1.2 i).output)
  have phase : (out, a.2) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 3) p.2.1
        (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree))).run
          ((r.2, p.2.2.1.2), p.2.2.2)) := by
    rw [simulateQ_executePhase]
    change _ ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality _ _ _).run _)
    rw [treeStages_trace_output, StateT.run_map, support_map]
    exact ⟨a, ha, rfl⟩
  have padded : (out, a.2.2) ∈ support (do
      let r ← (simulateQ (localAnswer prims) padding).run p.2.2.1.1
      (fun u : (A.State × (C.Party → Option TreeOutput)) × TreeSimState C => (u.1, u.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D)
          (executePhase worldRoles D A noFunctionality (fuel + 3) p.2.1
            (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree))).run
              ((r.2, p.2.2.1.2), p.2.2.2)) := by
    simp only [support_bind, Set.mem_iUnion, support_map]
    exact ⟨r, hr, (out, a.2), phase, rfl⟩
  have unpadded := (mem_support_evalDist_iff _ _).2 padded
  rw [treeStages_phase_padding prims D A (fuel + 3) p.2.1 _ padding p.2.2] at unpadded
  have replay := (mem_support_evalDist_iff _ _).1 unpadded
  have ghost : (p.1, (out, a.2.2)) ∈ support (treeSimGhostRun prims D
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
      (realExecution D A noFunctionality (fuel + 3)
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
        (dealtKeys parameter seeds pairs) z)) := by
    rw [treeStages_ghost_phase_prefix prims K circuits settings top tree D A parameter seeds pairs z]
    simp only [support_bind, Set.mem_iUnion, support_map] at replay ⊢
    obtain ⟨v, hv, he⟩ := replay
    exact ⟨p, hp, v, hv, by rw [← he]⟩
  obtain ⟨hash, good, _, rows⟩ := treeSimCheck_ghost_hashes prims D _ _ p.1 out a.2.2 ghost
  exact ⟨hash, good, rows⟩

/-- info: 'ThresholdLeanXmssSecurity.treeLate_reached_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLate_reached_hashes

end ReachedHashWitness
-- A71_REACHED_HASH_HELPER_END

/-- Keep pending steps and successful outputs, while preserving an abort. -/
def treeLateSnapshotOut : Step C E RealSpec α → Option (Step C E RealSpec α)
  | .done none => none
  | step => some step

/-- Run only the displayed number of exchanges and retain the resulting step.
The local head at the cutoff is executed in its original scheduler position. -/
def treeLateSnapshot : ℕ → PartyM C E RealSpec α → PartyM C E RealSpec (Step C E RealSpec α)
  | n, p => OptionT.mk (do
    let step ← liftComp (advance p.run) (PartySpec C E RealSpec)
    match step with
    | .done out => pure (treeLateSnapshotOut (.done out))
    | .wait out resume =>
      match n with
      | 0 => pure (some (.wait out resume))
      | n + 1 => do
        let inbox ← OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out)))
        (treeLateSnapshot n (OptionT.mk (resume inbox))).run
    | .call input _ => input.elim)
termination_by n => n

/-- The pending-step representation of the same bounded snapshot. -/
def treeLateSnapshotStep (n : ℕ) : Step C E RealSpec α → Step C E RealSpec (Step C E RealSpec α)
  | .done out => .done (treeLateSnapshotOut (.done out))
  | .wait out resume =>
    match n with
    | 0 => .done (some (.wait out resume))
    | n + 1 => .wait out (fun inbox => (treeLateSnapshot n (OptionT.mk (resume inbox))).run)
  | .call input _ => input.elim

/-- Local snapshotting changes only the retained program, not its queries. -/
theorem treeLateSnapshot_advance (n : ℕ) (p : PartyM C E RealSpec α) :
    advance (treeLateSnapshot n p).run = treeLateSnapshotStep n <$> advance p.run := by
  rw [treeLateSnapshot, OptionT.run_mk, advance_liftComp_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro step
  cases step with
  | done out => rfl
  | wait out resume => cases n <;> rfl
  | call input _ => exact input.elim


@[simp] theorem treeLateSnapshotStep_done (n : ℕ) (out : Option α) :
    treeLateSnapshotStep (C := C) (E := E) n (.done out) = .done (out.map fun a => .done (some a)) := by
  cases out <;> rfl

@[simp] theorem treeLateSnapshotStep_outbox (n : ℕ) (step : Step C E RealSpec α) :
    (treeLateSnapshotStep (n+1) step).outbox = step.outbox := by
  cases step with
  | done out => cases out <;> rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

@[simp] theorem treeLateSnapshotStep_delivered (n : ℕ) (step : Step C E RealSpec α) :
    (treeLateSnapshotStep (n+1) step).delivered = step.delivered := by
  cases step with
  | done out => cases out <;> rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

@[simp] theorem treeLateSnapshotStep_isDone (n : ℕ) (step : Step C E RealSpec α) :
    (treeLateSnapshotStep (n+1) step).isDone = step.isDone := by
  cases step with
  | done out => rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

@[simp] theorem treeLateSnapshotStep_zero_output (step : Step C E RealSpec α) :
    (treeLateSnapshotStep 0 step).output = treeLateSnapshotOut step := by
  cases step with
  | done out => rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- One local handler retains its original query order and shared inbox. -/
theorem treeLateSnapshot_roundLocal (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (fun j => treeLateSnapshotStep (n+1) (steps j)) sent i =
      treeLateSnapshotStep n <$> roundLocal D steps sent i := by
  unfold roundLocal
  dsimp only
  cases hs : steps i with
  | done out => cases out <;> rfl
  | call input _ => exact input.elim
  | wait out resume =>
    rw [treeLateSnapshotStep]
    dsimp only
    split_ifs
    · rfl
    · simp only [treeLateSnapshotStep_delivered]
      exact treeLateSnapshot_advance n _

/-- A synchronous snapshot preserves the single adversary reply and all
ordered honest queries of the actual round. -/
theorem treeLateSnapshot_stepRound (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (fun i => treeLateSnapshotStep (n+1) (steps i)) =
      (fun r => (r.1, (fun i => treeLateSnapshotStep n (r.2.1 i)), r.2.2)) <$>
        stepRound worldRoles D A noFunctionality state steps := by
  rw [stepRound_real, stepRound_real]
  simp only [treeLateSnapshotStep_outbox, map_bind, map_pure]
  apply bind_congr
  rintro ⟨state', sent⟩
  have hs : Concrete.sequenceFin (roundLocal D (fun i => treeLateSnapshotStep (n+1) (steps i)) sent) =
      (fun row i => treeLateSnapshotStep n (row i)) <$>
        Concrete.sequenceFin (roundLocal D steps sent) := by
    change Concrete.sequenceFin (fun i => roundLocal D (fun j => treeLateSnapshotStep (n+1) (steps j)) sent i) = _
    simp only [treeLateSnapshot_roundLocal, map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]
  rw [hs]
  simp only [map_eq_bind_pure_comp, free_bind, bind_assoc]
  rfl

/-- Snapshotting preserves the initial local queries and corrupt abort rows. -/
theorem treeLateSnapshot_start (D : C.Coalition) (n : ℕ) (p : C.Party → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => treeLateSnapshot n (p i)) =
      (fun steps i => treeLateSnapshotStep n (steps i)) <$> startSteps worldRoles D p := by
  unfold startSteps
  have hl (i) : (if i ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (treeLateSnapshot n (p i)).run)) =
      treeLateSnapshotStep n <$>
        (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (p i).run)) := by
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, map_pure, treeLateSnapshotStep_done, Option.map_none]
    · simp only [if_neg hi, treeLateSnapshot_advance, worldRoles]
      simp only [map_eq_bind_pure_comp, free_bind, free_pure, Function.comp_def]
  simp_rw [hl]
  simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]


/-- The bounded snapshot keeps exactly the reached pending steps, rather than
projecting those steps to absent final ceremony outputs. -/
theorem treeLateSnapshot_rounds (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (corrupt : ∀ i ∈ D.1, steps i = .done none) :
    executeRounds worldRoles D A noFunctionality n state (fun i => treeLateSnapshotStep n (steps i)) =
      (fun r => (r.1, fun i => treeLateSnapshotOut (r.2 i))) <$>
        executeSteps worldRoles D A noFunctionality n state steps := by
  induction n generalizing state steps with
  | zero => simp only [executeRounds, executeSteps, treeLateSnapshotStep_zero_output, map_pure]
  | succ n ih =>
    simp only [executeRounds, executeSteps, treeLateSnapshotStep_isDone]
    split_ifs with stopped
    · rw [map_pure]
      congr 2
      funext i
      dsimp only
      have done : (steps i).isDone := by
        by_cases hi : i ∈ D.1
        · rw [corrupt i hi]; trivial
        · exact stopped i hi
      cases hs : steps i with
      | done out => cases out <;> rfl
      | wait _ _ => simp [hs, Step.isDone] at done
      | call input _ => exact input.elim
    · rw [treeLateSnapshot_stepRound, map_bind]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro r hr
      exact ih r.1 r.2.1 (world_stepRound_corruptDone D A state steps corrupt r hr)

/-- The complete snapshot law is an equality of world programs. Thus it
preserves the final state, both caches and every logged query jointly. -/
theorem treeLateSnapshot_phase (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality n state (fun i => treeLateSnapshot n (p i)) =
      (fun r => (r.1, fun i => treeLateSnapshotOut (r.2 i))) <$>
        (startSteps worldRoles D p >>= fun steps =>
          executeSteps worldRoles D A noFunctionality n state steps) := by
  unfold executePhase
  rw [treeLateSnapshot_start, map_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro steps hs
  apply treeLateSnapshot_rounds
  intro i hi
  have h := mem_support_sequenceFin_oc _ steps hs i
  simpa only [if_pos hi, mem_support_pure_iff] using h

/-- Every nonaborted reached step supplies a snapshot output; a later abort
cannot remove this earlier witness. -/
theorem treeLateSnapshotOut_some (step : Step C E RealSpec α) (live : step ≠ .done none) :
    treeLateSnapshotOut step = some step := by
  cases step with
  | done out => cases out <;> simp_all [treeLateSnapshotOut]
  | wait _ _ => rfl
  | call input _ => exact input.elim


@[simp] theorem treeLateSnapshot_pure (n : ℕ) (out : Option α) :
    (treeLateSnapshot (C := C) (E := E) n (OptionT.mk (pure out))).run =
      pure (out.map fun a => .done (some a)) := by
  rw [treeLateSnapshot]
  cases out <;> rfl

theorem treeLateSnapshot_local (n : ℕ) (q : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α)) :
    (treeLateSnapshot n (OptionT.mk (.roll (.inl (.inl q)) k))).run =
      .roll (.inl (.inl q)) (fun u => (treeLateSnapshot n (OptionT.mk (k u))).run) := by
  conv_lhs => rw [treeLateSnapshot]
  simp only [OptionT.run_mk, advance, liftComp_bind, liftComp_query, bind_assoc]
  have hq : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
      OracleComp (PartySpec C E RealSpec) _) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
    rw [← liftM_query_local]; rfl
  rw [hq]
  change OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inl q)) _ = OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inl q)) _
  apply congrArg (OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inl q)))
  funext u
  rw [treeLateSnapshot]
  rfl

theorem treeLateSnapshot_round (n : ℕ) (out : Mail C E)
    (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)) :
    (treeLateSnapshot (n+1) (OptionT.mk (.roll (.inl (.inr out)) k))).run =
      .roll (.inl (.inr out)) (fun u => (treeLateSnapshot n (OptionT.mk (k u))).run) := by
  rw [treeLateSnapshot]
  rfl

/-- An exact exchange schedule and its upper bound move the cutoff through
that prefix. The upper bound excludes an overshooting branch that only aborts. -/
theorem treeLateSnapshot_bind {β : Type} {m : ℕ} {p : PartyM C E RealSpec α}
    (within : TreeTwinWithin m p.run) (j : ℕ)
    (exactRun : TreeSegmentRun (fun _ _ _ _ => True) j (j+m) p.run)
    (fuel : ℕ) (k : α → PartyM C E RealSpec β) :
    treeLateSnapshot (m+fuel) (p >>= k) = p >>= fun a => treeLateSnapshot fuel (k a) := by
  have eta (q : PartyM C E RealSpec β) : OptionT.mk q.run = q := by apply OptionT.ext; rfl
  apply OptionT.ext
  conv_lhs => rw [← eta (p >>= k)]
  simp only [OptionT.run_bind, Option.elimM]
  generalize p.run = code at within exactRun ⊢
  induction within generalizing j with
  | pure m out =>
    cases out with
    | none => simp only [pure_bind, Option.elim_none, treeLateSnapshot_pure, Option.map_none]
    | some a =>
      have zero : m = 0 := by
        generalize he : j + m = endpoint at exactRun
        cases exactRun
        omega
      subst m
      simp only [Nat.zero_add, pure_bind, Option.elim_some, eta]
  | queryLocal m q f h ih =>
    have run (u) : TreeSegmentRun (fun _ _ _ _ => True) j (j+m) (f u) := by
      generalize he : j + m = endpoint at exactRun
      cases exactRun with | queryLocal _ _ _ _ _ hf => exact he ▸ hf u
    change (treeLateSnapshot (m+fuel) (OptionT.mk (.roll (.inl (.inl q)) _))).run = _
    rw [treeLateSnapshot_local]
    change OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inl q)) _ = OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inl q)) _
    exact congrArg (OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inl q))) (funext fun u => ih u j (run u))
  | round m out f h ih =>
    have run (u) : TreeSegmentRun (fun _ _ _ _ => True) (j+1) ((j+1)+m) (f u) := by
      generalize he : j + (m + 1) = endpoint at exactRun
      cases exactRun with | round _ _ _ _ hf =>
        convert hf u using 1; omega
    rw [Nat.succ_add]
    change (treeLateSnapshot (m+fuel+1) (OptionT.mk (.roll (.inl (.inr out)) _))).run = _
    rw [treeLateSnapshot_round]
    change OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inr out)) _ = OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inr out)) _
    exact congrArg (OracleComp.queryBind (spec := PartySpec C E RealSpec) (.inl (.inr out))) (funext fun u => ih u (j+1) (run u))


/-- Erasing audit values cannot change the exchange upper bound. -/
theorem treeLateWithin_of_map {β : Type} (f : α → β)
    (p : OracleComp (PartySpec C E RealSpec) (Option α)) (n : ℕ)
    (h : TreeTwinWithin n (Option.map f <$> p)) : TreeTwinWithin n p := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure out => exact TreeTwinWithin.pure n out
  | query_bind t k ih =>
    rcases t with (q | mail) | input
    · change TreeTwinWithin n (.roll (.inl (.inl q)) (fun u => Option.map f <$> k u)) at h
      cases h with
      | queryLocal _ _ _ hk => exact .queryLocal _ q _ fun u => ih u _ (hk u)
    · change TreeTwinWithin n (.roll (.inl (.inr mail)) (fun u => Option.map f <$> k u)) at h
      cases h with
      | round _ _ _ hk => exact .round _ mail _ fun u => ih u _ (hk u)
    · exact input.elim

/-- Erasing audit values also preserves the exact successful exchange count. -/
theorem treeLateSegment_of_map {β : Type} (f : α → β)
    (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j n : ℕ)
    (h : TreeSegmentRun S j n (Option.map f <$> p)) : TreeSegmentRun S j n p := by
  induction p using OracleComp.inductionOn generalizing j n with
  | pure out =>
    cases out with
    | none => exact .abort j n
    | some a =>
      simp only [map_pure, Option.map_some] at h
      cases h
      exact .done j a
  | query_bind t k ih =>
    rcases t with (q | mail) | input
    · change TreeSegmentRun S j n (.roll (.inl (.inl q)) (fun u => Option.map f <$> k u)) at h
      cases h with
      | queryLocal _ _ _ _ hq hk => exact .queryLocal _ _ q _ hq fun u => ih u _ _ (hk u)
    · change TreeSegmentRun S j n (.roll (.inl (.inr mail)) (fun u => Option.map f <$> k u)) at h
      cases h with
      | round _ _ _ _ hk => exact .round _ _ mail _ fun u => ih u _ _ (hk u)
    · exact input.elim

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The audited batch has the same exact timing as its erased program. -/
theorem treeLateSnapshot_batch_timing (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    let p := (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial
    let n := batchRounds circuits settings.mode ctx.keys.parameter jobs
    TreeTwinWithin n p.run ∧ TreeSegmentRun (fun _ _ _ _ => True) 0 n p.run := by
  have upper := treeTwinWithin_ceremonyBatch K circuits settings ctx jobs initial
  have exactRun := treeExactExchanges_ceremonyBatch K circuits settings ctx jobs initial
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs] at upper exactRun
  change TreeTwinWithin _ ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run initial).run at upper
  change TreeSegmentRun _ _ _ ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run initial).run at exactRun
  rw [StateT.run_map, OptionT.run_map] at upper exactRun
  exact ⟨treeLateWithin_of_map _ _ _ upper, treeLateSegment_of_map _ _ _ _ _ exactRun⟩


/-- A local query prefix stays in place when the exchange cutoff moves. -/
theorem treeLateSnapshot_local_bind {β : Type} (n : ℕ) (p : OracleComp (LocalSpec C) β)
    (k : β → PartyM C E RealSpec α) :
    treeLateSnapshot n (localStep p >>= k) = localStep p >>= fun a => treeLateSnapshot n (k a) := by
  apply OptionT.ext
  conv_lhs => rw [treeLateSnapshot]
  simp only [OptionT.run_mk, liftComp_bind, bind_assoc,
    localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM, Option.elim_some, pure_bind, advance_liftComp_bind]
  apply bind_congr
  intro a
  rw [treeLateSnapshot]
  rfl

/-- Aborting local gates remain before the snapshot, with their original queries. -/
theorem treeLateSnapshot_gate {β : Type} (n : ℕ)
    (gate : OracleComp (LocalSpec C) (Option Unit)) (p : PartyM C E RealSpec β) :
    treeLateSnapshot n (treeLockstepLocalPrelude gate >>= fun _ => p) =
      treeLockstepLocalPrelude gate >>= fun _ => treeLateSnapshot n p := by
  unfold treeLockstepLocalPrelude
  rw [bind_assoc, treeLateSnapshot_local_bind, bind_assoc]
  apply bind_congr
  intro out
  cases out with
  | none =>
    simp only [failure_bind]
    apply OptionT.ext
    exact treeLateSnapshot_pure n none
  | some u => simp

-- The raw writer/state law is the same one used by A64's batch induction.
private theorem treeLate_batches_cons (ctx : Context C) (jobs : List Job)
    (batches : List (List Job)) (initial : ℕ × ℕ) :
    (((jobs :: batches).mapM (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial) =
      (do
        let a ← (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial
        let b ← ((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run a.2)
        pure ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)) := by
  simp [List.mapM_cons, WriterT.run_bind, StateT.run_bind]

/-- Move a cutoff through an entire audited batch list. The continuation still
receives the actual records and counters, including on paths that later abort. -/
theorem treeLateSnapshot_batches_bind {β : Type} (ctx : Context C) (batches : List (List Job))
    (initial : ℕ × ℕ) (fuel : ℕ)
    (k : ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec β) :
    treeLateSnapshot (((batches.map (batchRounds circuits settings.mode ctx.keys.parameter)).sum)+fuel)
      (((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial) >>= k) =
    ((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial) >>=
      fun a => treeLateSnapshot fuel (k a) := by
  induction batches generalizing initial k with
  | nil => simp [List.mapM_nil, WriterT.run_pure, StateT.run_pure]
  | cons jobs batches ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc, treeLate_batches_cons, bind_assoc, pure_bind]
    obtain ⟨upper, exactRun⟩ := treeLateSnapshot_batch_timing K circuits settings ctx jobs initial
    have exactRun' : TreeSegmentRun (fun _ _ _ _ => True) 0 (0 + batchRounds circuits settings.mode ctx.keys.parameter jobs)
        ((treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial).run := by
      simpa only [Nat.zero_add] using exactRun
    rw [treeLateSnapshot_bind upper 0 exactRun']
    apply bind_congr
    intro a
    exact ih a.2 _

private theorem treeLate_batched_run (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    (batched settings.batchSize (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx) jobs).run.run initial =
      (do
        let a ← ((chunks settings.batchSize jobs).mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial
        pure ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)) := by
  unfold batched
  simp only [WriterT.run_bind, WriterT.run_pure, StateT.run_bind, StateT.run_pure, map_pure]
  simp

/-- The ordinary batched interface has the same cutoff law. -/
theorem treeLateSnapshot_batched_bind {β : Type} (ctx : Context C) (jobs : List Job)
    (initial : ℕ × ℕ) (fuel : ℕ)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec β) :
    treeLateSnapshot (((chunks settings.batchSize jobs).map
      (batchRounds circuits settings.mode ctx.keys.parameter)).sum + fuel)
      ((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs).run.run initial >>= k) =
      (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs).run.run initial >>=
        fun a => treeLateSnapshot fuel (k a) := by
  simp only [treeLate_batched_run, bind_assoc, pure_bind]
  exact treeLateSnapshot_batches_bind K circuits settings ctx _ initial fuel _


/-- At a reached batch-list boundary, one live pending step is sufficient for
common first-run outputs. The original reached state and log are retained; no
successful final ceremony output is assumed. -/
theorem treeLate_first_boundary (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)) (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
        (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i)) jobs).run.run initial >>= k i)
        >>= fun steps => executeSteps worldRoles D A noFunctionality
          (((chunks settings.batchSize jobs).map (batchRounds circuits settings.mode parameter)).sum)
          state steps)).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (live : ∃ i, i ∉ D.1 ∧ r.1.2 i ≠ .done none) :
    ∃ (values : List (List (List Bit))) (records : C.Party → List (TreeSimCheckBatchRecord C))
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      values.length = (chunks settings.batchSize jobs).length ∧
      (∀ i, (records i).map (·.outputs) = values) ∧
      ((r.1.1, fun i => treeLateSnapshotOut (r.1.2 i)), r.2) ∈ support
        ((simulateQ (treeSimLoggedWorld prims D)
          (executePhase worldRoles D A noFunctionality 0 state'
            (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
              treeLateSnapshot 0 (k i ((some values.flatten, records i),
                (initial.1 + ((chunks settings.batchSize jobs).map (batchLabels circuits parameter)).sum,
                  initial.2 + (chunks settings.batchSize jobs).length)))))).run cache) := by
  let count := ((chunks settings.batchSize jobs).map (batchRounds circuits settings.mode parameter)).sum
  let p := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
    (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i)) jobs).run.run initial >>= k i
  let captured := ((r.1.1, fun i => treeLateSnapshotOut (r.1.2 i)), r.2)
  have capturedRun : captured ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality count state (fun i => treeLateSnapshot count (p i)))).run s) := by
    rw [treeLateSnapshot_phase, simulateQ_map, StateT.run_map, support_map]
    exact ⟨r, run, rfl⟩
  have programs (i) : treeLateSnapshot count (p i) = treeLockstepLocalPrelude (gate i) >>= fun _ =>
      (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i)) jobs).run.run initial >>=
        fun a => treeLateSnapshot 0 (k i a) := by
    unfold p
    rw [treeLateSnapshot_gate]
    apply bind_congr
    intro _
    have h := treeLateSnapshot_batched_bind K circuits settings (ctx i) jobs initial 0 (k i)
    simpa only [parameters i, Nat.add_zero, count] using h
  simp_rw [programs] at capturedRun
  have accepted : ∃ i value, captured.1.2 i = some value := by
    obtain ⟨i, _, hi⟩ := live
    exact ⟨i, r.1.2 i, treeLateSnapshotOut_some _ hi⟩
  exact treeLockstep_batched_next prims K circuits settings D A 0 state ctx self parameter parameters
    keys gate jobs initial (fun i a => treeLateSnapshot 0 (k i a)) s captured capturedRun good accepted


/-- With zero exchanges left, the snapshot is exactly the current local head. -/
theorem treeLateSnapshot_zero_run (p : PartyM C E RealSpec α) :
    (treeLateSnapshot 0 p).run = treeLateSnapshotOut <$> liftComp (advance p.run) (PartySpec C E RealSpec) := by
  rw [treeLateSnapshot, OptionT.run_mk, map_eq_bind_pure_comp]
  apply bind_congr
  intro step
  cases step with
  | done out => rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

/-- A captured live step is the actual local head, rather than a separate
successful execution of the original continuation. -/
theorem treeLateSnapshot_zero_support (p : PartyM C E RealSpec α) (step : Step C E RealSpec α)
    (h : some step ∈ support (treeLateSnapshot 0 p).run) : step ∈ support (advance p.run) := by
  rw [treeLateSnapshot_zero_run, support_map] at h
  obtain ⟨actual, ha, he⟩ := h
  have ha' : actual ∈ support (advance p.run) := by
    exact mem_support_of_mem_support_liftComp (PartySpec C E RealSpec) _ _ ha
  cases actual with
  | done out =>
    cases out with
    | none => cases he
    | some a => exact Option.some.inj he ▸ ha'
  | wait out resume => exact Option.some.inj he ▸ ha'
  | call input _ => exact input.elim

theorem treeLateSnapshot_oracle_bind {β : Type} (n : ℕ) (p : OracleComp (RoSpec C) β)
    (k : β → PartyM C E RealSpec α) :
    treeLateSnapshot n (oracleStep p >>= k) = oracleStep p >>= fun a => treeLateSnapshot n (k a) :=
  treeLateSnapshot_local_bind n (liftComp p _) k

/-- The public selection has one common value at the retained boundary, even
when the actual second-run head is only waiting and later all parties abort. -/
theorem treeLate_public_boundary {β : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (hash : Query C → HashOutput) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (p : OracleComp HashSpec β) (k : C.Party → β → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Step C E RealSpec α))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality 0 state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeLateSnapshot 0 (oracleStep (tweakable p) >>= k i)))).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes hash t u) :
    ∃ gate' : C.Party → OracleComp (LocalSpec C) (Option Unit),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 0 state
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            treeLateSnapshot 0 (k i (ThresholdLeanXmssSecurity.D prims hash (tweakable p)))))).run s) := by
  simp_rw [treeLateSnapshot_oracle_bind] at run
  exact treeLockstep_public_phase_gate prims D A 0 state hash gate p
    (fun i a => treeLateSnapshot 0 (k i a)) s r run rows

/-- From the joint retained boundary, every live honest step is supported by
its fixed continuation's local head. Earlier aborts give no fabricated witness. -/
theorem treeLate_boundary_local (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)) (p : C.Party → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C)
    (run : ((r.1.1, fun i => treeLateSnapshotOut (r.1.2 i)), r.2) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 0 state
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => treeLateSnapshot 0 (p i)))).run s))
    (i : C.Party) (hi : i ∉ D.1) (live : r.1.2 i ≠ .done none) :
    r.1.2 i ∈ support (advance (p i).run) := by
  have allowed := treeLockstep_logged_run_allowed prims D _ s _ run
  have localRun := treeSimCheck_phase_replay D A noFunctionality _ 0 state _ _ allowed i hi
    (r.1.2 i) (treeLateSnapshotOut_some _ live)
  obtain ⟨_, _, rest⟩ := localRun.option_bind_inv _ _ _
  exact treeLateSnapshot_zero_support (p i) _ rest.choose_spec.1.mem_support


/-- The audit projection preserves every local salt schedule. -/
theorem treeLate_auditSegment (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j n : ℕ)
    (h : TreeSegmentRun S j n
      ((ceremonyBatch K circuits settings ctx jobs : StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run initial).run) :
    TreeSegmentRun S j n ((treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial).run := by
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs] at h
  change TreeSegmentRun _ _ _ ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run initial).run at h
  rw [StateT.run_map, OptionT.run_map] at h
  exact treeLateSegment_of_map _ _ _ _ _ h

/-- The audited selected batch list keeps its fixed encoding, including every
branch that subsequently aborts. Counters come from the actual preceding batch. -/
theorem treeLate_audit_batches (ctx : Context C) (js : List (List Job)) :
    ∀ (cs rest : List (List Job)) (o tag : ℕ), js.drop o = cs ++ rest →
      TreeSegmentRun (LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term ctx.self js)
        (lockstepRoundStart circuits settings.mode ctx.keys.parameter js o)
        (lockstepRoundStart circuits settings.mode ctx.keys.parameter js (o + cs.length))
        (((cs.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run
          (lockstepStart circuits ctx.keys.parameter js o, tag))).run
  | [], rest, o, tag, _ => by
    simpa only [List.mapM_nil, List.length_nil, Nat.add_zero, WriterT.run_pure, StateT.run_pure]
      using TreeSegmentRun.pure _ _
  | c :: cs, rest, o, tag, hd => by
    obtain ⟨hlt, hc, hd'⟩ := lockstep_drop_eq_cons hd
    rw [treeLate_batches_cons]
    refine TreeSegmentRun.bind (treeLate_auditSegment K circuits settings ctx c _ _ _ _
      (treeSegmentRun_ceremonyBatch K circuits settings ctx c _ _ ?_)) fun a ha => ?_
    · intro hcount T hT
      refine ⟨rfl, hT, o, hlt, by rw [hc]; exact hcount, ?_, ?_⟩
      · unfold lockstepSaltLabel
        rw [hc]
        omega
      · unfold lockstepSaltRound
        rw [hc]
    · obtain ⟨record, _, _, _, next⟩ := lockstep_batchAudit circuits K settings ctx c _ a.1.1 a.1.2 a.2 ha
      rw [next, ← hc, ← lockstepStart_succ circuits ctx.keys.parameter js o hlt,
        ← lockstepRoundStart_succ circuits settings.mode ctx.keys.parameter js o hlt]
      refine (treeLate_audit_batches ctx js cs rest (o+1) (tag+1) hd').bind fun b _ => ?_
      rw [List.length_cons, show o+1+cs.length=o+(cs.length+1) by omega]
      exact TreeSegmentRun.pure _ _

/-- Attach a selected-run continuation to its audited batched interface. -/
theorem treeLate_audit_batched_bind {β : Type} (ctx : Context C) (js : List (List Job))
    (jobs : List Job) (rest : List (List Job)) (o tag n : ℕ)
    (split : js.drop o = chunks settings.batchSize jobs ++ rest)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec β)
    (hk : ∀ a, TreeSegmentRun
      (LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term ctx.self js)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js
        (o + (chunks settings.batchSize jobs).length)) n (k a).run) :
    TreeSegmentRun (LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term ctx.self js)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js o) n
      ((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs).run.run
        (lockstepStart circuits ctx.keys.parameter js o, tag) >>= k).run := by
  rw [treeLate_batched_run, bind_assoc]
  simp only [pure_bind]
  exact (treeLate_audit_batches K circuits settings ctx js _ rest o tag split).bind fun a _ => hk _


/-- The final bottom-tree verification uses no network exchange or salt. -/
theorem treeLate_bottomFinish_segment (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j : ℕ)
    (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (root : Digest) (randomness : Randomness)
    (values : Option (List (List Bit))) (records : List (TreeSimCheckBatchRecord C)) :
    TreeSegmentRun S j j
      (treeLockstepBottomFinish (E := E) parameter top b outputs root randomness values records).run := by
  cases values with
  | none => exact TreeSegmentRun.failure j j
  | some values =>
    unfold treeLockstepBottomFinish
    refine TreeSegmentRun.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) _)
      (fun _ _ _ h => h.elim) _ fun path => ?_
    refine TreeSegmentRun.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) _)
      (fun _ _ _ h => h.elim) _ fun result => ?_
    split_ifs
    · exact TreeSegmentRun.failure j j
    · exact TreeSegmentRun.pure j _

/-- The actual audited continuation at the selected second-run encoding. -/
def treeLateBottomTail (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (root : Digest) (randomness : Randomness) (enc : Encoding)
    (prior : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) := do
  let result ← (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) (signJobs b enc)).run.run initial
  treeLockstepBottomFinish ctx.keys.parameter top b outputs root randomness result.1.1 (prior ++ result.1.2)

/-- The selected audited tail keeps the actual encoding in all later segments. -/
theorem treeLate_bottomTail_segment (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (root : Digest) (randomness : Randomness) (enc : Encoding)
    (prior : List (TreeSimCheckBatchRecord C)) (tag : ℕ) :
    let js := lockstepChunks settings enc (.bottom b)
    let first := (chunks settings.batchSize (bottomJobs b)).length
    TreeSegmentRun
      (LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term ctx.self js)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js first)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js js.length)
      (treeLateBottomTail K circuits settings ctx top b outputs root randomness enc prior
        (lockstepStart circuits ctx.keys.parameter js first, tag)).run := by
  dsimp only
  unfold treeLateBottomTail
  apply treeLate_audit_batched_bind K circuits settings ctx _ (signJobs b enc) [] _ tag _
    (by simp [lockstepChunks])
  intro a
  have length : (chunks settings.batchSize (bottomJobs b)).length +
      (chunks settings.batchSize (signJobs b enc)).length =
      (lockstepChunks settings enc (.bottom b)).length := by simp [lockstepChunks]
  rw [length]
  exact treeLate_bottomFinish_segment _ _ _ _ _ _ _ _ _ _


set_option linter.constructorNameAsVariable false in
/-- A live first-run boundary fixes one second-run encoding for every honest
pending continuation, without assuming any final ceremony output. -/
theorem treeLate_bottom_boundary (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (hash : Query C → HashOutput) (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
        treeSimCheckAfterSetupAudit K circuits settings (ctx i) top (.bottom b)) >>= fun steps =>
          executeSteps worldRoles D A noFunctionality
            (((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum)
            state steps)).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes hash t u)
    (live : ∃ i, i ∉ D.1 ∧ r.1.2 i ≠ .done none) :
    ∃ enc : Encoding, ∀ i, i ∉ D.1 → SegmentsStep
      (LockstepSchedule circuits settings.mode parameter (ctx i).prss.term i
        (lockstepChunks settings enc (.bottom b)))
      ((((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum)+1)
      (r.1.2 i) := by
  simp only [treeLockstep_afterSetup_first, treeLockstepFirstJobs] at run
  obtain ⟨values, records, state', cache, gate', _, recorded, boundary⟩ :=
    treeLate_first_boundary K circuits settings prims D A state ctx self parameter parameters keys gate
      (bottomJobs b) (0,0) (fun i => treeLockstepFirstRest K circuits settings (ctx i) top (.bottom b)) s r run good live
  let initial := (((chunks settings.batchSize (bottomJobs b)).map (batchLabels circuits parameter)).sum,
    (chunks settings.batchSize (bottomJobs b)).length)
  let k := fun i (choice : Option (Digest × Randomness × Encoding)) =>
    match choice with
    | none => (failure : PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))
    | some (root, randomness, enc) => treeLateBottomTail K circuits settings (ctx i) top b values.flatten
        root randomness enc (records i) initial
  have rest (i) : treeLockstepFirstRest K circuits settings (ctx i) top (.bottom b)
      ((some values.flatten, records i), initial) =
      (oracleStep (tweakable (treeLockstepPublicChoiceCode parameter b values.flatten)) >>= k i) := by
    simp only [treeLockstepFirstRest, treeLateBottomTail, k, parameters i]
    apply bind_congr
    rintro (_ | ⟨root, randomness, enc⟩) <;> rfl
  simp only [Nat.zero_add] at boundary
  change ((r.1.1, fun i => treeLateSnapshotOut (r.1.2 i)), r.2) ∈ support
    ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality 0 state'
        (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
          treeLateSnapshot 0 (treeLockstepFirstRest K circuits settings (ctx i) top (.bottom b)
            ((some values.flatten, records i), initial))))).run cache) at boundary
  simp_rw [rest] at boundary
  obtain ⟨gate'', fixed⟩ := treeLate_public_boundary prims D A state' hash gate'
    (treeLockstepPublicChoiceCode parameter b values.flatten) k cache _ boundary rows
  cases selected : ThresholdLeanXmssSecurity.D prims hash
      (tweakable (treeLockstepPublicChoiceCode parameter b values.flatten)) with
  | none =>
    simp only [selected, k] at fixed
    obtain ⟨i, hi, live⟩ := live
    have h := treeLate_boundary_local prims D A state' gate'' (fun _ => failure) cache r fixed i hi live
    simp only [advance_run_failure, mem_support_pure_iff] at h
    exact (live h).elim
  | some selectedValue =>
    obtain ⟨root, randomness, enc⟩ := selectedValue
    simp only [selected, k] at fixed
    refine ⟨enc, ?_⟩
    intro i hi
    by_cases dead : r.1.2 i = .done none
    · rw [dead]; trivial
    have localHead := treeLate_boundary_local prims D A state' gate''
      (fun i => treeLateBottomTail K circuits settings (ctx i) top b values.flatten root randomness enc
        (records i) initial) cache r fixed i hi dead
    have schedule := treeLate_bottomTail_segment K circuits settings (ctx i) top b values.flatten root randomness enc
      (records i) initial.2
    have label : initial.1 = lockstepStart circuits (ctx i).keys.parameter
        (lockstepChunks settings enc (.bottom b)) (chunks settings.batchSize (bottomJobs b)).length := by
      simp [initial, parameters i, lockstepStart, lockstepChunks]
    have head : r.1.2 i ∈ support (advance (treeLateBottomTail K circuits settings (ctx i) top b values.flatten
        root randomness enc (records i) (lockstepStart circuits (ctx i).keys.parameter
          (lockstepChunks settings enc (.bottom b)) (chunks settings.batchSize (bottomJobs b)).length,
            initial.2)).run) := by
      simpa only [← label] using localHead
    have atStep := schedule.from.advance_mem _ head
    simpa only [parameters i, self i, lockstepRoundStart, lockstepChunks, List.take_left] using atStep


/-- Audit erasure preserves pending programs at every cutoff, including aborts. -/
theorem treeLate_executeSteps_map {β : Type} (f : α → β) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    executeSteps worldRoles D A noFunctionality fuel state (fun i => treeSimCheckMapStep f (steps i)) =
      (fun r => (r.1, fun i => treeSimCheckMapStep f (r.2 i))) <$>
        executeSteps worldRoles D A noFunctionality fuel state steps := by
  induction fuel generalizing state steps with
  | zero => rfl
  | succ fuel ih =>
    simp only [executeSteps, treeSimCheckMapStep_isDone]
    split_ifs
    · rfl
    · rw [treeSimCheck_stepRound_map, map_bind]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      exact bind_congr fun r => ih r.1 r.2.1

theorem treeLate_segments_map {β : Type} (f : α → β)
    (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j : ℕ)
    (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (h : TreeSegmentsFrom S j p) : TreeSegmentsFrom S j (Option.map f <$> p) := by
  induction h with
  | pure j out => simpa only [map_pure] using TreeSegmentsFrom.pure j (out.map f)
  | queryLocal j q k hq h ih => exact .queryLocal j q _ hq ih
  | round j out k h ih => exact .round j out _ ih

theorem treeLate_segmentsStep_map {β : Type} (f : α → β)
    (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j : ℕ) (step : Step C E RealSpec α)
    (h : SegmentsStep S j step) : SegmentsStep S j (treeSimCheckMapStep f step) := by
  cases step with
  | done _ => trivial
  | wait out resume => exact fun inbox => treeLate_segments_map f S j _ (h inbox)
  | call input _ => exact input.elim

/-- A fixed schedule propagates through the exact retained suffix, including
the final rejecting round and the persistent all-aborted state. -/
theorem treeLate_segments_steps (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (S : C.Party → ℕ → C.Term → HashOutput → ℕ → Prop) :
    ∀ (fuel j : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α)
      (s : TreeSimState C) (r : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C),
      (∀ i, i ∉ D.1 → SegmentsStep (S i) j (steps i)) →
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executeSteps worldRoles D A noFunctionality fuel state steps)).run s) →
      ∃ log, r.2.2 = s.2 ++ log ∧
        (∀ i, i ∉ D.1 → SegmentsStep (S i) (j+fuel) (r.1.2 i)) ∧
        ∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
          ∃ i, i ∉ D.1 ∧ ∃ k, j ≤ k ∧ k < j+fuel ∧ SaltRead (S i k) y
  | 0, j, state, steps, s, r, hs, run => by
    simp only [executeSteps, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact ⟨[], by simp, by simpa only [Nat.add_zero] using hs, by simp⟩
  | fuel+1, j, state, steps, s, r, hs, run => by
    simp only [executeSteps] at run
    split_ifs at run with stopped
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      refine ⟨[], by simp, ?_, by simp⟩
      intro i hi
      dsimp only
      have hd := stopped i hi
      cases h : steps i with
      | done out => trivial
      | wait _ _ => simp [h, Step.isDone] at hd
      | call input _ => exact input.elim
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨mid, hm, tail⟩ := run
      have raw := (treeLockstep_logged_run_allowed prims D _ s mid hm).choose_spec.1.mem_support
      have next := segmentsStep_round D A state steps S j hs mid.1 raw
      obtain ⟨log, hlog, finalSteps, finalLog⟩ := treeLate_segments_steps prims D A S fuel (j+1)
        mid.1.1 mid.1.2.1 mid.2 r next tail
      obtain ⟨now, hnow, rows⟩ := worldSalts_round prims D
        (fun y => ∃ i, i ∉ D.1 ∧ SaltRead (S i j) y) A state steps
        (fun i hi => by
          have h := hs i hi
          revert h
          cases steps i with
          | done _ => intro _; trivial
          | call input _ => exact input.elim
          | wait out resume => exact fun h inbox => (h inbox).segmentSalts fun y hy => ⟨i, hi, hy⟩)
        s mid hm
      refine ⟨now ++ log, by rw [hlog, hnow, List.append_assoc], ?_, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalSteps
      · intro y b h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨i, hi, hy⟩ := rows y b h
          exact ⟨i, hi, j, le_rfl, by omega, hy⟩
        · obtain ⟨i, hi, k, hj, hk, hy⟩ := finalLog y b h
          exact ⟨i, hi, k, by omega, by omega, hy⟩


/-- Erasure commutes with the entire retained phase, not only final outputs. -/
theorem treeLate_phase_map {β : Type} (f : α → β) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) :
    (startSteps worldRoles D (fun i => f <$> p i) >>= fun steps =>
      executeSteps worldRoles D A noFunctionality fuel state steps) =
      (fun r => (r.1, fun i => treeSimCheckMapStep f (r.2 i))) <$>
        (startSteps worldRoles D p >>= fun steps =>
          executeSteps worldRoles D A noFunctionality fuel state steps) := by
  rw [treeSimCheck_startSteps_map, map_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  exact bind_congr fun steps => treeLate_executeSteps_map f D A fuel state steps

/-- The setup continuation erases the audit at the pending-step level. -/
theorem treeLate_setup_erase (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) :
    treeSimContinue (treeSimRealCont K circuits settings top tree x) setup =
      (fun steps i => treeSimCheckMapStep Prod.fst (steps i)) <$>
        free (Concrete.sequenceFin fun i => continueStep
          (fun pi => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, pi⟩ top tree)
          (.done (setup i))) := by
  unfold treeSimContinue
  simp only [free_sequenceFin]
  have hl (i) : free (continueStep (treeSimRealCont K circuits settings top tree x i) (.done (setup i))) =
      treeSimCheckMapStep Prod.fst <$> free (continueStep
        (fun pi => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, pi⟩ top tree) (.done (setup i))) := by
    cases hs : setup i with
    | none => simp [continueStep, free_pure, treeSimCheckMapStep]
    | some pi =>
      simp only [continueStep, treeSimRealCont]
      rw [← treeSimCheckAfterSetupAudit_erase K circuits settings ⟨i, x i, pi⟩ top tree]
      rw [OptionT.run_map, treeSimCheck_advance_map]
      simp only [map_eq_bind_pure_comp, free_bind, free_pure, Function.comp_def]
  simp_rw [hl]
  simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]

/-- Completing absent setup contexts preserves the original retained phase,
via exact audit erasure. -/
theorem treeLate_setup_trace (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (ctx : C.Party → Context C)
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (start : free (Concrete.sequenceFin fun i => continueStep
      (fun pi => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, pi⟩ top tree) (.done (setup i))) =
      startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
        treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree)) :
    (treeSimContinue (treeSimRealCont K circuits settings top tree x) setup >>= fun steps =>
      executeSteps worldRoles D A noFunctionality fuel state steps) =
      (fun r => (r.1, fun i => treeSimCheckMapStep Prod.fst (r.2 i))) <$>
        (startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree) >>= fun steps =>
            executeSteps worldRoles D A noFunctionality fuel state steps) := by
  rw [treeLate_setup_erase, start, map_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  exact bind_congr fun steps => treeLate_executeSteps_map Prod.fst D A fuel state steps


/-- The retained real runner is the logged simulation of the world runner. -/
theorem treeLate_executeSteps_real (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    executeSteps (treeSimRealRoles prims D) D A noFunctionality fuel state steps =
      simulateQ (treeSimLoggedWorld prims D) (executeSteps worldRoles D A noFunctionality fuel state steps) := by
  induction fuel generalizing state steps with
  | zero => simp only [executeSteps, simulateQ_pure]
  | succ fuel ih =>
    simp only [executeSteps]
    split_ifs
    · simp only [simulateQ_pure]
    · simp only [simulateQ_bind, ih, simulateQ_stepRound]
      rfl

/-- Lift one actual retained trace to the audit while preserving its full cache and log. -/
theorem treeLate_reach_audit (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (x : C.Party → Keys C) (parameter : PublicParameter)
    (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (fuel : ℕ)
    (s : TreeSimState C) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top (.bottom b) D A x state s fuel a)
    (good : ¬ TreeSimHashBudgetCollision a.2.2) :
    ∃ (ctx : C.Party → Context C) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
      (state' : A.State) (s' : TreeSimState C)
      (audit : (A.State × (C.Party → Step C E RealSpec
        (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C),
      (∀ i, (ctx i).self = i) ∧ (∀ i, (ctx i).keys.parameter = parameter) ∧
      Consistent D (fun i T => (ctx i).prss.term T) ∧
      audit ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top (.bottom b)) >>= fun steps =>
          executeSteps worldRoles D A noFunctionality fuel state' steps)).run s') ∧
      ((audit.1.1, fun i => treeSimCheckMapStep Prod.fst (audit.1.2 i)), audit.2) = a := by
  unfold TreeStagesReach treeStagesTrace at reach
  simp only [StateT.run_bind, mem_support_bind_iff] at reach
  obtain ⟨setup, hs, next, hn, tail⟩ := reach
  rw [treeLate_executeSteps_real] at tail
  have combined : a ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeSimContinue (treeSimRealCont K circuits settings top (.bottom b) x) setup.1.2 >>= fun steps =>
        executeSteps worldRoles D A noFunctionality
          fuel
          setup.1.1 steps)).run setup.2) := by
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    with_reducible exact ⟨next, hn, tail⟩
  have prefLog := by
    with_reducible exact (treeSimLoggedWorld_prefix prims D _ setup.2 a combined)
  have setupGood : ¬ TreeSimHashBudgetCollision setup.2.2 := fun h =>
    good (treeSimHashBudgetCollision_mono prefLog h)
  have agree := treeSetup_phase_agree prims D A state s setup hs setupGood
  have corrupt := treeSetup_corrupt_none prims D A state s setup hs
  obtain ⟨ctx, gate, self, uniform, keys, start⟩ := treeLockstep_setup_contexts K circuits settings D x
    parameter parameters setup.1.2 corrupt agree top (.bottom b)
  rw [treeLate_setup_trace K circuits settings D A _ _ _ _ _ _ ctx gate start,
    simulateQ_map, StateT.run_map, support_map] at combined
  obtain ⟨audit, auditRun, equal⟩ := combined
  exact ⟨ctx, gate, setup.1.1, setup.2, audit, self, uniform, keys, auditRun, equal⟩

/-- An actual live first-run boundary of the original ceremony fixes one
encoding for all later honest segments. The setup and audit are obtained from
that very prefix, and the full reached log remains unchanged. -/
theorem treeLate_reach_boundary (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (x : C.Party → Keys C) (parameter : PublicParameter)
    (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (hash : Query C → HashOutput)
    (s : TreeSimState C) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top (.bottom b) D A x state s
      (((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum) a)
    (good : ¬ TreeSimHashBudgetCollision a.2.2)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ a.2.2 →
      TreeSimCheckWorldHashes hash t u)
    (live : ∃ i, i ∉ D.1 ∧ a.1.2 i ≠ .done none) :
    ∃ enc : Encoding, ∀ i, i ∉ D.1 → SegmentsStep
      (fun j _ _ label => TreeLateScheduleShape circuits settings parameter b enc j label)
      ((((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum)+1)
      (a.1.2 i) := by
  obtain ⟨ctx, gate, state', s', audit, self, uniform, keys, auditRun, equal⟩ :=
    treeLate_reach_audit K circuits settings prims D A state x parameter parameters top b _ s a reach good
  have logs : audit.2.2 = a.2.2 := congrArg (fun v => v.2.2) equal
  have steps : ∀ i, treeSimCheckMapStep Prod.fst (audit.1.2 i) = a.1.2 i :=
    fun i => congrArg (fun v => v.1.2 i) equal
  have auditLive : ∃ i, i ∉ D.1 ∧ audit.1.2 i ≠ .done none := by
    obtain ⟨i, hi, live⟩ := live
    refine ⟨i, hi, fun dead => live ?_⟩
    rw [← steps i, dead]
    rfl
  have auditGood : ¬ TreeSimHashBudgetCollision audit.2.2 := logs ▸ good
  have auditRows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ audit.2.2 →
      TreeSimCheckWorldHashes hash t u := logs ▸ rows
  obtain ⟨enc, schedule⟩ := treeLate_bottom_boundary K circuits settings prims D A state' ctx self
    parameter uniform keys gate top b hash s' audit auditRun auditGood auditRows auditLive
  refine ⟨enc, ?_⟩
  intro i hi
  rw [← steps i]
  have erased := treeLate_segmentsStep_map Prod.fst _ _ _ (schedule i hi)
  revert erased
  cases treeSimCheckMapStep Prod.fst (audit.1.2 i) with
  | done _ => intro _; trivial
  | call input _ => exact input.elim
  | wait out resume =>
    intro h inbox
    exact (h inbox).mono fun _ _ _ _ hs => hs.2.2

/-- Every salt retained through the first-run boundary has the same schedule
under any selected encoding. Setup and the incoming prefix add no such salts. -/
theorem treeLate_early_log (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (x : C.Party → Keys C) (parameter : PublicParameter)
    (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (enc : Encoding)
    (s : TreeSimState C) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top (.bottom b) D A x state s
      (((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum) a)
    (noSalt : ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ s.2 → SaltRead (fun _ _ _ => False) y) :
    ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ a.2.2 →
      ∀ T key label g, y = (.term T, key, label, 2, g) →
        ∃ j ≤ ((chunks settings.batchSize (bottomJobs b)).map
          (batchRounds circuits settings.mode parameter)).sum,
          TreeLateScheduleShape circuits settings parameter b enc j label := by
  obtain ⟨setup, hs, log, logs, _, salt⟩ :=
    segments_reach prims K circuits settings D top (.bottom b) A x state s _ a reach
  intro y bit hy T key label g eq
  rw [logs] at hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨added, append, noSalt'⟩ := treeSetup_noSalt prims D A state s setup hs
    rw [append] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (noSalt y bit hy T key label g eq).elim
    · exact (noSalt' y bit hy T key label g eq).elim
  · obtain ⟨i, hi, j, hj, salt⟩ := salt y bit hy
    obtain ⟨prss, _, schedule⟩ := salt T key label g eq
    rw [parameters i hi] at schedule
    have early : j ≤ lockstepRoundStart circuits settings.mode parameter
        (lockstepChunks settings enc (.bottom b)) (chunks settings.batchSize (bottomJobs b)).length + 2 := by
      simpa only [lockstepRoundStart, lockstepChunks, List.take_left] using (show j ≤
        ((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum + 2 by omega)
    exact ⟨j, hj, (ceremonySchedule_before_second circuits settings settings.mode parameter prss.term i b enc
      j T key label early schedule).2.2⟩

/-- Split one retained run without projecting pending steps or changing caches. -/
theorem treeLate_reach_split (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (x : C.Party → Keys C) (top : TopTree) (tree : Tree)
    (s : TreeSimState C) (a : TreeSimConfig A (TreeSimState C)) (m n : ℕ)
    (reach : TreeStagesReach prims K circuits settings top tree D A x state s (m+n) a) :
    ∃ middle, TreeStagesReach prims K circuits settings top tree D A x state s m middle ∧
      a ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executeSteps worldRoles D A noFunctionality n middle.1.1 middle.1.2)).run middle.2) := by
  unfold TreeStagesReach at reach ⊢
  rw [treeStages_trace_add] at reach
  simp only [StateT.run_bind, mem_support_bind_iff] at reach
  obtain ⟨middle, hm, tail⟩ := reach
  rw [treeLate_executeSteps_real] at tail
  exact ⟨middle, hm, tail⟩

/-- A common encoding covers the entire actual retained log and every next
honest segment, including prefixes whose second run has already aborted. -/
theorem treeLate_reached_schedule (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (x : C.Party → Keys C) (parameter : PublicParameter)
    (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (hash : Query C → HashOutput)
    (s : TreeSimState C) (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top (.bottom b) D A x state s n a)
    (good : ¬ TreeSimHashBudgetCollision a.2.2)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ a.2.2 →
      TreeSimCheckWorldHashes hash t u)
    (noSalt : ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ s.2 → SaltRead (fun _ _ _ => False) y)
    (late : ((chunks settings.batchSize (bottomJobs b)).map
      (batchRounds circuits settings.mode parameter)).sum ≤ n) :
    ∃ enc : Encoding,
      (∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
          (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ a.2.2 →
        ∀ T key label g, y = (.term T, key, label, 2, g) →
          ∃ j ≤ n, TreeLateScheduleShape circuits settings parameter b enc j label) ∧
      ∀ i, i ∉ D.1 → SegmentsStep
        (fun j _ _ label => TreeLateScheduleShape circuits settings parameter b enc j label)
        (n+1) (a.1.2 i) := by
  let first := ((chunks settings.batchSize (bottomJobs b)).map
    (batchRounds circuits settings.mode parameter)).sum
  have length : n = first + (n-first) := by dsimp only [first]; omega
  have reach' : TreeStagesReach prims K circuits settings top (.bottom b) D A x state s
      (first + (n-first)) a := length ▸ reach
  obtain ⟨middle, hm, tail⟩ := treeLate_reach_split K circuits settings prims D A state x top (.bottom b)
    s a first (n-first) reach'
  have prefLog := treeSimLoggedWorld_prefix prims D _ middle.2 a tail
  have midGood : ¬ TreeSimHashBudgetCollision middle.2.2 := fun h =>
    good (treeSimHashBudgetCollision_mono prefLog h)
  have midRows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ middle.2.2 →
      TreeSimCheckWorldHashes hash t u := fun t u h => rows t u (prefLog.subset h)
  have boundary : ∃ enc : Encoding, ∀ i, i ∉ D.1 → SegmentsStep
      (fun j _ _ label => TreeLateScheduleShape circuits settings parameter b enc j label)
      (first+1) (middle.1.2 i) := by
    by_cases live : ∃ i, i ∉ D.1 ∧ middle.1.2 i ≠ .done none
    · exact treeLate_reach_boundary K circuits settings prims D A state x parameter parameters top b hash
        s middle hm midGood midRows live
    · refine ⟨fun _ => digit 0, fun i hi => ?_⟩
      have dead : middle.1.2 i = .done none := by by_contra h; exact live ⟨i, hi, h⟩
      rw [dead]
      trivial
  obtain ⟨enc, boundary⟩ := boundary
  obtain ⟨log, logs, finalSteps, logRows⟩ := treeLate_segments_steps prims D A
    (fun _ j _ _ label => TreeLateScheduleShape circuits settings parameter b enc j label)
    (n-first) (first+1) middle.1.1 middle.1.2 middle.2 a boundary tail
  have early := treeLate_early_log K circuits settings prims D A state x parameter parameters top b enc
    s middle hm noSalt
  refine ⟨enc, ?_, ?_⟩
  · intro y bit hy T key label g eq
    rw [logs] at hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨j, hj, shape⟩ := early y bit hy T key label g eq
      exact ⟨j, hj.trans late, shape⟩
    · obtain ⟨i, hi, j, _, hj, salt⟩ := logRows y bit hy
      exact ⟨j, by omega, salt T key label g eq⟩
  · have count : first+1+(n-first) = n+1 := by omega
    rwa [count] at finalSteps

/-- The exact late-bottom goal, retaining aborted prefixes and the target's
arbitrary setup witness. No final-success or extra readiness premise is used. -/
theorem treeLockstepEncodingLateBottom (prims : Primitives) :
    TreeLockstepEncodingLateBottomGoal circuits settings prims K := by
  intro _ top b D A parameter seeds pairs z p hp padding r hr n a reach good ps _ l logs hsteps hlog late
  have afterFirst : ((chunks settings.batchSize (bottomJobs b)).map
      (batchRounds circuits settings.mode parameter)).sum ≤ n := by
    simp only [lockstepRoundStart, lockstepChunks, List.take_left] at late
    omega
  obtain ⟨hash, _, rows⟩ := treeLate_reached_hashes prims K circuits settings top (.bottom b) D A
    parameter seeds pairs z p hp padding r hr n a reach
  obtain ⟨enc, fullShape, next⟩ := treeLate_reached_schedule K circuits settings prims D A p.2.1
    (dealtKeys parameter seeds pairs) parameter (fun _ _ => rfl) top b hash _ n a reach good rows
    (treeSimCommonPrefix_noSalt circuits prims settings top (.bottom b) D A parameter seeds pairs z p hp)
    afterFirst
  refine treeLate_scheduleAt_transfer circuits settings (dealtKeys parameter seeds pairs) parameter b enc
    ps.1.2 D (fun _ _ => rfl) n a.1.2 a.2.2 ps.2.2 l logs hsteps hlog fullShape ?_
  intro i hi
  have h := next i hi
  revert h
  cases a.1.2 i with
  | done out => intro _; trivial
  | call input _ => exact input.elim
  | wait out resume =>
    intro h inbox
    exact (h inbox).segmentSalts fun y hy => hy

/-- The complete retained-prefix encoding agreement, using A61's proved early
and top cases and the exact late-bottom theorem above. -/
theorem treeLockstepEncoding (prims : Primitives) :
    TreeLockstepEncodingGoal circuits prims K settings :=
  treeLockstepEncodingGoal_of_late_bottom circuits settings prims K
    (treeLockstepEncodingLateBottom K circuits settings prims)

/-- The original lockstep salt-segment goal follows with no remaining premise. -/
theorem treeLockstepSegments (prims : Primitives) :
    TreeLockstepSegmentsGoal circuits prims K settings :=
  treeLockstepSegmentsGoal_of_encoding circuits prims K settings
    (treeLockstepEncoding K circuits settings prims)

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepEncodingLateBottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepEncodingLateBottom

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepEncoding

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepSegments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepSegments

end ThresholdLeanXmssSecurity
