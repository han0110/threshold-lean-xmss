import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkState

/-!
# The walk state at the end of the first run

This file concerns `WalkStateEntry` of `TreeCheckWalkState`, for the fixed
walk `family` of `TreeCheckWalkRecipe`. The family, its decoder and its
witness are not changed. `L` is the number of batches of the first run.

## Lemmas

* `residual_batch_cont` takes one batch `j` of the first run, also the last
  one. The residual after `batchRounds` exchanges is an abort, or the
  continuation `callerCont` of batch `j` after a local tail, at a real
  output `some value`, one real record and the counters of batch `j + 1`. Its
  proof repeats the steps of `residual_batch`, because `residual_batch` does
  not give the output and does not cover the last batch.
* `residual_batch_some` is the case `j + 1 < L`. The new caller has one more
  output `some value`.
* `residual_first_some` iterates this. After the batches before `j`, the
  program is an abort, or `callerProgram j` of a caller whose saved outputs
  are all `some`.
* `residual_last` takes the last batch `j + 1 = L`. The residual is an abort,
  or `treeLockstepFirstRest` after a tail, at `some` of the concatenated
  outputs, the saved records with the new record, and the counters
  `signingInitial`.
* `firstChunks_bottom_pos` states that the first run of a bottom tree has a
  batch, and `batchStart_last` splits `batchStart L` at the last batch.
* `walkStateEntry` is `WalkStateEntry`. The signing point of a party that did
  not abort holds the real outputs, records and tail of `residual_last`. An
  aborted party gets the tail `pure none` and `L` copies of a placeholder
  record. These placeholders are only behind `pure none`, so its program does
  not read them.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkEntry

open TreeCheckWalkRecipe TreeCheckWalkCoverage TreeCheckWalkState

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

theorem foldlM_some (vs : List (List (List Bit))) (acc : List (List Bit)) :
    (vs.map some).foldlM (fun acc batch => batch.map (acc ++ ·)) acc = some (acc ++ vs.flatten) := by
  induction vs generalizing acc with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.foldlM_cons, Option.map_some, Option.bind_eq_bind,
      Option.bind_some, List.flatten_cons]
    rw [ih, List.append_assoc]

section Batch

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

set_option maxHeartbeats 1000000 in
/-- Inside the first run, the residual of the program at the start of batch
`j` after the exchanges of that batch is an abort, or the continuation of
batch `j` after a tail, at a real output, one record and the counters of batch
`j + 1`. -/
theorem residual_batch_cont (j : ℕ) (current : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (value : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        callerCont K circuits settings top tree x setup j caller i
          ((some value, [record]), (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings tree) (j + 1), j + 1))).run := by
  unfold callerProgram at h
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding j current.le,
    treeSimCheckBatchAudit_run_prefix] at h
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (firstChunks settings tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  rw [show (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
      (treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j) >>=
        treeSimCheckBatchFinish K circuits ctx jobs (start, j)) >>=
          callerCont K circuits settings top tree x setup j caller i) =
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
            callerCont K circuits settings top tree x setup j caller i) by
    simp only [bind_assoc]] at h
  have prefixTimed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  rw [parameter] at prefixTimed
  rw [show batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter jobs =
      (depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        (checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) + 1) by
      unfold batchRounds
      omega] at h
  rcases Residual.party_bind prefixTimed h with none | ⟨data, hdata, h⟩
  · exact .inl none
  obtain ⟨-, -, hprefix⟩ := treeSimCheck_some_bind _ _ _ hdata
  obtain ⟨-, hlabel, -, -, -⟩ :=
    treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hprefix
  have hcount : (data.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    unfold treeSimCheckBatchPrefix at hprefix
    obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ hprefix
    obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
    have he' : data = (inputs, q) := by simpa only [OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] using he
    subst data
    exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs start j q.1 q.2 hq
  rw [parameter] at hcount hlabel
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify at h
  simp only [bind_assoc, pure_bind] at h
  have checkTimed := check_timed K ctx data.2.1.2 data.2.2
  rw [hcount] at checkTimed
  rcases Residual.party_bind checkTimed h with none | ⟨checked, hchecked, h⟩
  · exact .inl none
  have finalLabel := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
  rw [hcount, hlabel] at finalLabel
  rcases residual_openRep K ctx _ _ _ h with none | ⟨inbox, rfl⟩
  · exact .inl none
  refine .inr ?_
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  rw [labels]
  exact ⟨_, _, _, rfl⟩

/-- `residual_batch_cont` before the last batch of the first run. The new
caller has one more output `some value` and one more record. -/
theorem residual_batch_some (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (value : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      Q = (callerProgram K D circuits settings top tree x setup (j + 1)
        (stepCaller caller i (some value, [record]) tail) i).run := by
  rcases residual_batch_cont K D circuits settings top tree x setup j (by omega) caller i same h with
    none | ⟨value, record, tail, rfl⟩
  · exact .inl none
  refine .inr ⟨value, record, tail, ?_⟩
  rw [callerCont_step K circuits settings top tree x setup j next caller i _ tail]
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree _ (j + 1) next,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ _ (j + 1) next.le]
  simp only [stepCaller]

/-- Inside the first run, the residual of the first program after the batches
before batch `j` is an abort, or the program at the start of batch `j` for a
caller whose saved outputs are all `some`. -/
theorem residual_first_some (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some) :
    ∀ j, j < (firstChunks settings tree).length →
    ∀ {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))},
      Residual (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j)
        (callerProgram K D circuits settings top tree x setup 0 caller i).run Q →
      Q = pure none ∨ ∃ caller' : Caller C,
        (caller'.records i).length = (caller.records i).length + j ∧
        (∃ values : List (List (List Bit)), caller'.outputs i = values.map some) ∧
        Q = (callerProgram K D circuits settings top tree x setup j caller' i).run
  | 0, _, Q, h => .inr ⟨caller, rfl, outputs, h.zero_inv⟩
  | j + 1, next, Q, h => by
    have current : j < (firstChunks settings tree).length := by omega
    rw [show batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (j + 1) =
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j +
          batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
            ((firstChunks settings tree).getD j []) by
      simp only [batchStart, List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem current, Option.toList_some, Option.getD_some, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]] at h
    obtain ⟨M, first, second⟩ := h.split
    rcases residual_first_some caller i same outputs j current first with rfl | ⟨middle, records, ⟨values, saved⟩, rfl⟩
    · exact .inl second.pure_inv
    rcases residual_batch_some K D circuits settings top tree x setup j next middle i same second with
      none | ⟨value, record, tail, rfl⟩
    · exact .inl none
    refine .inr ⟨_, ?_, ⟨values ++ [value], ?_⟩, rfl⟩
    · simp only [stepCaller, List.length_append, List.length_singleton, records]
      omega
    · simp only [stepCaller, saved, List.map_append, List.map_singleton]

/-- The last batch of the first run. The residual is an abort, or
`treeLockstepFirstRest` after a tail, at `some` outputs, the saved records with
one more record and the counters after the first run. -/
theorem residual_last (j : ℕ) (last : j + 1 = (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (opened : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
          ((some opened, caller.records i ++ [record]),
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
              (firstChunks settings tree) (j + 1), j + 1))).run := by
  have current : j < (firstChunks settings tree).length := by omega
  rcases residual_batch_cont K D circuits settings top tree x setup j current caller i same h with
    none | ⟨value, record, tail, rfl⟩
  · exact .inl none
  obtain ⟨values, saved⟩ := outputs
  refine .inr ⟨values.flatten ++ value, record, tail, ?_⟩
  have empty : (firstChunks settings tree).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
  unfold callerCont
  simp only [phaseChunks, phaseIndex, if_pos current, empty, List.mapM_nil, saved]
  simp [foldlM_some]

end Batch

section Assembly

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The first run of a bottom tree has at least one batch. -/
theorem firstChunks_bottom_pos (positive : 0 < settings.batchSize) (b : Fin (2 ^ layerHeight)) :
    0 < (firstChunks settings (.bottom b)).length := by
  change 0 < (chunks settings.batchSize (bottomJobs b)).length
  rw [length_chunks]
  have jobs : 0 < (bottomJobs b).length := by simp [bottomJobs]
  exact Nat.div_pos (by omega) positive

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The exchanges of the first run are those before its last batch and those
of its last batch. -/
theorem batchStart_last (tree : Tree) (parameter : PublicParameter) (j : ℕ)
    (last : j + 1 = (firstChunks settings tree).length) :
    batchStart circuits settings tree parameter (firstChunks settings tree).length =
      batchStart circuits settings tree parameter j +
        batchRounds circuits settings.mode parameter ((firstChunks settings tree).getD j []) := by
  have current : j < (firstChunks settings tree).length := by omega
  rw [← last]
  simp only [batchStart, List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem current, Option.toList_some, Option.getD_some, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem walkStateEntry : WalkStateEntry prims K circuits settings := by
  intro positive top b D A x z Z dealt p _ q reached
  have pos := firstChunks_bottom_pos settings positive b
  obtain ⟨j, last⟩ : ∃ j, j + 1 = (firstChunks settings (.bottom b)).length :=
    ⟨(firstChunks settings (.bottom b)).length - 1, by omega⟩
  have current : j < (firstChunks settings (.bottom b)).length := by omega
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos pos)
  have same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    intro i
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  have rounds := batchStart_last circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter j last
  have each : ∀ i, ∃ point : List (List Bit) × List (TreeSimCheckBatchRecord C) ×
      OracleComp (LocalSpec C) (Option Unit), i ∉ D.1 →
      point.2.1.length = (firstChunks settings (.bottom b)).length ∧
      q.program i = treeLockstepLocalPrelude point.2.2 >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys p.1.2 i⟩ top (.bottom b)
          ((some point.1, point.2.1), signingInitial K D circuits settings (.bottom b) x) := by
    intro i
    by_cases hi : i ∈ D.1
    · exact ⟨([], [], pure none), fun h => (h hi).elim⟩
    have abort : (q.program i).run = pure none → ∃ point : List (List Bit) × List (TreeSimCheckBatchRecord C) ×
        OracleComp (LocalSpec C) (Option Unit), i ∉ D.1 →
        point.2.1.length = (firstChunks settings (.bottom b)).length ∧
        q.program i = treeLockstepLocalPrelude point.2.2 >>= fun _ =>
          treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys p.1.2 i⟩ top (.bottom b)
            ((some point.1, point.2.1), signingInitial K D circuits settings (.bottom b) x) := by
      intro aborted
      let record : TreeSimCheckBatchRecord C :=
        ⟨⟨i, x i, setupKeys p.1.2 i⟩, [], (0, 0), [], [], ⟨fun _ => [], 0, 0⟩, [], ⟨fun _ => [], 0, 0⟩⟩
      refine ⟨([], List.replicate (firstChunks settings (.bottom b)).length record, pure none),
        fun _ => ⟨List.length_replicate, ?_⟩⟩
      apply OptionT.ext
      rw [aborted, localPrelude_none, failure_bind, OptionT.run_failure]
    have residual := reached.residual prims D Z i hi
    rw [initial_program K D A circuits settings top (.bottom b) x p head rest chunked i,
      boundary_program, rounds] at residual
    obtain ⟨M, first, second⟩ := residual.split
    rcases residual_first_some K D circuits settings top (.bottom b) x p.1.2 (firstCaller p.1.2) i (same i)
        ⟨[], rfl⟩ j current first with rfl | ⟨middle, records, outputs, rfl⟩
    · exact abort second.pure_inv
    rcases residual_last K D circuits settings top (.bottom b) x p.1.2 j last middle i (same i) outputs second with
      none | ⟨opened, record, tail, program⟩
    · exact abort none
    refine ⟨(opened, middle.records i ++ [record], tail), fun _ => ⟨?_, ?_⟩⟩
    · simp only [List.length_append, List.length_singleton, records, firstCaller, List.length_nil]
      omega
    · apply OptionT.ext
      rw [program]
      simp only [signingInitial, last]
  choose points facts using each
  exact ⟨⟨fun i => (points i).1, fun i => (points i).2.1, fun i => (points i).2.2⟩,
    fun i hi => (facts i hi).1, fun i hi => (facts i hi).2⟩

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEntry.residual_batch_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_batch_cont

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEntry.residual_first_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_first_some

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEntry.residual_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_last

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEntry.walkStateEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkStateEntry

end TreeCheckWalkEntry
end ThresholdLeanXmssSecurity
