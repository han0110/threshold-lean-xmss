import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgFirstFresh
import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgSigningClock
import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgProbe
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCacheSigning

/-! # Hidden-cache freshness at live signing checkpoints

Actual local passes share a PRG clock. The first signing pass consumes its
initial label; the following cutoff and every later pass use the same clock.
A live checkpoint probes this floor on one actual first-pass witness.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckWalkEntry TreeCheckWalkEncoding
open TreeCheckHonestDisc TreeCheckPrgDisc TreeCheckPrgWindow TreeCheckPrgClock TreeCheckPrgFloor
open TreeCheckPrgSigningClock TreeCheckPrgFirstFresh TreeCheckSigningClock TreeCheckSigningChoice
open TreeCheckWalkCacheSigning TreeSimHashCount TreeCheckWalkCache
attribute [local instance] Classical.propDecidable
attribute [local irreducible] treeLockstepPublicChoiceCode merkleNode merklePath Concrete.layerRoot tweakable
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
variable {C : Committee} {E α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition)
variable (K : Constants C E) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))
variable (Z : Distinguisher C A.State TreeOutput)

-- Port of TreeCheckWalkEntry.residual_batch_some, keeping the literal quiet tail.
theorem residual_batch_some_prg (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ (value : List (List Bit)) (record : TreeSimCheckBatchRecord C)
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      (∀ L, IsQueryBoundP tail (PrgFrom L) 0) ∧
      Q = (callerProgram K D circuits settings top tree x setup (j + 1)
        (stepCaller caller i (some value, [record]) tail) i).run := by
  rcases residual_batch_cont_prg circuits settings K D top tree x setup j (by omega) caller i same h with
    none | ⟨value, record, tail, quiet, rfl⟩
  · exact .inl none
  refine .inr ⟨value, record, tail, quiet, ?_⟩
  rw [callerCont_step K circuits settings top tree x setup j next caller i _ tail]
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree _ (j + 1) next,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ _ (j + 1) next.le]
  simp only [stepCaller]

-- Port of TreeCheckWalkEntry.residual_first_some, keeping the literal quiet tail.
theorem residual_first_some_prg (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : ∀ L, IsQueryBoundP (caller.tail i) (PrgFrom L) 0)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some) :
    ∀ j, j < (firstChunks settings tree).length →
    ∀ {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))},
      Residual (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j)
        (callerProgram K D circuits settings top tree x setup 0 caller i).run Q →
      Q = pure none ∨ ∃ caller' : Caller C,
        (caller'.records i).length = (caller.records i).length + j ∧
        (∃ values : List (List (List Bit)), caller'.outputs i = values.map some) ∧
        (∀ L, IsQueryBoundP (caller'.tail i) (PrgFrom L) 0) ∧
        Q = (callerProgram K D circuits settings top tree x setup j caller' i).run
  | 0, _, Q, h => .inr ⟨caller, rfl, outputs, quiet, h.zero_inv⟩
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
    rcases residual_first_some_prg caller i same quiet outputs j current first with rfl | ⟨middle, records, ⟨values, saved⟩, quietMiddle, rfl⟩
    · exact .inl second.pure_inv
    rcases residual_batch_some_prg D K circuits settings top tree x setup j next middle i same second with
      none | ⟨value, record, tail, quietTail, rfl⟩
    · exact .inl none
    refine .inr ⟨_, ?_, ⟨values ++ [value], ?_⟩, quietTail, rfl⟩
    · simp only [stepCaller, List.length_append, List.length_singleton, records]
      omega
    · simp only [stepCaller, saved, List.map_append, List.map_singleton]

/-- The complete first run leaves the actual quiet opening tail at its entry. -/
theorem residual_first_entry_prg (positive : 0 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : ∀ L, IsQueryBoundP (caller.tail i) (PrgFrom L) 0)
    (outputs : ∃ values : List (List (List Bit)), caller.outputs i = values.map some)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (run : Residual (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree).length)
      (callerProgram K D circuits settings top tree x setup 0 caller i).run Q) :
    Q = pure none ∨ ∃ (opened : List (List Bit)) (records : List (TreeSimCheckBatchRecord C))
      (tail : OracleComp (LocalSpec C) (Option Unit)),
      (∀ L, IsQueryBoundP tail (PrgFrom L) 0) ∧
      Q = (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
          ((some opened, records),
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
              (firstChunks settings tree) (firstChunks settings tree).length,
              (firstChunks settings tree).length))).run := by
  obtain ⟨j, last⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (firstChunks settings tree).length ≠ 0)
  have last' : j + 1 = (firstChunks settings tree).length := last.symm
  rw [TreeCheckWalkEntry.batchStart_last circuits settings tree _ j last'] at run
  obtain ⟨M, first, second⟩ := run.split
  rcases residual_first_some_prg D K circuits settings top tree x setup caller i same quiet outputs j
    (by omega) first with aborted | ⟨middle, records, outputs', quiet', rfl⟩
  · rw [aborted] at second
    exact .inl second.pure_inv
  · rcases residual_last_prg circuits settings K D top tree x setup j last' middle i same outputs' second with
      aborted | ⟨opened, record, tail, quietTail, equal⟩
    · exact .inl aborted
    · exact .inr ⟨opened, middle.records i ++ [record], tail, quietTail, by simpa only [last'] using equal⟩

/-- The complete first run bounds PRG labels by its final counter. -/
theorem initial_complete_prgDisc
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (positive : 0 < (firstChunks settings tree).length) (dealt : DealtInputs D x) (i : C.Party) :
    PrgDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) (firstChunks settings tree).length)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings tree).length)
      ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run := by
  obtain ⟨upper, disc, _⟩ := initial_program_prgClock circuits settings K D top tree x A start
    positive dealt _ le_rfl
  exact (disc i).mono upper

-- Port of Disc.bind, restricting its continuation to the requested horizon.
theorem prgDisc_bind_prefix {β : Type} {limit n : ℕ} 
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : ∀ m, PrgDisc limit m P)
    (f : Option α → OracleComp (PartySpec C E RealSpec) (Option β))
    (rest : ∀ a, a ∈ support P → PrgDisc limit n (f a)) :
    PrgDisc limit n (P >>= f) := by
  induction P generalizing n with
  | pure a =>
    change PrgDisc limit n (f a)
    exact (rest a (by change a ∈ support (Pure.pure a : OracleComp (PartySpec C E RealSpec) _); simp))
  | queryBind t k ih =>
    cases n with
    | zero => exact .zero _
    | succ n =>
      rcases t with (q | out) | impossible
      · refine .queryLocal _ _ _ (h (n + 1)).local_inv.1 fun r => ?_
        apply ih r (fun m => ?_) (fun a ha => ?_)
        · cases m with
          | zero => exact .zero _
          | succ m => exact (h (m + 1)).local_inv.2 r
        · apply rest a
          change a ∈ support (OracleComp.lift (OracleSpec.query
            (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
          rw [mem_support_bind_iff]
          exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
      · refine .round _ _ _ fun inbox => ?_
        apply ih inbox (fun m => (h (m + 1)).round_inv inbox) (fun a ha => ?_)
        apply (rest a ?_).antitone (Nat.le_succ n)
        change a ∈ support (OracleComp.lift (OracleSpec.query
          (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩
      · exact impossible.elim

theorem prgDisc_party_prefix {β : Type} {limit n : ℕ} {p : PartyM C E RealSpec α}
    {f : α → PartyM C E RealSpec β} (h : ∀ m, PrgDisc limit m p.run)
    (rest : ∀ a, some a ∈ support p.run → PrgDisc limit n (f a).run) :
    PrgDisc limit n (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  apply prgDisc_bind_prefix h
  intro a ha
  cases a with
  | none => exact .pure _ _
  | some a => exact rest a ha

theorem localOption_prg (limit : ℕ) (gate : OracleComp (LocalSpec C) (Option α))
    (quiet : IsQueryBoundP gate (PrgFrom limit) 0) :
    PartyBudget (PrgFrom limit) (treeLockstepLocalOption (E := E) gate) 0 := by
  unfold treeLockstepLocalOption
  refine (localStep_bound (E := E) (G := RealSpec) quiet).bind (m := 0) fun out => ?_
  cases out with
  | none => exact TreeCheckPrgWindow.party_quiet_of_zero limit PartyBound.failure
  | some _ => exact .pure _

variable (b : Fin (2 ^ layerHeight))

/-- The first signing pass reads below S+1, including its first layer at S. -/
theorem entry_first_prg (positive : 0 < settings.batchSize) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (outputs : List (List Bit)) (records : List (TreeSimCheckBatchRecord C))
    (tail : OracleComp (LocalSpec C) (Option Unit)) (quiet : IsQueryBoundP tail (PrgFrom 0) 0) :
    PrgDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length + 1) 1
      (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top (.bottom b)
          ((some outputs, records), signingInitial K D circuits settings (.bottom b) x)).run := by
  rw [signingHead_program]
  apply prgDisc_party_prefix (fun n => PrgDisc.of_quiet
    (party_prg_mono (Nat.zero_le _) (localOption_prg 0 _ (head_noPrg _ b _ _ quiet))) n)
  intro choice _
  obtain ⟨head, rest, chunks⟩ := signing_chunks_nonempty settings b positive choice.2.2
  rw [signingCont_caller K D circuits settings top x setup b (fun _ => outputs) (fun _ => records)
    choice head rest chunks i]
  let caller := signingCaller (fun _ => outputs) (fun _ => records) (fun _ => pure (some choice)) choice
  have current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b) := by
    have len := lockstepChunks_length settings choice.2.2 (.bottom b)
    simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs, List.length_append, chunks,
      List.length_cons] at len ⊢
    omega
  have clock := ((sign_caller_prgClock circuits settings K D top x setup b
    (firstChunks settings (.bottom b)).length 1 le_rfl current caller).2 i same
      (isQueryBoundP_pure _ _ _)).1
  rw [prgCallerClock_one circuits settings _ _ _ (by
    rw [lockstepChunks_length]; exact current), signing_start] at clock
  exact clock

/-- The complete first run and its next signing-entry pass use cutoff S+1. -/
theorem initial_entry_prgDisc (positive : 0 < settings.batchSize) (dealt : DealtInputs D x)
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) (i : C.Party) :
    PrgDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length + 1)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length + 1)
      ((TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start).program i).run := by
  have pos := firstChunks_bottom_pos settings positive b
  apply ((initial_complete_prgDisc D K A circuits settings top (.bottom b) x start pos dealt i).mono
    (Nat.le_succ _)).of_residual
  intro Q run
  obtain ⟨head, rest, chunks⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos pos)
  rw [initial_program K D A circuits settings top (.bottom b) x start head rest chunks i, boundary_program] at run
  have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]; rfl
  rcases residual_first_entry_prg D K circuits settings top (.bottom b) x start.1.2 pos
      (firstCaller start.1.2) i same (fun _ => isQueryBoundP_pure _ _ _) ⟨[], rfl⟩ run with
    aborted | ⟨outputs, records, tail, quiet, rfl⟩
  · rw [aborted]; exact .pure _ _
  · simpa only [ite_self, signingInitial] using
      entry_first_prg D K circuits settings top x start.1.2 b positive i same outputs records tail (quiet 0)

-- Port of H5 reached_futureEmpty at exactly N rather than N+1 passes.
theorem reached_futureEmpty_cut (limit N : ℕ) (start : TreeCheckWalkDef.Pending A)
    (fresh : TreeSimFutureEmpty limit start.world.1.2)
    (disc : ∀ i, i ∉ D.1 → PrgDisc limit N (start.program i).run)
    {m : ℕ} {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z start m q) (below : m ≤ N) :
    TreeSimFutureEmpty limit q.world.1.2 := by
  induction reached with
  | start => exact fresh
  | @next n fuel p q reached fuelLeft run ih =>
    apply next_futureEmpty prims D limit Z fuel p q (ih (by omega)) _ run
    intro i hi
    exact ((disc i hi).residual (Reached.residual prims D Z reached i hi) (by omega)).antitone (by omega)

-- Port of H9, retaining the log prefix of its same actual witness.
/-- The same first pass supports the PRG-label probe and hidden-cache transfer. -/
theorem boundary_prg_probe_prefix (Z : Distinguisher C A.State TreeOutput)
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
      out.2.2 <+: o.2.2 ∧
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
  refine ⟨out, firstRun, treeSimLoggedWorld_prefix prims D _ _ _ run, ?_, ?_⟩
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
    have finishFloor := TreeCheckPrgProbe.suspended_prgFloor (started.1 i) pending (k i) data replay floor
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
      dataNonzero limit (IsQueryBoundP.of_bind_left finishFloor)
    exact label ▸ le

/-- The decoded source retains an actual first pass whose live future floor
cannot exceed the label of the fixed hybrid. -/
theorem source_prg_probe_prefix (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
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
      out.2.2 <+: o.2.2 ∧
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
  obtain ⟨out, supported, pref, fresh, probe⟩ := boundary_prg_probe_prefix prims D K A circuits settings
    Z b self parameter nonzero o preRun r contRun i honest actual accepted
  refine ⟨out, ?_, pref, fresh, probe⟩
  have fits := decode_sound prims K D A circuits settings top tree x setup.1.2 j.val c
  rw [fits.2.2]
  exact supported

-- Port of A188 common-pass assembly with H8 PRG clocks.
/-- The actual first-pass output carries a common freshness cutoff and future floor. -/
def PrgPassClock (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C) : Prop :=
  ∃ limit, TreeSimFutureEmpty limit out.2.1.2 ∧
    ∀ i, i ∉ D.1 → ∀ inbox, PrgFloor limit (resumed (out.1 i) inbox)

theorem signing_suffix_prgClock (caller : Caller C)
    (same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : ∀ i, IsQueryBoundP (caller.tail i) (PrgFrom 0) 0)
    (current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b))
    (base q : TreeCheckWalkDef.Pending A) (t : ℕ)
    (common : ∀ i, i ∉ D.1 → (base.program i).run = pure none ∨
      Residual 1 (callerProgram K D circuits settings top (.bottom b) x setup
        (firstChunks settings (.bottom b)).length caller i).run (base.program i).run)
    (honest : ∀ limit, lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) (firstChunks settings (.bottom b)).length + 1 ≤ limit →
      TreeSimFutureEmpty limit base.world.1.2)
    (reached : Reached prims D Z base t q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A q)) : PrgPassClock D out := by
  obtain ⟨lower, clock⟩ := sign_caller_prgClock circuits settings K D top x setup b
    (firstChunks settings (.bottom b)).length (t + 2) le_rfl current caller
  set limit := prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding (.bottom b)) (firstChunks settings (.bottom b)).length (t + 2)
  have disc : ∀ i, i ∉ D.1 → PrgDisc limit (t + 1) (base.program i).run := by
    intro i hi
    rcases common i hi with aborted | residual
    · rw [aborted]; exact .pure _ _
    · simpa using ((clock i (same i) (quiet i)).1.residual residual (by omega))
  have lower' := prgCallerClock_mono circuits settings (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding (.bottom b)) (firstChunks settings (.bottom b)).length
    (show 1 ≤ t + 2 by omega)
  rw [prgCallerClock_one circuits settings _ _ _ (by rw [lockstepChunks_length]; exact current)] at lower'
  have log := reached_futureEmpty prims D limit t Z base (honest limit lower') disc reached le_rfl
  refine ⟨limit, start_futureEmpty prims D limit q.program ?_ q.world log out run, ?_⟩
  · intro i hi
    simpa using ((disc i hi).residual (Reached.residual prims D Z reached i hi) (by omega))
  · intro i hi inbox
    have tail := (Reached.residual prims D Z reached i hi).trans (pass_residual prims D A q out run i hi inbox)
    rcases common i hi with aborted | first
    · rw [aborted] at tail
      rw [tail.pure_inv]
      exact .pure _ _
    · apply (clock i (same i) (quiet i)).2
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans tail

/-- The entry pass can be classified by its actual common choice. -/
theorem entry_pass_prgClock (positive : 0 < settings.batchSize) (dealt : DealtInputs D x)
    (z : Aux) (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : start ∈ support (treeSaltSetup prims D A x z))
    (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length) q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A q)) (clean : ¬ TreeSimHashBudgetCollision out.2.2) :
    PrgPassClock D out := by
  set N := batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)).length
  set S := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length
  have initialDisc := initial_entry_prgDisc D K A circuits settings top x b positive dealt start
  have log := reached_futureEmpty prims D (S + 1) N Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start) (setup_futureEmpty prims D (S + 1) A x z start setupRun)
    (fun i _ => initialDisc i) reached le_rfl
  have outLog : TreeSimFutureEmpty (S + 1) out.2.1.2 := by
    apply start_futureEmpty prims D (S + 1) q.program _ q.world log out run
    intro i hi
    simpa only [N, Nat.add_sub_cancel_left] using (initialDisc i).residual (Reached.residual prims D Z reached i hi) (by omega)
  obtain ⟨point, matching, allAbort | ⟨chosen, selected, selection, common⟩⟩ :=
    actual_pass_common prims D K circuits settings top b A x z Z positive dealt start setupRun q reached out run clean
  · refine ⟨S + 1, outLog, ?_⟩
    intro i hi inbox
    rw [allAbort i hi]
    exact .pure _ _
  · have current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b) := by
      have chunks := signing_chunks_nonempty settings b positive chosen.value.2.2
      obtain ⟨head, rest, eq⟩ := chunks
      have len := lockstepChunks_length settings chosen.value.2.2 (.bottom b)
      simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs, List.length_append, eq,
        List.length_cons] at len ⊢
      omega
    let caller := signingCaller point.outputs point.records (fun _ => pure (some chosen.value)) chosen.value
    obtain ⟨lower, clock⟩ := sign_caller_prgClock circuits settings K D top x start.1.2 b
      (firstChunks settings (.bottom b)).length 1 le_rfl current caller
    refine ⟨prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (lockstepChunks settings caller.encoding (.bottom b)) (firstChunks settings (.bottom b)).length 1, ?_, ?_⟩
    · rw [prgCallerClock_one circuits settings _ _ _ (by rw [lockstepChunks_length]; exact current), signing_start]
      exact outLog
    · intro i hi inbox
      rcases common i hi with aborted | residual
      · rw [aborted]; exact .pure _ _
      · have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
          obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
          rw [hx i, hx (refHolder D K.publicTerm)]; rfl
        exact (clock i same (isQueryBoundP_pure _ _ _)).2 _ (residual inbox)

/-- Every clean reached local pass has a common clock; no decoded caller is
used to choose that clock. -/
theorem actual_pass_prgClock (positive : 0 < settings.batchSize) (dealt : DealtInputs D x)
    (current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b))
    (z : Aux) (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : start ∈ support (treeSaltSetup prims D A x z))
    (m : ℕ) (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start) m q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A q)) (clean : ¬ TreeSimHashBudgetCollision out.2.2) :
    PrgPassClock D out := by
  set N := batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)).length
  set S := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length
  set initial := TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start
  have same (i) : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]; rfl
  by_cases early : m + 1 ≤ N
  · obtain ⟨upper, disc, floor⟩ := initial_program_prgClock circuits settings K D top (.bottom b) x A start
      (firstChunks_bottom_pos settings positive b) dealt (m + 1) early
    set limit := prgCallerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)) 0 (m + 1)
    have log := reached_futureEmpty prims D limit m Z initial (setup_futureEmpty prims D limit A x z start setupRun)
      (fun i _ => disc i) reached le_rfl
    refine ⟨limit, start_futureEmpty prims D limit q.program ?_ q.world log out run, ?_⟩
    · intro i hi
      simpa using (disc i).residual (Reached.residual prims D Z reached i hi) (by omega)
    · intro i hi inbox
      exact floor i _ ((Reached.residual prims D Z reached i hi).trans (pass_residual prims D A q out run i hi inbox))
  · by_cases atEntry : m = N
    · subst m
      exact entry_pass_prgClock prims D K A circuits settings top x Z b positive dealt z start setupRun q reached out run clean
    · have after : N + 1 ≤ m := by omega
      have split : Reached prims D Z initial (N + 1 + (m - (N + 1))) q := by
        simpa only [Nat.add_sub_of_le after] using reached
      obtain ⟨base, first, suffix⟩ := reached_split prims D A Z (N + 1) (m - (N + 1)) split
      obtain ⟨entry, fuel, started, reply, before, fuelLeft, firstRun, nonterminal, replyRun, baseEq, pref⟩ :=
        TreeCheckWalkFirstOpening.reached_last D prims A Z initial N base first
      have cleanFirst : ¬ TreeSimHashBudgetCollision started.2.2 := by
        intro bad
        apply clean
        exact treeSimHashBudgetCollision_mono
          ((pref.trans (reached_prefix prims D A Z suffix)).trans
            (treeSimLoggedWorld_prefix prims D _ _ _ run)) bad
      obtain ⟨point, matching, allAbort | ⟨chosen, selected, selection, common⟩⟩ :=
        actual_pass_common prims D K circuits settings top b A x z Z positive dealt start setupRun entry before
          started firstRun cleanFirst
      · exact False.elim (nonterminal (fun i hi => by rw [allAbort i hi]; trivial))
      · let caller := signingCaller point.outputs point.records (fun _ => pure (some chosen.value)) chosen.value
        have baseLog : TreeSimFutureEmpty (S + 1) base.world.1.2 :=
          reached_futureEmpty_cut prims D A Z (S + 1) (N + 1) initial (setup_futureEmpty prims D (S + 1) A x z start setupRun)
            (fun i _ => initial_entry_prgDisc D K A circuits settings top x b positive dealt start i) first le_rfl
        apply signing_suffix_prgClock prims D K A circuits settings top x start.1.2 Z b caller same
          (fun i => isQueryBoundP_pure _ _ _) current base q (m - (N + 1)) ?_ ?_ suffix out run
        · intro i hi
          rcases common i hi with aborted | residual
          · left
            rw [baseEq]
            simp only [TreeCheckWalkDef.resume, aborted]
            rfl
          · right
            let inbox := fun h => if h ∈ D.1 then reply.1.2 h i else (started.1 h).delivered i
            have h := residual inbox
            convert h using 1
            rw [baseEq]
            simp only [TreeCheckWalkDef.resume]
            cases started.1 i with
            | done output => rfl
            | wait output k => simp [hi, resumed, inbox]
            | call impossible k => exact impossible.elim
        · intro limit lower
          rw [signing_start] at lower
          exact fun address later => baseLog address (lower.trans later)

/-- Every live signing checkpoint of the fixed walk has a fresh hidden-cache future. -/
theorem walkCheckpoint_futureEmpty_signing :
    AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
      (∃ b, tree = .bottom b) → (firstChunks settings tree).length ≤ j.val →
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
      TreeSimFutureEmpty ((W.cut prims K circuits settings D Z).hybrid (.inl (c, o))).label o.2.1.2 := by
  intro positive top tree D A x z Z q dealt bounded small j setup setupRun bottom signing
  obtain ⟨b, rfl⟩ := bottom
  intro c o run live
  dsimp only [TreeCheckTailWalk.cut] at run live ⊢
  let W := family prims K circuits settings top (.bottom b) D A x Z q bounded j setup
  obtain ⟨r, contRun, bad, counted⟩ := live
  obtain ⟨parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    keys, honest, accepted, _⟩ := bad.2.2
  have preRun : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible apply TreeCheckTailWalk.mem_support_cut_pre (W := W) (Z := Z) (c := c)
    with_reducible simpa only [W, TreeCheckTailWalk.cut] using run
  obtain ⟨out, outRun, pref, transfer, probe⟩ := source_prg_probe_prefix prims D K A circuits settings
    top (.bottom b) x dealt z j Z (TreeCheckQueryBudget.ofBound bounded).step setup c o preRun r contRun bad i honest (value, records) accepted
  have hit : .inl c ∈ support W.pre := by
    with_reducible exact (TreeCheckWalkDef.index_support prims D Z K circuits settings W c o
      (by simpa only [W, TreeCheckTailWalk.cut] using run))
  with_reducible obtain ⟨m, pending, reached, actualRun⟩ := (walk_hit_pass prims D K A circuits settings top (.bottom b) x setup.1.2 j Z
    (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x setup)
    (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x setup).fuel 0
    (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x setup) .start rfl c hit out outRun)
  have clean : ¬ TreeSimHashBudgetCollision out.2.2 := by
    intro collision
    apply bad.1
    exact treeSimHashBudgetCollision_mono
      (pref.trans (treeCheckBatchCont_log_prefix prims K circuits D A Z (W.boundary c).batch o r contRun)) collision
  obtain ⟨limit, outFresh, floor⟩ := actual_pass_prgClock prims D K A circuits settings top x Z b positive dealt
    (by omega) z setup setupRun m pending reached out actualRun clean
  apply transfer
  intro address later
  exact outFresh address ((probe limit (floor i honest)).trans later)

/-- The original Live premise suffices at every checkpoint, including the first signing batch. -/
theorem walkCheckpoint_futureEmpty_live :
    AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
      TreeSimFutureEmpty ((W.cut prims K circuits settings D Z).hybrid (.inl (c, o))).label o.2.1.2 := by
  intro positive top tree D A x z Z q dealt bounded small j setup setupRun
  by_cases first : j.val < (firstChunks settings tree).length
  · intro c o run _
    have result := TreeCheckPrgFirstFresh.walkCheckpoint_futureEmpty prims K circuits settings
    unfold AtWalk at result
    with_reducible exact result positive top tree D A x z Z q dealt bounded small j setup setupRun first c o run
  · have result := walkCheckpoint_futureEmpty_signing prims K circuits settings
    unfold AtWalk at result
    with_reducible apply (result positive top tree D A x z Z q dealt bounded small j setup setupRun)
    · cases tree with
      | bottom b => exact ⟨b, rfl⟩
      | top =>
        apply False.elim
        apply first
        simpa only [firstChunks, treeLockstepFirstJobs, treeBatches] using j.isLt
    · omega

end ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.residual_first_entry_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.residual_first_entry_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.initial_complete_prgDisc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.initial_complete_prgDisc

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.entry_first_prg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.entry_first_prg

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.initial_entry_prgDisc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.initial_entry_prgDisc

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.reached_futureEmpty_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.reached_futureEmpty_cut

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.boundary_prg_probe_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.boundary_prg_probe_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.source_prg_probe_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.source_prg_probe_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.signing_suffix_prgClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.signing_suffix_prgClock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.entry_pass_prgClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.entry_pass_prgClock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.actual_pass_prgClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.actual_pass_prgClock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.walkCheckpoint_futureEmpty_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.walkCheckpoint_futureEmpty_signing

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.walkCheckpoint_futureEmpty_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgSigningFresh.walkCheckpoint_futureEmpty_live
