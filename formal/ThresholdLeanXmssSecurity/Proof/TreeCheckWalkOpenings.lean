import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkRecipe
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSource

/-!
# Opening provenance for the fixed source walk

A decoded caller has exactly `j` earlier records. Its actual continuation
retains those records, appends the selected batch, and then appends later
records. These statements concern the fixed `callerCont`, including its
rejecting branches; no alternative caller or batch index is selected.

The actual tuple check and opening are cut from the same continuation with
their caches and logs. Acceptance supplies enough scheduler fuel for the cut.
A snapshot passes through the fixed typed preparation and walk to an original
audited execution that still has no final outputs. Replay uniqueness places
that snapshot before the successful coherent reference. `IndexedReference`
retains the reference replay in its type when its witness is selected.

The pinned and current leanVM libraries have no audited synchronous caller or
indexed-opening provenance lemma.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkRecipe

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A successful finish after the first phase only appends audit records.
This also covers the additional signing phase of a bottom tree. -/
theorem firstRest_records_prefix (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (ctx : Context C) (top : TopTree) (tree : Tree)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C))
    (run : some actual ∈ support
      (treeLockstepFirstRest K circuits settings ctx top tree a).run) :
    a.1.2 <+: actual.2 := by
  rcases a with ⟨⟨values, records⟩, counters⟩
  cases values with
  | none => simp [treeLockstepFirstRest] at run
  | some outputs =>
    dsimp only [treeLockstepFirstRest] at run
    cases tree with
    | top =>
      change some actual ∈ support (treeLockstepTopFinish (E := E) ctx.keys.parameter outputs records).run at run
      have h : actual.2 = records := by
        with_reducible exact treeLockstep_topFinish_records (E := E) ctx.keys.parameter outputs records actual run
      rw [h]
    | bottom b =>
      dsimp only [treeLockstepFirstRest] at run
      obtain ⟨chosen, _, run⟩ := by
        with_reducible exact treeSimCheck_some_bind _ _ _ run
      cases chosen with
      | none => simp at run
      | some chosen =>
        obtain ⟨result, _, run⟩ := by
          with_reducible exact treeSimCheck_some_bind _ _ _ run
        have h := treeLockstep_bottomFinish_records (E := E) ctx.keys.parameter top b outputs
          chosen.1 chosen.2.1 result.1.1 (records ++ result.1.2) actual run
        rw [h]
        exact List.prefix_append _ _

/-- The selected batch's complete record list survives the fixed caller's
remaining batches and final verification. -/
theorem callerCont_records_prefix (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C))
    (run : some actual ∈ support
      (callerCont K circuits settings top tree x setup j caller i a).run) :
    caller.records i ++ a.1.2 <+: actual.2 := by
  dsimp only [callerCont] at run
  obtain ⟨rest, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  have hprefix : caller.records i ++ a.1.2 <+:
      caller.records i ++ a.1.2 ++ rest.1.2 := List.prefix_append _ _
  split_ifs at run
  · exact hprefix.trans (firstRest_records_prefix K circuits settings _ top tree _ actual run)
  · cases tree with
    | top =>
      exact hprefix.trans (firstRest_records_prefix K circuits settings _ top .top _ actual run)
    | bottom b =>
      have h := treeLockstep_bottomFinish_records (E := E) (x i).parameter top b (caller.firstOutputs i)
        (caller.root i) (caller.randomness i) _ _ actual run
      rw [h]
      exact hprefix

/-- The decoder's length guard identifies the selected singleton with the
original final result's record at index `j`. -/
theorem callerCont_record_index (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (caller : Caller C) (i : C.Party)
    (hlen : (caller.records i).length = j)
    (value : Option (List (List Bit))) (record : TreeSimCheckBatchRecord C) (counters : ℕ × ℕ)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C))
    (run : some actual ∈ support
      (callerCont K circuits settings top tree x setup j caller i ((value, [record]), counters)).run) :
    actual.2[j]? = some record := by
  obtain ⟨later, h⟩ := callerCont_records_prefix K circuits settings top tree x setup j caller i
    ((value, [record]), counters) actual run
  rw [← h, ← hlen, List.append_assoc]
  simp

/-- A successful batch finish supplies the exact record written after its
actual local check and opening to the fixed caller. -/
theorem batchFinish_caller_record (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (caller : Caller C) (i : C.Party)
    (hlen : (caller.records i).length = j) (ctx : Context C) (jobs : List Job)
    (initial : ℕ × ℕ)
    (p : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C))
    (run : some actual ∈ support
      (treeSimCheckBatchFinish K circuits ctx jobs initial p >>=
        callerCont K circuits settings top tree x setup j caller i).run) :
    ∃ (checked : Unit × RunState C) (opened : ℕ → Bit),
      some checked ∈ support ((check (G := RealSpec) K ctx (realCheckGadgets K ctx) p.2.1.2).run p.2.2).run ∧
      some opened ∈ support (openRep (G := RealSpec) K ctx p.2.1.1
        (outputsOf (jobs.map (circuits ctx.keys.parameter ·.kind))).length).run ∧
      actual.2[j]? = some ⟨ctx, jobs, initial, p.1, p.2.1.2, p.2.2,
        assemble (jobs.map (circuits ctx.keys.parameter ·.kind)) opened, checked.2⟩ := by
  rw [treeLockstep_batchFinish_check] at run
  obtain ⟨checked, checkedRun, run⟩ := by
    with_reducible exact treeSimCheck_some_bind _ _ _ run
  unfold treeLockstepBatchCheckCont at run
  obtain ⟨opened, openedRun, run⟩ := by
    with_reducible exact treeSimCheck_some_bind _ _ _ run
  exact ⟨checked, opened, checkedRun, openedRun,
    callerCont_record_index K circuits settings top tree x setup j caller i hlen _ _ _ actual run⟩

private theorem allowed_of_support {ι α : Type} {spec : OracleSpec ι}
    (p : OracleComp spec α) (a : α) (h : a ∈ support p) :
    TreeSimCheckAllowed (fun _ _ => True) p a := by
  obtain ⟨log, replay⟩ := treeSimCheckReplay_of_support p a h
  exact ⟨log, replay, fun _ _ _ => trivial⟩

/-- Successful resumption retains the same honest party's local continuation;
missing checkpoint rows cannot acquire a later output. -/
theorem resumed_local_support {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (pref : C.Party → Option α) (k : C.Party → α → PartyM C E RealSpec β)
    (next : C.Party → Step C E RealSpec β)
    (start : next ∈ support (free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i)))))
    (out : A.State × (C.Party → Option β))
    (run : out ∈ support (executeRounds worldRoles D A noFunctionality fuel state next))
    (i : C.Party) (honest : i ∉ D.1) (actual : β) (accepted : out.2 i = some actual) :
    ∃ a, pref i = some a ∧ some actual ∈ support (k i a).run := by
  have localRun := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ start) i
  have finish := treeSimCheck_rounds_replay D A noFunctionality (fun _ _ => True) fuel state next
    out (allowed_of_support _ _ run) i honest actual accepted
  cases present : pref i with
  | none =>
    have stopped : next i = .done none := by simpa only [present, continueStep, mem_support_pure_iff] using localRun
    simp only [stopped, TreeSimCheckStepAllowed] at finish
    cases finish
  | some a =>
    have advanced : next i ∈ support (advance (k i a).run) := by
      simpa only [present, continueStep] using localRun
    have replay := treeSimCheck_advance_replay (fun _ _ => True) (k i a).run (next i) actual
      (allowed_of_support _ _ advanced) finish
    exact ⟨a, rfl, replay.choose_spec.1.mem_support⟩

/-- Extract the selected party's local check/open/caller program from the
actual logged batch continuation, before its distinguisher runs. -/
theorem batchCont_local_support (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A)
    (o : TreeCheckTailCheckpoint A) (r : TreeCheckTailResult A)
    (run : r ∈ support (treeCheckBatchCont prims K circuits D A Z b o))
    (i : C.Party) (honest : i ∉ D.1)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C)) (accepted : r.1.2.2 i = some actual) :
    ∃ p, o.1.2 i = some p ∧ some actual ∈ support
      (treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i).run := by
  unfold treeCheckBatchCont treeCheckObserve at run
  simp only [mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨next, start, out, rest, z, _, rfl⟩ := run
  exact resumed_local_support D A b.fuel o.1.1 o.1.2 _ next.1
    (treeCheck_logged_support prims D _ _ start) out.1
    (treeCheck_logged_support prims D _ _ rest) i honest actual accepted

/-- Every indexed bad-record witness is the selected caller's actual batch
record. Its inputs, tuples and checkpoint come from the retained row, and its
outputs come from that row's subsequent check and opening. -/
theorem sourceWalk_indexed_record (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup.1.2 j))
    (o : TreeCheckTailCheckpoint A) (r : TreeCheckTailResult A)
    (run : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (record : TreeCheckIndexedRecord prims circuits D A x j r) :
    let b := (sourceWalk prims K D A circuits settings top tree x j Z step setup).boundary c
    ∃ (data : MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
      (checked : Unit × RunState C) (opened : ℕ → Bit),
      o.1.2 record.party = some data ∧
      some checked ∈ support ((check (G := RealSpec) K (b.batch.ctx record.party)
        (realCheckGadgets K (b.batch.ctx record.party)) data.2.1.2).run data.2.2).run ∧
      some opened ∈ support (openRep (G := RealSpec) K (b.batch.ctx record.party) data.2.1.1
        (outputsOf (b.batch.jobs.map (circuits (b.batch.ctx record.party).keys.parameter ·.kind))).length).run ∧
      record.record = ⟨b.batch.ctx record.party, b.batch.jobs, b.batch.initial, data.1,
        data.2.1.2, data.2.2,
        assemble (b.batch.jobs.map (circuits (b.batch.ctx record.party).keys.parameter ·.kind)) opened,
        checked.2⟩ := by
  let b := (sourceWalk prims K D A circuits settings top tree x j Z step setup).boundary c
  obtain ⟨data, present, localRun⟩ := batchCont_local_support prims K circuits D A Z b.batch o r
    run record.party record.honest (record.output, record.records) record.result
  have hlen := (decode_sound prims K D A circuits settings top tree x setup.1.2 j c).1
    record.party record.honest
  have selected := batchFinish_caller_record K circuits settings top tree x setup.1.2 j c.1.2
    record.party hlen.1 (b.batch.ctx record.party) b.batch.jobs b.batch.initial data
    (record.output, record.records) localRun
  obtain ⟨checked, opened, checkRun, openRun, indexed⟩ := selected
  exact ⟨data, checked, opened, present, checkRun, openRun,
    Option.some.inj (record.indexed.symm.trans indexed)⟩

/-- The indexed witness and the fixed boundary have the same jobs and public
parameter. This uses only actual continuation provenance and the dealt keys. -/
theorem sourceWalk_indexed_metadata (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup.1.2 j))
    (o : TreeCheckTailCheckpoint A) (r : TreeCheckTailResult A)
    (run : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (record : TreeCheckIndexedRecord prims circuits D A x j r) :
    let b := (sourceWalk prims K D A circuits settings top tree x j Z step setup).boundary c
    (∀ h, h ∉ D.1 → (b.batch.ctx h).keys = x h) ∧
      b.batch.jobs = record.record.jobs ∧ b.batch.parameter = record.parameter := by
  obtain ⟨data, checked, opened, _, _, _, recorded⟩ :=
    sourceWalk_indexed_record prims K D A circuits settings top tree x j Z step setup c o r run record
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · rw [recorded]
  · change (x (refHolder D K.publicTerm)).parameter = record.parameter
    exact congrArg (fun xs : C.Party → Keys C => (xs (refHolder D K.publicTerm)).parameter) record.dealt

/-- A successful phase output retains one actual scheduled opening and a
supported execution of that same opening's own continuation. The head's final
log is a prefix of the original phase's final log. -/
theorem opening_phase_success {α : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (phase : TreeCheckOpeningPhaseRun prims K D A fuel state count v k s r)
    (i : C.Party) (honest : i ∉ D.1) (actual : α) (accepted : r.1.2 i = some actual) :
    ∃ opening : TreeCheckOpeningRun prims K D count v,
      opening.party = i ∧ s.2 <+: opening.before.2 ∧ opening.after.2 <+: r.2.2 ∧
      some actual ∈ support (k i opening.output).run := by
  have rawRest := treeCheck_logged_support prims D _ _ phase.restRun
  have finish := treeSimCheck_rounds_replay D A noFunctionality (fun _ _ => True) fuel
    phase.reply.1 phase.steps r.1 (allowed_of_support _ _ rawRest) i honest actual accepted
  have kept : phase.steps i ≠ .done none := by
    intro stopped
    simp only [stopped, TreeSimCheckStepAllowed] at finish
    cases finish
  obtain ⟨opening, _, _, _, party, before, after, tail, continued, _⟩ := phase.opening i kept
  have advanced := treeSimCheck_support_free _ (treeCheck_logged_support prims D _ _ continued)
  have localRun := treeSimCheck_advance_replay (fun _ _ => True) (k i opening.output).run
    (phase.steps i) actual (allowed_of_support _ _ advanced) finish
  exact ⟨opening, party, before, after, localRun.choose_spec.1.mem_support⟩

/-- The audited record assembled by the selected batch's post-check opening. -/
def openingRecord (circuits : Circuits) (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (checked : Unit × RunState C) (opened : ℕ → Bit) : TreeSimCheckBatchRecord C :=
  ⟨ctx, jobs, initial, data.1, data.2.1.2, data.2.2,
    assemble (jobs.map (circuits ctx.keys.parameter ·.kind)) opened, checked.2⟩

/-- The fixed source caller immediately after the selected opening. -/
def openingCaller (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (caller : Caller C)
    (jobs : List Job) (initial : ℕ × ℕ)
    (data : C.Party → MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (checked : C.Party → Unit × RunState C) (i : C.Party) (opened : ℕ → Bit) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) :=
  let record := openingRecord circuits ⟨i, x i, setupKeys setup i⟩ jobs initial (data i) (checked i) opened
  callerCont K circuits settings top tree x setup j caller i
    ((some record.outputs, [record]), ((checked i).2.label, initial.2 + 1))

/-- In an actual opening phase, the selected party's scheduled head writes the
final record at `j`; its cached/logged execution is retained intact. -/
theorem opening_phase_indexed (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (caller : Caller C)
    (jobs : List Job) (initial : ℕ × ℕ)
    (data : C.Party → MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (checked : C.Party → Unit × RunState C) (fuel : ℕ) (state : A.State)
    (count : ℕ) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (phase : TreeCheckOpeningPhaseRun prims K D A fuel state count (fun i => (data i).2.1.1)
      (openingCaller K circuits settings top tree x setup j caller jobs initial data checked) s r)
    (i : C.Party) (honest : i ∉ D.1) (hlen : (caller.records i).length = j)
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C)) (accepted : r.1.2 i = some actual) :
    ∃ opening : TreeCheckOpeningRun prims K D count (fun i => (data i).2.1.1),
      opening.party = i ∧ s.2 <+: opening.before.2 ∧ opening.after.2 <+: r.2.2 ∧
      actual.2[j]? = some (openingRecord circuits ⟨i, x i, setupKeys setup i⟩ jobs initial
        (data i) (checked i) opening.output) := by
  obtain ⟨opening, party, before, after, localRun⟩ :=
    opening_phase_success prims K D A fuel state count _ _ s r phase i honest actual accepted
  exact ⟨opening, party, before, after,
    callerCont_record_index K circuits settings top tree x setup j caller i hlen _ _ _ actual localRun⟩

/-- A timed prefix cannot expose an attached continuation before its last
exchange. This uses the actual scheduler steps, including early aborts. -/
theorem timed_rounds_early {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel n : ℕ) (early : fuel < n)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimedStep n (steps i))
    (out : A.State × (C.Party → Option β))
    (run : out ∈ support (executeRounds worldRoles D A noFunctionality fuel state
      (fun i => suspendStep (k i) (steps i)))) : out.2 = fun _ => none := by
  induction fuel generalizing n state steps out with
  | zero =>
    have he : out = (state, fun _ => none) := by
      simpa only [executeRounds, suspendStep_output, mem_support_pure_iff] using run
    exact congrArg Prod.snd he
  | succ fuel ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [executeRounds] at run
    simp only [suspendStep_isDone] at run
    split_ifs at run
    · have he : out = (state, fun _ => none) := by
        simpa only [suspendStep_output, mem_support_pure_iff] using run
      exact congrArg Prod.snd he
    · rw [stepRound_suspend D A state steps k (fun i => (timed i).pending)
        (fun i box resume he hi inbox => ((he ▸ timed i) inbox).suspend (k i))] at run
      simp only [bind_assoc, pure_bind, mem_support_bind_iff] at run
      obtain ⟨next, stepRun, rest⟩ := run
      exact ih (n + 1) (by omega) next.1 next.2.1
        (treeSimCheckTimed_round D A (n + 1) state steps timed next stepRun) out rest

/-- Every successful joint execution has enough rounds for its actual timed
prefix. No query-bound or bad-event assumption is needed. -/
theorem timed_phase_fuel {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel n : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed n (p i).run)
    (out : A.State × (C.Party → Option β))
    (run : out ∈ support (executePhase worldRoles D A noFunctionality fuel state (fun i => p i >>= k i)))
    (accepted : ∃ i value, out.2 i = some value) : n ≤ fuel := by
  by_contra h
  have early : fuel < n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold executePhase at run
  rw [treeSimCheckTimed_start D m p k timed] at run
  simp only [bind_map_left, mem_support_bind_iff] at run
  obtain ⟨steps, start, run⟩ := run
  have failed := timed_rounds_early D A fuel (m + 1) early state steps k
    (treeSimCheckTimed_start_mem D (m + 1) p timed steps start) out run
  obtain ⟨i, value, accepted⟩ := accepted
  rw [failed] at accepted
  cases accepted

/-- A program with a mandatory next exchange cannot finish with zero rounds. -/
theorem exchange_phase_positive {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (exchange : ∀ i, TreeSimCheckExchange (p i))
    (out : A.State × (C.Party → Option α))
    (run : out ∈ support (executePhase worldRoles D A noFunctionality fuel state p))
    (accepted : ∃ i value, out.2 i = some value) : 0 < fuel := by
  cases fuel with
  | succ fuel => omega
  | zero =>
    simp only [executePhase, executeRounds, mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨steps, start, rfl⟩ := run
    obtain ⟨i, value, accepted⟩ := accepted
    have each := mem_support_sequenceFin_oc _ _ start i
    by_cases hi : i ∈ D.1
    · have stopped : steps i = .done none := by
        simpa only [if_pos hi, mem_support_pure_iff] using each
      simp only [stopped, Step.output] at accepted
      cases accepted
    · simp only [if_neg hi] at each
      have pending := (exchange i (steps i) (treeSimCheck_support_free _ each)).pending
      simp only [pending] at accepted
      cases accepted

/-- Cut the actual tuple check at its subsequent opening phase. The fuel
argument is derived from acceptance, so the phase cannot be placed past the
original run. Empty checks are handled without consuming an extra round. -/
theorem check_open_phase {α : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (ctx : C.Party → Context C)
    (self : ∀ i, (ctx i).self = i) (tuples : C.Party → List (Tuple C))
    (st : C.Party → RunState C) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count)
    (width : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (Unit × RunState C) → (ℕ → Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun checked =>
          openRep K (ctx i) (v i) width >>= k i checked))).run s))
    (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (remaining : ℕ) (nextState : A.State) (checked : C.Party → Unit × RunState C)
      (before : TreeSimState C), s.2 <+: before.2 ∧
      Nonempty (TreeCheckOpeningPhaseRun prims K D A remaining nextState width v
        (fun i => k i (checked i)) before r) := by
  let next := fun i checked => openRep K (ctx i) (v i) width >>= k i checked
  have exchange (i) (checked) : TreeSimCheckExchange (next i checked) :=
    (treeSimCheck_openRep_exchange K (ctx i) (v i) width).bind _
  by_cases zero : count = 0
  · have empty i : (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) =
        pure ((), st i) := by
      simp only [check, counts i, zero]
      rfl
    simp only [empty, pure_bind] at run
    have positive := exchange_phase_positive D A fuel state (fun i => next i ((), st i))
      (fun i => exchange i _) r.1 (treeCheck_logged_support prims D _ _ run) accepted
    obtain ⟨remaining, hremaining⟩ : ∃ remaining, fuel = remaining + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨remaining, state, fun i => ((), st i), s, List.prefix_refl _, ⟨?_⟩⟩
    exact treeCheckOpeningPhaseRun_of_run prims K D A remaining state ctx self width v
      (fun i => k i ((), st i)) s r (by simpa only [hremaining] using run)
  · let n := 2 * halvings count + 4
    let p := fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
    have timed i : TreeSimCheckTimed (n + 1) (p i).run := by
      have h := treeLockstep_check_timed K (ctx i) (tuples i) (st i) (by rw [counts i]; exact zero)
      have hs : sliceBits ≤ halvings count := by unfold halvings; omega
      convert h using 1
      rw [counts i]
      dsimp only [n]
      omega
    have enough := timed_phase_fuel D A fuel (n + 1) state p next timed r.1
      (treeCheck_logged_support prims D _ _ run) accepted
    obtain ⟨restFuel, hrestFuel⟩ : ∃ restFuel, fuel = n + 1 + restFuel :=
      ⟨fuel - (n + 1), by omega⟩
    obtain ⟨pref, checked, prefRun, _, rest⟩ := treeLockstep_timed_boundary prims D A n restFuel
      state p next ((), ⟨fun _ => [], 0, 0⟩) timed exchange s r
      (by simpa only [hrestFuel] using run) accepted
    have positive := exchange_phase_positive D A restFuel pref.1.1 (fun i => next i (checked i))
      (fun i => exchange i _) r.1 (treeCheck_logged_support prims D _ _ rest) accepted
    obtain ⟨remaining, hremaining⟩ : ∃ remaining, restFuel = remaining + 1 :=
      ⟨restFuel - 1, by omega⟩
    refine ⟨remaining, pref.1.1, checked, pref.2,
      treeSimLoggedWorld_prefix prims D _ s pref prefRun, ⟨?_⟩⟩
    exact treeCheckOpeningPhaseRun_of_run prims K D A remaining pref.1.1 ctx self width v
      (fun i => k i (checked i)) pref.2 r (by simpa only [hremaining] using rest)

/-- The exact continuation stored in a batch boundary after its check and
opening; only the values already returned by those computations are inserted. -/
def batchOpeningCont {A : Adversary C E (Keys C) PEmpty PEmpty}
    (circuits : Circuits) (b : TreeCheckBatchBoundary A)
    (data : C.Party → MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (i : C.Party) (checked : Unit × RunState C) (opened : ℕ → Bit) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) :=
  let record := openingRecord circuits (b.ctx i) b.jobs b.initial (data i) checked opened
  b.k i ((some record.outputs, [record]), (checked.2.label, b.initial.2 + 1))

private theorem world_phase_congr {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p q : C.Party → PartyM C E RealSpec α) (same : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D A noFunctionality fuel state p =
      executePhase worldRoles D A noFunctionality fuel state q := by
  unfold executePhase startSteps
  congr 2
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · simp only [if_neg hi, same i hi]

private theorem resume_start {α β : Type} (D : C.Coalition)
    (k : C.Party → α → PartyM C E RealSpec β) (pref : C.Party → Option α) (data : C.Party → α)
    (corrupt : ∀ i, i ∈ D.1 → pref i = none)
    (present : ∀ i, i ∉ D.1 → pref i = some (data i)) :
    free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i))) =
      startSteps worldRoles D (fun i => k i (data i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, corrupt i hi, continueStep, free_pure]
  · simp only [if_neg hi, present i hi, continueStep, worldRoles]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
/-- The actual successful batch continuation contains an actual opening
phase. Honest saved rows are unchanged; normalization touches only absent
corrupt check inputs, which the scheduler never executes. -/
theorem batchCont_opening_phase (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A)
    (self : ∀ i, (b.batch.ctx i).self = i)
    (parameters : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (o : TreeCheckTailCheckpoint A) (preRun : o ∈ support (b.pre prims K circuits settings D))
    (r : TreeCheckTailResult A) (run : r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o))
    (accepted : ∃ i value, r.1.2.2 i = some value) :
    let data := fun i => treeCheckPrefixData (o.1.2 i)
    ∃ (remaining : ℕ) (state : A.State) (checked : C.Party → Unit × RunState C)
      (before : TreeSimState C)
      (out : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C),
      o.2.2 <+: before.2 ∧ out.2.2 <+: r.2 ∧ out.1 = r.1.2 ∧
      Nonempty (TreeCheckOpeningPhaseRun prims K D A remaining state
        (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length
        (fun i => (data i).2.1.1) (fun i => batchOpeningCont circuits b.batch data i (checked i)) before out) := by
  let data := fun i => treeCheckPrefixData (o.1.2 i)
  have live := treeCheckBatch_live prims K circuits D A Z b.batch o r run accepted
  have present i (hi : i ∉ D.1) : o.1.2 i = some (data i) := by
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (live i hi)
    simp only [data, treeCheckPrefixData, hp, Option.getD_some]
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A
    (b.batch.rounds circuits settings) b.batch.state _ b.batch.world o
    (by simpa only [TreeCheckTailBoundary.pre, simulateQ_executePhase] using preRun)
  have counts i (hi : i ∉ D.1) : ((data i).2.1.2.map (·.count)).sum = (b.batch.counts circuits).sum := by
    obtain ⟨p, hp, _, _, _, hc, _⟩ := b.counts prims K circuits settings D Z self parameters o preRun r run accepted i hi
    have same : p = data i := Option.some.inj (hp.symm.trans (present i hi))
    rw [← same, hc]
  let tuples := fun i => if i ∈ D.1 then (data (refHolder D K.publicTerm)).2.1.2 else (data i).2.1.2
  have countsAll i : ((tuples i).map (·.count)).sum = (b.batch.counts circuits).sum := by
    dsimp only [tuples]
    split_ifs with hi
    · exact counts _ (refHolder_spec D K.publicTerm).2
    · exact counts i hi
  have normalized := world_phase_congr D A b.batch.fuel o.1.1
    (fun i => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial (data i) >>= b.batch.k i)
    (fun i => (check K (b.batch.ctx i) (realCheckGadgets K (b.batch.ctx i)) (tuples i)).run (data i).2.2 >>=
      fun checked => openRep K (b.batch.ctx i) (data i).2.1.1
        (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length >>=
          batchOpeningCont circuits b.batch data i checked) (by
      intro i hi
      rw [treeLockstep_batchFinish_check]
      simp only [tuples, if_neg hi]
      congr 1
      funext checked
      unfold treeLockstepBatchCheckCont batchOpeningCont openingRecord
      rw [parameters i])
  unfold treeCheckBatchCont at run
  rw [resume_start D _ o.1.2 data corrupt present] at run
  have combined : (do
      let next ← (simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (fun i => treeSimCheckBatchFinish K circuits (b.batch.ctx i)
          b.batch.jobs b.batch.initial (data i) >>= b.batch.k i))).run o.2
      let out ← (simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality b.batch.fuel o.1.1 next.1)).run next.2
      treeCheckObserve prims D A Z out) = (do
      let out ← (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality b.batch.fuel o.1.1
          (fun i => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial
            (data i) >>= b.batch.k i))).run o.2
      treeCheckObserve prims D A Z out) := by
    simp only [executePhase, simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [combined, normalized] at run
  simp only [mem_support_bind_iff] at run
  obtain ⟨out, phaseRun, observation⟩ := run
  unfold treeCheckObserve at observation
  simp only [mem_support_bind_iff, mem_support_pure_iff] at observation
  obtain ⟨observed, observedRun, rfl⟩ := observation
  obtain ⟨remaining, state, checked, before, beforeLog, phase⟩ := by
    with_reducible exact (check_open_phase prims K D A
      b.batch.fuel o.1.1 b.batch.ctx self tuples (fun i => (data i).2.2) _ countsAll
      (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length
      (fun i => (data i).2.1.1) (batchOpeningCont circuits b.batch data) o.2 out phaseRun accepted)
  exact ⟨remaining, state, checked, before, out, beforeLog,
    treeSimLoggedWorld_prefix prims D _ out.2 observed observedRun, rfl, phase⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
/-- The selected indexed record comes from one actual scheduled opening in
the same cached/logged continuation. The opening uses the retained saved rows,
and its final log is a prefix of the original bad run's final log. -/
theorem sourceWalk_indexed_trace (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (preRun : (.inl (c, o) : ((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).σ) ∈ support
        ((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut prims K circuits settings D Z).pre)
    (r : TreeCheckTailResult A)
    (run : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (record : TreeCheckIndexedRecord prims circuits D A x j r) :
    ∃ trace : TreeCheckOpeningTrace prims K circuits D A
      ((sourceWalk prims K D A circuits settings top tree x j Z step setup).boundary c).batch o record.record,
      trace.after.2 <+: r.2 := by
  let W := sourceWalk prims K D A circuits settings top tree x j Z step setup
  let b := W.boundary c
  let data := fun i => treeCheckPrefixData (o.1.2 i)
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    have one := congrArg (fun xs : C.Party → Keys C => (xs i).parameter) record.dealt
    have two := congrArg (fun xs : C.Party → Keys C => (xs (refHolder D K.publicTerm)).parameter) record.dealt
    exact one.trans two.symm
  have boundaryRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre (W := W)
      (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      (D := D) (Z := Z) (c := c) (o := o) preRun)
  obtain ⟨remaining, state, checked, before, out, _, outLog, outEq, ⟨phase⟩⟩ :=
    batchCont_opening_phase prims K circuits settings D A Z b (fun _ => rfl) parameters o boundaryRun r run
      ⟨record.party, (record.output, record.records), record.result⟩
  obtain ⟨opening, _, _, openingLog, localRun⟩ := opening_phase_success prims K D A remaining state
    (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length
    (fun i => (data i).2.1.1) (fun i => batchOpeningCont circuits b.batch data i (checked i))
    before out phase record.party record.honest (record.output, record.records)
    (by simpa only [outEq] using record.result)
  have hlen := (decode_sound prims K D A circuits settings top tree x setup.1.2 j c).1
    record.party record.honest
  have indexed := callerCont_record_index K circuits settings top tree x setup.1.2 j c.1.2 record.party
    hlen.1 _ _ _ (record.output, record.records) localRun
  have recorded : record.record = openingRecord circuits (b.batch.ctx record.party) b.batch.jobs
      b.batch.initial (data record.party) (checked record.party) opening.output :=
    Option.some.inj (record.indexed.symm.trans indexed)
  have assembled : assemble (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) opening.output =
      record.record.outputs := by
    rw [recorded]
    simp only [openingRecord, parameters record.party]
  exact ⟨opening.toTrace record.record assembled, openingLog.trans outLog⟩



/-- Fewer scheduler rounds give an earlier log when both complete replays
follow the same classified transcript. -/
theorem replay_rounds_log_prefix {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel more : ℕ) (room : fuel ≤ more)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (a b : A.State × (C.Party → Option α)) (left right log : TreeSimLog C)
    (ha : TreeSimCheckReplay (executeRounds worldRoles D A noFunctionality fuel state steps) left a)
    (hb : TreeSimCheckReplay (executeRounds worldRoles D A noFunctionality more state steps) right b)
    (hl : left <+: log) (hr : right <+: log) : left <+: right := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le room
  rw [executeRounds_eq_executeSteps] at ha hb
  obtain ⟨sa, ha, _⟩ := ha.map_inv _
  obtain ⟨sb, hb, _⟩ := hb.map_inv _
  rw [executeSteps_add] at hb
  obtain ⟨middle, pre, post, before, _, rfl⟩ := hb.bind_inv _ _
  obtain ⟨_, logs⟩ := ha.common_prefix_unique before hl ((List.prefix_append pre post).trans hr)
  rw [logs]
  exact List.prefix_append _ _

/-- The original source executions have ordered transcript prefixes when
their round budgets are ordered, including setup and initial local work. -/
theorem replay_execution_log_prefix {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel more : ℕ) (room : fuel ≤ more)
    (program : C.Party → Keys C → PartyM C E RealSpec α) (x : C.Party → Keys C) (z : Aux)
    (a b : A.State × (C.Party → Option α)) (left right log : TreeSimLog C)
    (ha : TreeSimCheckReplay (realExecution D A noFunctionality fuel program x z) left a)
    (hb : TreeSimCheckReplay (realExecution D A noFunctionality more program x z) right b)
    (hl : left <+: log) (hr : right <+: log) : left <+: right := by
  unfold realExecution executePhase at ha hb
  obtain ⟨sa, preA, postA, hsa, hka, rfl⟩ := ha.bind_inv _ _
  obtain ⟨sb, preB, postB, hsb, hkb, rfl⟩ := hb.bind_inv _ _
  have hpreA : preA <+: log := (List.prefix_append preA postA).trans hl
  have hpreB : preB <+: log := (List.prefix_append preB postB).trans hr
  obtain ⟨rfl, rfl⟩ := hsa.common_prefix_unique hsb hpreA hpreB
  obtain ⟨tail, rfl⟩ := hpreA
  simp only [List.prefix_append_right_inj] at hl hr ⊢
  obtain ⟨stepsA, initA, restA, hstepsA, hrestA, rfl⟩ := hka.bind_inv _ _
  obtain ⟨stepsB, initB, restB, hstepsB, hrestB, rfl⟩ := hkb.bind_inv _ _
  have hinitA : initA <+: tail := (List.prefix_append initA restA).trans hl
  have hinitB : initB <+: tail := (List.prefix_append initB restB).trans hr
  obtain ⟨rfl, rfl⟩ := hstepsA.common_prefix_unique hstepsB hinitA hinitB
  obtain ⟨final, rfl⟩ := hinitA
  simp only [List.prefix_append_right_inj] at hl hr ⊢
  exact replay_rounds_log_prefix D A fuel more room sa stepsA a b restA restB final hrestA hrestB hl hr

/-- A still-pending original-source execution precedes every successful
reference execution sharing its classified transcript. -/
theorem replay_pending_before_reference {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel referenceFuel : ℕ)
    (program : C.Party → Keys C → PartyM C E RealSpec α) (x : C.Party → Keys C) (z : Aux)
    (pending reference : A.State × (C.Party → Option α)) (left right log : TreeSimLog C)
    (hp : TreeSimCheckReplay (realExecution D A noFunctionality fuel program x z) left pending)
    (hr : TreeSimCheckReplay (realExecution D A noFunctionality referenceFuel program x z) right reference)
    (hl : left <+: log) (href : right <+: log) (absent : pending.2 = fun _ => none)
    (accepted : ∃ i value, reference.2 i = some value) : left <+: right := by
  by_cases room : fuel ≤ referenceFuel
  · exact replay_execution_log_prefix D A fuel referenceFuel room program x z pending reference
      left right log hp hr hl href
  · obtain ⟨i, value, accepted⟩ := accepted
    have present := treeSimCheckReplay_execution_mono D A noFunctionality referenceFuel fuel
      (by omega) program x z reference pending right left log hr hp href hl i value accepted
    rw [absent] at present
    cases present


/-- Run a pending source for a fixed number of exchanges while retaining
actual scheduler steps, both caches and the whole classified log. -/
def pendingSteps (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (rounds : ℕ) (p : TreeCheckWalkDef.Pending A) :
    ProbComp ((A.State × (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C)))) × TreeSimState C) :=
  (simulateQ (treeSimLoggedWorld prims D) (do
    let steps ← startSteps worldRoles D p.program
    executeSteps worldRoles D A noFunctionality rounds p.state steps)).run p.world

/-- The typed signing selector preserves the complete source snapshot law,
not only the eventual observation. -/
theorem selectPending_steps {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (p : TreeCheckWalkDef.Pending A)
    (source : ∀ i, i ∉ D.1 → p.program i = treeLockstepLocalOption (gate i) >>= cont i) (rounds : ℕ) :
    pendingSteps prims D A rounds p =
      selectPending prims D A gate cont p >>= pendingSteps prims D A rounds := by
  have start : startSteps worldRoles D p.program =
      startSteps worldRoles D (fun i => treeLockstepLocalOption (gate i) >>= cont i) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, source i]
  unfold pendingSteps selectPending
  rw [start, start_select_programs]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

/-- Preparing a signing checkpoint preserves the same pending source
snapshot, including the already executed part of its local pass. -/
theorem prepare_steps (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j rounds : ℕ) (p : TreeCheckWalkDef.Pending A) :
    pendingSteps prims D A rounds p =
      prepare prims K D A circuits settings top tree x setup j p >>= pendingSteps prims D A rounds := by
  unfold prepare
  cases tree with
  | top => simp
  | bottom b =>
    dsimp only
    split_ifs with first found
    · apply selectPending_steps
      intro i hi
      rw [(Classical.choose_spec found).2 i hi, signingHead_program]
    · simp
    · simp

/-- A nonterminal source scheduler step followed by a snapshot is an actual
snapshot of its predecessor one exchange later. -/
theorem next_steps_support (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (fuel rounds : ℕ) (p next : TreeCheckWalkDef.Pending A)
    (nextRun : .inl next ∈ support (TreeCheckWalkDef.next prims D Z fuel p))
    (out : (A.State × (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C)))) × TreeSimState C)
    (rest : out ∈ support (pendingSteps prims D A rounds next)) :
    out ∈ support (pendingSteps prims D A (rounds + 1) p) := by
  unfold TreeCheckWalkDef.next at nextRun
  simp only [mem_support_bind_iff] at nextRun
  obtain ⟨started, startRun, nextRun⟩ := nextRun
  split_ifs at nextRun with stopped
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at nextRun
    obtain ⟨observed, _, impossible⟩ := nextRun
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at nextRun
    obtain ⟨reply, replyRun, rfl⟩ := nextRun
    have corrupt := TreeCheckWalkDef.start_corrupt D p.program started.1
      (treeCheck_logged_support prims D _ _ startRun)
    unfold pendingSteps at rest ⊢
    dsimp only at rest
    rw [TreeCheckWalkDef.resume_start D started.1 corrupt reply.1.2] at rest
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨locals, localsRun, suffix⟩ := rest
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    refine ⟨started, startRun, ?_⟩
    rw [executeSteps, if_neg stopped, stepRound_real]
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind, mem_support_bind_iff]
    exact ⟨reply, replyRun, locals, localsRun, suffix⟩

/-- Every snapshot after a decoded checkpoint is a snapshot of the original
source. Each missed recognition adds exactly one actual scheduler exchange. -/
theorem walk_steps_support (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (Z : Distinguisher C A.State TreeOutput)
    (fuel : ℕ) (p : TreeCheckWalkDef.Pending A)
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup j))
    (run : .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p))
    (rounds : ℕ)
    (out : (A.State × (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C)))) × TreeSimState C)
    (rest : out ∈ support (pendingSteps prims D A rounds c.1.1)) :
    ∃ spent, spent ≤ fuel ∧ out ∈ support (pendingSteps prims D A (spent + rounds) p) := by
  induction fuel generalizing p with
  | zero =>
    simp only [walk, mem_support_bind_iff] at run
    obtain ⟨current, prepared, run⟩ := run
    split_ifs at run
    · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
      cases run
      refine ⟨0, le_rfl, ?_⟩
      simp only [Nat.zero_add]
      change out ∈ support (pendingSteps prims D A rounds {p with fuel := 0})
      rw [prepare_steps prims K D A circuits settings top tree x setup j rounds {p with fuel := 0},
        mem_support_bind_iff]
      exact ⟨current, prepared, rest⟩
    · simp only [support_map, Set.mem_image] at run
      obtain ⟨_, _, impossible⟩ := run
      cases impossible
  | succ fuel ih =>
    simp only [walk, mem_support_bind_iff] at run
    obtain ⟨current, prepared, run⟩ := run
    split_ifs at run
    · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
      cases run
      refine ⟨0, Nat.zero_le _, ?_⟩
      simp only [Nat.zero_add]
      change out ∈ support (pendingSteps prims D A rounds {p with fuel := fuel + 1})
      rw [prepare_steps prims K D A circuits settings top tree x setup j rounds {p with fuel := fuel + 1},
        mem_support_bind_iff]
      exact ⟨current, prepared, rest⟩
    · rw [mem_support_bind_iff] at run
      obtain ⟨outcome, nextRun, run⟩ := run
      cases outcome with
      | inr terminal => simp only [mem_support_pure_iff] at run; cases run
      | inl next =>
        obtain ⟨spent, bound, snapshot⟩ := ih next run
        have previous := next_steps_support prims D A Z fuel (spent + rounds) current next nextRun out snapshot
        refine ⟨spent + 1, by omega, ?_⟩
        rw [show spent + 1 + rounds = spent + rounds + 1 by omega]
        change out ∈ support (pendingSteps prims D A (spent + rounds + 1) {p with fuel := fuel + 1})
        rw [prepare_steps prims K D A circuits settings top tree x setup j (spent + rounds + 1)
            {p with fuel := fuel + 1}, mem_support_bind_iff]
        exact ⟨current, prepared, previous⟩


/-- Projecting a retained-step snapshot gives the ordinary phase execution,
with exactly the same cache and log. -/
theorem pendingSteps_projection (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (rounds : ℕ) (p : TreeCheckWalkDef.Pending A) :
    (fun out => ((out.1.1, fun i => (out.1.2 i).output), out.2)) <$> pendingSteps prims D A rounds p =
      (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality rounds p.state p.program)).run p.world := by
  unfold pendingSteps executePhase
  simp only [executeRounds_eq_executeSteps, simulateQ_bind, simulateQ_map, StateT.run_bind,
    StateT.run_map, map_bind]

set_option maxRecDepth 2000 in
/-- Just after the selected batch prefix, the real source still has no final
outputs. The retained start of its mandatory check/open exchange gives an
actual snapshot log between this checkpoint and its continuation's final log. -/
theorem batch_prefix_pending (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A)
    (parameters : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (o : TreeCheckTailCheckpoint A) (preRun : o ∈ support (b.pre prims K circuits settings D))
    (r : TreeCheckTailResult A) (run : r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o)) :
    ∃ out : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C,
      out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (b.batch.rounds circuits settings) b.batch.state
          (b.program K circuits settings))).run b.batch.world) ∧
      o.2.2 <+: out.2.2 ∧ out.2.2 <+: r.2 ∧ out.1.2 = fun _ => none := by
  unfold treeCheckBatchCont treeCheckObserve at run
  simp only [mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨next, nextRun, final, finalRun, observed, observeRun, rfl⟩ := run
  have each := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _
    (treeCheck_logged_support prims D _ _ nextRun))
  have pending i : (next.1 i).output = none := by
    have localRun := each i
    cases present : o.1.2 i with
    | none =>
      have stopped : next.1 i = .done none := by
        simpa only [present, continueStep, mem_support_pure_iff] using localRun
      simp only [stopped, Step.output]
    | some data =>
      have exchange : TreeSimCheckExchange
          (treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial data >>= b.batch.k i) := by
        unfold treeSimCheckBatchFinish
        rw [bind_assoc]
        exact (treeSimCheckAfterVerify_exchange K (b.batch.ctx i) _ data.2).bind _
      exact (exchange (next.1 i) (by simpa only [present, continueStep] using localRun)).pending
  refine ⟨((o.1.1, fun i => (next.1 i).output), next.2), ?_,
    treeSimLoggedWorld_prefix prims D _ o.2 next nextRun,
    (treeSimLoggedWorld_prefix prims D _ next.2 final finalRun).trans
      (treeSimLoggedWorld_prefix prims D _ final.2 observed observeRun), funext pending⟩
  have split := treeSimCheckTimed_phase_split D A
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds)
    0 b.batch.state
    (fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
      treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial)
    (fun i data => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial data >>= b.batch.k i)
    (fun i => treeLockstep_localPrelude_timed _ _ _ (by
      simpa only [parameters i] using treeSimCheckBatchPrefix_timed K circuits settings
        (b.batch.ctx i) b.batch.jobs b.batch.initial))
  simp only [Nat.add_zero, bind_assoc] at split
  unfold TreeCheckTailBoundary.program TreeCheckBatchBoundary.rounds
  simp only [treeSimCheckBatchAudit_run_prefix, bind_assoc]
  rw [split]
  simp only [simulateQ_bind, StateT.run_bind, executeRounds, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨o, preRun, next, nextRun, rfl⟩


/-- The fixed initial source phase is the literal continuation of its actual
setup rows, for every snapshot round budget. -/
theorem initial_phase (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : setup ∈ support (treeSaltSetup prims D A x z)) (rounds : ℕ) :
    (simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rounds
        (TreeCheckWalkDef.initial K circuits settings top tree x setup).state
        (TreeCheckWalkDef.initial K circuits settings top tree x setup).program)).run setup.2 =
      treeCheckAfterSetupPrefix prims D A rounds
        (fun i keys prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, keys, prss⟩ top tree) x setup := by
  have corrupt : ∀ i ∈ D.1, setup.1.2 i = none := by
    simp only [treeSaltSetup, mem_support_bind_iff] at setupRun
    obtain ⟨start, _, hs⟩ := setupRun
    exact treeSetup_corrupt_none prims D A start.1 start.2 setup hs
  have restart : free (Concrete.sequenceFin fun i => continueStep
      (fun prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
      (.done (setup.1.2 i))) =
      startSteps worldRoles D (TreeCheckWalkDef.initial K circuits settings top tree x setup).program := by
    unfold startSteps
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi, corrupt i hi, continueStep, free_pure]
    · cases he : setup.1.2 i <;>
        simp [TreeCheckWalkDef.initial, hi, he, continueStep, worldRoles, advance_pure, free_pure]
  unfold treeCheckAfterSetupPrefix executePhase
  rw [restart]
  simp only [simulateQ_bind, StateT.run_bind]
  rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
/-- A checkpoint on the frozen source supplies an original audited execution
whose final outputs are still absent and whose log already contains that
checkpoint. This is a supported snapshot of the same cached/logged run. -/
theorem sourceWalk_pending_execution (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : setup ∈ support (treeSaltSetup prims D A x z))
    (c : TreeCheckWalkDef.Decoded (decode prims K D A circuits settings top tree x setup.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (preRun : (.inl (c, o) : ((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).σ) ∈ support
        ((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut prims K circuits settings D Z).pre)
    (r : TreeCheckTailResult A)
    (run : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (dealt : DealtInputs D x) :
    ∃ (rounds : ℕ)
      (out : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C),
      out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (realExecution D A noFunctionality rounds
          (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree) x z)).run ((∅, ∅), [])) ∧
      o.2.2 <+: out.2.2 ∧ out.2.2 <+: r.2 ∧ out.1.2 = fun _ => none := by
  let W := sourceWalk prims K D A circuits settings top tree x j Z step setup
  let b := W.boundary c
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  have boundaryRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre (W := W)
      (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      (D := D) (Z := Z) (c := c) (o := o) preRun)
  have walkRun : .inl c ∈ support W.pre := by
    with_reducible exact (TreeCheckWalkDef.index_support prims D Z K circuits settings W c o preRun)
  obtain ⟨out, phaseRun, before, after, absent⟩ :=
    batch_prefix_pending prims K circuits settings D A Z b parameters o boundaryRun r run
  have same : (simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (b.batch.rounds circuits settings) c.1.1.state c.1.1.program)).run c.1.1.world =
      (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (b.batch.rounds circuits settings) b.batch.state
          (b.program K circuits settings))).run b.batch.world := by
    unfold executePhase
    simp only [simulateQ_bind, StateT.run_bind]
    rw [(decode_sound prims K D A circuits settings top tree x setup.1.2 j c).2.2]
    rfl
  rw [← same, ← pendingSteps_projection, support_map] at phaseRun
  obtain ⟨snapshot, snapshotRun, snapshotEq⟩ := phaseRun
  obtain ⟨spent, _, original⟩ := by
    with_reducible exact (walk_steps_support prims K D A circuits settings top tree x setup.1.2 j Z
      (TreeCheckWalkDef.initial K circuits settings top tree x setup).fuel
      (TreeCheckWalkDef.initial K circuits settings top tree x setup) c walkRun
      (b.batch.rounds circuits settings) snapshot snapshotRun)
  have projected : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (spent + b.batch.rounds circuits settings)
        (TreeCheckWalkDef.initial K circuits settings top tree x setup).state
        (TreeCheckWalkDef.initial K circuits settings top tree x setup).program)).run setup.2) := by
    have mapped : out ∈ support ((fun out => ((out.1.1, fun i => (out.1.2 i).output), out.2)) <$>
        pendingSteps prims D A (spent + b.batch.rounds circuits settings)
          (TreeCheckWalkDef.initial K circuits settings top tree x setup)) := by
      rw [support_map]
      exact ⟨snapshot, original, snapshotEq⟩
    rw [pendingSteps_projection] at mapped
    exact mapped
  rw [initial_phase prims K D A circuits settings top tree x z setup setupRun] at projected
  have supported := (treeCheckAfterSetupPrefix_supported prims D A _ _ x z setup setupRun out projected).1
  exact ⟨spent + b.batch.rounds circuits settings + setupRounds, out, supported, before, after, absent⟩

/-- An indexed record together with the successful audited replay that
supplies its coherent reference log. The replay is retained in the type, so
selecting a witness cannot discard this provenance. -/
structure IndexedReference (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : ℕ) (r : TreeCheckTailResult A) where
  record : TreeCheckIndexedRecord prims circuits D A x j r
  fuel : ℕ
  within : fuel ≤ ceremonyFuel circuits settings
  audited : A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))
  replay : TreeSimCheckReplay (realExecution D A noFunctionality fuel
    (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree) x z) record.referenceLog audited
  accepted : audited.2 record.party = some (record.output, record.records)

/-- Fix the indexed witness and its actual reference replay from the same bad
event, without weakening the reference to mere coherence on an arbitrary log. -/
def indexedReference (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree)) (r : TreeCheckTailResult A)
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r) :
    IndexedReference prims K circuits settings top tree D A x z j.val r :=
  Classical.choice (by
    obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
      dealt, hi, result, _, _, listed, index, _, wrong, reference⟩ := bad.2
    obtain ⟨fuel, pref, audited, dealer, out, room, hpref, _, replay, accepted, _, _, hashes⟩ := reference
    rw [← dealt] at replay
    exact ⟨⟨⟨parameter, seeds, pairs, i, value, records, hash, batch, pref, dealt, hi,
      result, by simp [listed, index], hpref, hashes, wrong⟩, fuel, room, audited, replay, accepted⟩⟩)

/-- The coherent audited reference selected from the same bad event contains
the selected checkpoint. Both the source family and the bad-record witness
are fixed; this clause asks only for chronological inclusion of their logs. -/
def WalkReferencePrefix (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
      ∀ r ∈ support ((W.cut prims K circuits settings D Z).cont (.inl (c, o))),
        ∀ bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r,
          ¬ TreeCheckUncounted D r.2 →
          o.2.2 <+: (indexedReference prims K circuits settings top tree D A x z j r bad).record.referenceLog


set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
/-- The coherent reference occurs after the source checkpoint: otherwise
its accepted output would persist into an original-source snapshot whose
outputs are all still absent. -/
theorem walkReferencePrefix (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    WalkReferencePrefix prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j setup setupRun c o preRun r run bad counted
  let reference := indexedReference prims K circuits settings top tree D A x z j r bad
  obtain ⟨fuel, out, original, before, after, absent⟩ := by
    with_reducible exact (sourceWalk_pending_execution prims K D A circuits settings top tree x z j.val Z
      (TreeCheckQueryBudget.ofBound bounded).step setup setupRun c o preRun r run dealt)
  have replay : TreeSimCheckReplay (realExecution D A noFunctionality fuel
      (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree) x z) out.2.2 out.1 := by
    apply treeSimCheckReplay_logged prims D
    rw [treeSimLoggedRun_eq_run, support_map]
    exact ⟨out, original, rfl⟩
  exact before.trans (replay_pending_before_reference D A fuel reference.fuel
    (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree) x z out.1 reference.audited
    out.2.2 reference.record.referenceLog r.2 replay reference.replay after reference.record.referencePrefix
    absent ⟨reference.record.party, (reference.record.output, reference.record.records), reference.accepted⟩)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
/-- Record identity and the actual scheduled opening discharge the original
opening clause from chronological inclusion of the fixed coherent reference. -/
theorem walkOpening_of_referencePrefix (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (reference : WalkReferencePrefix prims K circuits settings) :
    WalkOpening prims K circuits settings := by
  unfold WalkReferencePrefix AtWalk at reference
  intro hb top tree D A x z Z q dealt bounded small j setup setupRun c o preRun r run bad counted
  let record := (indexedReference prims K circuits settings top tree D A x z j r bad).record
  have metadata := sourceWalk_indexed_metadata prims K D A circuits settings top tree x j.val Z
    (TreeCheckQueryBudget.ofBound bounded).step setup c o r run record
  have hprefix : o.2.2 <+: record.referenceLog := by
    with_reducible exact (reference hb top tree D A x z Z q dealt bounded small j setup setupRun
      c o preRun r run bad counted)
  obtain ⟨trace, later⟩ := by
    with_reducible exact (sourceWalk_indexed_trace prims K D A circuits settings top tree x j.val Z
      (TreeCheckQueryBudget.ofBound bounded).step setup c o preRun r run record)
  exact ⟨record, metadata.1, metadata.2.1, metadata.2.2, hprefix, trace, later⟩

/-- The original indexed-opening clause for the single frozen source family. -/
theorem walkOpening (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    WalkOpening prims K circuits settings :=
  walkOpening_of_referencePrefix prims K circuits settings (walkReferencePrefix prims K circuits settings)

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.callerCont_record_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms callerCont_record_index

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.sourceWalk_indexed_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_indexed_record

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.opening_phase_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms opening_phase_success

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.timed_phase_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms timed_phase_fuel

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.check_open_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_open_phase

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.batchCont_opening_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchCont_opening_phase

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.sourceWalk_indexed_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_indexed_trace

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.replay_pending_before_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_pending_before_reference

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.prepare_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_steps

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.walk_steps_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_steps_support

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.batch_prefix_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_prefix_pending

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.sourceWalk_pending_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_pending_execution

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.walkReferencePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkReferencePrefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.walkOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkOpening


end TreeCheckWalkRecipe
end ThresholdLeanXmssSecurity
