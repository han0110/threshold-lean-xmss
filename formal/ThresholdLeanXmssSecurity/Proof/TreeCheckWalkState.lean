import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoverage

/-!
# The walk state of the fixed source walk

This file concerns the state of the fixed walk `family` of
`TreeCheckWalkRecipe` at the start of a batch. The family, its decoder and its
witness are not changed.

## Programs after exchanges

* `Residual n P Q` states that the scheduler turns the program `P` into the
  program `Q` with exactly `n` exchanges. A program that stops keeps its output.
* `Residual.trans` and `Residual.split` join and cut residuals.
  `Residual.of_advance` is one local pass and one exchange.
* `Residual.timed_bind` and `Residual.party_bind` cut after a prefix with
  `TreeSimCheckTimed`. Only the continuation of one supported result of the
  prefix remains.
* `residual_openRep` shows that one exchange into `openRep` leaves an abort,
  or the rejecting tail `openTail` followed by the continuation at the opened
  value. An abort frame gives the abort (`exchangeResume`).

## Batches of the first run

* `callerProgram j caller i` is the program of party `i` at the start of batch
  `j` for `caller`. It is the program of the boundary of `callerBatch`
  (`boundary_program`).
* `residual_batch` and `batch_step` take one batch of the first run. The
  residual after `batchRounds` exchanges is the program at batch `j + 1` for a
  caller with one more output, one more record and the tail `openTail`. The
  counters are `(lockstepStart … (j + 1), j + 1)` by `lockstepLabels_check`.
  An abort is a caller whose tail is `pure none`. Its new output and record
  are placeholders.
* `residual_first` iterates this from batch `0` to batch `j`.
  `batchStart j` counts the exchanges of the batches before `j`.

## The walk state

* `Reached start n q` states that `n` rounds of `next` lead from `start` to
  `q`, with one unit of fuel for each round. `Reached.residual` gives the
  residual of each honest program, and `Reached.fuel` the fuel.
* `walkState_first` is the invariant inside the first run. At the state
  reached after `batchStart j` rounds, each honest program is
  `callerProgram j` of one merged caller with the lengths of `CallerLengths`.
  The counters are those of `callerBatch`. By `batch_step` and
  `callerProgram_abort`, a party that got an abort frame has a caller whose
  tail is `pure none`.
* `walkState_first_fits` adds the fuel room and gives `Fits`.
  `walkState_first_decode` gives a decoder hit. The encoding of the merged
  caller is a constant, because the first run does not read it.
* `walk_hit_reached` shows that a decoded walk checkpoint away from the first
  signing batch is a reached state. The decoder can hit early, for example
  when every honest party has aborted.
* `walk_terminal_first` shows that a finished walk outcome of batch `j` inside
  the first run comes from a state before round `batchStart j`, where `next`
  stops because each honest step is done.
* `WalkStateFirst` is the invariant on the fixed family for every batch of the
  first run, and `walkStateFirst` proves it. This covers every batch of a top
  tree.

## The signing run

* `WalkStateSigning` is the program part for the batches of the signing run of
  a bottom tree, for one party and one fixed encoding.
* `WalkStateEntry` states that the walk state at the end of the first run
  matches a signing point.

The jobs `signJobs b encoding` have the circuit `.chainValue … (encoding l)`,
so `batchRounds` of a signing chunk can depend on the encoding. A common round
index for the honest parties in the signing run thus needs one encoding.

One encoding does not hold at every reached state. Take a committee where a
corrupt operator owns a term `T` and two honest parties `i` and `k` do not
hold `T`. In the last opening of the first run, the owner sends one copy of
`T` to `i` and a different copy to `k`. Just after this exchange, the opened
values of `i` and `k` differ, and the encodings that they compute from these
values later can differ. The tails `openTail` that compare
the `.copy` digests have not run, so the log has no collision yet. The tails
reject one of the two copies unless a `.copy` collision occurs. One encoding is
thus a fact about the states after the tails, and only outside a `.copy`,
`.history` or `.digest` collision. `prepare` stops at the first successful head
and keeps the later heads pending, so a fresh wrong-copy query can still collide
on a later branch. At the first signing batch, the successful signing heads
agree along the runs whose extended log, with its checks, has no budget
collision. A collision-free current log does not give this for every cache
extension.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkState

open TreeCheckWalkRecipe TreeCheckWalkCoverage

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

section Residual

/-- `Residual n P Q` states that the scheduler can turn the program `P` into
the program `Q` with exactly `n` exchanges. A program that stops keeps its
output. -/
inductive Residual {α : Type} :
    ℕ → OracleComp (PartySpec C E RealSpec) (Option α) →
      OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | refl (P : OracleComp (PartySpec C E RealSpec) (Option α)) : Residual 0 P P
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (r : (LocalSpec C).Range q) (Q : OracleComp (PartySpec C E RealSpec) (Option α))
      (h : Residual (n + 1) (k r) Q) : Residual (n + 1) (.roll (.inl (.inl q)) k) Q
  | round (n : ℕ) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (inbox : Mail C E) (Q : OracleComp (PartySpec C E RealSpec) (Option α))
      (h : Residual n (k inbox) Q) : Residual (n + 1) (.roll (.inl (.inr out)) k) Q
  | done (n : ℕ) (out : Option α) : Residual (n + 1) (pure out) (pure out)

variable {α : Type}

theorem Residual.pure_inv {n : ℕ} {out : Option α} {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Residual n (pure out) Q) : Q = pure out := by
  cases h with
  | refl => rfl
  | done => rfl

theorem Residual.zero_inv {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Residual 0 P Q) : Q = P := by
  cases h
  rfl

theorem Residual.trans {n m : ℕ} {P Q R : OracleComp (PartySpec C E RealSpec) (Option α)}
    (first : Residual n P Q) (second : Residual m Q R) : Residual (n + m) P R := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | queryLocal n q k r Q h ih =>
    rw [Nat.add_right_comm]
    exact .queryLocal (n + m) q k r R (by rw [Nat.add_right_comm]; exact ih second)
  | round n out k inbox Q h ih =>
    rw [Nat.add_right_comm]
    exact .round (n + m) out k inbox R (ih second)
  | done n out =>
    rw [second.pure_inv, Nat.add_right_comm]
    exact .done (n + m) out

theorem Residual.split {a b : ℕ} {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Residual (a + b) P Q) : ∃ M, Residual a P M ∧ Residual b M Q := by
  generalize count : a + b = n at h
  induction h generalizing a with
  | refl P =>
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    exact ⟨P, .refl P, .refl P⟩
  | queryLocal n q k r Q h ih =>
    cases a with
    | zero => exact ⟨_, .refl _, by rw [Nat.zero_add] at count; rw [count]; exact .queryLocal n q k r Q h⟩
    | succ a =>
      obtain ⟨M, first, second⟩ := ih count
      exact ⟨M, .queryLocal a q k r M first, second⟩
  | round n out k inbox Q h ih =>
    cases a with
    | zero => exact ⟨_, .refl _, by rw [Nat.zero_add] at count; rw [count]; exact .round n out k inbox Q h⟩
    | succ a =>
      obtain ⟨M, first, second⟩ := ih (a := a) (by omega)
      exact ⟨M, .round a out k inbox M first, second⟩
  | done n out =>
    cases a with
    | zero => exact ⟨_, .refl _, by rw [Nat.zero_add] at count; rw [count]; exact .done n out⟩
    | succ a =>
      refine ⟨pure out, .done a out, ?_⟩
      cases b with
      | zero => exact .refl _
      | succ b => exact .done b out

/-- The program that the scheduler resumes after a step. -/
def resumed : Step C E RealSpec α → Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)
  | .done out, _ => pure out
  | .wait _ k, inbox => k inbox
  | .call impossible _, _ => impossible.elim

theorem Residual.of_advance {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (step : Step C E RealSpec α) (run : step ∈ support (advance Q)) (inbox : Mail C E) :
    Residual 1 Q (resumed step inbox) := by
  induction Q with
  | pure out =>
    change step ∈ support (pure (Step.done out) : OracleComp (LocalSpec C) (Step C E RealSpec α)) at run
    have same : step = .done out := by simpa using run
    subst same
    exact .done 0 out
  | queryBind t k ih =>
    rcases t with (q | out) | impossible
    · simp only [ThresholdLeanXmss.advance, mem_support_bind_iff] at run
      obtain ⟨r, -, run⟩ := run
      exact .queryLocal 0 q k r _ (ih r run)
    · simp only [ThresholdLeanXmss.advance, mem_support_pure_iff] at run
      subst run
      exact .round 0 out k inbox _ (.refl _)
    · exact impossible.elim

theorem Residual.local_inv {c : ℕ} {q : (LocalSpec C).Domain}
    {k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α)}
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Residual c (.roll (.inl (.inl q)) k) Q) :
    c = 0 ∨ ∃ r, Residual c (k r) Q := by
  cases h with
  | refl => exact .inl rfl
  | queryLocal n q k r Q h => exact .inr ⟨r, h⟩

theorem Residual.round_inv {c : ℕ} {out : Mail C E}
    {k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)}
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Residual c (.roll (.inl (.inr out)) k) Q) :
    c = 0 ∨ ∃ n inbox, c = n + 1 ∧ Residual n (k inbox) Q := by
  cases h with
  | refl => exact .inl rfl
  | round n out k inbox Q h => exact .inr ⟨n, inbox, rfl, h⟩

/-- A residual of a timed prefix followed by a continuation. After the
exchanges of the prefix, only the continuation of one of its results remains. -/
theorem Residual.timed_bind {β : Type} {m N : ℕ}
    {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed m oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α)) (abort : f none = pure none)
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)} (h : Residual (m + N) (oa >>= f) Q) :
    Q = pure none ∨ ∃ a, some a ∈ support oa ∧ Residual N (f (some a)) Q := by
  induction timed generalizing N with
  | abort n =>
    rw [pure_bind, abort] at h
    exact .inl h.pure_inv
  | done a =>
    rw [pure_bind, Nat.zero_add] at h
    exact .inr ⟨a, by simp, h⟩
  | queryLocal n q k hk ih =>
    rcases Residual.local_inv (k := fun r => k r >>= f) h with zero | ⟨r, h⟩
    · omega
    · rcases ih r h with none | ⟨a, ha, h⟩
      · exact .inl none
      · refine .inr ⟨a, ?_, h⟩
        change some a ∈ support (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
  | round n out k hk ih =>
    rcases Residual.round_inv (k := fun r => k r >>= f) h with zero | ⟨c, inbox, count, h⟩
    · omega
    · rw [show c = n + N by omega] at h
      rcases ih inbox h with none | ⟨a, ha, h⟩
      · exact .inl none
      · refine .inr ⟨a, ?_, h⟩
        change some a ∈ support (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩

/-- `Residual.timed_bind` for a party program. -/
theorem Residual.party_bind {β : Type} {m N : ℕ} {P : PartyM C E RealSpec β}
    {g : β → PartyM C E RealSpec α} (timed : TreeSimCheckTimed m P.run)
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)} (h : Residual (m + N) (P >>= g).run Q) :
    Q = pure none ∨ ∃ a, some a ∈ support P.run ∧ Residual N (g a).run Q := by
  simp only [OptionT.run_bind, Option.elimM] at h
  exact Residual.timed_bind timed (fun o => o.elim (pure none) fun a => (g a).run) rfl h

set_option backward.isDefEq.respectTransparency false in
/-- Local queries before the next exchange leave only the continuation of one
of their results. -/
theorem Residual.lift_bind {β : Type} {n : ℕ} (p : OracleComp (LocalSpec C) β)
    (f : β → OracleComp (PartySpec C E RealSpec) (Option α))
    {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Residual (n + 1) (liftComp p (PartySpec C E RealSpec) >>= f) Q) :
    ∃ a, Residual (n + 1) (f a) Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact ⟨a, by simpa only [liftComp_pure, pure_bind] using h⟩
  | query_bind q k ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, bind_assoc] at h
    have hq : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
      rw [← liftM_query_local]
      rfl
    rw [hq] at h
    rcases Residual.local_inv h with zero | ⟨r, h⟩
    · omega
    · exact ih r h

set_option backward.isDefEq.respectTransparency false in
/-- After one exchange, the program is the continuation of `exchange` at
some inbox. -/
theorem Residual.exchange_inv {β : Type} (out : Mail C E) (k : Mail C E → PartyM C E RealSpec β)
    {Q : OracleComp (PartySpec C E RealSpec) (Option β)}
    (h : Residual 1 (exchange out >>= k).run Q) : ∃ inbox, Q = exchangeResume k inbox := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk,
      pure_bind, Option.elimM]
    apply bind_congr
    intro inbox
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he] at h
  rcases Residual.round_inv h with zero | ⟨n, inbox, count, h⟩
  · omega
  · obtain rfl : n = 0 := by omega
    exact ⟨inbox, h.zero_inv⟩

end Residual

section Opening

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)

set_option backward.isDefEq.respectTransparency false in
/-- One exchange into `openRep` leaves an abort, or the rejecting local tail
`openTail` followed by the continuation at the fixed opened value. -/
theorem residual_openRep {β : Type} (ctx : Context C) (v : Shares C Bit) (count : ℕ)
    (k : (ℕ → Bit) → PartyM C E RealSpec β) {Q : OracleComp (PartySpec C E RealSpec) (Option β)}
    (h : Residual 1 (openRep K ctx v count >>= k).run Q) :
    Q = pure none ∨ ∃ inbox, Q = (treeLockstepLocalPrelude (openTail K ctx.self count v inbox) >>= fun _ =>
      k (fun g => ∑ T, treeSimOpenCopy K ctx.self count v inbox T g)).run := by
  unfold openRep at h
  simp only [bind_assoc, pure_bind] at h
  rw [show ∀ {γ : Type} (p : OracleComp (RoSpec C) γ) (f : γ → PartyM C E RealSpec β),
      (oracleStep p >>= f).run = liftComp (liftComp p (LocalSpec C)) (PartySpec C E RealSpec) >>= fun a => (f a).run
    from fun p f => by simp [oracleStep, localStep, OptionT.run_bind, OptionT.lift]] at h
  obtain ⟨digests, h⟩ := Residual.lift_bind (n := 0) _ _ h
  obtain ⟨inbox, rfl⟩ := Residual.exchange_inv _ _ h
  unfold exchangeResume
  split_ifs with aborted
  · exact .inl rfl
  · refine .inr ⟨inbox, ?_⟩
    rw [← openResume_tail]
    rfl

end Opening

section Batch

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

/-- The program of party `i` at the start of batch `j`, for the caller `caller`. -/
def callerProgram (j : ℕ) (caller : Caller C) (i : C.Party) :
    PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)) :=
  treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
    (treeSimCheckBatchAudit K circuits settings ⟨i, x i, setupKeys setup i⟩
      ((lockstepChunks settings caller.encoding tree).getD j [])).run.run
      (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding tree) j, j) >>=
    callerCont K circuits settings top tree x setup j caller i

theorem boundary_program (j : ℕ) (p : TreeCheckWalkDef.Pending A) (caller : Caller C) (i : C.Party) :
    (TreeCheckWalkDef.boundary D K circuits settings x
      (p, callerBatch K D A circuits settings top tree x setup j caller)).program K circuits settings i =
      callerProgram K D circuits settings top tree x setup j caller i := rfl

/-- The caller of party `i` after one more batch with the result `a` and the
pending tail `tail`. -/
def stepCaller (caller : Caller C) (i : C.Party)
    (a : Option (List (List Bit)) × List (TreeSimCheckBatchRecord C))
    (tail : OracleComp (LocalSpec C) (Option Unit)) : Caller C :=
  { caller with
    outputs := fun _ => caller.outputs i ++ [a.1]
    records := fun _ => caller.records i ++ a.2
    tail := fun _ => tail }

omit [Fintype E] [DecidableEq E] in
theorem lockstepChunks_getD_first (encoding : Encoding) (k : ℕ)
    (first : k < (firstChunks settings tree).length) :
    (lockstepChunks settings encoding tree).getD k [] = (firstChunks settings tree).getD k [] := by
  cases tree with
  | top => rfl
  | bottom b =>
    simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs, List.getD_eq_getElem?_getD] at first ⊢
    rw [List.getElem?_append_left first]

omit [Fintype E] [DecidableEq E] in
theorem lockstepStart_first (parameter : PublicParameter) (encoding : Encoding) (k : ℕ)
    (first : k ≤ (firstChunks settings tree).length) :
    lockstepStart circuits parameter (lockstepChunks settings encoding tree) k =
      lockstepStart circuits parameter (firstChunks settings tree) k := by
  cases tree with
  | top => rfl
  | bottom b =>
    simp only [lockstepStart, lockstepChunks, firstChunks, treeLockstepFirstJobs] at first ⊢
    rw [List.take_append_of_le_length first]

omit [Fintype E] [DecidableEq E] in
/-- Inside the first run, the continuation of batch `j` runs batch `j + 1`
and then the continuation of the next caller. -/
theorem callerCont_step (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))
    (tail : OracleComp (LocalSpec C) (Option Unit)) :
    callerCont K circuits settings top tree x setup j caller i a =
      (treeSimCheckBatchAudit K circuits settings ⟨i, x i, setupKeys setup i⟩
        ((firstChunks settings tree).getD (j + 1) [])).run.run a.2 >>=
      callerCont K circuits settings top tree x setup (j + 1) (stepCaller caller i a.1 tail) i := by
  have current : j < (firstChunks settings tree).length := by omega
  have split : (firstChunks settings tree).drop (j + 1) =
      (firstChunks settings tree).getD (j + 1) [] :: (firstChunks settings tree).drop (j + 2) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem next, Option.getD_some]
    exact List.drop_eq_getElem_cons next
  unfold callerCont
  simp only [phaseChunks, phaseIndex, if_pos current, if_pos next, stepCaller]
  rw [split, auditChunks_cons]
  simp only [bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

/-- The real check of `tuples` makes exactly `checkLabels` exchanges, and only
pure work follows its last exchange. -/
theorem check_timed (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    TreeSimCheckTimed (checkLabels (tuples.map (·.count)).sum)
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run := by
  by_cases zero : (tuples.map (·.count)).sum = 0
  · rw [show checkLabels (tuples.map (·.count)).sum = 0 by simp [checkLabels, zero]]
    unfold check
    simp only [zero, if_true]
    exact .done _
  · have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by
      unfold halvings
      omega
    have timed := treeLockstep_check_timed K ctx tuples st zero
    rwa [show checkLabels (tuples.map (·.count)).sum =
      2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 5 by
        unfold checkLabels
        rw [if_neg zero]
        omega]

set_option maxHeartbeats 1000000 in
/-- Inside the first run, the residual of the program at the start of batch
`j` after the exchanges of that batch is an abort, or the program at the
start of batch `j + 1` for a caller with one more output and one more record.
The new tail is the rejecting local tail of the last opening. -/
theorem residual_batch (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      Q = (callerProgram K D circuits settings top tree x setup (j + 1) caller' i).run := by
  have current : j < (firstChunks settings tree).length := by omega
  unfold callerProgram at h
  rw [lockstepChunks_getD_first settings tree caller.encoding j current,
    lockstepStart_first circuits settings tree _ caller.encoding j current.le,
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
  rw [callerCont_step K circuits settings top tree x setup j next caller i _ (openTail K ctx.self
      (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length data.2.1.1 inbox)]
  set count := (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length
  set value := assemble (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs) fun g =>
    ∑ T, treeSimOpenCopy K ctx.self count data.2.1.1 inbox T g
  refine ⟨stepCaller caller i (some value, [⟨ctx, jobs, (start, j), data.1, data.2.1.2, data.2.2, value,
    checked.2⟩]) (openTail K ctx.self count data.2.1.1 inbox), rfl, by simp [stepCaller],
    by simp [stepCaller], ?_⟩
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  unfold callerProgram
  rw [lockstepChunks_getD_first settings tree _ (j + 1) next,
    lockstepStart_first circuits settings tree _ _ (j + 1) next.le]
  simp only [stepCaller, labels]

omit [Fintype E] [DecidableEq E] in
theorem callerProgram_abort (j : ℕ) (caller : Caller C) (i : C.Party) (rejects : caller.tail i = pure none) :
    (callerProgram K D circuits settings top tree x setup j caller i).run = pure none := by
  unfold callerProgram
  rw [rejects, localPrelude_none]
  rfl

/-- `residual_batch` with the abort written as a caller whose tail rejects. -/
theorem batch_step (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      Q = (callerProgram K D circuits settings top tree x setup (j + 1) caller' i).run := by
  rcases residual_batch K D circuits settings top tree x setup j next caller i same h with aborted | found
  · let record : TreeSimCheckBatchRecord C :=
      ⟨⟨i, x i, setupKeys setup i⟩, [], (0, 0), [], [], ⟨fun _ => [], 0, 0⟩, [], ⟨fun _ => [], 0, 0⟩⟩
    refine ⟨stepCaller caller i (none, [record]) (pure none), rfl, by simp [stepCaller],
      by simp [stepCaller], ?_⟩
    rw [aborted, callerProgram_abort K D circuits settings top tree x setup (j + 1) _ i rfl]
  · exact found

/-- The exchanges of the batches before batch `j`. -/
def batchStart (parameter : PublicParameter) (j : ℕ) : ℕ :=
  (((firstChunks settings tree).take j).map (batchRounds circuits settings.mode parameter)).sum

/-- Inside the first run, the residual of the first program after the batches
before batch `j` is the program at the start of batch `j` for some caller. -/
theorem residual_first (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter) :
    ∀ j, j < (firstChunks settings tree).length →
    ∀ {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))},
      Residual (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j)
        (callerProgram K D circuits settings top tree x setup 0 caller i).run Q →
      ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
        (caller'.records i).length = (caller.records i).length + j ∧
        (caller'.outputs i).length = (caller.outputs i).length + j ∧
        Q = (callerProgram K D circuits settings top tree x setup j caller' i).run
  | 0, _, Q, h => ⟨caller, rfl, rfl, rfl, h.zero_inv⟩
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
    obtain ⟨middle, encoding, records, outputs, rfl⟩ := residual_first caller i same j current first
    obtain ⟨final, encoding', records', outputs', rfl⟩ :=
      batch_step K D circuits settings top tree x setup j next middle i same second
    exact ⟨final, encoding'.trans encoding, by omega, by omega, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The program at batch `j` reads only the fields of party `i` and the
encoding. -/
theorem callerProgram_congr (j : ℕ) (caller caller' : Caller C) (i : C.Party)
    (encoding : caller.encoding = caller'.encoding)
    (firstOutputs : caller.firstOutputs i = caller'.firstOutputs i) (root : caller.root i = caller'.root i)
    (randomness : caller.randomness i = caller'.randomness i) (outputs : caller.outputs i = caller'.outputs i)
    (records : caller.records i = caller'.records i) (tail : caller.tail i = caller'.tail i) :
    callerProgram K D circuits settings top tree x setup j caller i =
      callerProgram K D circuits settings top tree x setup j caller' i := by
  obtain ⟨e, f, r, ρ, o, w, t⟩ := caller
  obtain ⟨e', f', r', ρ', o', w', t'⟩ := caller'
  dsimp only at encoding firstOutputs root randomness outputs records tail
  subst encoding
  unfold callerProgram callerCont phaseChunks
  simp only [firstOutputs, root, randomness, outputs, records, tail]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem batchRounds_le_maxBatch (parameter : PublicParameter) (jobs : List Job)
    (mem : jobs ∈ firstChunks settings tree) :
    batchRounds circuits settings.mode parameter jobs ≤ maxBatch circuits settings (runRounds settings.mode) := by
  have rounds : batchRounds circuits settings.mode parameter jobs ≤
      runRounds settings.mode (runCircuits circuits parameter jobs) := by
    unfold batchRounds runRounds runCircuits batchCount checkLabels
    split_ifs <;> omega
  refine rounds.trans ?_
  cases tree with
  | top =>
    exact measure_le_maxBatch circuits settings (runRounds settings.mode) parameter ⟨0, Nat.two_pow_pos _⟩
      (fun _ => digit 0) jobs (Or.inl mem)
  | bottom b =>
    exact measure_le_maxBatch circuits settings (runRounds settings.mode) parameter b (fun _ => digit 0) jobs
      (Or.inr (Or.inl mem))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem firstChunks_length_le : (firstChunks settings tree).length ≤ ceremonyBatches settings := by
  refine le_trans ?_ ((lockstepChunks_length settings (fun _ => digit 0) tree).le.trans
    (treeBatches_le_ceremonyBatches settings tree))
  cases tree with
  | top => exact le_rfl
  | bottom b =>
    simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs, List.length_append]
    omega

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The fuel after the batches before batch `j` holds the rounds of batch `j`. -/
theorem batchStart_room (parameter : PublicParameter) (j : ℕ) (first : j < (firstChunks settings tree).length) :
    batchStart circuits settings tree parameter j +
        batchRounds circuits settings.mode parameter ((firstChunks settings tree).getD j []) ≤
      ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) := by
  have succ : batchStart circuits settings tree parameter j +
      batchRounds circuits settings.mode parameter ((firstChunks settings tree).getD j []) =
      batchStart circuits settings tree parameter (j + 1) := by
    simp only [batchStart, List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem first, Option.toList_some, Option.getD_some, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  rw [succ]
  have bound := List.sum_le_card_nsmul
    (((firstChunks settings tree).take (j + 1)).map (batchRounds circuits settings.mode parameter))
    (maxBatch circuits settings (runRounds settings.mode)) (by
      intro rounds mapped
      obtain ⟨jobs, taken, rfl⟩ := List.mem_map.mp mapped
      exact batchRounds_le_maxBatch circuits settings tree parameter jobs (List.mem_of_mem_take taken))
  rw [List.length_map, smul_eq_mul] at bound
  have length : ((firstChunks settings tree).take (j + 1)).length ≤ ceremonyBatches settings := by
    rw [List.length_take]
    exact (min_le_right _ _).trans (firstChunks_length_le settings tree)
  exact bound.trans (Nat.mul_le_mul_right _ length)

end Batch

section Scheduler

variable {A : Adversary C E (Keys C) PEmpty PEmpty}
variable (prims : Primitives) (D : C.Coalition) (Z : Distinguisher C A.State TreeOutput)

/-- `Reached start n q` states that the scheduler reaches the pending state `q`
from `start` with `n` actual rounds of `next`. Each round uses one unit of
fuel. -/
inductive Reached (start : TreeCheckWalkDef.Pending A) : ℕ → TreeCheckWalkDef.Pending A → Prop
  | start : Reached start 0 start
  | next {n fuel : ℕ} {p q : TreeCheckWalkDef.Pending A} (reached : Reached start n p)
      (fuelLeft : p.fuel = fuel + 1) (run : .inl q ∈ support (TreeCheckWalkDef.next prims D Z fuel p)) :
      Reached start (n + 1) q

theorem Reached.fuel {start q : TreeCheckWalkDef.Pending A} {n : ℕ}
    (reached : Reached prims D Z start n q) : q.fuel + n = start.fuel := by
  induction reached with
  | start => rfl
  | next reached fuelLeft run ih =>
    rw [next_fuel prims D A Z _ _ _ run]
    omega

/-- One round of `next` adds one exchange to the residual of each honest
program. -/
theorem next_residual {fuel : ℕ} {p q : TreeCheckWalkDef.Pending A}
    (run : .inl q ∈ support (TreeCheckWalkDef.next prims D Z fuel p)) (i : C.Party) (hi : i ∉ D.1) :
    Residual 1 (p.program i).run (q.program i).run := by
  unfold TreeCheckWalkDef.next at run
  simp only [mem_support_bind_iff] at run
  obtain ⟨started, startRun, run⟩ := run
  split_ifs at run with stopped
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨observed, _, impossible⟩ := run
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
    obtain ⟨reply, _, rfl⟩ := run
    have steps := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ startRun) i
    simp only [if_neg hi, worldRoles] at steps
    have advanced := treeSimCheck_support_free _ steps
    have residual := Residual.of_advance (started.1 i) advanced
      (fun h => if h ∈ D.1 then reply.1.2 h i else (started.1 h).delivered i)
    convert residual using 1
    simp only [TreeCheckWalkDef.resume]
    cases started.1 i with
    | done out => rfl
    | wait out k => simp [hi, resumed]
    | call impossible k => exact impossible.elim

theorem Reached.residual {start q : TreeCheckWalkDef.Pending A} {n : ℕ}
    (reached : Reached prims D Z start n q) (i : C.Party) (hi : i ∉ D.1) :
    Residual n (start.program i).run (q.program i).run := by
  induction reached with
  | start => exact .refl _
  | next reached fuelLeft run ih => exact ih.trans (next_residual prims D Z run i hi)

end Scheduler

section State

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)

/-- The caller that collects the fields of party `i` from `callers i`. -/
def mergeCallers (callers : C.Party → Caller C) : Caller C where
  encoding := fun _ => digit 0
  firstOutputs := fun i => (callers i).firstOutputs i
  root := fun i => (callers i).root i
  randomness := fun i => (callers i).randomness i
  outputs := fun i => (callers i).outputs i
  records := fun i => (callers i).records i
  tail := fun i => (callers i).tail i

/-- The walk state of batch `j` inside the first run. At the state that the
scheduler reaches after the exchanges of the batches before `j`, each honest
program is the program of one caller at batch `j`, and this caller has the
lengths of batch `j`. A party that got an abort has a tail that rejects. -/
theorem walkState_first (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (j : ℕ) (first : j < (firstChunks settings tree).length)
    {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x setup)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) q) :
    ∃ caller : Caller C, CallerLengths D settings tree j caller ∧
      ∀ i, i ∉ D.1 → q.program i = callerProgram K D circuits settings top tree x setup.1.2 j caller i := by
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega :
    0 < (firstChunks settings tree).length))
  have same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    intro i
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  have each : ∀ i, ∃ caller' : Caller C, i ∉ D.1 → caller'.encoding = (fun _ => digit 0) ∧
      (caller'.records i).length = j ∧ (caller'.outputs i).length = j ∧
      q.program i = callerProgram K D circuits settings top tree x setup.1.2 j caller' i := by
    intro i
    by_cases hi : i ∈ D.1
    · exact ⟨firstCaller setup.1.2, fun h => (h hi).elim⟩
    have residual := reached.residual prims D Z i hi
    rw [initial_program K D A circuits settings top tree x setup head rest chunked i,
      boundary_program] at residual
    obtain ⟨caller', encoding, records, outputs, program⟩ :=
      residual_first K D circuits settings top tree x setup.1.2 _ i (same i) j first residual
    refine ⟨caller', fun _ => ⟨encoding, by simpa [firstCaller] using records,
      by simpa [firstCaller] using outputs, OptionT.ext program⟩⟩
  choose callers facts using each
  have encoding i hi := (facts i hi).1
  have records i hi := (facts i hi).2.1
  have outputs i hi := (facts i hi).2.2.1
  have program i hi := (facts i hi).2.2.2
  refine ⟨mergeCallers callers, fun i hi => ⟨records i hi, ?_⟩, fun i hi => ?_⟩
  · simp only [mergeCallers, phaseIndex, if_pos first]
    exact outputs i hi
  · rw [program i hi]
    exact callerProgram_congr K D circuits settings top tree x setup.1.2 j _ _ i (encoding i hi)
      rfl rfl rfl rfl rfl rfl

/-- At the walk state of batch `j` inside the first run, the decoder of batch
`j` recognizes the state: `Fits` holds for the merged caller. -/
theorem walkState_first_fits (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (j : ℕ) (first : j < (firstChunks settings tree).length)
    {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x setup)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) q) :
    ∃ caller : Caller C, Fits prims K D A circuits settings top tree x setup.1.2 j q caller := by
  obtain ⟨caller, lengths, program⟩ :=
    walkState_first prims K D A circuits settings top tree x Z setup dealt j first reached
  refine ⟨caller, lengths, ?_, ?_⟩
  · have fuel := reached.fuel
    have room := batchStart_room circuits settings tree (x (refHolder D K.publicTerm)).parameter j first
    change _ = ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) at fuel
    simp only [TreeCheckWalkDef.boundary, callerBatch, TreeCheckBatchBoundary.rounds,
      lockstepChunks_getD_first settings tree caller.encoding j first]
    unfold batchRounds at room
    omega
  · congr 1
    congr 1
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi, program i hi, boundary_program]

/-- The decoder of batch `j` recognizes the walk state of batch `j` inside the
first run. -/
theorem walkState_first_decode (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (j : ℕ) (first : j < (firstChunks settings tree).length)
    {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x setup)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) q) :
    (decode prims K D A circuits settings top tree x setup.1.2 j q).isSome := by
  obtain ⟨caller, fits⟩ :=
    walkState_first_fits prims K D A circuits settings top tree x Z setup dealt j first reached
  exact decode_hit prims K D A circuits settings top tree x setup.1.2 j q caller fits

omit [Fintype E] [DecidableEq E] in
/-- Away from the first signing batch, `prepare` changes no state. -/
theorem prepare_first (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (first : j ≠ (firstChunks settings tree).length) (p : TreeCheckWalkDef.Pending A) :
    prepare prims K D A circuits settings top tree x setup j p = pure p := by
  unfold prepare
  cases tree with
  | top => rfl
  | bottom b =>
    dsimp only
    rw [if_neg first]

/-- Away from the first signing batch, a finished outcome of the walk of batch
`j` comes from a state that the scheduler reaches before round `N`, when the
decoder recognizes each state at round `N`. At that state the fuel is zero, or
`next` stops because each honest step is done. -/
theorem walk_terminal_before (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (first : j ≠ (firstChunks settings tree).length) (start : TreeCheckWalkDef.Pending A) (N : ℕ)
    (hits : ∀ q, Reached prims D Z start N q →
      (decode prims K D A circuits settings top tree x setup j q).isSome) :
    ∀ (fuel n : ℕ) (p : TreeCheckWalkDef.Pending A), Reached prims D Z start n p → p.fuel = fuel → n ≤ N →
      ∀ r, .inr r ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p) →
        ∃ m q, m < N ∧ Reached prims D Z start m q ∧
          ((q.fuel = 0 ∧ r ∈ support (TreeCheckWalkDef.finish prims D Z q)) ∨
            ∃ fuel, q.fuel = fuel + 1 ∧ .inr r ∈ support (TreeCheckWalkDef.next prims D Z fuel q))
  | fuel, n, p, reached, fuelLeft, below, r, run => by
    have same : ({p with fuel := fuel} : TreeCheckWalkDef.Pending A) = p := by
      cases p
      simp_all
    have missed : ¬ (decode prims K D A circuits settings top tree x setup j p).isSome → n < N := by
      intro miss
      rcases Nat.lt_or_eq_of_le below with lt | eq
      · exact lt
      · exact (miss (hits p (eq ▸ reached))).elim
    cases fuel with
    | zero =>
      simp only [walk, prepare_first prims K D A circuits settings top tree x setup j first, same,
        pure_bind] at run
      split_ifs at run with hit
      · simp at run
      · simp only [support_map, Set.mem_image, Sum.inr.injEq] at run
        obtain ⟨r', hr, rfl⟩ := run
        exact ⟨n, p, missed hit, reached, .inl ⟨fuelLeft, hr⟩⟩
    | succ fuel =>
      simp only [walk, prepare_first prims K D A circuits settings top tree x setup j first, same,
        pure_bind] at run
      split_ifs at run with hit
      · simp at run
      · rw [mem_support_bind_iff] at run
        obtain ⟨outcome, nextRun, run⟩ := run
        cases outcome with
        | inr terminal =>
          simp only [mem_support_pure_iff, Sum.inr.injEq] at run
          subst run
          exact ⟨n, p, missed hit, reached, .inr ⟨fuel, fuelLeft, nextRun⟩⟩
        | inl pending =>
          have fuelNext := next_fuel prims D A Z fuel p pending nextRun
          exact walk_terminal_before setup j first start N hits fuel (n + 1) pending
            (.next reached fuelLeft nextRun) fuelNext (Nat.succ_le_of_lt (missed hit)) r run

/-- Away from the first signing batch, a decoded walk checkpoint is a state
that the scheduler reaches from the start. The decoder can hit before the walk
state of batch `j`, for example when every honest party has aborted. -/
theorem walk_hit_reached (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (first : j ≠ (firstChunks settings tree).length) (start : TreeCheckWalkDef.Pending A) :
    ∀ (fuel n : ℕ) (p : TreeCheckWalkDef.Pending A), Reached prims D Z start n p → p.fuel = fuel →
      ∀ c, .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p) →
        ∃ m, n ≤ m ∧ Reached prims D Z start m c.1.1
  | fuel, n, p, reached, fuelLeft, c, run => by
    have same : ({p with fuel := fuel} : TreeCheckWalkDef.Pending A) = p := by
      cases p
      simp_all
    cases fuel with
    | zero =>
      simp only [walk, prepare_first prims K D A circuits settings top tree x setup j first, same,
        pure_bind] at run
      split_ifs at run with hit
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        subst run
        exact ⟨n, le_rfl, reached⟩
      · simp only [support_map, Set.mem_image] at run
        obtain ⟨_, _, impossible⟩ := run
        cases impossible
    | succ fuel =>
      simp only [walk, prepare_first prims K D A circuits settings top tree x setup j first, same,
        pure_bind] at run
      split_ifs at run with hit
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        subst run
        exact ⟨n, le_rfl, reached⟩
      · rw [mem_support_bind_iff] at run
        obtain ⟨outcome, nextRun, run⟩ := run
        cases outcome with
        | inr terminal => simp only [mem_support_pure_iff] at run; cases run
        | inl pending =>
          obtain ⟨m, below, later⟩ := walk_hit_reached setup j first start fuel (n + 1) pending
            (.next reached fuelLeft nextRun) (next_fuel prims D A Z fuel p pending nextRun) c run
          exact ⟨m, by omega, later⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
/-- A finished outcome of the walk of batch `j` inside the first run comes from
a state that the scheduler reaches before the walk state of batch `j`, where
`next` stops because each honest step is done. -/
theorem walk_terminal_first (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (j : ℕ) (first : j < (firstChunks settings tree).length)
    (r : TreeCheckTailResult A)
    (run : .inr r ∈ support (walk prims K D A circuits settings top tree x setup.1.2 j Z
      (TreeCheckWalkDef.initial K circuits settings top tree x setup).fuel
      (TreeCheckWalkDef.initial K circuits settings top tree x setup))) :
    ∃ m q, m < batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j ∧
      Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x setup) m q ∧
      ∃ fuel, q.fuel = fuel + 1 ∧ .inr r ∈ support (TreeCheckWalkDef.next prims D Z fuel q) := by
  have hits : ∀ q, Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x setup)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) q →
      (decode prims K D A circuits settings top tree x setup.1.2 j q).isSome := fun q reached =>
    walkState_first_decode prims K D A circuits settings top tree x Z setup dealt j first reached
  have bridge := walk_terminal_before prims K D A circuits settings top tree x Z setup.1.2 j (Nat.ne_of_lt first)
    (TreeCheckWalkDef.initial K circuits settings top tree x setup)
    (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) hits
    (TreeCheckWalkDef.initial K circuits settings top tree x setup).fuel 0
    (TreeCheckWalkDef.initial K circuits settings top tree x setup) .start rfl (Nat.zero_le _) r
  obtain ⟨m, q, below, reached, stop⟩ := by with_reducible exact bridge run
  refine ⟨m, q, below, reached, ?_⟩
  rcases stop with ⟨empty, -⟩ | stop
  · have fuel := reached.fuel
    have room := batchStart_room circuits settings tree (x (refHolder D K.publicTerm)).parameter j first
    change _ = ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) at fuel
    omega
  · exact stop

end State

section Assembly

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The walk-state invariant of the fixed family inside the first run. The
state that the scheduler reaches from the start of the family after the
exchanges of the batches before `j` fits a caller of batch `j`. -/
def WalkStateFirst : Prop :=
  AtWalk prims K circuits settings fun top tree D A x _ Z _ _ j p _ =>
    j.val < (firstChunks settings tree).length →
      ∀ q, Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x p)
          (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j.val) q →
        ∃ caller, Fits prims K D A circuits settings top tree x p.1.2 j.val q caller

theorem walkStateFirst : WalkStateFirst prims K circuits settings := by
  intro _ top tree D A x z Z q dealt bounded _ j p _ first state reached
  exact walkState_first_fits prims K D A circuits settings top tree x Z p dealt j.val first reached

/-- The exchanges of the batches of the signing run before batch `j`, for the
encoding `encoding`. -/
def signRounds (parameter : PublicParameter) (encoding : Encoding) (tree : Tree) (j : ℕ) : ℕ :=
  ((((lockstepChunks settings encoding tree).take j).drop (firstChunks settings tree).length).map
    (batchRounds circuits settings.mode parameter)).sum

/-- The program part of the walk state inside the signing run of a bottom tree,
for one party and one fixed encoding. It is the form of `residual_first` for
the batches after the first run. -/
def WalkStateSigning : Prop :=
  ∀ (D : C.Coalition) (top : TopTree) (b : Fin (2 ^ layerHeight)) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (caller : Caller C) (i : C.Party),
    (x i).parameter = (x (refHolder D K.publicTerm)).parameter →
    ∀ j, (firstChunks settings (.bottom b)).length ≤ j → j < treeBatches settings (.bottom b) →
    ∀ Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C))),
      Residual (signRounds circuits settings (x (refHolder D K.publicTerm)).parameter caller.encoding
          (.bottom b) j)
        (callerProgram K D circuits settings top (.bottom b) x setup
          (firstChunks settings (.bottom b)).length caller i).run Q →
      ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
        (caller'.records i).length + (firstChunks settings (.bottom b)).length =
          (caller.records i).length + j ∧
        (caller'.outputs i).length + (firstChunks settings (.bottom b)).length =
          (caller.outputs i).length + j ∧
        Q = (callerProgram K D circuits settings top (.bottom b) x setup j caller' i).run

/-- The walk state at the end of the first run of a bottom tree matches a
signing point. -/
def WalkStateEntry : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput),
      DealtInputs D x →
      ∀ p ∈ support (treeSaltSetup prims D A x z),
      ∀ q, Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
          (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings (.bottom b)).length) q →
        ∃ point, SigningMatches K D A circuits settings top x p.1.2
          (firstChunks settings (.bottom b)).length b q point

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.Residual.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Residual.split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.Residual.timed_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Residual.timed_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.residual_openRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_openRep

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.residual_batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_batch

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.residual_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_first

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.Reached.residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reached.residual

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.walkState_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkState_first

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.walkState_first_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkState_first_fits

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.walkState_first_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkState_first_decode

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.walk_terminal_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_terminal_first

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.walk_hit_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_hit_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkState.walkStateFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkStateFirst

end TreeCheckWalkState
end ThresholdLeanXmssSecurity
