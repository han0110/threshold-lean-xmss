import ThresholdLeanXmssSecurity.Proof.TreeCheckCountedCut

/-!
# The parts of the counted cut at batch `j`

This module works on `TreeCheckCountedCutParts` (`TreeCheckCountedCut`). It cuts the audited logged
run in three stages.

* `treeCheckSetup_split` cuts the run after the PRSS setup. The prefix is `treeSaltSetup`, and the
  rest is `treeCheckAfterSetup`. It lifts `treeSimCheck_audit_setup_split` to the logged run.
* A `TreeCheckBatchWalk` goes from a setup state to the start of the prefix of batch `j`. Each of
  its states is a `TreeCheckBatchBoundary`, where all honest operators run the same jobs from the
  same counters, or a finished run.
* `treeCheckBatch_split` cuts the run from a boundary at the start of the check of the batch. It
  lifts `treeSimCheckBatchAudit_phase_split` to the logged run.

The cut of `TreeCheckCountedCutParts` is `TreeCheckCountedCutData.ofSetup`. After each setup state
it takes the cut of a walk (`TreeCheckBatchWalk.cut`). Its state at a boundary holds the adversary
state, the prefix output of each operator, both caches and the log. The boundary holds the rest of
each audited ceremony and the fuel that is left.

The local implications are:

* `Split` for the setup stage and for the batch stage.
* For `Inputs`, `treeCheckBatch_live` and `treeCheckBatch_counts` (review P2). An honest acceptance
  after the cut makes every honest prefix output present, also for an operator that aborts after
  the prefix. So all honest operators hold tuples with one count list.
  `TreeCheckBatchWalk.inputs_counts` gives the first two clauses of `TupleInputs` and the count
  equation, and `TreeCheckBatchWalk.inputs` gives `Inputs` from `Unreached` and `Consistent`.

`treeCheckCountedCutParts_of_walk` proves `TreeCheckCountedCutParts` from
`TreeCheckBatchWalkParts`. It has the following global walk requirements.

* The walk `Split`. All honest operators that reach batch `j` must run the same jobs from the
  same counters, and the walk must keep each operator identity.
* `Unreached`. A run that ends before the boundary of batch `j` has no counted bad event. This is
  the other half of review P2. An operator that aborts later must have run the jobs of the
  boundary.
* `Consistent`, the third clause of `TupleInputs`.
* `Jobs`, `Queries`, `Cache`, `Prior`, `Reject`, `Budget` and `Transport` on the cut of the walk.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The audited logged run after the PRSS setup, with the batches and the distinguisher. -/
def treeCheckAfterSetup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    ProbComp ((Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C) := do
  let next ← (simulateQ (treeSimLoggedWorld prims D)
    (free (Concrete.sequenceFin fun i => continueStep
      (fun prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
      (.done (p.1.2 i))))).run p.2
  let out ← (simulateQ (treeSimLoggedWorld prims D)
    (executeRounds worldRoles D A noFunctionality
      (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode))
      p.1.1 next.1)).run next.2
  let b ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (Z (out.1.1, fun i => (out.1.2 i).map Prod.fst)))).run out.2
  pure ((b.1, out.1), b.2.2)

/-- The audited logged run is the PRSS setup followed by the rest of the run. -/
theorem treeCheckSetup_split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z) =
      treeSaltSetup prims D A x z >>=
        treeCheckAfterSetup prims K circuits settings top tree D A x Z := by
  rw [treeSimLoggedRun_eq_run]
  unfold treeSimCheckAuditedGame realExecution treeSaltSetup treeCheckAfterSetup
  simp only [treeSimCheck_audit_setup_split K circuits settings top tree D A x]
  simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_assoc, simulateQ_pure,
    StateT.run_pure, map_pure, simulateQ_executePhase, treeSimRealRoles]

/-- A state of the audited run at the start of the prefix of one batch, in the form of
`treeSimCheckBatchAudit_phase_split`. All honest operators run the same jobs from the same
counters, and `k` is the rest of each audited ceremony. -/
structure TreeCheckBatchBoundary (A : Adversary C E (Keys C) PEmpty PEmpty) where
  state : A.State
  ctx : C.Party → Context C
  parameter : PublicParameter
  jobs : List Job
  initial : ℕ × ℕ
  k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C))
  fuel : ℕ
  world : TreeSimState C

/-- The rounds of the prefix of the batch. -/
def TreeCheckBatchBoundary.rounds {A : Adversary C E (Keys C) PEmpty PEmpty}
    (b : TreeCheckBatchBoundary A) : ℕ :=
  depth (b.jobs.map (circuits b.parameter ·.kind)) * settings.mode.rounds + 1

/-- The final observation of the logged run. -/
def treeCheckObserve (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput)
    (out : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) ×
      TreeSimState C) :
    ProbComp ((Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C) := do
  let b ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (Z (out.1.1, fun i => (out.1.2 i).map Prod.fst)))).run out.2
  pure ((b.1, out.1), b.2.2)

/-- The logged run from a batch boundary to the end. -/
def treeCheckBatchRun (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A) :
    ProbComp ((Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C) := do
  let out ← (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (b.rounds circuits settings + b.fuel) b.state
      (fun i => (treeSimCheckBatchAudit K circuits settings (b.ctx i) b.jobs).run.run b.initial >>=
        b.k i))).run b.world
  treeCheckObserve prims D A Z out

/-- The logged prefix of the batch, up to the start of its check. -/
def treeCheckBatchPre (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckBatchBoundary A) :
    ProbComp ((A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C) :=
  (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (b.rounds circuits settings) b.state
      (fun i => treeSimCheckBatchPrefix K circuits settings (b.ctx i) b.jobs b.initial))).run b.world

/-- The logged run from the start of the check of the batch to the end. -/
def treeCheckBatchCont (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A)
    (o : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C) :
    ProbComp ((Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C) := do
  let next ← (simulateQ (treeSimLoggedWorld prims D)
    (free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))))).run o.2
  let out ← (simulateQ (treeSimLoggedWorld prims D)
    (executeRounds worldRoles D A noFunctionality b.fuel o.1.1 next.1)).run next.2
  treeCheckObserve prims D A Z out

/-- The logged run from a batch boundary is the prefix of the batch, then the rest from the start
of its check. -/
theorem treeCheckBatch_split (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A)
    (hparameter : ∀ i, (b.ctx i).keys.parameter = b.parameter) :
    treeCheckBatchRun prims K circuits settings D A Z b =
      treeCheckBatchPre prims K circuits settings D A b >>=
        treeCheckBatchCont prims K circuits D A Z b := by
  unfold treeCheckBatchRun treeCheckBatchPre treeCheckBatchCont TreeCheckBatchBoundary.rounds
  rw [treeSimCheckBatchAudit_phase_split K circuits settings D A b.fuel b.state b.ctx b.parameter
    hparameter b.jobs b.initial b.k]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]

theorem treeCheck_logged_support {α : Type} (D : C.Coalition) (oa : OracleComp (WorldSpec C) α)
    (w : TreeSimState C) {o : α × TreeSimState C}
    (h : o ∈ support ((simulateQ (treeSimLoggedWorld prims D) oa).run w)) : o.1 ∈ support oa := by
  apply support_simulateQ_run'_subset (treeSimLoggedWorld prims D) oa w
  rw [StateT.run'_eq, support_map]
  exact ⟨o, h, rfl⟩

/-- An honest acceptance after the start of the check makes every honest prefix output of the
batch present, also for an operator that aborts after the prefix (review P2). -/
theorem treeCheckBatch_live (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A)
    (o : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (r : (Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
    (hr : r ∈ support (treeCheckBatchCont prims K circuits D A Z b o))
    (accepted : ∃ i value, r.1.2.2 i = some value) :
    ∀ i, i ∉ D.1 → (o.1.2 i).isSome := by
  unfold treeCheckBatchCont treeCheckObserve at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨next, hnext, out, hout, z', -, rfl⟩ := hr
  refine treeSimCheck_exchange_continuations_live D A b.fuel o.1.1 o.1.2
    (fun i p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
    (fun i p => ?_) next.1 (treeCheck_logged_support prims D _ _ hnext) out.1
    (treeCheck_logged_support prims D _ _ hout) accepted
  unfold treeSimCheckBatchFinish
  rw [bind_assoc]
  exact (treeSimCheckAfterVerify_exchange K (b.ctx i) _ p.2).bind _

/-- The count list of the batch. -/
def TreeCheckBatchBoundary.counts {A : Adversary C E (Keys C) PEmpty PEmpty}
    (b : TreeCheckBatchBoundary A) : List ℕ :=
  let js := b.jobs.map (circuits b.parameter ·.kind)
  (List.range (depth js)).map (fun l => (gatesAt js l).length) ++ [(outputsOf js).length]

/-- At the start of the check after an honest acceptance, every honest operator holds tuples with
the one count list of the batch, also an operator that aborts after the prefix (review P2). -/
theorem treeCheckBatch_counts (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A)
    (self : ∀ i, (b.ctx i).self = i) (hparameter : ∀ i, (b.ctx i).keys.parameter = b.parameter)
    (o : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (ho : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (r : (Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
    (hr : r ∈ support (treeCheckBatchCont prims K circuits D A Z b o))
    (accepted : ∃ i value, r.1.2.2 i = some value) :
    ∀ i, i ∉ D.1 → ∃ data, o.1.2 i = some data ∧
      data.2.2.history = filledHistory K i data.2.1.2 ∧
      data.2.2.label = b.initial.1 + depth (b.jobs.map (circuits b.parameter ·.kind)) + 1 ∧
      data.2.2.tag = b.initial.2 ∧
      data.2.1.2.map (·.count) = b.counts circuits ∧
      data.2.1.2.map (·.mode) = (List.range (depth (b.jobs.map (circuits b.parameter ·.kind)))).map
        (fun _ => settings.mode) ++ [.peer] := by
  have live := treeCheckBatch_live prims K circuits D A Z b o r hr accepted
  obtain ⟨log, hlog⟩ := treeSimCheckReplay_of_support _ _
    (treeCheck_logged_support prims D _ _ ho)
  exact treeSimCheckBatchPrefix_joint K circuits settings D A _ b.state b.ctx self b.parameter
    hparameter b.jobs b.initial log o.1 hlog live

/-- A cut of the audited run after the setup state `p` at the start of the check of batch `j`,
with all its parts. The parts are the parts of `TreeCheckCountedCutParts`, and `Split` is on
`treeCheckAfterSetup`. -/
def TreeCheckAfterSetupCutAt (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (cut : TreeCheckCountedCutData A) : Prop :=
  treeCheckAfterSetup prims K circuits settings top tree D A x Z p = cut.pre >>= cut.cont ∧
    cut.Jobs prims K circuits settings top tree D A x z j ∧
    cut.Inputs prims K circuits settings top tree D A x z j ∧
    cut.Queries prims K circuits settings top tree D A x z j ∧
    cut.Cache prims K circuits settings top tree D A x z j ∧
    cut.Prior prims K circuits settings top tree D A x z j ∧
    cut.Reject prims K circuits settings top tree D A x z j ∧
    cut.Budget prims K circuits settings top tree D A x z q j ∧
    cut.Transport prims K circuits settings top tree D A x z j

/-- After each reachable setup state, a cut at the check of each batch exists with all its
parts. -/
def TreeCheckAfterSetupCutParts : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ cut : TreeCheckCountedCutData A,
          TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p cut

/-- A hybrid check with no tuples, for the cut states that are never live. -/
def treeCheckDummyHybrid : TreeCheckHybrid C E :=
  { counts := []
    adversary := ⟨Unit, fun _ _ => pure (), fun _ _ => pure ((), fun _ _ => none),
      fun _ _ => pure ((), .inl (.inl ∅))⟩
    tuples := fun _ => []
    step := 0
    state := ()
    tag := 0
    label := 0
    cache := ∅
    seen := ∅
    keys := ∅ }

/-- The walk of the audited run after a setup state up to the start of the prefix of batch `j`.
A state of `pre` is either a batch boundary or a finished run that never reaches the boundary.
`hybrid` names the hybrid check at each state at the start of the check. -/
structure TreeCheckBatchWalk (A : Adversary C E (Keys C) PEmpty PEmpty) where
  β : Type
  pre : ProbComp (β ⊕ ((Bool × (A.State ×
    (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C))
  boundary : β → TreeCheckBatchBoundary A
  hybrid : β → (A.State × (C.Party → Option
    (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C →
    TreeCheckHybrid C E

namespace TreeCheckBatchWalk

variable {prims K circuits settings}
variable {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}

variable (prims K circuits settings D) in
/-- The cut of a walk at the start of the check of the batch. Its count is the tuple count of the
jobs of the boundary. -/
def cut (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckBatchWalk A) :
    TreeCheckCountedCutData (C := C) (E := E) A where
  σ := (W.β × (A.State × (C.Party → Option
    (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C) ⊕
    ((Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
  pre := W.pre >>= fun e => match e with
    | .inl c => (fun o => .inl (c, o)) <$> treeCheckBatchPre prims K circuits settings D A (W.boundary c)
    | .inr r => pure (.inr r)
  cont := fun s => match s with
    | .inl (c, o) => treeCheckBatchCont prims K circuits D A Z (W.boundary c) o
    | .inr r => pure r
  count := fun s => match s with
    | .inl (c, _) => tupleCount ((W.boundary c).jobs.map (circuits (W.boundary c).parameter ·.kind))
    | .inr _ => 0
  hybrid := fun s => match s with
    | .inl (c, o) => W.hybrid c o
    | .inr _ => treeCheckDummyHybrid

variable (prims K circuits settings D) in
/-- The walk splits the run after the setup state `p`, and the operators at each boundary share
one public parameter. -/
def Split (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckBatchWalk A)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) : Prop :=
  treeCheckAfterSetup prims K circuits settings top tree D A x Z p = (W.pre >>= fun e => match e with
    | .inl c => treeCheckBatchRun prims K circuits settings D A Z (W.boundary c)
    | .inr r => pure r) ∧
  ∀ c i, ((W.boundary c).ctx i).keys.parameter = (W.boundary c).parameter

theorem cut_split {top : TopTree} {tree : Tree} {x : C.Party → Keys C}
    {Z : Distinguisher C A.State TreeOutput} {W : TreeCheckBatchWalk A}
    {p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C}
    (h : W.Split prims K circuits settings D top tree x Z p) :
    treeCheckAfterSetup prims K circuits settings top tree D A x Z p =
      (W.cut prims K circuits settings D Z).pre >>= (W.cut prims K circuits settings D Z).cont := by
  rw [h.1]
  unfold cut
  simp only [bind_assoc]
  refine bind_congr fun e => ?_
  cases e with
  | inl c =>
    simp only [bind_map_left]
    exact treeCheckBatch_split prims K circuits settings D A Z (W.boundary c) (h.2 c)
  | inr r => simp only [pure_bind]

theorem mem_support_cut_pre {Z : Distinguisher C A.State TreeOutput} {W : TreeCheckBatchWalk A}
    {c : W.β} {o : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C}
    (h : (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre) :
    o ∈ support (treeCheckBatchPre prims K circuits settings D A (W.boundary c)) := by
  unfold cut at h
  rw [mem_support_bind_iff] at h
  obtain ⟨e, -, h⟩ := h
  cases e with
  | inl c' =>
    rw [support_map] at h
    obtain ⟨o', ho', he⟩ := h
    cases he
    exact ho'
  | inr r => simp at h

theorem counts_sum (b : TreeCheckBatchBoundary A) :
    (b.counts circuits).sum = tupleCount (b.jobs.map (circuits b.parameter ·.kind)) := by
  unfold TreeCheckBatchBoundary.counts
  simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact (tupleCount_eq _).symm

variable (prims K circuits settings D) in
/-- The hybrid check at the start of the check of a boundary takes the count list of the batch and
the honest tuples of the prefix. -/
def StandardTuples (W : TreeCheckBatchWalk A) : Prop :=
  ∀ c o, (W.hybrid c o).counts = (W.boundary c).counts circuits ∧
    ∀ i, i ∉ D.1 → (W.hybrid c o).tuples i = ((o.1.2 i).map (·.2.1.2)).getD []

/-- At a live boundary state with standard tuples, the honest tuples have the count list of the
batch and one mode list, and the count list sums to the tuple count of the cut. These
are the first two clauses of `TupleInputs` and the count equation of `Inputs`. -/
theorem inputs_counts {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckBatchWalk A}
    (hstandard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).ctx i).self = i)
    (hparameter : ∀ c i, ((W.boundary c).ctx i).keys.parameter = (W.boundary c).parameter)
    (c : W.β) (o : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (hs : (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre)
    (hlive : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o))) :
    (∀ i, i ∉ D.1 → ((W.hybrid c o).tuples i).map (·.count) = (W.hybrid c o).counts) ∧
      (∀ i k, i ∉ D.1 → k ∉ D.1 →
        ((W.hybrid c o).tuples i).map (·.mode) = ((W.hybrid c o).tuples k).map (·.mode)) ∧
      (W.hybrid c o).counts.sum = (W.cut prims K circuits settings D Z).count (.inl (c, o)) := by
  obtain ⟨r, hr, hbad, -⟩ := hlive
  obtain ⟨-, -, -, -, i, value, records, -, -, -, -, -, -, hout, -⟩ := hbad.2
  have hdata := treeCheckBatch_counts prims K circuits settings D A Z (W.boundary c) (self c)
    (hparameter c) o (mem_support_cut_pre hs) r hr ⟨i, (value, records), hout⟩
  obtain ⟨hcounts, htuples⟩ := hstandard c o
  refine ⟨fun i hi => ?_, fun i k hi hk => ?_, ?_⟩
  · obtain ⟨data, hd, -, -, -, hc, -⟩ := hdata i hi
    rw [htuples i hi, hd, hcounts]
    exact hc
  · obtain ⟨data, hd, -, -, -, -, hm⟩ := hdata i hi
    obtain ⟨data', hd', -, -, -, -, hm'⟩ := hdata k hk
    rw [htuples i hi, htuples k hk, hd, hd']
    exact hm.trans hm'.symm
  · rw [hcounts, counts_sum]
    rfl

theorem mem_support_cut_pre_inr {Z : Distinguisher C A.State TreeOutput} {W : TreeCheckBatchWalk A}
    {r : (Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C}
    (h : (.inr r : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre) :
    .inr r ∈ support W.pre := by
  unfold cut at h
  rw [mem_support_bind_iff] at h
  obtain ⟨e, he, h⟩ := h
  cases e with
  | inl c' =>
    rw [support_map] at h
    obtain ⟨o', -, he'⟩ := h
    cases he'
  | inr r' =>
    simp only [support_pure, Set.mem_singleton_iff, Sum.inr.injEq] at h
    cases h
    exact he

variable (prims K circuits settings D) in
/-- A run that never reaches the boundary of batch `j` has no counted bad event of the batch. So an
operator that aborts later ran the jobs of the boundary at batch `j`. -/
def Unreached (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree)) (W : TreeCheckBatchWalk A) : Prop :=
  ∀ r, .inr r ∈ support W.pre →
    ¬ (TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧ ¬ TreeCheckUncounted D r.2)

variable (prims K circuits settings D) in
/-- At a live boundary state, the first two clauses of `TupleInputs` give the third. -/
def Consistent (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckBatchWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)) →
    (∀ i, i ∉ D.1 → ((W.hybrid c o).tuples i).map (·.count) = (W.hybrid c o).counts) →
    (∀ i k, i ∉ D.1 → k ∉ D.1 →
      ((W.hybrid c o).tuples i).map (·.mode) = ((W.hybrid c o).tuples k).map (·.mode)) →
    TupleInputs K (W.hybrid c o).counts D (W.hybrid c o).tuples

/-- `Inputs` on the cut of a walk, from the standard tuples, the unreached runs and the third
clause of `TupleInputs`. -/
theorem inputs {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckBatchWalk A}
    (hstandard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).ctx i).self = i)
    (hparameter : ∀ c i, ((W.boundary c).ctx i).keys.parameter = (W.boundary c).parameter)
    (hunreached : W.Unreached prims K circuits settings D top tree x z j)
    (hconsistent : W.Consistent prims K circuits settings D top tree x z Z j) :
    (W.cut prims K circuits settings D Z).Inputs prims K circuits settings top tree D A x z j := by
  rintro (⟨c, o⟩ | r) hs hlive
  · obtain ⟨h1, h2, hsum⟩ := inputs_counts hstandard self hparameter c o
      hs hlive
    exact ⟨hconsistent c o hs hlive h1 h2, hsum⟩
  · exfalso
    obtain ⟨r', hr', hbad, hunc⟩ := hlive
    have he : r' = r := by simpa [cut] using hr'
    subst he
    exact hunreached r' (mem_support_cut_pre_inr hs) ⟨hbad, hunc⟩

end TreeCheckBatchWalk

namespace TreeCheckCountedCutData

variable {prims K circuits settings}
variable {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
  {x : C.Party → Keys C} {z : Aux} {Z : Distinguisher C A.State TreeOutput} {q : ℕ}
  {j : Fin (treeBatches settings tree)}

/-- The cut with no prefix. Its state is the start of `cont`. -/
def trivial (run : ProbComp ((Bool × (A.State ×
    (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)) :
    TreeCheckCountedCutData (C := C) (E := E) A where
  σ := Unit
  pre := pure ()
  cont := fun _ => run
  count := fun _ => 0
  hybrid := fun _ => treeCheckDummyHybrid

variable (prims K circuits settings top tree D A x z Z q j)

/-- The chosen cut after the setup state `p`. It is a cut with all its parts if one exists, else
the trivial cut. Both split the run after `p`. -/
def afterSetup (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    TreeCheckCountedCutData (C := C) (E := E) A :=
  if h : ∃ cut, TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p cut
  then h.choose
  else trivial (treeCheckAfterSetup prims K circuits settings top tree D A x Z p)

/-- The setup cut followed by the chosen cut after each setup state. -/
def ofSetup : TreeCheckCountedCutData (C := C) (E := E) A where
  σ := Σ p, (afterSetup prims K circuits settings top tree D A x z Z q j p).σ
  pre := treeSaltSetup prims D A x z >>= fun p =>
    (fun s => (⟨p, s⟩ : Σ p, (afterSetup prims K circuits settings top tree D A x z Z q j p).σ)) <$>
      (afterSetup prims K circuits settings top tree D A x z Z q j p).pre
  cont := fun s => (afterSetup prims K circuits settings top tree D A x z Z q j s.1).cont s.2
  count := fun s => (afterSetup prims K circuits settings top tree D A x z Z q j s.1).count s.2
  hybrid := fun s => (afterSetup prims K circuits settings top tree D A x z Z q j s.1).hybrid s.2

theorem afterSetup_split (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    treeCheckAfterSetup prims K circuits settings top tree D A x Z p =
      (afterSetup prims K circuits settings top tree D A x z Z q j p).pre >>=
        (afterSetup prims K circuits settings top tree D A x z Z q j p).cont := by
  unfold afterSetup
  by_cases h : ∃ cut, TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p cut
  · rw [dif_pos h]
    exact h.choose_spec.1
  · rw [dif_neg h]
    exact (pure_bind _ _).symm

theorem afterSetup_spec (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (h : ∃ cut, TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p cut) :
    TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p
      (afterSetup prims K circuits settings top tree D A x z Z q j p) := by
  unfold afterSetup
  rw [dif_pos h]
  exact h.choose_spec

theorem ofSetup_split :
    (ofSetup prims K circuits settings top tree D A x z Z q j).Split
      prims K circuits settings top tree D A x z Z := by
  unfold Split ofSetup
  rw [treeCheckSetup_split]
  simp only [bind_assoc, bind_map_left]
  refine bind_congr fun p => ?_
  exact afterSetup_split prims K circuits settings top tree D A x z Z q j p

theorem mem_support_ofSetup
    {p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C}
    {s : (afterSetup prims K circuits settings top tree D A x z Z q j p).σ}
    (hs : (⟨p, s⟩ : Σ p, (afterSetup prims K circuits settings top tree D A x z Z q j p).σ) ∈
      support (treeSaltSetup prims D A x z >>= fun p =>
        (fun s => (⟨p, s⟩ : Σ p, (afterSetup prims K circuits settings top tree D A x z Z q j p).σ)) <$>
          (afterSetup prims K circuits settings top tree D A x z Z q j p).pre)) :
    p ∈ support (treeSaltSetup prims D A x z) ∧
      s ∈ support (afterSetup prims K circuits settings top tree D A x z Z q j p).pre := by
  rw [mem_support_bind_iff] at hs
  obtain ⟨p', hp', hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨s', hs', h⟩ := hs
  cases h
  exact ⟨hp', hs'⟩

end TreeCheckCountedCutData

/-- `TreeCheckCountedCutParts` from a cut after each reachable setup state. The cut is the setup
cut followed by the chosen cut after the setup state. -/
theorem treeCheckCountedCutParts_of_afterSetup
    (parts : TreeCheckAfterSetupCutParts prims K circuits settings) :
    TreeCheckCountedCutParts prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j
  have spec : ∀ p ∈ support (treeSaltSetup prims D A x z),
      TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p
        (TreeCheckCountedCutData.afterSetup prims K circuits settings top tree D A x z Z q j p) :=
    fun p hp => TreeCheckCountedCutData.afterSetup_spec prims K circuits settings top tree D A x z
      Z q j p (parts hbatch top tree D A x z Z q hx hq hsmall j p hp)
  have mem := fun {p} {s} hs =>
    TreeCheckCountedCutData.mem_support_ofSetup prims K circuits settings top tree D A x z Z q j
      (p := p) (s := s) hs
  refine ⟨TreeCheckCountedCutData.ofSetup prims K circuits settings top tree D A x z Z q j,
    TreeCheckCountedCutData.ofSetup_split prims K circuits settings top tree D A x z Z q j,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.2.2.1 s (mem hs).2
  · rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.2.2.2 s (mem hs).2

/-- After each reachable setup state, a walk to the start of the prefix of batch `j` exists, and
its cut has all parts. The walk splits the run (`TreeCheckBatchWalk.Split`), its hybrid checks
take the standard tuples, and each boundary keeps the identity of each operator. `Inputs` comes
from `Unreached` and `Consistent` by `TreeCheckBatchWalk.inputs`. -/
def TreeCheckBatchWalkParts : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ W : TreeCheckBatchWalk A,
          W.Split prims K circuits settings D top tree x Z p ∧
          W.StandardTuples circuits D ∧
          (∀ c i, ((W.boundary c).ctx i).self = i) ∧
          (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j ∧
          W.Unreached prims K circuits settings D top tree x z j ∧
          W.Consistent prims K circuits settings D top tree x z Z j ∧
          (W.cut prims K circuits settings D Z).Queries prims K circuits settings top tree D A x z j ∧
          (W.cut prims K circuits settings D Z).Cache prims K circuits settings top tree D A x z j ∧
          (W.cut prims K circuits settings D Z).Prior prims K circuits settings top tree D A x z j ∧
          (W.cut prims K circuits settings D Z).Reject prims K circuits settings top tree D A x z j ∧
          (W.cut prims K circuits settings D Z).Budget prims K circuits settings top tree D A x z q j ∧
          (W.cut prims K circuits settings D Z).Transport prims K circuits settings top tree D A x z j

theorem treeCheckAfterSetupCutParts_of_walk
    (walk : TreeCheckBatchWalkParts prims K circuits settings) :
    TreeCheckAfterSetupCutParts prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j p hp
  obtain ⟨W, hsplit, hstandard, self, hjobs, hunreached, hconsistent, hqueries, hcache, hprior,
    hreject, hbudget, htransport⟩ := walk hbatch top tree D A x z Z q hx hq hsmall j p hp
  exact ⟨_, TreeCheckBatchWalk.cut_split hsplit, hjobs,
    TreeCheckBatchWalk.inputs hstandard self hsplit.2 hunreached
      hconsistent, hqueries, hcache, hprior, hreject, hbudget, htransport⟩

/-- `TreeCheckCountedCutParts` from the walk to batch `j` and the parts of its cut. -/
theorem treeCheckCountedCutParts_of_walk
    (walk : TreeCheckBatchWalkParts prims K circuits settings) :
    TreeCheckCountedCutParts prims K circuits settings :=
  treeCheckCountedCutParts_of_afterSetup prims K circuits settings
    (treeCheckAfterSetupCutParts_of_walk prims K circuits settings walk)

/-- info: 'ThresholdLeanXmssSecurity.treeCheckSetup_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckSetup_split

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCutParts_of_afterSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCutParts_of_afterSetup

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCutParts_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCutParts_of_walk

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckBatchWalk.inputs_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckBatchWalk.inputs_counts

end ThresholdLeanXmssSecurity
