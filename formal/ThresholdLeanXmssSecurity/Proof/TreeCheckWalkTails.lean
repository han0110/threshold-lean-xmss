import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSync
import ThresholdLeanXmssSecurity.Proof.TreeCheckHybrid

/-!
# Check cuts with pending opening tails

A batch boundary retains each operator's pending local work from the preceding
opening. The scheduler runs that tail immediately before the same operator's
next batch prefix. An absent or rejected tail aborts only that operator. The
prefix split and the snapshot split preserve the literal logged computation,
including both caches and the order of honest and adversarial queries.

The F4 trace in `review_opus_codex3.md` distinguishes these local orders:
`copy₁(previous), prf₁(next), copy₂(previous), prf₂(next)` and
`copy₁(previous), copy₂(previous), prf₁(next), prf₂(next)`. `openRep` performs
the copy checks after its exchange, and the next batch performs its input PRFs
before its exchange, so moving all opening tails into a global prefix does
change the log. This is an obstruction to that proposed construction, not a
counterexample to the existential `TreeCheckBatchWalkParts`: the trace assumes
a supported counted bad acceptance, and the old existential boundary leaves
its jobs, world and continuation unrestricted. Neither a supported instance
of that event nor an obstruction for every such boundary follows from the
displayed order comparison.

All cut clauses below concern one walk witness. Restricting `seen` changes only
the hybrid certificate; the source experiment and its actual cache remain the
same. The pinned and current leanVM libraries have no synchronous batch-tail
or pending-step cut lemma; the construction uses the local execution lemmas.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

abbrev TreeCheckTailResult (A : Adversary C E (Keys C) PEmpty PEmpty) :=
  (Bool × (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) ×
    TreeSimLog C

abbrev TreeCheckTailCheckpoint (A : Adversary C E (Keys C) PEmpty PEmpty) :=
  (A.State × (C.Party → Option
    (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C

/-- The pending opening checks stay in the local program of their operator. -/
structure TreeCheckTailBoundary (A : Adversary C E (Keys C) PEmpty PEmpty) where
  batch : TreeCheckBatchBoundary A
  tail : C.Party → OracleComp (LocalSpec C) (Option Unit)

namespace TreeCheckTailBoundary

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) {A : Adversary C E (Keys C) PEmpty PEmpty}

def program (b : TreeCheckTailBoundary A) (i : C.Party) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) :=
  treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
    (treeSimCheckBatchAudit K circuits settings (b.batch.ctx i) b.batch.jobs).run.run b.batch.initial
      >>= b.batch.k i

def run (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A) :
    ProbComp (TreeCheckTailResult A) := do
  let out ← (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality
      (b.batch.rounds circuits settings + b.batch.fuel) b.batch.state
      (b.program K circuits settings))).run b.batch.world
  treeCheckObserve prims D A Z out

def pre (b : TreeCheckTailBoundary A) : ProbComp (TreeCheckTailCheckpoint A) :=
  (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (b.batch.rounds circuits settings) b.batch.state
      (fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial))).run
      b.batch.world

/-- Pending local tails are executed in place, before the timed batch prefix. -/
theorem split (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter) :
    b.run prims K circuits settings D Z = b.pre prims K circuits settings D >>=
      treeCheckBatchCont prims K circuits D A Z b.batch := by
  have split := treeSimCheckTimed_phase_split D A
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds)
    b.batch.fuel b.batch.state
    (fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
      treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial)
    (fun i data => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial data
      >>= b.batch.k i) (fun i => treeLockstep_localPrelude_timed _ _ _ (by
        simpa only [parameter i] using treeSimCheckBatchPrefix_timed K circuits settings
          (b.batch.ctx i) b.batch.jobs b.batch.initial))
  unfold run program pre treeCheckBatchCont TreeCheckBatchBoundary.rounds
  simp only [bind_assoc] at split
  simp only [treeSimCheckBatchAudit_run_prefix, bind_assoc]
  rw [split]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]

/-- A snapshot may be placed anywhere in this same run. Its retained steps
include pending local opening continuations and preserve prior aborts. -/
theorem snapshot (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A)
    (n fuel : ℕ) (rounds : b.batch.rounds circuits settings + b.batch.fuel = n + fuel) :
    b.run prims K circuits settings D Z = (do
      let captured ← (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality n b.batch.state
          (fun i => treeLateSnapshot n (b.program K circuits settings i)))).run b.batch.world
      let out ← (simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality fuel captured.1.1
          (fun i => (captured.1.2 i).getD (.done none)))).run captured.2
      treeCheckObserve prims D A Z out) := by
  unfold run
  rw [rounds, treeCheck_snapshot_logged]
  simp only [bind_assoc]

/-- A supported checkpoint gives the actual prefix of every present operator,
after its own pending tail. -/
theorem prefix_support (b : TreeCheckTailBoundary A) (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings D))
    (i : C.Party) (hi : i ∉ D.1) (data : MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (present : o.1.2 i = some data) :
    some data ∈ support
      (treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial).run := by
  have allowed := treeLockstep_logged_run_allowed prims D _ _ o run
  have localRun := treeSimCheck_phase_replay D A noFunctionality _ _ b.batch.state _ o.1
    allowed i hi data present
  obtain ⟨_, _, hpref⟩ := localRun.option_bind_inv _ _ _
  exact hpref.choose_spec.1.mem_support

/-- Successful continuations force all honest checkpoint rows to be present,
including rows of operators that abort later. -/
theorem counts (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A)
    (self : ∀ i, (b.batch.ctx i).self = i)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (o : TreeCheckTailCheckpoint A) (ho : o ∈ support (b.pre prims K circuits settings D))
    (r : TreeCheckTailResult A)
    (hr : r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o))
    (accepted : ∃ i value, r.1.2.2 i = some value) :
    ∀ i, i ∉ D.1 → ∃ data, o.1.2 i = some data ∧
      data.2.2.history = filledHistory K i data.2.1.2 ∧
      data.2.2.label = b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1 ∧
      data.2.2.tag = b.batch.initial.2 ∧
      data.2.1.2.map (·.count) = b.batch.counts circuits ∧
      data.2.1.2.map (·.mode) =
        (List.range (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)))).map
          (fun _ => settings.mode) ++ [.peer] := by
  intro i hi
  have live := treeCheckBatch_live prims K circuits D A Z b.batch o r hr accepted
  obtain ⟨data, present⟩ := Option.isSome_iff_exists.mp (live i hi)
  refine ⟨data, present, ?_⟩
  simpa only [self i, parameter i, TreeCheckBatchBoundary.counts] using
    treeSimCheckBatchPrefix_state K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial data
      (b.prefix_support prims K circuits settings D o ho i hi data present)

/-- A coherent hash view of the actual logged prefix identifies the honest
inputs with one complete dealer family. -/
theorem dealer_inputs (b : TreeCheckTailBoundary A) (self : ∀ i, (b.batch.ctx i).self = i)
    (seeds : C.Term → HashOutput)
    (seed : ∀ i T, i ∉ D.1 → i ∈ C.holders T → (b.batch.ctx i).keys.seed T = seeds T)
    (o : TreeCheckTailCheckpoint A) (run : o ∈ support (b.pre prims K circuits settings D))
    (hash : Query C → HashOutput)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ o.2.2 →
      TreeSimCheckWorldHashes hash t u) :
    ∀ i, i ∉ D.1 → ∀ data, o.1.2 i = some data →
      data.1 = batchInputs hash seeds b.batch.jobs i := by
  have allowed := treeLockstep_logged_allowed prims D (TreeSimCheckWorldHashes hash) _ _ o run rows
  intro i hi data hd
  have localRun := treeSimCheck_phase_replay D A noFunctionality _ _ b.batch.state _ o.1
    allowed i hi data hd
  obtain ⟨_, _, localRun⟩ := localRun.option_bind_inv _ _ _
  unfold treeSimCheckBatchPrefix at localRun
  obtain ⟨inputs, hp, ht⟩ := localRun.option_bind_inv _ _ _
  obtain ⟨rest, _, he⟩ := ht.option_bind_inv _ _ _
  have he : data = (inputs, rest) := Option.some.inj he.pure_inv
  subst data
  rw [treeCheck_inputShares_replay prims hash _ (fun q u h => h) _ _ inputs hp]
  apply List.map_congr_left
  intro job _
  funext T
  rw [self i]
  by_cases held : i ∈ C.holders T
  · simp only [if_pos held, inputBits, seed i T hi held]
  · simp only [if_neg held]

/-- Prefix traces and completed honest inputs determine the saved circuit
outputs under deterministic verification. -/
theorem saved_correct (b : TreeCheckTailBoundary A)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (o : TreeCheckTailCheckpoint A) (run : o ∈ support (b.pre prims K circuits settings D))
    (live : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (x : C.Party → MainInput C)
    (inputs : MainInputs (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) D x)
    (same : ∀ i, i ∉ D.1 → (treeCheckPrefixData (o.1.2 i)).1 = x i)
    (accept : (multVerifyLeak D (stagesHonest D
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2))).2.2) :
    let js := b.batch.jobs.map (circuits b.batch.parameter ·.kind)
    let v := fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1
    (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf js).length →
      v i T g = v (refHolder D T) T g) ∧
    assemble js (shareValue (fun T => v (refHolder D T) T)) = mainOutputs js (stagesX D x) := by
  dsimp only
  have traces : ∀ i, ∃ p, i ∉ D.1 →
      TreeCheckLayerTrace K settings.mode (b.batch.jobs.map (circuits b.batch.parameter ·.kind))
        (x i) (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind))) p ∧
      (treeCheckPrefixData (o.1.2 i)).2.1.2 = p.2 ++
        [⟨outputShares K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) p.1, one K,
          (treeCheckPrefixData (o.1.2 i)).2.1.1,
          (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length, .peer⟩] := by
    intro i
    by_cases hi : i ∈ D.1
    · exact ⟨([], []), fun h => (h hi).elim⟩
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (live i hi)
    obtain ⟨p, ht, he⟩ := treeCheck_batchPrefix_trace K circuits settings (b.batch.ctx i)
      b.batch.jobs b.batch.initial data
      (b.prefix_support prims K circuits settings D o run i hi data hd)
    refine ⟨p, fun _ => ?_⟩
    have hx : data.1 = x i := by simpa only [hd, treeCheckPrefixData, Option.getD_some] using same i hi
    simpa only [hd, treeCheckPrefixData, Option.getD_some, parameter i, hx] using And.intro ht he
  choose p hp using traces
  have eq : stagesHonest D (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2) =
      stagesHonest D (treeCheckSavedTuples K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) p
        (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1)) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [stagesHonest, hi]
    · simp only [stagesHonest, if_neg hi, treeCheckSavedTuples, (hp i hi).2]
  rw [eq] at accept
  exact treeCheck_saved_correct K D settings.mode _ x inputs p _ (fun i hi => (hp i hi).1) accept

set_option maxHeartbeats 800000 in
/-- An actual wrong opening of the saved checkpoint values forces the exact
deterministic rejection predicate, also with pending tails in the prefix. -/
theorem opening_reject (b : TreeCheckTailBoundary A)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (self : ∀ i, (b.batch.ctx i).self = i)
    (o : TreeCheckTailCheckpoint A) (run : o ∈ support (b.pre prims K circuits settings D))
    (present : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (opening : TreeCheckOpeningAt prims K circuits D A b.batch o) :
    ¬ (multVerifyLeak D (stagesHonest D
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2))).2.2 := by
  intro accept
  have same : ∀ i, i ∉ D.1 →
      (treeCheckPrefixData (o.1.2 i)).1 = batchInputs opening.hash opening.seeds b.batch.jobs i := by
    intro i hi
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (present i hi)
    simpa only [hd, treeCheckPrefixData, Option.getD_some] using
      b.dealer_inputs prims K circuits settings D self opening.seeds opening.seed o run
        opening.hash opening.rows i hi data hd
  obtain ⟨held, correct⟩ := b.saved_correct prims K circuits settings D parameter o run present _
    (treeCheck_batchInputs_main D opening.hash opening.seeds circuits b.batch.parameter b.batch.jobs)
    same accept
  have value : ∀ g < (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length,
      opening.output g =
        shareValue (fun T => (treeCheckPrefixData (o.1.2 (refHolder D T))).2.1.1 T) g := by
    with_reducible
      exact treeLockstep_open_head_value prims K D opening.live _
        (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1)
        (fun T => (treeCheckPrefixData (o.1.2 (refHolder D T))).2.1.1 T)
        held opening.ds opening.sent opening.party opening.before opening.after opening.output
        opening.hashes opening.run opening.good
  exact opening.wrong ((treeLockstep_assemble_congr _ opening.output _ value).trans
    (correct.trans (treeCheck_mainOutputs_dealer prims D opening.hash opening.seeds circuits
      b.batch.parameter b.batch.jobs)))

end TreeCheckTailBoundary

/-- A synchronized walk to a batch, retaining each operator's local opening
tail. Finished branches have their original complete logged result. -/
structure TreeCheckTailWalk (A : Adversary C E (Keys C) PEmpty PEmpty) where
  β : Type
  pre : ProbComp (β ⊕ TreeCheckTailResult A)
  boundary : β → TreeCheckTailBoundary A
  hybrid : β → TreeCheckTailCheckpoint A → TreeCheckHybrid C E

namespace TreeCheckTailWalk

variable {prims : Primitives} {K : Constants C E} {circuits : Circuits} {settings : Settings}
variable {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}

variable (prims K circuits settings D) in
/-- The cut records the actual joint prefix, world state and log. -/
def cut (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckTailWalk A) :
    TreeCheckCountedCutData A where
  σ := (W.β × TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A
  pre := W.pre >>= fun e => match e with
    | .inl c => (fun o => .inl (c, o)) <$> (W.boundary c).pre prims K circuits settings D
    | .inr r => pure (.inr r)
  cont := fun s => match s with
    | .inl (c, o) => treeCheckBatchCont prims K circuits D A Z (W.boundary c).batch o
    | .inr r => pure r
  count := fun s => match s with
    | .inl (c, _) => tupleCount
        ((W.boundary c).batch.jobs.map (circuits (W.boundary c).batch.parameter ·.kind))
    | .inr _ => 0
  hybrid := fun s => match s with
    | .inl (c, o) => W.hybrid c o
    | .inr _ => treeCheckDummyHybrid

variable (prims K circuits settings D) in
/-- Equality to the actual after-setup run, with a common public parameter. -/
def Split (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckTailWalk A)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) : Prop :=
  treeCheckAfterSetup prims K circuits settings top tree D A x Z p =
    (W.pre >>= fun e => match e with
      | .inl c => (W.boundary c).run prims K circuits settings D Z
      | .inr r => pure r) ∧
    ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter

theorem cut_split {top : TopTree} {tree : Tree} {x : C.Party → Keys C}
    {Z : Distinguisher C A.State TreeOutput} {W : TreeCheckTailWalk A}
    {p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C}
    (h : W.Split prims K circuits settings D top tree x Z p) :
    treeCheckAfterSetup prims K circuits settings top tree D A x Z p =
      (W.cut prims K circuits settings D Z).pre >>= (W.cut prims K circuits settings D Z).cont := by
  rw [h.1]
  unfold cut
  simp only [bind_assoc]
  apply bind_congr
  intro e
  cases e with
  | inl c =>
    simp only [bind_map_left]
    exact (W.boundary c).split prims K circuits settings D Z (h.2 c)
  | inr r => simp only [pure_bind]

theorem mem_support_cut_pre {Z : Distinguisher C A.State TreeOutput} {W : TreeCheckTailWalk A}
    {c : W.β} {o : TreeCheckTailCheckpoint A}
    (h : (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre) :
    o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
  unfold cut at h
  rw [mem_support_bind_iff] at h
  obtain ⟨e, _, h⟩ := h
  cases e with
  | inl c' =>
    rw [support_map] at h
    obtain ⟨o', ho', he⟩ := h
    cases he
    exact ho'
  | inr r => simp at h

theorem mem_support_cut_pre_inr {Z : Distinguisher C A.State TreeOutput} {W : TreeCheckTailWalk A}
    {r : TreeCheckTailResult A}
    (h : (.inr r : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre) :
    .inr r ∈ support W.pre := by
  unfold cut at h
  rw [mem_support_bind_iff] at h
  obtain ⟨e, he, h⟩ := h
  cases e with
  | inl c =>
    rw [support_map] at h
    obtain ⟨o, _, ho⟩ := h
    cases ho
  | inr r' =>
    simp only [support_pure, Set.mem_singleton_iff, Sum.inr.injEq] at h
    cases h
    exact he

def StandardTuples (circuits : Circuits) (D : C.Coalition) (W : TreeCheckTailWalk A) : Prop :=
  ∀ c o, (W.hybrid c o).counts = (W.boundary c).batch.counts circuits ∧
    ∀ i, i ∉ D.1 → (W.hybrid c o).tuples i = ((o.1.2 i).map (·.2.1.2)).getD []

variable (prims K circuits settings D) in
def Unreached (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree)) (W : TreeCheckTailWalk A) : Prop :=
  ∀ r, .inr r ∈ support W.pre →
    ¬ (TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧ ¬ TreeCheckUncounted D r.2)

/-- A supported counted bad run must traverse a genuine pending-tail
checkpoint. Sending every outcome directly to the finished side cannot
satisfy these clauses when such an outcome exists. -/
theorem reached_of_counted_bad {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    {p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C}
    (split : W.Split prims K circuits settings D top tree x Z p)
    (unreached : W.Unreached prims K circuits settings D top tree x z j)
    (r : TreeCheckTailResult A)
    (run : r ∈ support (treeCheckAfterSetup prims K circuits settings top tree D A x Z p))
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r)
    (counted : ¬ TreeCheckUncounted D r.2) :
    ∃ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre ∧
      r ∈ support ((W.cut prims K circuits settings D Z).cont (.inl (c, o))) := by
  rw [W.cut_split split, mem_support_bind_iff] at run
  obtain ⟨s, hs, hr⟩ := run
  rcases s with ⟨c, o⟩ | r'
  · exact ⟨c, o, hs, hr⟩
  · have he : r = r' := by simpa only [cut, support_pure, Set.mem_singleton_iff] using hr
    subst r'
    exact (unreached r (mem_support_cut_pre_inr hs) ⟨bad, counted⟩).elim

variable (prims K circuits settings D) in
/-- The third `TupleInputs` clause at the same supported joint checkpoint. -/
def Consistent (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)) →
    (∀ i, i ∉ D.1 → ((W.hybrid c o).tuples i).map (·.count) = (W.hybrid c o).counts) →
    (∀ i k, i ∉ D.1 → k ∉ D.1 →
      ((W.hybrid c o).tuples i).map (·.mode) = ((W.hybrid c o).tuples k).map (·.mode)) →
    TupleInputs K (W.hybrid c o).counts D (W.hybrid c o).tuples

theorem inputs_counts {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    (standard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).batch.ctx i).self = i)
    (parameter : ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter)
    (c : W.β) (o : TreeCheckTailCheckpoint A)
    (hs : (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o))) :
    (∀ i, i ∉ D.1 → ((W.hybrid c o).tuples i).map (·.count) = (W.hybrid c o).counts) ∧
      (∀ i k, i ∉ D.1 → k ∉ D.1 →
        ((W.hybrid c o).tuples i).map (·.mode) = ((W.hybrid c o).tuples k).map (·.mode)) ∧
      (W.hybrid c o).counts.sum = (W.cut prims K circuits settings D Z).count (.inl (c, o)) := by
  obtain ⟨r, hr, hbad, _⟩ := live
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, hout, _⟩ := hbad.2
  have data := (W.boundary c).counts prims K circuits settings D Z (self c) (parameter c)
    o (mem_support_cut_pre hs) r hr ⟨i, (value, records), hout⟩
  obtain ⟨counts, tuples⟩ := standard c o
  refine ⟨fun i hi => ?_, fun i k hi hk => ?_, ?_⟩
  · obtain ⟨v, hv, _, _, _, hc, _⟩ := data i hi
    rw [tuples i hi, hv, counts]
    exact hc
  · obtain ⟨v, hv, _, _, _, _, hm⟩ := data i hi
    obtain ⟨w, hw, _, _, _, _, hm'⟩ := data k hk
    rw [tuples i hi, tuples k hk, hv, hw]
    exact hm.trans hm'.symm
  · rw [counts, TreeCheckBatchWalk.counts_sum]
    rfl

/-- The first two tuple clauses and the count identity follow from the
actual pending-tail prefix; only its consistency clause is supplied. -/
theorem inputs {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    (standard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).batch.ctx i).self = i)
    (parameter : ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter)
    (unreached : W.Unreached prims K circuits settings D top tree x z j)
    (consistent : W.Consistent prims K circuits settings D top tree x z Z j) :
    (W.cut prims K circuits settings D Z).Inputs prims K circuits settings top tree D A x z j := by
  rintro (⟨c, o⟩ | r) hs live
  · obtain ⟨hc, hm, hsum⟩ := inputs_counts standard self parameter c o hs live
    exact ⟨consistent c o hs live hc hm, hsum⟩
  · obtain ⟨r', hr, bad, counted⟩ := live
    have he : r' = r := by simpa only [cut, support_pure, Set.mem_singleton_iff] using hr
    subst r'
    exact (unreached r (mem_support_cut_pre_inr hs) ⟨bad, counted⟩).elim

variable (prims K circuits settings D) in
/-- Each live checkpoint is linked to an actual wrong opening of its own
saved values, under one coherent dealer hash view. -/
def Opening (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)) →
    Nonempty (TreeCheckOpeningAt prims K circuits D A (W.boundary c).batch o)

theorem reject_of_opening {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    (standard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).batch.ctx i).self = i)
    (parameter : ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter)
    (unreached : W.Unreached prims K circuits settings D top tree x z j)
    (opening : W.Opening prims K circuits settings D top tree x z Z j) :
    (W.cut prims K circuits settings D Z).Reject prims K circuits settings top tree D A x z j := by
  rintro (⟨c, o⟩ | r) hs live
  · obtain ⟨proof⟩ := opening c o hs live
    obtain ⟨r, hr, hbad, _⟩ := live
    obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, hout, _⟩ := hbad.2
    have present := treeCheckBatch_live prims K circuits D A Z (W.boundary c).batch o r hr
      ⟨i, (value, records), hout⟩
    have reject := (W.boundary c).opening_reject prims K circuits settings D (parameter c) (self c)
      o (mem_support_cut_pre hs) present proof
    have same : (fun i => if i ∈ D.1 then none else some ((W.hybrid c o).tuples i)) =
        stagesHonest D (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2) := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [stagesHonest, hi]
      · simp only [if_neg hi, stagesHonest, (standard c o).2 i hi]
        cases o.1.2 i <;> rfl
    change ¬ (multVerifyLeak D
      (fun i => if i ∈ D.1 then none else some ((W.hybrid c o).tuples i))).2.2
    rw [same]
    exact reject
  · obtain ⟨r', hr, bad, counted⟩ := live
    have he : r' = r := by simpa only [cut, support_pure, Set.mem_singleton_iff] using hr
    subst r'
    exact (unreached r (mem_support_cut_pre_inr hs) ⟨bad, counted⟩).elim

/-- One fixed transformation of the witness restricts only its ghost set. -/
def restrictSeen (W : TreeCheckTailWalk A) : TreeCheckTailWalk A :=
  { W with hybrid := fun c o => (W.hybrid c o).restrictSeen }

theorem cut_restrictSeen (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckTailWalk A) :
    W.restrictSeen.cut prims K circuits settings D Z =
      (W.cut prims K circuits settings D Z).restrictSeen := by
  have dummy : (treeCheckDummyHybrid (C := C) (E := E)).restrictSeen = treeCheckDummyHybrid := by
    simp only [TreeCheckHybrid.restrictSeen, treeCheckDummyHybrid, treeCheckSeen, Finset.filter_empty]
  simp only [cut, restrictSeen, TreeCheckCountedCutData.restrictSeen]
  congr 1
  · apply bind_congr
    rintro (c | r) <;> rfl
  · funext s
    cases s <;> rfl
  · funext s
    cases s <;> rfl
  · funext s
    cases s <;> simp only [dummy]

end TreeCheckTailWalk

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- All obligations are attached to this particular walk. No clause chooses
another walk or another actual prefix. -/
def TreeCheckTailWalk.At (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (W : TreeCheckTailWalk A) : Prop :=
  W.Split prims K circuits settings D top tree x Z p ∧
  W.StandardTuples circuits D ∧
  (∀ c i, ((W.boundary c).batch.ctx i).self = i) ∧
  (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j ∧
  W.Unreached prims K circuits settings D top tree x z j ∧
  W.Consistent prims K circuits settings D top tree x z Z j ∧
  (W.cut prims K circuits settings D Z).Reject prims K circuits settings top tree D A x z j ∧
  (W.cut prims K circuits settings D Z).HybridParts prims K circuits settings top tree D A x z j q

/-- Construction data for the same walk: opening linkage and raw accounting
replace the derived rejection and the projected-set budget. -/
structure TreeCheckTailWalk.Prepared (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (W : TreeCheckTailWalk A) : Prop where
  split : W.Split prims K circuits settings D top tree x Z p
  standard : W.StandardTuples circuits D
  self : ∀ c i, ((W.boundary c).batch.ctx i).self = i
  jobs : (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j
  unreached : W.Unreached prims K circuits settings D top tree x z j
  consistent : W.Consistent prims K circuits settings D top tree x z Z j
  opening : W.Opening prims K circuits settings D top tree x z Z j
  queries : (W.cut prims K circuits settings D Z).Queries prims K circuits settings top tree D A x z j
  cache : (W.cut prims K circuits settings D Z).Cache prims K circuits settings top tree D A x z j
  prior : (W.cut prims K circuits settings D Z).Prior prims K circuits settings top tree D A x z j
  accounted : ∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
    ((W.cut prims K circuits settings D Z).hybrid s).seen.card +
      (2 * halvings ((W.cut prims K circuits settings D Z).count s) + 5) *
        ((W.cut prims K circuits settings D Z).hybrid s).step ≤ q
  reserved : ∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
    ∃ point ∈ ((W.cut prims K circuits settings D Z).hybrid s).seen, ¬ TreeCheckSeenQuery point
  transport : (W.cut prims K circuits settings D Z).Transport prims K circuits settings top tree D A x z j

/-- Rejection, cache projection and the extra reserved query all use one
fixed witness `W.restrictSeen`. The actual source log and cache are unchanged. -/
theorem TreeCheckTailWalk.at_of_prepared {top : TopTree} {tree : Tree} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {q : ℕ} {j : Fin (treeBatches settings tree)}
    {p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C} {W : TreeCheckTailWalk A}
    (h : W.Prepared prims K circuits settings top tree D A x z Z q j p) :
    W.restrictSeen.At prims K circuits settings top tree D A x z Z q j p := by
  have hcut := W.cut_restrictSeen (prims := prims) (K := K) (circuits := circuits)
    (settings := settings) (D := D) Z
  have hpre : (W.restrictSeen.cut prims K circuits settings D Z).pre =
      (W.cut prims K circuits settings D Z).pre := by
    simp only [cut, restrictSeen]
    apply bind_congr
    rintro (c | r) <;> rfl
  refine ⟨?_, h.standard, h.self, ?_, h.unreached, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, h.split.2⟩
    rw [h.split.1]
    apply bind_congr
    rintro (c | r) <;> rfl
  · rw [hcut]
    exact h.jobs
  · intro c o hs live hc hm
    rw [hpre] at hs
    exact h.consistent c o hs live hc hm
  · rw [hcut]
    exact W.reject_of_opening h.standard h.self h.split.2 h.unreached h.opening
  · rw [hcut]
    exact h.queries
  · rw [hcut]
    exact TreeCheckCountedCutData.restrictSeen_cache prims K circuits settings top tree D A x z j _ h.cache
  · rw [hcut]
    exact h.prior
  · rw [hcut]
    exact TreeCheckCountedCutData.restrictSeen_budget prims K circuits settings top tree D A x z j _ q
      h.accounted h.reserved
  · rw [hcut]
    exact h.transport

/-- One pending-tail walk, with all clauses, for every reached setup state. -/
def TreeCheckTailWalkParts : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ W : TreeCheckTailWalk A,
          W.At prims K circuits settings top tree D A x z Z q j p

/-- Global pending-tail construction and indexed opening linkage, with all
hybrid obligations about that same walk, before its fixed `seen` projection. -/
def TreeCheckTailWalkConstruction : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ W : TreeCheckTailWalk A,
          W.Prepared prims K circuits settings top tree D A x z Z q j p

theorem treeCheckTailWalkParts_of_construction
    (construction : TreeCheckTailWalkConstruction prims K circuits settings) :
    TreeCheckTailWalkParts prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j p hp
  obtain ⟨W, prepared⟩ := construction hbatch top tree D A x z Z q hx hq hsmall j p hp
  exact ⟨W.restrictSeen, W.at_of_prepared prims K circuits settings prepared⟩

theorem TreeCheckTailWalk.afterSetup {top : TopTree} {tree : Tree} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {q : ℕ} {j : Fin (treeBatches settings tree)}
    {p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C} {W : TreeCheckTailWalk A}
    (parts : W.At prims K circuits settings top tree D A x z Z q j p) :
    TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p
      (W.cut prims K circuits settings D Z) := by
  obtain ⟨split, standard, self, jobs, unreached, consistent, reject,
    queries, cache, prior, budget, transport⟩ := parts
  exact ⟨W.cut_split split, jobs, W.inputs standard self split.2 unreached consistent,
    queries, cache, prior, reject, budget, transport⟩

/-- The pending-tail target supplies the original counted cut with all nine
clauses and the same literal distributional equality. -/
theorem treeCheckCountedCutParts_of_tailWalk
    (walk : TreeCheckTailWalkParts prims K circuits settings) :
    TreeCheckCountedCutParts prims K circuits settings := by
  apply treeCheckCountedCutParts_of_afterSetup prims K circuits settings
  intro hbatch top tree D A x z Z q hx hq hsmall j p hp
  obtain ⟨W, parts⟩ := walk hbatch top tree D A x z Z q hx hq hsmall j p hp
  exact ⟨W.cut prims K circuits settings D Z, W.afterSetup prims K circuits settings parts⟩

theorem treeCheckCountedCutParts_of_tailConstruction
    (construction : TreeCheckTailWalkConstruction prims K circuits settings) :
    TreeCheckCountedCutParts prims K circuits settings :=
  treeCheckCountedCutParts_of_tailWalk prims K circuits settings
    (treeCheckTailWalkParts_of_construction prims K circuits settings construction)

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailBoundary.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailBoundary.split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailBoundary.snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailBoundary.snapshot

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailBoundary.counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailBoundary.counts

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailBoundary.dealer_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailBoundary.dealer_inputs

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailBoundary.saved_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailBoundary.saved_correct

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.reached_of_counted_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.reached_of_counted_bad

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.inputs

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.reject_of_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.reject_of_opening

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.cut_restrictSeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.cut_restrictSeen

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.at_of_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.at_of_prepared

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCutParts_of_tailWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCutParts_of_tailWalk

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCutParts_of_tailConstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCutParts_of_tailConstruction

end ThresholdLeanXmssSecurity
