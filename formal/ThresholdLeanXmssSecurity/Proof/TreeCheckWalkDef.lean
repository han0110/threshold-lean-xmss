import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkHybrid

/-!
# Scheduler cuts before pending local heads

The compiler delivers one adversary round, then retains each raw local
continuation before `advance` runs it. Its next iteration executes these
continuations in the scheduler's party order. Both caches, the log and the
remaining round budget stay in the checkpoint.

A shared `RecipeFamily` supplies the batch decoder and hybrid adversary.
`LocalDecoding` requires honest local-program identities and enough remaining
fuel at each decoded index. `walkSplit` derives the original split from those
local laws. `sourceConstruction_of_positions` combines them with the bad-run,
opening, position and hybrid clauses for that same compiled walk. Finished
branches must satisfy the original `Unreached` clause.

The pinned and current leanVM proof libraries have no synchronous scheduler
or pending-head compiler. The construction uses `stepRound_real` and the
existing threshold execution model.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkDef

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable {A : Adversary C E (Keys C) PEmpty PEmpty}

abbrev Output := TreeOutput × List (TreeSimCheckBatchRecord C)

/-- A raw program checkpoint, before any pending local head runs. -/
structure Pending (A : Adversary C E (Keys C) PEmpty PEmpty) where
  state : A.State
  program : C.Party → PartyM C E RealSpec (Output (C := C))
  fuel : ℕ
  world : TreeSimState C

/-- The messages are already fixed; this definition performs no query. -/
def resume (D : C.Coalition)
    (steps : C.Party → Step C E RealSpec (Output (C := C)))
    (sent : C.Party → Mail C E) (i : C.Party) : PartyM C E RealSpec (Output (C := C)) :=
  match steps i with
  | .done out => OptionT.mk (pure out)
  | .wait _ k => if i ∈ D.1 then failure else
      OptionT.mk (k fun h => if h ∈ D.1 then sent h i else (steps h).delivered i)
  | .call impossible _ => impossible.elim

/-- Starting the retained programs performs precisely the original local pass. -/
theorem resume_start (D : C.Coalition)
    (steps : C.Party → Step C E RealSpec (Output (C := C)))
    (corrupt : ∀ i ∈ D.1, steps i = .done none) (sent : C.Party → Mail C E) :
    startSteps worldRoles D (resume D steps sent) =
      free (Concrete.sequenceFin (roundLocal D steps sent)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, roundLocal, free_pure]
  · simp only [if_neg hi]
    cases hs : steps i with
    | done out => simp [resume, roundLocal, hs, worldRoles, advance_pure, free_pure]
    | wait out k => simp [resume, roundLocal, hs, hi, worldRoles]
    | call impossible k => exact impossible.elim

/-- The scheduler never starts a corrupt local program. -/
theorem start_corrupt (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec (Output (C := C)))
    (steps : C.Party → Step C E RealSpec (Output (C := C)))
    (run : steps ∈ support (startSteps worldRoles D program)) :
    ∀ i ∈ D.1, steps i = .done none := by
  intro i hi
  have h := mem_support_sequenceFin_oc _ steps run i
  simpa [hi] using h

variable (prims : Primitives) (D : C.Coalition)
    (Z : Distinguisher C A.State TreeOutput)

def finish (p : Pending A) : ProbComp (TreeCheckTailResult A) := do
  let out ← (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality p.fuel p.state p.program)).run p.world
  treeCheckObserve prims D A Z out

/-- One actual round, suspended before the local pass following delivery.
Terminal branches retain the actual final observation and its log. -/
def next (fuel : ℕ) (p : Pending A) :
    ProbComp (Pending A ⊕ TreeCheckTailResult A) := do
  let started ← (simulateQ (treeSimLoggedWorld prims D)
    (startSteps worldRoles D p.program)).run p.world
  if ∀ i, i ∉ D.1 → (started.1 i).isDone then
    return .inr (← treeCheckObserve prims D A Z
      ((p.state, fun i => (started.1 i).output), started.2))
  else
    let reply ← (simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.adversary (A.round p.state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (started.1 i).outbox c else none))).run started.2
    return .inl ⟨reply.1.1, resume D started.1 reply.1.2, fuel, reply.2⟩

/-- Resuming the raw continuations is a literal equality of logged programs. -/
theorem next_split (fuel : ℕ) (p : Pending A) :
    finish prims D Z {p with fuel := fuel + 1} =
      next prims D Z fuel p >>= fun r => match r with
        | .inl pending => finish prims D Z pending
        | .inr result => pure result := by
  unfold finish next
  simp only [executePhase, simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro started hs
  have raw : started.1 ∈ support (startSteps worldRoles D p.program) := by
    apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨started, hs, rfl⟩
  have hc := start_corrupt D p.program started.1 raw
  rw [executeRounds]
  split_ifs with hd
  · simp only [simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc, bind_pure]
  · rw [stepRound_real]
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro reply
    rw [resume_start D started.1 hc reply.1.2]

/-- Every returned index retains the actual decoder result at that program position. -/
abbrev Decoded {M : Type} (decode : Pending A → Option M) :=
  {c : Pending A × M // decode c.1 = some c.2}

/-- The decoder is inspected before local execution; a miss runs one real
round. The recursion is bounded by the remaining ceremony fuel. -/
def walk {M : Type} (decode : Pending A → Option M) :
    ℕ → Pending A → ProbComp (Decoded decode ⊕ TreeCheckTailResult A)
  | 0, p =>
      let current := {p with fuel := 0}
      if hit : (decode current).isSome then
        pure (.inl ⟨(current, (decode current).get hit), Option.some_get hit |>.symm⟩)
      else .inr <$> finish prims D Z current
  | fuel + 1, p =>
      let current := {p with fuel := fuel + 1}
      if hit : (decode current).isSome then
        pure (.inl ⟨(current, (decode current).get hit), Option.some_get hit |>.symm⟩)
      else next prims D Z fuel p >>= fun outcome => match outcome with
        | .inl pending => walk decode fuel pending
        | .inr result => pure (.inr result)

/-- The bounded compiler preserves the original program, including its
terminal branches and every pending local query. -/
theorem walk_split {M : Type} (decode : Pending A → Option M)
    (fuel : ℕ) (p : Pending A) :
    finish prims D Z {p with fuel := fuel} =
      walk prims D Z decode fuel p >>= fun outcome => match outcome with
        | .inl c => finish prims D Z c.1.1
        | .inr result => pure result := by
  induction fuel generalizing p with
  | zero =>
    simp only [walk]
    split_ifs <;> simp only [pure_bind, bind_map_left, bind_pure]
  | succ fuel ih =>
    simp only [walk]
    split_ifs with hit
    · simp only [pure_bind]
    · rw [next_split prims D Z fuel p, bind_assoc]
      apply bind_congr_of_forall_mem_support
      intro outcome ho
      cases outcome with
      | inr result => simp only [pure_bind]
      | inl pending =>
        have hf : pending.fuel = fuel := by
          unfold next at ho
          simp only [mem_support_bind_iff] at ho
          obtain ⟨started, _, ho⟩ := ho
          split_ifs at ho
          · simp only [mem_support_bind_iff, mem_support_pure_iff] at ho
            obtain ⟨r, _, impossible⟩ := ho
            cases impossible
          · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at ho
            obtain ⟨reply, _, he⟩ := ho
            cases he
            rfl
        have same : {pending with fuel := fuel} = pending := by
          cases pending
          simp_all
        simpa only [same] using ih pending

/-- Delivery extends the retained log without executing the pending heads. -/
theorem next_prefix (fuel : ℕ) (p pending : Pending A)
    (run : .inl pending ∈ support (next prims D Z fuel p)) :
    p.world.2 <+: pending.world.2 := by
  unfold next at run
  rw [mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  split_ifs at run
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨out, _, impossible⟩ := run
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
    obtain ⟨reply, hr, he⟩ := run
    cases he
    exact (treeSimLoggedWorld_prefix prims D _ p.world started hs).trans
      (treeSimLoggedWorld_prefix prims D _ started.2 reply hr)

/-- Every decoded position extends the same starting execution log. -/
theorem walk_prefix {M : Type} (decode : Pending A → Option M)
    (fuel : ℕ) (p : Pending A) (c : Decoded decode)
    (run : .inl c ∈ support (walk prims D Z decode fuel p)) :
    p.world.2 <+: c.1.1.world.2 := by
  induction fuel generalizing p with
  | zero =>
    simp only [walk] at run
    split_ifs at run
    · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
      cases run
      exact List.prefix_refl _
    · simp only [support_map, Set.mem_image] at run
      obtain ⟨r, _, impossible⟩ := run
      cases impossible
  | succ fuel ih =>
    simp only [walk] at run
    split_ifs at run
    · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
      cases run
      exact List.prefix_refl _
    · rw [mem_support_bind_iff] at run
      obtain ⟨outcome, ho, run⟩ := run
      cases outcome with
      | inr result => simp only [mem_support_pure_iff] at run; cases run
      | inl pending =>
        exact (next_prefix prims D Z fuel p pending ho).trans (ih pending run)

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The actual audited program immediately after PRSS setup. -/
def initial (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) : Pending A where
  state := p.1.1
  program := fun i => (p.1.2 i).elim failure
    (fun prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
  fuel := ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)
  world := p.2

/-- The compiler starts at the exact supported setup state. -/
theorem initial_split (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z)) :
    treeCheckAfterSetup prims K circuits settings top tree D A x Z p =
      finish prims D Z (initial K circuits settings top tree x p) := by
  have corrupt : ∀ i ∈ D.1, p.1.2 i = none := by
    simp only [treeSaltSetup, mem_support_bind_iff] at hp
    obtain ⟨start, _, hs⟩ := hp
    exact treeSetup_corrupt_none prims D A start.1 start.2 p hs
  have restart : free (Concrete.sequenceFin fun i => continueStep
      (fun prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
      (.done (p.1.2 i))) =
      startSteps worldRoles D (initial K circuits settings top tree x p).program := by
    unfold startSteps
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi, corrupt i hi, continueStep, free_pure]
    · cases he : p.1.2 i <;>
        simp [initial, hi, he, continueStep, worldRoles, advance_pure, free_pure]
  unfold treeCheckAfterSetup finish
  rw [restart]
  simp only [executePhase, simulateQ_bind, StateT.run_bind, bind_assoc]
  rfl

/-- Batch metadata contains no caller-selected context. Contexts are always
rebuilt from the real input keys and each party's own index. -/
structure Batch (A : Adversary C E (Keys C) PEmpty PEmpty) where
  prss : C.Party → PrssKeys C
  jobs : List Job
  counters : ℕ × ℕ
  tail : C.Party → OracleComp (LocalSpec C) (Option Unit)
  cont : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
    PartyM C E RealSpec (Output (C := C))

def boundary (x : C.Party → Keys C) (c : Pending A × Batch A) : TreeCheckTailBoundary A where
  batch := {
    state := c.1.state
    ctx := fun i => ⟨i, x i, c.2.prss i⟩
    parameter := (x (refHolder D K.publicTerm)).parameter
    jobs := c.2.jobs
    initial := c.2.counters
    k := c.2.cont
    fuel := c.1.fuel - (depth (c.2.jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1)
    world := c.1.world }
  tail := c.2.tail

/-- Local decoding laws: the same pending program and the same remaining
rounds, independently of any bad event or final observation. -/
def Decodes (x : C.Party → Keys C) (decode : Pending A → Option (Batch A)) : Prop :=
  ∀ c : Decoded decode,
    (boundary D K circuits settings x c.1).batch.rounds circuits settings ≤ c.1.1.fuel ∧
    ∀ i, i ∉ D.1 → c.1.1.program i =
      (boundary D K circuits settings x c.1).program K circuits settings i

/-- Every decoded local program has the identical actual continuation. -/
theorem decoded_finish (x : C.Party → Keys C) (decode : Pending A → Option (Batch A))
    (sound : Decodes D K circuits settings x decode) (c : Decoded decode) :
    finish prims D Z c.1.1 = (boundary D K circuits settings x c.1).run prims K circuits settings D Z := by
  obtain ⟨room, same⟩ := sound c
  unfold finish TreeCheckTailBoundary.run
  congr 1
  congr 1
  have fuel : (boundary D K circuits settings x c.1).batch.rounds circuits settings +
      (boundary D K circuits settings x c.1).batch.fuel = c.1.1.fuel :=
    Nat.add_sub_of_le room
  rw [fuel]
  congr 1
  unfold executePhase
  congr 1
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · simp only [if_neg hi, same i hi]

/-- The hybrid adapter supplies only the adversary state and prior keys.
The tuples, count, counters, budget, cache and log are fixed by the checkpoint. -/
structure HybridSeed where
  adversary : CheckAdversary C E (List (Tuple C))
  state : adversary.State
  keys : Finset HashOutput

def hybrid (x : C.Party → Keys C) (step : ℕ)
    (c : Pending A × Batch A) (o : TreeCheckTailCheckpoint A)
    (seed : HybridSeed (C := C) (E := E)) : TreeCheckHybrid C E where
  counts := (boundary D K circuits settings x c).batch.counts circuits
  adversary := seed.adversary
  tuples := fun i => ((o.1.2 i).map (·.2.1.2)).getD []
  step := step
  state := seed.state
  tag := c.2.counters.2
  label := c.2.counters.1 +
    depth (c.2.jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1
  cache := o.2.1.1
  seen := treeCheckCountedSeen o.2.2
  keys := seed.keys

/-- One decoder and one hybrid adapter are used throughout this same compiler run. -/
structure Recipe (A : Adversary C E (Keys C) PEmpty PEmpty) where
  decode : Pending A → Option (Batch A)
  seed : Decoded decode → TreeCheckTailCheckpoint A → HybridSeed (C := C) (E := E)

/-- A source walk produced by the actual bounded scheduler compiler. -/
abbrev sourceWalk (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (recipe : Recipe A) : TreeCheckTailWalk A where
  β := Decoded recipe.decode
  pre := walk prims D Z recipe.decode
    (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p)
  boundary := fun c => boundary D K circuits settings x c.1
  hybrid := fun c o => hybrid D K circuits settings x step c.1 o (recipe.seed c o)

/-- Context identity and standard tuple projection hold at every index,
including indices outside the supported execution. -/
theorem sourceWalk_standard (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) (recipe : Recipe A) :
    (sourceWalk prims D Z K circuits settings top tree x step p recipe).StandardTuples circuits D ∧
    ∀ c i, (((sourceWalk prims D Z K circuits settings top tree x step p recipe).boundary c).batch.ctx i).self = i := by
  exact ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩

/-- Local decoder soundness gives the exact `Split` clause of the original
source target, with no event-conditioned equality. -/
theorem sourceWalk_split (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) (recipe : Recipe A)
    (dealt : DealtInputs D x) (hp : p ∈ support (treeSaltSetup prims D A x z))
    (sound : Decodes D K circuits settings x recipe.decode) :
    (sourceWalk prims D Z K circuits settings top tree x step p recipe).Split
      prims K circuits settings D top tree x Z p := by
  constructor
  · rw [initial_split prims D Z K circuits settings top tree x z p hp]
    have cut := walk_split prims D Z recipe.decode
      (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p)
    rw [cut]
    dsimp only [sourceWalk]
    apply bind_congr
    intro outcome
    cases outcome with
    | inr result => rfl
    | inl c => with_reducible exact decoded_finish prims D Z K circuits settings x recipe.decode sound c
  · intro c i
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl

/-- A supported batch checkpoint retains its index from the same walk prefix. -/
theorem index_support (W : TreeCheckTailWalk A) (c : W.β) (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : (W.β × TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A) ∈ support (W.cut prims K circuits settings D Z).pre) :
    .inl c ∈ support W.pre := by
  unfold TreeCheckTailWalk.cut at run
  rw [mem_support_bind_iff] at run
  obtain ⟨outcome, hr, run⟩ := run
  cases outcome with
  | inr result => simp only [mem_support_pure_iff] at run; cases run
  | inl c' =>
    rw [support_map] at run
    obtain ⟨o', ho, he⟩ := run
    cases he
    exact hr

set_option linter.constructorNameAsVariable false in
/-- The actual source compiler supplies setup-prefix provenance at every
supported checkpoint; no live-event premise is required. -/
theorem sourceWalk_log_prefix (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) (recipe : Recipe A)
    (c : Decoded recipe.decode)
    (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : (Decoded recipe.decode × TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A) ∈ support
      ((sourceWalk prims D Z K circuits settings top tree x step p recipe).cut
        prims K circuits settings D Z).pre) : p.2.2 <+: o.2.2 := by
  let W := sourceWalk prims D Z K circuits settings top tree x step p recipe
  have hc : .inl c ∈ support W.pre := by
    with_reducible exact index_support prims D Z K circuits settings W c o run
  have ho : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre (W := W) (prims := prims) (K := K)
      (circuits := circuits) (settings := settings) (D := D) (Z := Z) (c := c) (o := o) run)
  dsimp only [W, sourceWalk] at hc
  have before : (initial K circuits settings top tree x p).world.2 <+: c.1.1.world.2 := by
    with_reducible exact (walk_prefix prims D Z recipe.decode
      (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p) c hc)
  dsimp only [W, sourceWalk] at ho
  unfold TreeCheckTailBoundary.pre at ho
  have after := treeSimLoggedWorld_prefix prims D _
    (boundary D K circuits settings x c.1).batch.world o ho
  exact before.trans after

end TreeCheckWalkDef

namespace TreeCheckWalkDef
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- One shared decoder and hybrid adapter for each actual setup and batch. -/
abbrev RecipeFamily : Type 1 :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C), Recipe A

variable (R : RecipeFamily (C := C) (E := E) circuits settings)

abbrev W (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) : TreeCheckTailWalk A :=
  sourceWalk prims D Z K circuits settings top tree x
    (TreeCheckQueryBudget.ofBound bounded).step p (R top tree D A x z Z q bounded j p)

/-- The common premises of every field. -/
def AtWalk (F : ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C), TreeCheckTailWalk A → Prop) : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x →
      ∀ bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q, q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z),
          F top tree D A x z Z q bounded j p (W prims K circuits settings R top tree D A x z Z q bounded j p)

/-- S1. The walk is the actual run, and its boundaries and hybrids have the standard form. -/
def WalkSplit : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p W =>
    W.Split prims K circuits settings D top tree x Z p ∧ W.StandardTuples circuits D ∧
      ∀ c i, ((W.boundary c).batch.ctx i).self = i

/-- S2. The counted bad runs pass the boundary of batch `j` with its jobs and its tuples. -/
def WalkBad : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p W =>
    (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j ∧
      W.Unreached prims K circuits settings D top tree x z j ∧
      W.Consistent prims K circuits settings D top tree x z Z j

/-- S3. The bad record of batch `j` comes from the opening head of the boundary. -/
def WalkOpening : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p W =>
    W.IndexedOpening prims K circuits settings top tree D A x z Z j

/-- S4. Each live checkpoint is a position of one bounded real execution. -/
def WalkLogs : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p W =>
    W.LogSources prims K circuits settings top tree D A x z Z j q (TreeCheckQueryBudget.ofBound bounded) p

/-- The log fields not supplied by the actual compiler: a corrupt participant
at a live cut and a bounded full-execution position for that checkpoint. -/
def WalkPositions : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p W =>
    ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
        (.inl (c, o)) →
      (∃ i, i ∈ D.1) ∧
      Nonempty (TreeCheckPrefixPosition prims circuits settings D A x z Z
        (TreeCheckQueryBudget.ofBound bounded)
        ((W.cut prims K circuits settings D Z).count (.inl (c, o))) o)

set_option linter.constructorNameAsVariable false in
/-- The compiler fixes the counted log, step budget and actual setup prefix. -/
theorem walkLogs_of_positions (positions : WalkPositions prims K circuits settings R) :
    WalkLogs prims K circuits settings R := by
  intro hb top tree D A x z Z q dealt bounded small j p hp c o run live
  have atPosition := positions hb top tree D A x z Z q dealt bounded small j p hp
  with_reducible obtain ⟨corrupt, position⟩ := atPosition c o run live
  refine ⟨rfl, rfl, ?_, corrupt, position⟩
  with_reducible exact (sourceWalk_log_prefix prims D Z K circuits settings top tree x
    (TreeCheckQueryBudget.ofBound bounded).step p (R top tree D A x z Z q bounded j p) c o run)

/-- S5. The hybrid check after each live checkpoint. -/
def WalkHybrid : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p W =>
    (W.cut prims K circuits settings D Z).Queries prims K circuits settings top tree D A x z j ∧
      (W.cut prims K circuits settings D Z).Cache prims K circuits settings top tree D A x z j ∧
      (W.cut prims K circuits settings D Z).Prior prims K circuits settings top tree D A x z j ∧
      (W.cut prims K circuits settings D Z).Transport prims K circuits settings top tree D A x z j

/-- Only a local program identity and its remaining fuel are required of
successful decoding. No source construction or bad-event bound is assumed. -/
def LocalDecoding : Prop :=
  AtWalk prims K circuits settings R fun top tree D A x z Z q bounded j p _ =>
    Decodes D K circuits settings x (R top tree D A x z Z q bounded j p).decode

theorem walkSplit (decoderLaws : LocalDecoding prims K circuits settings R) :
    WalkSplit prims K circuits settings R := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  have sound := decoderLaws hb top tree D A x z Z q dealt bounded small j p hp
  exact ⟨sourceWalk_split prims D Z K circuits settings top tree x z _ p _ dealt hp sound,
    sourceWalk_standard prims D Z K circuits settings top tree x _ p _⟩

theorem sourceConstruction_of_fields
    (split : WalkSplit prims K circuits settings R) (bad : WalkBad prims K circuits settings R)
    (opening : WalkOpening prims K circuits settings R) (logs : WalkLogs prims K circuits settings R)
    (hybrid : WalkHybrid prims K circuits settings R) :
    TreeCheckTailWalkSourceConstruction prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨s, standard, self⟩ := split hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨jobs, unreached, consistent⟩ := bad hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨queries, cache, prior, transport⟩ := hybrid hb top tree D A x z Z q dealt bounded small j p hp
  exact ⟨W prims K circuits settings R top tree D A x z Z q bounded j p,
    { split := s, standard := standard, self := self, jobs := jobs, unreached := unreached,
      consistent := consistent,
      opening := opening hb top tree D A x z Z q dealt bounded small j p hp,
      logs := logs hb top tree D A x z Z q dealt bounded small j p hp,
      queries := queries, cache := cache, prior := prior, transport := transport }⟩

/-- The actual compiler and the same shared recipe feed the original source
target. The decoder and hybrid adapter are explicit construction data. -/
theorem sourceConstruction_of_recipe
    (decoderLaws : LocalDecoding prims K circuits settings R)
    (bad : WalkBad prims K circuits settings R)
    (opening : WalkOpening prims K circuits settings R)
    (logs : WalkLogs prims K circuits settings R)
    (hybrid : WalkHybrid prims K circuits settings R) :
    TreeCheckTailWalkSourceConstruction prims K circuits settings :=
  sourceConstruction_of_fields prims K circuits settings R
    (walkSplit prims K circuits settings R decoderLaws) bad opening logs hybrid

/-- The reduced source fields use one shared decoder and hybrid adapter;
setup-prefix provenance and the raw log/budget identities are derived. -/
theorem sourceConstruction_of_positions
    (decoderLaws : LocalDecoding prims K circuits settings R)
    (bad : WalkBad prims K circuits settings R)
    (opening : WalkOpening prims K circuits settings R)
    (positions : WalkPositions prims K circuits settings R)
    (hybrid : WalkHybrid prims K circuits settings R) :
    TreeCheckTailWalkSourceConstruction prims K circuits settings :=
  sourceConstruction_of_recipe prims K circuits settings R decoderLaws bad opening
    (walkLogs_of_positions prims K circuits settings R positions) hybrid

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.resume_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resume_start

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.next_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms next_split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.walk_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.walk_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.initial_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.decoded_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decoded_finish

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.sourceWalk_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.sourceWalk_log_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_log_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.walkSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkSplit

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.walkLogs_of_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkLogs_of_positions

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.sourceConstruction_of_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceConstruction_of_fields

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkDef.sourceConstruction_of_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceConstruction_of_positions


end TreeCheckWalkDef
end ThresholdLeanXmssSecurity
