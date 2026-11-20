import ThresholdLeanXmss.Scheme
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk

/-!
# The check start and the run of a ceremony that stops at a check

`CheckStart` is the start of the check of one batch, and `checkFrom` is the real check from that
start in `streamWorld`. `SoundCase` collects the premises of the pilot at a start, with the budget
`CheckBudget`. `cutRun k` is the ceremony program of one operator that stops at the check of the batch with the tag
`k` (`Paused.stop`). `CheckBad` is an accepted check with a wrong tuple or split copies. `OnPath`
states that each output of a step with `H` fixed is an output of the program
(`executeRounds_onPath`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The game after the PRF hop -/

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

/-- The start of the check of one batch, namely the inputs of `pilotOutputs`. -/
structure CheckStart (C : Committee) (σ : Type) where
  keys : C.Party → Keys C
  prss : C.Party → PrssKeys C
  counts : List ℕ
  x : C.Party → List (Tuple C)
  L : ℕ
  tg : ℕ
  st : σ
  world : StreamState C

/-- The real check of one batch from its start, answered by `streamWorld`. -/
def checkFrom (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (c : CheckStart C net.State) :
    ProbComp ((net.State × (C.Party → Option Unit)) × StreamState C) :=
  (simulateQ (streamWorld prims D) (pilotRun K D net c.keys c.prss c.counts c.x c.L c.tg c.st)).run c.world

/-- The honest view of the tuples. -/
def honestTuples (D : C.Coalition) (x : C.Party → List (Tuple C)) : C.Party → Option (List (Tuple C)) :=
  fun i => if i ∈ D.1 then none else some (x i)

/-- The counts of a check start fit the budget `q` of the game and the round bound `step`. The cache
has the premises of the pilot with at most `2 q + 2 gameCoinKeys` charged inputs of the coin keys
with the calls of the check, at most `2 gameCoinKeys` earlier expansion keys and at most
`2 splitBudget` digest salts, and the batch count is a count of the ceremonies. -/
def CheckBudget (q step : ℕ) {σ : Type} (c : CheckStart C σ) : Prop :=
  ∃ (seen : Finset (Query C)) (expansionKeys : Finset HashOutput) (salts : Finset (List Bit)) (split : ℕ),
    PilotCache c.L c.world.1 seen expansionKeys salts split ∧
    seen.card + checkRounds c.counts.sum * step ≤ 2 * q + 2 * gameCoinKeys circuits settings runLimit C ∧
    expansionKeys.card ≤ 2 * gameCoinKeys circuits settings runLimit C ∧
    salts.card ≤ 2 * splitBudget settings runLimit C q ∧ checkRounds c.counts.sum * step ≤ q ∧
    c.counts.sum ∈ batchCounts circuits settings

/-- A check that the pilot bounds. The start has the premises of the pilot, and the honest copies of
the tuples agree on a wrong tuple. -/
def SoundCase (D : C.Coalition) (q step : ℕ) {σ : Type} (c : CheckStart C σ) : Prop :=
  TupleInputs K c.counts D c.x ∧ WrongTuple D c.x ∧ MultVerifyAgree D (honestTuples D c.x) ∧
    PrssKeysAgree D c.prss ∧ StreamsFresh D c.L c.prss c.world.2 ∧
    CheckBudget circuits settings runLimit q step c

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The program that stops at a check -/

/-- The start of the check of one batch at one operator. It is the context of the ceremony, the
tuples of the batch and the run state at the start of the check. -/
structure CheckPoint (C : Committee) where
  ctx : Context C
  tuples : List (Tuple C)
  state : RunState C

/-- A program of one operator that stops at most one time at the start of a check. It ends with a
value, or it stops with the start of the check and the rest of the program from the run state after
the check. -/
structure Paused (K : Constants C E) (α : Type) where
  run : PartyM C E RealSpec (α ⊕ (CheckPoint C × (RunState C → PartyM C E RealSpec α)))

/-- The real check from a start, then the rest. -/
def resumeAt (K : Constants C E) {α : Type} (point : CheckPoint C) (rest : RunState C → PartyM C E RealSpec α) :
    PartyM C E RealSpec α :=
  (check K point.ctx (realCheckBuildingBlocks K point.ctx) point.tuples).run point.state >>= fun r => rest r.2

/-- A program that stops at a check, run to its end with the real check at the stop. -/
def Paused.finish {K : Constants C E} {α : Type} (x : Paused K α) : PartyM C E RealSpec α :=
  x.run >>= fun o => match o with
    | .inl a => pure a
    | .inr (point, rest) => resumeAt K point rest

instance (K : Constants C E) : Monad (Paused K) where
  pure a := ⟨pure (.inl a)⟩
  bind x f := ⟨x.run >>= fun o => match o with
    | .inl a => (f a).run
    | .inr (point, rest) => pure (.inr (point, fun s => rest s >>= fun a => (f a).finish))⟩

/-- A program with no stop. -/
def Paused.lift {K : Constants C E} {α : Type} (p : PartyM C E RealSpec α) : Paused K α :=
  ⟨Sum.inl <$> p⟩

/-- The stop at the start of a check. The value is the run state after the check. -/
def Paused.stop {K : Constants C E} (point : CheckPoint C) : Paused K (RunState C) :=
  ⟨pure (.inr (point, pure))⟩

/-- A program on the counters of the ceremonies that stops at most one time at a check. -/
abbrev CutM (K : Constants C E) := StateT (ℕ × ℕ) (Paused K)

/-- A program on the counters with no stop. -/
def CutM.lift {K : Constants C E} {α : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) : CutM K α :=
  StateT.mk fun s => Paused.lift (x.run s)

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The part of `runJobs` before `verify`. It gives the tuples of the check, the outputs after
`Rerand`, their count and the widths of the jobs. The code is the code of `runJobs` in
`ThresholdLeanXmss/Scheme.lean`. -/
def runJobsHead {ι : Type} {G : OracleSpec ι} (buildingBlocks : RunBuildingBlocks C E G) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    RunM C E G (List (Tuple C) × Shares C Bit × ℕ × List ℕ) := do
  let (wires, tuples) ← (List.range (depth jobs)).foldlM (init := (inputs, ([] : List (Tuple C))))
    fun (wires, tuples) layer => do
      let gates := jobs.zipIdx.flatMap fun (job, k) =>
        (job.layers.getD layer []).map fun ab => (k, ab)
      let x : Shares C Bit := fun T g => match gates[g]? with
        | some (k, ab) => ab.1.share (wires.getD k fun _ => []) K.publicTerm T | none => 0
      let y : Shares C Bit := fun T g => match gates[g]? with
        | some (k, ab) => ab.2.share (wires.getD k fun _ => []) K.publicTerm T | none => 0
      let z ← buildingBlocks.mult x y gates.length
      let wires := wires.zipIdx.map fun (w, k) T =>
        w T ++ ((gates.zipIdx.filter (·.1.1 = k)).map fun (_, g) => z T g)
      pure (wires, tuples ++ [⟨x, y, z, gates.length, buildingBlocks.mode⟩])
  let outputs := jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)
  let v : Shares C Bit := fun T g => match outputs[g]? with
    | some (k, a) => a.share (wires.getD k fun _ => []) K.publicTerm T | none => 0
  let v' ← buildingBlocks.rerand v outputs.length
  pure (tuples ++ [⟨v, one K, v', outputs.length, .peer⟩], v', outputs.length, jobs.map (·.outputs.length))

/-- The batch with the tag `k` of a ceremony at operator `ctx.self`. It runs the batch up to its
check, stops with the start of the check, and then opens the outputs as `runJobs` does. -/
def cutBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    CutM K (Option (List (List Bit))) := do
  let (label, k) ← get
  let inputs ← CutM.lift (StateT.lift (jobs.mapM (inputShares ctx)))
  let (head, state) ← CutM.lift (StateT.lift ((runJobsHead K (realRunBuildingBlocks K ctx settings.mode)
    (jobs.map (circuits parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩))
  let after ← StateT.lift (Paused.stop ⟨ctx, head.1, state⟩)
  let (opened, final) ← CutM.lift (StateT.lift
    (((realRunBuildingBlocks K ctx settings.mode).output head.2.1 head.2.2.1).run after))
  set (final.label, k + 1)
  pure (some (head.2.2.2.zipIdx.map fun (width, j) => vector width fun g => opened ((head.2.2.2.take j).sum + g)))

/-- One ceremony at operator `i`, as in `newTree`, that stops at the check of the batch with the tag
`k`. -/
def cutRun (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) : CutM K (Option (List (List Bit))) := do
  let prss ← CutM.lift (StateT.lift (prssSetup i))
  let ctx : Context C := ⟨i, keys, prss⟩
  batched settings.batchSize (fun js => do
    let (_, tag) ← get
    if tag = k then cutBatch K circuits settings ctx keys.parameter js
    else CutM.lift (realBatch K circuits settings.mode ctx keys.parameter js)) jobs

/-- The outcome of a program that stops at a check. -/
abbrev CutOutcome (C : Committee) :=
  Option TreeOutput ⊕ (CheckPoint C × (RunState C → PartyM C E RealSpec (Option TreeOutput)))

variable (prims : Primitives) (runLimit : ℕ) (budget : StartBudget)

/-- Each honest operator stops at the start of the check in an outcome of the prefix. -/
def AllStopped (D : C.Coalition) (outcomes : C.Party → Option (CutOutcome (E := E) C)) : Prop :=
  ∀ i, i ∉ D.1 → ∃ point rest, outcomes i = some (.inr (point, rest))

/-- An accepted check of batch `k` with a wrong tuple or split copies, from a start with fresh
streams, with no global event at the start of the check and no collision of two history and digest
cells at its end. -/
def CheckBad (D : C.Coalition) {σ : Type}
    (r : Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C)) : Prop :=
  ∃ c out, r = (some c, some out) ∧ (∃ i, i ∉ D.1 ∧ out.1.2 i = some ()) ∧
    (WrongTuple D c.x ∨ ¬ MultVerifyAgree D (honestTuples D c.x)) ∧ StreamsFresh D c.L c.prss c.world.2 ∧
    ¬ GlobalEvent c.world ∧ ¬ DomainCollision SplitHashDomain out.2.1

/-- The error of a run of `tree` whose PRSS setup repeats the derivation input of a hidden key, with
at most `budget.hiddenKeys` keys under each name at the start of the run. -/
def freshErrorAt (C : Committee) (tree : Tree) : ℝ :=
  (treeSetups tree * prssKeyCount C * (budget.hiddenKeys + treeSetups tree) : ℕ) / 2 ^ 256

/-! ## The hops of a run -/

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The monad of a program that stops at a check -/

section Paused

variable {K : Constants C E}

omit [Fintype E] [DecidableEq E] in
theorem Paused.ext_run {α : Type} {x y : Paused K α} (h : x.run = y.run) : x = y := by
  cases x
  cases y
  cases h
  rfl

omit [Fintype E] [DecidableEq E] in
theorem Paused.run_pure {α : Type} (a : α) : (pure a : Paused K α).run = pure (.inl a) := rfl

omit [Fintype E] [DecidableEq E] in
theorem Paused.run_bind {α β : Type} (x : Paused K α) (f : α → Paused K β) :
    (x >>= f).run = x.run >>= fun o => match o with
      | .inl a => (f a).run
      | .inr (point, rest) => pure (.inr (point, fun s => rest s >>= fun a => (f a).finish)) := rfl

omit [Fintype E] [DecidableEq E] in
theorem Paused.finish_pure {α : Type} (a : α) : (pure a : Paused K α).finish = pure a := by
  simp [Paused.finish, Paused.run_pure]

omit [Fintype E] [DecidableEq E] in
theorem Paused.finish_bind {α β : Type} (x : Paused K α) (f : α → Paused K β) :
    (x >>= f).finish = x.finish >>= fun a => (f a).finish := by
  simp only [Paused.finish, Paused.run_bind, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with a | ⟨point, rest⟩
  · simp
  · simp [resumeAt, bind_assoc]

instance (K : Constants C E) : LawfulMonad (Paused K) := LawfulMonad.mk'
  (id_map := fun x => by
    refine Paused.ext_run ?_
    change (x >>= fun a => pure a).run = x.run
    rw [Paused.run_bind]
    conv_rhs => rw [← bind_pure x.run]
    refine bind_congr fun o => ?_
    rcases o with a | ⟨point, rest⟩
    · rfl
    · simp [Paused.finish_pure])
  (pure_bind := fun a f => by
    refine Paused.ext_run ?_
    rw [Paused.run_bind, Paused.run_pure, pure_bind])
  (bind_assoc := fun x f g => by
    refine Paused.ext_run ?_
    simp only [Paused.run_bind, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with a | ⟨point, rest⟩
    · rfl
    · simp [Paused.finish_bind, bind_assoc])

end Paused

/-! ## The cut program run to its end -/

section CutHop

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- `runJobs` is `runJobsHead`, then `verify`, then `output`. -/
theorem runJobs_eq_head {ι : Type} {G : OracleSpec ι} (buildingBlocks : RunBuildingBlocks C E G)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    runJobs K buildingBlocks jobs inputs = runJobsHead K buildingBlocks jobs inputs >>= fun head =>
      buildingBlocks.verify head.1 >>= fun _ => buildingBlocks.output head.2.1 head.2.2.1 >>= fun opened =>
        pure (head.2.2.2.zipIdx.map fun (width, j) => vector width fun g => opened ((head.2.2.2.take j).sum + g)) := by
  unfold runJobs runJobsHead
  simp only [bind_assoc, pure_bind]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem CutM.lift_run {α : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) (s : ℕ × ℕ) :
    (CutM.lift (K := K) x).run s = Paused.lift (x.run s) := rfl

end CutHop

/-! ## The rest after a stop starts with a round -/

section AbortHop

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem mem_support_optionT_bind {α β : Type} (x : PartyM C E RealSpec α) (f : α → PartyM C E RealSpec β)
    (o : Option β) (ho : o ∈ support (x >>= f).run) :
    o = none ∨ ∃ a, some a ∈ support x.run ∧ o ∈ support (f a).run := by
  rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at ho
  obtain ⟨a, ha, ho⟩ := ho
  rcases a with _ | a
  · left
    simpa using ho
  · exact Or.inr ⟨a, ha, ho⟩

variable {K : Constants C E}

end AbortHop

/-! ## A predicate with a pure rule and a bind rule -/

section Closed

variable {m : Type → Type} [Monad m] [LawfulMonad m] (P : ∀ {β : Type}, m β → Prop)
  (hpure : ∀ {β : Type} (b : β), P (pure b))
  (hbind : ∀ {β γ : Type} (x : m β) (f : β → m γ), P x → (∀ b, P (f b)) → P (x >>= f))

include hpure hbind in
theorem closed_mapM {β γ : Type} (f : β → m γ) (hf : ∀ b, P (f b)) : ∀ l : List β, P (l.mapM f)
  | [] => hpure []
  | b :: l => by
    rw [List.mapM_cons]
    exact hbind _ _ (hf b) fun _ => hbind _ _ (closed_mapM f hf l) fun _ => hpure _

include hpure hbind in
theorem closed_batched (size : ℕ) (run : List Job → m (Option (List (List Bit)))) (hr : ∀ js, P (run js))
    (jobs : List Job) : P (batched size run jobs) :=
  hbind _ _ (closed_mapM P hpure hbind run hr _) fun _ => hpure _

omit [LawfulMonad m] in
include hpure hbind in
theorem closed_ceremonyOutput (lift : ∀ {β : Type}, OracleComp HashSpec β → m β)
    (hl : ∀ {β : Type} (oa : OracleComp HashSpec β), P (lift oa))
    (run : List Job → m (Option (List (List Bit)))) (hr : ∀ js, P (run js)) (parameter : PublicParameter)
    (top : TopTree) (tree : Tree) : P (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine hbind _ _ (hr topJobs) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · exact hbind _ _ (hl _) fun _ => hpure _
  | bottom b =>
    simp only [ceremonyOutput]
    refine hbind _ _ (hr (bottomJobs b)) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · refine hbind _ _ (hl _) fun root => hbind _ _ (hl _) fun base => hbind _ _ (hl _) fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · exact hpure _
      · refine hbind _ _ (hr _) fun o => ?_
        rcases o with _ | values
        · exact hpure _
        · refine hbind _ _ (hl _) fun path => hbind _ _ (hl _) fun topRoot => ?_
          split_ifs
          · exact hpure _
          · exact hpure _

end Closed

section AbortHopProof

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
theorem output_run (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) (st : RunState C) :
    ((realRunBuildingBlocks (G := RealSpec) K ctx mode).output v count).run st =
      openRep K ctx v count >>= fun a => pure (a, st) := rfl

omit [Fintype E] [DecidableEq E] in
/-- The check with the count `0` makes no round and keeps the run state. -/
theorem check_run_zero (ctx : Context C) (tuples : List (Tuple C)) (hcount : (tuples.map (·.count)).sum = 0)
    (st : RunState C) :
    (check (G := RealSpec) K ctx (realCheckBuildingBlocks K ctx) tuples).run st = pure ((), st) := by
  unfold check
  dsimp only
  rw [ite_eq_left hcount]
  rfl

end AbortHopProof

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

/-! ## The path of an honest operator in a run -/

section Path

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- The program that a step stands for. -/
def stepProgram {α : Type} : Step C E G α → OracleComp (PartySpec C E G) (Option α)
  | .done out => pure out
  | .wait outbox resume =>
    OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inr outbox))) >>= resume
  | .call input resume => OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inr input)) >>= resume

/-- Each output of the step with `H` fixed to `h` is an output of the program with `H` fixed to
`h`. -/
def OnPath (h : Query C → HashOutput) {α : Type} (program : OracleComp (PartySpec C E G) (Option α))
    (step : Step C E G α) : Prop :=
  ∀ a, some a ∈ support (simulateQ (fixHash h) (stepProgram step)) → some a ∈ support (simulateQ (fixHash h) program)

theorem onPath_done_none (h : Query C → HashOutput) {α : Type} (program : OracleComp (PartySpec C E G) (Option α)) :
    OnPath h program (.done none) := by
  intro a ha
  simp [stepProgram] at ha

theorem simulateQ_fixHash_query_bind (h : Query C → HashOutput) {α : Type} (t : (PartySpec C E G).Domain)
    (k : (PartySpec C E G).Range t → OracleComp (PartySpec C E G) α) :
    simulateQ (fixHash h) (OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) t) >>= k) =
      fixHash h t >>= fun r => simulateQ (fixHash h) (k r) := by
  simp [simulateQ_bind]

end Path

section Walk

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

/-- The local steps of an honest operator in `streamWorld` grow the hash cache, and they reach a step
on the path of the program for each good `h` that agrees with the new cache. -/
theorem advance_onPath {ι : Type} {G : OracleSpec ι} {α : Type} (oa : OracleComp (PartySpec C E G) (Option α)) :
    ∀ s z, z ∈ support ((simulateQ (streamWorld prims D) (free (advance oa))).run s) →
      s.1 ≤ z.2.1 ∧ ∀ h, Good prims h → Agrees h z.2.1 → OnPath h oa z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro s z hz
    simp only [advance_pure, free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun h _ _ a ha => by simpa [stepProgram] using ha⟩
  | query_bind t k ih =>
    intro s z hz
    rcases t with (q | outbox) | input
    · change z ∈ support ((simulateQ (streamWorld prims D) (free (OracleComp.lift
        (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)))).run s) at hz
      simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rw [simulateQ_HasQuery_query] at hy
      obtain ⟨hle₁, hanswer⟩ := streamWorld_local (E := E) (G := G) prims D q s y hy
      obtain ⟨hle₂, hpath⟩ := ih y.1 y.2 z hz
      refine ⟨hle₁.trans hle₂, fun h hg ha a hmem => ?_⟩
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
      exact ⟨y.1, hanswer h hg (ha.mono hle₂), hpath h hg ha a hmem⟩
    · change z ∈ support ((simulateQ (streamWorld prims D) (free (pure (Step.wait outbox k)))).run s) at hz
      simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨le_rfl, fun _ _ _ _ ha => ha⟩
    · change z ∈ support ((simulateQ (streamWorld prims D) (free (pure (Step.call input k)))).run s) at hz
      simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨le_rfl, fun _ _ _ _ ha => ha⟩

/-- A round of the honest operators in `streamWorld` grows the hash cache and keeps each honest
step on the path of its program. -/
theorem stepRound_onPath {α Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α))
    (s : HashCache C × HiddenCache C) (y : (A.State × (C.Party → Step C E RealSpec α) ×
      (C.Party → C.Party → Option (Msg E))) × (HashCache C × HiddenCache C))
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D' A noFunctionality st steps)).run s)) :
    s.1 ≤ y.2.1 ∧ ∀ h, Good prims h → Agrees h y.2.1 → (∀ i, i ∉ D'.1 → OnPath h (program i) (steps i)) →
      ∀ i, i ∉ D'.1 → OnPath h (program i) (y.1.2.1 i) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D'.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D'.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRound at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, ha, w, hw, rfl⟩ := hy
  have hseq := sequenceFin_streamWorld prims D (fun j v c => j ∉ D'.1 → ∀ h, Good prims h → Agrees h c →
      OnPath h (program j) (steps j) → OnPath h (program j) v) _
    (fun j b c c' hq hle hj h hg hagree => hq hj h hg (hagree.mono hle)) (fun j s' y hy hj h hg hagree hon => ?_)
    a.2 w hw
  · exact ⟨(streamWorld_run_mono prims D _ s a ha).trans (streamWorld_run_mono prims D _ a.2 w hw),
      fun h hg hagree hon i hi => hseq i hi h hg hagree (hon i hi)⟩
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [← hsj]
    exact hon
  · simp only [hsj, hj, ↓reduceIte] at hy
    obtain ⟨hle, hpath⟩ := advance_onPath prims D _ s' y hy
    intro a' hmem
    rw [hsj] at hon
    refine hon a' ?_
    rw [stepProgram, simulateQ_fixHash_query_bind, mem_support_bind_iff]
    exact ⟨_, by simp [fixHash], hpath h hg hagree a' hmem⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact onPath_done_none h _

theorem onPath_output {α : Type} (h : Query C → HashOutput) (program : OracleComp (PartySpec C E RealSpec) (Option α))
    (step : Step C E RealSpec α) (hpath : OnPath h program step) (a : α) (ha : step.output = some a) :
    some a ∈ support (simulateQ (fixHash h) program) := by
  rcases step with out | _ | _
  · cases ha
    exact hpath a (by simp [stepProgram])
  · cases ha
  · cases ha

/-- The rounds of the honest operators in `streamWorld` give only outputs on the paths of their
programs, from steps on these paths. -/
theorem executeRounds_onPath {α Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α)) (fuel : ℕ) :
    ∀ st steps s z, z ∈ support ((simulateQ (streamWorld prims D)
      (executeRounds worldRoles D' A noFunctionality fuel st steps)).run s) →
      ∀ h, Good prims h → Agrees h z.2.1 → (∀ i, i ∉ D'.1 → OnPath h (program i) (steps i)) →
        ∀ i, i ∉ D'.1 → ∀ a, z.1.2 i = some a → some a ∈ support (simulateQ (fixHash h) (program i)) := by
  induction fuel with
  | zero =>
    intro st steps s z hz h _ _ hon i hi a ha
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact onPath_output h _ _ (hon i hi) a ha
  | succ fuel ih =>
    intro st steps s z hz h hg hagree hon i hi a ha
    unfold executeRounds at hz
    split_ifs at hz with hdone
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact onPath_output h _ _ (hon i hi) a ha
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rcases y with ⟨⟨state, steps', sent⟩, c⟩
      obtain ⟨-, hstep⟩ := stepRound_onPath prims D D' A st steps program s _ hy
      exact ih state steps' c z hz h hg hagree
        (hstep h hg (hagree.mono (streamWorld_run_mono prims D _ c z hz)) hon) i hi a ha

end Walk

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.executeRounds_onPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.executeRounds_onPath
