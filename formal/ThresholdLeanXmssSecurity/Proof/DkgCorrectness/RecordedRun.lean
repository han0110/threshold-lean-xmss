import ThresholdLeanXmss.Scheme
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cores

/-!
# The recorded run of a ceremony and its fuel

`executePhaseR` is `executePhase` with a record for each party. `recRun` is the ceremony program that records the start, the opened outputs and the tuples
of each batch (`RecEvent`), and `dropRecS_recRun` states that it is `ceremonyRun` with the record
dropped. `recCheckOpenWith`, `recBatchAt` and `recRunAt` take the place of the opening record as
an argument `early`. With `early` the pass of a check is recorded before the exchange of `OpenRep`,
and with `early = false` they are `recCheckOpen`, `recBatch` and `recRun`. `startsOf`, `openingsOf`
and `batchOutputsOf` read the record. The section `Fuel` bounds
the rounds that an honest program uses (`Within`, `RunWithin`, `within_newTree`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The ghost executor -/

section Ghost

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α R : Type}

/-- A program stopped at its output with its record, at its next round, or at its next call. Copy
of `Step` of `ThresholdLeanXmss/Scheme.lean` (306) with the record. -/
inductive RStep (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) (α R : Type) where
  | done (out : Option α) (record : R)
  | wait (outbox : Mail C E) (resume : Mail C E → OracleComp (PartySpec C E G) (Option α × R))
  | call (input : ι) (resume : G input → OracleComp (PartySpec C E G) (Option α × R))

/-- A ghost step with its record dropped. -/
def RStep.erase : RStep C E G α R → Step C E G α
  | .done out _ => .done out
  | .wait outbox resume => .wait outbox fun inbox => Prod.fst <$> resume inbox
  | .call input resume => .call input fun r => Prod.fst <$> resume r

/-- Run the local steps of a program up to its output, its next round or its next call. Copy of
`advance` of `ThresholdLeanXmss/Scheme.lean` (314) with the record. -/
def advanceR : OracleComp (PartySpec C E G) (Option α × R) → OracleComp (LocalSpec C) (RStep C E G α R)
  | .pure out => pure (.done out.1 out.2)
  | .liftBind (Sum.inl (Sum.inl q)) k => do
      let r ← OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q)
      advanceR (k r)
  | .liftBind (Sum.inl (Sum.inr outbox)) k => pure (.wait outbox k)
  | .liftBind (Sum.inr input) k => pure (.call input k)

/-- The outbox of a ghost step. Copy of `Step.outbox` of `ThresholdLeanXmss/Scheme.lean` (1459). -/
def RStep.outbox : RStep C E G α R → Mail C E
  | .wait outbox _ => outbox
  | _ => fun _ => none

/-- The message to `j` in a round, with the abort frame of an operator that aborted, also with its
record. Copy of `Step.delivered` of `ThresholdLeanXmss/Scheme.lean` (1464). -/
def RStep.delivered : RStep C E G α R → Mail C E
  | .wait outbox _ => outbox
  | .done none _ => fun _ => some .abort
  | _ => fun _ => none

/-- The output of a ghost step. Copy of `Step.output` of `ThresholdLeanXmss/Scheme.lean` (1469). -/
def RStep.output : RStep C E G α R → Option α
  | .done out _ => out
  | _ => none

/-- A ghost step is done. Copy of `Step.isDone` of `ThresholdLeanXmss/Scheme.lean` (1473). -/
def RStep.isDone : RStep C E G α R → Prop
  | .done _ _ => True
  | _ => False

/-- The call of a ghost step. Copy of `Step.callInput` of `ThresholdLeanXmss/Scheme.lean` (1477). -/
def RStep.callInput : RStep C E G α R → Option ι
  | .call input _ => some input
  | _ => none

/-- The record of a ghost step, or `blank` before the end. -/
def RStep.record (blank : R) : RStep C E G α R → R
  | .done _ record => record
  | _ => blank

theorem RStep.isDone_erase (s : RStep C E G α R) : s.erase.isDone = s.isDone := by
  cases s <;> rfl

/-- With the records dropped, `advanceR` is `advance`. -/
theorem advanceR_erase (oa : OracleComp (PartySpec C E G) (Option α × R)) :
    RStep.erase <$> advanceR oa = advance (Prod.fst <$> oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rcases t with (t | outbox) | input
    · have h : ∀ {γ : Type} (g : (LocalSpec C).Range t → OracleComp (PartySpec C E G) (Option γ)),
          advance (liftM (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) >>= g) =
            OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (g r) :=
        fun g => rfl
      have hR : ∀ (g : (LocalSpec C).Range t → OracleComp (PartySpec C E G) (Option α × R)),
          advanceR (liftM (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) >>= g) =
            OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advanceR (g r) :=
        fun g => rfl
      rw [map_bind, h, hR, map_bind]
      simp only [ih]
    · rw [map_bind]
      rfl
    · rw [map_bind]
      rfl

end Ghost

section Execution

variable {C : Committee} {E : Type} {m : Type → Type} [Monad m] {I O L Rs Ia α ρ : Type}

/-- One synchronous step of the ghost run. Copy of `stepRound` of `ThresholdLeanXmss/Scheme.lean`
(1503) with the records. An operator that the original sets to `.done none` gets the record
`blank`. -/
def stepRoundR (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs)
    (blank : ρ) (state : A.State) (steps : C.Party → RStep C E (CallSpec I O) α ρ) :
    m (A.State × (C.Party → RStep C E (CallSpec I O) α ρ) × (C.Party → C.Party → Option (Msg E))) := do
  if (∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧ ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone then
    let (state, outputs) ← runFunctionality Ro D A F state fun i => if i ∈ D.1 then none else (steps i).callInput
    let steps' ← OverPermutation.sequenceFin fun j => match steps j with
      | .call _ resume => if j ∈ D.1 then pure (RStep.done none blank) else Ro.honest (advanceR (resume (outputs j)))
      | step => pure step
    pure (state, steps', fun _ _ => none)
  else
    let (state, sent) ← Ro.adversary (A.round state fun c i =>
      if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none)
    let steps' ← OverPermutation.sequenceFin fun j => match steps j with
      | .done out record => pure (RStep.done out record)
      | .wait _ resume => if j ∈ D.1 then pure (RStep.done none blank) else
          Ro.honest (advanceR (resume fun k => if k ∈ D.1 then sent k j else (steps k).delivered j))
      | .call _ _ => pure (RStep.done none blank)
    pure (state, steps', sent)

/-- Run the honest programs of the ghost run for at most `fuel` steps. It gives the last step of each
operator, with the record of each operator that is done. Copy of `executeRounds` of
`ThresholdLeanXmss/Scheme.lean` (1523). -/
def executeRoundsR (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs)
    (blank : ρ) : ℕ → A.State → (C.Party → RStep C E (CallSpec I O) α ρ) →
      m (A.State × (C.Party → RStep C E (CallSpec I O) α ρ))
  | 0, state, steps => pure (state, steps)
  | fuel + 1, state, steps =>
    if ∀ i, i ∉ D.1 → (steps i).isDone then pure (state, steps) else do
    let (state, steps, _) ← stepRoundR Ro D A F blank state steps
    executeRoundsR Ro D A F blank fuel state steps

/-- The first steps of the honest programs of the ghost run. Copy of `startSteps` of
`ThresholdLeanXmss/Scheme.lean` (1532). -/
def startStepsR (Ro : Roles C m) (D : C.Coalition) (blank : ρ)
    (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    m (C.Party → RStep C E (CallSpec I O) α ρ) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure (RStep.done none blank) else Ro.honest (advanceR (program i))

/-- One phase of the ghost run of at most `fuel` steps. Copy of `executePhase` of
`ThresholdLeanXmss/Scheme.lean` (1537). -/
def executePhaseR (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs)
    (blank : ρ) (fuel : ℕ) (state : A.State)
    (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    m (A.State × (C.Party → RStep C E (CallSpec I O) α ρ)) := do
  executeRoundsR Ro D A F blank fuel state (← startStepsR Ro D blank program)

variable [LawfulMonad m]

end Execution

/-! ## The recorded program -/

section Recorded

variable {C : Committee} {E : Type}

/-- The start of the check of a batch at one operator. It has the mode, the jobs, the parameter and
the circuits of the batch, the input sharings, the products `zs` of the AND layers, the sharing `v'`
after `Rerand`, the context and the run state. -/
structure BatchStart (C : Committee) where
  mode : ReshareMode
  jobs : List Job
  parameter : PublicParameter
  circuits : List Circuit
  inputs : List (C.Term → List Bit)
  zs : ℕ → Shares C Bit
  v' : Shares C Bit
  ctx : Context C
  state : RunState C

/-- An event of the record of one operator. `start` is the start of the check of a batch, `opened` is
the inbox of `OpenRep` with the sharing that it opens, and `output` is the batch output. -/
inductive RecEvent (C : Committee) (E : Type) where
  | start (batch : BatchStart C)
  | opened (v' : Shares C Bit) (inbox : Mail C E)
  | output (outputs : List (List Bit))

/-- A program of one operator with a record below the failure. An operator that aborts keeps the
events that it recorded before. -/
abbrev RecM (C : Committee) (E : Type) := OptionT (WriterT (List (RecEvent C E)) (OracleComp (PartySpec C E RealSpec)))

/-- A program with no record. -/
def RecM.lift {α : Type} (p : PartyM C E RealSpec α) : RecM C E α := OptionT.mk (liftM p.run)

/-- Record events. -/
def RecM.record (events : List (RecEvent C E)) : RecM C E PUnit :=
  OptionT.lift (tell events : WriterT (List (RecEvent C E)) (OracleComp (PartySpec C E RealSpec)) PUnit)

/-- A recorded program with its record dropped. -/
def dropRec : RecM C E →ᵐ PartyM C E RealSpec where
  toFun _ x := OptionT.mk (dropLog.toFun _ x.run)
  toFun_pure' a := OptionT.ext (by
    change dropLog.toFun _ (pure (some a)) = pure (some a)
    exact dropLog.toFun_pure' _)
  toFun_bind' x f := OptionT.ext (by
    simp only [OptionT.run_mk, OptionT.run_bind, Option.elimM]
    rw [dropLog.toFun_bind']
    refine bind_congr fun o => ?_
    cases o with
    | none => exact dropLog.toFun_pure' _
    | some a => rfl)

theorem dropRec_lift {α : Type} (p : PartyM C E RealSpec α) : dropRec (RecM.lift p) = p :=
  OptionT.ext (dropLog_liftM _)

theorem dropRec_record (events : List (RecEvent C E)) : dropRec (RecM.record events) = pure PUnit.unit :=
  OptionT.ext (by
    change dropLog.toFun _ ((tell events : WriterT (List (RecEvent C E)) (OracleComp (PartySpec C E RealSpec)) PUnit) >>=
      fun u => pure (some u)) = pure (some PUnit.unit)
    rw [dropLog.toFun_bind', dropLog_tell, pure_bind, dropLog.toFun_pure'])

/-- A recorded program on a state with its record dropped. -/
def dropRecS {S : Type} : StateT S (RecM C E) →ᵐ StateT S (PartyM C E RealSpec) where
  toFun _ x := StateT.mk fun s => dropRec (x.run s)
  toFun_pure' a := StateT.ext fun s => by
    simp only [StateT.run_mk, StateT.run_pure, MonadHom.mmap_pure]
  toFun_bind' x f := StateT.ext fun s => by
    simp only [StateT.run_mk, StateT.run_bind, MonadHom.mmap_bind]

/-- A program on a state with no record. -/
def RecM.liftS {S α : Type} (x : StateT S (PartyM C E RealSpec) α) : StateT S (RecM C E) α :=
  StateT.mk fun s => RecM.lift (x.run s)

theorem dropRecS_liftS {S α : Type} (x : StateT S (PartyM C E RealSpec) α) :
    dropRecS (RecM.liftS x) = x :=
  StateT.ext fun s => dropRec_lift (x.run s)

theorem dropRecS_record {S : Type} (events : List (RecEvent C E)) :
    dropRecS (StateT.lift (RecM.record events) : StateT S (RecM C E) PUnit) = pure PUnit.unit :=
  StateT.ext fun s => by
    change dropRec (RecM.record events >>= fun a => pure (a, s)) = pure (PUnit.unit, s)
    rw [MonadHom.mmap_bind, dropRec_record, pure_bind, MonadHom.mmap_pure]

theorem dropRecS_get {S : Type} : dropRecS (get : StateT S (RecM C E) S) = get :=
  StateT.ext fun s => by
    change dropRec (pure (s, s)) = pure (s, s)
    exact MonadHom.mmap_pure _ _

theorem dropRecS_set {S : Type} (t : S) : dropRecS (set t : StateT S (RecM C E) PUnit) = set t :=
  StateT.ext fun _ => by
    change dropRec (pure (PUnit.unit, t)) = pure (PUnit.unit, t)
    exact MonadHom.mmap_pure _ _

end Recorded

/-! ## The support of a recorded program -/

section RecSupport

variable {C : Committee} {E : Type}

theorem mem_support_recM_bind {α β : Type} (x : RecM C E α) (f : α → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (x >>= f).run.run) :
    ∃ z₁ ∈ support x.run.run, (z₁.1 = none ∧ z = (none, z₁.2)) ∨
      ∃ a, z₁.1 = some a ∧ ∃ z₂ ∈ support (f a).run.run, z = (z₂.1, z₁.2 ++ z₂.2) := by
  rw [OptionT.run_bind, Option.elimM, WriterT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨z₁, h₁, hz⟩ := hz
  refine ⟨z₁, h₁, ?_⟩
  rcases z₁ with ⟨_ | a, w⟩
  · left
    simp only [Option.elim, WriterT.run_pure, support_pure, support_map, Set.mem_image, Set.mem_singleton_iff] at hz
    simp at hz
    exact ⟨rfl, hz.symm⟩
  · right
    refine ⟨a, rfl, ?_⟩
    simp only [Option.elim, support_map, Set.mem_image] at hz
    obtain ⟨z₂, h₂, rfl⟩ := hz
    exact ⟨z₂, h₂, rfl⟩

theorem mem_support_lift_bind {α β : Type} (p : PartyM C E RealSpec α) (f : α → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (RecM.lift p >>= f).run.run) :
    z = (none, []) ∨ ∃ a, ∃ z₂ ∈ support (f a).run.run, z = z₂ := by
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · have hlog : z₁.2 = [] := by
      change z₁ ∈ support (liftM p.run : WriterT (List (RecEvent C E)) _ _).run at h₁
      simp only [WriterT.run_liftM, support_map, Set.mem_image] at h₁
      obtain ⟨_, -, rfl⟩ := h₁
      rfl
    left
    rw [hlog]
  · have hlog : z₁.2 = [] := by
      change z₁ ∈ support (liftM p.run : WriterT (List (RecEvent C E)) _ _).run at h₁
      simp only [WriterT.run_liftM, support_map, Set.mem_image] at h₁
      obtain ⟨_, -, rfl⟩ := h₁
      rfl
    right
    exact ⟨a, z₂, h₂, by rw [hlog, List.nil_append]⟩

theorem mem_support_record_bind {β : Type} (events : List (RecEvent C E)) (f : PUnit → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (RecM.record events >>= f).run.run) :
    ∃ z₂ ∈ support (f PUnit.unit).run.run, z = (z₂.1, events ++ z₂.2) := by
  obtain ⟨z₁, h₁, ⟨hnone, -⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · simp [RecM.record, OptionT.run_lift, WriterT.run_tell] at h₁
    rw [h₁] at hnone
    cases hnone
  · simp [RecM.record, OptionT.run_lift, WriterT.run_tell] at h₁
    subst h₁
    exact ⟨z₂, h₂, rfl⟩

end RecSupport

/-! ## The layers with their products -/

section Layers

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The AND layers of `runJobs` with the products of each layer in a function. The inputs of layer `l`
are read from `layerPrefix` of the products before `l`. -/
def recLayers (B : RunBuildingBlocks C E G) (cs : List Circuit) (inputs : List (C.Term → List Bit)) (n : ℕ) :
    RunM C E G (ℕ → Shares C Bit) :=
  (List.range n).foldlM (fun zs l => (fun z => Function.update zs l z) <$>
    B.mult (layerX K cs l (layerPrefix K B.mode cs inputs zs l).1) (layerY K cs l (layerPrefix K B.mode cs inputs zs l).1)
      (gatesAt cs l).length) (fun _ _ _ => 0)

theorem layerPrefix_congr (mode : ReshareMode) (cs : List Circuit) (inputs : List (C.Term → List Bit))
    {zs zs' : ℕ → Shares C Bit} : ∀ n, (∀ j < n, zs j = zs' j) →
      layerPrefix K mode cs inputs zs n = layerPrefix K mode cs inputs zs' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [layerPrefix_succ, layerPrefix_succ, layerPrefix_congr mode cs inputs n fun j hj => h j (by omega), layerStep,
      layerStep, h n (by omega)]

/-- The fold of `runJobs` over the AND layers is `layerPrefix` of the products of `recLayers`. -/
theorem foldlM_layerBody_eq (B : RunBuildingBlocks C E G) (cs : List Circuit) (inputs : List (C.Term → List Bit)) :
    ∀ n, (List.range n).foldlM (layerBody K B cs) (inputs, []) =
      (fun zs => layerPrefix K B.mode cs inputs zs n) <$> recLayers K B cs inputs n
  | 0 => by simp [recLayers, layerPrefix]
  | n + 1 => by
    unfold recLayers
    rw [List.range_succ, List.foldlM_append, List.foldlM_append, ← recLayers, foldlM_layerBody_eq B cs inputs n,
      bind_map_left, map_bind]
    refine bind_congr fun zs => ?_
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, layerBody, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    refine bind_congr fun z => ?_
    rw [layerPrefix_succ, layerPrefix_congr K B.mode cs inputs (zs := Function.update zs n z) (zs' := zs) n
      fun j hj => Function.update_of_ne (by omega) _ _, layerStep, Function.update_self]

end Layers

/-! ## The recorded batch -/

section Batch

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- The check and the opening of a recorded batch from its start `b` and the counter `k`. It records
`b`, runs the check on `batchTuples` of the products `b.zs` and the sharing `b.v'`, opens `b.v'`
with `OpenRep` and records its inbox before its hash test, and records the batch output. -/
def recCheckOpen (b : BatchStart C) (k : ℕ) : StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  StateT.lift (RecM.record [.start b])
  let (_, s3) ← RecM.liftS (StateT.lift (((realRunBuildingBlocks (G := RealSpec) K b.ctx b.mode).verify
    (batchTuples K b.mode b.circuits b.inputs b.zs b.v')).run b.state))
  let digests ← RecM.liftS (StateT.lift (oracleStep (C.terms.mapM fun T =>
    hashQuery (.copy (vector (outputsOf b.circuits).length (b.v' T))))))
  let inbox ← RecM.liftS (StateT.lift (exchange (repOutbox K b.ctx.self b.v' (outputsOf b.circuits).length digests)))
  StateT.lift (RecM.record [.opened b.v' inbox])
  let opened ← RecM.liftS (StateT.lift (repRest K b.ctx.self b.v' (outputsOf b.circuits).length inbox))
  StateT.lift (RecM.record [.output (ThresholdLeanXmssSecurity.assemble b.circuits opened)])
  set (s3.label, k + 1)
  pure (some (ThresholdLeanXmssSecurity.assemble b.circuits opened))

/-- The check and the opening of a recorded batch with the record of the opening at one of two
places. With `early` it records the pass right after the check with no inbox, before the copy hashes
and the exchange of `OpenRep`. With `early = false` it is `recCheckOpen`. -/
def recCheckOpenWith (early : Bool) (b : BatchStart C) (k : ℕ) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  StateT.lift (RecM.record [.start b])
  let (_, s3) ← RecM.liftS (StateT.lift (((realRunBuildingBlocks (G := RealSpec) K b.ctx b.mode).verify
    (batchTuples K b.mode b.circuits b.inputs b.zs b.v')).run b.state))
  if early then StateT.lift (RecM.record [.opened b.v' fun _ => none])
  let digests ← RecM.liftS (StateT.lift (oracleStep (C.terms.mapM fun T =>
    hashQuery (.copy (vector (outputsOf b.circuits).length (b.v' T))))))
  let inbox ← RecM.liftS (StateT.lift (exchange (repOutbox K b.ctx.self b.v' (outputsOf b.circuits).length digests)))
  if !early then StateT.lift (RecM.record [.opened b.v' inbox])
  let opened ← RecM.liftS (StateT.lift (repRest K b.ctx.self b.v' (outputsOf b.circuits).length inbox))
  StateT.lift (RecM.record [.output (ThresholdLeanXmssSecurity.assemble b.circuits opened)])
  set (s3.label, k + 1)
  pure (some (ThresholdLeanXmssSecurity.assemble b.circuits opened))

/-- One batch of a ceremony at operator `ctx.self` with its record. It is `realBatch` with the
products of the AND layers in `recLayers`, then `recCheckOpen` of the start of its check. -/
def recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let (label, k) ← get
  let cs := jobs.map (circuits parameter ·.kind)
  let B := realRunBuildingBlocks (G := RealSpec) K ctx settings.mode
  let inputs ← RecM.liftS (StateT.lift (jobs.mapM (inputShares ctx)))
  let (zs, s1) ← RecM.liftS (StateT.lift ((recLayers K B cs inputs (depth cs)).run ⟨fun _ => [], label, k⟩))
  let (v', s2) ← RecM.liftS (StateT.lift ((B.rerand (outputShares K cs
    (layerPrefix K B.mode cs inputs zs (depth cs)).1) (outputsOf cs).length).run s1))
  recCheckOpen K ⟨B.mode, jobs, parameter, cs, inputs, zs, v', ctx, s2⟩ k

/-- One recorded batch with the record of the opening at its place for `early`, as `recBatch`. With
`early = false` it is `recBatch`. -/
def recBatchAt (early : Bool) (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let (label, k) ← get
  let cs := jobs.map (circuits parameter ·.kind)
  let B := realRunBuildingBlocks (G := RealSpec) K ctx settings.mode
  let inputs ← RecM.liftS (StateT.lift (jobs.mapM (inputShares ctx)))
  let (zs, s1) ← RecM.liftS (StateT.lift ((recLayers K B cs inputs (depth cs)).run ⟨fun _ => [], label, k⟩))
  let (v', s2) ← RecM.liftS (StateT.lift ((B.rerand (outputShares K cs
    (layerPrefix K B.mode cs inputs zs (depth cs)).1) (outputsOf cs).length).run s1))
  recCheckOpenWith K early ⟨B.mode, jobs, parameter, cs, inputs, zs, v', ctx, s2⟩ k

/-- With its record dropped, `recBatch` is `realBatch`. -/
theorem dropRecS_recBatch [Fintype E] [DecidableEq E] (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    dropRecS (recBatch K circuits settings ctx parameter jobs) = realBatch K circuits settings.mode ctx parameter jobs := by
  unfold recBatch recCheckOpen
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_get, dropRecS_set, dropRecS_liftS, dropRecS_record,
    pure_bind]
  refine StateT.ext fun st => ?_
  rw [realBatch_run]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    StateT.run_pure]
  refine bind_congr fun inputs => ?_
  rw [runJobs_eq, StateT.run_bind, foldlM_layerBody_eq, StateT.run_map, bind_map_left, bind_assoc]
  refine bind_congr fun r => ?_
  simp only [tailBody, StateT.run_bind, bind_assoc]
  refine bind_congr fun x => ?_
  refine bind_congr fun y => ?_
  have hopen : ∀ (v : Shares C Bit) (count : ℕ), openRep (G := RealSpec) K ctx v count =
      oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (v T)))) >>= fun digests =>
        exchange (repOutbox (E := E) K ctx.self v count digests) >>= fun inbox => repRest K ctx.self v count inbox := by
    intro v count
    change openRep K (localContext ctx.self) v count = _
    rw [openRep_eq]
    rfl
  change _ = StateT.run (StateT.lift (openRep (G := RealSpec) K ctx x.1 _)) y.2 >>= _
  rw [StateT.run_lift, hopen]
  simp only [bind_assoc, pure_bind, StateT.run_pure]

/-- With its record dropped, `recBatchAt` is `realBatch` at both places of the opening record. -/
theorem dropRecS_recBatchAt [Fintype E] [DecidableEq E] (early : Bool) (ctx : Context C)
    (parameter : PublicParameter) (jobs : List Job) :
    dropRecS (recBatchAt K circuits settings early ctx parameter jobs) =
      realBatch K circuits settings.mode ctx parameter jobs := by
  rw [← dropRecS_recBatch]
  cases early
  · rfl
  unfold recBatchAt recBatch recCheckOpenWith recCheckOpen
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, dropRecS_get, dropRecS_set, dropRecS_liftS, dropRecS_record,
    pure_bind, ↓reduceIte, Bool.not_true, Bool.false_eq_true]

end Batch

/-! ## The recorded tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

/-- One ceremony at operator `i` with its record, as `ceremonyRun` of `newTree`. -/
def recRun (i : C.Party) (keys : Keys C) (jobs : List Job) : StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let prss ← RecM.liftS (StateT.lift (prssSetup i))
  batched settings.batchSize (recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter) jobs

/-- One recorded ceremony with the record of the opening at its place for `early`, as `recRun`. -/
def recRunAt (early : Bool) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let prss ← RecM.liftS (StateT.lift (prssSetup i))
  batched settings.batchSize (recBatchAt K circuits settings early ⟨i, keys, prss⟩ keys.parameter) jobs

theorem dropRecS_recRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    dropRecS (recRun K circuits settings i keys jobs) =
      ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs := by
  unfold recRun
  rw [MonadHom.mmap_bind, dropRecS_liftS]
  simp only [monadHom_batched, dropRecS_recBatch]
  rfl

end Tree

/-! ## The one ghost run of a tree -/

section Run

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives) (runLimit : ℕ)
  (budget : StartBudget)

/-- The record of one operator. -/
abbrev Record (C : Committee) (E : Type) := List (RecEvent C E)

/-- The last step of each operator in a ghost run of a tree. -/
abbrev GhostSteps (C : Committee) (E : Type) := C.Party → RStep C E RealSpec TreeOutput (Record C E)

/-- The starts of the checks in a record. -/
def startsOf (record : Record C E) : List (BatchStart C) :=
  record.filterMap fun e => match e with
    | .start b => some b
    | _ => none

/-- The sharings and the inboxes of the openings in a record. -/
def openingsOf (record : Record C E) : List (Shares C Bit × Mail C E) :=
  record.filterMap fun e => match e with
    | .opened v' inbox => some (v', inbox)
    | _ => none

/-- The batch outputs in a record. -/
def batchOutputsOf (record : Record C E) : List (List (List Bit)) :=
  record.filterMap fun e => match e with
    | .output o => some o
    | _ => none

/-- The record of operator `i` at the end of a ghost run. -/
def recordOf (steps : GhostSteps C E) (i : C.Party) : Record C E := (steps i).record []

/-- Each honest operator recorded the start of the check of batch `k`. -/
def AllStartedAt (D : C.Coalition) (k : ℕ) (steps : GhostSteps C E) : Prop :=
  ∀ i, i ∉ D.1 → ((startsOf (recordOf steps i))[k]?).isSome

/-- An honest operator with an output recorded a batch `k` whose output is not right, for a good `H`
that agrees with the final hash cache, on the seeds of the game. -/
def WrongBatchAt (D : C.Coalition) {σ : Type} (s : RealState C σ) (k : ℕ)
    (ω : ((σ × GhostSteps C E) × Bool) × StreamState C) : Prop :=
  ∃ i, i ∉ D.1 ∧ (ω.1.1.2 i).output.isSome ∧ ∃ b out h, (startsOf (recordOf ω.1.1.2 i))[k]? = some b ∧
    (batchOutputsOf (recordOf ω.1.1.2 i))[k]? = some out ∧ Good prims h ∧ Agrees h ω.2.1 ∧
    ¬ RightBatch prims circuits h b.parameter (gameSeeds D fun j => (s.operators j).keys) b.jobs (some out)

end Run

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace Fuel

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## Programs with at most `n` rounds -/

section Within

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- A program that takes at most `n` rounds or calls on each path. -/
inductive Within {α : Type} : ℕ → OracleComp (PartySpec C E G) (Option α) → Prop
  | ret (n : ℕ) (out : Option α) : Within n (pure out)
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, Within n (k r)) : Within n (.liftBind (.inl (.inl q)) k)
  | round (n : ℕ) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, Within n (k r)) : Within (n + 1) (.liftBind (.inl (.inr out)) k)
  | call (n : ℕ) (input : ι) (k : G input → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, Within n (k r)) : Within (n + 1) (.liftBind (.inr input) k)

theorem Within.mono {α : Type} {m : ℕ} {p : OracleComp (PartySpec C E G) (Option α)} (h : Within m p) :
    ∀ {n : ℕ}, m ≤ n → Within n p := by
  induction h with
  | ret m out => exact fun _ => Within.ret _ out
  | queryLocal m q k _ ih => exact fun hn => Within.queryLocal _ q k fun r => ih r hn
  | round m out k _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact Within.round n out k fun r => ih r (by omega)
  | call m input k _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact Within.call n input k fun r => ih r (by omega)

/-- A timed program is within its count. -/
theorem Within.of_timed {α : Type} {n : ℕ} {p : OracleComp (PartySpec C E G) (Option α)} (h : Timed n p) :
    Within n p := by
  induction h with
  | abort n => exact Within.ret n none
  | done a => exact Within.ret 0 (some a)
  | queryLocal n q k _ ih => exact Within.queryLocal n q k ih
  | round n out k _ ih => exact Within.round n out k ih
  | call n input k _ ih => exact Within.call n input k ih

/-- The bound of a sequence is the sum of the two bounds. Copy of `Timed.bind`. -/
theorem Within.bind {α β : Type} {m n : ℕ} {p : PartyM C E G α} {k : α → PartyM C E G β}
    (hp : Within m p.run) (hk : ∀ a, Within n (k a).run) : Within (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change Within (m + n) (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | ret m out =>
    cases out with
    | none => simpa only [pure_bind, Option.elim_none] using Within.ret (α := β) (m + n) none
    | some a => simpa only [pure_bind, Option.elim_some] using (hk a).mono (Nat.le_add_left n m)
  | queryLocal m q f _ ih => exact Within.queryLocal (m + n) q _ ih
  | round m out f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Within.round (m + n) out _ ih
  | call m input f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Within.call (m + n) input _ ih

/-- A stopped program that needs at most `n` more rounds or calls. -/
def StepWithin {α : Type} (n : ℕ) : Step C E G α → Prop
  | .done _ => True
  | .wait _ resume => ∃ m, n = m + 1 ∧ ∀ inbox, Within m (resume inbox)
  | .call _ resume => ∃ m, n = m + 1 ∧ ∀ r, Within m (resume r)

/-- The local steps of a program within `n` rounds stop at a step within `n` rounds. Copy of
`timed_advance`. -/
theorem within_advance {α : Type} {n : ℕ} {p : OracleComp (PartySpec C E G) (Option α)} (h : Within n p) :
    ∀ step ∈ support (advance p), StepWithin n step := by
  induction h with
  | ret n out =>
    intro step hs
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    trivial
  | queryLocal n q k _ ih =>
    intro step hs
    change step ∈ support (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)) at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨r, -, hr⟩ := hs
    exact ih r step hr
  | round n out k h _ =>
    intro step hs
    change step ∈ support (pure (Step.wait out k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨n, rfl, h⟩
  | call n input k h _ =>
    intro step hs
    change step ∈ support (pure (Step.call input k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨n, rfl, h⟩

/-- A step with no round to go is done. -/
theorem StepWithin.isDone {α : Type} {step : Step C E G α} (h : StepWithin 0 step) : step.isDone := by
  cases step with
  | done out => trivial
  | wait out resume => obtain ⟨m, hm, -⟩ := h; exact absurd hm.symm (Nat.succ_ne_zero m)
  | call input resume => obtain ⟨m, hm, -⟩ := h; exact absurd hm.symm (Nat.succ_ne_zero m)

/-- A ghost step from the local steps of a program has the bound of the erased program. -/
theorem within_advanceR {α R : Type} {n : ℕ} {p : OracleComp (PartySpec C E G) (Option α × R)}
    (h : Within n (Prod.fst <$> p)) : ∀ s ∈ support (advanceR p), StepWithin n s.erase := by
  intro s hs
  refine within_advance h s.erase ?_
  rw [← advanceR_erase, support_map]
  exact Set.mem_image_of_mem _ hs

end Within

/-! ## The ghost executor with enough fuel -/

section Execution

variable {C : Committee} {E : Type} {Ia L Rs O α ρ : Type}

theorem mem_support_sequenceFin {κ β : Type} {spec : OracleSpec κ} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec β), ∀ x ∈ support (OverPermutation.sequenceFin f), ∀ j, x j ∈ support (f j)
  | 0, _, _, _, j => j.elim0
  | n + 1, f, x, hx, j => by
    simp only [OverPermutation.sequenceFin, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨a, ha, xs, hxs, rfl⟩ := hx
    cases j using Fin.cases with
    | zero => exact ha
    | succ j => exact mem_support_sequenceFin (fun i : Fin n => f i.succ) xs hxs j

theorem mem_support_honest {β : Type} (oa : OracleComp (LocalSpec C) β) :
    ∀ x ∈ support ((worldRoles (C := C)).honest oa), x ∈ support oa :=
  fun _ hx => support_simulateQ_subset _ _ hx

variable (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C PEmpty O L Rs) (blank : ρ)

/-- A round of the ghost executor takes one round from each honest bound. -/
theorem stepRoundR_within (n : ℕ) (state : A.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ)
    (h : ∀ i, i ∉ D.1 → StepWithin (n + 1) (steps i).erase) :
    ∀ r ∈ support (stepRoundR worldRoles D A F blank state steps), ∀ i, i ∉ D.1 → StepWithin n (r.2.1 i).erase := by
  have hcall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, -, hi⟩, -⟩
    cases hs : steps i with
    | done out record => rw [hs] at hi; exact absurd hi (by simp [RStep.callInput])
    | wait outbox resume => rw [hs] at hi; exact absurd hi (by simp [RStep.callInput])
    | call input resume => exact input.elim
  intro r hr i hi
  unfold stepRoundR at hr
  simp only [hcall, ↓reduceIte] at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨⟨st, sent⟩, -, hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨steps', hsteps', hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  have hj := mem_support_sequenceFin _ steps' hsteps' i
  have hhi := h i hi
  show StepWithin n (steps' i).erase
  revert hj hhi
  cases steps i with
  | done out record =>
    intro hj _
    rw [support_pure, Set.mem_singleton_iff] at hj
    rw [hj]
    trivial
  | wait outbox resume =>
    intro hj hhi
    simp only [hi, ↓reduceIte] at hj
    obtain ⟨m, hm, hk⟩ := hhi
    obtain rfl : n = m := by omega
    exact within_advanceR (hk _) _ (mem_support_honest _ _ hj)
  | call input resume => exact input.elim

/-- The ghost executor with fuel at least the honest bounds ends with each honest step done. -/
theorem executeRoundsR_done : ∀ (fuel n : ℕ), n ≤ fuel → ∀ (state : A.State)
    (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ), (∀ i, i ∉ D.1 → StepWithin n (steps i).erase) →
    ∀ r ∈ support (executeRoundsR worldRoles D A F blank fuel state steps), ∀ i, i ∉ D.1 → (r.2 i).isDone
  | 0, n, hn, state, steps, h, r, hr, i, hi => by
    simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    obtain rfl : n = 0 := by omega
    rw [← RStep.isDone_erase]
    exact (h i hi).isDone
  | fuel + 1, n, hn, state, steps, h, r, hr, i, hi => by
    unfold executeRoundsR at hr
    split_ifs at hr with hall
    · rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hall i hi
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
        rcases n with _ | n
        · refine absurd (fun j hj => ?_) hall
          rw [← RStep.isDone_erase]
          exact (h j hj).isDone
        · exact ⟨n, rfl⟩
      rw [mem_support_bind_iff] at hr
      obtain ⟨⟨st, steps', sent⟩, h₁, hr⟩ := hr
      exact executeRoundsR_done fuel n (by omega) st steps'
        (stepRoundR_within D A F blank n state steps h _ h₁) r hr i hi

/-- A ghost phase with fuel at least the bound of each honest program ends with each honest step
done. -/
theorem executePhaseR_done (fuel n : ℕ) (hn : n ≤ fuel) (state : A.State)
    (program : C.Party → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ))
    (h : ∀ i, i ∉ D.1 → Within n (Prod.fst <$> program i)) :
    ∀ r ∈ support (executePhaseR worldRoles D A F blank fuel state program), ∀ i, i ∉ D.1 → (r.2 i).isDone := by
  intro r hr
  unfold executePhaseR at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨steps, hsteps, hr⟩ := hr
  refine executeRoundsR_done D A F blank fuel n hn state steps (fun i hi => ?_) r hr
  have hj := mem_support_sequenceFin _ steps hsteps i
  simp only [hi, ↓reduceIte] at hj
  exact within_advanceR (h i hi) _ (mem_support_honest _ _ hj)

end Execution

/-! ## The bound of the program of a tree -/

section Program

variable {C : Committee} {E : Type}

/-- A program on the counters that takes at most `n` rounds from each state. -/
def RunWithin {β : Type} (n : ℕ) (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) : Prop :=
  ∀ st, Within n (x.run st).run

theorem RunWithin.bind {β γ : Type} {m n : ℕ} {x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β}
    {k : β → StateT (ℕ × ℕ) (PartyM C E RealSpec) γ} (hx : RunWithin m x) (hk : ∀ b, RunWithin n (k b)) :
    RunWithin (m + n) (x >>= k) := fun st => by
  rw [StateT.run_bind]
  exact (hx st).bind fun q => hk q.1 q.2

theorem RunWithin.mono {β : Type} {m n : ℕ} {x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β} (hx : RunWithin m x)
    (h : m ≤ n) : RunWithin n x :=
  fun st => (hx st).mono h

theorem RunWithin.of_runTimed {β : Type} {n : ℕ} {x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β} (hx : RunTimed n x) :
    RunWithin n x :=
  fun st => Within.of_timed (hx st)

theorem runWithin_pure {β : Type} (b : β) : RunWithin 0 (pure b : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) :=
  RunWithin.of_runTimed (runTimed_pure b)

/-- The ceremony of the top tree takes at most the rounds of its run. -/
theorem runWithin_ceremonyOutput_top
    (lift : ∀ {β : Type}, OracleComp HashSpec β → StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), RunWithin 0 (lift oa)) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (a : ℕ)
    (hrun : RunWithin a (run topJobs)) (top : TopTree) :
    RunWithin a (ceremonyOutput lift parameter run top .top) := by
  refine (RunWithin.bind (n := 0) hrun fun o => ?_).mono (by omega)
  rcases o with _ | outputs
  · exact runWithin_pure _
  · exact (RunWithin.bind (m := 0) (n := 0) (hlift _) fun _ => runWithin_pure _).mono (by omega)

/-- The ceremonies of a bottom tree take at most the rounds of the first run and the most rounds of
the second run over all encodings. -/
theorem runWithin_ceremonyOutput_bottom
    (lift : ∀ {β : Type}, OracleComp HashSpec β → StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), RunWithin 0 (lift oa)) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (b : Fin (2 ^ layerHeight))
    (a c : ℕ) (hfirst : RunWithin a (run (bottomJobs b))) (hsecond : ∀ encoding, RunWithin c (run (signJobs b encoding)))
    (top : TopTree) :
    RunWithin (a + c) (ceremonyOutput lift parameter run top (.bottom b)) := by
  refine RunWithin.bind hfirst fun o => ?_
  rcases o with _ | outputs
  · exact (runWithin_pure _).mono (Nat.zero_le _)
  refine (RunWithin.bind (hlift _) fun root => ?_).mono (Nat.zero_add c).le
  refine (RunWithin.bind (hlift _) fun base => ?_).mono (Nat.zero_add c).le
  refine (RunWithin.bind (hlift _) fun g => ?_).mono (Nat.zero_add c).le
  rcases g with _ | ⟨randomness, encoding⟩
  · exact (runWithin_pure _).mono (Nat.zero_le _)
  refine (RunWithin.bind (n := 0) (hsecond encoding) fun o' => ?_).mono (by omega)
  rcases o' with _ | values
  · exact runWithin_pure _
  refine RunWithin.bind (m := 0) (n := 0) (hlift _) fun path => ?_
  refine RunWithin.bind (m := 0) (n := 0) (hlift _) fun topRoot => ?_
  split <;> exact runWithin_pure _

variable [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- `newTree` takes at most the rounds of its ceremonies. -/
theorem within_newTree (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) (n : ℕ)
    (h : RunWithin n (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) top tree)) :
    Within n (newTree K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput).run := by
  unfold newTree
  refine (Within.bind (m := n) (n := 0) ?_ fun o => ?_).mono (by omega)
  · rw [StateT.run'_eq, map_eq_bind_pure_comp]
    exact (h (0, 0)).bind (n := 0) fun p => Within.ret 0 (some p.1)
  · rcases o with _ | output
    · exact Within.ret 0 none
    · exact Within.ret 0 (some output)

/-- The program of each operator for each tree takes at most `treeFuel` rounds. -/
theorem within_treeProgram (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    Within (treeFuel circuits settings) (treeProgram K circuits settings i operator tree).run := by
  have hlift : ∀ {β : Type} (oa : OracleComp HashSpec β),
      RunWithin 0 (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) :=
    fun oa => RunWithin.of_runTimed (RunTimed.lift (timed_oracleStep _))
  cases tree with
  | top =>
    unfold treeProgram
    rcases operator.keys with _ | keys
    · exact Within.ret _ none
    refine within_newTree K circuits settings i keys emptyTop .top _ ?_
    refine (runWithin_ceremonyOutput_top _ hlift _ _ _
      (RunWithin.of_runTimed (runTimed_ceremonyRun K circuits settings i keys topJobs)) _).mono ?_
    have := topRounds_le circuits settings keys.parameter
    unfold treeFuel batchesRounds
    omega
  | bottom b =>
    unfold treeProgram
    rcases operator.keys with _ | keys <;> rcases operator.top with _ | top
    · exact Within.ret _ none
    · exact Within.ret _ none
    · exact Within.ret _ none
    have hb := bottomRounds_le circuits settings keys.parameter b (fun _ => digit 0)
    refine within_newTree K circuits settings i keys top (.bottom b) _ ?_
    refine (runWithin_ceremonyOutput_bottom _ hlift _ _ b
      (setupRounds + batchesRounds circuits settings keys.parameter (bottomJobs b))
      (treeFuel circuits settings - (setupRounds + batchesRounds circuits settings keys.parameter (bottomJobs b)))
      (RunWithin.of_runTimed (runTimed_ceremonyRun K circuits settings i keys (bottomJobs b)))
      (fun encoding => (RunWithin.of_runTimed (runTimed_ceremonyRun K circuits settings i keys
        (signJobs b encoding))).mono ?_) _).mono ?_
    · have := bottomRounds_le circuits settings keys.parameter b encoding
      unfold treeFuel batchesRounds at *
      omega
    · unfold treeFuel batchesRounds at *
      omega

end Program

end Fuel

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Fuel.within_newTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Fuel.within_newTree
