import Sketch.Pilot
import ThresholdLeanXmssSecurity.Proof.Dealer

/-!
# Right batch outputs give the output of `referenceTree`

This file proves the hop H13 of `DkgCorrectness` on the program of one honest operator.
An output of a run of a tree whose batches have right outputs is the output of `referenceTree`.

* `ceremonyAt_eq_referenceTree`. With `H` fixed to a good `h`, the tree of the right outputs is
  `referenceTree`, when the circuits compute `Th`.
* `rel_ceremonyOutput`. A predicate on the outcomes with a pure rule and a bind rule passes through
  `ceremonyOutput` and `batched`.
* `fixHash h` fixes only `H` to `h`. Private sampling, `PRG`, the rounds and the calls stay free, so
  its support holds each path of the operator in each world whose answers of `H` agree with `h`.
* `loggedTree` is `newTree` with a log of the jobs and the outputs of each batch of its ceremonies.
  `newTree_eq_loggedTree` drops the log.
* `RightBatch` says that the outputs of one batch are the circuit values on the PRF values of the
  seeds. `loggedTree_referenceTree` is the fact on the program. An outcome with only right batches in
  its log has the output of `referenceTree`. It needs a positive batch size, because `batched_zero`
  shows that the batch size `0` runs no batch.
* `RightTuples` is the negation of `WrongTuple`. `ProjectsOnPaths` is the projection of a run on the
  network on the path of one honest operator. `runOutput_referenceTree` is the fact on the network
  from it, and `treeRun_logged` links the run of `treeProgram` to the run of `loggedTreeProgram`.
* `exists_honest_holder`, `seed_eq_gameSeeds` and `parameter_eq_gameParameter` give the values that
  the honest operators fix.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The tree of the right outputs -/

section Reference

variable (prims : Primitives) (circuits : Circuits)

/-- A computation that keeps each cache and gives `a` has the value `a` with `H` fixed to each good
`h`. -/
theorem D_of_fixedR {α : Type} {oa : OracleComp (RoSpec C) α} {a : α} (hfix : FixedR prims oa a)
    {h : Query C → HashOutput} (hg : Good prims h) : D prims h oa = a := by
  have hz : (a, (∅ : HashCache C)) ∈ support (roRun prims oa ∅) := by
    rw [hfix ∅]
    simp
  exact ((roRun_support prims oa ∅ _ hz).2.2 h hg (fun q v hq => by simp at hq)).symm

/-- With `H` fixed to a good `h`, a circuit that computes `Th` gives `referenceJob` on each job of
its arity. -/
theorem D_evalJob_eq_referenceJob (hc : CircuitsCompute circuits prims.Th) {h : Query C → HashOutput}
    (hg : Good prims h) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (job : Job)
    (harity : job.points.length = job.kind.arity) :
    D prims h (evalJob circuits parameter seeds job) =
      D prims h (referenceJob tweakable (prfValue seeds) parameter job) := by
  rw [referenceJob_eq, D_bind, D_mapM, D_of_fixedR prims (fixedR_refCore _ _ _) hg]
  unfold evalJob
  rw [D_bind, D_mapM, D_pure]
  exact eval_eq_refCore prims circuits hc parameter job.kind _ (by rw [List.length_map, harity])

/-- With `H` fixed to a good `h`, the tree of the right outputs is `referenceTree`, when the circuits
compute `Th`. -/
theorem ceremonyAt_eq_referenceTree (hc : CircuitsCompute circuits prims.Th) {h : Query C → HashOutput}
    (hg : Good prims h) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (tree : Tree) :
    ceremonyAt prims circuits parameter seeds h top tree =
      D prims h (referenceTree tweakable (prfValue seeds) parameter top tree) := by
  unfold referenceTree
  rw [map_ceremonyOutput (fun x => D prims h x) (fun b => D_pure (prims := prims) h b)
    (fun x f => D_bind (prims := prims) h x f)]
  unfold ceremonyAt
  refine ceremonyOutput_congr _ _ _ _ (fun js hjs => ?_) top tree
  rw [evalRun_eq, D_map, D_mapM]
  congr 1
  exact List.map_congr_left fun job hjob =>
    D_evalJob_eq_referenceJob prims circuits hc hg parameter seeds job (hjs job hjob)

/-- With the batch size `0`, a run in batches runs no batch and gives no output of a job. -/
theorem batched_zero {m : Type → Type} [Monad m] [LawfulMonad m] (run : List Job → m (Option (List (List Bit))))
    (jobs : List Job) : batched 0 run jobs = pure (some []) := by
  simp [batched, chunks]

end Reference

/-! ## A predicate on the outcomes of `ceremonyOutput` -/

section Relation

variable {m : Type → Type} [Monad m] [LawfulMonad m] (S : ∀ {β : Type}, (β → Prop) → m β → Prop)
  (hpure : ∀ {β : Type} (P : β → Prop) (b : β), P b → S P (pure b))
  (hbind : ∀ {β γ : Type} (Q : β → Prop) (P : γ → Prop) (x : m β) (f : β → m γ),
    S Q x → (∀ b, Q b → S P (f b)) → S P (x >>= f))

include hpure hbind in
theorem rel_mapM {β γ : Type} (f : β → m γ) (g : β → γ) (hf : ∀ b, S (· = g b) (f b)) :
    ∀ l : List β, S (· = l.map g) (l.mapM f)
  | [] => hpure _ [] rfl
  | b :: l => by
    rw [List.mapM_cons]
    refine hbind _ _ _ _ (hf b) fun c hc => hbind _ _ _ _ (rel_mapM f g hf l) fun cs hcs => hpure _ _ ?_
    rw [hc, hcs, List.map_cons]

include hpure hbind in
theorem rel_batched (size : ℕ) (run : List Job → m (Option (List (List Bit))))
    (run' : List Job → Option (List (List Bit))) (hr : ∀ js, S (· = run' js) (run js)) (jobs : List Job) :
    S (· = batched (m := Id) size run' jobs) (batched size run jobs) := by
  unfold batched
  refine hbind _ _ _ _ (rel_mapM S hpure hbind run run' hr (chunks size jobs)) fun outs houts => hpure _ _ ?_
  rw [houts, id_bind_eq, id_mapM]
  rfl

omit [LawfulMonad m] in
include hpure hbind in
/-- When each hash computation and each run has a fixed value on its outcomes, `ceremonyOutput` has
the value of `ceremonyOutput` on these values. -/
theorem rel_ceremonyOutput (lift : ∀ {β : Type}, OracleComp HashSpec β → m β)
    (lift' : ∀ {β : Type}, OracleComp HashSpec β → β)
    (hl : ∀ {β : Type} (oa : OracleComp HashSpec β), S (· = lift' oa) (lift oa))
    (run : List Job → m (Option (List (List Bit)))) (run' : List Job → Option (List (List Bit)))
    (hr : ∀ js, S (· = run' js) (run js)) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    S (· = ceremonyOutput (m := Id) (fun oa => lift' oa) parameter run' top tree)
      (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine hbind _ _ _ _ (hr topJobs) fun o ho => ?_
    subst ho
    rcases run' topJobs with _ | outputs
    · exact hpure _ _ rfl
    · refine hbind _ _ _ _ (hl _) fun root hroot => hpure _ _ ?_
      subst hroot
      rfl
  | bottom b =>
    simp only [ceremonyOutput, id_bind_eq]
    refine hbind _ _ _ _ (hr (bottomJobs b)) fun o ho => ?_
    subst ho
    rcases run' (bottomJobs b) with _ | outputs
    · exact hpure _ _ rfl
    · refine hbind _ _ _ _ (hl _) fun root hroot => ?_
      subst hroot
      refine hbind _ _ _ _ (hl _) fun base hbase => ?_
      subst hbase
      refine hbind _ _ _ _ (hl _) fun g hg => ?_
      simp only [← hg]
      rcases g with _ | ⟨randomness, encoding⟩
      · exact hpure _ _ rfl
      · refine hbind _ _ _ _ (hr _) fun o ho => ?_
        simp only [← ho]
        rcases o with _ | values
        · exact hpure _ _ rfl
        · refine hbind _ _ _ _ (hl _) fun path hpath => ?_
          subst hpath
          refine hbind _ _ _ _ (hl _) fun topRoot htopRoot => ?_
          simp only [← htopRoot]
          split_ifs
          · exact hpure _ _ rfl
          · exact hpure _ _ rfl

end Relation

/-! ## The program of one operator with `H` fixed -/

section Program

variable {E : Type} {ι : Type} {G : OracleSpec ι}

/-- The oracles of an operator with `H` fixed to `h`. Private sampling, `PRG`, the rounds and the
calls stay free queries. -/
def fixHash (h : Query C → HashOutput) : QueryImpl (PartySpec C E G) (OracleComp (PartySpec C E G)) :=
  fun t => match t with
  | Sum.inl (Sum.inl (Sum.inr (Sum.inl q))) => pure (h q)
  | t => OracleComp.lift (OracleSpec.query t)

variable (prims : Primitives)

/-- A local step of `H` calls has the value with `H` fixed to `h`. -/
theorem fixHash_oracleStep_tweakable (h : Query C → HashOutput) {β : Type} (oa : OracleComp HashSpec β) :
    simulateQ (fixHash (E := E) (G := G) h) (oracleStep (tweakable oa) : PartyM C E G β).run =
      pure (some (D prims h (tweakable oa))) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [oracleStep, localStep, tweakable, D]
  | query_bind t k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_query, oracleStep, localStep] at ih ⊢
    simp [OptionT.run_lift, liftComp_bind] at ih ⊢
    refine ⟨h (.hash t), ?_, ?_⟩
    · simp [hashQuery]
      rfl
    · rw [ih, D_bind, D_hashQuery]

/-- The log of the batches of a run, namely the jobs and the outputs of each batch. -/
abbrev BatchLog := List (List Job × Option (List (List Bit)))

/-- A program of one operator on the counters of its ceremonies, with the log of its batches. -/
abbrev LogM (C : Committee) (E : Type) := WriterT BatchLog (StateT (ℕ × ℕ) (PartyM C E RealSpec))

/-- Each outcome of `x` with `H` fixed to `h` and with only `right` batches in its log has a value
with `P`. -/
def Sound (h : Query C → HashOutput) (right : List Job → Option (List (List Bit)) → Prop) {β : Type}
    (P : β → Prop) (x : LogM C E β) : Prop :=
  ∀ s z, z ∈ support (simulateQ (fixHash h) (x.run.run s).run) → ∀ a w s', z = some ((a, w), s') →
    (∀ e ∈ w, right e.1 e.2) → P a

/-- A local step of `H` calls with no log. -/
def hashStep {β : Type} (oa : OracleComp HashSpec β) : LogM C E β :=
  liftM (StateT.lift (oracleStep (tweakable oa) : PartyM C E RealSpec β) : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)

variable (h : Query C → HashOutput) (right : List Job → Option (List (List Bit)) → Prop)

theorem sound_pure {β : Type} (P : β → Prop) (b : β) (hb : P b) : Sound (E := E) h right P (pure b) := by
  intro s z hz a w s' hzeq hw
  simp [WriterT.run_pure] at hz
  rw [hz] at hzeq
  cases hzeq
  exact hb

theorem sound_bind {β γ : Type} (Q : β → Prop) (P : γ → Prop) (x : LogM C E β) (f : β → LogM C E γ)
    (hx : Sound h right Q x) (hf : ∀ b, Q b → Sound h right P (f b)) : Sound h right P (x >>= f) := by
  intro s z hz a w s' hzeq hw
  subst hzeq
  rw [WriterT.run_bind, StateT.run_bind, OptionT.run_bind, Option.elimM, simulateQ_bind,
    mem_support_bind_iff] at hz
  obtain ⟨o, ho, hz⟩ := hz
  rcases o with _ | ⟨⟨b, w₁⟩, s₁⟩
  · simp at hz
  · simp only [Option.elim, StateT.run_map, OptionT.run_map, simulateQ_map, support_map, Set.mem_image] at hz
    obtain ⟨o, ho', hz⟩ := hz
    rcases o with _ | ⟨⟨c, w₂⟩, s₂⟩
    · simp at hz
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz
      have hQ := hx s _ ho b w₁ s₁ rfl fun e he => hw e (List.mem_append_left _ he)
      exact hf b hQ s₁ _ ho' c w₂ s₂ rfl fun e he => hw e (List.mem_append_right _ he)

/-- Each outcome of a step with no log, with `H` fixed to `h`, has a value with `P`. -/
theorem sound_liftM {β : Type} (P : β → Prop) (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hx : ∀ s z, z ∈ support (simulateQ (fixHash h) (x.run s).run) → ∀ b s', z = some (b, s') → P b) :
    Sound h right P (liftM x : LogM C E β) := by
  intro s z hz a w s' hzeq hw
  subst hzeq
  rw [WriterT.run_liftM, StateT.run_map, OptionT.run_map, simulateQ_map, support_map] at hz
  obtain ⟨o, ho, hz⟩ := hz
  rcases o with _ | ⟨b, s₁⟩
  · simp at hz
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨⟨rfl, -⟩, rfl⟩ := hz
    exact hx s _ ho _ s₁ rfl

theorem sound_true {β : Type} (x : LogM C E β) : Sound h right (fun _ => True) x :=
  fun _ _ _ _ _ _ _ _ => trivial

/-- The log of `tell` is right. -/
theorem sound_tell (js : List Job) (o : Option (List (List Bit))) :
    Sound h right (fun _ => right js o) (tell [(js, o)] : LogM C E PUnit) := by
  intro s z hz a w s' hzeq hw
  subst hzeq
  simp [WriterT.run_tell] at hz
  obtain ⟨rfl, -⟩ := hz
  exact hw _ (List.mem_singleton_self _)

/-- A local step of `H` calls has its value with `H` fixed to `h`. -/
theorem sound_hash {β : Type} (oa : OracleComp HashSpec β) :
    Sound h right (· = D prims h (tweakable oa)) (hashStep (C := C) (E := E) oa) := by
  refine sound_liftM h right _ _ fun s z hz b s' hzeq => ?_
  subst hzeq
  rw [StateT.run_lift, OptionT.run_bind, Option.elimM, simulateQ_bind,
    fixHash_oracleStep_tweakable prims h oa, pure_bind] at hz
  simp at hz
  exact hz.1

end Program

/-! ## The program of a tree with the log of its batches -/

section Logged

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- One ceremony at operator `i`, as in `newTree`, with the jobs and the outputs of each batch in the
log. -/
def loggedRun (i : C.Party) (keys : Keys C) (jobs : List Job) : LogM C E (Option (List (List Bit))) := do
  let prss ← liftM (StateT.lift (prssSetup i) : StateT (ℕ × ℕ) (PartyM C E RealSpec) (PrssKeys C))
  batched settings.batchSize (fun js => do
    let outputs ← liftM (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter js)
    tell [(js, outputs)]
    pure outputs) jobs

/-- The ceremonies of a tree at operator `i`, as in `newTree`, with the log of all its batches. -/
def loggedTree (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PartyM C E RealSpec (Option TreeOutput × BatchLog) :=
  (ceremonyOutput (m := LogM C E) (fun oa => hashStep oa)
    keys.parameter (loggedRun K circuits settings i keys) top tree).run.run' (0, 0)

/-- The outputs of one batch are right. They are the circuit values of its jobs on the PRF values of
`seeds`, with `H` fixed to `h`. -/
def RightBatch (h : Query C → HashOutput) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (jobs : List Job) (outputs : Option (List (List Bit))) : Prop :=
  outputs = some (jobs.map fun job => D prims h (evalJob circuits parameter seeds job))

omit [Fintype E] [DecidableEq E] in
/-- With right batches, a ceremony has the right outputs of all its jobs. -/
theorem sound_loggedRun (h : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (hsize : 0 < settings.batchSize) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    Sound h (RightBatch prims circuits h keys.parameter seeds)
      (· = evalRun prims circuits keys.parameter seeds h jobs) (loggedRun K circuits settings i keys jobs) := by
  let right := RightBatch prims circuits h keys.parameter seeds
  refine sound_bind h right _ _ _ _ (sound_true h right _) fun prss _ => ?_
  rw [evalRun_eq, ← batched_id settings.batchSize hsize]
  refine rel_batched (fun P x => Sound h right P x) (fun P b hb => sound_pure h right P b hb)
    (fun Q P x f hx hf => sound_bind h right Q P x f hx hf) _ _ _ (fun js => ?_) jobs
  refine sound_bind h right _ _ _ _ (sound_true h right _) fun o _ => ?_
  exact sound_bind h right _ _ _ _ (sound_tell h right js o) fun _ ho => sound_pure h right _ _ ho

omit [Fintype E] [DecidableEq E] in
/-- With right batches, the tree of an operator is `ceremonyAt`. -/
theorem sound_loggedTree (h : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (hsize : 0 < settings.batchSize) (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    Sound h (RightBatch prims circuits h keys.parameter seeds)
      (· = ceremonyAt prims circuits keys.parameter seeds h top tree)
      (ceremonyOutput (m := LogM C E) (fun oa => hashStep oa)
        keys.parameter (loggedRun K circuits settings i keys) top tree) := by
  let right := RightBatch prims circuits h keys.parameter seeds
  exact rel_ceremonyOutput (fun P x => Sound h right P x) (fun P b hb => sound_pure h right P b hb)
    (fun Q P x f hx hf => sound_bind h right Q P x f hx hf) _ (fun oa => D prims h (tweakable oa))
    (fun oa => sound_hash prims h right oa) _ _
    (fun js => sound_loggedRun prims K circuits settings h seeds hsize i keys js) keys.parameter top tree

omit [Fintype E] [DecidableEq E] in
/-- With its log dropped, a logged ceremony is `ceremonyRun` of `newTree`. -/
theorem dropLog_loggedRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    dropLog (loggedRun K circuits settings i keys jobs) =
      ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs := by
  unfold loggedRun
  rw [MonadHom.mmap_bind]
  simp only [monadHom_batched, MonadHom.mmap_bind, MonadHom.mmap_pure, dropLog_liftM, dropLog_tell, pure_bind, bind_pure]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- With its log dropped, `loggedTree` is `newTree`. -/
theorem newTree_eq_loggedTree (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    newTree K circuits settings i keys top tree =
      loggedTree K circuits settings i keys top tree >>= fun p => match p.1 with
        | some output => pure output
        | none => failure := by
  have key : dropLog (ceremonyOutput (m := LogM C E) (fun oa => hashStep oa) keys.parameter
      (loggedRun K circuits settings i keys) top tree) =
      ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
        (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys)
        top tree := by
    have hlift : ∀ {β : Type} (oa : OracleComp HashSpec β),
        dropLog (hashStep (C := C) (E := E) oa) = StateT.lift (oracleStep (tweakable oa)) :=
      fun oa => dropLog_liftM _
    rw [monadHom_ceremonyOutput]
    simp only [hlift, dropLog_loggedRun]
  have hdrop : ∀ (Y : LogM C E (Option TreeOutput)) (g : Option TreeOutput → PartyM C E RealSpec TreeOutput),
      (dropLog Y).run' (0, 0) >>= g = Y.run.run' (0, 0) >>= fun p => g p.1 := by
    intro Y g
    change (Prod.fst <$> Y.run).run' (0, 0) >>= g = _
    simp only [StateT.run'_eq, StateT.run_map, Functor.map_map, bind_map_left]
  unfold newTree
  rw [← key, hdrop]
  unfold loggedTree
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | output, log⟩ <;> rfl

omit [Fintype E] [DecidableEq E] in
/-- Hop H13 on the program of one operator. In each outcome of `loggedTree` with `H` fixed to `h`,
an output with right batches is `ceremonyAt` on the parameter of the operator. -/
theorem loggedTree_ceremonyAt (h : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (hsize : 0 < settings.batchSize) (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    ∀ z ∈ support (simulateQ (fixHash h) (loggedTree K circuits settings i keys top tree).run),
      ∀ (output : TreeOutput) (log : BatchLog), z = some (some output, log) →
        (∀ e ∈ log, RightBatch prims circuits h keys.parameter seeds e.1 e.2) →
        some output = ceremonyAt prims circuits keys.parameter seeds h top tree := by
  intro z hz output log hzeq hlog
  subst hzeq
  unfold loggedTree at hz
  rw [StateT.run'_eq, OptionT.run_map, simulateQ_map, support_map] at hz
  obtain ⟨o, ho, hz⟩ := hz
  rcases o with _ | ⟨⟨a, w⟩, s'⟩
  · simp at hz
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact sound_loggedTree prims K circuits settings h seeds hsize i keys top tree (0, 0) _ ho _ _ s' rfl hlog

omit [Fintype E] [DecidableEq E] in
/-- Hop H13 on the program of one operator, with `referenceTree`. In each outcome of `loggedTree`
with `H` fixed to a good `h`, an output with right batches is the output of `referenceTree` on the
PRF values of `seeds`, the parameter of the operator and its top tree, when the circuits compute
`Th`. -/
theorem loggedTree_referenceTree (hc : CircuitsCompute circuits prims.Th) (h : Query C → HashOutput)
    (hg : Good prims h) (seeds : C.Term → HashOutput) (hsize : 0 < settings.batchSize) (i : C.Party)
    (keys : Keys C) (top : TopTree) (tree : Tree) :
    ∀ z ∈ support (simulateQ (fixHash h) (loggedTree K circuits settings i keys top tree).run),
      ∀ (output : TreeOutput) (log : BatchLog), z = some (some output, log) →
        (∀ e ∈ log, RightBatch prims circuits h keys.parameter seeds e.1 e.2) →
        some output = D prims h (referenceTree tweakable (prfValue seeds) keys.parameter top tree) := by
  intro z hz output log hzeq hlog
  rw [loggedTree_ceremonyAt prims K circuits settings h seeds hsize i keys top tree z hz output log hzeq hlog,
    ceremonyAt_eq_referenceTree prims circuits hc hg]

end Logged

/-! ## The runs of a tree on the network -/

section Network

variable {E : Type} [Field E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Right tuples of one batch. On the honest views of the tuples `x`, each position of each tuple
has `z = x * y`. It is the negation of `WrongTuple`. -/
def RightTuples (D : C.Coalition) (x : C.Party → List (Tuple C)) : Prop :=
  ¬ WrongTuple D x

/-- `newTree` with the log of its batches in its output. It aborts as `newTree` does. -/
def loggedProgram (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PartyM C E RealSpec (TreeOutput × BatchLog) :=
  loggedTree K circuits settings i keys top tree >>= fun p => match p.1 with
    | some output => pure (output, p.2)
    | none => failure

/-- `treeProgram` with the log of its batches in its output. -/
def loggedTreeProgram (i : C.Party) (operator : OperatorState C) : Tree → PartyM C E RealSpec (TreeOutput × BatchLog)
  | .top => match operator.keys with
    | some keys => loggedProgram K circuits settings i keys emptyTop .top
    | none => failure
  | .bottom b => match operator.keys, operator.top with
    | some keys, some top => loggedProgram K circuits settings i keys top (.bottom b)
    | _, _ => failure

/-- With its log dropped, `loggedProgram` is `newTree`. -/
theorem fst_loggedProgram (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    Prod.fst <$> loggedProgram K circuits settings i keys top tree = newTree K circuits settings i keys top tree := by
  rw [newTree_eq_loggedTree, loggedProgram, map_bind]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | output, log⟩
  · exact OptionT.ext (by simp [OptionT.run_failure])
  · simp

/-- With its log dropped, `loggedTreeProgram` is `treeProgram`. -/
theorem fst_loggedTreeProgram (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    Prod.fst <$> loggedTreeProgram K circuits settings i operator tree = treeProgram K circuits settings i operator tree := by
  have hfail : (Prod.fst <$> (failure : PartyM C E RealSpec (TreeOutput × BatchLog))) = failure :=
    OptionT.ext (by simp [OptionT.run_failure])
  cases tree with
  | top =>
    unfold loggedTreeProgram treeProgram
    rcases operator.keys with _ | keys
    · exact hfail
    · exact fst_loggedProgram K circuits settings i keys emptyTop .top
  | bottom b =>
    unfold loggedTreeProgram treeProgram
    rcases operator.keys with _ | keys <;> rcases operator.top with _ | top
    · exact hfail
    · exact hfail
    · exact hfail
    · exact fst_loggedProgram K circuits settings i keys top (.bottom b)

omit [Field E] [Algebra Bit E] in
/-- A map of each honest program is a map of the outputs of the phase in the world. -/
theorem executePhase_worldRoles_map {I O L R Ia α β : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α)
    (f : α → β) :
    executePhase worldRoles D A F fuel st (fun i => f <$> p i) =
      (fun r => (r.1, fun i => (r.2 i).map f)) <$> executePhase worldRoles D A F fuel st p := by
  unfold executePhase
  rw [startSteps_map worldRoles worldRoles_honest_map, bind_map_left, map_bind]
  exact bind_congr fun steps => executeRounds_map worldRoles worldRoles_honest_map D A F f fuel st steps

/-- Each outcome of a run of `treeProgram` in a world is the outcome of a run of `loggedTreeProgram`
with the logs dropped. -/
theorem treeRun_logged {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (st : net.State)
    (operators : C.Party → OperatorState C) (tree : Tree) (s : σ)
    (z : (net.State × (C.Party → Option TreeOutput)) × σ)
    (hz : z ∈ support ((simulateQ impl (executePhase worldRoles D net noFunctionality fuel st
      fun i => treeProgram K circuits settings i (operators i) tree)).run s)) :
    ∃ z' ∈ support ((simulateQ impl (executePhase worldRoles D net noFunctionality fuel st
        fun i => loggedTreeProgram K circuits settings i (operators i) tree)).run s),
      z'.2 = z.2 ∧ z'.1.1 = z.1.1 ∧ ∀ i, z.1.2 i = (z'.1.2 i).map Prod.fst := by
  simp only [← fst_loggedTreeProgram K circuits settings _ (operators _) tree] at hz
  rw [executePhase_worldRoles_map, simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  exact ⟨z', hz', rfl, rfl, fun _ => rfl⟩

/-- The projection of a run on the network on the path of one honest operator. For each outcome of a
run of programs in the world `impl` from each state, each good `h` that agrees with the final hash
cache `cacheOf` and each honest operator with an output, the output is an outcome of its program
with `H` fixed to `h`. -/
def ProjectsOnPaths {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (cacheOf : σ → HashCache C) :
    Prop :=
  ∀ {α : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (st : net.State)
    (program : C.Party → PartyM C E RealSpec α) (s : σ) (z : (net.State × (C.Party → Option α)) × σ),
    z ∈ support ((simulateQ impl (executePhase worldRoles D net noFunctionality fuel st program)).run s) →
    ∀ h, Good prims h → Agrees h (cacheOf z.2) → ∀ i, i ∉ D.1 → ∀ a, z.1.2 i = some a →
      some a ∈ support (simulateQ (fixHash h) (program i).run)

/-- Hop H13 on the network. In a run of the logged tree programs in a world with `ProjectsOnPaths`,
an honest output whose log has only right batches on `seeds` is the output of `referenceTree` on the
PRF values of `seeds`, with the parameter and the top tree of its operator and `H` fixed to each good
`h` that agrees with the final cache. -/
theorem runOutput_referenceTree [Fintype E] [DecidableEq E] {σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (cacheOf : σ → HashCache C)
    (hproj : ProjectsOnPaths (E := E) prims impl cacheOf) (hc : CircuitsCompute circuits prims.Th)
    (hsize : 0 < settings.batchSize) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ)
    (st : net.State) (operators : C.Party → OperatorState C) (tree : Tree) (s : σ)
    (z : (net.State × (C.Party → Option (TreeOutput × BatchLog))) × σ)
    (hz : z ∈ support ((simulateQ impl (executePhase worldRoles D net noFunctionality fuel st
      fun i => loggedTreeProgram K circuits settings i (operators i) tree)).run s))
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h (cacheOf z.2)) (i : C.Party) (hi : i ∉ D.1)
    (output : TreeOutput) (log : BatchLog) (hout : z.1.2 i = some (output, log)) (keys : Keys C) (top : TopTree)
    (hprogram : loggedTreeProgram K circuits settings i (operators i) tree =
      loggedProgram K circuits settings i keys top tree)
    (seeds : C.Term → HashOutput) (hright : ∀ e ∈ log, RightBatch prims circuits h keys.parameter seeds e.1 e.2) :
    some output =
      ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable (prfValue seeds) keys.parameter top tree) := by
  have hpath := hproj D net fuel st _ s z hz h hg ha i hi _ hout
  rw [hprogram, loggedProgram, OptionT.run_bind, Option.elimM, simulateQ_bind, mem_support_bind_iff] at hpath
  obtain ⟨o, ho, hpath⟩ := hpath
  rcases o with _ | ⟨_ | output', log'⟩
  · simp at hpath
  · simp [OptionT.run_failure] at hpath
  · simp at hpath
    obtain ⟨rfl, rfl⟩ := hpath
    exact loggedTree_referenceTree prims K circuits settings hc h hg seeds hsize i keys top tree _ ho
      output log rfl hright

end Network

/-! ## The values that the honest operators fix -/

section Fixed

/-- Each term has an honest holder. A term has `t` holders and the coalition has at most `t - 1`
operators. -/
theorem exists_honest_holder (D : C.Coalition) (T : C.Term) : ∃ i, i ∈ C.holders T ∧ i ∉ D.1 := by
  by_contra hne
  have hcard := Finset.card_le_card (show C.holders T ⊆ D.1 from fun i hi => by
    by_contra hiD
    exact hne ⟨i, hi, hiD⟩)
  have hD := D.2
  have hT := T.2
  have ht := C.one_le_t
  simp only [Committee.holders, Finset.card_compl, Fintype.card_fin, Committee.n] at hcard
  omega

/-- With no `seedsDiffer`, each honest holder of a term with keys holds the seed of the game. -/
theorem seed_eq_gameSeeds (D : C.Coalition) (keys : C.Party → Option (Keys C))
    (hsame : seedsDiffer D keys = false) (i : C.Party) (hi : i ∉ D.1) (ki : Keys C) (hk : keys i = some ki)
    (T : C.Term) (hT : i ∈ C.holders T) : ki.seed T = gameSeeds D keys T := by
  unfold gameSeeds
  split
  · rename_i j hj
    have hj' := List.find?_some hj
    simp only [decide_eq_true_eq] at hj'
    obtain ⟨hjT, hjD, hjk⟩ := hj'
    obtain ⟨kj, hkj⟩ := Option.isSome_iff_exists.1 hjk
    rw [hkj]
    by_contra hne
    have : seedsDiffer D keys = true := by
      unfold seedsDiffer
      exact decide_eq_true ⟨i, j, ki, kj, hi, hjD, hk, hkj, Or.inr (Or.inl ⟨T, hT, hjT, hne⟩)⟩
    simp [hsame] at this
  · rename_i hnone
    have := List.find?_eq_none.1 hnone i (List.mem_finRange i)
    simp [hT, hi, hk] at this

/-- With no `seedsDiffer`, each honest operator with keys holds the parameter of the game. -/
theorem parameter_eq_gameParameter (D : C.Coalition) (keys : C.Party → Option (Keys C))
    (hsame : seedsDiffer D keys = false) (i : C.Party) (hi : i ∉ D.1) (ki : Keys C) (hk : keys i = some ki) :
    ki.parameter = gameParameter D keys := by
  unfold gameParameter
  split
  · rename_i j hj
    have hj' := List.find?_some hj
    simp only [decide_eq_true_eq] at hj'
    obtain ⟨hjD, hjk⟩ := hj'
    obtain ⟨kj, hkj⟩ := Option.isSome_iff_exists.1 hjk
    rw [hkj]
    by_contra hne
    have : seedsDiffer D keys = true := by
      unfold seedsDiffer
      exact decide_eq_true ⟨i, j, ki, kj, hi, hjD, hk, hkj, Or.inl hne⟩
    simp [hsame] at this
  · rename_i hnone
    have := List.find?_eq_none.1 hnone i (List.mem_finRange i)
    simp [hi, hk] at this

end Fixed

end ThresholdLeanXmss.Sketch

/-- info: 'ThresholdLeanXmss.Sketch.runOutput_referenceTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmss.Sketch.runOutput_referenceTree

/-- info: 'ThresholdLeanXmss.Sketch.loggedTree_referenceTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmss.Sketch.loggedTree_referenceTree

/-- info: 'ThresholdLeanXmss.Sketch.newTree_eq_loggedTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmss.Sketch.newTree_eq_loggedTree
