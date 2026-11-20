import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.Pilot.Pilot

/-!
# The outputs of a batch and of a tree

Right tuples and a good opening give a right output of one batch. Right batch outputs give the
output of `referenceTree` (`loggedTree_referenceTree`), and a run of a tree whose logged batches are
right gives the output of `referenceTree` (`runOutput_referenceTree`). `openedSums_agree` states that
two honest operators that pass the hash check of `OpenRep` of one batch open the same sums, when
their shares agree, the honest messages arrive as sent, and `CopySound` holds at both receivers.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

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
/-- The output of one operator from right batches. In each outcome of `loggedTree` with `H` fixed to `h`,
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
/-- The output of one operator from right batches, with `referenceTree`. In each outcome of `loggedTree`
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

/-- The outputs of a run on the network from right batches. In a run of the logged tree programs in a
world with `ProjectsOnPaths`, an honest output whose log has only right batches on `seeds` is the output
of `referenceTree` on the PRF values of `seeds`, with the parameter and the top tree of its operator and
`H` fixed to each good `h` that agrees with the final cache. -/
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

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The holder that `reconstruct` reads -/

section Glue

/-- The first honest holder of term `T` in the order of `C.parties`. `reconstruct` on the honest
views reads term `T` from it. -/
def refHolder (D : C.Coalition) (T : C.Term) : C.Party :=
  (C.parties.find? fun j => j ∈ C.holders T ∧ j ∉ D.1).get (by
    obtain ⟨j, hj, hjD⟩ := exists_honest_holder D T
    exact List.find?_isSome.2 ⟨j, List.mem_finRange j, by simp [hj, hjD]⟩)

theorem refHolder_spec (D : C.Coalition) (T : C.Term) : refHolder D T ∈ C.holders T ∧ refHolder D T ∉ D.1 := by
  unfold refHolder
  generalize_proofs hp
  have h := List.find?_some (Option.some_get hp).symm
  simpa using h

theorem reconstruct_honest {α : Type} [Inhabited α] (D : C.Coalition) (views : C.Party → Option (C.Term → α))
    (f : C.Party → C.Term → α) (hv : ∀ j, views j = if j ∈ D.1 then none else some (f j)) (T : C.Term) :
    reconstruct views T = f (refHolder D T) T := by
  have key : ∀ l : List C.Party,
      ((l.filterMap fun i => if i ∈ C.holders T then views i else none).head?.map (· T)) =
        (l.find? fun j => j ∈ C.holders T ∧ j ∉ D.1).map fun j => f j T := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : a ∈ C.holders T ∧ a ∉ D.1
      · simp [hv a, ha.1, ha.2, List.find?_cons_of_pos]
      · rw [List.find?_cons_of_neg (by simpa using ha), ← ih, List.filterMap_cons]
        by_cases h1 : a ∈ C.holders T
        · have h2 : a ∈ D.1 := by tauto
          simp [h1, hv a, h2]
        · simp [h1]
  unfold reconstruct refHolder
  rw [key, Option.map_eq_some_iff.2 ⟨_, Option.some_get _ |>.symm, rfl⟩]
  rfl

end Glue

/-! ## The trace of one batch at one operator -/

section Trace

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)

/-- One AND layer of `runJobs` with the products `zs l` of layer `l`. -/
def layerStep (zs : ℕ → Shares C Bit) (p : List (C.Term → List Bit) × List (Tuple C)) (l : ℕ) :
    List (C.Term → List Bit) × List (Tuple C) :=
  (appendLayer jobs l p.1 (zs l),
    p.2 ++ [⟨layerX K jobs l p.1, layerY K jobs l p.1, zs l, (gatesAt jobs l).length, mode⟩])

/-- The wires and the tuples after the first `d` AND layers of `runJobs` on `inputs`, with the
products `zs`. -/
def layerPrefix (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    List (C.Term → List Bit) × List (Tuple C) :=
  (List.range d).foldl (layerStep K mode jobs zs) (inputs, [])

/-- The tuples that `runJobs` on `inputs` gives to the check, with the products `zs` of the layers
and the sharing `v'` after `Rerand`. -/
def batchTuples (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) :
    List (Tuple C) :=
  (layerPrefix K mode jobs inputs zs (depth jobs)).2 ++
    [⟨outputShares K jobs (layerPrefix K mode jobs inputs zs (depth jobs)).1, one K, v', (outputsOf jobs).length, .peer⟩]

theorem layerPrefix_succ (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    layerPrefix K mode jobs inputs zs (d + 1) = layerStep K mode jobs zs (layerPrefix K mode jobs inputs zs d) d := by
  simp [layerPrefix, List.range_succ, List.foldl_append]

theorem layerPrefix_tuples (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    (layerPrefix K mode jobs inputs zs d).2 = (List.range d).map fun l =>
      ⟨layerX K jobs l (layerPrefix K mode jobs inputs zs l).1, layerY K jobs l (layerPrefix K mode jobs inputs zs l).1,
        zs l, (gatesAt jobs l).length, mode⟩ := by
  induction d with
  | zero => rfl
  | succ d ih => rw [layerPrefix_succ, layerStep, ih, List.range_succ, List.map_append, List.map_singleton]

theorem length_batchTuples (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) :
    (batchTuples K mode jobs inputs zs v').length = depth jobs + 1 := by
  simp [batchTuples, layerPrefix_tuples]

theorem batchTuples_layer (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) (l : ℕ)
    (hl : l < depth jobs) :
    (batchTuples K mode jobs inputs zs v')[l]? = some ⟨layerX K jobs l (layerPrefix K mode jobs inputs zs l).1,
      layerY K jobs l (layerPrefix K mode jobs inputs zs l).1, zs l, (gatesAt jobs l).length, mode⟩ := by
  rw [batchTuples, List.getElem?_append_left (by simpa [layerPrefix_tuples] using hl), layerPrefix_tuples]
  simp [List.getElem?_range hl]

theorem batchTuples_output (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) :
    (batchTuples K mode jobs inputs zs v')[depth jobs]? = some ⟨outputShares K jobs
      (layerPrefix K mode jobs inputs zs (depth jobs)).1, one K, v', (outputsOf jobs).length, .peer⟩ := by
  rw [batchTuples, List.getElem?_append_right (by simp [layerPrefix_tuples])]
  simp [layerPrefix_tuples]

/-- Two traces agree on term `T`. -/
def AgreeAt (T : C.Term) (p q : List (C.Term → List Bit) × List (Tuple C)) : Prop :=
  p.1.length = q.1.length ∧ (∀ k, (p.1.getD k fun _ => []) T = (q.1.getD k fun _ => []) T) ∧
    p.2.length = q.2.length ∧ ∀ m : ℕ, (p.2[m]?).map (fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)) =
      (q.2[m]?).map fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)

theorem agreeAt_layerStep (T : C.Term) (zs zs' : ℕ → Shares C Bit) (p q : List (C.Term → List Bit) × List (Tuple C))
    (l : ℕ) (h : AgreeAt T p q) (hz : zs l T = zs' l T) :
    AgreeAt T (layerStep K mode jobs zs p l) (layerStep K mode jobs zs' q l) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [layerStep, length_appendLayer, h1], fun k => ?_, by simp [layerStep, h3], fun m => ?_⟩
  · simp only [layerStep, getD_appendLayer, h1]
    split_ifs
    · simp only [newWires, hz, h2 k]
    · rfl
  · simp only [layerStep, List.getElem?_append, h3]
    split_ifs
    · exact h4 m
    · simp only [List.getElem?_singleton]
      split_ifs
      · simp [layerX_congr K jobs l p.1 q.1 T h2, layerY_congr K jobs l p.1 q.1 T h2, hz]
      · rfl

theorem agreeAt_layerPrefix (T : C.Term) (I I' : List (C.Term → List Bit)) (zs zs' : ℕ → Shares C Bit)
    (hI : I.length = I'.length) (hIT : ∀ k, (I.getD k fun _ => []) T = (I'.getD k fun _ => []) T)
    (hz : ∀ l, zs l T = zs' l T) (d : ℕ) :
    AgreeAt T (layerPrefix K mode jobs I zs d) (layerPrefix K mode jobs I' zs' d) := by
  induction d with
  | zero => exact ⟨hI, hIT, rfl, fun _ => rfl⟩
  | succ d ih => rw [layerPrefix_succ, layerPrefix_succ]; exact agreeAt_layerStep K mode jobs T zs zs' _ _ d ih (hz d)

theorem batchTuples_agreeAt (T : C.Term) (I I' : List (C.Term → List Bit)) (zs zs' : ℕ → Shares C Bit)
    (v v'' : Shares C Bit) (h : AgreeAt T (layerPrefix K mode jobs I zs (depth jobs)) (layerPrefix K mode jobs I' zs' (depth jobs)))
    (hv : v T = v'' T) (m : ℕ) :
    ((batchTuples K mode jobs I zs v)[m]?).map (fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)) =
      ((batchTuples K mode jobs I' zs' v'')[m]?).map fun τ : Tuple C => (τ.x T, τ.y T, τ.z T) := by
  obtain ⟨-, h2, h3, h4⟩ := h
  simp only [batchTuples, List.getElem?_append, h3]
  split_ifs
  · exact h4 m
  · simp only [List.getElem?_singleton]
    split_ifs
    · simp [outputShares_congr K jobs _ _ T h2, hv]
    · rfl

theorem batchTuples_shape (I : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v : Shares C Bit) :
    (batchTuples K mode jobs I zs v).map (fun τ : Tuple C => (τ.count, τ.mode)) =
      (List.range (depth jobs)).map (fun l => ((gatesAt jobs l).length, mode)) ++ [((outputsOf jobs).length, .peer)] := by
  simp [batchTuples, layerPrefix_tuples]

end Trace

/-! ## The tuples that `reconstruct` reads are one glued trace -/

section Glued

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)

/-- The glued products, each term from its holder `refHolder D T`. -/
def gluedProducts (D : C.Coalition) (zs : C.Party → ℕ → Shares C Bit) : ℕ → Shares C Bit :=
  fun l T => zs (refHolder D T) l T

/-- The glued sharing after `Rerand`, each term from its holder `refHolder D T`. -/
def gluedShares (D : C.Coalition) (v' : C.Party → Shares C Bit) : Shares C Bit :=
  fun T => v' (refHolder D T) T

/-- `reconstruct` on the honest views of the tuples of the honest traces reads the glued trace. The
glued inputs `I` agree with the inputs of the holder of each term. -/
theorem tupleAt_glued (D : C.Coalition) (inputs : C.Party → List (C.Term → List Bit))
    (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit) (x : C.Party → List (Tuple C))
    (hx : ∀ j, j ∉ D.1 → x j = batchTuples K mode jobs (inputs j) (zs j) (v' j)) (I : List (C.Term → List Bit))
    (hI : ∀ T, I.length = (inputs (refHolder D T)).length ∧
      ∀ k, (I.getD k fun _ => []) T = ((inputs (refHolder D T)).getD k fun _ => []) T)
    (m : ℕ) (τ : Tuple C) (hτ : (batchTuples K mode jobs I (gluedProducts D zs) (gluedShares D v'))[m]? = some τ) :
    (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x = τ.x ∧
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y = τ.y ∧
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z = τ.z ∧
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count = τ.count := by
  have hm : m < depth jobs + 1 := by
    rw [← length_batchTuples K mode jobs I (gluedProducts D zs) (gluedShares D v')]
    exact (List.getElem?_eq_some_iff.1 hτ).1
  have hsome : ∀ j, j ∉ D.1 → ∃ σ, (x j)[m]? = some σ := fun j hj =>
    ⟨(x j)[m]'(by rw [hx j hj, length_batchTuples]; exact hm), List.getElem?_eq_getElem _⟩
  have hagree : ∀ T, ((x (refHolder D T))[m]?).map (fun σ : Tuple C => (σ.x T, σ.y T, σ.z T)) =
      some (τ.x T, τ.y T, τ.z T) := by
    intro T
    have h := batchTuples_agreeAt K mode jobs T I (inputs (refHolder D T)) (gluedProducts D zs)
      (zs (refHolder D T)) (gluedShares D v') (v' (refHolder D T))
      (agreeAt_layerPrefix K mode jobs T _ _ (gluedProducts D zs) (zs (refHolder D T)) (hI T).1 (hI T).2
        (fun l => rfl) _) rfl m
    rw [hx _ (refHolder_spec D T).2, ← h, hτ]
    rfl
  have hrec : ∀ (part : Tuple C → Shares C Bit) (hpart : ∀ T, ((x (refHolder D T))[m]?).map (fun σ => part σ T) =
      some (part τ T)),
      reconstruct (fun i => ((if i ∈ D.1 then none else some (x i)).bind (·[m]?)).map part) = part τ := by
    intro part hpart
    funext T
    rw [reconstruct_honest D _ (fun j => (((x j)[m]?).map part).getD fun _ _ => 0) (fun j => ?_) T]
    · have := hpart T
      rcases h : (x (refHolder D T))[m]? with _ | σ
      · rw [h] at this; cases this
      · rw [h] at this
        simpa using this
    · by_cases hj : j ∈ D.1
      · simp [hj]
      · obtain ⟨σ, hσ⟩ := hsome j hj
        simp [hj, hσ]
  have hpart : ∀ T, ∃ σ, (x (refHolder D T))[m]? = some σ ∧ σ.x T = τ.x T ∧ σ.y T = τ.y T ∧ σ.z T = τ.z T := by
    intro T
    have := hagree T
    rcases h : (x (refHolder D T))[m]? with _ | σ
    · simp [h] at this
    · simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨σ, rfl, this⟩
  refine ⟨hrec _ fun T => ?_, hrec _ fun T => ?_, hrec _ fun T => ?_, ?_⟩
  · obtain ⟨σ, hσ, h⟩ := hpart T; simp [hσ, h.1]
  · obtain ⟨σ, hσ, h⟩ := hpart T; simp [hσ, h.2.1]
  · obtain ⟨σ, hσ, h⟩ := hpart T; simp [hσ, h.2.2]
  · obtain ⟨j, hj, hfirst⟩ := firstInput_honest D x
    unfold tupleAt
    simp only [hfirst]
    have h1 := congrArg (·[m]?) (batchTuples_shape K mode jobs (inputs j) (zs j) (v' j))
    have h2 := congrArg (·[m]?) (batchTuples_shape K mode jobs I (gluedProducts D zs) (gluedShares D v'))
    simp only [List.getElem?_map, hτ, ← hx j hj] at h1 h2
    rw [← h2] at h1
    rcases hxj : (x j)[m]? with _ | σ
    · rw [hxj] at h1; cases h1
    · rw [hxj] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      simp [h1.1]

/-- The agreement of the copies of `F_multVerify` gives the agreement of the honest copies of the
sharing after `Rerand`, which is `z` of the last tuple. -/
theorem shares_agree_of_multVerifyAgree (D : C.Coalition) (inputs : C.Party → List (C.Term → List Bit))
    (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit) (x : C.Party → List (Tuple C))
    (hx : ∀ j, j ∉ D.1 → x j = batchTuples K mode jobs (inputs j) (zs j) (v' j))
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    ∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
      ∀ g < (outputsOf jobs).length, v' j T g = v' j' T g := by
  intro T j j' hj hj' hjT hj'T g hg
  obtain ⟨j₀, hj₀, hfirst⟩ := firstInput_honest D x
  have hlast : ∀ k, k ∉ D.1 → (x k)[depth jobs]? = some ⟨outputShares K jobs
      (layerPrefix K mode jobs (inputs k) (zs k) (depth jobs)).1, one K, v' k, (outputsOf jobs).length, .peer⟩ :=
    fun k hk => by rw [hx k hk, batchTuples_output]
  have hcount : (((List.range (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length).map
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)))).getD (depth jobs)
        ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count = (outputsOf jobs).length := by
    rw [hfirst, hx j₀ hj₀, length_batchTuples, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, tupleAt, hfirst, hlast j₀ hj₀]
  have h := hagree (depth jobs) (by rw [hfirst, hx j₀ hj₀, length_batchTuples]; omega) T j hjT j' hj'T hj hj' g
    (by rw [hcount]; exact hg)
  simp only [hj, hj', ↓reduceIte, Option.bind_some, hlast j hj, hlast j' hj', Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at h
  exact h.2.2

end Glued

/-! ## The values of one trace with product tuples -/

section Values

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)

/-- `appendLayer` reads the products only at the gates of the layer. -/
theorem appendLayer_congr (l : ℕ) (w : List (C.Term → List Bit)) (z z' : Shares C Bit)
    (h : ∀ T g, g < (gatesAt jobs l).length → z T g = z' T g) :
    appendLayer jobs l w z = appendLayer jobs l w z' := by
  unfold appendLayer
  refine List.map_congr_left fun p _ => funext fun T => ?_
  obtain ⟨w', k⟩ := p
  dsimp only
  congr 1
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hq, -⟩ := List.mem_filter.1 hq
  have hlt := List.snd_lt_of_mem_zipIdx hq
  obtain ⟨a, g⟩ := q
  exact h T g (by simpa using hlt)

variable (x : C.Party → List (C.Term → List Bit))

/-- With product tuples, the wires of a trace from the common inputs keep the invariant `LayerInv`
of the honest run. -/
theorem layerInv_layerPrefix (hx : MainInputs jobs noCoalition x) (Z : ℕ → Shares C Bit)
    (hprod : ∀ l < depth jobs, ∀ g < (gatesAt jobs l).length, shareValue (Z l) g =
      shareValue (layerX K jobs l (layerPrefix K mode jobs
        ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z l).1) g *
      shareValue (layerY K jobs l (layerPrefix K mode jobs
        ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z l).1) g) :
    ∀ d ≤ depth jobs, ∃ p Ts, LayerInv jobs x d p (layerPrefix K mode jobs
      ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z d).1 Ts := by
  intro d
  induction d with
  | zero => exact fun _ => ⟨_, _, layerInv_zero jobs x hx⟩
  | succ d ih =>
    intro hd
    obtain ⟨p, Ts, hinv⟩ := ih (by omega)
    set W := (layerPrefix K mode jobs ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z d).1
    set n := (gatesAt jobs d).length
    have hX : ∀ i T, i ∈ C.holders T → ∀ g, layerX K jobs d (p i).1 T g = layerX K jobs d W T g :=
      fun i T h g => by rw [layerX_congr K jobs d _ _ T (hinv.agree i T h)]
    have hY : ∀ i T, i ∈ C.holders T → ∀ g, layerY K jobs d (p i).1 T g = layerY K jobs d W T g :=
      fun i T h g => by rw [layerY_congr K jobs d _ _ T (hinv.agree i T h)]
    have hz : ∀ g, ∑ T, (fun T g => if g < n then Z d T g else 0) T g =
        ∑ i, mulRep K (localContext i) (layerX K jobs d (p i).1) (layerY K jobs d (p i).1) g := by
      intro g
      rw [mulRep_views_sum K _ _ (layerX K jobs d W) (layerY K jobs d W) g (fun i T h => hX i T h g)
        (fun i T h => hY i T h g)]
      by_cases hg : g < n
      · simp only [hg, ite_true]
        exact hprod d (by omega) g hg
      · have h0 : ∀ T, layerX K jobs d W T g = 0 := fun T => by
          simp [layerX, List.getElem?_eq_none (show (gatesAt jobs d).length ≤ g by omega)]
        simp [hg, shareValue, h0]
    have := layerInv_step K jobs x mode d p W Ts hinv _ hz
    rw [layerPrefix_succ, layerStep]
    dsimp only
    rw [appendLayer_congr jobs d W (Z d) _ fun T g hg => (show Z d T g = if g < n then
      (fun T g => if g < n then Z d T g else 0) T g else 0 by simp [n, hg])]
    exact ⟨_, _, this⟩

end Values

/-! ## The opening -/

section Opening

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The copy hashes that operator `j` sends in `OpenRep` of `v` with `H` fixed to `h`. -/
def copyHashes (h : Query C → HashOutput) (v : Shares C Bit) (count : ℕ) : List HashOutput :=
  C.terms.map fun T => h (.copy (vector count (v T)))

theorem copyHashes_idxOf (h : Query C → HashOutput) (v : Shares C Bit) (count : ℕ) (T : C.Term) :
    (copyHashes h v count)[C.terms.idxOf T]? = some (h (.copy (vector count (v T)))) := by
  rw [copyHashes, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_terms T))]
  simp

/--
The honest messages arrive as sent, and no received copy has the hash of a different honest copy of
the same term. -/
theorem repCopy_sound (D : C.Coalition) (h : Query C → HashOutput) (w : Shares C Bit)
    (vr : C.Party → Shares C Bit) (count : ℕ)
    (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < count → vr j T g = w T g)
    (i : C.Party) (hiD : i ∉ D.1) (inbox : Mail C E)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (vr j) count (copyHashes h (vr j) count) i)
    (hcheck : repCheck K i inbox (copyHashes h (repCopy K i (vr i) count inbox) count))
    (hcopy : ∀ T j, j ∉ D.1 → j ∈ C.holders T →
      h (.copy (vector count (vr j T))) = h (.copy (vector count (repCopy K i (vr i) count inbox T))) →
      vector count (vr j T) = vector count (repCopy K i (vr i) count inbox T))
    (T : C.Term) (g : ℕ) (hg : g < count) :
    repCopy K i (vr i) count inbox T g = w T g := by
  by_cases hiT : i ∈ C.holders T
  · simpa only [repCopy, hiT, ↓reduceIte] using hvr i T g hiD hiT hg
  by_cases hown : K.owner T ∉ D.1
  · have hne : i ≠ K.owner T := fun e => hiT (e ▸ K.owner_held T)
    simp only [repCopy, hiT, hinbox _ hown (Ne.symm hne), repOutbox, hne, ↓reduceIte,
      Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hiT]⟩)
      (terms_nodup.filter _) g hg]
    exact hvr _ T g hown (K.owner_held T) hg
  · obtain ⟨j, hjT, hjD⟩ := exists_honest_holder D T
    have hne : j ≠ K.owner T := fun e => hown (e ▸ hjD)
    have hc := hcheck T hiT j hjT hne
    dsimp only at hc
    rw [hinbox j hjD (fun e => hiT (e ▸ hjT)), main_open_hash_sent K i j (vr j) count _ (by simp [copyHashes]) T hiT hjT hne,
      lookup_zip_idxOf C.terms _ (by simp [copyHashes]) T (mem_terms T), copyHashes_idxOf,
      copyHashes_idxOf] at hc
    have heq := hcopy T j hjD hjT (Option.some.inj hc)
    have heqg := congrArg (fun l : List Bit => l.getD g 0) heq
    have hvec : ∀ f : ℕ → Bit, (vector count f).getD g 0 = f g := by
      intro f
      simp [vector, List.getD_eq_getElem?_getD, List.getElem?_range hg]
    rw [hvec, hvec] at heqg
    exact heqg.symm.trans (hvr j T g hjD hjT hg)

end Opening

/-! ## The opened outputs of a batch -/

section Output

variable {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E) (mode : ReshareMode)
  (circuits : Circuits)

theorem batchInputs_congr (h : Query C → HashOutput) (seed seeds : C.Term → HashOutput) (jobs : List Job)
    (j : C.Party) (hseed : ∀ T, j ∈ C.holders T → seed T = seeds T) :
    batchInputs h seed jobs j = batchInputs h seeds jobs j := by
  unfold batchInputs
  refine List.map_congr_left fun job _ => funext fun T => ?_
  split_ifs with hj
  · simp [inputBits, hseed T hj]
  · rfl

/-- The opened outputs of one batch from right tuples. Take the tuples `x` of the honest operators, each
from the inputs of its keys, its products `zs j` and its sharing `v' j` after `Rerand`, the inbox of
`OpenRep` at the honest operator `i` and the hash check that `i` passes. Assume right tuples, agreeing
parameters and seeds, copies of `v'` that agree among the honest holders, the honest messages of
`OpenRep` as sent, and no copy collision. Then the opened outputs of `i` are the circuit values on the
PRF values of `seeds`. -/
theorem opened_right (parameter : PublicParameter) (jobs : List Job) (D : C.Coalition) (i : C.Party)
    (hiD : i ∉ D.1) (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C)
    (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit) (x : C.Party → List (Tuple C))
    (inbox : Mail C E)
    (hshape : ∀ j, j ∉ D.1 → x j = batchTuples K mode (jobs.map (circuits (keys j).parameter ·.kind))
      (batchInputs h (keys j).seed jobs j) (zs j) (v' j))
    (hparameter : ∀ j, j ∉ D.1 → (keys j).parameter = parameter)
    (hseed : ∀ j T, j ∉ D.1 → j ∈ C.holders T → (keys j).seed T = seeds T)
    (hright : RightTuples D x)
    (hagree : ∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
      ∀ g < (outputsOf (jobs.map (circuits parameter ·.kind))).length, v' j T g = v' j' T g)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (v' j) (outputsOf (jobs.map (circuits parameter ·.kind))).length
      (copyHashes h (v' j) (outputsOf (jobs.map (circuits parameter ·.kind))).length) i)
    (hcheck : repCheck K i inbox (copyHashes h (repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length
      inbox) (outputsOf (jobs.map (circuits parameter ·.kind))).length))
    (hcopy : ∀ T j, j ∉ D.1 → j ∈ C.holders T →
      h (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length (v' j T))) =
        h (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length
          (repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T))) →
      vector (outputsOf (jobs.map (circuits parameter ·.kind))).length (v' j T) =
        vector (outputsOf (jobs.map (circuits parameter ·.kind))).length
          (repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T)) :
    ThresholdLeanXmssSecurity.assemble (jobs.map (circuits parameter ·.kind))
        (fun g => ∑ T, repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T g) =
      jobs.map fun job => ThresholdLeanXmssSecurity.D prims h (evalJob circuits parameter seeds job) := by
  set circs := jobs.map (circuits parameter ·.kind) with hcircs
  set n := (outputsOf circs).length with hn
  set x0 := batchInputs h seeds jobs with hx0
  set W0 := (List.range circs.length).map fun k => reconstruct fun j => (x0 j)[k]? with hW0def
  set Z := gluedProducts D zs
  set V := gluedShares D v'
  have hshape' : ∀ j, j ∉ D.1 → x j = batchTuples K mode circs (x0 j) (zs j) (v' j) := fun j hj => by
    rw [hshape j hj, hparameter j hj, batchInputs_congr h _ seeds jobs j (hseed j · hj)]
  have hlen0 : ∀ j, (x0 j).length = jobs.length := fun j => by simp [hx0, batchInputs]
  have hW0 : ∀ k (hk : k < jobs.length) T, (W0.getD k fun _ => []) T = inputBits h seeds jobs[k] T := by
    intro k hk T
    rw [hW0def, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa [circs] using hk)]
    simp only [Option.map_some, Option.getD_some]
    refine reconstruct_of_agree _ T _ fun j hj =>
      ⟨fun T => if j ∈ C.holders T then inputBits h seeds jobs[k] T else [], ?_, by simp [hj]⟩
    simp [hx0, batchInputs, List.getElem?_eq_getElem hk]
  have hI : ∀ T, W0.length = (x0 (refHolder D T)).length ∧
      ∀ k, (W0.getD k fun _ => []) T = ((x0 (refHolder D T)).getD k fun _ => []) T := by
    intro T
    refine ⟨by simp [hW0def, circs, hlen0], fun k => ?_⟩
    rcases Nat.lt_or_ge k jobs.length with hk | hk
    · rw [hW0 k hk T, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen0]; exact hk)]
      simp [hx0, batchInputs, (refHolder_spec D T).1]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [W0, circs]; omega),
        List.getElem?_eq_none (by rw [hlen0]; exact hk)]
  -- The glued tuples are products.
  have hprod : ∀ (m : ℕ) (τ : Tuple C), (batchTuples K mode circs W0 Z V)[m]? = some τ → ∀ g < τ.count,
      shareValue τ.z g = shareValue τ.x g * shareValue τ.y g := by
    intro m τ hτ g hg
    obtain ⟨hxe, hye, hze, hce⟩ := tupleAt_glued K mode circs D x0 zs v' x hshape' W0 hI m τ hτ
    by_contra hne
    refine hright ⟨m, ?_, g, by rw [hce]; exact hg, ?_⟩
    · obtain ⟨j, hj, hfirst⟩ := firstInput_honest D x
      rw [hfirst, hshape' j hj, length_batchTuples]
      have := (List.getElem?_eq_some_iff.1 hτ).1
      rwa [length_batchTuples] at this
    · rw [hxe, hye, hze]
      exact sub_ne_zero.2 hne
  obtain ⟨p, Ts, hinv⟩ := layerInv_layerPrefix K mode circs x0 (batchInputs_main h seeds circuits parameter jobs) Z
    (fun l hl g hg => hprod l _ (batchTuples_layer K mode circs W0 Z V l hl) g hg) (depth circs) le_rfl
  rw [← mainOutputs_batch prims h seeds circuits parameter jobs]
  refine assemble_eq K circs x0 p _ Ts hinv _ fun g hg => ?_
  have hopen : ∀ T, repCopy K i (v' i) n inbox T g = V T g := fun T =>
    repCopy_sound K D h V v' n (fun j T g hj hjT hg => hagree T j (refHolder D T) hj (refHolder_spec D T).2 hjT
      (refHolder_spec D T).1 g hg) i hiD inbox hinbox hcheck hcopy T g hg
  have hout := hprod (depth circs) _ (batchTuples_output K mode circs W0 Z V) g hg
  simp only [shareValue_one, mul_one] at hout
  simp only [hopen]
  exact hout

end Output

/-! ## The outcomes of a program with `H` fixed -/

section Holds

variable {E : Type} (h : Query C → HashOutput)

/-- Each outcome `some a` of `x` with `H` fixed to `h` has `P a`. The rounds, `PRG` and the sampling
stay free. -/
def Holds {α : Type} (P : α → Prop) (x : PartyM C E RealSpec α) : Prop :=
  ∀ z ∈ support (simulateQ (fixHash h) x.run), ∀ a, z = some a → P a

theorem holds_pure {α : Type} (P : α → Prop) (a : α) (ha : P a) : Holds h P (pure a : PartyM C E RealSpec α) := by
  intro z hz b hb
  simp at hz
  subst hz
  cases hb
  exact ha

theorem holds_bind {α β : Type} (Q : α → Prop) (P : β → Prop) (x : PartyM C E RealSpec α)
    (f : α → PartyM C E RealSpec β) (hx : Holds h Q x) (hf : ∀ a, Q a → Holds h P (f a)) :
    Holds h P (x >>= f) := by
  intro z hz b hb
  subst hb
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, mem_support_bind_iff] at hz
  obtain ⟨o, ho, hz⟩ := hz
  rcases o with _ | a
  · simp at hz
  · exact hf a (hx _ ho a rfl) _ hz b rfl

theorem holds_require (c : Prop) : Holds h (fun _ => c) (require c : PartyM C E RealSpec Unit) := by
  intro z hz a ha
  unfold require at hz
  split_ifs at hz with hc
  · exact hc
  · simp [OptionT.run_failure] at hz
    subst hz
    cases ha

end Holds

section Pins

variable {E : Type} [Field E] [Algebra Bit E] (h : Query C → HashOutput) (prims : Primitives)

/-- A step of `H` calls has the value with `H` fixed to `h`. -/
def Pins {β : Type} (oa : OracleComp (RoSpec C) β) : Prop :=
  Holds (E := E) h (· = ThresholdLeanXmssSecurity.D prims h oa) (oracleStep oa)

theorem pins_pure {β : Type} (b : β) : Pins (E := E) h prims (pure b : OracleComp (RoSpec C) β) := by
  unfold Pins
  rw [oracleStep_pure]
  exact holds_pure h _ b rfl

theorem pins_bind {β γ : Type} (oa : OracleComp (RoSpec C) β) (f : β → OracleComp (RoSpec C) γ)
    (ha : Pins (E := E) h prims oa) (hf : ∀ b, Pins (E := E) h prims (f b)) : Pins (E := E) h prims (oa >>= f) := by
  unfold Pins at *
  rw [oracleStep_bind]
  refine holds_bind h _ _ _ _ ha fun b hb => ?_
  subst hb
  rw [D_bind]
  exact hf _

omit [Field E] [Algebra Bit E] in
theorem fixHash_oracleStep_hashQuery (q : Query C) :
    simulateQ (fixHash (E := E) (G := RealSpec) h) (oracleStep (hashQuery q) : PartyM C E RealSpec HashOutput).run =
      pure (some (h q)) := by
  rw [show hashQuery q = (query (spec := RoSpec C) (.inl q) >>= pure : OracleComp (RoSpec C) HashOutput) by
    simp [hashQuery]]
  simp only [oracleStep, localStep]
  simp [OptionT.run_lift]
  rfl

omit [Field E] [Algebra Bit E] in
theorem pins_hashQuery (q : Query C) : Pins (E := E) h prims (hashQuery q) := by
  intro z hz a ha
  subst ha
  rw [D_hashQuery, fixHash_oracleStep_hashQuery] at *
  simp at hz
  exact hz

theorem pins_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, Pins (E := E) h prims (f a)) :
    ∀ l : List α, Pins (E := E) h prims (l.mapM f)
  | [] => pins_pure h prims _
  | a :: l => by
    rw [List.mapM_cons]
    exact pins_bind h prims _ _ (hf a) fun _ => pins_bind h prims _ _ (pins_mapM f hf l) fun _ => pins_pure h prims _

end Pins

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace OpenedAgreement

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The premise on the copy hashes of `OpenRep` at operator `i` with `H` fixed to `h`. No received
copy has the hash of a different honest copy of the same term. -/
def CopySound (D : C.Coalition) (h : Query C → HashOutput) (vr : C.Party → Shares C Bit) (count : ℕ)
    (i : C.Party) (inbox : Mail C E) : Prop :=
  ∀ T j, j ∉ D.1 → j ∈ C.holders T →
    h (.copy (vector count (vr j T))) = h (.copy (vector count (repCopy K i (vr i) count inbox T))) →
    vector count (vr j T) = vector count (repCopy K i (vr i) count inbox T)

/-- The opened sum of an honest operator `i` that passes the hash check of `OpenRep` is the sum of
the agreed sharing `w`. -/
theorem openedSum_eq (D : C.Coalition) (h : Query C → HashOutput) (w : Shares C Bit)
    (vr : C.Party → Shares C Bit) (count : ℕ)
    (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < count → vr j T g = w T g)
    (i : C.Party) (hiD : i ∉ D.1) (inbox : Mail C E)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (vr j) count (copyHashes h (vr j) count) i)
    (hcheck : repCheck K i inbox (copyHashes h (repCopy K i (vr i) count inbox) count))
    (hcopy : CopySound K D h vr count i inbox) (g : ℕ) (hg : g < count) :
    ∑ T, repCopy K i (vr i) count inbox T g = ∑ T, w T g :=
  Finset.sum_congr rfl fun T _ => repCopy_sound K D h w vr count hvr i hiD inbox hinbox hcheck hcopy T g hg

/-- The equal opened sums. Two honest operators `i` and `i'` that pass the hash check of `OpenRep` of one batch,
with the honest messages as sent and no copy collision, open sums that are both the sum of the
agreed sharing `w` at each `g < count`. -/
theorem openedSums_agree (D : C.Coalition) (h : Query C → HashOutput) (w : Shares C Bit)
    (vr : C.Party → Shares C Bit) (count : ℕ)
    (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < count → vr j T g = w T g)
    (i i' : C.Party) (hiD : i ∉ D.1) (hiD' : i' ∉ D.1) (inbox inbox' : Mail C E)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (vr j) count (copyHashes h (vr j) count) i)
    (hinbox' : ∀ j, j ∉ D.1 → j ≠ i' → inbox' j = repOutbox K j (vr j) count (copyHashes h (vr j) count) i')
    (hcheck : repCheck K i inbox (copyHashes h (repCopy K i (vr i) count inbox) count))
    (hcheck' : repCheck K i' inbox' (copyHashes h (repCopy K i' (vr i') count inbox') count))
    (hcopy : CopySound K D h vr count i inbox) (hcopy' : CopySound K D h vr count i' inbox')
    (g : ℕ) (hg : g < count) :
    ∑ T, repCopy K i (vr i) count inbox T g = ∑ T, w T g ∧
      ∑ T, repCopy K i' (vr i') count inbox' T g = ∑ T, w T g :=
  ⟨openedSum_eq K D h w vr count hvr i hiD inbox hinbox hcheck hcopy g hg,
    openedSum_eq K D h w vr count hvr i' hiD' inbox' hinbox' hcheck' hcopy' g hg⟩

variable (prims : Primitives)

end OpenedAgreement

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.runOutput_referenceTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.runOutput_referenceTree

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.loggedTree_referenceTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.loggedTree_referenceTree

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.newTree_eq_loggedTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.newTree_eq_loggedTree

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.opened_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.opened_right

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.OpenedAgreement.openedSums_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.OpenedAgreement.openedSums_agree
