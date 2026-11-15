import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Simulator

/-!
# The real run of the hybrid ceremony, batch by batch

The real run of the batches is the simulator of the batches with the opened values, for every
observer (GS20, Theorem 2, Hybrids 2 to 5, for each batch).

* `ceremonyHybrid_eq` writes the program of an operator as its batches in sequence. The counters do
  not change a program in the hybrid model.
* `engine_split` cuts the run at the end of the first batch (`executePhase_bind`).
* `engine_alive` is the step for a batch that every honest operator starts. Its inputs are values of
  `H`, so it fixes `H` (`obsEq_hash`), takes the valid inputs (`honestInputs_main`), and then it uses
  the claim of one batch from every cache (`MainRealHybridCore`).
* `engine_dead` is the step after a partial abort. The surviving operators do local work and stop at
  their first call (`executePhase_partial`).
* `lazyBatches_eager` moves the computation of the outputs of all jobs to the start, as `F_ceremony`
  computes them. An output of a batch that does not run has no use (`obsEq_drop`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-! ## The program of an operator -/

section Program

variable (K : Constants C E) (circuits : Circuits) (mode : ReshareMode)

/-- One batch of the hybrid ceremony at operator `i`, the input wires and then the batch. -/
def hybridBatch (i : C.Party) (keys : Keys C) (batch : List Job) : PartyM C E (MainSpec C) (List (List Bit)) :=
  oracleStep (batchInputQuery i keys batch) >>= fun inputs =>
    mainProtocol K mode (batch.map (circuits keys.parameter ·.kind)) i inputs

/-- The batches of the hybrid ceremony at operator `i`. -/
def hybridBatches (i : C.Party) (keys : Keys C) : List (List Job) → PartyM C E (MainSpec C) (List (List Bit))
  | [] => pure []
  | batch :: rest => do
      let out ← hybridBatch K circuits mode i keys batch
      let outs ← hybridBatches i keys rest
      pure (out ++ outs)

/-- The program of each operator for the batches `bs`. `pre` holds the outputs so far of each operator
that still runs. An operator that aborted does not start. -/
def restProgram (x : C.Party → Keys C) (bs : List (List Job)) (pre : C.Party → Option (List (List Bit))) :
    C.Party → PartyM C E (MainSpec C) (List (List Bit)) := fun i =>
  (pre i).elim failure fun o => (o ++ ·) <$> hybridBatches K circuits mode i (x i) bs

private theorem foldlM_tailBody_run (cs : List Circuit) (i : C.Party) :
    ∀ (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st st₀ : RunState C),
      (ls.foldlM (layerBody K (hybridRunBuildingBlocks K mode i) cs) p >>=
          tailBody K (hybridRunBuildingBlocks K mode i) cs).run st =
        (fun o => (o, st)) <$> progAt K mode cs i ls p st₀
  | [], p, st, st₀ => by
    rw [List.foldlM_nil, pure_bind, tailBody_apply, hybrid_rerand, progAt_nil]
    simp only [bind_assoc, StateT.run_bind, StateT.run_lift, map_bind]
    refine bind_congr fun r => ?_
    rcases r with _ | ((z | v') | u) <;> simp [StateT.run_lift, StateT.run_pure, hybrid_verify, hybrid_output]
    refine bind_congr fun r' => ?_
    rcases r' with _ | ((w | w) | ⟨⟩) <;> simp [StateT.run_lift, StateT.run_pure, Functor.map_map]
  | l :: ls, p, st, st₀ => by
    rw [List.foldlM_cons, bind_assoc, layerBody_apply, hybrid_mult, progAt_cons]
    simp only [bind_assoc, StateT.run_bind, StateT.run_lift, map_bind]
    refine bind_congr fun r => ?_
    rcases r with _ | ((z | z) | u) <;> simp [StateT.run_lift, StateT.run_pure]
    rw [← StateT.run_bind]
    exact foldlM_tailBody_run cs i ls _ st st₀

/-- A run of the hybrid building blocks does not change the state of the run, and it does not read
the label or the tag. -/
theorem runJobs_hybrid_run (i : C.Party) (cs : List Circuit) (inputs : List (C.Term → List Bit))
    (st : RunState C) :
    (runJobs K (hybridRunBuildingBlocks K mode i) cs inputs).run st =
      (fun o => (o, st)) <$> mainProtocol K mode cs i inputs := by
  rw [runJobs_eq, foldlM_tailBody_run K mode cs i _ _ st startRun, mainProtocol_eq]

private theorem mapM_run_of {σ β : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (body : List Job → StateT σ M (Option β)) (f : List Job → M β) (next : σ → σ)
    (h : ∀ b s, (body b).run s = (fun o => (some o, next s)) <$> f b) :
    ∀ (L : List (List Job)) (s : σ),
      (L.mapM body).run s = (fun os => (os.map some, next^[L.length] s)) <$> L.mapM f
  | [], s => by simp
  | b :: L, s => by
    simp [List.mapM_cons, StateT.run_bind, h, mapM_run_of body f next h L, Function.iterate_succ_apply]

private theorem hybridBatches_eq (i : C.Party) (keys : Keys C) :
    ∀ L : List (List Job),
      hybridBatches K circuits mode i keys L = List.flatten <$> L.mapM (hybridBatch K circuits mode i keys)
  | [] => by simp [hybridBatches]
  | b :: L => by
    simp [hybridBatches, List.mapM_cons, hybridBatches_eq i keys L]

/-- The hybrid ceremony of an operator is its batches in sequence, for every start of the counters. -/
theorem ceremonyHybrid_eq (settings : Settings) (i : C.Party) (keys : Keys C) (counters : ℕ × ℕ)
    (jobs : List Job) :
    ceremonyHybrid K circuits settings i keys counters jobs =
      hybridBatches K circuits settings.mode i keys (chunks settings.batchSize jobs) := by
  unfold ceremonyHybrid batched
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind]
  rw [mapM_run_of _ (hybridBatch K circuits settings.mode i keys) (fun c => (c.1, c.2 + 1)) ?_, hybridBatches_eq]
  · simp [foldlM_some_append]
  intro b s
  simp [hybridBatch, StateT.run_bind, StateT.run_lift, runJobs_hybrid_run, batchInputQuery, hybridContext]
  rw [show (inputShares (E := E) (G := MainSpec C) _ : Job → _) = fun job => oracleStep (inputQuery _ job) from
    funext (inputShares_eq _), mapM_oracleStep]

/-- `OpenRep` takes one round. -/
theorem timed_openRep (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    Timed 1 (openRep (G := MainSpec C) K ctx v count).run := by
  unfold openRep
  exact Timed.oracleStep_bind 1 _ _ fun digests => Timed.exchange_bind 0 _ _ fun inbox =>
    Timed.oracleStep_bind 0 _ _ fun copyDigests => Timed.require_bind 0 _ _ fun _ => timed_pure _

/-- The rest of a batch before the layers `ls` takes one call for each layer and for `Rerand`, one call
of the check and one round. -/
theorem timed_progAt (jobs : List Circuit) (i : C.Party) :
    ∀ (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C),
      Timed (ls.length + 3) (progAt K mode jobs i ls p st).run
  | [], p, st => by
    rw [progAt_nil]
    refine Timed.call_bind 2 _ _ fun r => ?_
    rcases r with _ | ((z | v') | u)
    · exact timed_failure 2
    · exact timed_failure 2
    · refine Timed.call_bind 1 _ _ fun r' => ?_
      rcases r' with _ | ((w | w) | ⟨⟩)
      · exact timed_failure 1
      · exact timed_failure 1
      · exact timed_failure 1
      · exact (timed_openRep K _ _ _).map _
    · exact timed_failure 2
  | l :: ls, p, st => by
    rw [progAt_cons, show (l :: ls).length + 3 = (ls.length + 3) + 1 by simp only [List.length_cons]]
    refine Timed.call_bind (ls.length + 3) _ _ fun r => ?_
    rcases r with _ | ((z | z) | u)
    · exact timed_failure _
    · exact timed_progAt jobs i ls _ st
    · exact timed_failure _
    · exact timed_failure _

/-- A batch takes one call for each AND layer and for `Rerand`, one call of the check and one round. -/
theorem timed_mainProtocol (jobs : List Circuit) (i : C.Party) (inputs : List (C.Term → List Bit)) :
    Timed (mainRounds jobs) (mainProtocol K mode jobs i inputs).run := by
  have h := timed_progAt K mode jobs i (List.range (depth jobs)) (inputs, []) startRun
  rw [List.length_range] at h
  rw [mainProtocol_eq]
  exact h

/-- A batch with its input wires takes the steps of the batch. -/
theorem timed_hybridBatch (i : C.Party) (keys : Keys C) (batch : List Job) :
    Timed (mainRounds (batch.map (circuits keys.parameter ·.kind)))
      (hybridBatch K circuits mode i keys batch).run :=
  Timed.oracleStep_bind _ _ _ fun inputs => timed_mainProtocol K mode _ i inputs

/-- An operator that runs starts a batch with the batch and then the next batches. -/
theorem restProgram_cons (x : C.Party → Keys C) (batch : List Job) (rest : List (List Job))
    (pre : C.Party → Option (List (List Bit))) (i : C.Party) (h : (pre i).isSome) :
    restProgram K circuits mode x (batch :: rest) pre i =
      hybridBatch K circuits mode i (x i) batch >>= fun out =>
        restProgram K circuits mode x rest (fun j => (pre j).map (· ++ out)) i := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  simp only [restProgram, ho, Option.elim, Option.map_some, hybridBatches, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_def, List.append_assoc]

/-- The programs of the next batches after a batch with the outputs `out`. -/
theorem restProgram_elim (x : C.Party → Keys C) (rest : List (List Job))
    (pre out : C.Party → Option (List (List Bit))) (i : C.Party) :
    ((out i).elim failure fun o => restProgram K circuits mode x rest (fun j => (pre j).map (· ++ o)) i) =
      restProgram K circuits mode x rest (fun j => (pre j).bind fun o₀ => (out j).map (o₀ ++ ·)) i := by
  unfold restProgram
  dsimp only
  cases out i <;> cases pre i <;> rfl

/-- The first step of an operator in a batch is a call, and it aborts when the functionality gives no
output. An operator that aborted is done. -/
theorem restProgram_call (x : C.Party → Keys C) (batch : List Job) (rest : List (List Job))
    (pre : C.Party → Option (List (List Bit))) (i : C.Party) :
    ∀ step ∈ support (advance (restProgram K circuits mode x (batch :: rest) pre i).run),
      step = .done none ∨
        ∃ input resume, step = .call input resume ∧ advance (resume none) = pure (.done none) := by
  intro step hs
  unfold restProgram at hs
  cases hpre : pre i with
  | none =>
    rw [hpre] at hs
    simp only [Option.elim] at hs
    rw [advance_run_failure, support_pure, Set.mem_singleton_iff] at hs
    exact Or.inl hs
  | some o =>
    rw [hpre] at hs
    simp only [Option.elim] at hs
    have hprog : ((o ++ ·) <$> hybridBatches K circuits mode i (x i) (batch :: rest)) =
        oracleStep (batchInputQuery i (x i) batch) >>= fun w =>
          mainProtocol K mode (batch.map (circuits (x i).parameter ·.kind)) i w >>= fun out =>
            (fun outs => o ++ (out ++ outs)) <$> hybridBatches K circuits mode i (x i) rest := by
      simp only [hybridBatches, hybridBatch, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    rw [hprog, advance_oracleStep_bind, mem_support_bind_iff] at hs
    obtain ⟨w, -, hs⟩ := hs
    rw [advance_bind, mainProtocol_eq, advance_progAt, pure_bind] at hs
    obtain ⟨input, resume, hcall, hnone⟩ := stages_callStep_none K mode
      (batch.map (circuits (x i).parameter ·.kind)) i
      (List.range (depth (batch.map (circuits (x i).parameter ·.kind)))) (w, [])
    rw [hcall] at hs
    simp only [continueStep, support_pure, Set.mem_singleton_iff] at hs
    refine Or.inr ⟨input, _, hs, ?_⟩
    rw [advance_bind]
    change advance (resume none) >>= _ = _
    rw [hnone, pure_bind]
    rfl

end Program

/-! ## The run of the batches -/

section Engine

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (mode : ReshareMode)
  (D : C.Coalition) (A : MainAdversary C E)
  {x : C.Party → Keys C} {parameter : PublicParameter} {seeds : C.Term → HashOutput}
  {pairKeys : C.Pair → HashOutput}

/-- With no batch to run, each honest operator that still runs gives its outputs so far. -/
theorem executePhase_rest_nil (x : C.Party → Keys C) (pre : C.Party → Option (List (List Bit)))
    (st : A.State) (fuel : ℕ) :
    executePhase localRoles D A (mainFunctionalities K mode) fuel st (restProgram K circuits mode x [] pre) =
      pure (st, fun i => if i ∈ D.1 then none else pre i) := by
  have hs : (fun i => if i ∈ D.1 then (pure (Step.done none) : OracleComp (LocalSpec C) _) else
      localRoles.honest (advance (restProgram K circuits mode x [] pre i).run)) =
      fun i => pure (if i ∈ D.1 then Step.done none else Step.done (pre i)) := by
    funext i
    split_ifs
    · rfl
    · cases h : pre i <;> simp [restProgram, h, hybridBatches, localRoles] <;> rfl
  rw [executePhase, startSteps, hs, sequenceFin_pure, pure_bind, stages_executeRounds_allDone]
  · congr 2
    funext i
    split_ifs <;> rfl
  · intro i
    split_ifs <;> simp [Step.isDone]

/-- The run of the batches, cut at the end of the first batch. Every honest operator starts the
batch. The run is the input wires, the batch on them, and then the next batches at each operator
with an output. -/
theorem engine_split (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) (batch : List Job)
    (rest : List (List Job)) (pre : C.Party → Option (List (List Bit))) (st : A.State) (b : ℕ)
    (halive : ∀ i, i ∉ D.1 → (pre i).isSome) :
    SameRun prims
      (executePhase localRoles D A (mainFunctionalities K mode)
        (mainRounds (batch.map (circuits parameter ·.kind)) + b) st
        (restProgram K circuits mode x (batch :: rest) pre))
      (liftComp (honestInputQuery D x batch) (LocalSpec C) >>= fun w =>
        executePhase localRoles D A (mainFunctionalities K mode)
          (mainRounds (batch.map (circuits parameter ·.kind))) st
          (fun i => mainProtocol K mode (batch.map (circuits parameter ·.kind)) i (w i)) >>= fun r =>
        executePhase localRoles D A (mainFunctionalities K mode) b r.1
          (restProgram K circuits mode x rest (fun j => (pre j).bind fun o₀ => (r.2 j).map (o₀ ++ ·)))) := by
  have hparam : ∀ i, (x i).parameter = parameter := fun i => by rw [hx i]; rfl
  have h1 := executePhase_congr D A (mainFunctionalities K mode)
    (mainRounds (batch.map (circuits parameter ·.kind)) + b) st
    (restProgram K circuits mode x (batch :: rest) pre)
    (fun i => hybridBatch K circuits mode i (x i) batch >>= fun out =>
      restProgram K circuits mode x rest (fun j => (pre j).map (· ++ out)) i)
    fun i hi => restProgram_cons K circuits mode x batch rest pre i (halive i hi)
  have htimed : ∀ i, i ∉ D.1 → Timed (mainRounds (batch.map (circuits parameter ·.kind)))
      (hybridBatch K circuits mode i (x i) batch).run := fun i _ => by
    have h := timed_hybridBatch K circuits mode i (x i) batch
    rwa [hparam i] at h
  have hb : (fun i => hybridBatch K circuits mode i (x i) batch) = fun i =>
      oracleStep (batchInputQuery i (x i) batch) >>= fun w =>
        mainProtocol K mode (batch.map (circuits parameter ·.kind)) i w := by
    funext i
    simp only [hybridBatch, hparam i]
  rw [h1]
  refine (executePhase_bind prims D A _ _ b st _ _ htimed).trans ?_
  simp only [restProgram_elim]
  rw [hb]
  unfold honestInputQuery
  have h3 := executePhase_oracleStep_bind prims D A (mainFunctionalities K mode) ([] : MainInput C)
    (mainRounds (batch.map (circuits parameter ·.kind))) st (fun i => batchInputQuery i (x i) batch)
    (fun i w => mainProtocol K mode (batch.map (circuits parameter ·.kind)) i w)
  have h4 := h3.bind fun r => SameRun.refl prims
    (executePhase localRoles D A (mainFunctionalities K mode) b r.1
      (restProgram K circuits mode x rest fun j => (pre j).bind fun o₀ => (r.2 j).map (o₀ ++ ·)))
  simpa only [bind_assoc] using h4

/-- The step for a batch that every honest operator starts, with `H` fixed to `h` (GS20, Theorem 2,
for one batch from every cache). The inputs of the batch are then fixed values, so `honestInputs_main`
gives valid inputs and `honestInputs_leak` gives the leak of `F_main`. `hrest` is the claim for the
next batches. -/
theorem engine_alive_fixed (hcore : MainRealHybridCore prims K)
    (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (batch : List Job) (rest : List (List Job)) (pre : C.Party → Option (List (List Bit))) (st : A.State)
    (b : ℕ)
    (hrest : ∀ (pre' : C.Party → Option (List (List Bit))) (st' : A.State),
      ObsEq prims
        (executePhase localRoles D A (mainFunctionalities K mode) b st' (restProgram K circuits mode x rest pre'))
        (lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds rest pre' st'))
    (h : Query C → HashOutput) :
    ObsEq prims
      (executePhase localRoles D A (mainFunctionalities K mode)
          (mainRounds (batch.map (circuits parameter ·.kind))) st
          (fun i => mainProtocol K mode (batch.map (circuits parameter ·.kind)) i
            (ThresholdLeanXmssSecurity.D prims h (honestInputQuery D x batch) i)) >>= fun r =>
        executePhase localRoles D A (mainFunctionalities K mode) b r.1
          (restProgram K circuits mode x rest (fun j => (pre j).bind fun o₀ => (r.2 j).map (o₀ ++ ·))))
      (mainSimAnswerX K D A mode (batch.map (circuits parameter ·.kind)) st
          (knownViews D (ThresholdLeanXmssSecurity.D prims h
              (batch.mapM (knownInputQuery D (knownSeed (corruptInputs D x))))),
            ThresholdLeanXmssSecurity.D prims h (batch.mapM (evalJob circuits parameter seeds))) >>= fun r =>
        lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds rest
          (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1) := by
  obtain ⟨w', hmain, hw⟩ := honestInputs_main prims circuits D hx h batch
  have hprog := executePhase_congr D A (mainFunctionalities K mode)
    (mainRounds (batch.map (circuits parameter ·.kind))) st
    (fun i => mainProtocol K mode (batch.map (circuits parameter ·.kind)) i
      (ThresholdLeanXmssSecurity.D prims h (honestInputQuery D x batch) i))
    (fun i => mainProtocol K mode (batch.map (circuits parameter ·.kind)) i (w' i))
    fun i hi => by rw [hw i hi]
  have hleak : mainIdealLeak D (batch.map (circuits parameter ·.kind)) w' =
      (knownViews D (ThresholdLeanXmssSecurity.D prims h
          (batch.mapM (knownInputQuery D (knownSeed (corruptInputs D x))))),
        ThresholdLeanXmssSecurity.D prims h (batch.mapM (evalJob circuits parameter seeds))) := by
    rw [← honestInputs_leak prims circuits D hx h batch]
    exact mainIdealLeak_congr D _ _ _ hw
  rw [hprog]
  refine ((hcore mode _ D A w' hmain st).bind fun r => SameRun.refl prims _).obsEq.trans ?_
  rw [bind_map_left, hleak]
  refine ObsEq.bind_right _ fun r => (hrest _ _).trans (ObsEq.of_eq ?_)
  refine lazyBatches_congr K circuits mode D A parameter _ seeds rest _ _ _ fun i hi => ?_
  simp only [nextOutputs, mainHybridOut, hi, not_false_eq_true, ↓reduceIte, Option.map_map]
  rfl

/-- The step for a batch that every honest operator starts (GS20, Theorem 2, for one batch from every
cache). The inputs of the batch are values of `H`, so the proof fixes `H` (`obsEq_hash`). `hrest` is
the claim for the next batches. -/
theorem engine_alive (hcore : MainRealHybridCore prims K) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i)
    (batch : List Job) (rest : List (List Job)) (pre : C.Party → Option (List (List Bit))) (st : A.State)
    (b : ℕ) (halive : ∀ i, i ∉ D.1 → (pre i).isSome)
    (hrest : ∀ (pre' : C.Party → Option (List (List Bit))) (st' : A.State),
      ObsEq prims
        (executePhase localRoles D A (mainFunctionalities K mode) b st' (restProgram K circuits mode x rest pre'))
        (lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds rest pre' st')) :
    ObsEq prims
      (executePhase localRoles D A (mainFunctionalities K mode)
        (mainRounds (batch.map (circuits parameter ·.kind)) + b) st
        (restProgram K circuits mode x (batch :: rest) pre))
      (lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds (batch :: rest) pre st) := by
  refine (engine_split prims K circuits mode D A hx batch rest pre st b halive).obsEq.trans ?_
  rw [lazyBatches, ite_eq_left_of_eq_true _ _ (eq_true halive)]
  have hv : (liftComp (batch.mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun outs =>
      liftComp (batch.mapM (knownInputQuery D (knownSeed (corruptInputs D x)))) (LocalSpec C) >>= fun known =>
      mainSimAnswerX K D A mode (batch.map (circuits parameter ·.kind)) st (knownViews D known, outs) >>= fun r =>
      lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds rest
        (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1) =
      liftComp (batch.mapM (evalJob circuits parameter seeds) >>= fun outs =>
        batch.mapM (knownInputQuery D (knownSeed (corruptInputs D x))) >>= fun known =>
          pure (outs, known)) (LocalSpec C) >>= fun p =>
      mainSimAnswerX K D A mode (batch.map (circuits parameter ·.kind)) st (knownViews D p.2, p.1) >>= fun r =>
      lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds rest
        (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1 := by
    simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  rw [hv]
  refine obsEq_hash prims _ _ _ _ fun h _ => ?_
  simp only [D_bind, D_pure]
  exact engine_alive_fixed prims K circuits mode D A hcore hx batch rest pre st b hrest h

/-- The step after a partial abort. An honest operator does not start the batch. The others do local
work and stop at their first call, so no operator gets an output and the adversary gets no step. -/
theorem engine_dead (x : C.Party → Keys C) (batch : List Job) (rest : List (List Job))
    (pre : C.Party → Option (List (List Bit))) (st : A.State) (fuel : ℕ)
    (hdead : ¬ ∀ i, i ∉ D.1 → (pre i).isSome) :
    ObsEq prims
      (executePhase localRoles D A (mainFunctionalities K mode) fuel st
        (restProgram K circuits mode x (batch :: rest) pre))
      (pure (st, fun _ => none)) := by
  have hex : ∃ i, i ∉ D.1 ∧ restProgram K circuits mode x (batch :: rest) pre i = failure := by
    push Not at hdead
    obtain ⟨i, hi, hpre⟩ := hdead
    refine ⟨i, hi, ?_⟩
    have hnone : pre i = none := by simpa using hpre
    simp only [restProgram, hnone, Option.elim]
  have h := executePhase_partial prims D A (mainFunctionalities K mode) fuel st _ hex
    fun i _ => restProgram_call K circuits mode x batch rest pre i
  exact h.obsEq.trans (obsEq_drop prims _ _)

/-- The real run of the batches is the simulator of the batches with the opened values, for every
observer (GS20, Theorem 2). The fuel is the steps of the batches and any more steps. -/
theorem engine (hcore : MainRealHybridCore prims K) (hx : ∀ i, x i = dealtKeys parameter seeds pairKeys i) :
    ∀ (bs : List (List Job)) (pre : C.Party → Option (List (List Bit))) (st : A.State) (extra : ℕ),
    ObsEq prims
      (executePhase localRoles D A (mainFunctionalities K mode) (hybridRounds circuits parameter bs + extra) st
        (restProgram K circuits mode x bs pre))
      (lazyBatches K circuits mode D A parameter (knownSeed (corruptInputs D x)) seeds bs pre st)
  | [], pre, st, extra => ObsEq.of_eq (executePhase_rest_nil K circuits mode D A x pre st _)
  | batch :: rest, pre, st, extra => by
    by_cases halive : ∀ i, i ∉ D.1 → (pre i).isSome
    · have h := engine_alive prims K circuits mode D A hcore hx batch rest pre st
        (hybridRounds circuits parameter rest + extra) halive
        fun pre' st' => engine hcore hx rest pre' st' extra
      simpa only [hybridRounds, List.map_cons, List.sum_cons, Nat.add_assoc] using h
    · simp only [lazyBatches, halive, ↓reduceIte]
      exact engine_dead prims K circuits mode D A x batch rest pre st _ halive

private theorem length_of_mem_support_mapM {ι α β : Type} {spec : OracleSpec ι}
    (f : α → OracleComp spec β) :
    ∀ (l : List α) (o : List β), o ∈ support (l.mapM f) → o.length = l.length
  | [], o, h => by
    simp at h
    simp [h]
  | a :: l, o, h => by
    simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨b, -, os, hos, rfl⟩ := h
    simp [length_of_mem_support_mapM f l os hos]

/-- The outputs of all jobs first, as `F_ceremony` computes them (BR93, lazy sampling). The simulator
does not read an output of a batch that does not run. -/
theorem lazyBatches_eager (seed seeds : C.Term → HashOutput) (bs : List (List Job))
    (pre : C.Party → Option (List (List Bit))) (st : A.State) :
    ObsEq prims (lazyBatches K circuits mode D A parameter seed seeds bs pre st)
      (liftComp (bs.flatten.mapM (evalJob circuits parameter seeds)) (LocalSpec C) >>= fun outputs =>
        simBatches K circuits mode D A parameter seed bs outputs pre st) := by
  induction bs generalizing pre st with
  | nil => exact ObsEq.of_eq (by simp [lazyBatches, simBatches])
  | cons batch rest ih =>
    by_cases halive : ∀ i, i ∉ D.1 → (pre i).isSome
    · simp only [lazyBatches, simBatches, ite_eq_left_of_eq_true _ _ (eq_true halive), List.flatten_cons,
        List.mapM_append, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
      refine ObsEq.bind_support _ fun o1 ho1 => ?_
      rw [OracleComp.support_liftComp] at ho1
      have hl : o1.length = batch.length := length_of_mem_support_mapM _ _ _ ho1
      simp only [List.take_left' hl, List.drop_left' hl]
      refine (ObsEq.bind_right _ fun known => ObsEq.bind_right _ fun r => ih _ _).trans ?_
      -- The outputs of the next batches move in front of the simulator of this batch.
      have h := (sameRun_swap prims
        ((batch.mapM (knownInputQuery D seed)).liftComp (LocalSpec C) >>= fun known =>
          mainSimAnswerX K D A mode (batch.map (circuits parameter ·.kind)) st (knownViews D known, o1))
        ((rest.flatten.mapM (evalJob circuits parameter seeds)).liftComp (LocalSpec C))
        fun r o2 => simBatches K circuits mode D A parameter seed rest o2
          (nextOutputs (batch.map (circuits parameter ·.kind)) pre r.2) r.1).obsEq
      simpa only [bind_assoc] using h
    · simp only [lazyBatches, simBatches, halive, ↓reduceIte]
      exact (obsEq_drop prims _ _).symm

end Engine

end ThresholdLeanXmssSecurity
