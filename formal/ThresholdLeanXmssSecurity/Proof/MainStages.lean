import ThresholdLeanXmssSecurity.Proof.MainSecurity
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# A batch: the two stages of `MainRealHybrid`

* `mainEngineReal`: `MainEngineReal`. The network runs round by round as `mainRealGame`, with one
  `runFunctionality` lemma for each call shape (`stages_run_mult`, `stages_run_rerand`,
  `stages_run_verify`), the round of `OpenRep` (`stages_stepRound_open`), the partial aborts
  (`stages_executeRounds_abort`) and induction over the layers (`stages_layers`).
* `mainRealSim`: `MainRealSim` (GS20, Theorem 2). `StagesInv` couples the real state and the
  simulator data: the known views agree, the hidden copies agree, the differences are
  `mainDifference` when the copies agree (`stages_diff_correct`), and the accepted wires share the
  plain wires (`stages_layer_correct`). The uniform terms of each layer are unused draws, the leak of
  `F_multVerify` is the simulator leak (`stages_verifyLeak`), and after acceptance the copies of
  `Rerand` are `mainRebuild` of the outputs (`stages_rebuild`).
* `mainStatementFull`: `MainStatement`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-! ## Generic runs -/

/-- An unused private draw changes neither an output nor the cache. -/
theorem stages_private_unused (prims : Primitives) {α β : Type} (p : ProbComp α)
    (k : OracleComp (LocalSpec C) β) :
    SameRun (C := C) prims (liftComp p (LocalSpec C) >>= fun _ => k) k := by
  have h := sameRun_swap prims (liftComp p (LocalSpec C)) k (fun _ b => pure b)
  simp only [bind_pure] at h
  refine h.trans ?_
  conv_rhs => rw [← bind_pure k]
  refine SameRun.bind_right k fun b => ?_
  intro s
  have hl : simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p :=
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, hl,
    unifFwdImpl.simulateQ_run, bind_map_left]
  exact DeferredSampling.evalDist_bind_const_neverFails p (by simp) _

/-! ## The functionalities of a batch -/

section Sum

set_option linter.unusedSectionVars false

variable {I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type} [Inhabited R₁] [Inhabited R₂]

/-- The right handler of `Functionality.sum`. -/
def stagesSumRight : QueryImpl (LocalSpec C + (L₂ →ₒ R₂)) (OracleComp (LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂))) :=
  (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂)) (Sum.inl t))) +
  (fun (l : L₂) => leak (C := C) (R := R₁ ⊕ R₂) (Sum.inr l : L₁ ⊕ L₂) >>= fun r =>
    match r with
    | .inr r => pure r
    | .inl _ => pure default)

theorem stages_sum_run_right (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂)
    (D : C.Coalition) (inputs : C.Party → Option I₂) (hin : ∃ i, (inputs i).isSome) :
    (F₁.sum F₂).run D (fun i => (inputs i).map Sum.inr) =
      (fun out i => (out i).map Sum.inr) <$>
        simulateQ (stagesSumRight (L₁ := L₁) (R₁ := R₁)) (F₂.run D inputs) := by
  obtain ⟨i₀, hi₀⟩ := hin
  unfold Functionality.sum
  dsimp only
  rw [if_neg (fun h => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hi₀
    have := h i₀ (Sum.inr a) (by simp [ha])
    simp at this)]
  rw [if_pos (fun i x hx => by
    obtain ⟨y, -, rfl⟩ := Option.mem_map.1 hx
    rfl)]
  have : (fun i => (Option.map (Sum.inr (α := I₁)) (inputs i)).bind Sum.getRight?) = inputs := by
    funext i
    cases inputs i <;> rfl
  rw [this]
  rfl

theorem stages_sumRight_leak (l : L₂) :
    simulateQ (stagesSumRight (C := C) (L₁ := L₁) (R₁ := R₁)) (leak (C := C) (R := R₂) l) =
      leak (C := C) (R := R₁ ⊕ R₂) (Sum.inr l : L₁ ⊕ L₂) >>= fun r =>
        match r with
        | .inr r => pure r
        | .inl _ => pure default := by
  unfold leak
  rw [simulateQ_query]
  exact id_map _

theorem stages_sumRight_liftComp {α : Type} (p : ProbComp α) :
    simulateQ (stagesSumRight (C := C) (L₁ := L₁) (R₁ := R₁) (L₂ := L₂) (R₂ := R₂))
        (liftComp p (LocalSpec C + (L₂ →ₒ R₂))) = liftComp p _ := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_bind, simulateQ_bind]
    simp only [ih]
    congr 1

end Sum

theorem stages_callImpl_liftComp {E' Ia L R : Type} (A : Adversary C E' Ia L R) {α : Type} (p : ProbComp α)
    (st : A.State) :
    (simulateQ (mainCallImpl A) (liftComp p (LocalSpec C + (L →ₒ R)))).run st =
      liftComp p (LocalSpec C) >>= fun x => pure (x, st) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_bind, simulateQ_bind, StateT.run_bind, bind_assoc]
    have h1 : (simulateQ (mainCallImpl A) ((liftM (OracleSpec.query t) : ProbComp _).liftComp
        (LocalSpec C + (L →ₒ R)))).run st =
        (liftM (OracleSpec.query t) : ProbComp _).liftComp (LocalSpec C) >>= fun u => pure (u, st) := by
      simp [mainCallImpl, localRoles]
      rfl
    rw [h1]
    simp [ih]

/-- The reply of the adversary to a call of `F_mult` for the AND gates. -/
def stagesReplyL (b : MainHybridReply C) : MainMultReply C :=
  match b with | .inl (.inl r) => r | _ => default

/-- The reply of the adversary to a call of `F_mult` for `Rerand`. -/
def stagesReplyR (b : MainHybridReply C) : MainMultReply C :=
  match b with | .inl (.inr r) => r | _ => default

/-- The reply of the adversary to a call of `F_multVerify`. -/
def stagesReplyV (b : MainHybridReply C) : Finset C.Party :=
  match b with | .inr rs => rs | _ => ∅

theorem stages_run_mult (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (mode : ReshareMode)
    (st : A.State) (n : ℕ) (X Y : C.Party → Shares C Bit) :
    runFunctionality localRoles D A (mainFunctionalities K mode) st
      (fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inl (X i, Y i, n)))) =
    A.answer st (.inl (.inl (mainMultLeak D n X Y))) >>= fun a =>
      liftComp ($ᵗ (C.Term → Fin n → Bit)) (LocalSpec C) >>= fun fresh =>
      pure (a.1, fun i => (mainMultOutputs K D mode n X Y (stagesReplyL a.2) fresh i).map
        fun z => Sum.inl (Sum.inl z)) := by
  unfold runFunctionality
  rw [if_neg (by simp)]
  simp only [pure_bind]
  have h1 : (fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inl (X i, Y i, n)))) =
      fun i => (((if i ∈ D.1 then none else some (X i, Y i, n)) : Option _).map
        (Sum.inl (β := Shares C Bit × Shares C Bit × ℕ))).map (Sum.inl (β := List (Tuple C))) := by
    funext i
    split_ifs <;> rfl
  rw [h1, mainFunctionalities, main_sum_run_left, main_sum_run_left, main_fmultBit_run]
  have h2 : ((fun (out : C.Party → Option (Shares C Bit ⊕ Shares C Bit)) i =>
      Option.map (Sum.inl (β := Unit)) (out i)) <$> simulateQ mainSumLeft
      ((fun (out : C.Party → Option (Shares C Bit)) i => Option.map (Sum.inl (β := Shares C Bit)) (out i)) <$>
        simulateQ mainSumLeft (do
        let r ← leak (mainMultLeak D n X Y)
        let fresh ← sample (C.Term → Fin n → Bit)
        pure (mainMultOutputs K D mode n X Y r fresh))) :
        OracleComp (LocalSpec C + (MainHybridLeak C →ₒ MainHybridReply C)) _) =
      leak (C := C) (R := MainHybridReply C) (.inl (.inl (mainMultLeak D n X Y))) >>= fun b =>
        liftComp ($ᵗ (C.Term → Fin n → Bit)) _ >>= fun fresh =>
          pure fun i => (mainMultOutputs K D mode n X Y (stagesReplyL b) fresh i).map
            fun z => Sum.inl (Sum.inl z) := by
    simp only [simulateQ_map, simulateQ_bind, main_sumLeft_leak, sample, main_sumLeft_liftComp,
      simulateQ_pure, bind_assoc, map_bind]
    refine bind_congr fun b => ?_
    rcases b with (r | r) | r
    all_goals simp [stagesReplyL, Function.comp_def]
    split
    · rename_i r' h
      simp [default] at h
    · simp
  rw [h2]
  change (simulateQ (mainCallImpl A) _).run st >>= _ = _
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, bind_assoc, main_callImpl_leak, pure_bind,
    stages_callImpl_liftComp, StateT.run_pure]

theorem stages_run_rerand (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (mode : ReshareMode)
    (st : A.State) (n : ℕ) (X Y : C.Party → Shares C Bit) :
    runFunctionality localRoles D A (mainFunctionalities K mode) st
      (fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inr (X i, Y i, n)))) =
    A.answer st (.inl (.inr (mainMultLeak D n X Y))) >>= fun a =>
      liftComp ($ᵗ (C.Term → Fin n → Bit)) (LocalSpec C) >>= fun fresh =>
      pure (a.1, fun i => (mainMultOutputs K D .peer n X Y (stagesReplyR a.2) fresh i).map
        fun z => Sum.inl (Sum.inr z)) := by
  unfold runFunctionality
  rw [if_neg (by simp)]
  simp only [pure_bind]
  have h1 : (fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inr (X i, Y i, n)))) =
      fun i => (((if i ∈ D.1 then none else some (X i, Y i, n)) : Option _).map
        (Sum.inr (α := Shares C Bit × Shares C Bit × ℕ))).map (Sum.inl (β := List (Tuple C))) := by
    funext i
    split_ifs <;> rfl
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  rw [h1, mainFunctionalities, main_sum_run_left, stages_sum_run_right _ _ _ _ ⟨i₀, by simp [hi₀]⟩,
    main_fmultBit_run]
  have h2 : ((fun (out : C.Party → Option (Shares C Bit ⊕ Shares C Bit)) i =>
      Option.map (Sum.inl (β := Unit)) (out i)) <$> simulateQ mainSumLeft
      ((fun (out : C.Party → Option (Shares C Bit)) i => Option.map (Sum.inr (α := Shares C Bit)) (out i)) <$>
        simulateQ stagesSumRight (do
        let r ← leak (mainMultLeak D n X Y)
        let fresh ← sample (C.Term → Fin n → Bit)
        pure (mainMultOutputs K D .peer n X Y r fresh))) :
        OracleComp (LocalSpec C + (MainHybridLeak C →ₒ MainHybridReply C)) _) =
      leak (C := C) (R := MainHybridReply C) (.inl (.inr (mainMultLeak D n X Y))) >>= fun b =>
        liftComp ($ᵗ (C.Term → Fin n → Bit)) _ >>= fun fresh =>
          pure fun i => (mainMultOutputs K D .peer n X Y (stagesReplyR b) fresh i).map
            fun z => Sum.inl (Sum.inr z) := by
    simp only [simulateQ_map, simulateQ_bind, stages_sumRight_leak, main_sumLeft_leak, sample,
      stages_sumRight_liftComp, main_sumLeft_liftComp, simulateQ_pure, bind_assoc, map_bind]
    refine bind_congr fun b => ?_
    rcases b with (r | r) | r
    all_goals simp [stagesReplyR, Function.comp_def]
    split
    · rename_i r' h
      simp [default] at h
      cases h
      simp
      rfl
    · simp
  rw [h2]
  change (simulateQ (mainCallImpl A) _).run st >>= _ = _
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, bind_assoc, main_callImpl_leak, pure_bind,
    stages_callImpl_liftComp, StateT.run_pure]

theorem stages_fmultVerify_run (D : C.Coalition) (inputs : C.Party → Option (List (Tuple C))) :
    (FmultVerify (C := C)).run D inputs =
      leak (mainVerifyLeak D inputs) >>= fun receivers =>
        pure fun i => if i ∉ D.1 ∧ (mainVerifyLeak D inputs).2.2 = true ∧ i ∈ receivers then some () else none :=
  rfl

theorem stages_run_verify (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (mode : ReshareMode)
    (st : A.State) (views : C.Party → List (Tuple C)) :
    runFunctionality localRoles D A (mainFunctionalities K mode) st
      (fun i => if i ∈ D.1 then none else some (Sum.inr (views i))) =
    A.answer st (.inr (mainVerifyLeak D fun i => if i ∈ D.1 then none else some (views i))) >>= fun b =>
      pure (b.1, fun i => if i ∉ D.1 ∧
        (mainVerifyLeak D fun i => if i ∈ D.1 then none else some (views i)).2.2 = true ∧
          i ∈ stagesReplyV b.2 then some (Sum.inr ()) else none) := by
  unfold runFunctionality
  rw [if_neg (by simp)]
  simp only [pure_bind]
  have h1 : (fun i => if i ∈ D.1 then none else some (Sum.inr (views i))) =
      fun i => (((if i ∈ D.1 then none else some (views i)) : Option _).map
        (Sum.inr (α := (Shares C Bit × Shares C Bit × ℕ) ⊕ (Shares C Bit × Shares C Bit × ℕ)))) := by
    funext i
    split_ifs <;> rfl
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  rw [h1, mainFunctionalities, stages_sum_run_right _ _ _ _ ⟨i₀, by simp [hi₀]⟩, stages_fmultVerify_run]
  set L := mainVerifyLeak D fun i => if i ∈ D.1 then none else some (views i) with hL
  have h2 : ((fun (out : C.Party → Option Unit) i =>
      Option.map (Sum.inr (α := Shares C Bit ⊕ Shares C Bit)) (out i)) <$>
      simulateQ stagesSumRight (leak (C := C) (R := Finset C.Party) L >>= fun receivers =>
        pure fun i => if i ∉ D.1 ∧ L.2.2 = true ∧ i ∈ receivers then some () else none) :
        OracleComp (LocalSpec C + (MainHybridLeak C →ₒ MainHybridReply C)) _) =
      leak (C := C) (R := MainHybridReply C) (.inr L) >>= fun b =>
        pure fun i => if i ∉ D.1 ∧ L.2.2 = true ∧ i ∈ stagesReplyV b then some (Sum.inr ()) else none := by
    simp only [simulateQ_bind, stages_sumRight_leak, simulateQ_pure, bind_assoc, map_bind]
    refine bind_congr fun b => ?_
    rcases b with (r | r) | r
    all_goals simp [stagesReplyV]
    all_goals first
      | rfl
      | (funext i; simp [show (default : Finset C.Party) = ∅ from rfl])
  rw [h2]
  change (simulateQ (mainCallImpl A) _).run st >>= _ = _
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, bind_assoc, main_callImpl_leak, pure_bind,
    StateT.run_pure]

/-! ## Aborts in the network -/

theorem stages_sequenceFin_eq_pure {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type} {n : ℕ}
    (f : Fin n → m β) (g : Fin n → β) (h : ∀ i, f i = pure (g i)) : Concrete.sequenceFin f = pure g := by
  rw [show f = fun i => pure (g i) from funext h]
  exact sequenceFin_pure g

section Abort

variable {E' Ia I O L R α : Type} (D : C.Coalition) (A : Adversary C E' Ia L R) (F : Functionality C I O L R)

theorem stages_executeRounds_done (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E' (CallSpec I O) α)
    (h : ∀ i, steps i = .done none) :
    executeRounds localRoles D A F fuel st steps = pure (st, fun _ => none) := by
  cases fuel with
  | zero => simp [executeRounds, h, Step.output]
  | succ fuel =>
    rw [executeRounds, if_pos (fun i _ => by simp [h, Step.isDone])]
    simp [h, Step.output]

theorem stages_executeRounds_allDone (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E' (CallSpec I O) α)
    (h : ∀ i, (steps i).isDone) :
    executeRounds localRoles D A F fuel st steps = pure (st, fun i => (steps i).output) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [executeRounds, if_pos (fun i _ => h i)]

/-- A partial abort: some honest operator aborted, and the others call. Then everyone aborts. -/
theorem stages_executeRounds_abort (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E' (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none)
    (h : ∀ i ∉ D.1, steps i = .done none ∨
      ∃ input resume, steps i = .call input resume ∧ advance (resume none) = pure (.done none))
    (hab : ∃ i ∉ D.1, steps i = .done none) :
    executeRounds localRoles D A F fuel st steps = pure (st, fun _ => none) := by
  cases fuel with
  | zero =>
    simp only [executeRounds]
    congr 2
    funext i
    by_cases hi : i ∈ D.1
    · simp [hD i hi, Step.output]
    · rcases h i hi with h' | ⟨input, resume, h', -⟩ <;> simp [h', Step.output]
  | succ fuel =>
    rw [executeRounds]
    split_ifs with hdone
    · congr 2
      funext i
      by_cases hi : i ∈ D.1
      · simp [hD i hi, Step.output]
      · rcases h i hi with h' | ⟨input, resume, h', -⟩
        · simp [h', Step.output]
        · have := hdone i hi
          rw [h'] at this
          exact this.elim
    · have hstep : stepRound localRoles D A F st steps = pure (st, fun _ => .done none, fun _ _ => none) := by
        unfold stepRound
        obtain ⟨i₀, hi₀, hdone₀⟩ := hab
        have hcall : ∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome := by
          by_contra hc
          push Not at hc
          apply hdone
          intro i hi
          rcases h i hi with h' | ⟨input, resume, h', -⟩
          · simp [h', Step.isDone]
          · have := hc i hi
            simp [h', Step.callInput] at this
        rw [if_pos ⟨hcall, fun i hi => by
          rcases h i hi with h' | ⟨input, resume, h', -⟩
          · simp [h', Step.isDone]
          · simp [h', Step.callInput]⟩]
        unfold runFunctionality
        rw [if_pos (fun hall => by simpa [hi₀, hdone₀, Step.callInput] using hall i₀ hi₀)]
        simp only [pure_bind]
        rw [stages_sequenceFin_eq_pure _ (fun _ => Step.done none) (fun j => ?_), pure_bind]
        by_cases hj : j ∈ D.1
        · simp [hD j hj]
        · rcases h j hj with h' | ⟨input, resume, h', hres⟩
          · simp [h']
          · simp [h', hj, localRoles, hres]
      rw [hstep, pure_bind]
      exact stages_executeRounds_done D A F fuel st _ fun _ => rfl

end Abort

/-! ## The layers in the network -/

section Network

variable (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (mode : ReshareMode) (jobs : List Circuit)

/-- The steps of the operators before the layers `ls`. -/
def stagesSteps (ls : List ℕ) (p : C.Party → MainInput C × List (Tuple C)) :
    C.Party → Step C E (MainSpec C) (List (List Bit)) :=
  fun i => if i ∈ D.1 then .done none else callStep K mode jobs i ls (p i)

/-- The state after a layer. -/
def stagesNext (l : ℕ) (p : C.Party → MainInput C × List (Tuple C)) (z : C.Party → Shares C Bit) :
    C.Party → MainInput C × List (Tuple C) := fun i =>
  (appendLayer jobs l (p i).1 (z i), (p i).2 ++
    [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1, z i, (gatesAt jobs l).length, mode⟩])

theorem stages_callStep_none (i : C.Party) (ls : List ℕ) (p : MainInput C × List (Tuple C)) :
    ∃ input resume, callStep K mode jobs i ls p = .call input resume ∧ advance (resume none) = pure (.done none) := by
  cases ls <;> exact ⟨_, _, rfl, rfl⟩

theorem stages_stepRound_layer (st : A.State) (l : ℕ) (ls : List ℕ) (p : C.Party → MainInput C × List (Tuple C)) :
    stepRound localRoles D A (mainFunctionalities K mode) st (stagesSteps K D mode jobs (l :: ls) p) =
      A.answer st (.inl (.inl (mainMultLeak D (gatesAt jobs l).length (fun i => layerX K jobs l (p i).1)
        (fun i => layerY K jobs l (p i).1)))) >>= fun a =>
      liftComp ($ᵗ (C.Term → Fin (gatesAt jobs l).length → Bit)) (LocalSpec C) >>= fun fresh =>
      pure (a.1, fun i => if i ∈ D.1 ∨ i ∉ (stagesReplyL a.2).2.2.2 then .done none else
        callStep K mode jobs i ls (stagesNext K mode jobs l p (mainFmultOut K D mode (gatesAt jobs l).length
          (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) (stagesReplyL a.2) fresh) i),
        fun _ _ => none) := by
  unfold stepRound
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  rw [if_pos ⟨⟨i₀, hi₀, by simp [stagesSteps, hi₀, callStep, Step.callInput]⟩, fun i hi => by
    simp [stagesSteps, hi, callStep, Step.callInput]⟩]
  have hin : (fun i => if i ∈ D.1 then none else (stagesSteps K D mode jobs (l :: ls) p i).callInput) =
      fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inl (layerX K jobs l (p i).1,
        layerY K jobs l (p i).1, (gatesAt jobs l).length))) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, stagesSteps, callStep, Step.callInput]
  rw [hin, stages_run_mult]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun fresh => ?_
  rw [stages_sequenceFin_eq_pure _ _ (fun j => ?_), pure_bind]
  by_cases hj : j ∈ D.1
  · simp [stagesSteps, hj]
  · simp only [stagesSteps, if_neg hj, callStep, localRoles, mainMultOutputs]
    by_cases hr : j ∉ (stagesReplyL a.2).2.2.2
    · simp only [hj, hr]
      rfl
    · simp only [hj, hr, or_false, if_false, Option.map_some]
      exact advance_progAt K mode jobs j ls _

/-- The call of `F_multVerify` by operator `i` with its output copies `v`. -/
def stagesVerifyStep (i : C.Party) (p : MainInput C × List (Tuple C)) (v : Shares C Bit) :
    Step C E (MainSpec C) (List (List Bit)) :=
  .call (Sum.inr (p.2 ++ [⟨outputShares K jobs p.1, one K, v, (outputsOf jobs).length, .peer⟩]))
    fun r' => (match r' with
      | some (.inr ()) => (fun opened => assemble jobs opened) <$>
          openRep K (localContext i) v (outputsOf jobs).length
      | _ => failure : PartyM C E (MainSpec C) (List (List Bit))).run

theorem stages_stepRound_rerand (st : A.State) (p : C.Party → MainInput C × List (Tuple C)) :
    stepRound localRoles D A (mainFunctionalities K mode) st (stagesSteps K D mode jobs [] p) =
      A.answer st (.inl (.inr (mainMultLeak D (outputsOf jobs).length (fun i => outputShares K jobs (p i).1)
        (fun _ => one K)))) >>= fun a =>
      liftComp ($ᵗ (C.Term → Fin (outputsOf jobs).length → Bit)) (LocalSpec C) >>= fun fresh =>
      pure (a.1, fun i => if i ∈ D.1 ∨ i ∉ (stagesReplyR a.2).2.2.2 then .done none else
        stagesVerifyStep K jobs i (p i) (mainFmultOut K D .peer (outputsOf jobs).length
          (fun i => outputShares K jobs (p i).1) (fun _ => one K) (stagesReplyR a.2) fresh i),
        fun _ _ => none) := by
  unfold stepRound
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  rw [if_pos ⟨⟨i₀, hi₀, by simp [stagesSteps, hi₀, callStep, Step.callInput]⟩, fun i hi => by
    simp [stagesSteps, hi, callStep, Step.callInput]⟩]
  have hin : (fun i => if i ∈ D.1 then none else (stagesSteps K D mode jobs [] p i).callInput) =
      fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inr (outputShares K jobs (p i).1,
        (fun _ => one K) i, (outputsOf jobs).length))) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, stagesSteps, callStep, Step.callInput]
  rw [hin, stages_run_rerand]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun fresh => ?_
  rw [stages_sequenceFin_eq_pure _ _ (fun j => ?_), pure_bind]
  by_cases hj : j ∈ D.1
  · simp [stagesSteps, hj]
  · simp only [stagesSteps, if_neg hj, callStep, localRoles, mainMultOutputs]
    by_cases hr : j ∉ (stagesReplyR a.2).2.2.2
    · simp only [hj, hr]
      rfl
    · simp only [hj, hr, or_false, if_false, Option.map_some]
      rw [advance_call_bind]
      unfold stagesVerifyStep
      congr 2
      funext r
      rcases r with _ | ((w | w) | u) <;> rfl

/-- The round of `OpenRep` at operator `i`. -/
def stagesOpenStep (i : C.Party) (v : Shares C Bit) (ds : List HashOutput) :
    Step C E (MainSpec C) (List (List Bit)) :=
  .wait (repOutbox K i v (outputsOf jobs).length ds) (exchangeResume fun inbox =>
    (fun opened => assemble jobs opened) <$> repRest (G := MainSpec C) K i v (outputsOf jobs).length inbox)

/-- The tuples of operator `i` at `F_multVerify`. -/
def stagesTuples (p : MainInput C × List (Tuple C)) (v : Shares C Bit) : List (Tuple C) :=
  p.2 ++ [⟨outputShares K jobs p.1, one K, v, (outputsOf jobs).length, .peer⟩]

theorem stages_stepRound_verify (st : A.State) (p : C.Party → MainInput C × List (Tuple C))
    (v : C.Party → Shares C Bit) :
    stepRound localRoles D A (mainFunctionalities K mode) st
        (fun i => if i ∈ D.1 then .done none else stagesVerifyStep K jobs i (p i) (v i)) =
      A.answer st (.inr (mainVerifyLeak D fun i => if i ∈ D.1 then none else
        some (stagesTuples K jobs (p i) (v i)))) >>= fun b =>
      Concrete.sequenceFin (fun j => if j ∉ D.1 ∧ (mainVerifyLeak D fun i => if i ∈ D.1 then none else
          some (stagesTuples K jobs (p i) (v i))).2.2 = true ∧ j ∈ stagesReplyV b.2 then
        mainCopyHashes (v j) (outputsOf jobs).length >>= fun ds => pure (stagesOpenStep K jobs j (v j) ds)
        else pure (.done none)) >>= fun steps' => pure (b.1, steps', fun _ _ => none) := by
  unfold stepRound
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  rw [if_pos ⟨⟨i₀, hi₀, by simp [hi₀, stagesVerifyStep, Step.callInput]⟩, fun i hi => by
    simp [hi, stagesVerifyStep, Step.callInput]⟩]
  have hin : (fun i => if i ∈ D.1 then none else
      ((if i ∈ D.1 then .done none else stagesVerifyStep K jobs i (p i) (v i) :
        Step C E (MainSpec C) (List (List Bit)))).callInput) =
      fun i => if i ∈ D.1 then none else some (Sum.inr (stagesTuples K jobs (p i) (v i))) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, stagesVerifyStep, Step.callInput, stagesTuples]
  rw [hin, stages_run_verify]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  congr 1
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp [hj]
  · simp only [hj, if_false, stagesVerifyStep, localRoles, not_false_eq_true, true_and]
    split_ifs with hr
    · show advance ((fun opened => assemble jobs opened) <$>
        openRep (G := MainSpec C) K (localContext j) (v j) (outputsOf jobs).length).run = _
      rw [advance_openRep, liftComp_mapM_local]
      rfl
    · rfl

theorem stages_stepRound_open (st : A.State) (R : Finset C.Party) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) :
    stepRound localRoles D A (mainFunctionalities K mode) st
        (fun j => if j ∉ D.1 ∧ j ∈ R then stagesOpenStep K jobs j (v j) (ds j) else .done none) =
      A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ R then
        repOutbox K i (v i) (outputsOf jobs).length (ds i) c else none) >>= fun q =>
      Concrete.sequenceFin (fun j => (fun o => (Step.done (o.map (assemble jobs)) :
          Step C E (MainSpec C) (List (List Bit)))) <$>
        mainOpenOne K D R (outputsOf jobs).length v ds q.2 j) >>= fun steps' =>
      pure (q.1, steps', q.2) := by
  unfold stepRound
  rw [if_neg (fun h => by
    obtain ⟨⟨i, -, hi⟩, -⟩ := h
    dsimp only at hi
    split_ifs at hi <;> simp [stagesOpenStep, Step.callInput] at hi)]
  have hout : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      ((if i ∉ D.1 ∧ i ∈ R then stagesOpenStep K jobs i (v i) (ds i) else .done none :
        Step C E (MainSpec C) (List (List Bit)))).outbox c else none) =
      fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ R then repOutbox K i (v i) (outputsOf jobs).length (ds i) c
        else none := by
    funext c i
    by_cases hc : c ∈ D.1 <;> by_cases hi : i ∈ D.1 <;> by_cases hR : i ∈ R <;>
      simp [hc, hi, hR, stagesOpenStep, Step.outbox]
  rw [hout]
  simp only [localRoles]
  refine bind_congr fun q => ?_
  congr 1
  congr 1
  funext j
  by_cases hj : j ∉ D.1 ∧ j ∈ R
  · rw [if_pos hj]
    simp only [stagesOpenStep, if_neg hj.1]
    have hinbox : (fun k => if k ∈ D.1 then q.2 k j else
        ((if k ∉ D.1 ∧ k ∈ R then Step.wait (repOutbox K k (v k) (outputsOf jobs).length (ds k))
          (exchangeResume fun inbox => (fun opened => assemble jobs opened) <$>
            repRest (G := MainSpec C) K k (v k) (outputsOf jobs).length inbox)
          else Step.done none : Step C E (MainSpec C) (List (List Bit)))).delivered j) =
        mainOpenInbox K D R (outputsOf jobs).length v ds q.2 j := by
      funext k
      unfold mainOpenInbox
      by_cases hk : k ∈ D.1 <;> by_cases hkR : k ∈ R <;> simp [hk, hkR]
    rw [hinbox]
    unfold exchangeResume mainOpenOne
    rw [if_neg (not_not.2 hj)]
    split_ifs with habort
    · simp
      rfl
    · rw [advance_openRest, mainCopyHashes, ← liftComp_mapM_local, map_bind]
      refine bind_congr fun cds => ?_
      split_ifs <;> simp
  · rw [if_neg hj]
    unfold mainOpenOne
    rw [if_pos hj]
    simp

theorem stages_realTail_eq (st : A.State) (p : C.Party → MainInput C × List (Tuple C)) :
    mainRealTail K D A jobs st p =
      A.answer st (.inl (.inr (mainMultLeak D (outputsOf jobs).length (fun i => outputShares K jobs (p i).1)
        (fun _ => one K)))) >>= fun a =>
      liftComp ($ᵗ (C.Term → Fin (outputsOf jobs).length → Bit)) (LocalSpec C) >>= fun fresh =>
      if ¬ mainAllReceive D (stagesReplyR a.2).2.2.2 then pure (a.1, fun _ => none) else
      A.answer a.1 (.inr (mainVerifyLeak D fun i => if i ∈ D.1 then none else
        some (stagesTuples K jobs (p i) (mainFmultOut K D .peer (outputsOf jobs).length
          (fun i => outputShares K jobs (p i).1) (fun _ => one K) (stagesReplyR a.2) fresh i)))) >>= fun b =>
      if ¬ (mainVerifyLeak D fun i => if i ∈ D.1 then none else
        some (stagesTuples K jobs (p i) (mainFmultOut K D .peer (outputsOf jobs).length
          (fun i => outputShares K jobs (p i).1) (fun _ => one K) (stagesReplyR a.2) fresh i))).2.2 = true
      then pure (b.1, fun _ => none) else
      mainOpenWith K D A b.1 (stagesReplyV b.2) (outputsOf jobs).length
        (mainFmultOut K D .peer (outputsOf jobs).length
          (fun i => outputShares K jobs (p i).1) (fun _ => one K) (stagesReplyR a.2) fresh) :=
  rfl

theorem stages_tail (f : ℕ) (st : A.State) (p : C.Party → MainInput C × List (Tuple C)) :
    executeRounds localRoles D A (mainFunctionalities K mode) (f + 3) st (stagesSteps K D mode jobs [] p) =
      mainHybridOut D jobs <$> mainRealTail K D A jobs st p := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  rw [executeRounds, if_neg (fun h => by simpa [stagesSteps, hi₀, callStep, Step.isDone] using h i₀ hi₀),
    stages_stepRound_rerand]
  rw [stages_realTail_eq]
  simp only [bind_assoc, pure_bind, map_bind]
  refine bind_congr fun a => bind_congr fun fresh => ?_
  by_cases hall : mainAllReceive D (stagesReplyR a.2).2.2.2
  · rw [if_neg (not_not.2 hall)]
    set v := mainFmultOut K D .peer (outputsOf jobs).length (fun i => outputShares K jobs (p i).1)
      (fun _ => one K) (stagesReplyR a.2) fresh with hv
    have hsteps : (fun i => if i ∈ D.1 ∨ i ∉ (stagesReplyR a.2).2.2.2 then .done none else
        stagesVerifyStep K jobs i (p i) (v i) : C.Party → Step C E (MainSpec C) (List (List Bit))) =
        fun i => if i ∈ D.1 then .done none else stagesVerifyStep K jobs i (p i) (v i) := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [hi]
      · simp [hi, hall i hi]
    rw [hsteps, executeRounds, if_neg (fun h => by simpa [hi₀, stagesVerifyStep, Step.isDone] using h i₀ hi₀),
      stages_stepRound_verify]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun b => ?_
    set L := mainVerifyLeak D fun i => if i ∈ D.1 then none else some (stagesTuples K jobs (p i) (v i)) with hL
    by_cases hacc : L.2.2 = true
    · rw [if_neg (not_not.2 hacc)]
      have hseq : (fun j => if j ∉ D.1 ∧ L.2.2 = true ∧ j ∈ stagesReplyV b.2 then
          mainCopyHashes (v j) (outputsOf jobs).length >>= fun ds => pure (stagesOpenStep K jobs j (v j) ds)
          else pure (.done none)) =
          fun j => (if j ∉ D.1 ∧ j ∈ stagesReplyV b.2 then mainCopyHashes (v j) (outputsOf jobs).length
            else pure []) >>= fun ds => pure ((fun j ds => if j ∉ D.1 ∧ j ∈ stagesReplyV b.2 then
              stagesOpenStep K jobs j (v j) ds else (.done none : Step C E (MainSpec C) (List (List Bit)))) j ds) := by
        funext j
        by_cases hj : j ∉ D.1 ∧ j ∈ stagesReplyV b.2
        · simp [hj, hacc]
        · simp [hj, hacc]
      rw [hseq, sequenceFin_bind_pure, bind_assoc]
      simp only [pure_bind]
      unfold mainOpenWith
      rw [map_bind]
      refine bind_congr fun ds => ?_
      by_cases hex : ∃ i, i ∉ D.1 ∧ i ∈ stagesReplyV b.2
      · rw [if_neg (not_not.2 hex)]
        obtain ⟨i₂, hi₂⟩ := hex
        rw [executeRounds, if_neg (fun h => by simpa [hi₂, stagesOpenStep, Step.isDone] using h i₂ hi₂.1)]
        simp only []
        rw [stages_stepRound_open]
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun q => ?_
        have hM : (fun j => (fun o => (Step.done (o.map (assemble jobs)) :
            Step C E (MainSpec C) (List (List Bit)))) <$>
            mainOpenOne K D (stagesReplyV b.2) (outputsOf jobs).length v ds q.2 j) =
            fun j => mainOpenOne K D (stagesReplyV b.2) (outputsOf jobs).length v ds q.2 j >>= fun o =>
              pure ((fun j o => (Step.done (if j ∉ D.1 then o.map (assemble jobs) else none) :
                Step C E (MainSpec C) (List (List Bit)))) j o) := by
          funext j
          by_cases hj : j ∈ D.1
          · simp [mainOpenOne, hj]
          · simp [hj, map_eq_bind_pure_comp]
        rw [hM, sequenceFin_bind_pure, bind_assoc]
        simp only [pure_bind]
        refine bind_congr fun os => ?_
        rw [stages_executeRounds_allDone D A _ _ _ _ fun j => by simp [Step.isDone]]
        simp [mainHybridOut, Step.output]
      · rw [if_pos hex, stages_executeRounds_done D A _ _ _ _ fun j => by
          have : ¬ (j ∉ D.1 ∧ j ∈ stagesReplyV b.2) := fun h => hex ⟨j, h⟩
          simp only [this, if_false]]
        simp [mainHybridOut]
    · rw [if_pos hacc, stages_sequenceFin_eq_pure _ (fun _ => .done none) (fun j => by simp [hacc]), pure_bind,
        stages_executeRounds_done D A _ _ _ _ fun _ => rfl]
      simp [mainHybridOut]
  · have hab : ∃ i ∉ D.1, i ∉ (stagesReplyR a.2).2.2.2 := by
      unfold mainAllReceive at hall
      push Not at hall
      exact hall
    obtain ⟨i₁, hi₁, hr₁⟩ := hab
    rw [if_pos hall, stages_executeRounds_abort D A _ _ _ _ (fun i hi => by simp [hi])
      (fun i hi => by
        by_cases hr : i ∈ (stagesReplyR a.2).2.2.2
        · exact Or.inr ⟨_, _, by simp [hi, hr]; rfl, rfl⟩
        · exact Or.inl (by simp [hi, hr]))
      ⟨i₁, hi₁, by simp [hi₁, hr₁]⟩]
    simp [mainHybridOut]

/-- The rest of the real game after the layers. -/
def stagesRealK (a : A.State × Option (C.Party → MainInput C × List (Tuple C))) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) :=
  match a.2 with
  | none => pure (a.1, fun _ => none)
  | some p => mainRealTail K D A jobs a.1 p

theorem stages_realLayers_cons (l : ℕ) (ls : List ℕ) (st : A.State) (p : C.Party → MainInput C × List (Tuple C)) :
    mainRealLayers K D A mode jobs (l :: ls) st p =
      A.answer st (.inl (.inl (mainMultLeak D (gatesAt jobs l).length (fun i => layerX K jobs l (p i).1)
        (fun i => layerY K jobs l (p i).1)))) >>= fun a =>
      liftComp ($ᵗ (C.Term → Fin (gatesAt jobs l).length → Bit)) (LocalSpec C) >>= fun fresh =>
      if ¬ mainAllReceive D (stagesReplyL a.2).2.2.2 then pure (a.1, none) else
      mainRealLayers K D A mode jobs ls a.1 (stagesNext K mode jobs l p (mainFmultOut K D mode
        (gatesAt jobs l).length (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1)
        (stagesReplyL a.2) fresh)) :=
  rfl

theorem stages_layers : ∀ (ls : List ℕ) (f : ℕ) (st : A.State) (p : C.Party → MainInput C × List (Tuple C)),
    executeRounds localRoles D A (mainFunctionalities K mode) (f + ls.length + 3) st
        (stagesSteps K D mode jobs ls p) =
      mainHybridOut D jobs <$> (mainRealLayers K D A mode jobs ls st p >>= stagesRealK K D A jobs)
  | [], f, st, p => by
    rw [mainRealLayers, pure_bind]
    exact stages_tail K D A mode jobs f st p
  | l :: ls, f, st, p => by
    obtain ⟨i₀, hi₀⟩ := main_honest_exists D
    rw [show f + (l :: ls).length + 3 = (f + ls.length + 3) + 1 by simp; omega, executeRounds,
      if_neg (fun h => by simpa [stagesSteps, hi₀, callStep, Step.isDone] using h i₀ hi₀),
      stages_stepRound_layer, stages_realLayers_cons]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun a => bind_congr fun fresh => ?_
    by_cases hall : mainAllReceive D (stagesReplyL a.2).2.2.2
    · rw [if_neg (not_not.2 hall), ← map_bind, ← stages_layers ls f a.1]
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [stagesSteps, hi]
      · simp [stagesSteps, hi, hall i hi]
    · have hab : ∃ i ∉ D.1, i ∉ (stagesReplyL a.2).2.2.2 := by
        unfold mainAllReceive at hall
        push Not at hall
        exact hall
      obtain ⟨i₁, hi₁, hr₁⟩ := hab
      rw [if_pos hall, stages_executeRounds_abort D A _ _ _ _ (fun i hi => by simp [hi])
        (fun i hi => by
          by_cases hr : i ∈ (stagesReplyL a.2).2.2.2
          · obtain ⟨input, resume, h1, h2⟩ := stages_callStep_none K mode jobs i ls
              (stagesNext K mode jobs l p (mainFmultOut K D mode (gatesAt jobs l).length
                (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) (stagesReplyL a.2) fresh) i)
            exact Or.inr ⟨input, resume, by simp [hi, hr, h1], h2⟩
          · exact Or.inl (by simp [hi, hr]))
        ⟨i₁, hi₁, by simp [hi₁, hr₁]⟩]
      simp [mainHybridOut, stagesRealK]

end Network

/-- The network runs the real phase as `mainRealGame`. -/
theorem mainEngineReal (prims : Primitives) (K : Constants C E) : MainEngineReal prims K := by
  intro mode jobs D A x _ st
  apply SameRun.of_eq
  unfold executePhase
  rw [main_startSteps, pure_bind]
  have h := stages_layers K D A mode jobs (List.range (depth jobs)) 0 st (fun i => (x i, []))
  rw [List.length_range, Nat.zero_add] at h
  exact h

/-! ## The simulation (GS20, Theorem 2) -/

section Simulation

/-- The terms of a tuple that the coalition knows. -/
def stagesKnownTuple (D : C.Coalition) (τ : Tuple C) : Tuple C :=
  ⟨knownView D.1 τ.count τ.x, knownView D.1 τ.count τ.y, knownView D.1 τ.count τ.z, τ.count, τ.mode⟩

/-- The inputs of the honest operators. -/
def stagesHonest {β : Type} (D : C.Coalition) (u : C.Party → β) : C.Party → Option β :=
  fun i => if i ∈ D.1 then none else some (u i)

/-- The honest copies of tuple `m` agree. -/
def stagesAgreeAt (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ) : Prop :=
  ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 →
    ∀ g < (((views i)[m]?).map (·.count)).getD 0,
      ((views i)[m]?).map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) =
        ((views j)[m]?).map fun τ => (τ.x T g, τ.y T g, τ.z T g)

/-- The difference of tuple `m`, as `F_multVerify` computes it. -/
def stagesRealDiff (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ) : ℕ → Bit := fun g =>
  if g < (tupleAt (stagesHonest D views) m).count then
    shareValue (tupleAt (stagesHonest D views) m).z g -
      shareValue (tupleAt (stagesHonest D views) m).x g * shareValue (tupleAt (stagesHonest D views) m).y g
  else 0

/-- Tuple `m` is a product. -/
def stagesProductAt (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ) : Prop :=
  IsProduct (tupleAt (stagesHonest D views) m)

theorem stages_firstInput {β : Type} [Inhabited β] (D : C.Coalition) (u : C.Party → β) (P : β → Prop)
    (hu : ∀ i ∉ D.1, P (u i)) : P (firstInput (stagesHonest D u)) := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  unfold firstInput
  have hmem : u i₀ ∈ C.parties.filterMap (stagesHonest D u) :=
    List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [stagesHonest, hi₀]⟩
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hl, List.headD_cons]
  have ha : a ∈ C.parties.filterMap (stagesHonest D u) := hl ▸ List.mem_cons_self
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 ha
  unfold stagesHonest at hj
  split_ifs at hj with hjD
  cases hj
  exact hu j hjD

/-- `reconstruct` reads an honest holder. -/
theorem stages_reconstruct {α β : Type} [Inhabited α] (D : C.Coalition) (u : C.Party → β)
    (f : β → C.Term → α) (T : C.Term) :
    ∃ h ∈ C.holders T, h ∉ D.1 ∧ reconstruct (fun i => (stagesHonest D u i).map f) T = f (u h) T := by
  obtain ⟨i₀, hi₀T, hi₀⟩ := main_exists_honest_holder D T
  unfold reconstruct
  have hmem : f (u i₀) ∈ C.parties.filterMap fun i =>
      if i ∈ C.holders T then (stagesHonest D u i).map f else none :=
    List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [stagesHonest, hi₀, hi₀T]⟩
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hl]
  have ha : a ∈ C.parties.filterMap fun i => if i ∈ C.holders T then (stagesHonest D u i).map f else none :=
    hl ▸ List.mem_cons_self
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 ha
  unfold stagesHonest at hj
  split_ifs at hj with hjT hjD
  · simp at hj
  · simp only [Option.map_some, Option.some.injEq] at hj
    subst hj
    exact ⟨j, hjT, hjD, by simp⟩

/-- The first honest operator. -/
def stagesFirst (D : C.Coalition) : C.Party :=
  ((C.parties.filter fun i => i ∉ D.1).head?).getD (Classical.choose (main_honest_exists D))

theorem stages_filterMap_honest {β : Type} (D : C.Coalition) (f : C.Party → β) :
    ∀ l : List C.Party, l.filterMap (stagesHonest D f) = (l.filter fun i => i ∉ D.1).map f
  | [] => rfl
  | i :: l => by
    have ih := stages_filterMap_honest D f l
    by_cases hi : i ∈ D.1
    · rw [List.filterMap_cons, List.filter_cons]
      simp only [stagesHonest, hi, if_true] at ih ⊢
      simpa using ih
    · rw [List.filterMap_cons, List.filter_cons]
      simp only [stagesHonest, hi, if_false] at ih ⊢
      simpa using ih

theorem stages_first_honest (D : C.Coalition) : stagesFirst D ∉ D.1 := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  have hmem : i₀ ∈ C.parties.filter fun i => i ∉ D.1 :=
    List.mem_filter.2 ⟨List.mem_finRange i₀, by simp [hi₀]⟩
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  unfold stagesFirst
  rw [hl]
  have ha : a ∈ C.parties.filter fun i => i ∉ D.1 := hl ▸ List.mem_cons_self
  simpa using (List.mem_filter.1 ha).2

theorem stages_firstInput_eq {β : Type} [Inhabited β] (D : C.Coalition) (f : C.Party → β) :
    firstInput (stagesHonest D f) = f (stagesFirst D) := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  have hmem : i₀ ∈ C.parties.filter fun i => i ∉ D.1 :=
    List.mem_filter.2 ⟨List.mem_finRange i₀, by simp [hi₀]⟩
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  unfold firstInput stagesFirst
  rw [stages_filterMap_honest, hl]
  rfl

theorem stages_tupleAt_congr (D : C.Coalition) (f f' : C.Party → List (Tuple C)) (m : ℕ)
    (h : ∀ i ∉ D.1, (f i)[m]? = (f' i)[m]?) :
    tupleAt (stagesHonest D f) m = tupleAt (stagesHonest D f') m := by
  have hat : ∀ i, (stagesHonest D f i).bind (·[m]?) = (stagesHonest D f' i).bind (·[m]?) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp [stagesHonest, hi]
    · simp [stagesHonest, hi, h i hi]
  unfold tupleAt
  simp only [stages_firstInput_eq, h _ (stages_first_honest D), hat]

/-- Tuple `m` of operator `i`. -/
def stagesAt (views : C.Party → List (Tuple C)) (i : C.Party) (m : ℕ) : Tuple C :=
  ((views i)[m]?).getD ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩

theorem stages_bind_at (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ)
    (hm : ∀ i ∉ D.1, m < (views i).length) :
    (fun i => (stagesHonest D views i).bind (·[m]?)) = stagesHonest D (fun i => stagesAt views i m) := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [stagesHonest, hi]
  · simp [stagesHonest, hi, stagesAt, List.getElem?_eq_getElem (hm i hi)]

theorem stages_tupleAt_x (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ)
    (hm : ∀ i ∉ D.1, m < (views i).length) (T : C.Term) :
    ∃ h ∈ C.holders T, h ∉ D.1 ∧ (tupleAt (stagesHonest D views) m).x T = (stagesAt views h m).x T := by
  unfold tupleAt
  dsimp only
  simp only [fun i => congrFun (stages_bind_at D views m hm) i]
  exact stages_reconstruct D (fun i => stagesAt views i m) Tuple.x T

theorem stages_tupleAt_y (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ)
    (hm : ∀ i ∉ D.1, m < (views i).length) (T : C.Term) :
    ∃ h ∈ C.holders T, h ∉ D.1 ∧ (tupleAt (stagesHonest D views) m).y T = (stagesAt views h m).y T := by
  unfold tupleAt
  dsimp only
  simp only [fun i => congrFun (stages_bind_at D views m hm) i]
  exact stages_reconstruct D (fun i => stagesAt views i m) Tuple.y T

theorem stages_tupleAt_z (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ)
    (hm : ∀ i ∉ D.1, m < (views i).length) (T : C.Term) :
    ∃ h ∈ C.holders T, h ∉ D.1 ∧ (tupleAt (stagesHonest D views) m).z T = (stagesAt views h m).z T := by
  unfold tupleAt
  dsimp only
  simp only [fun i => congrFun (stages_bind_at D views m hm) i]
  exact stages_reconstruct D (fun i => stagesAt views i m) Tuple.z T

theorem stages_tupleAt_count (D : C.Coalition) (views : C.Party → List (Tuple C)) (m : ℕ)
    (hshape : ∀ i ∉ D.1, ∀ j ∉ D.1, (views i).map (fun τ => (τ.count, τ.mode)) =
      (views j).map (fun τ => (τ.count, τ.mode))) (i : C.Party) (hi : i ∉ D.1) :
    (tupleAt (stagesHonest D views) m).count = (((views i)[m]?).map (·.count)).getD 0 := by
  unfold tupleAt
  dsimp only
  refine stages_firstInput D views (fun l => (((l[m]?).map (·.count)).getD 0) =
    (((views i)[m]?).map (·.count)).getD 0) fun j hj => ?_
  have h := congrArg (fun l : List (ℕ × ReshareMode) => ((l[m]?).map (·.1)).getD 0) (hshape j hj i hi)
  simpa [List.getElem?_map, Function.comp_def] using h

/-- The agreement that `F_multVerify` checks. -/
def stagesRealAgree (D : C.Coalition) (views : C.Party → List (Tuple C)) (N : ℕ) : Prop :=
  ∀ k < N, ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 →
    ∀ g < ((List.map (tupleAt (stagesHonest D views)) (List.range N)).getD k
      ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count,
      Option.map (fun τ : Tuple C => (τ.x T g, τ.y T g, τ.z T g)) ((stagesHonest D views i).bind (·[k]?)) =
        Option.map (fun τ : Tuple C => (τ.x T g, τ.y T g, τ.z T g)) ((stagesHonest D views j).bind (·[k]?))

theorem stages_realAgree_iff (D : C.Coalition) (views : C.Party → List (Tuple C)) (N : ℕ)
    (_hlen : ∀ i ∉ D.1, (views i).length = N)
    (hshape : ∀ i ∉ D.1, ∀ j ∉ D.1, (views i).map (fun τ => (τ.count, τ.mode)) =
      (views j).map (fun τ => (τ.count, τ.mode))) :
    stagesRealAgree D views N ↔ ∀ m < N, stagesAgreeAt D views m := by
  unfold stagesRealAgree stagesAgreeAt
  refine forall₂_congr fun k hk => forall_congr' fun T => forall₂_congr fun i hi =>
    forall₂_congr fun j hj => forall_congr' fun hiD => forall_congr' fun hjD => ?_
  have hc : ((List.map (tupleAt (stagesHonest D views)) (List.range N)).getD k
      ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count = (((views i)[k]?).map (·.count)).getD 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    exact stages_tupleAt_count D views k hshape i hiD
  rw [hc]
  simp [stagesHonest, hiD, hjD]

theorem stages_vector_eq_iff {R : Type} (c : ℕ) (f f' : ℕ → R) :
    vector c f = vector c f' ↔ ∀ g < c, f g = f' g := by
  unfold vector
  rw [List.map_inj_left]
  simp

theorem stages_knownAgree_iff (D : C.Coalition) (views sviews : C.Party → List (Tuple C)) (N : ℕ)
    (hlen : ∀ i ∉ D.1, (views i).length = N)
    (hshape : ∀ i ∉ D.1, ∀ j ∉ D.1, (views i).map (fun τ => (τ.count, τ.mode)) =
      (views j).map (fun τ => (τ.count, τ.mode)))
    (hknown : ∀ i ∉ D.1, sviews i = (views i).map (stagesKnownTuple D))
    (hhidden : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ m : ℕ,
      ((views i)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)) =
        ((views j)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T))) :
    (∀ m < N, stagesAgreeAt D views m) ↔ mainKnownAgree D sviews := by
  constructor
  · intro h k T i hi j hj hiD hjD
    rw [hknown i hiD, hknown j hjD, List.getElem?_map, List.getElem?_map]
    rcases Nat.lt_or_ge k N with hk | hk
    · have hki : k < (views i).length := by rw [hlen i hiD]; exact hk
      have hkj : k < (views j).length := by rw [hlen j hjD]; exact hk
      rw [List.getElem?_eq_getElem hki, List.getElem?_eq_getElem hkj]
      have hcnt : (views i)[k].count = (views j)[k].count := by
        have := congrArg (fun l : List (ℕ × ReshareMode) => (l[k]?).map (·.1)) (hshape i hiD j hjD)
        simpa [List.getElem?_map, List.getElem?_eq_getElem hki, List.getElem?_eq_getElem hkj] using this
      simp only [Option.map_some, Option.some.injEq, stagesKnownTuple, Prod.mk.injEq]
      rw [hcnt]
      by_cases hT : KnownTo D.1 T
      · have hag := h k hk T i hi j hj hiD hjD
        simp only [List.getElem?_eq_getElem hki, List.getElem?_eq_getElem hkj,
          Option.map_some, Option.getD_some, Option.some.injEq, Prod.mk.injEq] at hag
        refine ⟨(stages_vector_eq_iff _ _ _).2 fun g hg => ?_, (stages_vector_eq_iff _ _ _).2 fun g hg => ?_,
          (stages_vector_eq_iff _ _ _).2 fun g hg => ?_⟩
        · simp only [knownView, hT, true_and, if_pos hg]
          exact (hag g (hcnt ▸ hg)).1
        · simp only [knownView, hT, true_and, if_pos hg]
          exact (hag g (hcnt ▸ hg)).2.1
        · simp only [knownView, hT, true_and, if_pos hg]
          exact (hag g (hcnt ▸ hg)).2.2
      · unfold knownView
        simp [hT]
    · rw [List.getElem?_eq_none (by rw [hlen i hiD]; exact hk), List.getElem?_eq_none (by rw [hlen j hjD]; exact hk)]
  · intro h m hm T i hi j hj hiD hjD g hg
    have hmi : m < (views i).length := by rw [hlen i hiD]; exact hm
    have hmj : m < (views j).length := by rw [hlen j hjD]; exact hm
    have hcnt : (views i)[m].count = (views j)[m].count := by
      have := congrArg (fun l : List (ℕ × ReshareMode) => (l[m]?).map (·.1)) (hshape i hiD j hjD)
      simpa [List.getElem?_map, List.getElem?_eq_getElem hmi, List.getElem?_eq_getElem hmj] using this
    rw [List.getElem?_eq_getElem hmi, Option.map_some, Option.getD_some] at hg
    by_cases hT : KnownTo D.1 T
    · have hag := h m T i hi j hj hiD hjD
      rw [hknown i hiD, hknown j hjD, List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hmi,
        List.getElem?_eq_getElem hmj] at hag
      simp only [Option.map_some, Option.some.injEq, stagesKnownTuple, Prod.mk.injEq] at hag
      rw [hcnt] at hag
      obtain ⟨h1, h2, h3⟩ := hag
      have e1 := (stages_vector_eq_iff _ _ _).1 h1 g (hcnt ▸ hg)
      have e2 := (stages_vector_eq_iff _ _ _).1 h2 g (hcnt ▸ hg)
      have e3 := (stages_vector_eq_iff _ _ _).1 h3 g (hcnt ▸ hg)
      simp only [knownView, hT, true_and, if_pos (hcnt ▸ hg : g < (views j)[m].count)] at e1 e2 e3
      rw [List.getElem?_eq_getElem hmi, List.getElem?_eq_getElem hmj]
      simp [e1, e2, e3]
    · have hh := congrArg (Option.map fun t : (ℕ → Bit) × (ℕ → Bit) × (ℕ → Bit) => (t.1 g, t.2.1 g, t.2.2 g))
        (hhidden i hiD j hjD T hT hi hj m)
      simpa [Option.map_map, Function.comp_def] using hh

/-- The output of `F_mult` at operator `i`, from the base and the target of the sharing. -/
def stagesMultZ (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ) (base : Shares C Bit)
    (target : ℕ → Bit) (r : MainMultReply C) (i : C.Party) : Shares C Bit := fun T g =>
  if i ∈ C.holders T ∧ g < n then
    mainMultSharing D base target T g + (if ∃ j ∈ D.1, filler K mode T g = some j then r.2.2.1 i T g else 0)
  else 0

/-- The target of `F_mult` on the honest inputs. -/
def stagesTarget (K : Constants C E) (D : C.Coalition) (X Y : C.Party → Shares C Bit) (r : MainMultReply C) :
    ℕ → Bit := fun g => (∑ j ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext j) (X j) (Y j) g) + r.1 g

theorem stages_mainFmultOut_eq (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y : C.Party → Shares C Bit) (r : MainMultReply C) (fresh : C.Term → Fin n → Bit) :
    mainFmultOut K D mode n X Y r fresh =
      stagesMultZ K D mode n (mainMultBase D n r.2.1 fresh) (stagesTarget K D X Y r) r := rfl

theorem stages_tupleAt_count' (D : C.Coalition) (views : C.Party → List (Tuple C)) (m n : ℕ)
    (h : ∀ i ∉ D.1, ((views i)[m]?).map (·.count) = some n) :
    (tupleAt (stagesHonest D views) m).count = n := by
  unfold tupleAt
  simp only [stages_firstInput_eq, h _ (stages_first_honest D), Option.getD_some]

/-- GS20: when the copies of tuple `m` agree, its difference is `mainDifference`. -/
theorem stages_diff_correct (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y Xs Ys : C.Party → Shares C Bit) (r : MainMultReply C) (base : Shares C Bit)
    (views : C.Party → List (Tuple C)) (m : ℕ)
    (hview : ∀ i ∉ D.1, (views i)[m]? = some
      ⟨X i, Y i, stagesMultZ K D mode n base (stagesTarget K D X Y r) r i, n, mode⟩)
    (hXb : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, i ∈ C.holders T → j ∈ C.holders T → ∀ g, n ≤ g → X i T g = X j T g)
    (hYb : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, i ∈ C.holders T → j ∈ C.holders T → ∀ g, n ≤ g → Y i T g = Y j T g)
    (hxs : ∀ i T, i ∉ D.1 → KnownTo D.1 T → i ∈ C.holders T → ∀ g < n, Xs i T g = X i T g)
    (hys : ∀ i T, i ∉ D.1 → KnownTo D.1 T → i ∈ C.holders T → ∀ g < n, Ys i T g = Y i T g)
    (hag : stagesAgreeAt D views m) :
    mainDifference K D mode n Xs Ys r = stagesRealDiff D views m := by
  have hm : ∀ i ∉ D.1, m < (views i).length := fun i hi => by
    by_contra hc
    have := hview i hi
    rw [List.getElem?_eq_none (by omega)] at this
    cases this
  have hat : ∀ i ∉ D.1, stagesAt views i m = ⟨X i, Y i, stagesMultZ K D mode n base (stagesTarget K D X Y r) r i, n, mode⟩ :=
    fun i hi => by simp [stagesAt, hview i hi]
  have hcount := stages_tupleAt_count' D views m n fun i hi => by simp [hview i hi]
  -- the agreement of tuple `m` at two honest holders
  have hpair : ∀ T i j, i ∈ C.holders T → j ∈ C.holders T → i ∉ D.1 → j ∉ D.1 → ∀ g < n,
      X i T g = X j T g ∧ Y i T g = Y j T g ∧
        stagesMultZ K D mode n base (stagesTarget K D X Y r) r i T g =
          stagesMultZ K D mode n base (stagesTarget K D X Y r) r j T g := by
    intro T i j hi hj hiD hjD g hg
    have := hag T i hi j hj hiD hjD g (by simp [hview i hiD, hg])
    simpa [hview i hiD, hview j hjD] using this
  have hx : ∀ i T, i ∉ D.1 → i ∈ C.holders T → X i T = (tupleAt (stagesHonest D views) m).x T := by
    intro i T hiD hiT
    obtain ⟨h, hhT, hhD, hxh⟩ := stages_tupleAt_x D views m hm T
    rw [hxh, hat h hhD]
    funext g
    rcases Nat.lt_or_ge g n with hg | hg
    · exact (hpair T i h hiT hhT hiD hhD g hg).1
    · exact hXb i hiD h hhD T hiT hhT g hg
  have hy : ∀ i T, i ∉ D.1 → i ∈ C.holders T → Y i T = (tupleAt (stagesHonest D views) m).y T := by
    intro i T hiD hiT
    obtain ⟨h, hhT, hhD, hyh⟩ := stages_tupleAt_y D views m hm T
    rw [hyh, hat h hhD]
    funext g
    rcases Nat.lt_or_ge g n with hg | hg
    · exact (hpair T i h hiT hhT hiD hhD g hg).2.1
    · exact hYb i hiD h hhD T hiT hhT g hg
  funext g
  unfold stagesRealDiff
  rw [hcount]
  by_cases hg : g < n
  · rw [if_pos hg, ← mainDifference_correct K D mode n X Y Xs Ys _ _ hx hy hxs hys r base g hg]
    congr 1
    unfold shareValue
    refine Finset.sum_congr rfl fun T _ => ?_
    obtain ⟨h, hhT, hhD, hzh⟩ := stages_tupleAt_z D views m hm T
    have href := mainRefHolder_spec D T
    rw [hzh, hat h hhD]
    dsimp only
    rw [(hpair T h (mainRefHolder D T) hhT href.1 hhD href.2 g hg).2.2]
    simp only [stagesMultZ, href.1, hg, and_self, if_true]
    rfl
  · rw [if_neg hg]
    simp [mainDifference, hg]

theorem stages_getElem?_append_lt {β : Type} (l : List β) (a : β) (m : ℕ) (hm : m < l.length) :
    (l ++ [a])[m]? = l[m]? := List.getElem?_append_left hm

theorem stages_getElem?_append_eq {β : Type} (l : List β) (a : β) : (l ++ [a])[l.length]? = some a := by
  simp

theorem stages_agreeAt_append (D : C.Coalition) (B : C.Party → List (Tuple C)) (a : C.Party → Tuple C) (N m : ℕ)
    (hlen : ∀ i ∉ D.1, (B i).length = N) (hm : m < N) :
    stagesAgreeAt D (fun i => B i ++ [a i]) m ↔ stagesAgreeAt D B m := by
  unfold stagesAgreeAt
  refine forall_congr' fun T => forall₂_congr fun i hi => forall₂_congr fun j hj =>
    forall_congr' fun hiD => forall_congr' fun hjD => ?_
  rw [stages_getElem?_append_lt _ _ _ (by rw [hlen i hiD]; exact hm),
    stages_getElem?_append_lt _ _ _ (by rw [hlen j hjD]; exact hm)]

theorem stages_realDiff_append (D : C.Coalition) (B : C.Party → List (Tuple C)) (a : C.Party → Tuple C) (N m : ℕ)
    (hlen : ∀ i ∉ D.1, (B i).length = N) (hm : m < N) :
    stagesRealDiff D (fun i => B i ++ [a i]) m = stagesRealDiff D B m := by
  unfold stagesRealDiff
  rw [stages_tupleAt_congr D (fun i => B i ++ [a i]) B m fun i hi =>
    stages_getElem?_append_lt _ _ _ (by rw [hlen i hi]; exact hm)]

/-- The hypotheses of `stages_verifyLeak` survive one more tuple. -/
theorem stages_append_hyps (D : C.Coalition) (B SB : C.Party → List (Tuple C)) (dB : List (ℕ → Bit))
    (a sa : C.Party → Tuple C) (dnew : ℕ → Bit)
    (hlen : ∀ i ∉ D.1, (B i).length = dB.length)
    (hshape : ∀ i ∉ D.1, ∀ j ∉ D.1, (B i).map (fun τ => (τ.count, τ.mode)) = (B j).map (fun τ => (τ.count, τ.mode)))
    (hknown : ∀ i ∉ D.1, SB i = (B i).map (stagesKnownTuple D))
    (hhidden : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ m : ℕ,
      ((B i)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)) =
        ((B j)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)))
    (hdiff : ∀ m (hm : m < dB.length), stagesAgreeAt D B m → dB[m] = stagesRealDiff D B m)
    (hsa : ∀ i ∉ D.1, sa i = stagesKnownTuple D (a i))
    (hashape : ∀ i ∉ D.1, ∀ j ∉ D.1, (a i).count = (a j).count ∧ (a i).mode = (a j).mode)
    (hahidden : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T →
      (a i).x T = (a j).x T ∧ (a i).y T = (a j).y T ∧ (a i).z T = (a j).z T)
    (hadiff : stagesAgreeAt D (fun i => B i ++ [a i]) dB.length →
      dnew = stagesRealDiff D (fun i => B i ++ [a i]) dB.length) :
    (∀ i ∉ D.1, (B i ++ [a i]).length = (dB ++ [dnew]).length) ∧
    (∀ i ∉ D.1, ∀ j ∉ D.1, (B i ++ [a i]).map (fun τ => (τ.count, τ.mode)) =
      (B j ++ [a j]).map (fun τ => (τ.count, τ.mode))) ∧
    (∀ i ∉ D.1, SB i ++ [sa i] = (B i ++ [a i]).map (stagesKnownTuple D)) ∧
    (∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ m : ℕ,
      ((B i ++ [a i])[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)) =
        ((B j ++ [a j])[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T))) ∧
    (∀ m (hm : m < (dB ++ [dnew]).length), stagesAgreeAt D (fun i => B i ++ [a i]) m →
      (dB ++ [dnew])[m] = stagesRealDiff D (fun i => B i ++ [a i]) m) := by
  refine ⟨fun i hi => by simp [hlen i hi], fun i hi j hj => ?_, fun i hi => ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, hshape i hi j hj, (hashape i hi j hj).1,
      (hashape i hi j hj).2]
  · simp [hknown i hi, hsa i hi]
  · intro i hi j hj T hT hiT hjT m
    rcases Nat.lt_trichotomy m dB.length with hm | rfl | hm
    · rw [stages_getElem?_append_lt _ _ _ (by rw [hlen i hi]; exact hm),
        stages_getElem?_append_lt _ _ _ (by rw [hlen j hj]; exact hm)]
      exact hhidden i hi j hj T hT hiT hjT m
    · rw [← hlen i hi, stages_getElem?_append_eq, hlen i hi, ← hlen j hj, stages_getElem?_append_eq]
      obtain ⟨h1, h2, h3⟩ := hahidden i hi j hj T hT hiT hjT
      simp [h1, h2, h3]
    · rw [List.getElem?_eq_none (by simp [hlen i hi]; omega), List.getElem?_eq_none (by simp [hlen j hj]; omega)]
  · intro m hm hag
    simp only [List.length_append, List.length_singleton] at hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · rw [List.getElem_append_left hm, stages_realDiff_append D B a dB.length m hlen hm]
      exact hdiff m hm ((stages_agreeAt_append D B a dB.length m hlen hm).1 hag)
    · rw [List.getElem_append_right (by omega)]
      simpa using hadiff hag

/-- The real tuple of one call of `F_mult`. -/
def stagesRealTuple (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y : C.Party → Shares C Bit) (r : MainMultReply C) (fresh : C.Term → Fin n → Bit) (i : C.Party) : Tuple C :=
  ⟨X i, Y i, mainFmultOut K D mode n X Y r fresh i, n, mode⟩

/-- The simulated tuple of one call of `F_mult`. -/
def stagesSimTuple (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (Xs Ys : C.Party → Shares C Bit) (r : MainMultReply C) (i : C.Party) : Tuple C :=
  ⟨knownView D.1 n (Xs i), knownView D.1 n (Ys i), mainKnownMult K D mode n r i, n, mode⟩

/-- The facts of `stages_append_hyps` for the tuple of one call of `F_mult`. -/
theorem stages_new_tuple (K : Constants C E) (D : C.Coalition) (mode : ReshareMode) (n : ℕ)
    (X Y Xs Ys : C.Party → Shares C Bit) (r : MainMultReply C) (fresh : C.Term → Fin n → Bit)
    (B : C.Party → List (Tuple C)) (N : ℕ) (hlen : ∀ i ∉ D.1, (B i).length = N)
    (hX1 : ∀ i ∉ D.1, ∀ T, KnownTo D.1 T → X i T = Xs i T)
    (hY1 : ∀ i ∉ D.1, ∀ T, KnownTo D.1 T → Y i T = Ys i T)
    (hX2 : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → X i T = X j T)
    (hY2 : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → Y i T = Y j T)
    (hXb : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, i ∈ C.holders T → j ∈ C.holders T → ∀ g, n ≤ g → X i T g = X j T g)
    (hYb : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, i ∈ C.holders T → j ∈ C.holders T → ∀ g, n ≤ g → Y i T g = Y j T g) :
    (∀ i ∉ D.1, stagesSimTuple K D mode n Xs Ys r i =
      stagesKnownTuple D (stagesRealTuple K D mode n X Y r fresh i)) ∧
    (∀ i ∉ D.1, ∀ j ∉ D.1, (stagesRealTuple K D mode n X Y r fresh i).count =
      (stagesRealTuple K D mode n X Y r fresh j).count ∧
      (stagesRealTuple K D mode n X Y r fresh i).mode = (stagesRealTuple K D mode n X Y r fresh j).mode) ∧
    (∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T →
      (stagesRealTuple K D mode n X Y r fresh i).x T = (stagesRealTuple K D mode n X Y r fresh j).x T ∧
      (stagesRealTuple K D mode n X Y r fresh i).y T = (stagesRealTuple K D mode n X Y r fresh j).y T ∧
      (stagesRealTuple K D mode n X Y r fresh i).z T = (stagesRealTuple K D mode n X Y r fresh j).z T) ∧
    (stagesAgreeAt D (fun i => B i ++ [stagesRealTuple K D mode n X Y r fresh i]) N →
      mainDifference K D mode n Xs Ys r =
        stagesRealDiff D (fun i => B i ++ [stagesRealTuple K D mode n X Y r fresh i]) N) := by
  refine ⟨fun i hi => ?_, fun i _ j _ => ⟨rfl, rfl⟩, fun i hi j hj T hT hiT hjT => ?_, fun hag => ?_⟩
  · unfold stagesSimTuple stagesKnownTuple stagesRealTuple
    dsimp only
    congr 1
    · funext T g
      unfold knownView
      split_ifs with h
      · rw [hX1 i hi T h.1]
      · rfl
    · funext T g
      unfold knownView
      split_ifs with h
      · rw [hY1 i hi T h.1]
      · rfl
    · exact (mainKnownMult_matches K D mode n r fresh _ i).symm
  · refine ⟨hX2 i hi j hj T hT hiT hjT, hY2 i hi j hj T hT hiT hjT, ?_⟩
    unfold stagesRealTuple
    dsimp only
    funext g
    simp only [mainFmultOut, hiT, hjT, true_and, main_unknown_offset_zero K D mode T hT]
  · refine stages_diff_correct K D mode n X Y Xs Ys r (mainMultBase D n r.2.1 fresh) _ N
      (fun i hi => ?_) hXb hYb (fun i T hi hT _ g _ => by rw [hX1 i hi T hT])
      (fun i T hi hT _ g _ => by rw [hY1 i hi T hT]) hag
    rw [← hlen i hi, stages_getElem?_append_eq]
    rfl

/-- The leak of `F_multVerify` on tuples whose hidden copies agree is the leak of the simulator. -/
theorem stages_verifyLeak (D : C.Coalition) (views sviews : C.Party → List (Tuple C)) (diffs : List (ℕ → Bit))
    (hlen : ∀ i ∉ D.1, (views i).length = diffs.length)
    (hshape : ∀ i ∉ D.1, ∀ j ∉ D.1, (views i).map (fun τ => (τ.count, τ.mode)) =
      (views j).map (fun τ => (τ.count, τ.mode)))
    (hknown : ∀ i ∉ D.1, sviews i = (views i).map (stagesKnownTuple D))
    (hhidden : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ m : ℕ,
      ((views i)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)) =
        ((views j)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)))
    (hdiff : ∀ m (hm : m < diffs.length), stagesAgreeAt D views m → diffs[m] = stagesRealDiff D views m) :
    mainVerifyLeak D (stagesHonest D views) = (stagesHonest D sviews,
      if mainKnownAgree D sviews then diffs else [],
      decide (mainKnownAgree D sviews ∧ ∀ d ∈ diffs, ∀ g, d g = 0)) := by
  have hcount : (firstInput (stagesHonest D views)).length = diffs.length :=
    stages_firstInput D views (fun l => l.length = diffs.length) hlen
  unfold mainVerifyLeak
  simp only [hcount]
  show (_, if stagesRealAgree D views diffs.length then _ else _,
    decide (stagesRealAgree D views diffs.length ∧ _)) = _
  have hR : stagesRealAgree D views diffs.length ↔ mainKnownAgree D sviews :=
    (stages_realAgree_iff D views _ hlen hshape).trans (stages_knownAgree_iff D views sviews _ hlen hshape hknown hhidden)
  have hL : stagesRealAgree D views diffs.length →
      List.map (fun (τ : Tuple C) g => if g < τ.count then shareValue τ.z g - shareValue τ.x g * shareValue τ.y g
        else 0) (List.map (tupleAt (stagesHonest D views)) (List.range diffs.length)) = diffs := by
    intro hag
    have hag' := (stages_realAgree_iff D views _ hlen hshape).1 hag
    refine List.ext_getElem (by simp) fun m h₁ h₂ => ?_
    rw [hdiff m h₂ (hag' m h₂)]
    simp only [List.getElem_map, List.getElem_range]
    rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    by_cases hi : i ∈ D.1
    · simp [stagesHonest, hi]
    · simp only [stagesHonest, hi, if_false, Option.map_some, hknown i hi]
      rfl
  · by_cases hag : stagesRealAgree D views diffs.length
    · simp only [if_pos hag, if_pos (hR.1 hag), hL hag]
    · simp only [if_neg hag, if_neg (mt hR.2 hag)]
  · simp only
    rw [decide_eq_decide]
    constructor
    · rintro ⟨hag, hp⟩
      refine ⟨hR.1 hag, fun d hd g => ?_⟩
      rw [← hL hag] at hd
      obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hd
      dsimp only
      split_ifs with hg
      · rw [hp τ hτ g hg, sub_self]
      · rfl
    · rintro ⟨hag, hp⟩
      refine ⟨hR.2 hag, fun τ hτ g hg => ?_⟩
      have := hp _ (by rw [← hL (hR.2 hag)]; exact List.mem_map_of_mem hτ) g
      simp only [if_pos hg] at this
      exact sub_eq_zero.1 this

/-- The inputs of the honest operators, empty at the corrupt operators. -/
def stagesX (D : C.Coalition) (x : C.Party → MainInput C) : C.Party → MainInput C :=
  fun i => if i ∈ D.1 then [] else x i

/-- The real state `p` and the simulator data after `l` layers. -/
structure StagesInv (D : C.Coalition) (jobs : List Circuit) (x : C.Party → MainInput C) (l : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (data : MainSimData C) : Prop where
  len_wires : ∀ i ∉ D.1, (p i).1.length = (data.wires i).length
  len_jobs : ∀ i ∉ D.1, (p i).1.length = jobs.length
  known_wires : ∀ i ∉ D.1, ∀ T, KnownTo D.1 T → ∀ k,
    ((p i).1.getD k fun _ => []) T = ((data.wires i).getD k fun _ => []) T
  hidden_wires : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ k,
    ((p i).1.getD k fun _ => []) T = ((p j).1.getD k fun _ => []) T
  tuples : ∀ i ∉ D.1, data.tuples i = (p i).2.map (stagesKnownTuple D)
  len_tuples : ∀ i ∉ D.1, (p i).2.length = data.differences.length
  shape : ∀ i ∉ D.1, ∀ j ∉ D.1, (p i).2.map (fun τ => (τ.count, τ.mode)) = (p j).2.map (fun τ => (τ.count, τ.mode))
  hidden_tuples : ∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ m : ℕ,
    ((p i).2[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)) =
      ((p j).2[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T))
  diff : ∀ m (hm : m < data.differences.length), stagesAgreeAt D (fun i => (p i).2) m →
    data.differences[m] = stagesRealDiff D (fun i => (p i).2) m
  correct : (∀ m < data.differences.length, stagesAgreeAt D (fun i => (p i).2) m ∧
      stagesProductAt D (fun i => (p i).2) m) →
    ∃ W Ts, LayerInv jobs (stagesX D x) l (fun _ => (W, Ts)) W Ts ∧
      ∀ i ∉ D.1, ∀ T, i ∈ C.holders T → ∀ k, ((p i).1.getD k fun _ => []) T = (W.getD k fun _ => []) T

variable (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (mode : ReshareMode) (jobs : List Circuit)

/-- The simulator data after layer `l`. -/
def stagesSimNext (l : ℕ) (data : MainSimData C) (r : MainMultReply C) : MainSimData C where
  wires := fun i => appendLayer jobs l (data.wires i)
    (mainKnownMult K D mode (gatesAt jobs l).length r i)
  tuples := fun i => data.tuples i ++ [⟨knownView D.1 (gatesAt jobs l).length (layerX K jobs l (data.wires i)),
    knownView D.1 (gatesAt jobs l).length (layerY K jobs l (data.wires i)),
    mainKnownMult K D mode (gatesAt jobs l).length r i, (gatesAt jobs l).length, mode⟩]
  differences := data.differences ++ [mainDifference K D mode (gatesAt jobs l).length
    (fun i => layerX K jobs l (data.wires i)) (fun i => layerY K jobs l (data.wires i)) r]

/-- The rest of the simulator after the layers. -/
def stagesSimK (outputs : List (List Bit)) (a : A.State × Option (MainSimData C)) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → Bit))) :=
  match a.2 with
  | none => pure (a.1, fun _ => none)
  | some data => mainSimTailX K D A jobs a.1 data outputs

theorem stages_simLayers_cons (l : ℕ) (ls : List ℕ) (st : A.State) (data : MainSimData C) :
    mainSimLayers K D A mode jobs (l :: ls) st data =
      A.answer st (.inl (.inl (mainMultLeak D (gatesAt jobs l).length (fun i => layerX K jobs l (data.wires i))
        (fun i => layerY K jobs l (data.wires i))))) >>= fun a =>
      if ¬ mainAllReceive D (stagesReplyL a.2).2.2.2 then pure (a.1, none) else
      mainSimLayers K D A mode jobs ls a.1 (stagesSimNext K D mode jobs l data (stagesReplyL a.2)) := by
  simp only [mainSimLayers, mainSimLayer, bind_assoc]
  refine bind_congr fun a => ?_
  rcases a with ⟨st', (r | r) | r⟩ <;>
  · dsimp only [stagesReplyL]
    split_ifs <;> rfl

theorem stages_multLeak_eq (x : C.Party → MainInput C) (l : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (data : MainSimData C) {l' : ℕ} (hinv : StagesInv D jobs x l' p data) :
    mainMultLeak D (gatesAt jobs l).length (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) =
      mainMultLeak D (gatesAt jobs l).length (fun i => layerX K jobs l (data.wires i))
        (fun i => layerY K jobs l (data.wires i)) := by
  unfold mainMultLeak
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, if_false]
    congr 2
    · funext T g
      unfold knownView
      split_ifs with hT
      · rw [layerX_congr K jobs l _ _ T (hinv.known_wires i hi T hT.1)]
      · rfl
    · funext T g
      unfold knownView
      split_ifs with hT
      · rw [layerY_congr K jobs l _ _ T (hinv.known_wires i hi T hT.1)]
      · rfl

theorem stages_layerX_beyond (l : ℕ) (w : MainInput C) (T : C.Term) (g : ℕ) (hg : (gatesAt jobs l).length ≤ g) :
    layerX K jobs l w T g = 0 := by
  simp [layerX, List.getElem?_eq_none hg]

theorem stages_layerY_beyond (l : ℕ) (w : MainInput C) (T : C.Term) (g : ℕ) (hg : (gatesAt jobs l).length ≤ g) :
    layerY K jobs l w T g = 0 := by
  simp [layerY, List.getElem?_eq_none hg]

theorem stages_outputShares_beyond (w : MainInput C) (T : C.Term) (g : ℕ) (hg : (outputsOf jobs).length ≤ g) :
    outputShares K jobs w T g = 0 := by
  simp [outputShares, List.getElem?_eq_none hg]

theorem stages_fmultOut_known (n : ℕ) (X Y : C.Party → Shares C Bit) (r : MainMultReply C)
    (fresh : C.Term → Fin n → Bit) (i : C.Party) (T : C.Term) (hT : KnownTo D.1 T) :
    mainFmultOut K D mode n X Y r fresh i T = mainKnownMult K D mode n r i T := by
  funext g
  have hne : lackedTerm D.1 ≠ some T := fun h => main_lacked_unknown D T h hT
  simp only [mainFmultOut, mainKnownMult, mainMultBase, hT, true_and, if_neg hne, if_true]

theorem stages_fmultOut_hidden (n : ℕ) (X Y : C.Party → Shares C Bit) (r : MainMultReply C)
    (fresh : C.Term → Fin n → Bit) (i j : C.Party) (T : C.Term) (hT : ¬ KnownTo D.1 T)
    (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    mainFmultOut K D mode n X Y r fresh i T = mainFmultOut K D mode n X Y r fresh j T := by
  funext g
  simp only [mainFmultOut, hiT, hjT, true_and, main_unknown_offset_zero K D mode T hT]

theorem stages_newWires_congr (l k : ℕ) (z z' : Shares C Bit) (T : C.Term)
    (h : ∀ g < (gatesAt jobs l).length, z T g = z' T g) :
    newWires jobs l k z T = newWires jobs l k z' T := by
  unfold newWires
  refine List.map_congr_left fun q hq => ?_
  have hq' := (List.mem_filter.1 hq).1
  exact h q.2 (by simpa using (List.mem_zipIdx hq').2.1)

theorem stages_layerInv_const (x : C.Party → MainInput C) (l : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (W : MainInput C) (Ts : List (Tuple C))
    (h : LayerInv jobs x l p W Ts) : LayerInv jobs x l (fun _ => (W, Ts)) W Ts :=
  ⟨fun _ => h.length_W, h.length_W, fun _ _ _ _ => rfl, h.length_plain, h.sum_plain, fun _ => rfl,
    fun _ _ _ => ⟨fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl⟩, h.product⟩

/-- GS20: an accepted product layer keeps the honest wires a sharing of the plain wires. -/
theorem stages_layer_correct (x : C.Party → MainInput C) (l : ℕ) (wires : C.Party → MainInput C)
    (z : C.Party → Shares C Bit) (B : C.Party → List (Tuple C)) (N : ℕ) (W : MainInput C) (Ts : List (Tuple C))
    (hlen : ∀ i ∉ D.1, (B i).length = N)
    (hLI : LayerInv jobs (stagesX D x) l (fun _ => (W, Ts)) W Ts)
    (hW : ∀ i ∉ D.1, ∀ T, i ∈ C.holders T → ∀ k, ((wires i).getD k fun _ => []) T = (W.getD k fun _ => []) T)
    (hwlen : ∀ i ∉ D.1, (wires i).length = jobs.length)
    (hag : stagesAgreeAt D (fun i => B i ++ [⟨layerX K jobs l (wires i), layerY K jobs l (wires i), z i,
      (gatesAt jobs l).length, mode⟩]) N)
    (hpr : stagesProductAt D (fun i => B i ++ [⟨layerX K jobs l (wires i), layerY K jobs l (wires i), z i,
      (gatesAt jobs l).length, mode⟩]) N) :
    ∃ W' Ts', LayerInv jobs (stagesX D x) (l + 1) (fun _ => (W', Ts')) W' Ts' ∧
      ∀ i ∉ D.1, ∀ T, i ∈ C.holders T → ∀ k,
        ((appendLayer jobs l (wires i) (z i)).getD k fun _ => []) T = (W'.getD k fun _ => []) T := by
  have hview : ∀ i ∉ D.1, (B i ++ [⟨layerX K jobs l (wires i), layerY K jobs l (wires i), z i,
      (gatesAt jobs l).length, mode⟩])[N]? = some ⟨layerX K jobs l (wires i), layerY K jobs l (wires i), z i,
      (gatesAt jobs l).length, mode⟩ :=
    fun i hi => by rw [← hlen i hi]; exact stages_getElem?_append_eq _ _
  have hm : ∀ i ∉ D.1, N < (B i ++ [(⟨layerX K jobs l (wires i), layerY K jobs l (wires i), z i,
      (gatesAt jobs l).length, mode⟩ : Tuple C)]).length := fun i hi => by simp [hlen i hi]
  have hat : ∀ h ∉ D.1, stagesAt (fun i => B i ++ [⟨layerX K jobs l (wires i), layerY K jobs l (wires i), z i,
      (gatesAt jobs l).length, mode⟩]) h N = ⟨layerX K jobs l (wires h), layerY K jobs l (wires h), z h,
      (gatesAt jobs l).length, mode⟩ := fun h hh => by
    unfold stagesAt
    rw [hview h hh]
    rfl
  have hpair : ∀ T i j, i ∈ C.holders T → j ∈ C.holders T → i ∉ D.1 → j ∉ D.1 →
      ∀ g < (gatesAt jobs l).length, z i T g = z j T g := by
    intro T i j hi hj hiD hjD g hg
    have := hag T i hi j hj hiD hjD g (by rw [hview i hiD]; exact hg)
    rw [hview i hiD, hview j hjD] at this
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    exact this.2.2
  have hcount := stages_tupleAt_count' D (fun i => B i ++ [⟨layerX K jobs l (wires i), layerY K jobs l (wires i),
    z i, (gatesAt jobs l).length, mode⟩]) N (gatesAt jobs l).length fun i hi => by rw [hview i hi]; rfl
  -- the common product terms
  set zc : Shares C Bit := fun T g => if g < (gatesAt jobs l).length then z (mainRefHolder D T) T g else 0
    with hzc
  have hzW : ∀ g, ∑ T, zc T g = ∑ i, mulRep K (localContext i) (layerX K jobs l ((fun _ => (W, Ts)) i).1)
      (layerY K jobs l ((fun _ => (W, Ts)) i).1) g := by
    intro g
    rw [mulRep_views_sum K (fun _ => layerX K jobs l W) (fun _ => layerY K jobs l W) _ _ g
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)]
    rcases Nat.lt_or_ge g (gatesAt jobs l).length with hg | hg
    · have hp := hpr g (by rw [hcount]; exact hg)
      have hx : shareValue (tupleAt (stagesHonest D fun i => B i ++ [⟨layerX K jobs l (wires i),
          layerY K jobs l (wires i), z i, (gatesAt jobs l).length, mode⟩]) N).x g =
          shareValue (layerX K jobs l W) g := by
        unfold shareValue
        refine Finset.sum_congr rfl fun T _ => ?_
        obtain ⟨h, hhT, hhD, hxh⟩ := stages_tupleAt_x D _ N hm T
        rw [hxh, hat h hhD]
        exact congrFun (layerX_congr K jobs l _ _ T (hW h hhD T hhT)) g
      have hy : shareValue (tupleAt (stagesHonest D fun i => B i ++ [⟨layerX K jobs l (wires i),
          layerY K jobs l (wires i), z i, (gatesAt jobs l).length, mode⟩]) N).y g =
          shareValue (layerY K jobs l W) g := by
        unfold shareValue
        refine Finset.sum_congr rfl fun T _ => ?_
        obtain ⟨h, hhT, hhD, hyh⟩ := stages_tupleAt_y D _ N hm T
        rw [hyh, hat h hhD]
        exact congrFun (layerY_congr K jobs l _ _ T (hW h hhD T hhT)) g
      have hzz : shareValue (tupleAt (stagesHonest D fun i => B i ++ [⟨layerX K jobs l (wires i),
          layerY K jobs l (wires i), z i, (gatesAt jobs l).length, mode⟩]) N).z g = ∑ T, zc T g := by
        unfold shareValue
        refine Finset.sum_congr rfl fun T _ => ?_
        obtain ⟨h, hhT, hhD, hzh⟩ := stages_tupleAt_z D _ N hm T
        rw [hzh, hat h hhD]
        have href := mainRefHolder_spec D T
        simp only [hzc, if_pos hg]
        exact hpair T h (mainRefHolder D T) hhT href.1 hhD href.2 g hg
      rw [← hzz, hp, hx, hy]
    · have h0 : shareValue (layerX K jobs l W) g = 0 := by
        unfold shareValue
        exact Finset.sum_eq_zero fun T _ => stages_layerX_beyond K jobs l W T g hg
      rw [h0, zero_mul]
      exact Finset.sum_eq_zero fun T _ => by simp [hzc, Nat.not_lt.2 hg]
  have hstep := layerInv_step K jobs (stagesX D x) mode l (fun _ => (W, Ts)) W Ts hLI zc hzW
  refine ⟨_, _, stages_layerInv_const jobs (stagesX D x) (l + 1) _ _ _ hstep, fun i hi T hiT k => ?_⟩
  rw [getD_appendLayer, getD_appendLayer, hwlen i hi, hLI.length_W]
  split_ifs
  · dsimp only
    rw [hW i hi T hiT k]
    congr 1
    refine stages_newWires_congr jobs l k _ _ T fun g hg => ?_
    simp only [hzc, if_pos hg]
    have href := mainRefHolder_spec D T
    exact hpair T i (mainRefHolder D T) hiT href.1 hi href.2 g hg
  · rfl

theorem stages_inv_step (x : C.Party → MainInput C) (l : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (data : MainSimData C) (hinv : StagesInv D jobs x l p data) (r : MainMultReply C)
    (fresh : C.Term → Fin (gatesAt jobs l).length → Bit) :
    StagesInv D jobs x (l + 1) (stagesNext K mode jobs l p (mainFmultOut K D mode (gatesAt jobs l).length
      (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) r fresh))
      (stagesSimNext K D mode jobs l data r) := by
  obtain ⟨n1, n2, n3, n4⟩ := stages_new_tuple K D mode (gatesAt jobs l).length
    (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1)
    (fun i => layerX K jobs l (data.wires i)) (fun i => layerY K jobs l (data.wires i)) r fresh
    (fun i => (p i).2) data.differences.length hinv.len_tuples
    (fun i hi T hT => layerX_congr K jobs l _ _ T (hinv.known_wires i hi T hT))
    (fun i hi T hT => layerY_congr K jobs l _ _ T (hinv.known_wires i hi T hT))
    (fun i hi j hj T hT hiT hjT => layerX_congr K jobs l _ _ T (hinv.hidden_wires i hi j hj T hT hiT hjT))
    (fun i hi j hj T hT hiT hjT => layerY_congr K jobs l _ _ T (hinv.hidden_wires i hi j hj T hT hiT hjT))
    (fun i _ j _ T _ _ g hg => by
      rw [stages_layerX_beyond K jobs l _ T g hg, stages_layerX_beyond K jobs l _ T g hg])
    (fun i _ j _ T _ _ g hg => by
      rw [stages_layerY_beyond K jobs l _ T g hg, stages_layerY_beyond K jobs l _ T g hg])
  obtain ⟨a1, a2, a3, a4, a5⟩ := stages_append_hyps D (fun i => (p i).2) data.tuples data.differences _ _ _
    hinv.len_tuples hinv.shape hinv.tuples hinv.hidden_tuples hinv.diff n1 n2 n3 n4
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi T hT k => ?_, fun i hi j hj T hT hiT hjT k => ?_,
    a3, a1, a2, a4, a5, fun hall => ?_⟩
  · simp only [stagesNext, stagesSimNext, length_appendLayer, hinv.len_wires i hi]
  · simp only [stagesNext, length_appendLayer, hinv.len_jobs i hi]
  · simp only [stagesNext, stagesSimNext]
    exact main_appendLayer_known D jobs l _ _ _ _ (hinv.len_wires i hi) (hinv.known_wires i hi)
      (fun T hT => stages_fmultOut_known K D mode _ _ _ r fresh i T hT) T hT k
  · simp only [stagesNext]
    rw [getD_appendLayer, getD_appendLayer, hinv.len_jobs i hi, hinv.len_jobs j hj]
    split_ifs
    · dsimp only
      rw [hinv.hidden_wires i hi j hj T hT hiT hjT k, stages_newWires_congr jobs l k _ _ T
        (fun g _ => congrFun (stages_fmultOut_hidden K D mode _ _ _ r fresh i j T hT hiT hjT) g)]
    · rfl
  · -- the names of the new layer
    obtain ⟨z, hz⟩ : ∃ z, z = mainFmultOut K D mode (gatesAt jobs l).length
        (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) r fresh := ⟨_, rfl⟩
    have hN : (stagesSimNext K D mode jobs l data r).differences.length = data.differences.length + 1 := by
      simp [stagesSimNext]
    have hall' : ∀ m < data.differences.length + 1,
        stagesAgreeAt D (fun i => (p i).2 ++ [stagesRealTuple K D mode (gatesAt jobs l).length
          (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) r fresh i]) m ∧
        stagesProductAt D (fun i => (p i).2 ++ [stagesRealTuple K D mode (gatesAt jobs l).length
          (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) r fresh i]) m :=
      fun m hm => hall m (by rw [hN]; exact hm)
    -- the earlier tuples give the plain wires
    obtain ⟨W, Ts, hLI, hW⟩ := hinv.correct fun m hm => by
      refine ⟨(stages_agreeAt_append D (fun i => (p i).2) _ _ m hinv.len_tuples hm).1 (hall' m (by omega)).1, ?_⟩
      have := (hall' m (by omega)).2
      unfold stagesProductAt at this ⊢
      rwa [stages_tupleAt_congr D _ (fun i => (p i).2) m fun i hi =>
        stages_getElem?_append_lt _ _ _ (by rw [hinv.len_tuples i hi]; exact hm)] at this
    subst hz
    exact stages_layer_correct K D mode jobs x l (fun i => (p i).1) _ (fun i => (p i).2)
      data.differences.length W Ts hinv.len_tuples hLI hW hinv.len_jobs
      (hall' _ (by omega)).1 (hall' _ (by omega)).2

/-- The tuples of the simulator at `F_multVerify`. -/
def stagesSimTuples (data : MainSimData C) (r : MainMultReply C) : C.Party → List (Tuple C) := fun i =>
  data.tuples i ++ [⟨knownView D.1 (outputsOf jobs).length (outputShares K jobs (data.wires i)),
    knownView D.1 (outputsOf jobs).length (one K), mainKnownMult K D .peer (outputsOf jobs).length r i,
    (outputsOf jobs).length, .peer⟩]

/-- The differences of the simulator at `F_multVerify`. -/
def stagesSimDiffs (data : MainSimData C) (r : MainMultReply C) : List (ℕ → Bit) :=
  data.differences ++ [mainDifference K D .peer (outputsOf jobs).length
    (fun i => outputShares K jobs (data.wires i)) (fun _ => one K) r]

/-- The leak of the simulator at `F_multVerify`. -/
def stagesSimLeak (data : MainSimData C) (r : MainMultReply C) :
    (C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool :=
  (stagesHonest D (stagesSimTuples K D jobs data r),
    if mainKnownAgree D (stagesSimTuples K D jobs data r) then stagesSimDiffs K D jobs data r else [],
    decide (mainKnownAgree D (stagesSimTuples K D jobs data r) ∧ ∀ d ∈ stagesSimDiffs K D jobs data r, ∀ g, d g = 0))

theorem stages_simTail_eq (st : A.State) (data : MainSimData C) (outputs : List (List Bit)) :
    mainSimTailX K D A jobs st data outputs =
      A.answer st (.inl (.inr (mainMultLeak D (outputsOf jobs).length (fun i => outputShares K jobs (data.wires i))
        (fun _ => one K)))) >>= fun a =>
      if ¬ mainAllReceive D (stagesReplyR a.2).2.2.2 then pure (a.1, fun _ => none) else
      A.answer a.1 (.inr (stagesSimLeak K D jobs data (stagesReplyR a.2))) >>= fun b =>
      if ¬ (stagesSimLeak K D jobs data (stagesReplyR a.2)).2.2 = true then pure (b.1, fun _ => none) else
      mainSimOpenX K D A jobs b.1 (stagesReplyV b.2)
        (mainKnownMult K D .peer (outputsOf jobs).length (stagesReplyR a.2)) outputs := by
  unfold mainSimTailX
  simp only [pure_bind]
  refine bind_congr fun a => ?_
  rcases a with ⟨st', (r | r) | r⟩
  all_goals
    dsimp only [stagesReplyR]
    congr 1

theorem stages_rerandLeak_eq (x : C.Party → MainInput C) (p : C.Party → MainInput C × List (Tuple C))
    (data : MainSimData C) {l' : ℕ} (hinv : StagesInv D jobs x l' p data) :
    mainMultLeak D (outputsOf jobs).length (fun i => outputShares K jobs (p i).1) (fun _ => one K) =
      mainMultLeak D (outputsOf jobs).length (fun i => outputShares K jobs (data.wires i)) (fun _ => one K) := by
  unfold mainMultLeak
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, if_false]
    congr 2
    funext T g
    unfold knownView
    split_ifs with hT
    · rw [outputShares_congr K jobs _ _ T (hinv.known_wires i hi T hT.1)]
    · rfl

theorem stages_tail_hyps (x : C.Party → MainInput C) (p : C.Party → MainInput C × List (Tuple C))
    (data : MainSimData C) {l' : ℕ} (hinv : StagesInv D jobs x l' p data) (r : MainMultReply C)
    (fresh : C.Term → Fin (outputsOf jobs).length → Bit) :
    let views := fun i => (p i).2 ++ [stagesRealTuple K D .peer (outputsOf jobs).length
      (fun i => outputShares K jobs (p i).1) (fun _ => one K) r fresh i]
    (∀ i ∉ D.1, (views i).length = (stagesSimDiffs K D jobs data r).length) ∧
    (∀ i ∉ D.1, ∀ j ∉ D.1, (views i).map (fun τ => (τ.count, τ.mode)) = (views j).map (fun τ => (τ.count, τ.mode))) ∧
    (∀ i ∉ D.1, stagesSimTuples K D jobs data r i = (views i).map (stagesKnownTuple D)) ∧
    (∀ i ∉ D.1, ∀ j ∉ D.1, ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → ∀ m : ℕ,
      ((views i)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T)) =
        ((views j)[m]?).map (fun (τ : Tuple C) => (τ.x T, τ.y T, τ.z T))) ∧
    (∀ m (hm : m < (stagesSimDiffs K D jobs data r).length), stagesAgreeAt D views m →
      (stagesSimDiffs K D jobs data r)[m] = stagesRealDiff D views m) := by
  intro views
  obtain ⟨n1, n2, n3, n4⟩ := stages_new_tuple K D .peer (outputsOf jobs).length
    (fun i => outputShares K jobs (p i).1) (fun _ => one K) (fun i => outputShares K jobs (data.wires i))
    (fun _ => one K) r fresh (fun i => (p i).2) data.differences.length hinv.len_tuples
    (fun i hi T hT => outputShares_congr K jobs _ _ T (hinv.known_wires i hi T hT))
    (fun _ _ _ _ => rfl)
    (fun i hi j hj T hT hiT hjT => outputShares_congr K jobs _ _ T (hinv.hidden_wires i hi j hj T hT hiT hjT))
    (fun _ _ _ _ _ _ _ _ => rfl)
    (fun i _ j _ T _ _ g hg => by
      rw [stages_outputShares_beyond K jobs _ T g hg, stages_outputShares_beyond K jobs _ T g hg])
    (fun _ _ _ _ _ _ _ _ _ => rfl)
  exact stages_append_hyps D (fun i => (p i).2) data.tuples data.differences _ _ _ hinv.len_tuples
    hinv.shape hinv.tuples hinv.hidden_tuples hinv.diff n1 n2 n3 n4

theorem stages_tailLeak_eq (x : C.Party → MainInput C) (p : C.Party → MainInput C × List (Tuple C))
    (data : MainSimData C) (hinv : StagesInv D jobs x (depth jobs) p data) (r : MainMultReply C)
    (fresh : C.Term → Fin (outputsOf jobs).length → Bit) :
    mainVerifyLeak D (fun i => if i ∈ D.1 then none else
      some (stagesTuples K jobs (p i) (mainFmultOut K D .peer (outputsOf jobs).length
        (fun i => outputShares K jobs (p i).1) (fun _ => one K) r fresh i))) =
      stagesSimLeak K D jobs data r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stages_tail_hyps K D jobs x p data hinv r fresh
  exact stages_verifyLeak D _ _ _ h1 h2 h3 h4 h5

theorem stages_mainOpenWith_congr (st : A.State) (R : Finset C.Party) (n : ℕ) (vr vr' : C.Party → Shares C Bit)
    (h : ∀ i ∉ D.1, vr i = vr' i) :
    mainOpenWith K D A st R n vr = mainOpenWith K D A st R n vr' := by
  have hinbox : ∀ ds sent i, mainOpenInbox K D R n vr ds sent i = mainOpenInbox K D R n vr' ds sent i := by
    intro ds sent i
    funext k
    unfold mainOpenInbox
    by_cases hk : k ∈ D.1
    · simp [hk]
    · simp [hk, h k hk]
  have hone : ∀ ds sent i, mainOpenOne K D R n vr ds sent i = mainOpenOne K D R n vr' ds sent i := by
    intro ds sent i
    unfold mainOpenOne
    simp only [hinbox]
    by_cases hi : i ∉ D.1 ∧ i ∈ R
    · simp only [hi, h i hi.1]
    · simp only [hi, not_false_eq_true, if_true]
  unfold mainOpenWith
  have hseq : (fun i => if i ∉ D.1 ∧ i ∈ R then mainCopyHashes (vr i) n else pure []) =
      fun i => if i ∉ D.1 ∧ i ∈ R then mainCopyHashes (vr' i) n else pure [] := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ R
    · simp only [hi, h i hi.1]
    · rw [if_neg hi, if_neg hi]
  rw [hseq]
  refine bind_congr fun ds => ?_
  by_cases hex : ∃ i, i ∉ D.1 ∧ i ∈ R
  · rw [if_neg (not_not.2 hex), if_neg (not_not.2 hex)]
    have hout : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ R then repOutbox K i (vr i) n (ds i) c else none) =
        fun c i => if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ R then repOutbox K i (vr' i) n (ds i) c else none := by
      funext c i
      by_cases hi : c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ R
      · simp only [hi, h i hi.2.1]
      · rw [if_neg hi, if_neg hi]
    rw [hout]
    refine bind_congr fun q => ?_
    rw [show mainOpenOne K D R n vr ds q.2 = mainOpenOne K D R n vr' ds q.2 from funext (hone ds q.2)]
  · rw [if_pos hex, if_pos hex]

theorem stages_assemble_flatten : ∀ (jobs : List Circuit) (V : ℕ → Bit) (g : ℕ),
    g < (jobs.map (·.outputs.length)).sum → (assemble jobs V).flatten.getD g 0 = V g
  | [], V, g, hg => by simp at hg
  | j :: js, V, g, hg => by
    rw [assemble_cons, List.flatten_cons]
    rcases Nat.lt_or_ge g j.outputs.length with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [vector]; exact h)]
      simp [vector, List.getElem?_range h]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [vector]; exact h)]
      have := stages_assemble_flatten js (fun g => V (j.outputs.length + g)) (g - j.outputs.length)
        (by simp at hg; omega)
      rw [List.getD_eq_getElem?_getD] at this
      simp only [vector, List.length_map, List.length_range] at this ⊢
      rw [this]
      congr 1
      omega

theorem stages_mainOutputs_eq (D : C.Coalition) (jobs : List Circuit) (x : C.Party → MainInput C) :
    mainOutputs jobs (stagesX D x) = (mainIdealLeak D jobs x).2 := by
  unfold mainOutputs mainIdealLeak
  dsimp only
  refine List.map_congr_left fun q _ => ?_
  congr 3
  funext i
  by_cases hi : i ∈ D.1 <;> simp [stagesX, hi]

/-- After acceptance, the copies of `Rerand` are `mainRebuild` of the outputs. -/
theorem stages_rebuild (n : ℕ) (r : MainMultReply C) (fresh : C.Term → Fin n → Bit) (target : ℕ → Bit)
    (outputs : List (List Bit))
    (hagree : ∀ i ∉ D.1, ∀ T, i ∈ C.holders T → ∀ g < n,
      stagesMultZ K D .peer n (mainMultBase D n r.2.1 fresh) target r i T g =
        stagesMultZ K D .peer n (mainMultBase D n r.2.1 fresh) target r (mainRefHolder D T) T g)
    (hsum : ∀ g < n, ∑ T, stagesMultZ K D .peer n (mainMultBase D n r.2.1 fresh) target r (mainRefHolder D T) T g =
      outputs.flatten.getD g 0) :
    ∀ i ∉ D.1, stagesMultZ K D .peer n (mainMultBase D n r.2.1 fresh) target r i =
      mainOpenVr n (mainRebuild D n (mainKnownMult K D .peer n r) outputs fresh) i := by
  -- the offset of a copy
  set off : C.Party → C.Term → ℕ → Bit := fun i T g =>
    if ∃ j ∈ D.1, filler K .peer T g = some j then r.2.2.1 i T g else 0 with hoff
  have hoff0 : ∀ i T g, ¬ KnownTo D.1 T → off i T g = 0 := fun i T g hT =>
    main_unknown_offset_zero K D .peer T hT g r.2.2.1 i
  have hZ : ∀ i T g, i ∈ C.holders T → g < n →
      stagesMultZ K D .peer n (mainMultBase D n r.2.1 fresh) target r i T g =
        mainMultSharing D (mainMultBase D n r.2.1 fresh) target T g + off i T g := fun i T g hi hg => by
    simp [stagesMultZ, hi, hg, hoff]
  -- the base of the simulator is the base of the real run plus the offsets
  have hbase : ∀ T g, g < n → mainMultBase D n (fun T => mainKnownMult K D .peer n r (mainRefHolder D T) T) fresh T g =
      mainMultBase D n r.2.1 fresh T g + off (mainRefHolder D T) T g := fun T g hg => by
    by_cases hT : KnownTo D.1 T
    · simp [mainMultBase, mainKnownMult, hT, (mainRefHolder_spec D T).1, hg, hoff]
    · simp [mainMultBase, hT, hoff0 _ T g hT]
  intro i hi
  funext T g
  unfold mainOpenVr
  by_cases hig : i ∈ C.holders T ∧ g < n
  · rw [if_pos hig, hZ i T g hig.1 hig.2]
    have href := mainRefHolder_spec D T
    unfold mainRebuild mainMultSharing
    by_cases hlack : lackedTerm D.1 = some T
    · have hT : ¬ KnownTo D.1 T := main_lacked_unknown D T hlack
      rw [if_pos hlack, if_pos hlack, hoff0 i T g hT, add_zero]
      -- the target from the opened sum
      have hs := hsum g hig.2
      simp only [fun T' => hZ (mainRefHolder D T') T' g (mainRefHolder_spec D T').1 hig.2,
        Finset.sum_add_distrib] at hs
      rw [show (∑ x, mainMultSharing D (mainMultBase D n r.2.1 fresh) target x g) = target g from
        mainMultSharing_sum D _ target T hlack g] at hs
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T), hoff0 _ T g hT, zero_add] at hs
      rw [Finset.sum_congr rfl fun T' _ => hbase T' g hig.2, Finset.sum_add_distrib]
      show _ = outputs.flatten.getD g 0 - _
      rw [← hs]
      ring
    · rw [if_neg hlack, if_neg hlack, hbase T g hig.2]
      by_cases hT : KnownTo D.1 T
      · have h1 := hagree i hi T hig.1 g hig.2
        rw [hZ i T g hig.1 hig.2, hZ _ T g href.1 hig.2] at h1
        unfold mainMultSharing at h1
        rw [if_neg hlack] at h1
        exact h1
      · rw [hoff0 i T g hT, hoff0 _ T g hT]
  · rw [if_neg hig]
    unfold stagesMultZ
    rw [if_neg hig]

theorem stages_open_core (n : ℕ) (Xo : C.Party → Shares C Bit) (r : MainMultReply C)
    (fresh : C.Term → Fin n → Bit) (B : C.Party → List (Tuple C)) (N₀ : ℕ) (W : MainInput C)
    (outputs : List (List Bit)) (hlen : ∀ i ∉ D.1, (B i).length = N₀)
    (hag : stagesAgreeAt D (fun i => B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]) N₀)
    (hpr : stagesProductAt D (fun i => B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]) N₀)
    (hXW : ∀ i ∉ D.1, ∀ T, i ∈ C.holders T → Xo i T = outputShares K jobs W T)
    (hout : ∀ g < n, shareValue (outputShares K jobs W) g = outputs.flatten.getD g 0) :
    ∀ i ∉ D.1, mainFmultOut K D .peer n Xo (fun _ => one K) r fresh i =
      mainOpenVr n (mainRebuild D n (mainKnownMult K D .peer n r) outputs fresh) i := by
  have hview : ∀ i ∉ D.1, (B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i])[N₀]? =
      some (stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i) :=
    fun i hi => by rw [← hlen i hi]; exact stages_getElem?_append_eq _ _
  have hm : ∀ i ∉ D.1, N₀ < (B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]).length :=
    fun i hi => by simp [hlen i hi]
  have hpair : ∀ T i j, i ∈ C.holders T → j ∈ C.holders T → i ∉ D.1 → j ∉ D.1 → ∀ g < n,
      Xo i T g = Xo j T g ∧ mainFmultOut K D .peer n Xo (fun _ => one K) r fresh i T g =
        mainFmultOut K D .peer n Xo (fun _ => one K) r fresh j T g := by
    intro T i j hi hj hiD hjD g hg
    have := hag T i hi j hj hiD hjD g (by rw [hview i hiD]; exact hg)
    rw [hview i hiD, hview j hjD] at this
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, stagesRealTuple] at this
    exact ⟨this.1, this.2.2⟩
  have hcount := stages_tupleAt_count' D
    (fun i => B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]) N₀ n
    fun i hi => by rw [hview i hi]; rfl
  have hsum : ∀ g < n, ∑ T, mainFmultOut K D .peer n Xo (fun _ => one K) r fresh (mainRefHolder D T) T g =
      outputs.flatten.getD g 0 := by
    intro g hg
    have hp := hpr g (by rw [hcount]; exact hg)
    rw [← hout g hg]
    have hat : ∀ h ∉ D.1, stagesAt (fun i => B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i])
        h N₀ = stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh h := fun h hh => by
      unfold stagesAt
      rw [hview h hh]
      rfl
    have hy : shareValue (tupleAt (stagesHonest D fun i =>
        B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]) N₀).y g = 1 := by
      rw [← shareValue_one K g]
      unfold shareValue
      refine Finset.sum_congr rfl fun T _ => ?_
      obtain ⟨h, -, hhD, hyh⟩ := stages_tupleAt_y D _ N₀ hm T
      rw [hyh, hat h hhD]
      rfl
    have hx : shareValue (tupleAt (stagesHonest D fun i =>
        B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]) N₀).x g =
        shareValue (outputShares K jobs W) g := by
      unfold shareValue
      refine Finset.sum_congr rfl fun T _ => ?_
      obtain ⟨h, hhT, hhD, hxh⟩ := stages_tupleAt_x D _ N₀ hm T
      rw [hxh, hat h hhD]
      exact congrFun (hXW h hhD T hhT) g
    have hz : shareValue (tupleAt (stagesHonest D fun i =>
        B i ++ [stagesRealTuple K D .peer n Xo (fun _ => one K) r fresh i]) N₀).z g =
        ∑ T, mainFmultOut K D .peer n Xo (fun _ => one K) r fresh (mainRefHolder D T) T g := by
      unfold shareValue
      refine Finset.sum_congr rfl fun T _ => ?_
      obtain ⟨h, hhT, hhD, hzh⟩ := stages_tupleAt_z D _ N₀ hm T
      rw [hzh, hat h hhD]
      have href := mainRefHolder_spec D T
      exact (hpair T h (mainRefHolder D T) hhT href.1 hhD href.2 g hg).2
    rw [← hz, hp, hx, hy, mul_one]
  rw [stages_mainFmultOut_eq]
  intro i hi
  refine stages_rebuild K D n r fresh _ _ (fun i hi T hiT g hg => ?_) hsum i hi
  have href := mainRefHolder_spec D T
  exact (hpair T i (mainRefHolder D T) hiT href.1 hi href.2 g hg).2

theorem stages_open_vr (x : C.Party → MainInput C) (p : C.Party → MainInput C × List (Tuple C))
    (data : MainSimData C) (hinv : StagesInv D jobs x (depth jobs) p data) (r : MainMultReply C)
    (hacc : (stagesSimLeak K D jobs data r).2.2 = true) (fresh : C.Term → Fin (outputsOf jobs).length → Bit) :
    ∀ i ∉ D.1, mainFmultOut K D .peer (outputsOf jobs).length (fun i => outputShares K jobs (p i).1)
      (fun _ => one K) r fresh i =
      mainOpenVr (outputsOf jobs).length (mainRebuild D (outputsOf jobs).length
        (mainKnownMult K D .peer (outputsOf jobs).length r) (mainIdealLeak D jobs x).2 fresh) i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stages_tail_hyps K D jobs x p data hinv r fresh
  unfold stagesSimLeak at hacc
  simp only [decide_eq_true_eq] at hacc
  obtain ⟨hKA, hZ0⟩ := hacc
  have hAll := (stages_knownAgree_iff D _ _ _ h1 h2 h3 h4).2 hKA
  have hN : (stagesSimDiffs K D jobs data r).length = data.differences.length + 1 := by
    simp [stagesSimDiffs]
  have hProd : ∀ m (hm : m < (stagesSimDiffs K D jobs data r).length),
      stagesProductAt D (fun i => (p i).2 ++ [stagesRealTuple K D .peer (outputsOf jobs).length
        (fun i => outputShares K jobs (p i).1) (fun _ => one K) r fresh i]) m := by
    intro m hm g hg
    have hd := hZ0 _ (List.getElem_mem hm) g
    rw [h5 m hm (hAll m hm)] at hd
    unfold stagesRealDiff at hd
    rw [if_pos hg] at hd
    exact sub_eq_zero.1 hd
  obtain ⟨W, Ts, hLI, hW⟩ := hinv.correct fun m hm => by
    refine ⟨(stages_agreeAt_append D (fun i => (p i).2) _ _ m hinv.len_tuples hm).1 (hAll m (by omega)), ?_⟩
    have := hProd m (by omega)
    unfold stagesProductAt at this ⊢
    rwa [stages_tupleAt_congr D _ (fun i => (p i).2) m fun i hi =>
      stages_getElem?_append_lt _ _ _ (by rw [hinv.len_tuples i hi]; exact hm)] at this
  have hXW : ∀ i ∉ D.1, ∀ T, i ∈ C.holders T → outputShares K jobs (p i).1 T = outputShares K jobs W T :=
    fun i hi T hiT => outputShares_congr K jobs _ _ T (hW i hi T hiT)
  have hassemble := assemble_eq K jobs (stagesX D x) _ W Ts hLI
    (fun g => shareValue (outputShares K jobs W) g) (fun _ _ => rfl)
  rw [stages_mainOutputs_eq] at hassemble
  refine stages_open_core K D jobs _ _ r fresh (fun i => (p i).2) data.differences.length W _ hinv.len_tuples
    (hAll _ (by omega)) (hProd _ (by omega)) hXW fun g hg => ?_
  rw [← hassemble, stages_assemble_flatten jobs _ g (by rw [← main_outputsOf_length]; exact hg)]

theorem stages_sim_tail (x : C.Party → MainInput C) (prims : Primitives) (st : A.State)
    (p : C.Party → MainInput C × List (Tuple C)) (data : MainSimData C)
    (hinv : StagesInv D jobs x (depth jobs) p data) :
    SameRun prims (mainRealTail K D A jobs st p) (mainSimTailX K D A jobs st data (mainIdealLeak D jobs x).2) := by
  rw [stages_realTail_eq, stages_simTail_eq, stages_rerandLeak_eq K D jobs x p data hinv]
  refine SameRun.bind_right _ fun a => ?_
  by_cases hall : mainAllReceive D (stagesReplyR a.2).2.2.2
  · simp only [hall, not_true_eq_false, if_false]
    simp only [stages_tailLeak_eq K D jobs x p data hinv]
    refine (sameRun_swap prims _ _ _).trans (SameRun.bind_right _ fun b => ?_)
    by_cases hacc : (stagesSimLeak K D jobs data (stagesReplyR a.2)).2.2 = true
    · simp only [hacc, not_true_eq_false, if_false]
      rw [mainSimOpenX_eq_with]
      refine SameRun.bind_right _ fun fresh => SameRun.of_eq ?_
      exact stages_mainOpenWith_congr K D A _ _ _ _ _
        (stages_open_vr K D jobs x p data hinv (stagesReplyR a.2) hacc fresh)
    · simp only [hacc]
      exact stages_private_unused prims _ _
  · simp only [hall, not_false_eq_true, if_true]
    exact stages_private_unused prims _ _

theorem stages_sim_layers (x : C.Party → MainInput C) (prims : Primitives) :
    ∀ (k l : ℕ) (st : A.State) (p : C.Party → MainInput C × List (Tuple C)) (data : MainSimData C),
      StagesInv D jobs x l p data → l + k = depth jobs →
      SameRun prims (mainRealLayers K D A mode jobs (List.range' l k) st p >>= stagesRealK K D A jobs)
        (mainSimLayers K D A mode jobs (List.range' l k) st data >>=
          stagesSimK K D A jobs (mainIdealLeak D jobs x).2)
  | 0, l, st, p, data, hinv, hl => by
    simp only [List.range'_zero, mainRealLayers, mainSimLayers, pure_bind, stagesRealK, stagesSimK]
    exact stages_sim_tail K D A jobs x prims st p data (by simpa using hl ▸ hinv)
  | k + 1, l, st, p, data, hinv, hl => by
    rw [List.range'_succ, stages_realLayers_cons, stages_simLayers_cons, bind_assoc, bind_assoc,
      stages_multLeak_eq K D jobs x l p data hinv]
    refine SameRun.bind_right _ fun a => ?_
    by_cases hall : mainAllReceive D (stagesReplyL a.2).2.2.2
    · simp only [hall, not_true_eq_false, if_false, bind_assoc]
      refine (SameRun.bind_right _ fun fresh =>
        stages_sim_layers x prims k (l + 1) a.1 _ _ (stages_inv_step K D mode jobs x l p data hinv _ fresh)
          (by omega)).trans ?_
      exact stages_private_unused prims _ _
    · simp only [hall, not_false_eq_true, if_true, bind_assoc, pure_bind, stagesRealK, stagesSimK]
      exact stages_private_unused prims _ _

/-- The inputs with each corrupt holder filled from an honest holder. -/
def stagesFill (x : C.Party → MainInput C) : C.Party → MainInput C := fun i =>
  if i ∈ D.1 then (List.range jobs.length).map fun k T =>
    if i ∈ C.holders T then ((x (mainRefHolder D T)).getD k fun _ => []) T else []
  else x i

theorem stages_layerInv_transfer (x₁ x₂ : C.Party → MainInput C) (l : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (W : MainInput C) (Ts : List (Tuple C))
    (h : LayerInv jobs x₁ l p W Ts) (hx : ∀ k < jobs.length, plainInput x₁ k = plainInput x₂ k) :
    LayerInv jobs x₂ l p W Ts :=
  ⟨h.length_wires, h.length_W, h.agree, fun k hk T => by rw [← hx k hk]; exact h.length_plain k hk T,
    fun k hk g => by rw [← hx k hk]; exact h.sum_plain k hk g, h.length_tuples, h.agree_tuples, h.product⟩

theorem stages_fill_inputs (x : C.Party → MainInput C) (hx : MainInputs jobs D x) :
    MainInputs jobs noCoalition (stagesFill D jobs x) := by
  obtain ⟨widths, hwl, hwidth, hcons⟩ := hx
  have href := fun T => mainRefHolder_spec D T
  refine ⟨widths, hwl, fun i _ => ?_, fun k T i hi j hj _ _ => ?_⟩
  · by_cases hiD : i ∈ D.1
    · refine ⟨by simp [stagesFill, hiD], fun k hk T => ?_⟩
      simp only [stagesFill, hiD, if_true, List.getElem?_map, List.getElem?_range hk, Option.map_some,
        Option.getD_some]
      split_ifs with hiT
      · have := (hwidth _ (href T).2).2 k hk T
        rw [if_pos (href T).1] at this
        rw [List.getD_eq_getElem?_getD]
        exact this
      · rfl
    · simp only [stagesFill, hiD, if_false]
      exact hwidth i hiD
  · -- every holder has the value of the reference holder
    have hval : ∀ a ∈ C.holders T, (((stagesFill D jobs x a)[k]?).getD fun _ => []) T =
        (((x (mainRefHolder D T))[k]?).getD fun _ => []) T := by
      intro a ha
      by_cases haD : a ∈ D.1
      · simp only [stagesFill, haD, if_true, List.getElem?_map]
        rcases Nat.lt_or_ge k jobs.length with hk | hk
        · simp [List.getElem?_range hk, ha, List.getD_eq_getElem?_getD]
        · rw [List.getElem?_eq_none (by simpa using hk)]
          rw [List.getElem?_eq_none (by rw [(hwidth _ (href T).2).1]; exact hk)]
          rfl
      · simp only [stagesFill, haD, if_false]
        exact hcons k T a ha (mainRefHolder D T) (href T).1 (by simp [noCoalition]) (by simp [noCoalition])
    dsimp only
    rw [hval i hi, hval j hj]

theorem stages_plainInput_fill (x : C.Party → MainInput C) (hx : MainInputs jobs D x) (k : ℕ)
    (hk : k < jobs.length) : plainInput (stagesFill D jobs x) k = plainInput (stagesX D x) k := by
  obtain ⟨widths, -, hwidth, hcons⟩ := hx
  unfold plainInput
  congr 1
  funext T
  have href := mainRefHolder_spec D T
  -- the value of term `T`
  have hval : ∀ a, a ∉ D.1 → a ∈ C.holders T →
      ((x a).getD k fun _ => []) T = ((x (mainRefHolder D T)).getD k fun _ => []) T := fun a ha haT => by
    have := hcons k T a haT (mainRefHolder D T) href.1 (by simp [noCoalition]) (by simp [noCoalition])
    simpa [List.getD_eq_getElem?_getD] using this
  rw [reconstruct_of_agree _ T (((x (mainRefHolder D T)).getD k fun _ => []) T) fun a ha => ?_]
  · have hX : (fun i => (stagesX D x i)[k]?) =
        fun i => (stagesHonest D (fun i => (x i).getD k fun _ => []) i).map id := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [stagesX, stagesHonest, hi]
      · simp [stagesX, stagesHonest, hi, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [(hwidth i hi).1]; exact hk : k < (x i).length)]
    rw [hX]
    obtain ⟨h, hhT, hhD, hrec⟩ := stages_reconstruct D (fun i => (x i).getD k fun _ => []) id T
    rw [hrec]
    exact (hval h hhD hhT).symm
  · by_cases haD : a ∈ D.1
    · refine ⟨fun T' => if a ∈ C.holders T' then ((x (mainRefHolder D T')).getD k fun _ => []) T' else [],
        ?_, by simp [ha]⟩
      simp only [stagesFill, haD, if_true, List.getElem?_map, List.getElem?_range hk, Option.map_some]
    · refine ⟨(x a)[k]'(by rw [(hwidth a haD).1]; exact hk), ?_, ?_⟩
      · simp [stagesFill, haD]
      · rw [← hval a haD ha, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [(hwidth a haD).1]; exact hk)]
        rfl

theorem stages_inv_zero (x : C.Party → MainInput C) (hx : MainInputs jobs D x) :
    StagesInv D jobs x 0 (fun i => (x i, []))
      ⟨fun i => ((mainIdealLeak D jobs x).1 i).getD [], fun _ => [], []⟩ := by
  have hx' := hx
  obtain ⟨widths, -, hwidth, hcons⟩ := hx'
  have hwire : ∀ i ∉ D.1, ((mainIdealLeak D jobs x).1 i).getD [] =
      (x i).map fun v T => if KnownTo D.1 T then v T else [] := fun i hi => by
    simp [mainIdealLeak, hi]
  refine ⟨fun i hi => ?_, fun i hi => (hwidth i hi).1, fun i hi T hT k => ?_,
    fun i hi j hj T _ hiT hjT k => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ _ _ => rfl, fun m hm => absurd hm (by simp), fun _ => ?_⟩
  · simp [hwire i hi]
  · dsimp only
    rw [hwire i hi]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (x i)[k]? with _ | v
    · simp
    · simp [hT]
  · have := hcons k T i hiT j hjT (by simp [noCoalition]) (by simp [noCoalition])
    simpa [List.getD_eq_getElem?_getD] using this
  · have h0 := layerInv_zero jobs (stagesFill D jobs x) (stages_fill_inputs D jobs x hx)
    have h1 := stages_layerInv_transfer jobs _ (stagesX D x) 0 _ _ _ h0
      (fun k hk => stages_plainInput_fill D jobs x hx k hk)
    refine ⟨_, _, stages_layerInv_const jobs _ 0 _ _ _ h1, fun i hi T hiT k => ?_⟩
    have := h1.agree i T hiT k
    simpa [stagesFill, hi] using this

end Simulation

/-- GS20, Theorem 2: the real phase and the simulator give the same run. -/
theorem mainRealSim (prims : Primitives) (K : Constants C E) : MainRealSim prims K := by
  intro mode jobs D A x hx st
  have h := stages_sim_layers K D A mode jobs x prims (depth jobs) 0 st _ _ (stages_inv_zero D jobs x hx)
    (Nat.zero_add _)
  rw [← List.range_eq_range'] at h
  exact h

/-- `MainStatement` (GS20, Theorem 2). -/
theorem mainStatementFull {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (prims : Primitives) (K : Constants C E) : MainStatement prims K :=
  mainStatementProof prims K (mainEngineReal prims K) (mainRealSim prims K)

/-- info: 'ThresholdLeanXmssSecurity.mainEngineReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainEngineReal

/-- info: 'ThresholdLeanXmssSecurity.mainRealSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainRealSim

/-- info: 'ThresholdLeanXmssSecurity.mainStatementFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mainStatementFull

end ThresholdLeanXmssSecurity
