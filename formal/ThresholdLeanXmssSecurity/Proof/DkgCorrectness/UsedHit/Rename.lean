import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndWorld
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets
import ThresholdLeanXmssSecurity.Proof.CheckSecurity

/-!
# The renaming of the hidden keys in the programs of the operators

`renameComp D σ` changes the key of each honest call of `PRG` under a hidden name by `σ`.
`renameLocal`, `renameParty` and `renameRo` are the same renaming on the local oracles, on the oracles
of an operator and on `H` and `PRG`. `executePhase_rename` moves the renaming of the honest programs
through a phase of the network. `renameCtx` puts `σ` on each held hidden coordinate of the PRSS keys,
and the ceremony on the renamed keys is the renamed ceremony (`prssRandomness_rename`, `check_rename`,
`realRunJobs_rename`, `slotCeremony_rename`). `slotTree_congr` states that the ceremonies of a tree read
the fresh keys only below `treeSetups`. `slotProgram_rename` states that the program of a run of a tree
with the fresh keys `σ ∘ row` is the renamed program with the fresh keys `row`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The renaming on each oracle specification -/

section Maps

variable (D : C.Coalition) (σ : Equiv.Perm HashOutput)

/-- The renaming on the local oracles. -/
def renameLocal : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inr x) =>
      if Hidden D x.1 then OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr (x.1, σ x.2.1, x.2.2))))
      else OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))
  | t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)

/-- The renaming on the oracles of an operator. -/
def renameParty : QueryImpl (PartySpec C E RealSpec) (OracleComp (PartySpec C E RealSpec)) := fun t =>
  match t with
  | .inl (.inl (.inr (.inr x))) =>
      if Hidden D x.1 then
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr (.inr (x.1, σ x.2.1, x.2.2))))))
      else OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr (.inr x)))))
  | t => OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) t)

/-- The renaming on `H` and `PRG`. -/
def renameRo : QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun t =>
  match t with
  | .inr x =>
      if Hidden D x.1 then OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inr (x.1, σ x.2.1, x.2.2)))
      else OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inr x))
  | t => OracleComp.lift (OracleSpec.query (spec := RoSpec C) t)

theorem renameComp_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    renameComp D σ (free oa) = free (simulateQ (renameLocal D σ) oa) := by
  unfold renameComp free
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | q | x
  · simp [renameLocal, renameImpl]
  · simp [renameLocal, renameImpl]
  · by_cases h : Hidden D x.1 <;> simp [renameLocal, renameImpl, h]

theorem renameComp_bind {α β : Type} (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β) :
    renameComp D σ (oa >>= f) = renameComp D σ oa >>= fun a => renameComp D σ (f a) :=
  simulateQ_bind _ _ _

theorem renameComp_pure {α : Type} (a : α) : renameComp D σ (pure a : OracleComp (WorldSpec C) α) = pure a :=
  simulateQ_pure _ _

theorem renameComp_map {α β : Type} (g : α → β) (oa : OracleComp (WorldSpec C) α) :
    renameComp D σ (g <$> oa) = g <$> renameComp D σ oa :=
  simulateQ_map _ _ _

theorem renameComp_sequenceFin {α : Type} {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α) :
    renameComp D σ (OverPermutation.sequenceFin f) = OverPermutation.sequenceFin fun i => renameComp D σ (f i) :=
  simulateQ_sequenceFin _ f

/-- The renaming changes no computation on the counted copy. -/
theorem renameComp_counted {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    renameComp D σ (counted oa) = counted oa := by
  unfold renameComp counted
  rw [← QueryImpl.simulateQ_compose]
  congr 1

theorem renameComp_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    renameComp D σ ((worldRoles (C := C)).adversary oa) = (worldRoles (C := C)).adversary oa :=
  renameComp_counted D σ _

/-- The renaming changes no computation without an honest call of `PRG`. -/
theorem renameComp_eq_self {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : IsQueryBoundP oa (HonestIn (C := C) .stream) 0) : renameComp D σ oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact renameComp_pure D σ a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ HonestIn (C := C) .stream t := h.1.resolve_right (lt_irrefl 0)
    have hk : ∀ u, renameComp D σ (k u) = k u := fun u => ih u (by simpa only [ht, ↓reduceIte] using h.2 u)
    have hq : renameImpl D σ t = OracleComp.lift (OracleSpec.query (spec := WorldSpec C) t) := by
      rcases t with t | u | q | x
      · rfl
      · rfl
      · rfl
      · exact (ht (show InClass (C := C) .stream (.inr (.inr x)) from rfl)).elim
    simp only [renameComp, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map] at hk ⊢
    rw [hq]
    simp only [hk]

end Maps

/-! ## The renaming through a phase of the network -/

section Steps

variable (D : C.Coalition) (σ : Equiv.Perm HashOutput)

/-- A stopped program with its continuation renamed. -/
def renameStep {α : Type} : Step C E RealSpec α → Step C E RealSpec α
  | .done out => .done out
  | .wait outbox k => .wait outbox fun m => simulateQ (renameParty D σ) (k m)
  | .call input k => .call input fun r => simulateQ (renameParty D σ) (k r)

theorem advance_rename {α : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α)) :
    advance (simulateQ (renameParty D σ) oa) = renameStep D σ <$> simulateQ (renameLocal D σ) (advance oa) := by
  induction oa using OracleComp.inductionOn with
  | pure o => simp only [simulateQ_pure]; rfl
  | query_bind t k ih =>
    rcases t with (q | outbox) | input
    · have hl : ∀ {γ : Type} (g : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) γ),
          (liftM (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl q))) >>= g) =
            OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl q))) >>= g :=
        fun g => rfl
      rw [hl, advance_query_bind]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        map_bind]
      simp only [← ih]
      rcases q with n | q | x
      · rfl
      · rfl
      · by_cases h : Hidden D x.1
        · simp only [renameParty, renameLocal, h, ↓reduceIte]; rfl
        · simp only [renameParty, renameLocal, h, ↓reduceIte]; rfl
    · rfl
    · exact input.elim

@[simp] theorem renameStep_outbox {α : Type} (st : Step C E RealSpec α) :
    (renameStep D σ st).outbox = st.outbox := by cases st <;> rfl

@[simp] theorem renameStep_delivered {α : Type} (st : Step C E RealSpec α) :
    (renameStep D σ st).delivered = st.delivered := by rcases st with (_ | _) | _ | _ <;> rfl

@[simp] theorem renameStep_output {α : Type} (st : Step C E RealSpec α) :
    (renameStep D σ st).output = st.output := by cases st <;> rfl

@[simp] theorem renameStep_isDone {α : Type} (st : Step C E RealSpec α) :
    (renameStep D σ st).isDone = st.isDone := by cases st <;> rfl

theorem free_renameStep {α : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α)) :
    (worldRoles (C := C)).honest (advance (simulateQ (renameParty D σ) oa)) =
      renameStep D σ <$> renameComp D σ ((worldRoles (C := C)).honest (advance oa)) := by
  rw [advance_rename, worldRoles_honest_map]
  change _ = renameStep D σ <$> renameComp D σ (free (advance oa))
  rw [renameComp_free]
  rfl

theorem stepRound_rename {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (fun i => renameStep D σ (steps i)) =
      (fun r => (r.1, (fun i => renameStep D σ (r.2.1 i)), r.2.2)) <$>
        renameComp D σ (stepRound worldRoles D A noFunctionality state steps) := by
  have hno : ∀ (st : C.Party → Step C E RealSpec α),
      ¬ ((∃ i, i ∉ D.1 ∧ (st i).callInput.isSome) ∧ ∀ i, i ∉ D.1 → (st i).callInput.isSome ∨ (st i).isDone) :=
    fun st h => by
      obtain ⟨i, -, hi⟩ := h.1
      simp [ThresholdLeanXmssSecurity.callInput_real] at hi
  unfold stepRound
  rw [ite_eq_right_iff.mpr (fun h => (hno _ h).elim), ite_eq_right_iff.mpr (fun h => (hno _ h).elim)]
  simp only [renameStep_outbox, renameStep_delivered, renameComp_bind, renameComp_adversary, map_bind]
  refine bind_congr fun r => ?_
  rw [renameComp_sequenceFin]
  simp only [renameComp_pure, map_pure]
  rw [sequenceFin_map_bind (g := renameStep D σ) (k := fun steps' => pure (r.1, steps', r.2))]
  congr 2
  funext j
  cases hs : steps j with
  | done out => rw [renameComp_pure, map_pure]; rfl
  | wait outbox resume =>
    simp only [renameStep]
    split_ifs
    · rw [renameComp_pure, map_pure]; rfl
    · exact free_renameStep D σ _
  | call input resume => exact input.elim

theorem executeRounds_rename {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      executeRounds worldRoles D A noFunctionality fuel state (fun i => renameStep D σ (steps i)) =
        renameComp D σ (executeRounds worldRoles D A noFunctionality fuel state steps)
  | 0, state, steps => by simp only [executeRounds, renameStep_output, renameComp_pure]
  | fuel + 1, state, steps => by
    simp only [executeRounds, renameStep_isDone]
    split_ifs
    · rw [renameComp_pure]
      simp only [renameStep_output]
    · rw [stepRound_rename, renameComp_bind, bind_map_left]
      exact bind_congr fun r => executeRounds_rename A fuel r.1 r.2.1

/-- An operator program with the renaming of its hidden calls. -/
def renamePM {α : Type} (p : PartyM C E RealSpec α) : PartyM C E RealSpec α :=
  OptionT.mk (simulateQ (renameParty D σ) p.run)

theorem startSteps_rename {α : Type} (P : C.Party → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => renamePM D σ (P i)) =
      (fun st i => renameStep D σ (st i)) <$> renameComp D σ (startSteps worldRoles D P) := by
  unfold startSteps
  rw [renameComp_sequenceFin, map_eq_bind_pure_comp]
  simp only [Function.comp_def]
  rw [sequenceFin_map_bind (g := renameStep D σ) (k := pure), bind_pure]
  congr 1
  funext i
  split_ifs
  · rw [renameComp_pure, map_pure]; rfl
  · exact free_renameStep D σ _

/-- The renaming of the honest programs moves through a phase of the network. -/
theorem executePhase_rename {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (P : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality fuel state (fun i => renamePM D σ (P i)) =
      renameComp D σ (executePhase worldRoles D A noFunctionality fuel state P) := by
  unfold executePhase
  rw [startSteps_rename, renameComp_bind, bind_map_left]
  exact bind_congr fun steps => executeRounds_rename D σ A fuel state steps

end Steps

/-! ## The renaming as a monad map on the programs of the operators -/

section Hom

open DigestBudgets (ClassBound StateBound PartyIn RoIn)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

variable (D : C.Coalition) (σ : Equiv.Perm HashOutput)

/-- The renaming of an operator program, as a monad map. -/
def renameHom : PartyM C E RealSpec →ᵐ PartyM C E RealSpec where
  toFun _ p := renamePM D σ p
  toFun_pure' a := OptionT.ext (by simp [renamePM])
  toFun_bind' x f := OptionT.ext (by
    simp only [renamePM, OptionT.run_mk, OptionT.run_bind, Option.elimM, simulateQ_bind]
    refine bind_congr fun o => ?_
    cases o with
    | none => simp
    | some a => rfl)

/-- A monad map on the programs of a state. -/
def stateHom {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (h : m →ᵐ m) : StateT S m →ᵐ StateT S m where
  toFun _ x := StateT.mk fun s => h (x.run s)
  toFun_pure' a := StateT.ext fun s => by simp only [StateT.run_mk, StateT.run_pure, MonadHom.mmap_pure]
  toFun_bind' x f := StateT.ext fun s => by simp only [StateT.run_mk, StateT.run_bind, MonadHom.mmap_bind]

theorem stateHom_run {S α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (h : m →ᵐ m)
    (x : StateT S m α) (s : S) : (stateHom h x).run s = h (x.run s) := rfl

theorem stateHom_lift {S α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (h : m →ᵐ m) (x : m α) :
    stateHom (S := S) h (StateT.lift x) = StateT.lift (h x) := StateT.ext fun s => by
  simp only [stateHom_run, StateT.run_lift, MonadHom.mmap_bind, MonadHom.mmap_pure]

theorem stateHom_eq_self {S α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {h : m →ᵐ m}
    {x : StateT S m α} (hx : ∀ s, h (x.run s) = x.run s) : stateHom h x = x :=
  StateT.ext fun s => hx s

/-- A program with no call of `PRG` is its renaming. -/
theorem renameHom_eq_self {α : Type} {p : PartyM C E RealSpec α} (h : ClassBound (E := E) .stream p 0) :
    renameHom D σ p = p := by
  apply OptionT.ext
  change simulateQ (renameParty D σ) p.run = p.run
  unfold ClassBound at h
  generalize p.run = oa at h
  induction oa using OracleComp.inductionOn with
  | pure a => exact simulateQ_pure _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ PartyIn (E := E) .stream t := h.1.resolve_right (lt_irrefl 0)
    have hk : ∀ u, simulateQ (renameParty D σ) (k u) = k u := fun u => ih u (by simpa only [ht, ↓reduceIte] using h.2 u)
    have hq : renameParty D σ t = OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) t) := by
      rcases t with ((n | q | x) | outbox) | input
      · rfl
      · rfl
      · exact (ht (show InClass (C := C) .stream (.inr (.inr x)) from rfl)).elim
      · rfl
      · rfl
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, hq, hk]

theorem renameS_eq_self {S α : Type} {x : StateT S (PartyM C E RealSpec) α} (h : StateBound (E := E) .stream x 0) :
    stateHom (renameHom D σ) x = x :=
  stateHom_eq_self fun s => renameHom_eq_self D σ (h s)

theorem simulateQ_renameParty_liftLift {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (renameParty (E := E) D σ) (liftComp (liftComp oa (LocalSpec C)) (PartySpec C E RealSpec)) =
      liftComp (liftComp (simulateQ (renameRo D σ) oa) (LocalSpec C)) (PartySpec C E RealSpec) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have e : ∀ {γ : Type} (g : (RoSpec C).Range t → OracleComp (RoSpec C) γ),
        liftComp (liftComp (liftM (OracleSpec.query t) >>= g) (LocalSpec C)) (PartySpec C E RealSpec) =
          OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr t)))) >>= fun u =>
            liftComp (liftComp (g u) (LocalSpec C)) (PartySpec C E RealSpec) := by
      intro γ g
      rw [liftComp_bind, liftComp_bind]
      rcases t with _ | _ <;> rfl
    rw [e, simulateQ_bind, simulateQ_bind, liftComp_bind, liftComp_bind]
    simp only [ih, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases t with q | x
    · rfl
    · by_cases h : Hidden D x.1
      · simp only [renameParty, renameRo, h, ↓reduceIte]; rfl
      · simp only [renameParty, renameRo, h, ↓reduceIte]; rfl

theorem renameHom_oracleStep {α : Type} (oa : OracleComp (RoSpec C) α) :
    renameHom (E := E) D σ (oracleStep oa) = oracleStep (simulateQ (renameRo D σ) oa) := by
  apply OptionT.ext
  change simulateQ (renameParty D σ) ((liftComp (liftComp oa (LocalSpec C)) (PartySpec C E RealSpec)) >>=
    fun a => pure (some a)) = (liftComp (liftComp (simulateQ (renameRo D σ) oa) (LocalSpec C)) (PartySpec C E RealSpec)) >>=
    fun a => pure (some a)
  rw [simulateQ_bind, simulateQ_renameParty_liftLift]
  rfl

end Hom

/-! ## The ceremony on the renamed keys -/

section Body

variable (D : C.Coalition) (σ : Equiv.Perm HashOutput)

/-- The key `σ key` under a hidden name, and the key itself under another name. -/
def renameKey (name : KeyName C) (key : HashOutput) : HashOutput := if Hidden D name then σ key else key

/-- The PRSS keys of operator `i` with `σ` on each held term and each pair under a hidden name. -/
def renamePrss (i : C.Party) (prss : PrssKeys C) : PrssKeys C :=
  ⟨fun T => if i ∈ C.holders T then renameKey D σ (.term T) (prss.term T) else prss.term T,
    fun j => if h : j = i then prss.pair j else renameKey D σ (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)⟩

/-- The context with the renamed PRSS keys. -/
def renameCtx (ctx : Context C) : Context C := ⟨ctx.self, ctx.keys, renamePrss D σ ctx.self ctx.prss⟩

theorem renameRo_prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    simulateQ (renameRo D σ) (prgBits name key ρ idx count) = prgBits name (renameKey D σ name key) ρ idx count := by
  by_cases h : Hidden D name
  · rw [show renameKey D σ name key = σ key by simp [renameKey, h]]
    unfold prgBits
    rw [simulateQ_bind]
    erw [simulateQ_list_mapM]
    congr 1
    congr 1
    funext position
    exact (simulateQ_spec_query (renameRo D σ) _).trans (by simp only [renameRo, h, ↓reduceIte]; rfl)
  · rw [show renameKey D σ name key = key by simp [renameKey, h]]
    unfold prgBits
    rw [simulateQ_bind]
    erw [simulateQ_list_mapM]
    congr 1
    congr 1
    funext position
    exact (simulateQ_spec_query (renameRo D σ) _).trans (by simp only [renameRo, h, ↓reduceIte]; rfl)

variable {D σ} in
theorem prssRandomness_rename {R : Type} [Zero R] (codec : Codec C E R)
    (hdraw : ∀ name key ρ idx count, simulateQ (renameRo D σ) (codec.draw name key ρ idx count) =
      codec.draw name (renameKey D σ name key) ρ idx count) (ctx : Context C) (idx count : ℕ) :
    (prssRandomness (renameCtx D σ ctx) codec idx count : RunM C E RealSpec _) =
      stateHom (renameHom D σ) (prssRandomness ctx codec idx count) := by
  have hl : stateHom (renameHom D σ) (freshLabel : RunM C E RealSpec ℕ) = freshLabel :=
    renameS_eq_self D σ (by unfold freshLabel; exact DigestBudgets.StateBound.modifyGet _)
  unfold prssRandomness
  rw [MonadHom.mmap_bind, hl]
  refine bind_congr fun ρ => ?_
  rw [MonadHom.mmap_bind, stateHom_lift, renameHom_oracleStep, simulateQ_list_mapM]
  congr 1
  · congr 2
    refine congrArg (fun f => List.mapM f C.terms) (funext fun T => ?_)
    simp only [renameCtx, renamePrss]
    split_ifs with hT
    · rw [hdraw]
    · simp
  funext r
  rw [MonadHom.mmap_bind, stateHom_lift, renameHom_oracleStep, simulateQ_list_mapM]
  congr 1
  · congr 2
    refine congrArg (fun f => List.mapM f C.parties) (funext fun j => ?_)
    simp only [renameCtx, renamePrss]
    split_ifs with hj
    · simp
    · rw [hdraw]


theorem renameRo_elementCodec [Field E] [Algebra Bit E] (K : Constants C E) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) : simulateQ (renameRo D σ) ((elementCodec K).draw name key ρ idx count) =
      (elementCodec K).draw name (renameKey D σ name key) ρ idx count := by
  change simulateQ (renameRo D σ) (prgBits name key ρ idx (elementBits * count) >>= _) =
    prgBits name (renameKey D σ name key) ρ idx (elementBits * count) >>= _
  rw [simulateQ_bind, renameRo_prgBits]
  simp only [simulateQ_pure]

/-- The renaming of the programs on a state. -/
abbrev renameS {S : Type} : StateT S (PartyM C E RealSpec) →ᵐ StateT S (PartyM C E RealSpec) :=
  stateHom (renameHom D σ)

variable {D σ}

theorem ren_bind {S α β : Type} {x x' : StateT S (PartyM C E RealSpec) α}
    {f f' : α → StateT S (PartyM C E RealSpec) β} (hx : x' = renameS D σ x) (hf : ∀ a, f' a = renameS D σ (f a)) :
    x' >>= f' = renameS D σ (x >>= f) := by
  rw [MonadHom.mmap_bind, hx]
  exact congrArg (_ >>= ·) (funext hf)

theorem ren_fix {S α : Type} {x x' : StateT S (PartyM C E RealSpec) α} (h : x' = x)
    (hb : DigestBudgets.StateBound (E := E) .stream x 0) : x' = renameS D σ x := by
  rw [renameS_eq_self D σ hb, h]

theorem ren_pure {S α : Type} (a : α) : (pure a : StateT S (PartyM C E RealSpec) α) = renameS D σ (pure a) :=
  (MonadHom.mmap_pure _ _).symm

theorem ren_foldlM {S α γ : Type} {f f' : α → γ → StateT S (PartyM C E RealSpec) α}
    (hf : ∀ a g, f' a g = renameS D σ (f a g)) : ∀ (xs : List γ) (a : α),
      xs.foldlM f' a = renameS D σ (xs.foldlM f a)
  | [], a => ren_pure a
  | g :: xs, a => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact ren_bind (hf a g) fun a' => ren_foldlM hf xs a'

open DigestBudgets (ClassBound StateBound RoIn)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_mapM noCall_query)

variable [Field E] [Algebra Bit E] (K : Constants C E)

/-- The check with renamed building blocks is the renamed check. -/
theorem check_rename (ctx : Context C) (bb bb' : CheckBuildingBlocks C E RealSpec)
    (hcoin : ∀ n, bb'.coin n = renameS D σ (bb.coin n))
    (hext : ∀ ps, bb'.extendMult ps = renameS D σ (bb.extendMult ps))
    (hel : ∀ n, bb'.randElements n = renameS D σ (bb.randElements n))
    (hbits : ∀ n, bb'.randBits n = renameS D σ (bb.randBits n)) (tuples : List (Tuple C)) :
    check K ctx bb' tuples = renameS D σ (check K ctx bb tuples) := by
  have hkey : coinKey K bb' = renameS D σ (coinKey K bb) := by
    unfold coinKey
    exact ren_bind (ren_fix rfl DigestBudgets.StateBound.get) fun _ => ren_bind (hcoin 2) fun _ =>
      ren_fix rfl (DigestBudgets.StateBound.lift_zero (DigestBudgets.ClassBound.oracleStep_zero
        (DigestBudgets.noCall_hashQuery (c := .stream) _ fun h => by simp [RoIn, InClass, queryClass] at h)))
  have hch : challenge K bb' = renameS D σ (challenge K bb) := by
    unfold challenge
    refine ren_bind hkey fun key => ren_bind (ren_fix rfl (DigestBudgets.StateBound.lift_zero
      (DigestBudgets.ClassBound.oracleStep_zero (DigestBudgets.noCall_findChallenge (c := .stream) K (by decide) key _ _)))) fun r => ?_
    split
    · exact ren_pure _
    · exact ren_fix rfl (DigestBudgets.StateBound.lift_zero DigestBudgets.ClassBound.failure)
  unfold check
  dsimp only
  split_ifs with hz
  · exact ren_pure _
  refine ren_bind hkey fun key => ?_
  refine ren_bind (ren_fix rfl (DigestBudgets.expand_bound (c := .stream) K (by decide) key _)) fun τ => ?_
  refine ren_bind (ren_fix rfl (DigestBudgets.StateBound.lift_zero (DigestBudgets.ClassBound.require _))) fun _ => ?_
  refine ren_bind (ren_foldlM (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨xs, ys, Dv⟩
    exact ren_bind (hext _) fun _ => ren_bind hch fun _ => ren_pure _
  rcases v with ⟨xs, ys, Dv⟩
  refine ren_bind (ren_foldlM (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨A, B, Dv⟩
    exact ren_bind (hext _) fun _ => ren_bind hch fun _ => ren_pure _
  rcases v with ⟨A, B, Dv⟩
  refine ren_bind (hel _) fun w => ?_
  refine ren_bind (hext _) fun q => ?_
  refine ren_bind (hbits _) fun salts => ?_
  refine ren_bind (ren_fix rfl ((DigestBudgets.compareDigests_bound (c := .stream) ctx _).mono
    (by simp [DigestBudgets.digestCost]))) fun _ => ?_
  exact ren_bind hch fun _ =>
    ren_bind (ren_fix rfl (DigestBudgets.StateBound.lift_zero (DigestBudgets.openSh_bound K ctx _ _))) fun _ =>
      ren_fix rfl (DigestBudgets.StateBound.lift_zero (DigestBudgets.ClassBound.require _))

omit [Field E] [Algebra Bit E] in
theorem bitRandomness_rename (ctx : Context C) (idx count : ℕ) :
    (prssRandomness (renameCtx D σ ctx) bitCodec idx count : RunM C E RealSpec _) =
      renameS D σ (prssRandomness ctx bitCodec idx count) :=
  prssRandomness_rename _ (fun name key ρ idx count => renameRo_prgBits D σ name key ρ idx count) ctx idx count

theorem elementRandomness_rename (ctx : Context C) (idx count : ℕ) :
    (prssRandomness (renameCtx D σ ctx) (elementCodec K) idx count : RunM C E RealSpec _) =
      renameS D σ (prssRandomness ctx (elementCodec K) idx count) :=
  prssRandomness_rename _ (fun name key ρ idx count => renameRo_elementCodec D σ K name key ρ idx count) ctx idx count

/-- The real check on the renamed keys is the renamed real check. -/
theorem realCheck_rename (ctx : Context C) (tuples : List (Tuple C)) :
    check K (renameCtx D σ ctx) (realCheckBuildingBlocks K (renameCtx D σ ctx)) tuples =
      renameS D σ (check K ctx (realCheckBuildingBlocks K ctx) tuples) := by
  refine check_rename K ctx _ _ (fun n => ?_) (fun ps => ?_) (fun n => ?_) (fun n => ?_) tuples
  · exact ren_bind (elementRandomness_rename K ctx _ _) fun r => ren_fix rfl
      (DigestBudgets.StateBound.bind_zero (DigestBudgets.StateBound.lift_zero (DigestBudgets.openSh_bound K ctx _ _))
        fun _ => DigestBudgets.StateBound.pure _)
  · exact ren_bind (elementRandomness_rename K ctx _ _) fun r => ren_fix rfl
      (DigestBudgets.reshare_bound K ctx _ _ _ _)
  · exact elementRandomness_rename K ctx _ _
  · exact bitRandomness_rename ctx _ _

/-- The run of the jobs with renamed building blocks is the renamed run. -/
theorem runJobs_rename (bb bb' : RunBuildingBlocks C E RealSpec) (hmode : bb'.mode = bb.mode)
    (hmult : ∀ x y n, bb'.mult x y n = renameS D σ (bb.mult x y n))
    (hrerand : ∀ v n, bb'.rerand v n = renameS D σ (bb.rerand v n))
    (hverify : ∀ ts, bb'.verify ts = renameS D σ (bb.verify ts))
    (houtput : ∀ v n, bb'.output v n = renameS D σ (bb.output v n)) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    runJobs K bb' jobs inputs = renameS D σ (runJobs K bb jobs inputs) := by
  unfold runJobs
  simp only [hmode]
  refine ren_bind (ren_foldlM (fun v layer => ?_) _ _) fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact ren_bind (hmult _ _ _) fun _ => ren_pure _
  rcases v with ⟨wires, tuples⟩
  exact ren_bind (hrerand _ _) fun _ => ren_bind (hverify _) fun _ => ren_bind (houtput _ _) fun _ => ren_pure _

/-- The real run on the renamed keys is the renamed real run. -/
theorem realRunJobs_rename (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    runJobs K (realRunBuildingBlocks K (renameCtx D σ ctx) mode) jobs inputs =
      renameS D σ (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs) := by
  refine runJobs_rename K (realRunBuildingBlocks K ctx mode) (realRunBuildingBlocks K (renameCtx D σ ctx) mode) rfl
    (fun x y n => ?_) (fun v n => ?_) (fun ts => ?_) (fun v n => ?_) jobs inputs
  · refine ren_bind (bitRandomness_rename ctx _ _) fun r => ren_fix rfl ?_
    cases mode
    · exact DigestBudgets.reshare_bound K ctx _ _ _ _
    · exact DigestBudgets.reshareCollector_bound K ctx _ _ _
  · exact ren_bind (bitRandomness_rename ctx _ _) fun r => ren_fix rfl (DigestBudgets.reshare_bound K ctx _ _ _ _)
  · exact realCheck_rename K ctx ts
  · exact ren_fix rfl (DigestBudgets.StateBound.lift_zero ((DigestBudgets.openRep_bound (c := .stream) K ctx _ _).mono
      (by simp [DigestBudgets.copyCost])))

omit [Field E] [Algebra Bit E] in
theorem inputShares_rename (ctx : Context C) (jobs : List Job) :
    (jobs.mapM (inputShares (renameCtx D σ ctx)) : PartyM C E RealSpec _) =
      renameHom D σ (jobs.mapM (inputShares ctx)) := by
  rw [renameHom_eq_self D σ ((DigestBudgets.ClassBound.mapM _ 0
    (fun job => DigestBudgets.inputShares_bound (c := .stream) ctx (by decide) job) _).mono (by simp))]
  rfl

end Body

/-! ## The ceremonies of a tree on the renamed fresh keys -/

section Tree

variable (D : C.Coalition) (σ : Equiv.Perm HashOutput)

/-- The fresh keys with `σ` on each key. -/
def renameFresh (f : FreshKeys C) : FreshKeys C := (fun T => σ (f.1 T), fun p => σ (f.2 p))

/-- The overlay of the renamed fresh keys is the renamed overlay. -/
theorem prssOverlay_rename (i : C.Party) (prss : PrssKeys C) (f : FreshKeys C) :
    prssOverlay D i prss (renameFresh σ f) = renamePrss D σ i (prssOverlay D i prss f) := by
  simp only [prssOverlay, renamePrss, seedGenHiddenOverlay, dealtKeys, renameFresh, renameKey]
  congr 1
  · funext T
    by_cases hk : KnownTo D.1 T <;> by_cases hT : i ∈ C.holders T <;> simp [hk, hT, Hidden]
  · funext j
    by_cases hj : j = i
    · subst hj
      simp
    · by_cases hD : i ∈ D.1 ∨ j ∈ D.1
      · have hh : ¬ Hidden D (.pair (C.pairOf i j (Ne.symm hj))) := by
          rw [hidden_pairOf]
          tauto
        simp [hj, hD, hh]
      · have hh : Hidden D (.pair (C.pairOf i j (Ne.symm hj))) := by
          rw [hidden_pairOf]
          tauto
        simp [hj, hD, hh]

variable {D σ}

theorem hom_bind_eq {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (h : m →ᵐ n)
    {α β : Type} {x : m α} {x' : n α} {f : α → m β} {f' : α → n β} (hx : x' = h x) (hf : ∀ a, f' a = h (f a)) : x' >>= f' = h (x >>= f) := by
  rw [MonadHom.mmap_bind, hx]
  exact congrArg (_ >>= ·) (funext hf)

theorem hom_pure_eq {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (h : m →ᵐ n)
    {α : Type} (a : α) : (pure a : n α) = h (pure a) :=
  (MonadHom.mmap_pure _ _).symm

theorem hom_mapM_eq {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (h : m →ᵐ n)
    {α β : Type} {f : α → m β} {f' : α → n β} (hf : ∀ a, f' a = h (f a)) (xs : List α) : xs.mapM f' = h (xs.mapM f) := by
  rw [SeedHitProof.hom_mapM]
  exact congrArg (List.mapM · xs) (funext hf)

theorem stateHom_get {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (h : m →ᵐ m) :
    (get : StateT S m S) = stateHom h get :=
  StateT.ext fun s => (MonadHom.mmap_pure h (s, s)).symm

theorem stateHom_set {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (h : m →ᵐ m) (t : S) :
    (set t : StateT S m PUnit) = stateHom h (set t) :=
  StateT.ext fun _ => (MonadHom.mmap_pure h (PUnit.unit, t)).symm

theorem hom_lift_eq {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (h : m →ᵐ m) {α : Type} {x x' : m α}
    (hx : x' = h x) : (StateT.lift x' : StateT S m α) = stateHom h (StateT.lift x) := by
  rw [stateHom_lift, hx]

/-- The renaming of the programs of a ceremony, with the state of the labels and the counter of the
ceremonies. -/
abbrev renameC : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) →ᵐ StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) :=
  stateHom (stateHom (renameHom D σ))

theorem renameC_liftLift {α : Type} (p : PartyM C E RealSpec α) :
    (StateT.lift (StateT.lift (renameHom D σ p)) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) =
      renameC (D := D) (σ := σ) (StateT.lift (StateT.lift p)) := by
  rw [stateHom_lift, stateHom_lift]

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A ceremony with the renamed fresh keys is the renamed ceremony, when each ceremony of the tree
has fresh keys. -/
theorem slotCeremony_rename (fresh fresh' : ℕ → Option (FreshKeys C)) (hfresh : ∀ c, ∃ f, fresh c = some f)
    (hfresh' : ∀ c, fresh' c = (fresh c).map (renameFresh σ)) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    slotCeremony K circuits settings D fresh' i keys jobs =
      renameC (D := D) (σ := σ) (slotCeremony K circuits settings D fresh i keys jobs) := by
  unfold slotCeremony
  refine hom_bind_eq _ (hom_lift_eq _ (stateHom_get _)) fun c => hom_bind_eq _ (hom_lift_eq _ (stateHom_set _ _))
    fun _ => hom_bind_eq _ (by rw [← renameC_liftLift, renameHom_eq_self D σ
      (DigestBudgets.prssSetup_bound (c := .stream) (by decide) i)]) fun prss => ?_
  obtain ⟨f, hf⟩ := hfresh c
  simp only [hfresh' c, hf, Option.map_some, Option.getD_some, prssOverlay_rename]
  unfold batched
  refine hom_bind_eq _ (hom_mapM_eq _ (fun js => ?_) _) fun outs => hom_pure_eq _ _
  refine hom_bind_eq _ (stateHom_get _) fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine hom_bind_eq _ ?_ fun inputs => ?_
  · have hin := inputShares_rename (D := D) (σ := σ) (E := E) ⟨i, keys, prssOverlay D i prss f⟩ js
    exact (congrArg (fun p => (StateT.lift (StateT.lift p) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) _))
      hin).trans (renameC_liftLift _)
  refine hom_bind_eq _ ?_ fun r => ?_
  · have hrun := congrArg (fun x => StateT.run x (⟨fun _ => [], label, k⟩ : RunState C))
      (realRunJobs_rename (D := D) (σ := σ) K ⟨i, keys, prssOverlay D i prss f⟩ settings.mode
        (js.map (circuits keys.parameter ·.kind)) inputs)
    exact (congrArg (fun p => (StateT.lift (StateT.lift p) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) _))
      hrun).trans (renameC_liftLift _)
  rcases r with ⟨outputs, state⟩
  exact hom_bind_eq _ (stateHom_set _ _) fun _ => hom_pure_eq _ _

omit [Field E] [Algebra Bit E] in
theorem renameHom_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    renameHom D σ (oracleStep (tweakable oa) : PartyM C E RealSpec α) = oracleStep (tweakable oa) :=
  renameHom_eq_self D σ (DigestBudgets.ClassBound.oracleStep_zero
    (DigestBudgets.noCall_of_onlySign (c := .stream) (by decide) (GameCount.onlySign_tweakable _)))

/-- The ceremonies of a tree with the renamed fresh keys are the renamed ceremonies, when each
ceremony has fresh keys. -/
theorem slotTree_rename_total (fresh fresh' : ℕ → Option (FreshKeys C)) (hfresh : ∀ c, ∃ f, fresh c = some f)
    (hfresh' : ∀ c, fresh' c = (fresh c).map (renameFresh σ)) (i : C.Party) (keys : Keys C) (top : TopTree)
    (tree : Tree) :
    slotTree K circuits settings D fresh' i keys top tree =
      renameHom D σ (slotTree K circuits settings D fresh i keys top tree) := by
  have hX : ceremonyOutput (m := StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)))
      (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
      (slotCeremony K circuits settings D fresh' i keys) top tree =
      renameC (D := D) (σ := σ) (ceremonyOutput (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa))))
        keys.parameter (slotCeremony K circuits settings D fresh i keys) top tree) := by
    have hr : (fun js => renameC (D := D) (σ := σ) (slotCeremony K circuits settings D fresh i keys js)) =
        slotCeremony K circuits settings D fresh' i keys :=
      funext fun js => (slotCeremony_rename K circuits settings fresh fresh' hfresh hfresh' i keys js).symm
    have hl : (fun {β : Type} (oa : OracleComp HashSpec β) => renameC (D := D) (σ := σ)
        (StateT.lift (StateT.lift (oracleStep (tweakable oa))) :
          StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β)) =
        (fun {β : Type} (oa : OracleComp HashSpec β) => (StateT.lift (StateT.lift (oracleStep (tweakable oa))) :
          StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β)) := by
      funext β oa
      rw [← renameC_liftLift, renameHom_tweakable]
    rw [SeedHitProof.hom_ceremonyOutput, hl, hr]
  unfold slotTree
  refine hom_bind_eq _ ?_ fun o => ?_
  · simp only [StateT.run'_eq, hX, stateHom_run, ← SeedHitProof.hom_map]
  · rcases o with _ | output
    · exact (renameHom_eq_self D σ DigestBudgets.ClassBound.failure).symm
    · exact hom_pure_eq _ _

end Tree

/-! ## The counter of the ceremonies of a tree -/

section Counter

variable (D : C.Coalition) [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A ceremony after the step of the counter, with the fresh keys `fr`. -/
def slotRest (fr : Option (FreshKeys C)) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))) := do
  let prss ← StateT.lift (prssSetup i)
  let ctx : Context C := ⟨i, keys, (fr.map (prssOverlay D i prss)).getD prss⟩
  batched settings.batchSize (fun jobs => do
    let (label, k) ← get
    let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
    let (outputs, state) ← StateT.lift ((runJobs K (realRunBuildingBlocks K ctx settings.mode)
      (jobs.map (circuits keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩)
    set (state.label, k + 1)
    pure (some outputs)) jobs

theorem stLift_pure {S α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (a : α) :
    (StateT.lift (pure a) : StateT S m α) = pure a :=
  StateT.ext fun s => by simp [StateT.run_lift]

theorem stLift_bind {S α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (x : m α) (f : α → m β) :
    (StateT.lift (x >>= f) : StateT S m β) = StateT.lift x >>= fun a => StateT.lift (f a) :=
  StateT.ext fun s => by simp [StateT.run_lift, StateT.run_bind]

/-- A computation that keeps the counter of the ceremonies. -/
def liftC : StateT (ℕ × ℕ) (PartyM C E RealSpec) →ᵐ StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) where
  toFun _ x := StateT.mk fun s => StateT.lift (x.run s)
  toFun_pure' a := StateT.ext fun s => by simp [stLift_pure]
  toFun_bind' x f := StateT.ext fun s => by simp [stLift_bind]

omit [Field E] [Algebra Bit E] in
theorem liftC_run {α : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) (s : ℕ × ℕ) (n : ℕ) :
    ((liftC x).run s).run n = (fun p => (p, n)) <$> x.run s := by
  change (StateT.lift (x.run s) : StateT ℕ (PartyM C E RealSpec) _).run n = _
  rw [StateT.run_lift, map_eq_bind_pure_comp]
  rfl

omit [Field E] [Algebra Bit E] in
theorem liftC_lift {α : Type} (p : PartyM C E RealSpec α) :
    (StateT.lift (StateT.lift p) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) = liftC (StateT.lift p) :=
  StateT.ext fun s => by
    change _ = StateT.lift ((StateT.lift p : StateT (ℕ × ℕ) (PartyM C E RealSpec) α).run s)
    rw [StateT.run_lift]
    simp only [StateT.run_lift, stLift_bind, stLift_pure]

omit [Field E] [Algebra Bit E] in
theorem liftC_get : (get : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (ℕ × ℕ)) = liftC get :=
  StateT.ext fun s => by change _ = StateT.lift (pure (s, s)); simp [stLift_pure]

omit [Field E] [Algebra Bit E] in
theorem liftC_set (t : ℕ × ℕ) : (set t : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) PUnit) = liftC (set t) :=
  StateT.ext fun s => by change _ = StateT.lift (pure (PUnit.unit, t)); simp [stLift_pure]

/-- A ceremony steps the counter and then runs with the fresh keys of the counter. -/
theorem slotCeremony_eq (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    slotCeremony K circuits settings D fresh i keys jobs = (do
      let c ← StateT.lift (get : StateT ℕ (PartyM C E RealSpec) ℕ)
      StateT.lift (set (c + 1) : StateT ℕ (PartyM C E RealSpec) Unit)
      liftC (slotRest D K circuits settings (fresh c) i keys jobs)) := by
  unfold slotCeremony slotRest batched
  refine congrArg (_ >>= ·) (funext fun c => congrArg (_ >>= ·) (funext fun _ => ?_))
  refine hom_bind_eq _ (liftC_lift _) fun prss => ?_
  refine hom_bind_eq _ (hom_mapM_eq _ (fun js => ?_) _) fun outs => hom_pure_eq _ _
  refine hom_bind_eq _ liftC_get fun lk => ?_
  rcases lk with ⟨label, k⟩
  exact hom_bind_eq _ (liftC_lift _) fun inputs => hom_bind_eq _ (liftC_lift _) fun r =>
    hom_bind_eq _ (liftC_set _) fun _ => hom_pure_eq _ _

theorem slotCeremony_run (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (s : ℕ × ℕ) (n : ℕ) :
    ((slotCeremony K circuits settings D fresh i keys jobs).run s).run n =
      (fun p => (p, n + 1)) <$> (slotRest D K circuits settings (fresh n) i keys jobs).run s := by
  rw [slotCeremony_eq]
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get, StateT.run_set, liftC_run]

omit [Field E] [Algebra Bit E] in
theorem liftLift_run {α : Type} (p : PartyM C E RealSpec α) (s : ℕ × ℕ) (n : ℕ) :
    ((StateT.lift (StateT.lift p) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α).run s).run n =
      (fun a => ((a, s), n)) <$> p := by
  simp [StateT.run_lift, map_eq_bind_pure_comp]

/-- The ceremonies of a tree read the fresh keys only below `treeSetups tree`. -/
theorem slotTree_congr (fresh₁ fresh₂ : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C) (top : TopTree)
    (tree : Tree) (h : ∀ c < treeSetups tree, fresh₁ c = fresh₂ c) :
    slotTree K circuits settings D fresh₁ i keys top tree = slotTree K circuits settings D fresh₂ i keys top tree := by
  unfold slotTree
  refine congrArg (· >>= _) ?_
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  refine congrArg (_ <$> ·) ?_
  cases tree with
  | top =>
    simp only [ceremonyOutput, StateT.run_bind, slotCeremony_run, bind_map_left]
    rw [h 0 (by decide)]
  | bottom b =>
    simp only [ceremonyOutput, StateT.run_bind, slotCeremony_run, bind_map_left]
    rw [h 0 (by simp [treeSetups])]
    refine bind_congr fun p => ?_
    rcases p with ⟨o, s'⟩
    rcases o with _ | outputs
    · rfl
    · simp only [StateT.run_bind, liftLift_run, bind_map_left]
      refine bind_congr fun root => bind_congr fun base => bind_congr fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · rfl
      · simp only [StateT.run_bind, slotCeremony_run, Nat.zero_add]
        rw [h 1 (by simp [treeSetups])]

variable {σ : Equiv.Perm HashOutput}

/-- The program of a run of a tree with the renamed fresh keys is the renamed program, when each
ceremony of the tree has fresh keys. -/
theorem slotProgram_rename (fresh fresh' : ℕ → Option (FreshKeys C)) (tree : Tree)
    (hsome : ∀ c < treeSetups tree, ∃ f, fresh c = some f)
    (hfresh' : ∀ c < treeSetups tree, fresh' c = (fresh c).map (renameFresh σ)) (i : C.Party)
    (operator : OperatorState C) :
    slotProgram K circuits settings D fresh' i operator tree =
      renamePM D σ (slotProgram K circuits settings D fresh i operator tree) := by
  let tot : ℕ → Option (FreshKeys C) := fun c =>
    if c < treeSetups tree then fresh c else some (fun _ => 0, fun _ => 0)
  let tot' : ℕ → Option (FreshKeys C) := fun c => (tot c).map (renameFresh σ)
  have htot : ∀ c, ∃ f, tot c = some f := by
    intro c
    by_cases hc : c < treeSetups tree
    · simpa [tot, hc] using hsome c hc
    · exact ⟨(fun _ => 0, fun _ => 0), by simp [tot, hc]⟩
  have htree : ∀ keys top, slotTree K circuits settings D fresh' i keys top tree =
      renameHom D σ (slotTree K circuits settings D fresh i keys top tree) := by
    intro keys top
    rw [slotTree_congr D K circuits settings fresh' tot' i keys top tree (fun c hc => by
        simp [tot', tot, hc, hfresh' c hc]),
      slotTree_congr D K circuits settings fresh tot i keys top tree (fun c hc => by simp [tot, hc])]
    exact slotTree_rename_total K circuits settings tot tot' htot (fun _ => rfl) i keys top tree
  have hfail : ∀ {α : Type}, (failure : PartyM C E RealSpec α) = renamePM D σ failure := fun {α} =>
    (renameHom_eq_self D σ (α := α) DigestBudgets.ClassBound.failure).symm
  cases tree with
  | top =>
    cases hk : operator.keys with
    | none => simp only [slotProgram, hk]; exact hfail
    | some keys => simp only [slotProgram, hk]; exact htree _ _
  | bottom b =>
    cases hk : operator.keys with
    | none => simp only [slotProgram, hk]; exact hfail
    | some keys =>
      cases ht : operator.top with
      | none => simp only [slotProgram, hk, ht]; exact hfail
      | some top => simp only [slotProgram, hk, ht]; exact htree _ _

end Counter



end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.slotProgram_rename' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.slotProgram_rename

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.executePhase_rename' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.executePhase_rename
