import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.General
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.End

/-!
# The shared rest as a program with reads of the blind view

`sharedRestOf` is generic in the handler `impl` of the world and in the view `view` of its state. Its
instance on `peekHandler` with the view `id` is a computation of the world with reads, and
`sharedProgram` is this computation as a program with reads.

`PeekRep impl view x y` states that the computation `y` with reads, run on `withPeek impl view` from
the blind view of the state, gives the result of `x` under `impl`, and ends on the blind view of the
end state. The rules are for bind, the state of the game, the signing layer, `simulateQ`, a
computation of the world and a read of the view. A read of the view gives the full view in `x` and
the blind view in `y`, so the rule needs a continuation that reads no cell of the class of the seed
generation. The flag of `sharedRunWith` reads the hidden cache and `GlobalEvent`, and both are the
same on the blind view (`globalEvent_blind`).

`sharedRestOf_eq_program` is the representation of the shared rest. `sharedRestTable` and
`sharedRestLogged` are its instances on `tableWorld` and on `loggedWorld`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The flag on the blind view -/

theorem splitRegionCache_eraseSeedGen (P : Query C → Prop) (hP : ∀ q, P q → isSeedGenQuery q = false)
    (cache : HashCache C) : splitRegionCache P (eraseSeedGen cache) = splitRegionCache P cache := by
  refine QueryCache.ext fun q => ?_
  by_cases h : P q
  · simp [splitRegionCache, eraseSeedGen, h, hP q h]
  · simp [splitRegionCache, h]

/-- The global events read no cell of the class of the seed generation. -/
theorem globalEvent_blind (w : StreamState C) : GlobalEvent (blind w) ↔ GlobalEvent w := by
  unfold GlobalEvent DomainCollision
  simp only [blind]
  rw [splitRegionCache_eraseSeedGen _ (fun q h => by cases q <;> simp_all [EchoDomain, isSeedGenQuery]; cases ‹Phase› <;> simp_all),
    splitRegionCache_eraseSeedGen _ (fun q h => by cases q <;> simp_all [DeriveDomain, isSeedGenQuery]; cases ‹Phase› <;> simp_all),
    splitRegionCache_eraseSeedGen _ (fun q h => by cases q <;> simp_all [CopyDomain, isSeedGenQuery]),
    splitRegionCache_eraseSeedGen _ (fun q h => by cases q <;> simp_all [SplitHashDomain, isSeedGenQuery])]

/-! ## The representation by a program with reads -/

section Rules

variable {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type}
  (impl : QueryImpl (WorldSpec C) (StateT W M)) (view : W → StreamState C)

/-- The monad of a computation of the world with reads. -/
abbrev PeekM (C : Committee) := StateT (StreamState C) (OracleComp (PeekSpec C))

/-- The computation `y` with reads, run on `withPeek impl view` from the blind view of the state, gives
the result and the state of `x` under `impl`, and ends on the blind view of the end state. -/
def PeekRep {β : Type} (x : StateT W M β) (y : PeekM C β) : Prop :=
  ∀ w, (simulateQ (withPeek impl view) (y.run (blind (view w)))).run w =
    (fun z => ((z.1, blind (view z.2)), z.2)) <$> x.run w

variable {impl view}

theorem peekRep_pure {β : Type} (b : β) : PeekRep impl view (pure b) (pure b) := by
  intro w
  simp

theorem PeekRep.bind {α β : Type} {x : StateT W M α} {y : PeekM C α} {f : α → StateT W M β}
    {g : α → PeekM C β} (hxy : PeekRep impl view x y) (hfg : ∀ a, PeekRep impl view (f a) (g a)) :
    PeekRep impl view (x >>= f) (y >>= g) := by
  intro w
  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hxy w, bind_map_left, StateT.run_bind, map_bind]
  exact bind_congr fun z => hfg z.1 z.2

theorem peekRep_query (t : (WorldSpec C).Domain) : PeekRep impl view (impl t) (peekHandler t) := by
  intro w
  simp [peekHandler, withPeek, map_eq_bind_pure_comp]

/-- A computation of the world. -/
theorem peekRep_simulateQ {β : Type} (oa : OracleComp (WorldSpec C) β) :
    PeekRep impl view (simulateQ impl oa) (simulateQ peekHandler oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b => simpa using peekRep_pure b
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (peekRep_query t).bind ih

variable (impl view) in
/-- `PeekRep` from each state of the game. -/
def PeekRepS {σ β : Type} (x : SharedM C M W σ β) (y : SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β) :
    Prop :=
  ∀ s, PeekRep impl view (x.run s) (y.run s)

variable (impl view) in
/-- `PeekRepS` from each state of the signing game. -/
def PeekRepT {σ β : Type} (x : StateT (TsigState C) (SharedM C M W σ) β)
    (y : StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ) β) : Prop :=
  ∀ st, PeekRepS impl view (x.run st) (y.run st)

variable {σ : Type}

theorem PeekRepS.bind {α β : Type} {x : SharedM C M W σ α} {y : SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ α}
    {f : α → SharedM C M W σ β} {g : α → SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β}
    (hxy : PeekRepS impl view x y) (hfg : ∀ a, PeekRepS impl view (f a) (g a)) :
    PeekRepS impl view (x >>= f) (y >>= g) := fun s => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hxy s).bind fun p => hfg p.1 p.2

theorem peekRepS_pure {β : Type} (b : β) :
    PeekRepS impl view (pure b : SharedM C M W σ β) (pure b) := fun _ => peekRep_pure _

theorem peekRepS_get_bind {β : Type} {f : RealState C σ → SharedM C M W σ β}
    {g : RealState C σ → SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β}
    (h : ∀ s, PeekRepS impl view (f s) (g s)) : PeekRepS impl view (get >>= f) (get >>= g) := fun s => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s s

theorem peekRepS_set (t : RealState C σ) :
    PeekRepS impl view (set t : SharedM C M W σ PUnit) (set t) := fun _ => by
  simp only [StateT.run_set]
  exact peekRep_pure _

theorem peekRepS_modify (f : RealState C σ → RealState C σ) :
    PeekRepS impl view (modify f : SharedM C M W σ PUnit) (modify f) := fun _ => by
  simp only [StateT.run_modify]
  exact peekRep_pure _

theorem peekRepS_lift {β : Type} {x : StateT W M β} {y : PeekM C β} (h : PeekRep impl view x y) :
    PeekRepS impl view (StateT.lift x : SharedM C M W σ β) (StateT.lift y) := fun s => by
  simp only [StateT.run_lift]
  exact h.bind fun _ => peekRep_pure _

/-- A computation of the world in the game. -/
theorem peekRepS_inWorld {β : Type} (oa : OracleComp (WorldSpec C) β) :
    PeekRepS impl view (inWorld impl oa : SharedM C M W σ β) (inWorld peekHandler oa) :=
  peekRepS_lift (peekRep_simulateQ oa)

/-- A read of the view. The computation reads the full view and the program the blind view. -/
theorem peekRepS_read_bind {β : Type} {f : StreamState C → SharedM C M W σ β}
    {g : StreamState C → SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β}
    (h : ∀ u, PeekRepS impl view (f u) (g (blind u))) :
    PeekRepS impl view (StateT.lift (view <$> get) >>= f) (StateT.lift (id <$> get) >>= g) := fun s w => by
  have e := h (view w) s w
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_get, map_pure, pure_bind, id,
    StateT.run_pure] at e ⊢
  exact e

theorem PeekRepT.bind {α β : Type} {x : StateT (TsigState C) (SharedM C M W σ) α}
    {y : StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ) α}
    {f : α → StateT (TsigState C) (SharedM C M W σ) β}
    {g : α → StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ) β}
    (hxy : PeekRepT impl view x y) (hfg : ∀ a, PeekRepT impl view (f a) (g a)) :
    PeekRepT impl view (x >>= f) (y >>= g) := fun st => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hxy st).bind fun p => hfg p.1 p.2

theorem peekRepT_pure {β : Type} (b : β) :
    PeekRepT impl view (pure b : StateT (TsigState C) (SharedM C M W σ) β) (pure b) := fun _ => peekRepS_pure _

theorem peekRepT_lift {β : Type} {x : SharedM C M W σ β}
    {y : SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β} (h : PeekRepS impl view x y) :
    PeekRepT impl view (StateT.lift x : StateT (TsigState C) (SharedM C M W σ) β) (StateT.lift y) := fun _ =>
  h.bind fun _ => peekRepS_pure _

theorem peekRepT_simulateQ {ι : Type} {spec : OracleSpec ι} {β : Type}
    (i₁ : QueryImpl spec (StateT (TsigState C) (SharedM C M W σ)))
    (i₂ : QueryImpl spec (StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ)))
    (h : ∀ t, PeekRepT impl view (i₁ t) (i₂ t)) (oa : OracleComp spec β) :
    PeekRepT impl view (simulateQ i₁ oa) (simulateQ i₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b => simpa using peekRepT_pure b
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (h t).bind ih

omit [LawfulMonad M] in
theorem PeekRepS.of_eq {β : Type} {x x' : SharedM C M W σ β}
    {y y' : SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ β} (h : PeekRepS impl view x y) (hx : x = x')
    (hy : y = y') : PeekRepS impl view x' y' := hx ▸ hy ▸ h

theorem peekRepT_get_bind {β : Type} {f : RealState C σ → StateT (TsigState C) (SharedM C M W σ) β}
    {g : RealState C σ → StateT (TsigState C) (SharedM C (OracleComp (PeekSpec C)) (StreamState C) σ) β}
    (h : ∀ s, PeekRepT impl view (f s) (g s)) :
    PeekRepT impl view (StateT.lift get >>= f) (StateT.lift get >>= g) := fun st => by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact peekRepS_get_bind fun s => h s st

theorem peekRepS_mapGet {β : Type} (f : RealState C σ → β) :
    PeekRepS impl view (f <$> (get : SharedM C M W σ _)) (f <$> get) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact peekRepS_get_bind fun _ => peekRepS_pure _

end Rules

/-! ## The walk of the shared rest -/

section Walk

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
variable {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type}
  (impl : QueryImpl (WorldSpec C) (StateT W M)) (view : W → StreamState C)

/-- The computations of the world in the game over `impl`. It is `worldHom` with a lawful monad `M`
in the place of `ProbComp`. -/
def worldHomOver (σ : Type) : OracleComp (WorldSpec C) →ᵐ SharedM C M W σ where
  toFun _ oa := inWorld impl oa
  toFun_pure' a := by ext; simp [inWorld]
  toFun_bind' _ _ := by ext; simp [inWorld]

theorem blind_snd (w : StreamState C) : (blind w).2 = w.2 := rfl

omit [Fintype E] [DecidableEq E] in
/-- One recorded run. -/
theorem peekRepS_sharedRunWith (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (program : C.Party → RecM C E TreeOutput) (tree : Tree) :
    PeekRepS impl view (sharedRunWith K circuits settings impl view D net program tree)
      (sharedRunWith K circuits settings peekHandler id D net program tree) := by
  unfold sharedRunWith
  refine peekRepS_get_bind fun s => ?_
  refine peekRepS_read_bind fun before => ?_
  refine (peekRepS_inWorld _).bind fun r => ?_
  refine peekRepS_read_bind fun after => ?_
  simp only [blind_snd, globalEvent_blind]
  exact peekRepS_set _

omit [Fintype E] [DecidableEq E] in
/-- One run in the real mode. -/
theorem peekRepS_sharedRun_real (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    PeekRepS impl view (sharedRun K circuits settings impl view Mode.real D net parameter seeds dealt emu tree)
      (sharedRun K circuits settings peekHandler id Mode.real D net parameter seeds dealt emu tree) := by
  unfold sharedRun
  refine peekRepS_get_bind fun s => ?_
  have hnot : ¬ s.runs tree < Mode.real.emulated tree := by simp [Mode.real]
  rw [ite_eq_right hnot, ite_eq_right hnot]
  exact peekRepS_sharedRunWith K circuits settings impl view D net _ tree

omit [Fintype E] [DecidableEq E] in
theorem peekRepS_sharedRuns_real (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, PeekRepS impl view
      (sharedRuns K circuits settings runLimit impl view Mode.real D net parameter seeds dealt emu tree count)
      (sharedRuns K circuits settings runLimit peekHandler id Mode.real D net parameter seeds dealt emu tree count)
  | 0 => peekRepS_pure ()
  | count + 1 => by
    have run := peekRepS_sharedRun_real K circuits settings impl view D net parameter seeds dealt emu tree
    have rest := peekRepS_sharedRuns_real D net parameter seeds dealt emu tree count
    unfold sharedRuns
    refine peekRepS_get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h, ite_eq_left h]
      exact run.bind fun _ => rest
    · rw [ite_eq_right h, ite_eq_right h]
      exact peekRepS_pure ()

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signing oracles of a dealer on the computations of the world. -/
theorem peekRepT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C) :
    PeekRepT impl view
      (tsigOracles (sharedLift (σ := σ) impl) (SeedHitProof.Dealt.hmap (worldHomOver impl σ) d) q)
      (tsigOracles (sharedLift (σ := σ) peekHandler) (SeedHitProof.Dealt.hmap (worldHomOver peekHandler σ) d) q) :=
  fun st => (peekRepS_inWorld _).of_eq
    (SeedHitProof.hom_tsigOracles (worldHomOver impl σ) (fun oa => free (liftComp oa _)) d q st)
    (SeedHitProof.hom_tsigOracles (worldHomOver peekHandler σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
theorem peekRepT_dealerOracles (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C) :
    PeekRepT impl view
      (sharedDealerOracles K circuits settings runLimit impl view Mode.real D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (worldHomOver impl A.net.State) d) q)
      (sharedDealerOracles K circuits settings runLimit peekHandler id Mode.real D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (worldHomOver peekHandler A.net.State) d) q) := by
  unfold sharedDealerOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact peekRepT_pure _
  · dsimp only
    refine (peekRepT_tsig impl view d _).bind fun answer => ?_
    by_cases hc : Mode.real.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      refine (peekRepT_lift (peekRepS_sharedRuns_real K circuits settings runLimit impl view D A.net parameter seeds
        dealt emu _ 1)).bind fun _ => peekRepT_get_bind fun s => ?_
      split <;> exact peekRepT_pure _
    · simp only [hc, ↓reduceIte]
      refine peekRepT_get_bind fun s => ?_
      split <;> exact peekRepT_pure _
  all_goals
    dsimp only
    refine (peekRepT_lift (peekRepS_modify _)).bind fun _ => peekRepT_get_bind fun s => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first | exact peekRepT_tsig impl view d _ | exact peekRepT_pure _

omit [Fintype E] [DecidableEq E] in
/-- The signing phase with the answers of the dealer, in the real mode. -/
theorem peekRepS_dealerSigning (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    PeekRepS impl view
      (sharedSigning K circuits settings runLimit impl view false Mode.real D A parameter seeds dealt emu)
      (sharedSigning K circuits settings runLimit peekHandler id false Mode.real D A parameter seeds dealt emu) := by
  unfold sharedSigning
  refine peekRepS_get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact peekRepS_pure _
  | some kt =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold sharedDealer
    simp only [bind_assoc, pure_bind]
    have e₁ : referenceTree (fun oa => sharedLift (σ := A.net.State) impl (tweakable oa))
        (fun x => sharedLift (σ := A.net.State) impl (prfValue seeds x)) parameter emptyTop .top =
        worldHomOver impl A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (worldHomOver impl A.net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    have e₂ : referenceTree (fun oa => sharedLift (σ := A.net.State) peekHandler (tweakable oa))
        (fun x => sharedLift (σ := A.net.State) peekHandler (prfValue seeds x)) parameter emptyTop .top =
        worldHomOver peekHandler A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (worldHomOver peekHandler A.net.State)
        (fun oa => free (liftComp (tweakable oa) _)) (fun x => free (liftComp (prfValue seeds x) _)) parameter
        emptyTop .top).symm
    rw [e₁, e₂]
    refine (peekRepS_inWorld _).bind fun out => ?_
    have d₁ : dealtWith (sharedLift (σ := A.net.State) impl) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => sharedLift (σ := A.net.State) impl (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (worldHomOver impl A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (worldHomOver impl A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    have d₂ : dealtWith (sharedLift (σ := A.net.State) peekHandler) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) (fun x => sharedLift (σ := A.net.State) peekHandler (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (worldHomOver peekHandler A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (worldHomOver peekHandler A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₁, d₂]
    refine (peekRepT_simulateQ _ _ (fun t => ?_) _ _).bind fun p => ?_
    · rcases t with t | q | q
      · exact peekRepT_lift (peekRepS_inWorld _)
      · exact peekRepT_dealerOracles K circuits settings runLimit impl view D A parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact peekRepT_lift (peekRepS_mapGet _)
        · exact peekRepT_lift (peekRepS_modify _)
    · rcases p with ⟨forgery, st⟩
      exact (peekRepS_inWorld _).of_eq
        (hom_forgeryWins (worldHomOver impl A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)
        (hom_forgeryWins (worldHomOver peekHandler A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)

omit [Fintype E] [DecidableEq E] in
theorem peekRep_sharedRestOf (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) :
    PeekRep impl view (sharedRestOf K circuits settings runLimit impl view false D A state keys)
      (sharedRestOf K circuits settings runLimit peekHandler id false D A state keys) := by
  unfold sharedRestOf sharedRest
  have h := (peekRepS_sharedRuns_real K circuits settings runLimit impl view D A.net (gameParameter D keys)
    (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none) .top runLimit).bind fun _ =>
      peekRepS_dealerSigning K circuits settings runLimit impl view D A (gameParameter D keys) (gameSeeds D keys)
        (fun i => (keys i).getD noKeys) (fun _ => none)
  exact (h (startState D state keys)).bind fun p => by
    rcases p with ⟨win, s⟩
    exact peekRep_pure _

end Walk

/-! ## The representation -/

/-- The shared rest as a program with reads. -/
def sharedProgram (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)
    (A : DkgTsigAdversary C E) (state : A.net.State) (keys : C.Party → Option (Keys C)) :
    OracleComp (PeekSpec C) (Bool × Bool) :=
  programOf (sharedRestOf K circuits settings runLimit peekHandler id false D A state keys)

/-- A computation that a program with reads represents is the program on `withPeek`. -/
theorem run'_eq_programOf {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type}
    {impl : QueryImpl (WorldSpec C) (StateT W M)} {view : W → StreamState C} {β : Type} {x : StateT W M β}
    {y : PeekM C β} (h : PeekRep impl view x y) (w : W) :
    x.run' w = (simulateQ (withPeek impl view) (programOf y)).run' w := by
  have e := congrArg (fun m => (fun z => z.1.1) <$> m) (h w)
  simp only [Functor.map_map] at e
  simp only [programOf, StateT.run'_eq, simulateQ_bind, StateT.run_bind, StateT.run_map, simulateQ_map]
  rw [← e]
  simp [withPeek]

omit [Fintype E] [DecidableEq E] in
/-- The representation of the shared rest. For each handler `impl` of the world over a lawful monad
and each view `view` of its state, the shared rest on `impl` is its program with reads on
`withPeek impl view`. -/
theorem sharedRestOf_eq_program (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
    {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W M))
    (view : W → StreamState C) (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) (w : W) :
    (sharedRestOf K circuits settings runLimit impl view false D A state keys).run' w =
      (simulateQ (withPeek impl view) (sharedProgram K circuits settings runLimit D A state keys)).run' w :=
  run'_eq_programOf (peekRep_sharedRestOf K circuits settings runLimit impl view D A state keys) w

/-- The cells of the log of a call of the world with reads. A read has no cell. -/
def peekCells : (PeekSpec C).Domain → List (Query C)
  | .inl t => countedCells t
  | .inr _ => []

/-- `loggedWorld` with reads of the view `Prod.fst` is `streamWorld` with reads and the log. -/
theorem withPeek_loggedWorld (prims : Primitives) (D : C.Coalition) :
    withPeek (loggedWorld prims D) Prod.fst = withLog (withPeek (streamWorld prims D) id) peekCells := by
  funext t
  rcases t with t | u
  · rfl
  · refine StateT.ext fun st => ?_
    simp [withPeek, withLog, peekCells]

omit [Fintype E] [DecidableEq E] in
/-- The shared rest in `loggedWorld` is its program with reads in `streamWorld`. -/
theorem sharedRestOf_logged (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (runLimit : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) (w : StreamState C) (log : List (Query C)) :
    (sharedRestOf K circuits settings runLimit (loggedWorld prims D) Prod.fst false D A state keys).run' (w, log) =
      (simulateQ (withPeek (streamWorld prims D) id) (sharedProgram K circuits settings runLimit D A state keys)).run' w := by
  rw [sharedRestOf_eq_program, withPeek_loggedWorld, StateT.run'_eq, StateT.run'_eq,
    ← withLog_run _ peekCells _ w log, Functor.map_map]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRestOf_eq_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRestOf_eq_program

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRestOf_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRestOf_logged
