import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Basics
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Monitor.Erase

/-!
# The erasure of the log, of the records and of a flag

Three general facts that read no flag.

* `withLog impl cells` is the handler `impl` with a log of the cells of each call. `withLog_run`
  states that the log changes no law of the result and of the state of `impl`, for each program.
* `FlagErases impl x y` relates a program `x` on the state of the game over the state of `impl` to a
  program `y` of the world on the state of the game. From two states that differ only in the flag, the
  run of `x` and the run of `y` under `impl` are equal with the flag erased. The rules are for bind,
  `get`, `set`, `modify`, a computation of the world, a read of the state of `impl`, the signing layer
  and `simulateQ`. `flagErases_phase` erases the records of a phase of the network, for each
  function that computes the flag from the records and from the states of `impl` before and after.
* `FlagErases.fst` gives one law of the result.

`monitorCommutes_stream` and `monitorKeeps_stream` are the two premises of `dkgTsigRun_obsEq` for
`streamWorld` with the unit observation.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The log -/

section Log

variable {ι : Type} {spec : OracleSpec ι} {W L : Type}

/-- The handler `impl` with a log of the cells `cells t` of each call `t`. -/
def withLog (impl : QueryImpl spec (StateT W ProbComp)) (cells : ι → List L) :
    QueryImpl spec (StateT (W × List L) ProbComp) := fun t =>
  StateT.mk fun st => (fun r => (r.1, (r.2, st.2 ++ cells t))) <$> (impl t).run st.1

/-- The log changes no law of the result and of the state of `impl`. -/
theorem withLog_run (impl : QueryImpl spec (StateT W ProbComp)) (cells : ι → List L) {α : Type}
    (oa : OracleComp spec α) (w : W) (log : List L) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (withLog impl cells) oa).run (w, log) = (simulateQ impl oa).run w := by
  induction oa using OracleComp.inductionOn generalizing w log with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, map_bind, OracleQuery.input_query, OracleQuery.cont_query,
      liftM, monadLift_self, withLog, StateT.run_mk, bind_map_left]
    exact bind_congr fun r => ih _ r.2 _

end Log

/-! ## A flag that no step reads -/

section Flag

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) {σ : Type}

/-- A result with the flag of the state of the game erased. -/
def eraseOut {α : Type} (r : α × RealState C σ) : α × RealState C σ := (r.1, eraseFlag r.2)

/-- From two states that differ only in the flag, the run of `x` and the run of `y` under `impl` are
equal with the flag erased. -/
def FlagErases {α : Type} (x : StateT (RealState C σ) (StateT W ProbComp) α) (y : RealM C σ α) : Prop :=
  ∀ s₁ s₂, eraseFlag s₁ = eraseFlag s₂ → eraseOut <$> x.run s₁ = eraseOut <$> simulateQ impl (y.run s₂)

variable {impl}

theorem FlagErases.bind {α β : Type} {x : StateT (RealState C σ) (StateT W ProbComp) α} {y : RealM C σ α}
    {f : α → StateT (RealState C σ) (StateT W ProbComp) β} {g : α → RealM C σ β}
    (hxy : FlagErases impl x y) (hfg : ∀ a, FlagErases impl (f a) (g a)) :
    FlagErases impl (x >>= f) (y >>= g) := by
  intro s₁ s₂ h
  have hK : ∀ p : α × RealState C σ, eraseOut <$> (f p.1).run p.2 =
      eraseOut <$> simulateQ impl ((g p.1).run (eraseFlag p.2)) := fun p => hfg p.1 p.2 _ (eraseFlag_idem p.2).symm
  have hG : ∀ p : α × RealState C σ, eraseOut <$> simulateQ impl ((g p.1).run (eraseFlag p.2)) =
      eraseOut <$> simulateQ impl ((g p.1).run p.2) := fun p =>
    (hfg p.1 p.2 _ (eraseFlag_idem p.2).symm).symm.trans (hfg p.1 p.2 p.2 rfl)
  calc eraseOut <$> (x >>= f).run s₁
      = x.run s₁ >>= fun p => eraseOut <$> simulateQ impl ((g p.1).run (eraseFlag p.2)) := by
        rw [StateT.run_bind, map_bind]
        exact bind_congr hK
    _ = (eraseOut <$> x.run s₁) >>= fun p => eraseOut <$> simulateQ impl ((g p.1).run p.2) := by
        rw [bind_map_left]
        rfl
    _ = (eraseOut <$> simulateQ impl (y.run s₂)) >>= fun p => eraseOut <$> simulateQ impl ((g p.1).run p.2) := by
        rw [hxy s₁ s₂ h]
    _ = eraseOut <$> simulateQ impl ((y >>= g).run s₂) := by
        rw [bind_map_left, StateT.run_bind, simulateQ_bind, map_bind]
        exact bind_congr hG

theorem flagErases_pure {α : Type} (a : α) :
    FlagErases impl (pure a : StateT (RealState C σ) (StateT W ProbComp) α) (pure a) := by
  intro s₁ s₂ h
  simp only [StateT.run_pure, map_pure, simulateQ_pure, eraseOut, h]

theorem flagErases_get_bind {α : Type} {f : RealState C σ → StateT (RealState C σ) (StateT W ProbComp) α}
    {g : RealState C σ → RealM C σ α}
    (h : ∀ s₁ s₂, eraseFlag s₁ = eraseFlag s₂ →
      eraseOut <$> (f s₁).run s₁ = eraseOut <$> simulateQ impl ((g s₂).run s₂)) :
    FlagErases impl (get >>= f) (get >>= g) := by
  intro s₁ s₂ hs
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s₁ s₂ hs

theorem flagErases_set (t₁ t₂ : RealState C σ) (ht : eraseFlag t₁ = eraseFlag t₂) :
    FlagErases impl (set t₁ : StateT (RealState C σ) (StateT W ProbComp) PUnit) (set t₂) := by
  intro s₁ s₂ _
  simp only [StateT.run_set, map_pure, simulateQ_pure, eraseOut, ht]

theorem flagErases_modify (f : RealState C σ → RealState C σ)
    (hf : ∀ s, eraseFlag (f s) = eraseFlag (f (eraseFlag s))) :
    FlagErases impl (modify f : StateT (RealState C σ) (StateT W ProbComp) PUnit) (modify f) := by
  intro s₁ s₂ hs
  simp only [StateT.run_modify, map_pure, simulateQ_pure, eraseOut]
  rw [hf s₁, hf s₂, hs]

theorem flagErases_lift {α : Type} (oa : OracleComp (WorldSpec C) α) :
    FlagErases impl (StateT.lift (simulateQ impl oa) : StateT (RealState C σ) (StateT W ProbComp) α)
      (StateT.lift oa) := by
  intro s₁ s₂ hs
  simp only [StateT.run_lift, map_bind, map_pure, simulateQ_bind, simulateQ_pure, eraseOut, hs]

/-- A read of the state of `impl` whose value the rest of `x` may use. -/
theorem flagErases_read_bind {α β : Type} (read : W → β) {f : β → StateT (RealState C σ) (StateT W ProbComp) α}
    {y : RealM C σ α} (h : ∀ v, FlagErases impl (f v) y) :
    FlagErases impl (StateT.lift (read <$> get) >>= f) y := by
  intro s₁ s₂ hs
  refine StateT.ext fun w => ?_
  simp only [StateT.run_bind, StateT.run_lift, map_bind, bind_assoc, pure_bind, StateT.run_map,
    StateT.run_get, map_pure]
  have e := congrArg (fun m => StateT.run m w) (h (read w) s₁ s₂ hs)
  simpa only [StateT.run_map] using e

theorem FlagErases.of_eq {α : Type} {x x' : StateT (RealState C σ) (StateT W ProbComp) α} {y y' : RealM C σ α}
    (h : FlagErases impl x y) (hx : x = x') (hy : y = y') : FlagErases impl x' y' := hx ▸ hy ▸ h

/-- One law of the result. -/
theorem FlagErases.fst {α : Type} {x : StateT (RealState C σ) (StateT W ProbComp) α} {y : RealM C σ α}
    (h : FlagErases impl x y) (s : RealState C σ) :
    Prod.fst <$> x.run s = Prod.fst <$> simulateQ impl (y.run s) := by
  have e := congrArg (fun m => Prod.fst <$> m) (h s s rfl)
  simpa only [eraseOut, Functor.map_map] using e

/-- `FlagErases` for each state of the signing game. -/
def FlagErasesT {α : Type} (x : StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) α)
    (y : StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ st, FlagErases impl (x.run st) (y.run st)

theorem FlagErasesT.bind {α β : Type} {x : StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) α}
    {y : StateT (TsigState C) (RealM C σ) α}
    {f : α → StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) β}
    {g : α → StateT (TsigState C) (RealM C σ) β} (hxy : FlagErasesT (impl := impl) x y)
    (hfg : ∀ a, FlagErasesT (impl := impl) (f a) (g a)) : FlagErasesT (impl := impl) (x >>= f) (y >>= g) :=
  fun st => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hxy st).bind fun p => hfg p.1 p.2

theorem flagErasesT_pure {α : Type} (a : α) :
    FlagErasesT (impl := impl) (pure a : StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) α)
      (pure a) := fun _ => flagErases_pure _

theorem flagErasesT_lift {α : Type} {x : StateT (RealState C σ) (StateT W ProbComp) α} {y : RealM C σ α}
    (h : FlagErases impl x y) :
    FlagErasesT (impl := impl) (StateT.lift x : StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp)) α)
      (StateT.lift y) :=
  fun _ => h.bind fun _ => flagErases_pure _

theorem flagErasesT_simulateQ {ι : Type} {spec : OracleSpec ι} {α : Type}
    (i₁ : QueryImpl spec (StateT (TsigState C) (StateT (RealState C σ) (StateT W ProbComp))))
    (i₂ : QueryImpl spec (StateT (TsigState C) (RealM C σ)))
    (h : ∀ t, FlagErasesT (impl := impl) (i₁ t) (i₂ t)) (oa : OracleComp spec α) :
    FlagErasesT (impl := impl) (simulateQ i₁ oa) (simulateQ i₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact flagErasesT_pure a
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (h t).bind ih

/-- The records of a phase of the network change no law, for each continuation `k₁` that reads the
records, the states of `impl` and the flag, and that agrees with `k₂` on the outputs. -/
theorem flagErases_phase {E I O L Rs Ia α ρ β : Type} (D : C.Coalition) (A : Adversary C E Ia L Rs)
    (F : Functionality C I O L Rs) (blank : ρ) (fuel : ℕ) (st : A.State)
    (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ))
    {k₁ : A.State × (C.Party → RStep C E (CallSpec I O) α ρ) → StateT (RealState C σ) (StateT W ProbComp) β}
    {k₂ : A.State × (C.Party → Option α) → RealM C σ β}
    (hk : ∀ r, FlagErases impl (k₁ r) (k₂ (r.1, fun i => (r.2 i).output))) :
    FlagErases impl (StateT.lift (simulateQ impl (executePhaseR worldRoles D A F blank fuel st program)) >>= k₁)
      (StateT.lift (executePhase worldRoles D A F fuel st fun i => dropRecord (program i)) >>= k₂) := by
  rw [executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D A F blank]
  have e : (StateT.lift ((fun r => (r.1, fun i => (r.2 i).output)) <$>
      executePhaseR worldRoles D A F blank fuel st program) : RealM C σ _) >>= k₂ =
      StateT.lift (executePhaseR worldRoles D A F blank fuel st program) >>= fun r =>
        k₂ (r.1, fun i => (r.2 i).output) := by
    refine StateT.ext fun s => ?_
    simp only [StateT.run_bind, StateT.run_lift, bind_map_left, bind_assoc, pure_bind]
  rw [e]
  exact (flagErases_lift _).bind hk

end Flag

/-! ## The monitor in `streamWorld` -/

section Stream

variable (prims : Primitives) (D : C.Coalition)

/-- A call of `streamWorld` that is no programming call is an atom on the hash cache or one query of
the random function on the hidden cache. -/
theorem streamAtom_noProgram (t : (WorldSpec C).Domain) (ht : ¬ WorldProgramQuery t) :
    WorldSplit.StreamAtom (streamWorld prims D t) := by
  rcases t with (t | p) | t
  · exact Or.inl ⟨_, isAtom_localAnswer prims t, rfl⟩
  · exact absurd trivial ht
  · exact WorldSplit.streamAtom_free prims D t

/-- In `streamWorld` a call of the monitor commutes with each call that is no programming call. -/
theorem monitorCommutes_stream : MonitorCommutes (streamWorld prims D) := fun t t' ht ht' =>
  WorldSplit.commutes_of_streamAtom (streamAtom_noProgram prims D t (by
    rcases t with (_ | _) | _ <;> simp_all [WorldProgramQuery, GameCount.MonitorCall]))
    (streamAtom_noProgram prims D t' ht')

/-- In `streamWorld` a call of the monitor keeps the unit observation. -/
theorem monitorKeeps_stream : MonitorKeeps (streamWorld prims D) fun _ => () := fun _ _ _ _ _ => rfl

end Stream

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.withLog_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.withLog_run

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.flagErases_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.flagErases_phase

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.monitorCommutes_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.monitorCommutes_stream
