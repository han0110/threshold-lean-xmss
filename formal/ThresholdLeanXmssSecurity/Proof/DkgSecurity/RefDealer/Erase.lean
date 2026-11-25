import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Split

/-!
# The ghost calls of the dealer change no law

A free computation on `.hash` and `.prf` commutes in `loggedWorld` with each call that is no
programming call, and with a read of the hidden cache or of the global events, which it keeps
(`CommW`). So such a computation whose result is unused can be dropped in front of each program
that commutes with it, with one law of the result and of the state of the game (`ObsW`, `ObsS`,
`ObsT`). `ghostErase` proves `GhostErase`, and `sharedRefDealer_of_couple` gives `SharedRefDealer`
from `PassCleanOutput` and `GhostCouple`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## Free calls of the dealer commute -/

section Commute

open GameCount (OnlySign MonitorCall)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_bind noCall_pure noCall_sequenceFin)

variable (D : C.Coalition)

/-- A computation on `.hash` and `.prf` on the free copy in `loggedWorld`. -/
def monitorRun {γ : Type} (oa : OracleComp (RoSpec C) γ) : StateT (LogState C) ProbComp γ :=
  simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))

/-- Each computation on `.hash` and `.prf` on the free copy commutes with `X` in `loggedWorld`. -/
def CommW {α : Type} (X : StateT (LogState C) ProbComp α) : Prop :=
  ∀ (γ : Type) (oa : OracleComp (RoSpec C) γ), OnlySign oa → Commutes (monitorRun prims D oa) X

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A log that a call of the monitor does not extend keeps the commutation. -/
theorem commutes_withLog {ι : Type} {spec : OracleSpec ι} {W L : Type} (impl : QueryImpl spec (StateT W ProbComp))
    (cells : ι → List L) {t t' : ι} (h : Commutes (impl t) (impl t')) (ht : cells t = []) :
    Commutes (withLog impl cells t) (withLog impl cells t') := fun st => by
  have e₁ : (do let a ← withLog impl cells t; let b ← withLog impl cells t'; pure (a, b)).run st =
      (fun r => (r.1, (r.2, st.2 ++ cells t'))) <$>
        (do let a ← impl t; let b ← impl t'; pure (a, b)).run st.1 := by
    simp [withLog, ht, StateT.run_bind, map_bind, bind_map_left]
  have e₂ : (do let b ← withLog impl cells t'; let a ← withLog impl cells t; pure (a, b)).run st =
      (fun r => (r.1, (r.2, st.2 ++ cells t'))) <$>
        (do let b ← impl t'; let a ← impl t; pure (a, b)).run st.1 := by
    simp [withLog, ht, StateT.run_bind, map_bind, bind_map_left]
  rw [e₁, e₂]
  exact (h st.1).map _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- In `loggedWorld` a call of the monitor commutes with each call that is no programming call. -/
theorem monitorCommutes_logged : MonitorCommutes (loggedWorld prims D) := fun t t' ht ht' => by
  have hc : countedCells t = [] := by
    rcases t with ((_ | _) | _) | _ <;> first | rfl | exact absurd ht (by simp [MonitorCall])
  exact commutes_withLog (streamWorld prims D) countedCells (monitorCommutes_stream prims D t t' ht ht') hc

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commW_pure {α : Type} (a : α) : CommW prims D (pure a : StateT (LogState C) ProbComp α) :=
  fun _ _ _ => commutes_pure _ a

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem CommW.bind {α β : Type} {X : StateT (LogState C) ProbComp α} {f : α → StateT (LogState C) ProbComp β}
    (hX : CommW prims D X) (hf : ∀ a, CommW prims D (f a)) : CommW prims D (X >>= f) :=
  fun γ oa h => (hX γ oa h).bind_right fun a => hf a γ oa h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the world with no programming call. -/
theorem commW_world {α : Type} (ob : OracleComp (WorldSpec C) α)
    (hob : AllQueriesSatisfy ob fun t => ¬ WorldProgramQuery t) :
    CommW prims D (simulateQ (loggedWorld prims D) ob) :=
  fun _ _ h => commutes_monitor_simulateQ (monitorCommutes_logged prims D) _ (GameCount.allQueries_free_liftComp h) ob hob

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A read of a function of the state that each call of the monitor keeps. -/
theorem commW_read {β : Type} (f : LogState C → β)
    (hf : ∀ {γ : Type} (oa : OracleComp (RoSpec C) γ), OnlySign oa → ∀ w, ∀ z ∈ support ((monitorRun prims D oa).run w),
      f z.2 = f w) :
    CommW prims D (f <$> (get : StateT (LogState C) ProbComp (LogState C))) := fun _ oa h w => by
  simp only [StateT.run_bind, StateT.run_map, StateT.run_get, map_pure, pure_bind, bind_pure_comp,
    Functor.map_map]
  refine EvalDistEq.of_eq ?_
  simp only [map_eq_bind_pure_comp]
  exact bind_congr_of_forall_mem_support _ fun z hz => by simp [hf oa h w z hz]

/-! ### What a call of the monitor keeps -/

/-- A cell outside `.hash` and `.prf`. -/
def OffSign (q : Query C) : Prop := (∀ x, q ≠ .hash x) ∧ ∀ seed x, q ≠ .prf seed x

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation on `.hash` and `.prf` changes no other cell of the hash cache. -/
theorem roRun_offSign {γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) :
    ∀ c, ∀ z ∈ support (roRun prims oa c), ∀ q, OffSign q → z.2 q = c q := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c z hz q _
    simp [roRun] at hz
    subst hz
    rfl
  | query_bind t k ih =>
    rw [GameCount.onlySign_iff, allQueriesSatisfy_query_bind_iff] at h
    obtain ⟨ht, hk⟩ := h
    intro c z hz q hq
    simp only [roRun, simulateQ_bind, simulateQ_query, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map] at hp
    have h₁ := ih p.1 ((GameCount.onlySign_iff _).2 (hk p.1)) p.2 z hz q hq
    rw [h₁]
    rcases t with q₀ | x
    · change p ∈ support ((hashAnswer prims q₀).run c) at hp
      have hne : q ≠ q₀ := by
        rintro rfl
        rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [GameCount.SignCall, OffSign]
      unfold hashAnswer at hp
      split at hp
      · split_ifs at hp
        · simp at hp
          subst hp
          rfl
        · exact SigningPartnerBoundProof.randomOracle_cache_ne _ c p hp q hne
      · exact SigningPartnerBoundProof.randomOracle_cache_ne _ c p hp q hne
    · exact absurd ht (by simp [GameCount.SignCall])

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A call of the monitor keeps the hidden cache and each cell outside `.hash` and `.prf`. -/
theorem monitorRun_keeps {γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) (w : LogState C) :
    ∀ z ∈ support ((monitorRun prims D oa).run w), z.2.1.2 = w.1.2 ∧ ∀ q, OffSign q → z.2.1.1 q = w.1.1 q := by
  intro z hz
  have hw := withLog_run (streamWorld prims D) countedCells (free (liftComp oa (LocalSpec C))) w.1 w.2
  rw [show withLog (streamWorld prims D) countedCells = loggedWorld prims D from rfl] at hw
  have hz' : (z.1, z.2.1) ∈ support (Ready.freeRun prims D oa w.1) := by
    change (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D) (free (liftComp oa (LocalSpec C)))).run w.1)
    rw [← hw, support_map]
    exact ⟨z, hz, rfl⟩
  rw [freeRun_onlySign prims D oa h, support_map] at hz'
  obtain ⟨y, hy, hyz⟩ := hz'
  simp only [Prod.mk.injEq] at hyz
  obtain ⟨-, hyz⟩ := hyz
  rw [← hyz]
  exact ⟨rfl, fun q hq => roRun_offSign prims oa h w.1.1 y hy q hq⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem splitRegionCache_congr {P : Query C → Prop} {c c' : HashCache C} (h : ∀ q, P q → c q = c' q) :
    splitRegionCache P c = splitRegionCache P c' := by
  refine QueryCache.ext fun q => ?_
  by_cases hq : P q
  · simp [splitRegionCache, hq, h q hq]
  · simp [splitRegionCache, hq]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Two caches that agree outside `.hash` and `.prf` have the same global events. -/
theorem globalEvent_congr {w w' : StreamState C} (h : ∀ q, OffSign q → w.1 q = w'.1 q) :
    GlobalEvent w ↔ GlobalEvent w' := by
  have key : ∀ P : Query C → Prop, (∀ q, P q → OffSign q) → (DomainCollision P w.1 ↔ DomainCollision P w'.1) :=
    fun P hP => by
      unfold DomainCollision
      rw [splitRegionCache_congr fun q hq => h q (hP q hq)]
  have off : ∀ P : Query C → Prop, (∀ x, ¬ P (.hash x)) → (∀ seed x, ¬ P (.prf seed x)) → ∀ q, P q → OffSign q :=
    fun P h₁ h₂ q hq => ⟨fun x hx => h₁ x (hx ▸ hq), fun seed x hx => h₂ seed x (hx ▸ hq)⟩
  unfold GlobalEvent
  rw [key EchoDomain (off _ (fun _ => id) fun _ _ => id), key DeriveDomain (off _ (fun _ => id) fun _ _ => id),
    key CopyDomain (off _ (fun _ => id) fun _ _ => id), key SplitHashDomain (off _ (fun _ => id) fun _ _ => id)]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commW_hidden : CommW prims D ((fun w : LogState C => w.1.2) <$> (get : StateT (LogState C) ProbComp _)) :=
  commW_read prims D _ fun oa h w z hz => (monitorRun_keeps prims D oa h w z hz).1

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commW_global :
    CommW prims D ((fun w : LogState C => decide (GlobalEvent w.1)) <$> (get : StateT (LogState C) ProbComp _)) :=
  commW_read prims D _ fun oa h w z hz => by
    simp only [decide_eq_decide]
    exact globalEvent_congr (monitorRun_keeps prims D oa h w z hz).2

/-! ### One law up to the calls of the monitor -/

/-- `X` and `Y`, each with a continuation that commutes with the monitor, give one law of the result
from each state. -/
def ObsW {α : Type} (X Y : StateT (LogState C) ProbComp α) : Prop :=
  ∀ (β : Type) (k : α → StateT (LogState C) ProbComp β), (∀ a, CommW prims D (k a)) → ∀ w,
    Prod.fst <$> (X >>= k).run w =ᵈ Prod.fst <$> (Y >>= k).run w

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsW.refl {α : Type} (X : StateT (LogState C) ProbComp α) : ObsW prims D X X :=
  fun _ _ _ _ => EvalDistEq.rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsW.trans {α : Type} {X Y Z : StateT (LogState C) ProbComp α} (h : ObsW prims D X Y)
    (h' : ObsW prims D Y Z) : ObsW prims D X Z :=
  fun β k hk w => (h β k hk w).trans (h' β k hk w)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsW.bind_left {α α' : Type} {X Y : StateT (LogState C) ProbComp α} (h : ObsW prims D X Y)
    {f : α → StateT (LogState C) ProbComp α'} (hf : ∀ a, CommW prims D (f a)) :
    ObsW prims D (X >>= f) (Y >>= f) := fun β k hk w => by
  rw [bind_assoc, bind_assoc]
  exact h β (fun a => f a >>= k) (fun a => CommW.bind prims D (hf a) hk) w

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsW.bind_right {α α' : Type} (X : StateT (LogState C) ProbComp α)
    {f g : α → StateT (LogState C) ProbComp α'} (h : ∀ a, ObsW prims D (f a) (g a)) :
    ObsW prims D (X >>= f) (X >>= g) := fun β k hk w => by
  simp only [bind_assoc, StateT.run_bind, map_bind]
  exact EvalDistEq.bind_right _ fun p => by
    have hp := h p.1 β k hk p.2
    simp only [StateT.run_bind, map_bind] at hp
    exact hp

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the monitor whose result is unused can be dropped. -/
theorem obsW_monitor {α γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) (a : α) :
    ObsW prims D (monitorRun prims D oa >>= fun _ => pure a) (pure a) := fun β k hk w => by
  have hc := (hk a γ oa h).bind (fun (_ : γ) (b : β) => (pure b : StateT (LogState C) ProbComp β)) w
  simp only [bind_pure] at hc
  rw [bind_assoc]
  simp only [pure_bind]
  refine (hc.map _).trans ?_
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_congr_of_support _ fun p _ => ?_
  exact EvalDistEq.bind_const _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One law of the result. -/
theorem ObsW.law {α : Type} {X Y : StateT (LogState C) ProbComp α} (h : ObsW prims D X Y) (w : LogState C) :
    Prod.fst <$> X.run w =ᵈ Prod.fst <$> Y.run w := by
  have e := h α pure (fun a => commW_pure prims D a) w
  simpa only [bind_pure] using e

/-! ### The recorded phase makes no programming call -/

section NoProgram

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rstep_callInput_real {α ρ : Type} (step : RStep C E RealSpec α ρ) : step.callInput = none := by
  cases step with
  | call input _ => exact input.elim
  | _ => rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgram_stepRoundR {Ia α ρ : Type} (net : Adversary C E Ia PEmpty PEmpty) (blank : ρ) (state : net.State)
    (steps : C.Party → RStep C E RealSpec α ρ) :
    NoCall WorldProgramQuery (stepRoundR worldRoles D net noFunctionality blank state steps) := by
  unfold stepRoundR
  split_ifs with hcall
  · exact absurd hcall (by simp [rstep_callInput_real])
  refine noCall_bind _ (Collision.noProgram_adversary _) fun p => ?_
  refine noCall_bind _ (noCall_sequenceFin _ _ fun j => ?_) fun _ => noCall_pure _ _
  split
  · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact Collision.noProgram_free _
  · exact noCall_pure _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgram_executeRoundsR {Ia α ρ : Type} (net : Adversary C E Ia PEmpty PEmpty) (blank : ρ) :
    ∀ (fuel : ℕ) (state : net.State) (steps : C.Party → RStep C E RealSpec α ρ),
      NoCall WorldProgramQuery (executeRoundsR worldRoles D net noFunctionality blank fuel state steps)
  | 0, _, _ => noCall_pure _ _
  | fuel + 1, state, steps => by
    unfold executeRoundsR
    split_ifs
    · exact noCall_pure _ _
    · exact noCall_bind _ (noProgram_stepRoundR D net blank state steps) fun p =>
        noProgram_executeRoundsR net blank fuel p.1 p.2.1

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noProgram_executePhaseR {Ia α ρ : Type} (net : Adversary C E Ia PEmpty PEmpty) (blank : ρ) (fuel : ℕ)
    (state : net.State) (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) :
    NoCall WorldProgramQuery (executePhaseR worldRoles D net noFunctionality blank fuel state program) := by
  unfold executePhaseR startStepsR
  refine noCall_bind _ (noCall_sequenceFin _ _ fun i => ?_) fun steps =>
    noProgram_executeRoundsR D net blank fuel state steps
  split_ifs
  · exact noCall_pure _ _
  · exact Collision.noProgram_free _

end NoProgram

/-! ### The programs on the state of the game -/

/-- Each call of the monitor commutes with `x` from each state of the game. -/
def CommS {σ α : Type} (x : SharedM C ProbComp (LogState C) σ α) : Prop := ∀ s, CommW prims D (x.run s)

/-- `x` and `y` give one law of the result and of the state of the game up to the calls of the
monitor, from each state of the game. -/
def ObsS {σ α : Type} (x y : SharedM C ProbComp (LogState C) σ α) : Prop := ∀ s, ObsW prims D (x.run s) (y.run s)

variable {σ : Type}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_pure {α : Type} (a : α) : CommS prims D (pure a : SharedM C ProbComp (LogState C) σ α) :=
  fun s => commW_pure prims D (a, s)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem CommS.bind {α β : Type} {x : SharedM C ProbComp (LogState C) σ α} {f : α → SharedM C ProbComp (LogState C) σ β}
    (hx : CommS prims D x) (hf : ∀ a, CommS prims D (f a)) : CommS prims D (x >>= f) := fun s => by
  rw [StateT.run_bind]
  exact CommW.bind prims D (hx s) fun p => hf p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_get_bind {α : Type} {f : RealState C σ → SharedM C ProbComp (LogState C) σ α}
    (hf : ∀ s, CommS prims D (f s)) : CommS prims D (get >>= f) := fun s => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf s s

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_modify (f : RealState C σ → RealState C σ) :
    CommS prims D (modify f : SharedM C ProbComp (LogState C) σ PUnit) := fun _ => by
  simp only [StateT.run_modify]
  exact commW_pure prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_lift {α : Type} {X : StateT (LogState C) ProbComp α} (hX : CommW prims D X) :
    CommS prims D (StateT.lift X : SharedM C ProbComp (LogState C) σ α) := fun s => by
  simp only [StateT.run_lift]
  exact CommW.bind prims D hX fun a => commW_pure prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the world with no programming call. -/
theorem commS_inWorld {α : Type} (oa : OracleComp (WorldSpec C) α) (h : NoCall WorldProgramQuery oa) :
    CommS prims D (inWorld (loggedWorld prims D) oa : SharedM C ProbComp (LogState C) σ α) :=
  commS_lift prims D (commW_world prims D oa (UsedHit.allQueries_of_noCall h))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A local computation of the honest operators. -/
theorem commS_sharedLift {α : Type} (oa : OracleComp (RoSpec C) α) :
    CommS prims D (sharedLift (loggedWorld prims D) oa : SharedM C ProbComp (LogState C) σ α) :=
  commS_inWorld prims D _ (Collision.noProgram_free _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsS.trans {α : Type} {x y z : SharedM C ProbComp (LogState C) σ α} (h : ObsS prims D x y)
    (h' : ObsS prims D y z) : ObsS prims D x z := fun s => (h s).trans prims D (h' s)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsS.bind_left {α β : Type} {x y : SharedM C ProbComp (LogState C) σ α} (h : ObsS prims D x y)
    {f : α → SharedM C ProbComp (LogState C) σ β} (hf : ∀ a, CommS prims D (f a)) :
    ObsS prims D (x >>= f) (y >>= f) := fun s => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (h s).bind_left prims D fun p => hf p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsS.bind_right {α β : Type} (x : SharedM C ProbComp (LogState C) σ α)
    {f g : α → SharedM C ProbComp (LogState C) σ β} (h : ∀ a, ObsS prims D (f a) (g a)) :
    ObsS prims D (x >>= f) (x >>= g) := fun s => by
  rw [StateT.run_bind, StateT.run_bind]
  exact ObsW.bind_right prims D _ fun p => h p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A local computation on `.hash` and `.prf` whose result is unused can be dropped. -/
theorem obsS_monitor {α γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) (a : α) :
    ObsS prims D (sharedLift (loggedWorld prims D) oa >>= fun _ => pure a : SharedM C ProbComp (LogState C) σ α)
      (pure a) := fun s => by
  have e : (sharedLift (loggedWorld prims D) oa >>= fun _ => pure a : SharedM C ProbComp (LogState C) σ α).run s =
      monitorRun prims D oa >>= fun _ => pure (a, s) := by
    simp [sharedLift, inWorld, monitorRun, StateT.run_lift]
  rw [e, StateT.run_pure]
  exact obsW_monitor prims D oa h (a, s)

omit [Fintype E] [DecidableEq E] in
/-- One recorded run. Its flag reads the hidden cache before the run and the global events after
it, and each call of the monitor keeps both. -/
theorem commS_sharedRunWith (net : Adversary C E Unit PEmpty PEmpty) (program : C.Party → RecM C E TreeOutput)
    (tree : Tree) :
    CommS prims D (sharedRunWith K circuits settings (loggedWorld prims D) Prod.fst D net program tree) := fun s => by
  have e : (sharedRunWith K circuits settings (loggedWorld prims D) Prod.fst D net program tree).run s =
      ((fun w : LogState C => w.1.2) <$> (get : StateT (LogState C) ProbComp _)) >>= fun hidden =>
        simulateQ (loggedWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E)
          (treeFuel circuits settings) s.adversary fun i => (program i).run.run) >>= fun r =>
        ((fun w : LogState C => decide (GlobalEvent w.1)) <$> (get : StateT (LogState C) ProbComp _)) >>= fun ge =>
        simulateQ (loggedWorld prims D) (voteRound worldRoles D net r.1 fun i => ((r.2 i).output).map (treeVote tree))
          >>= fun v =>
        pure (PUnit.unit, (⟨v.1, fun i => (s.operators i).keep (committed v.2 (fun i => (r.2 i).output) i) tree,
          Function.update s.runs tree (s.runs tree + 1), s.closed,
          s.flag || (decide (PassBad K D fun i => (r.2 i).record []) ||
            (decide (ReusedBefore D hidden fun i => (r.2 i).record []) || ge)) ||
            split D (committed v.2 fun i => (r.2 i).output)⟩ : RealState C net.State)) := by
    simp only [sharedRunWith, inWorld, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
      StateT.run_set, bind_assoc, bind_map_left]
    simp [Bool.decide_or]
  rw [e]
  exact CommW.bind prims D (commW_hidden prims D) fun _ =>
    CommW.bind prims D (commW_world prims D _ (UsedHit.allQueries_of_noCall (noProgram_executePhaseR D net _ _ _ _)))
      fun _ => CommW.bind prims D (commW_global prims D) fun _ =>
        CommW.bind prims D (commW_world prims D _ (UsedHit.allQueries_of_noCall (Collision.noProgram_voteRound D net _ _)))
          fun _ => commW_pure prims D _

omit [Fintype E] [DecidableEq E] in
/-- The real runs of a tree. -/
theorem commS_sharedRuns_real (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, CommS prims D (sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
      parameter seeds dealt emu tree count)
  | 0 => commS_pure prims D ()
  | count + 1 => by
    unfold sharedRuns
    refine commS_get_bind prims D fun s => ?_
    split_ifs
    · rw [sharedRun_real]
      exact CommS.bind prims D (commS_get_bind prims D fun s' =>
        commS_sharedRunWith prims K circuits settings D net _ tree) fun _ =>
          commS_sharedRuns_real net parameter seeds dealt emu tree count
    · exact commS_pure prims D ()


omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_roHom {α : Type} (oa : OracleComp (RoSpec C) α) : CommS prims D (roHom prims D σ oa) :=
  commS_sharedLift prims D oa

/-! ### The signing layer -/

/-- Each call of the monitor commutes with `x` from each signing state and each state of the game. -/
def CommT {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) : Prop :=
  ∀ st, CommS prims D (x.run st)

/-- `ObsS` from each signing state. -/
def ObsT {α : Type} (x y : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) : Prop :=
  ∀ st, ObsS prims D (x.run st) (y.run st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commT_pure {α : Type} (a : α) :
    CommT prims D (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) :=
  fun st => commS_pure prims D (a, st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem CommT.bind {α β : Type} {x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    {f : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β}
    (hx : CommT prims D x) (hf : ∀ a, CommT prims D (f a)) : CommT prims D (x >>= f) := fun st => by
  rw [StateT.run_bind]
  exact CommS.bind prims D (hx st) fun p => hf p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commT_lift {α : Type} {x : SharedM C ProbComp (LogState C) σ α} (hx : CommS prims D x) :
    CommT prims D (StateT.lift x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) := fun st => by
  simp only [StateT.run_lift]
  exact CommS.bind prims D hx fun a => commS_pure prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commT_simulateQ {ι : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (LogState C) σ)))
    (hH : ∀ t, CommT prims D (H t)) {α : Type} (oa : OracleComp spec α) : CommT prims D (simulateQ H oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using commT_pure prims D a
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    exact CommT.bind prims D (hH t) ih

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsT.trans {α : Type} {x y z : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    (h : ObsT prims D x y) (h' : ObsT prims D y z) : ObsT prims D x z := fun st => (h st).trans prims D (h' st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsT.bind_left {α β : Type} {x y : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    (h : ObsT prims D x y) {f : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β}
    (hf : ∀ a, CommT prims D (f a)) : ObsT prims D (x >>= f) (y >>= f) := fun st => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (h st).bind_left prims D fun p => hf p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsT.bind_right {α β : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α)
    {f g : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β} (h : ∀ a, ObsT prims D (f a) (g a)) :
    ObsT prims D (x >>= f) (x >>= g) := fun st => by
  rw [StateT.run_bind, StateT.run_bind]
  exact ObsS.bind_right prims D _ fun p => h p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem obsT_simulateQ {ι : Type} {spec : OracleSpec ι}
    (H' H : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (LogState C) σ)))
    (h : ∀ t, ObsT prims D (H' t) (H t)) (hH : ∀ t, CommT prims D (H t)) {α : Type} (oa : OracleComp spec α) :
    ObsT prims D (simulateQ H' oa) (simulateQ H oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun st s => ObsW.refl prims D _
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (ObsT.bind_right prims D _ ih).trans prims D
      ((h t).bind_left prims D fun a => commT_simulateQ prims D H hH (k a))

end Commute

/-! ## The proof of `GhostErase` -/

section Erase

open GameCount (OnlySign)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall)

variable (D : C.Coalition) {σ : Type}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_mapGet {β : Type} (f : RealState C σ → β) :
    CommS prims D (f <$> (get : SharedM C ProbComp (LogState C) σ (RealState C σ))) := fun s => by
  simp only [StateT.run_map, StateT.run_get, map_pure]
  exact commW_pure prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_get : CommS prims D (get : SharedM C ProbComp (LogState C) σ (RealState C σ)) := by
  simpa using commS_mapGet prims D (σ := σ) id

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsS.refl {α : Type} (x : SharedM C ProbComp (LogState C) σ α) : ObsS prims D x x :=
  fun _ => ObsW.refl prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ObsT.refl {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) : ObsT prims D x x :=
  fun _ => ObsS.refl prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The answer of an operator on its own outputs. -/
theorem commT_operatorAnswer (seeds : C.Term → HashOutput) (operator : OperatorState C) (e : KeyIndex)
    (q : TsigQuery C) :
    CommT prims D (operatorAnswer (sharedLift (σ := σ) (loggedWorld prims D))
      (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) operator e q) := fun st => by
  have h := hom_operatorAnswer (roHom prims D σ) (fun oa => oa) (fun x => prfValue seeds x) operator e q st
  have h' : (operatorAnswer (sharedLift (σ := σ) (loggedWorld prims D))
      (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) operator e q).run st =
      roHom prims D σ ((operatorAnswer (fun oa => oa) (fun x => prfValue seeds x) operator e q).run st) := h.symm
  rw [h']
  exact commS_roHom prims D _

omit [Fintype E] [DecidableEq E] in
/-- The signing oracles of the real game. -/
theorem commT_ownOracles (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (q : TsigQuery C) :
    CommT prims D (sharedOwnOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
      parameter seeds dealt emu q) := by
  unfold sharedOwnOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact commT_pure prims D _
  · refine commT_lift prims D (CommS.bind prims D (commS_sharedRuns_real prims K circuits settings runLimit D net
      parameter seeds dealt emu _ 1) fun _ => commS_get_bind prims D fun s => ?_)
    split
    · exact CommS.bind prims D (commS_sharedLift prims D _) fun _ => commS_pure prims D _
    · exact commS_pure prims D _
  all_goals
    exact CommT.bind prims D (commT_lift prims D (commS_modify prims D _)) fun _ =>
      CommT.bind prims D (commT_lift prims D (commS_get prims D)) fun s => commT_operatorAnswer prims D _ _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A ghost call before a program that commutes with the monitor can be dropped. -/
theorem obsT_ghost {γ α : Type} (g : OracleComp (RoSpec C) γ) (hg : OnlySign g)
    (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) (hx : CommT prims D x) :
    ObsT prims D (StateT.lift (sharedLift (loggedWorld prims D) g) >>= fun _ => x) x := fun st => by
  have e : (StateT.lift (sharedLift (loggedWorld prims D) g) >>= fun _ => x).run st =
      (sharedLift (loggedWorld prims D) g >>= fun _ => pure ()) >>= fun _ => x.run st := by
    simp [StateT.run_bind, StateT.run_lift]
  rw [e]
  have h := (obsS_monitor prims D g hg ()).bind_left prims D (f := fun _ => x.run st) fun _ => hx st
  simpa using h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A ghost call before a program on the game state that commutes with the monitor can be dropped. -/
theorem obsS_ghost {γ α : Type} (g : OracleComp (RoSpec C) γ) (hg : OnlySign g)
    (x : SharedM C ProbComp (LogState C) σ α) (hx : CommS prims D x) :
    ObsS prims D (sharedLift (loggedWorld prims D) g >>= fun _ => x) x := by
  have h := (obsS_monitor prims D g hg ()).bind_left prims D (f := fun _ => x) fun _ => hx
  simpa using h

omit [Fintype E] [DecidableEq E] in
/-- The signing oracles with ghosts and the signing oracles of the real game. -/
theorem obsT_ghostOracles (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (top : TopTree) (q : TsigQuery C) :
    ObsT prims D (ghostOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst D net parameter seeds dealt
      top q) (sharedOwnOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
        parameter seeds dealt (fun _ => none) q) := by
  have own := commT_ownOracles prims K circuits settings runLimit D net parameter seeds dealt (fun _ => none)
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact ObsT.refl prims D _
  · exact obsT_ghost prims D _ (onlySign_ghostTreeRo parameter seeds top b) _ (own _)
  · exact ObsT.refl prims D _
  · set x := sharedOwnOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
      parameter seeds dealt (fun _ => none) (.round2 i J e message parts)
    have ex : x = (get >>= fun _ => StateT.lift (get : SharedM C ProbComp (LogState C) net.State _) >>= fun _ =>
        (pure () : StateT (TsigState C) (SharedM C ProbComp (LogState C) net.State) Unit) >>= fun _ => x) := by
      refine StateT.ext fun st => StateT.ext fun s => ?_
      simp [StateT.run_bind, StateT.run_lift]
    conv => rhs; rw [ex]
    unfold ghostOracles
    refine ObsT.bind_right prims D _ fun st => ObsT.bind_right prims D _ fun s => ?_
    split_ifs
    · exact obsT_ghost prims D _ (GameCount.onlySign_map _ (onlySign_refBottom parameter seeds top _)) x (own _)
    · exact ObsT.refl prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The win test of the real game. -/
theorem commS_forgeryWins (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (held : Fin (2 ^ layerHeight) → Option BottomTree) (st : TsigState C)
    (forgery : Forgery) :
    CommS prims D (forgeryWins (sharedLift (σ := σ) (loggedWorld prims D))
      { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
          (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
        bottom := fun b => pure (held b) } st forgery) := by
  rw [← hmap_heldDealt prims D σ parameter keys top seeds held]
  have h := hom_forgeryWins (roHom prims D σ) (fun oa => oa) (heldDealt parameter keys top seeds held) st forgery
  have h' : forgeryWins (sharedLift (σ := σ) (loggedWorld prims D))
      (SeedHitProof.Dealt.hmap (roHom prims D σ) (heldDealt parameter keys top seeds held)) st forgery =
      roHom prims D σ (forgeryWins (fun oa => oa) (heldDealt parameter keys top seeds held) st forgery) := h.symm
  rw [h']
  exact commS_roHom prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem commS_honestSignature (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (held : Fin (2 ^ layerHeight) → Option BottomTree) (e : KeyIndex)
    (message : Message) :
    CommS prims D (honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
      { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
          (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
        bottom := fun b => pure (held b) } e message) := by
  rw [← hmap_heldDealt prims D σ parameter keys top seeds held]
  have h := hom_honestSignature (roHom prims D σ) (fun oa => oa) (heldDealt parameter keys top seeds held) e message
  have h' : honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
      (SeedHitProof.Dealt.hmap (roHom prims D σ) (heldDealt parameter keys top seeds held)) e message =
      roHom prims D σ (honestSignature (fun oa => oa) (heldDealt parameter keys top seeds held) e message) := h.symm
  rw [h']
  exact commS_roHom prims D _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The win test with the ghosts and the win test of the real game. -/
theorem obsS_winTest (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (held : Fin (2 ^ layerHeight) → Option BottomTree)
    (ghost : Fin (2 ^ layerHeight) → OracleComp (RoSpec C) Unit) (hghost : ∀ b, OnlySign (ghost b))
    (st : TsigState C) (forgery : Forgery) :
    ObsS prims D (forgeryWins (sharedLift (σ := σ) (loggedWorld prims D))
      { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
          (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
        bottom := fun b => do
          sharedLift (loggedWorld prims D) (ghost b)
          pure (held b) } st forgery)
      (forgeryWins (sharedLift (σ := σ) (loggedWorld prims D))
      { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
          (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
        bottom := fun b => pure (held b) } st forgery) := by
  unfold forgeryWins
  refine ObsS.bind_right prims D _ fun verified => ?_
  split_ifs
  · exact ObsS.refl prims D _
  · have e : honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
        { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
            (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
          bottom := fun b => do
            sharedLift (loggedWorld prims D) (ghost b)
            pure (held b) } forgery.signature.leafIndex forgery.message =
        sharedLift (loggedWorld prims D) (ghost (treeOf forgery.signature.leafIndex)) >>= fun _ =>
          honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
            { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
                (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
              bottom := fun b => pure (held b) } forgery.signature.leafIndex forgery.message := by
      unfold honestSignature
      simp only [bind_assoc, pure_bind]
    rw [e]
    simp only [bind_assoc]
    exact obsS_ghost prims D _ (hghost _) _ (CommS.bind prims D (commS_honestSignature prims D parameter keys top
      seeds held _ _) fun _ => CommS.bind prims D (commS_pure prims D _) fun _ => commS_pure prims D _)

omit [Fintype E] [DecidableEq E] in
/-- The signing phase with ghosts and the signing phase of the real game. -/
theorem obsS_ghostSigning (A : DkgTsigAdversary C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) :
    ObsS prims D (ghostSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D A parameter seeds dealt)
      (sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst true Mode.real D A parameter seeds dealt
        (fun _ => none)) := by
  unfold ghostSigning sharedSigning
  refine ObsS.bind_right prims D _ fun s => ?_
  cases topHolder D s.operators with
  | none => exact ObsS.refl prims D _
  | some kt =>
    rcases kt with ⟨keys, top⟩
    simp only [↓reduceIte]
    refine (ObsS.bind_right prims D _ fun _ => ?_).trans prims D (obsS_ghost prims D _ ?_ _ ?_)
    · refine (ObsS.bind_right prims D _ fun p => ?_).trans prims D
        ((obsT_simulateQ prims D _ _ (fun t => ?_) (fun t => ?_) _ _).bind_left prims D fun p => ?_)
      · rcases p with ⟨forgery, st⟩
        exact ObsS.bind_right prims D _ fun _ => obsS_winTest prims D _ _ _ _ _ _
          (fun b => GameCount.onlySign_map _ (onlySign_refBottom parameter seeds top b)) _ _
      · rcases t with t | q | q
        · exact ObsT.refl prims D _
        · exact obsT_ghostOracles prims K circuits settings runLimit D A.net parameter seeds dealt top q
        · rcases q with _ | state <;> exact ObsT.refl prims D _
      · rcases t with t | q | q
        · exact commT_lift prims D (commS_inWorld prims D _ (Collision.noProgram_adversary _))
        · exact commT_ownOracles prims K circuits settings runLimit D A.net parameter seeds dealt _ q
        · rcases q with _ | state
          · exact commT_lift prims D (commS_mapGet prims D _)
          · exact commT_lift prims D (commS_modify prims D _)
      · rcases p with ⟨forgery, st⟩
        exact commS_get_bind prims D fun _ => commS_forgeryWins prims D _ _ _ _ _ _ _
    · exact GameCount.onlySign_map _ (GameCount.onlySign_referenceTree seeds parameter emptyTop .top)
    · refine CommS.bind prims D (commT_simulateQ prims D _ (fun t => ?_) _ _) fun p => ?_
      · rcases t with t | q | q
        · exact commT_lift prims D (commS_inWorld prims D _ (Collision.noProgram_adversary _))
        · exact commT_ownOracles prims K circuits settings runLimit D A.net parameter seeds dealt _ q
        · rcases q with _ | state
          · exact commT_lift prims D (commS_mapGet prims D _)
          · exact commT_lift prims D (commS_modify prims D _)
      · rcases p with ⟨forgery, st⟩
        exact commS_get_bind prims D fun _ => commS_forgeryWins prims D _ _ _ _ _ _ _

end Erase

omit [Fintype E] [DecidableEq E] in
/-- The proof of `GhostErase`. -/
theorem ghostErase : GhostErase prims K circuits settings runLimit := by
  intro keys D A s w
  have h := ObsW.law prims D (obsS_ghostSigning prims K circuits settings runLimit D A (gameParameter D keys)
    (gameSeeds D keys) (fun i => (keys i).getD noKeys) s) w
  have e := EvalDistEq.prEvent_eq h (fun y => y.1 = true ∧ y.2.flag = false)
  simp only [prEvent_map] at e
  exact e.symm

omit [Fintype E] [DecidableEq E] in
/-- `SharedRefDealer` from the outputs of one run and the coupling. -/
theorem sharedRefDealer_of_couple (clean : PassCleanOutput prims K circuits settings)
    (couple : GhostCouple prims K circuits settings runLimit) : SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_ghosts prims K circuits settings runLimit clean (ghostErase prims K circuits settings runLimit)
    couple

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.ghostErase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.ghostErase

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_couple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_couple
