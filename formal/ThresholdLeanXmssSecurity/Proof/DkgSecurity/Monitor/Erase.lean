import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.JointSetup
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops

/-!
# The erasure of a monitor

A monitor of the runs is free when it makes only free calls of `H` on `.hash` and on `.prf`
(`FreeMonitor`). Its result only sets the flag of the game, and no step of the game reads that flag.
This file states that the monitor changes no law of the game besides the flag.

`ObsEq impl obs X Y` states that `X` and `Y`, each with a continuation that makes no programming call,
have one law of the result and of `obs` of the final state of `impl`. The handler `impl` has two
properties. A call of the monitor commutes with each call that is no programming call
(`MonitorCommutes`), and a call of the monitor keeps `obs` (`MonitorKeeps`). Then a computation of the
monitor whose result is unused can move to the end of the run, where it keeps `obs`
(`obsEq_monitor_pure`).

`FlagEq x y` relates two programs on the state of the game. From two states that differ only in the
flag, the two runs with the flag erased are `ObsEq`. `dkgTsigRun_obsEq` states that `dkgTsigRun` with
two free monitors gives one law of the win and of `obs`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mono)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

open GameCount (MonitorCall)
open UsedHit (allQueries_of_noCall)

variable {C : Committee}

/-! ## The handler -/

section Handler

variable {S β : Type} (impl : QueryImpl (WorldSpec C) (StateT S ProbComp)) (obs : S → β)

/-- A call of the monitor commutes with each call that is no programming call. -/
def MonitorCommutes : Prop :=
  ∀ t t', MonitorCall t → ¬ WorldProgramQuery t' → Commutes (impl t) (impl t')

/-- A call of the monitor keeps `obs`. -/
def MonitorKeeps : Prop :=
  ∀ t, MonitorCall t → ∀ s, ∀ r ∈ support ((impl t).run s), obs r.2 = obs s

variable {impl obs}

theorem commutes_query_simulateQ (hcomm : MonitorCommutes impl) {t : (WorldSpec C).Domain} (ht : MonitorCall t)
    {α : Type} (ob : OracleComp (WorldSpec C) α) (hob : AllQueriesSatisfy ob fun t => ¬ WorldProgramQuery t) :
    Commutes (impl t) (simulateQ impl ob) := by
  induction ob using OracleComp.inductionOn with
  | pure b => rw [simulateQ_pure]; exact commutes_pure (impl t) b
  | query_bind t' k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hob
    rw [simulateQ_bind, simulateQ_query]
    exact ((hcomm t t' ht hob.1).map_right _).bind_right fun u => ih u (hob.2 u)

/-- A computation of the monitor commutes with each computation that makes no programming call. -/
theorem commutes_monitor_simulateQ (hcomm : MonitorCommutes impl) {α γ : Type} (m : OracleComp (WorldSpec C) γ)
    (hm : AllQueriesSatisfy m MonitorCall) (ob : OracleComp (WorldSpec C) α)
    (hob : AllQueriesSatisfy ob fun t => ¬ WorldProgramQuery t) :
    Commutes (simulateQ impl m) (simulateQ impl ob) := by
  induction m using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact (commutes_pure (simulateQ impl ob) a).symm
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hm
    rw [simulateQ_bind, simulateQ_query]
    exact ((commutes_query_simulateQ hcomm hm.1 ob hob).map_left _).bind_left fun u => ih u (hm.2 u)

/-- A computation of the monitor keeps `obs`. -/
theorem monitor_keeps (hkeep : MonitorKeeps impl obs) {γ : Type} (m : OracleComp (WorldSpec C) γ)
    (hm : AllQueriesSatisfy m MonitorCall) : ∀ s, ∀ r ∈ support ((simulateQ impl m).run s), obs r.2 = obs s := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    intro s r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hm
    intro s r hr
    rw [simulateQ_bind, simulateQ_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    rw [StateT.run_map, support_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    exact (ih _ (hm.2 _) u'.2 r hr).trans (hkeep t hm.1 s u' hu')

end Handler

/-! ## One law of the result and of the observation -/

section Obs

variable {S β : Type} (impl : QueryImpl (WorldSpec C) (StateT S ProbComp)) (obs : S → β)

/-- `X` and `Y`, each with a continuation that makes no programming call, give one law of the result
and of `obs` of the final state, from each state. -/
def ObsEq {α : Type} (X Y : OracleComp (WorldSpec C) α) : Prop :=
  ∀ (γ : Type) (k : α → OracleComp (WorldSpec C) γ), (∀ a, NoCall WorldProgramQuery (k a)) → ∀ s : S,
    (fun r => (r.1, obs r.2)) <$> (simulateQ impl (X >>= k)).run s =ᵈ
      (fun r => (r.1, obs r.2)) <$> (simulateQ impl (Y >>= k)).run s

variable {impl obs}

theorem ObsEq.refl {α : Type} (X : OracleComp (WorldSpec C) α) : ObsEq impl obs X X :=
  fun _ _ _ _ => EvalDistEq.rfl

theorem ObsEq.of_eq {α : Type} {X Y : OracleComp (WorldSpec C) α} (h : X = Y) : ObsEq impl obs X Y :=
  h ▸ ObsEq.refl X

theorem ObsEq.symm {α : Type} {X Y : OracleComp (WorldSpec C) α} (h : ObsEq impl obs X Y) : ObsEq impl obs Y X :=
  fun γ k hk s => (h γ k hk s).symm

theorem ObsEq.trans {α : Type} {X Y Z : OracleComp (WorldSpec C) α} (h : ObsEq impl obs X Y)
    (h' : ObsEq impl obs Y Z) : ObsEq impl obs X Z :=
  fun γ k hk s => (h γ k hk s).trans (h' γ k hk s)

theorem ObsEq.bind_left {α α' : Type} {X Y : OracleComp (WorldSpec C) α} (h : ObsEq impl obs X Y)
    {f : α → OracleComp (WorldSpec C) α'} (hf : ∀ a, NoCall WorldProgramQuery (f a)) :
    ObsEq impl obs (X >>= f) (Y >>= f) := fun γ k hk s => by
  rw [bind_assoc, bind_assoc]
  exact h γ (fun a => f a >>= k) (fun a => noCall_bind _ (hf a) hk) s

theorem ObsEq.bind_right {α α' : Type} (X : OracleComp (WorldSpec C) α) {f g : α → OracleComp (WorldSpec C) α'}
    (h : ∀ a, ObsEq impl obs (f a) (g a)) : ObsEq impl obs (X >>= f) (X >>= g) := fun γ k hk s => by
  simp only [bind_assoc, simulateQ_bind, StateT.run_bind, map_bind]
  refine EvalDistEq.bind_right _ fun p => ?_
  have hp := h p.1 γ k hk p.2
  simp only [simulateQ_bind, StateT.run_bind, map_bind] at hp
  exact hp

theorem ObsEq.map {α α' : Type} {X Y : OracleComp (WorldSpec C) α} (h : ObsEq impl obs X Y) (f : α → α') :
    ObsEq impl obs (f <$> X) (f <$> Y) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind_left fun _ => noCall_pure _ _

/-- A computation of the monitor whose result is unused can be dropped. -/
theorem obsEq_monitor_pure (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {α γ : Type}
    (m : OracleComp (WorldSpec C) γ) (hm : AllQueriesSatisfy m MonitorCall) (a : α) :
    ObsEq impl obs (m >>= fun _ => pure a) (pure a) := by
  intro γ' k hk s
  have e : simulateQ impl ((m >>= fun _ => pure a) >>= k) =
      (do let _ ← simulateQ impl m; simulateQ impl (k a)) := by
    simp only [bind_assoc, pure_bind, simulateQ_bind]
  have hc := (commutes_monitor_simulateQ hcomm m hm (k a) (allQueries_of_noCall (hk a))).bind
    (fun (_ : γ) (b : γ') => (pure b : StateT S ProbComp γ')) s
  simp only [bind_pure] at hc
  rw [e, pure_bind]
  refine (hc.map _).trans ?_
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_congr_of_support _ fun p _ => ?_
  rw [bind_congr_of_forall_mem_support _ fun r hr => by rw [monitor_keeps hkeep m hm p.2 r hr]]
  exact EvalDistEq.bind_const _ _

/-- A computation of the monitor whose result is unused can be dropped before a computation `V` with
no programming call. -/
theorem obsEq_monitor_drop (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {α γ : Type}
    (m : OracleComp (WorldSpec C) γ) (hm : AllQueriesSatisfy m MonitorCall) (V : OracleComp (WorldSpec C) α)
    (hV : NoCall WorldProgramQuery V) : ObsEq impl obs (m >>= fun _ => V) V := by
  have e : (m >>= fun _ => V) = (m >>= fun _ => pure ()) >>= fun _ => V := by simp only [bind_assoc, pure_bind]
  rw [e]
  exact ((obsEq_monitor_pure hcomm hkeep m hm ()).bind_left fun _ => hV).trans (ObsEq.of_eq (pure_bind _ _))

end Obs

/-! ## Programs on the state of the game -/

section Flag

variable {S β : Type} (impl : QueryImpl (WorldSpec C) (StateT S ProbComp)) (obs : S → β) {τ : Type}

/-- The state of the game with the flag erased. -/
def eraseFlag (s : RealState C τ) : RealState C τ := { s with flag := false }

/-- The run of `x` from `s` with the flag of the final state erased. -/
def erasedRun {α : Type} (x : RealM C τ α) (s : RealState C τ) : OracleComp (WorldSpec C) (α × RealState C τ) :=
  (fun r => (r.1, eraseFlag r.2)) <$> x.run s

/-- `y` makes no programming call, and from two states that differ only in the flag, the runs of `x`
and of `y` with the flag erased are `ObsEq`. -/
def FlagEq {α : Type} (x y : RealM C τ α) : Prop :=
  UsedHit.NoProg y ∧ ∀ s₁ s₂, eraseFlag s₁ = eraseFlag s₂ → ObsEq impl obs (erasedRun x s₁) (erasedRun y s₂)

variable {impl obs}

theorem eraseFlag_idem (s : RealState C τ) : eraseFlag (eraseFlag s) = eraseFlag s := rfl

theorem noCall_erasedRun {α : Type} {y : RealM C τ α} (hy : UsedHit.NoProg y) (s : RealState C τ) :
    NoCall WorldProgramQuery (erasedRun y s) :=
  noCall_map _ _ (hy s)

theorem erasedRun_bind {α α' : Type} (x : RealM C τ α) (f : α → RealM C τ α') (s : RealState C τ) :
    erasedRun (x >>= f) s = x.run s >>= fun p => erasedRun (f p.1) p.2 := by
  simp only [erasedRun, StateT.run_bind, map_bind]

theorem erasedRun_bind_erase {α α' : Type} (x : RealM C τ α) (f : α → RealM C τ α') (s : RealState C τ) :
    (x.run s >>= fun p => erasedRun (f p.1) (eraseFlag p.2)) = erasedRun x s >>= fun p => erasedRun (f p.1) p.2 := by
  simp only [erasedRun, bind_map_left]

theorem FlagEq.bind {α α' : Type} {x y : RealM C τ α} {f g : α → RealM C τ α'} (hxy : FlagEq impl obs x y)
    (hfg : ∀ a, FlagEq impl obs (f a) (g a)) (hg : ∀ a, FlagEq impl obs (g a) (g a)) :
    FlagEq impl obs (x >>= f) (y >>= g) := by
  refine ⟨hxy.1.bind fun a => (hg a).1, fun s₁ s₂ h => ?_⟩
  rw [erasedRun_bind, erasedRun_bind]
  refine ObsEq.trans (ObsEq.bind_right (x.run s₁) (g := fun p => erasedRun (g p.1) (eraseFlag p.2))
    fun p => (hfg p.1).2 p.2 (eraseFlag p.2) (eraseFlag_idem p.2).symm) ?_
  rw [erasedRun_bind_erase x g s₁]
  refine ObsEq.trans (ObsEq.bind_left (hxy.2 s₁ s₂ h) fun p => noCall_erasedRun (hg p.1).1 p.2) ?_
  rw [← erasedRun_bind_erase y g s₂]
  exact ObsEq.bind_right _ fun p => (hg p.1).2 (eraseFlag p.2) p.2 (eraseFlag_idem p.2)

theorem flagEq_get_bind {α : Type} {f g : RealState C τ → RealM C τ α} (hg : ∀ s, UsedHit.NoProg (g s))
    (h : ∀ s₁ s₂, eraseFlag s₁ = eraseFlag s₂ → ObsEq impl obs (erasedRun (f s₁) s₁) (erasedRun (g s₂) s₂)) :
    FlagEq impl obs (get >>= f) (get >>= g) := by
  have e : ∀ (F : RealState C τ → RealM C τ α) s, erasedRun (get >>= F) s = erasedRun (F s) s := by
    intro F s
    simp only [erasedRun, StateT.run_bind, StateT.run_get, pure_bind]
  refine ⟨UsedHit.NoProg.get.bind hg, fun s₁ s₂ hs => ?_⟩
  rw [e, e]
  exact h s₁ s₂ hs

theorem flagEq_pure {α : Type} (a : α) : FlagEq impl obs (pure a : RealM C τ α) (pure a) :=
  ⟨UsedHit.NoProg.pure a, fun s₁ s₂ h => ObsEq.of_eq (by simp only [erasedRun, StateT.run_pure, map_pure, h])⟩

theorem flagEq_lift {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa) :
    FlagEq impl obs (StateT.lift oa : RealM C τ α) (StateT.lift oa) :=
  ⟨UsedHit.NoProg.lift h, fun s₁ s₂ hs => ObsEq.of_eq (by simp only [erasedRun, StateT.run_lift, map_bind, map_pure, hs])⟩

theorem flagEq_modify (f : RealState C τ → RealState C τ) (hf : ∀ s, eraseFlag (f s) = eraseFlag (f (eraseFlag s))) :
    FlagEq impl obs (modify f : RealM C τ PUnit) (modify f) := by
  refine ⟨UsedHit.NoProg.modify f, fun s₁ s₂ hs => ObsEq.of_eq ?_⟩
  simp only [erasedRun, StateT.run_modify, map_pure]
  rw [hf s₁, hf s₂, hs]

theorem flagEq_map_get {α : Type} (f : RealState C τ → α) (hf : ∀ s, f (eraseFlag s) = f s) :
    FlagEq impl obs (f <$> (get : RealM C τ (RealState C τ))) (f <$> get) := by
  rw [map_eq_bind_pure_comp]
  refine flagEq_get_bind (fun _ => UsedHit.NoProg.pure _) fun s₁ s₂ hs => ?_
  simp only [Function.comp_apply]
  rw [← hf s₁, hs, hf s₂]
  exact (flagEq_pure _).2 s₁ s₂ hs

/-- `FlagEq` for each state of the signing game. -/
def FlagEqT {α : Type} (x y : StateT (TsigState C) (RealM C τ) α) : Prop :=
  ∀ st, FlagEq impl obs (x.run st) (y.run st)

theorem FlagEqT.bind {α α' : Type} {x y : StateT (TsigState C) (RealM C τ) α}
    {f g : α → StateT (TsigState C) (RealM C τ) α'} (hxy : FlagEqT x y (impl := impl) (obs := obs))
    (hfg : ∀ a, FlagEqT (f a) (g a) (impl := impl) (obs := obs)) (hg : ∀ a, FlagEqT (g a) (g a) (impl := impl) (obs := obs)) :
    FlagEqT (x >>= f) (y >>= g) (impl := impl) (obs := obs) := fun st => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hxy st).bind (fun p => hfg p.1 p.2) fun p => hg p.1 p.2

theorem flagEqT_pure {α : Type} (a : α) :
    FlagEqT (pure a : StateT (TsigState C) (RealM C τ) α) (pure a) (impl := impl) (obs := obs) := fun _ =>
  flagEq_pure _

theorem flagEqT_lift {α : Type} {x y : RealM C τ α} (h : FlagEq impl obs x y) :
    FlagEqT (StateT.lift x : StateT (TsigState C) (RealM C τ) α) (StateT.lift y) (impl := impl) (obs := obs) :=
  fun _ => h.bind (fun _ => flagEq_pure _) fun _ => flagEq_pure _

theorem flagEqT_simulateQ {ι : Type} {spec : OracleSpec ι} {α : Type}
    (i₁ i₂ : QueryImpl spec (StateT (TsigState C) (RealM C τ)))
    (h₁₂ : ∀ t, FlagEqT (i₁ t) (i₂ t) (impl := impl) (obs := obs))
    (h₂₂ : ∀ t, FlagEqT (i₂ t) (i₂ t) (impl := impl) (obs := obs)) (oa : OracleComp spec α) :
    FlagEqT (simulateQ i₁ oa) (simulateQ i₂ oa) (impl := impl) (obs := obs) ∧
      FlagEqT (simulateQ i₂ oa) (simulateQ i₂ oa) (impl := impl) (obs := obs) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact ⟨flagEqT_pure a, flagEqT_pure a⟩
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact ⟨(h₁₂ t).bind (fun u => (ih u).1) fun u => (ih u).2, (h₂₂ t).bind (fun u => (ih u).2) fun u => (ih u).2⟩

end Flag

/-! ## The game -/

section Game

variable {S β : Type} {impl : QueryImpl (WorldSpec C) (StateT S ProbComp)} {obs : S → β}

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

/-- A monitor that makes only free calls of `H` on `.hash` and on `.prf`. -/
def FreeMonitor (monitor : TreeMonitor C) : Prop :=
  ∀ keys tree outputs, NoCall (fun t => ¬ MonitorCall t) (monitor keys tree outputs)

theorem FreeMonitor.allQueries {monitor : TreeMonitor C} (h : FreeMonitor monitor) (keys : C.Party → Option (Keys C))
    (tree : Tree) (outputs : C.Party → Option TreeOutput) : AllQueriesSatisfy (monitor keys tree outputs) MonitorCall := by
  have h' := (noCall_iff _ _).1 (h keys tree outputs)
  rw [← isQueryBoundP_zero_iff]
  convert h'

theorem FreeMonitor.noProgram {monitor : TreeMonitor C} (h : FreeMonitor monitor) (keys : C.Party → Option (Keys C))
    (tree : Tree) (outputs : C.Party → Option TreeOutput) : NoCall WorldProgramQuery (monitor keys tree outputs) :=
  noCall_mono _ (fun t hp hm => by rcases t with (_ | _) | _ <;> simp_all [WorldProgramQuery, MonitorCall])
    (h keys tree outputs)

theorem freeMonitor_noMonitor : FreeMonitor (noMonitor : TreeMonitor C) := fun _ _ _ => noCall_pure _ _

theorem freeMonitor_wrongOutput : FreeMonitor (wrongOutput D) := fun keys tree outputs =>
  GameCount.wrongOutput_noCall D _ (fun _ ht h => h ht) keys tree outputs

theorem fields_of_eraseFlag {τ : Type} {s₁ s₂ : RealState C τ} (h : eraseFlag s₁ = eraseFlag s₂) :
    s₁.adversary = s₂.adversary ∧ s₁.operators = s₂.operators ∧ s₁.runs = s₂.runs ∧ s₁.closed = s₂.closed := by
  have h₁ := congrArg RealState.adversary h
  have h₂ := congrArg RealState.operators h
  have h₃ := congrArg RealState.runs h
  have h₄ := congrArg RealState.closed h
  exact ⟨h₁, h₂, h₃, h₄⟩

omit [Fintype E] [DecidableEq E] in
theorem flagEq_treeRun (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {M₁ M₂ : TreeMonitor C}
    (h₁ : FreeMonitor M₁) (h₂ : FreeMonitor M₂) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    FlagEq impl obs (treeRun K circuits settings M₁ D net tree) (treeRun K circuits settings M₂ D net tree) := by
  unfold treeRun
  refine flagEq_get_bind (fun s => ?_) fun s₁ s₂ hs => ?_
  · exact (UsedHit.NoProg.lift (Collision.noProgram_executePhase D net _ _ _)).bind fun r =>
      (UsedHit.NoProg.lift (h₂.noProgram _ _ _)).bind fun _ =>
        (UsedHit.NoProg.lift (Collision.noProgram_voteRound D net _ _)).bind fun _ => UsedHit.NoProg.set _
  · obtain ⟨a₁, o₁, r₁, c₁, f₁⟩ := s₁
    obtain ⟨a₂, o₂, r₂, c₂, f₂⟩ := s₂
    obtain ⟨rfl, rfl, rfl, rfl⟩ := fields_of_eraseFlag hs
    simp only [erasedRun, StateT.run_bind, StateT.run_lift, StateT.run_set, bind_assoc, pure_bind, map_bind,
      map_pure, eraseFlag]
    refine ObsEq.bind_right _ fun r => ?_
    have hV := fun (x : net.State × Bool → Unit × RealState C net.State) =>
      noCall_bind (f := fun v => (pure (x v) : OracleComp (WorldSpec C) _)) _
        (Collision.noProgram_voteRound D net r.1 fun i => (r.2 i).map (treeVote tree)) fun v => noCall_pure _ _
    exact (obsEq_monitor_drop hcomm hkeep _ (h₁.allQueries _ _ _) _ (hV _)).trans
      (obsEq_monitor_drop hcomm hkeep _ (h₂.allQueries _ _ _) _ (hV _)).symm

omit [Fintype E] [DecidableEq E] in
theorem flagEq_treeRuns (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs)
    (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count {M₁ M₂ : TreeMonitor C}, FreeMonitor M₁ → FreeMonitor M₂ →
      FlagEq impl obs (treeRuns K circuits settings runLimit M₁ D net tree count)
        (treeRuns K circuits settings runLimit M₂ D net tree count)
  | 0, _, _, _, _ => flagEq_pure ()
  | count + 1, M₁, M₂, h₁, h₂ => by
    have run₁₂ := flagEq_treeRun K circuits settings D hcomm hkeep h₁ h₂ net tree
    have run₂₂ := flagEq_treeRun K circuits settings D hcomm hkeep h₂ h₂ net tree
    have rest₁₂ := flagEq_treeRuns hcomm hkeep net tree count h₁ h₂
    have rest₂₂ := flagEq_treeRuns hcomm hkeep net tree count h₂ h₂
    unfold treeRuns
    refine flagEq_get_bind (fun s => ?_) fun s₁ s₂ hs => ?_
    · split
      · exact run₂₂.1.bind fun _ => rest₂₂.1
      · exact UsedHit.NoProg.pure _
    · have hm : mayRun runLimit D s₁ tree ↔ mayRun runLimit D s₂ tree := by
        obtain ⟨-, ho, hr, hc⟩ := fields_of_eraseFlag hs
        cases tree <;> simp only [mayRun, ho, hr, hc]
      by_cases h : mayRun runLimit D s₁ tree
      · rw [ite_eq_left h, ite_eq_left (hm.1 h)]
        exact (run₁₂.bind (fun _ => rest₁₂) fun _ => rest₂₂).2 s₁ s₂ hs
      · rw [ite_eq_right h, ite_eq_right (mt hm.2 h)]
        exact (flagEq_pure ()).2 s₁ s₂ hs

/-- The end of a request of a bottom tree reads the outputs of the operators only. -/
theorem flagEq_heldAnswer {τ : Type} (b : Fin (2 ^ layerHeight)) :
    FlagEq impl obs (get >>= fun s : RealState C τ => match heldBottom D s.operators b with
        | some tree => do
          let v ← gameValue D s.operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none)
      (get >>= fun s : RealState C τ => match heldBottom D s.operators b with
        | some tree => do
          let v ← gameValue D s.operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none) := by
  have inner : ∀ operators : C.Party → OperatorState C, FlagEq impl obs
      (match heldBottom D operators b with
        | some tree => do
          let v ← gameValue (σ := τ) D operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none)
      (match heldBottom D operators b with
        | some tree => do
          let v ← gameValue (σ := τ) D operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none) := fun operators => by
    split
    · exact (flagEq_lift (Collision.noProgram_free _)).bind (fun _ => flagEq_pure _) fun _ => flagEq_pure _
    · exact flagEq_pure _
  refine flagEq_get_bind (fun s => (inner s.operators).1) fun s₁ s₂ hs => ?_
  rw [(fields_of_eraseFlag hs).2.1]
  exact (inner s₂.operators).2 s₁ s₂ hs

omit [Fintype E] [DecidableEq E] in
theorem flagEq_treeRequest (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {M₁ M₂ : TreeMonitor C}
    (h₁ : FreeMonitor M₁) (h₂ : FreeMonitor M₂) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    FlagEq impl obs (treeRequest K circuits settings runLimit M₁ D net b)
      (treeRequest K circuits settings runLimit M₂ D net b) := by
  unfold treeRequest
  exact (flagEq_treeRuns K circuits settings runLimit D hcomm hkeep net _ 1 h₁ h₂).bind
    (fun _ => flagEq_heldAnswer D b) fun _ => flagEq_heldAnswer D b

/-- A signing request reads the outputs of the operators only and closes a bottom tree. -/
theorem flagEqT_signRequest {τ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    FlagEqT (signRequest D (σ := τ) i e q) (signRequest D (σ := τ) i e q) (impl := impl) (obs := obs) := by
  have closeT : FlagEqT (StateT.lift (modify fun s : RealState C τ =>
      { s with closed := Function.update s.closed (treeOf e) true }) : StateT (TsigState C) (RealM C τ) PUnit)
      (StateT.lift (modify fun s : RealState C τ => { s with closed := Function.update s.closed (treeOf e) true }))
      (impl := impl) (obs := obs) :=
    flagEqT_lift (flagEq_modify _ fun _ => rfl)
  have answer : ∀ st : TsigState C, FlagEq impl obs
      (get >>= fun s : RealState C τ => (operatorAnswer (m := RealM C τ) realLift (gameValue D s.operators) (s.operators i) e q).run st)
      (get >>= fun s : RealState C τ => (operatorAnswer (m := RealM C τ) realLift (gameValue D s.operators) (s.operators i) e q).run st) := by
    intro st
    refine flagEq_get_bind (fun s => ?_) fun s₁ s₂ hs => ?_
    · rw [UsedHit.operatorAnswer_eq_free]
      exact UsedHit.NoProg.lift (Collision.noProgram_free _)
    · rw [(fields_of_eraseFlag hs).2.1, UsedHit.operatorAnswer_eq_free]
      exact (flagEq_lift (Collision.noProgram_free _)).2 s₁ s₂ hs
  unfold signRequest
  refine closeT.bind (fun _ => ?_) fun _ => ?_ <;>
  · intro st
    have e : ((StateT.lift (get : RealM C τ (RealState C τ)) : StateT (TsigState C) (RealM C τ) _) >>= fun s =>
        operatorAnswer (m := RealM C τ) realLift (gameValue D s.operators) (s.operators i) e q).run st =
        get >>= fun s : RealState C τ => (operatorAnswer (m := RealM C τ) realLift (gameValue D s.operators) (s.operators i) e q).run st := by
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    rw [e]
    exact answer st

omit [Fintype E] [DecidableEq E] in
theorem flagEqT_realOracles (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {M₁ M₂ : TreeMonitor C}
    (h₁ : FreeMonitor M₁) (h₂ : FreeMonitor M₂) (A : DkgTsigAdversary C E) (q : TsigQuery C) :
    FlagEqT (realOracles K circuits settings runLimit M₁ D A q) (realOracles K circuits settings runLimit M₂ D A q)
      (impl := impl) (obs := obs) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact flagEqT_pure _
  · exact flagEqT_lift (flagEq_treeRequest K circuits settings runLimit D hcomm hkeep h₁ h₂ A.net b)
  · exact flagEqT_signRequest D i e _
  · exact flagEqT_signRequest D i e _

/-- The oracles of `forge` in `dkgSigning` with the monitor `monitor`. -/
def realForgeOracles (monitor : TreeMonitor C) (A : DkgTsigAdversary C E) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) (StateT (TsigState C) (RealM C A.net.State)) :=
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  HAdd.hAdd forger (HAdd.hAdd (realOracles K circuits settings runLimit monitor D A) cell)

omit [Fintype E] [DecidableEq E] in
theorem flagEqT_realForgeOracles (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {M₁ M₂ : TreeMonitor C}
    (h₁ : FreeMonitor M₁) (h₂ : FreeMonitor M₂) (A : DkgTsigAdversary C E) (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    FlagEqT (realForgeOracles K circuits settings runLimit D M₁ A t) (realForgeOracles K circuits settings runLimit D M₂ A t)
      (impl := impl) (obs := obs) := by
  rcases t with t | q | q
  · exact flagEqT_lift (flagEq_lift (Collision.noProgram_adversary _))
  · exact flagEqT_realOracles K circuits settings runLimit D hcomm hkeep h₁ h₂ A q
  · rcases q with _ | state
    · exact flagEqT_lift (flagEq_map_get _ fun _ => rfl)
    · exact flagEqT_lift (flagEq_modify _ fun _ => rfl)

/-- The win test reads the outputs of the operators only. -/
theorem flagEq_winTest {τ : Type} (parameter : PublicParameter) (top : TopTree) (st : TsigState C) (forgery : Forgery) :
    FlagEq impl obs
      (get >>= fun s : RealState C τ => forgeryWins realLift (canonicalDealt D s.operators parameter top) st forgery)
      (get >>= fun s : RealState C τ => forgeryWins realLift (canonicalDealt D s.operators parameter top) st forgery) := by
  refine flagEq_get_bind (fun s => ?_) fun s₁ s₂ hs => ?_
  · rw [UsedHit.forgeryWins_eq_free]
    exact UsedHit.NoProg.lift (Collision.noProgram_free _)
  · rw [(fields_of_eraseFlag hs).2.1, UsedHit.forgeryWins_eq_free]
    exact (flagEq_lift (Collision.noProgram_free _)).2 s₁ s₂ hs

omit [Fintype E] [DecidableEq E] in
theorem flagEq_dkgSigning (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {M₁ M₂ : TreeMonitor C}
    (h₁ : FreeMonitor M₁) (h₂ : FreeMonitor M₂) (A : DkgTsigAdversary C E) :
    FlagEq impl obs (dkgSigning K circuits settings runLimit M₁ D A) (dkgSigning K circuits settings runLimit M₂ D A) := by
  have sim := fun pk top => flagEqT_simulateQ _ _
    (flagEqT_realForgeOracles K circuits settings runLimit D hcomm hkeep h₁ h₂ A)
    (flagEqT_realForgeOracles K circuits settings runLimit D hcomm hkeep h₂ h₂ A) (A.forge pk top)
  unfold dkgSigning
  refine flagEq_get_bind (fun s => ?_) fun s₁ s₂ hs => ?_
  · split
    · rename_i keys top _
      exact ((sim ⟨top.root, keys.parameter⟩ top).2 _).1.bind fun p => by
        rcases p with ⟨forgery, st⟩
        exact (flagEq_winTest (impl := impl) (obs := obs) D keys.parameter top st forgery).1
    · exact UsedHit.NoProg.pure _
  · rw [(fields_of_eraseFlag hs).2.1]
    split
    · rename_i keys top _
      refine (((sim ⟨top.root, keys.parameter⟩ top).1 _).bind (fun p => ?_) fun p => ?_).2 s₁ s₂ hs
      · rcases p with ⟨forgery, st⟩
        exact flagEq_winTest D keys.parameter top st forgery
      · rcases p with ⟨forgery, st⟩
        exact flagEq_winTest D keys.parameter top st forgery
    · exact (flagEq_pure _).2 s₁ s₂ hs

omit [Fintype E] [DecidableEq E] in
/-- The erasure of a free monitor. `dkgTsigRun` with two free monitors gives one law of the win and of
`obs` of the final state of `impl`, for each continuation with no programming call. -/
theorem dkgTsigRun_obsEq (hcomm : MonitorCommutes impl) (hkeep : MonitorKeeps impl obs) {M₁ M₂ : TreeMonitor C}
    (h₁ : FreeMonitor M₁) (h₂ : FreeMonitor M₂) (A : DkgTsigAdversary C E) :
    ObsEq impl obs (Prod.fst <$> dkgTsigRun K circuits settings runLimit M₁ D A)
      (Prod.fst <$> dkgTsigRun K circuits settings runLimit M₂ D A) := by
  have body := (flagEq_treeRuns K circuits settings runLimit D hcomm hkeep A.net .top runLimit h₁ h₂).bind
    (fun _ => flagEq_dkgSigning K circuits settings runLimit D hcomm hkeep h₁ h₂ A)
    fun _ => flagEq_dkgSigning K circuits settings runLimit D hcomm hkeep h₂ h₂ A
  unfold dkgTsigRun
  simp only [map_bind]
  refine ObsEq.bind_right _ fun p => ObsEq.bind_right _ fun v => ?_
  have h := (body.2 (seedState D v.1 p.2 v.2) (seedState D v.1 p.2 v.2) rfl).map Prod.fst
  simp only [erasedRun, Functor.map_map] at h
  simpa [map_eq_bind_pure_comp] using h

end Game

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgTsigRun_obsEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dkgTsigRun_obsEq
