import ThresholdLeanXmss.Statement
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# The execution model

Lemmas that unfold the execution model of `ThresholdLeanXmss/Scheme.lean`. The module also holds the
runs with a fixed `H`, the query counting and the facts that several claim proofs share.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-! ## The local steps of a program -/

section Advance

theorem liftM_query_local (t : (LocalSpec C).Domain) :
    (liftM (OracleSpec.query t) : OracleComp (PartySpec C E G) _) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) := by
  rcases t with n | x | x <;> rfl

theorem advance_pure {α : Type} (out : Option α) :
    advance (C := C) (E := E) (G := G) (pure out) = pure (.done out) := rfl

theorem advance_query_bind {α : Type} (t : (LocalSpec C).Domain)
    (f : (LocalSpec C).Range t → OracleComp (PartySpec C E G) (Option α)) :
    advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) >>= f) =
      OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (f r) := rfl

theorem advance_liftComp_bind {α β : Type} (oa : OracleComp (LocalSpec C) β)
    (f : β → OracleComp (PartySpec C E G) (Option α)) :
    advance (liftComp oa (PartySpec C E G) >>= f) = oa >>= fun b => advance (f b) := by
  induction oa using OracleComp.inductionOn with
  | pure b => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, bind_assoc]
    have hq : ((OracleSpec.query t).cont <$> liftM (OracleSpec.query (OracleSpec.query t).input) :
        OracleComp (PartySpec C E G) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) := by
      rw [← liftM_query_local]; rfl
    rw [hq]
    refine (advance_query_bind t (fun x => (k x).liftComp (PartySpec C E G) >>= f)).trans ?_
    simp only [ih]

theorem advance_run_pure {α : Type} (a : α) :
    advance (pure a : PartyM C E G α).run = pure (.done (some a)) := rfl

theorem advance_run_failure {α : Type} :
    advance (failure : PartyM C E G α).run = pure (.done none) := rfl

theorem advance_localStep_bind {α β : Type} (oa : OracleComp (LocalSpec C) β) (f : β → PartyM C E G α) :
    advance (localStep oa >>= f).run = oa >>= fun b => advance (f b).run := by
  have : (localStep (E := E) (G := G) oa >>= f).run =
      liftComp oa (PartySpec C E G) >>= fun b => (f b).run := by
    simp [localStep, OptionT.run_bind, OptionT.lift]
  rw [this, advance_liftComp_bind]

theorem advance_oracleStep_bind {α β : Type} (oa : OracleComp (RoSpec C) β) (f : β → PartyM C E G α) :
    advance (oracleStep oa >>= f).run = liftComp oa (LocalSpec C) >>= fun b => advance (f b).run :=
  advance_localStep_bind _ f

/-- The continuation of `exchange`. It aborts on an abort frame from any operator. -/
def exchangeResume {α : Type} (f : Mail C E → PartyM C E G α) (inbox : Mail C E) :
    OracleComp (PartySpec C E G) (Option α) :=
  if C.parties.any fun j => Msg.isAbort (inbox j) then pure none else (f inbox).run

theorem advance_exchange_bind {α : Type} (outbox : Mail C E) (f : Mail C E → PartyM C E G α) :
    advance (exchange outbox >>= f).run = pure (.wait outbox (exchangeResume f)) := by
  have : (exchange (C := C) (G := G) outbox >>= f).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inr outbox))) >>=
        exchangeResume f := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind,
      Option.elimM]
    refine bind_congr fun inbox => ?_
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [this]
  rfl

theorem advance_call_bind {α : Type} (input : ι) (f : G input → PartyM C E G α) :
    advance (call input >>= f).run = pure (.call input fun r => (f r).run) := by
  have : (call (C := C) (E := E) (G := G) input >>= f).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inr input)) >>= fun r => (f r).run := by
    simp [call, OptionT.run_bind, OptionT.lift]
  rw [this]
  rfl

theorem advance_require_bind {α : Type} (c : Prop) (f : Unit → PartyM C E G α) :
    advance (require c >>= f).run = if c then advance (f ()).run else pure (.done none) := by
  unfold require
  split_ifs
  · simp
  · simp; rfl

end Advance

/-! ## Aborts -/

section Abort

variable {α : Type}

@[simp] theorem delivered_wait (outbox : Mail C E) (resume : Mail C E → OracleComp (PartySpec C E G) (Option α)) :
    (Step.wait outbox resume).delivered = outbox := rfl

@[simp] theorem delivered_done_none : (Step.done (C := C) (E := E) (G := G) (none : Option α)).delivered =
    fun _ => some .abort := rfl

@[simp] theorem delivered_done_some (a : α) : (Step.done (C := C) (E := E) (G := G) (some a)).delivered =
    fun _ => none := rfl

@[simp] theorem delivered_call (input : ι) (resume : G input → OracleComp (PartySpec C E G) (Option α)) :
    (Step.call input resume).delivered = fun _ => none := rfl

theorem exchangeResume_abort (f : Mail C E → PartyM C E G α) (inbox : Mail C E) (k : C.Party)
    (hk : inbox k = some .abort) : exchangeResume f inbox = pure none := by
  have : (C.parties.any fun j => Msg.isAbort (inbox j)) = true :=
    List.any_eq_true.mpr ⟨k, List.mem_finRange k, by simp [hk, Msg.isAbort]⟩
  simp [exchangeResume, this]

theorem advance_exchangeResume_abort (f : Mail C E → PartyM C E G α) (inbox : Mail C E) (k : C.Party)
    (hk : inbox k = some .abort) : advance (exchangeResume f inbox) = pure (.done none) := by
  rw [exchangeResume_abort f inbox k hk]
  rfl

/-- The inbox of operator `j` in a round, as `stepRound` builds it. -/
def roundInbox (D : C.Coalition) (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E G α) (j : C.Party) : Mail C E :=
  fun k => if k ∈ D.1 then sent k j else (steps k).delivered j

/-- An honest operator that aborted sends the abort frame to every operator. -/
theorem roundInbox_abort (D : C.Coalition) (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E G α) (j k : C.Party) (hk : k ∉ D.1) (habort : steps k = .done none) :
    roundInbox D sent steps j k = some .abort := by
  simp [roundInbox, hk, habort]

/-- Every operator that waits in `exchange` aborts in the round after an honest operator aborts. -/
theorem advance_roundInbox_abort (D : C.Coalition) (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E G α) (j k : C.Party) (hk : k ∉ D.1) (habort : steps k = .done none)
    (f : Mail C E → PartyM C E G α) :
    advance (exchangeResume f (roundInbox D sent steps j)) = pure (.done none) :=
  advance_exchangeResume_abort f _ k (roundInbox_abort D sent steps j k hk habort)

end Abort

/-! ## Sequences and the world -/

section World

theorem sequenceFin_bind_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} :
    ∀ {n : ℕ} (X : Fin n → m α) (h : Fin n → α → β),
    Concrete.sequenceFin (fun i => X i >>= fun r => pure (h i r)) =
      Concrete.sequenceFin X >>= fun rs => pure fun i => h i (rs i)
  | 0, X, h => by
    simp only [Concrete.sequenceFin, pure_bind]
    congr 1; funext i; exact i.elim0
  | n + 1, X, h => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    rw [sequenceFin_bind_pure (fun i : Fin n => X i.succ) (fun i => h i.succ)]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun a => bind_congr fun rs => ?_
    congr 1; funext i; cases i using Fin.cases <;> rfl

theorem sequenceFin_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ {n : ℕ} (f : Fin n → α), Concrete.sequenceFin (fun i => (pure (f i) : m α)) = pure f
  | 0, f => by
    simp only [Concrete.sequenceFin]; congr 1; funext i; exact i.elim0
  | n + 1, f => by
    simp only [Concrete.sequenceFin, pure_bind]
    rw [sequenceFin_pure (fun i : Fin n => f i.succ)]
    simp only [pure_bind]
    congr 1; funext i; cases i using Fin.cases <;> rfl

theorem simulateQ_sequenceFin {κ : Type} {spec : OracleSpec κ} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α),
    simulateQ impl (Concrete.sequenceFin f) = Concrete.sequenceFin fun i => simulateQ impl (f i)
  | 0, f => by simp [Concrete.sequenceFin]
  | n + 1, f => by
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure]
    refine bind_congr fun a => ?_
    rw [simulateQ_sequenceFin impl (fun i : Fin n => f i.succ)]

theorem mem_support_sequenceFin {α : Type} :
    ∀ {n : ℕ} (f : Fin n → ProbComp α) (x : Fin n → α), x ∈ support (Concrete.sequenceFin f) →
      ∀ i, x i ∈ support (f i)
  | 0, f, x, _ => fun i => i.elim0
  | n + 1, f, x, hx => by
    simp only [Concrete.sequenceFin, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hx
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    intro i
    cases i using Fin.cases with
    | zero => exact ha
    | succ i => exact mem_support_sequenceFin (fun i : Fin n => f i.succ) t ht i

@[simp] theorem free_pure {α : Type} (a : α) : free (C := C) (pure a) = pure a := simulateQ_pure _ _

@[simp] theorem free_bind {α β : Type} (oa : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β) :
    free (oa >>= f) = free oa >>= fun a => free (f a) := simulateQ_bind _ _ _

theorem free_sequenceFin {α : Type} {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) α) :
    free (Concrete.sequenceFin f) = Concrete.sequenceFin fun i => free (f i) :=
  simulateQ_sequenceFin _ f

variable (prims : Primitives)

/-- The world without the query count. -/
abbrev worldAnswer : QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  localAnswer (C := C) prims + programAnswer (C := C) + localAnswer (C := C) prims

theorem simulateQ_free {m : Type → Type} [Monad m] [LawfulMonad m]
    (I : QueryImpl (SimulatorSpec C) m) (J : QueryImpl (LocalSpec C) m) {α : Type}
    (oa : OracleComp (LocalSpec C) α) : simulateQ (I + J) (free oa) = simulateQ J oa := by
  rw [free, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  exact (simulateQ_query _ _).trans (id_map _)

theorem simulateQ_counted {m : Type → Type} [Monad m] [LawfulMonad m]
    (I : QueryImpl (SimulatorSpec C) m) (J : QueryImpl (LocalSpec C) m) {α : Type}
    (oa : OracleComp (SimulatorSpec C) α) : simulateQ (I + J) (counted oa) = simulateQ I oa := by
  rw [counted, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  exact (simulateQ_query _ _).trans (id_map _)

theorem fst_map_run_withAddCost {κ : Type} {spec : OracleSpec κ} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (costFn : spec.Domain → ℕ) (oa : OracleComp spec α) (s : σ) :
    (fun r => r.1) <$> (simulateQ (impl.withAddCost costFn) oa).run.run' s = (simulateQ impl oa).run' s := by
  rw [QueryImpl.withAddCost,
    ← QueryImpl.fst_map_run_withCost impl (fun t => Multiplicative.ofAdd (costFn t)) oa]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]

theorem fst_map_runWorld {α : Type} (oa : OracleComp (WorldSpec C) α) :
    (fun r => r.1) <$> runWorld prims oa = (simulateQ (worldAnswer (C := C) prims) oa).run' ∅ :=
  fst_map_run_withAddCost _ _ oa ∅

theorem world_eq_add :
    world (C := C) prims = (QueryImpl.withAddCost (localAnswer (C := C) prims + programAnswer (C := C) :
      QueryImpl (SimulatorSpec C) (StateT (HashCache C) ProbComp))
      (fun t : (SimulatorSpec C).Domain => match t with
        | .inl (.inl _) => 0
        | .inl (.inr (.inl (.hash input))) => if MpcInput input then 0 else 1
        | _ => 1) : QueryImpl (SimulatorSpec C) _) +
      (localAnswer (C := C) prims).withAddCost (fun _ => (0 : ℕ)) := by
  funext t
  rcases t with ((t | (t | t)) | t) | t
  · rfl
  · rcases t with _ | _ <;> rfl
  · rfl
  · rfl
  · rfl

theorem run_simulateQ_withAddCost_zero {κ : Type} {spec : OracleSpec κ} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) :
    (simulateQ (impl.withAddCost (fun _ => (0 : ℕ))) oa).run = (·, 1) <$> simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [WriterT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      WriterT.run_bind, ih, map_bind, QueryImpl.withAddCost_apply]
    simp [AddWriterT.addTell]

/-- The free copy costs nothing, from any cache. -/
theorem simulateQ_world_free {α : Type} (oa : OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (world prims) (free oa)).run.run s =
      (fun z => ((z.1, 1), z.2)) <$> (simulateQ (localAnswer prims) oa).run s := by
  rw [world_eq_add, simulateQ_free, run_simulateQ_withAddCost_zero, StateT.run_map]

/-- The counted copy pays the cost of the world for each of its queries, from any cache. -/
theorem simulateQ_world_counted {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    simulateQ (world prims) (counted oa) =
      simulateQ (QueryImpl.withAddCost (localAnswer (C := C) prims + programAnswer (C := C) :
        QueryImpl (SimulatorSpec C) (StateT (HashCache C) ProbComp))
        (fun t : (SimulatorSpec C).Domain => match t with
          | .inl (.inl _) => 0
          | .inl (.inr (.inl (.hash input))) => if MpcInput input then 0 else 1
          | _ => 1)) oa := by
  rw [world_eq_add, simulateQ_counted]

theorem runWorld_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    runWorld prims (free oa) = (fun a => (a, 0)) <$> (simulateQ (localAnswer prims) oa).run' ∅ := by
  unfold runWorld
  rw [StateT.run'_eq, simulateQ_world_free, StateT.run'_eq, Functor.map_map, Functor.map_map]
  rfl

end World

/-! ## The lazy random oracle

`H` reorders freely, a repeated query returns the cached answer, and the cache only grows. Each fact
holds from every starting cache. -/

section Cache

variable {σ : Type}

local notation "CacheM" => StateT σ ProbComp

/-- Two computations commute when, from every cache, the two orders give the same distribution of
the pair of results and the final cache. -/
def Commutes {α β : Type} (x : CacheM α) (y : CacheM β) : Prop :=
  ∀ s, 𝒟[(do let a ← x; let b ← y; pure (a, b)).run s] = 𝒟[(do let b ← y; let a ← x; pure (a, b)).run s]

theorem evalDist_run_bind_congr {α β : Type} (m : CacheM α) {f g : α → CacheM β}
    (h : ∀ a s, 𝒟[(f a).run s] = 𝒟[(g a).run s]) (s : σ) :
    𝒟[(m >>= f).run s] = 𝒟[(m >>= g).run s] := by
  simp only [StateT.run_bind, evalDist_bind]
  congr 1
  funext p
  exact h p.1 p.2

theorem evalDist_run_bind_of_eq {α β : Type} {m₁ m₂ : CacheM α} (f : α → CacheM β)
    (s : σ) (h : 𝒟[m₁.run s] = 𝒟[m₂.run s]) :
    𝒟[(m₁ >>= f).run s] = 𝒟[(m₂ >>= f).run s] := by
  rw [StateT.run_bind, StateT.run_bind, evalDist_bind, evalDist_bind, h]

theorem Commutes.bind {α β γ : Type} {x : CacheM α} {y : CacheM β} (h : Commutes x y)
    (k : α → β → CacheM γ) (s : σ) :
    𝒟[(do let a ← x; let b ← y; k a b).run s] = 𝒟[(do let b ← y; let a ← x; k a b).run s] := by
  have e1 : (do let a ← x; let b ← y; k a b) =
      ((do let a ← x; let b ← y; pure (a, b)) >>= fun p => k p.1 p.2) := by simp [bind_assoc]
  have e2 : (do let b ← y; let a ← x; k a b) =
      ((do let b ← y; let a ← x; pure (a, b)) >>= fun p => k p.1 p.2) := by simp [bind_assoc]
  rw [e1, e2]
  exact evalDist_run_bind_of_eq _ s (h s)

theorem Commutes.symm {α β : Type} {x : CacheM α} {y : CacheM β} (h : Commutes x y) :
    Commutes y x := fun s => (h.bind (fun a b => pure (b, a)) s).symm

theorem Commutes.map_left {α α' β : Type} {x : CacheM α} {y : CacheM β} (h : Commutes x y)
    (f : α → α') : Commutes (f <$> x) y := fun s => by
  have e1 : (do let a ← f <$> x; let b ← y; pure (a, b)) = (do let a ← x; let b ← y; pure (f a, b)) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  have e2 : (do let b ← y; let a ← f <$> x; pure (a, b)) = (do let b ← y; let a ← x; pure (f a, b)) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  rw [e1, e2]
  exact h.bind (fun a b => pure (f a, b)) s

theorem Commutes.map_right {α β β' : Type} {x : CacheM α} {y : CacheM β} (h : Commutes x y)
    (f : β → β') : Commutes x (f <$> y) := (h.symm.map_left f).symm

theorem commutes_pure {α β : Type} (x : CacheM α) (b : β) : Commutes x (pure b) := fun s => by
  have e : (do let b' ← (pure b : CacheM β); let a ← x; pure (a, b')) =
      (do let a ← x; let b' ← (pure b : CacheM β); pure (a, b')) := by
    rw [pure_bind]
    exact (bind_congr fun a => (pure_bind b fun b' => (pure (a, b') : CacheM (α × β)))).symm
  rw [e]

theorem Commutes.bind_right {α β γ : Type} {x : CacheM α} {y : CacheM β} {g : β → CacheM γ}
    (h : Commutes x y) (hg : ∀ b, Commutes x (g b)) : Commutes x (y >>= g) := fun s => by
  have e1 : (do let a ← x; let c ← y >>= g; pure (a, c)) =
      (do let a ← x; let b ← y; (g b >>= fun c => pure (a, c))) := by simp only [bind_assoc]
  have e2 : (do let c ← y >>= g; let a ← x; pure (a, c)) =
      (do let b ← y; (do let c ← g b; let a ← x; pure (a, c))) := by simp only [bind_assoc]
  rw [e1, e2, h.bind (fun a b => g b >>= fun c => pure (a, c)) s]
  exact evalDist_run_bind_congr y (fun b s' => hg b s') s

theorem Commutes.bind_left {α β γ : Type} {x : CacheM α} {f : α → CacheM β} {y : CacheM γ}
    (h : Commutes x y) (hf : ∀ a, Commutes (f a) y) : Commutes (x >>= f) y :=
  (h.symm.bind_right fun a => (hf a).symm).symm

theorem commutes_simulateQ {κ : Type} {spec : OracleSpec κ} (I : QueryImpl spec CacheM)
    (hI : ∀ t t', Commutes (I t) (I t')) {α β : Type} (oa : OracleComp spec α)
    (ob : OracleComp spec β) : Commutes (simulateQ I oa) (simulateQ I ob) := by
  have hquery : ∀ t {β : Type} (ob : OracleComp spec β), Commutes (I t) (simulateQ I ob) := by
    intro t β ob
    induction ob using OracleComp.inductionOn with
    | pure b => rw [simulateQ_pure]; exact commutes_pure (I t) b
    | query_bind t' k ih =>
        rw [simulateQ_bind, simulateQ_query]
        exact ((hI t t').map_right _).bind_right ih
  induction oa using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact (commutes_pure (simulateQ I ob) a).symm
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_query]
      exact ((hquery t ob).map_left _).bind_left ih

section RandomOracle

variable {Dom R : Type} [DecidableEq Dom] [SampleableType R]

theorem run_liftM_stateT {α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = p >>= fun a => pure (a, s) := rfl

theorem commutes_lift_lift {α β : Type} (p : ProbComp α) (q : ProbComp β) :
    Commutes (StateT.lift p : StateT σ ProbComp α) (StateT.lift q) := fun s => by
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact DeferredSampling.evalDist_bind_comm _ _ _

theorem commutes_lift_randomOracle {α : Type} (p : ProbComp α) (x : Dom) :
    Commutes (StateT.lift p : StateT (Dom →ₒ R).QueryCache ProbComp α) ((Dom →ₒ R).randomOracle x) :=
  fun s => by
  simp only [randomOracle.apply_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc,
    pure_bind, StateT.run_get]
  rcases hs : s x with _ | u
  · simp only [StateT.run_bind, StateT.run_modifyGet, bind_assoc, pure_bind]
    exact DeferredSampling.evalDist_bind_comm _ _ _
  · simp only [StateT.run_pure, pure_bind]

theorem commutes_randomOracle_randomOracle (x y : Dom) :
    Commutes ((Dom →ₒ R).randomOracle x) ((Dom →ₒ R).randomOracle y) := fun s => by
  simp only [randomOracle.apply_eq, StateT.run_bind, StateT.run_pure, bind_assoc,
    pure_bind, StateT.run_get]
  by_cases hxy : x = y
  · subst hxy
    rcases hs : s x with _ | u
    · simp only [StateT.run_bind, StateT.run_modifyGet, bind_assoc, pure_bind,
        QueryCache.cacheQuery_self, StateT.run_pure]
    · simp only [StateT.run_pure, pure_bind, hs]
  · rcases hs : s x with _ | u <;> rcases ht : s y with _ | v <;>
      simp only [StateT.run_bind, StateT.run_modifyGet, bind_assoc, pure_bind, StateT.run_pure,
        run_liftM_stateT, QueryCache.cacheQuery_of_ne _ _ hxy,
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy), hs, ht]
    rw [DeferredSampling.evalDist_bind_comm]
    simp only [show ∀ u v, (s.cacheQuery x u).cacheQuery y v = (s.cacheQuery y v).cacheQuery x u from
      fun u v => Function.update_comm hxy _ _ _]

end RandomOracle

end Cache

section LazyOracle

variable (prims : Primitives)

/-- A step of the world is a sampling that ignores the cache, or a map of one query of `H`. -/
def IsAtom {α : Type} (m : StateT (HashCache C) ProbComp α) : Prop :=
  (∃ p : ProbComp α, m = StateT.lift p) ∨
    ∃ (x : Query C) (f : HashOutput → α), m = f <$> (Query C →ₒ HashOutput).randomOracle x

theorem commutes_of_isAtom {α β : Type} {x : StateT (HashCache C) ProbComp α}
    {y : StateT (HashCache C) ProbComp β} (hx : IsAtom x) (hy : IsAtom y) : Commutes x y := by
  rcases hx with ⟨p, rfl⟩ | ⟨a, f, rfl⟩ <;> rcases hy with ⟨q, rfl⟩ | ⟨b, g, rfl⟩
  · exact commutes_lift_lift p q
  · exact (commutes_lift_randomOracle p b).map_right g
  · exact ((commutes_lift_randomOracle q a).map_right f).symm
  · exact ((commutes_randomOracle_randomOracle a b).map_left f).map_right g

theorem isAtom_pure {α : Type} (a : α) : IsAtom (pure a : StateT (HashCache C) ProbComp α) :=
  .inl ⟨pure a, StateT.ext fun s => by simp [StateT.run_lift]⟩

theorem IsAtom.map {α β : Type} {m : StateT (HashCache C) ProbComp α} (h : IsAtom m)
    (g : α → β) : IsAtom (g <$> m) := by
  rcases h with ⟨p, rfl⟩ | ⟨x, f, rfl⟩
  · exact .inl ⟨g <$> p, StateT.ext fun s => by simp [StateT.run_lift]⟩
  · exact .inr ⟨x, g ∘ f, by rw [Functor.map_map]; rfl⟩

/-- The inputs of `H` that the fixed function `Th` answers. -/
def IsFixed (q : Query C) : Prop := ∃ input, q = .hash input ∧ MpcInput input

theorem hashAnswer_of_isFixed {input : HashInput} (h : MpcInput input) :
    hashAnswer (C := C) prims (.hash input) = pure (prims.Th input) := by
  simp [hashAnswer, h]

theorem hashAnswer_of_not_isFixed {q : Query C} (h : ¬ IsFixed q) :
    hashAnswer prims q = (Query C →ₒ HashOutput).randomOracle q := by
  cases q with
  | hash input =>
    have : ¬ MpcInput input := fun hm => h ⟨input, rfl, hm⟩
    simp [hashAnswer, this]
  | _ => rfl

theorem isAtom_hashAnswer (q : Query C) : IsAtom (hashAnswer prims q) := by
  by_cases h : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := h
    rw [hashAnswer_of_isFixed prims hm]
    exact isAtom_pure _
  · rw [hashAnswer_of_not_isFixed prims h]
    exact .inr ⟨q, id, (id_map _).symm⟩

theorem isAtom_localAnswer (t : (LocalSpec C).Domain) : IsAtom (localAnswer (C := C) prims t) := by
  rcases t with n | x | x
  · exact .inl ⟨_, rfl⟩
  · exact isAtom_hashAnswer prims x
  · have h := (isAtom_hashAnswer prims (.streamKey (C := C) x.2.1)).map
      (fun d => prims.aes.eval (truncateHash d) x.2.2)
    rw [map_eq_bind_pure_comp] at h
    exact h

/-- Two computations are the same in the world when, from every cache, they give the same
distribution of the result and the final cache. -/
def SameRun {α : Type} (oa ob : OracleComp (LocalSpec C) α) : Prop :=
  ∀ s, 𝒟[(simulateQ (localAnswer prims) oa).run s] = 𝒟[(simulateQ (localAnswer prims) ob).run s]

/-- Lazy sampling. Two computations in the local oracles commute in distribution. -/
theorem sameRun_swap {α β γ : Type} (oa : OracleComp (LocalSpec C) α) (ob : OracleComp (LocalSpec C) β)
    (k : α → β → OracleComp (LocalSpec C) γ) :
    SameRun prims (do let a ← oa; let b ← ob; k a b) (do let b ← ob; let a ← oa; k a b) := by
  intro s
  simp only [simulateQ_bind]
  exact (commutes_simulateQ _ (fun t t' => commutes_of_isAtom (isAtom_localAnswer prims t)
    (isAtom_localAnswer prims t')) oa ob).bind _ s

theorem SameRun.refl {α : Type} (oa : OracleComp (LocalSpec C) α) : SameRun prims oa oa := fun _ => rfl

variable {prims}

theorem SameRun.symm {α : Type} {oa ob : OracleComp (LocalSpec C) α} (h : SameRun prims oa ob) :
    SameRun prims ob oa := fun s => (h s).symm

theorem SameRun.trans {α : Type} {oa ob oc : OracleComp (LocalSpec C) α} (h : SameRun prims oa ob)
    (h' : SameRun prims ob oc) : SameRun prims oa oc := fun s => (h s).trans (h' s)

theorem SameRun.bind {α β : Type} {oa ob : OracleComp (LocalSpec C) α} {f g : α → OracleComp (LocalSpec C) β}
    (h : SameRun prims oa ob) (hfg : ∀ a, SameRun prims (f a) (g a)) : SameRun prims (oa >>= f) (ob >>= g) :=
  fun s => by
  simp only [simulateQ_bind, StateT.run_bind, evalDist_bind]
  rw [h s]
  congr 1
  funext p
  exact hfg p.1 p.2

theorem SameRun.of_eq {α : Type} {oa ob : OracleComp (LocalSpec C) α} (h : oa = ob) : SameRun prims oa ob :=
  h ▸ SameRun.refl prims oa

theorem SameRun.bind_right {α β : Type} (oa : OracleComp (LocalSpec C) α) {f g : α → OracleComp (LocalSpec C) β}
    (hfg : ∀ a, SameRun prims (f a) (g a)) : SameRun prims (oa >>= f) (oa >>= g) :=
  (SameRun.refl prims oa).bind hfg

theorem SameRun.map {α β : Type} {oa ob : OracleComp (LocalSpec C) α} (h : SameRun prims oa ob) (f : α → β) :
    SameRun prims (f <$> oa) (f <$> ob) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind fun a => SameRun.refl prims _

/-- Equal runs from the empty cache give equal outputs. -/
theorem SameRun.run'_eq {α : Type} {oa ob : OracleComp (LocalSpec C) α} (h : SameRun prims oa ob) :
    𝒟[(simulateQ (localAnswer prims) oa).run' ∅] = 𝒟[(simulateQ (localAnswer prims) ob).run' ∅] := by
  simp only [StateT.run'_eq, evalDist_map, h ∅]

variable (prims)

/-- The steps of `n` operators reorder in distribution, each with its own continuation. -/
theorem sameRun_sequenceFin_dep {β₁ β₂ γ : Type} :
    ∀ {n : ℕ} (A : Fin n → OracleComp (LocalSpec C) β₁) (B : Fin n → β₁ → OracleComp (LocalSpec C) β₂)
      (m : Fin n → β₁ → β₂ → γ),
    SameRun prims (Concrete.sequenceFin fun j => do let u ← A j; let v ← B j u; pure (m j u v))
      (do
        let x ← Concrete.sequenceFin A
        let y ← Concrete.sequenceFin fun j => B j (x j)
        pure fun j => m j (x j) (y j))
  | 0, A, B, m => by
      simp only [Concrete.sequenceFin, pure_bind]
      have : (fun j : Fin 0 => m j (Fin.elim0 j) (Fin.elim0 j)) = Fin.elim0 := funext fun j => j.elim0
      rw [this]
      exact SameRun.refl _ _
  | n + 1, A, B, m => by
      simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
      refine SameRun.bind_right (A 0) fun u => ?_
      refine (SameRun.bind_right (B 0 u) fun v =>
        (sameRun_sequenceFin_dep (fun i : Fin n => A i.succ) (fun i => B i.succ)
          (fun i => m i.succ)).bind fun t => SameRun.refl _ _).trans ?_
      simp only [bind_assoc, pure_bind]
      refine (sameRun_swap prims (B 0 u) (Concrete.sequenceFin fun i : Fin n => A i.succ) _).trans ?_
      refine SameRun.bind_right _ fun x => ?_
      simp only [Fin.cases_zero, Fin.cases_succ]
      refine SameRun.bind_right _ fun v => SameRun.bind_right _ fun y => ?_
      have : (Fin.cases (m 0 u v) fun j => m j.succ (x j) (y j) : Fin (n + 1) → γ) =
          fun j => m j (Fin.cases u x j) (Fin.cases v y j) := by
        funext j
        cases j using Fin.cases <;> rfl
      rw [this]
      exact SameRun.refl _ _

/-- A cached input of a random-oracle domain returns its cached answer and keeps the cache. -/
theorem hashAnswer_run_cached {q : Query C} (h : ¬ IsFixed q) {s : HashCache C} {u : HashOutput}
    (hs : s q = some u) : (hashAnswer prims q).run s = pure (u, s) := by
  rw [hashAnswer_of_not_isFixed prims h, OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs]

/-- After a query of a random-oracle domain, the cache holds its answer. -/
theorem hashAnswer_cached {q : Query C} (h : ¬ IsFixed q) (s : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run s), z.2 q = some z.1 := by
  rw [hashAnswer_of_not_isFixed prims h, OracleSpec.randomOracle]
  rcases hs : s q with _ | u
  · rw [QueryImpl.withCaching_run_none _ hs]
    intro z hz
    rw [support_map] at hz
    obtain ⟨v, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_self _ _ _
  · rw [QueryImpl.withCaching_run_some _ hs]
    intro z hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs

/-- A repeated query of `H` returns the first answer. -/
theorem hashAnswer_dup (q : Query C) {γ : Type}
    (f : HashOutput → HashOutput → StateT (HashCache C) ProbComp γ) :
    (hashAnswer prims q >>= fun a => hashAnswer prims q >>= fun b => f a b) =
      hashAnswer prims q >>= fun a => f a a := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    simp [hashAnswer_of_isFixed prims hm]
  · rw [hashAnswer_of_not_isFixed prims hq]
    refine StateT.ext fun s => ?_
    rcases hs : s q with _ | u
    · simp only [StateT.run_bind]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs]
      simp only [bind_map_left]
      refine bind_congr fun a => ?_
      rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _)]
      simp
    · simp only [StateT.run_bind]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs]
      simp [hs]

theorem simulateQ_localAnswer_liftComp {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (localAnswer (C := C) prims) (liftComp oa (LocalSpec C)) =
      simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, simulateQ_bind]
    simp only [ih]
    congr 1

theorem simulateQ_localAnswer_hash (q : Query C) :
    simulateQ (localAnswer (C := C) prims)
      (liftComp (hashQuery q) (LocalSpec C)) = hashAnswer prims q := by
  rw [simulateQ_localAnswer_liftComp, hashQuery]
  exact (simulateQ_query _ _).trans (id_map _)

theorem sameRun_hash_dup (q : Query C) {γ : Type}
    (k : HashOutput → HashOutput → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (liftComp (hashQuery q) (LocalSpec C) >>= fun a => liftComp (hashQuery q) (LocalSpec C) >>= fun b => k a b)
      (liftComp (hashQuery q) (LocalSpec C) >>= fun a => k a a) := fun s => by
  simp only [simulateQ_bind, simulateQ_localAnswer_hash]
  rw [hashAnswer_dup]

/-- A query of `H` after a computation `m` returns the answer of the same query before `m`. -/
theorem sameRun_hash_dup_after (q : Query C) {β γ : Type} (m : OracleComp (LocalSpec C) β)
    (k : HashOutput → β → HashOutput → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (liftComp (hashQuery q) (LocalSpec C) >>= fun a => m >>= fun y =>
        liftComp (hashQuery q) (LocalSpec C) >>= fun b => k a y b)
      (liftComp (hashQuery q) (LocalSpec C) >>= fun a => m >>= fun y => k a y a) :=
  (SameRun.bind_right _ fun a => sameRun_swap prims m (liftComp (hashQuery q) (LocalSpec C)) (k a)).trans
    (sameRun_hash_dup prims q fun a b => m >>= fun y => k a y b)

/-- An implementation whose steps only add entries to the cache. -/
def Grows {κ : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (StateT (HashCache C) ProbComp)) : Prop :=
  ∀ t s, ∀ z ∈ support ((impl t).run s), s ≤ z.2

theorem Grows.simulateQ {κ : Type} {spec : OracleSpec κ} {impl : QueryImpl spec (StateT (HashCache C) ProbComp)}
    (h : Grows impl) {α : Type} (oa : OracleComp spec α) :
    ∀ s, ∀ z ∈ support ((simulateQ impl oa).run s), s ≤ z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact (h t s p hp).trans (ih p.1 p.2 z hz)

theorem grows_hashAnswer : Grows (hashAnswer (C := C) prims) := by
  intro q s z hz
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  · rw [hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle] at hz
    rcases hs : s q with _ | u
    · rw [QueryImpl.withCaching_run_none _ hs, support_map] at hz
      obtain ⟨v, -, rfl⟩ := hz
      exact QueryCache.le_cacheQuery _ hs
    · rw [QueryImpl.withCaching_run_some _ hs, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_rfl

theorem grows_localAnswer : Grows (localAnswer (C := C) prims) := by
  rintro (n | q | x) s z hz
  · simp [localAnswer, unifFwdImpl] at hz
    obtain ⟨_, rfl⟩ := hz
    exact le_rfl
  · exact grows_hashAnswer prims q s z hz
  · simp [localAnswer, prgAnswer] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact grows_hashAnswer prims _ s p hp

theorem grows_programAnswer : Grows (programAnswer (C := C)) := by
  intro x s z hz
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    have : (s x.1).isNone := by simp_all
    exact QueryCache.le_cacheQuery _ (Option.isNone_iff_eq_none.mp this)

theorem grows_worldAnswer : Grows (worldAnswer (C := C) prims) := by
  rintro ((t | t) | t)
  · exact grows_localAnswer prims t
  · exact grows_programAnswer t
  · exact grows_localAnswer prims t

end LazyOracle

/-! ## The honest network

With no corrupt operator and the honest adversary, an execution is one computation in the local
oracles on the free copy. -/

section Honest

variable {I O L R α : Type}

@[simp] theorem noCoalition_val : (noCoalition (C := C)).1 = ∅ := rfl

/-- The local oracles answer themselves, and each leak gets the reply `reply`. -/
def replyImpl (reply : L → R) : QueryImpl (LocalSpec C + (L →ₒ R)) (OracleComp (LocalSpec C)) :=
  (fun (t : (LocalSpec C).Domain) => OracleComp.lift (OracleSpec.query t)) + fun (l : L) => (pure (reply l) : OracleComp (LocalSpec C) R)

/-- A functionality in an honest run. -/
def honestFunctionality (F : Functionality C I O L R) (reply : L → R) (inputs : C.Party → Option I) :
    OracleComp (LocalSpec C) (C.Party → Option O) :=
  if ¬ ∀ i, (inputs i).isSome then pure fun _ => none else
    simulateQ (replyImpl reply) (F.run noCoalition inputs)

/-- One step of the honest network, which is `stepRound` with no corrupt operator. -/
def honestStep (F : Functionality C I O L R) (reply : L → R) (steps : C.Party → Step C E (CallSpec I O) α) :
    OracleComp (LocalSpec C) (C.Party → Step C E (CallSpec I O) α) :=
  if (∃ i, (steps i).callInput.isSome) ∧ ∀ i, (steps i).callInput.isSome ∨ (steps i).isDone then do
    let outputs ← honestFunctionality F reply fun i => (steps i).callInput
    Concrete.sequenceFin fun j => match steps j with
      | .call _ resume => advance (resume (outputs j))
      | step => pure step
  else
    Concrete.sequenceFin fun j => match steps j with
      | .done out => pure (Step.done out)
      | .wait _ resume => advance (resume fun k => (steps k).delivered j)
      | .call _ _ => pure (Step.done none)

/-- At most `fuel` steps of the honest network. -/
def honestRounds (F : Functionality C I O L R) (reply : L → R) :
    ℕ → (C.Party → Step C E (CallSpec I O) α) → OracleComp (LocalSpec C) (C.Party → Option α)
  | 0, steps => pure fun i => (steps i).output
  | fuel + 1, steps =>
    if ∀ i, (steps i).isDone then pure fun i => (steps i).output else
      honestStep F reply steps >>= honestRounds F reply fuel

/-- The first steps of the honest programs. -/
def honestStart (program : C.Party → PartyM C E (CallSpec I O) α) :
    OracleComp (LocalSpec C) (C.Party → Step C E (CallSpec I O) α) :=
  Concrete.sequenceFin fun i => advance (program i).run

/-- A stateful implementation that answers each query on the free copy and each leak with `reply`,
and keeps its state, runs `replyImpl reply` on the free copy. -/
theorem simulateQ_run_of_reply (reply : L → R) {σ : Type} (st : σ)
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (hl : ∀ t, (impl (.inl t)).run st = (fun a => (a, st)) <$> free (replyImpl reply (.inl t)))
    (hr : ∀ l, (impl (.inr l)).run st = (fun a => (a, st)) <$> free (replyImpl reply (.inr l)))
    {β : Type} (oa : OracleComp (LocalSpec C + (L →ₒ R)) β) :
    (simulateQ impl oa).run st = (fun b => (b, st)) <$> free (simulateQ (replyImpl reply) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, free_bind]
    rcases t with t | l
    · rw [hl, bind_map_left, map_bind]
      exact bind_congr fun a => ih a
    · rw [hr, bind_map_left, map_bind]
      exact bind_congr fun a => ih a

/-- `runFunctionality` with the honest adversary runs the functionality on the free copy. -/
theorem runFunctionality_honest {Ia : Type} (F : Functionality C I O L R) (reply : L → R)
    (state : (honestAdversary (C := C) (E := E) (I := Ia) reply).State) (inputs : C.Party → Option I) :
    runFunctionality worldRoles noCoalition (honestAdversary (E := E) (I := Ia) reply) F state inputs =
      (fun o => (state, o)) <$> free (honestFunctionality F reply inputs) := by
  unfold runFunctionality honestFunctionality
  by_cases h : ∀ i, (inputs i).isSome
  · simp only [noCoalition_val, Finset.notMem_empty, not_false_eq_true, forall_const, h, implies_true,
      not_true_eq_false, if_false]
    rw [simulateQ_run_of_reply _ _ _ ?_ ?_]
    · simp only [map_bind, Functor.map_map, bind_map_left]
      rfl
    · intro t
      exact (map_eq_bind_pure_comp (m := OracleComp (WorldSpec C)) _ _).symm
    · intro l
      show (fun a => (a.2, a.1)) <$> worldRoles.adversary (pure ((), reply l)) =
        (fun a => (a, ())) <$> free (pure (reply l))
      simp only [worldRoles, counted, liftComp_pure, map_pure, free_pure]
      rfl
  · simp [h]

variable {Ia : Type}

@[simp] theorem worldRoles_adversary_pure {β : Type} (b : β) : (worldRoles (C := C)).adversary (pure b) = pure b :=
  rfl

@[simp] theorem worldRoles_honest {β : Type} (oa : OracleComp (LocalSpec C) β) :
    (worldRoles (C := C)).honest oa = free oa := rfl

@[simp] theorem honestAdversary_round (reply : L → R) (state : (honestAdversary (C := C) (E := E) (I := Ia) reply).State)
    (sent : C.Party → C.Party → Option (Msg E)) :
    (honestAdversary (C := C) (E := E) (I := Ia) reply).round state sent = pure ((), fun _ _ => none) := rfl

/-- One step with the honest adversary is one step of the honest network on the free copy. -/
theorem stepRound_honest (F : Functionality C I O L R) (reply : L → R)
    (state : (honestAdversary (C := C) (E := E) (I := Ia) reply).State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    stepRound worldRoles noCoalition (honestAdversary (I := Ia) reply) F state steps =
      (fun s => (state, s, fun _ _ => none)) <$> free (honestStep F reply steps) := by
  unfold stepRound honestStep
  by_cases h : (∃ i, (steps i).callInput.isSome) ∧ ∀ i, (steps i).callInput.isSome ∨ (steps i).isDone
  · rw [if_pos (by simpa using h), if_pos h]
    simp only [noCoalition_val, Finset.notMem_empty, if_false]
    rw [runFunctionality_honest]
    simp only [free_bind, free_sequenceFin, map_bind, bind_map_left]
    refine bind_congr fun outputs => ?_
    rw [map_eq_bind_pure_comp]
    congr 2
    funext j
    cases steps j <;> rfl
  · rw [if_neg (by simpa using h), if_neg h]
    simp only [honestAdversary_round, free_sequenceFin, noCoalition_val, Finset.notMem_empty, if_false]
    erw [worldRoles_adversary_pure, pure_bind]
    rw [map_eq_bind_pure_comp]
    congr 2
    funext j
    cases steps j <;> rfl

/-- The honest execution is the honest network on the free copy. -/
theorem executeRounds_honest (F : Functionality C I O L R) (reply : L → R)
    (state : (honestAdversary (C := C) (E := E) (I := Ia) reply).State) :
    ∀ (fuel : ℕ) (steps : C.Party → Step C E (CallSpec I O) α),
    executeRounds worldRoles noCoalition (honestAdversary (I := Ia) reply) F fuel state steps =
      (fun o => (state, o)) <$> free (honestRounds F reply fuel steps)
  | 0, steps => by simp [executeRounds, honestRounds]
  | fuel + 1, steps => by
    unfold executeRounds honestRounds
    by_cases h : ∀ i, (steps i).isDone
    · rw [if_pos (by simpa using h), if_pos h]
      simp
    · rw [if_neg (by simpa using h), if_neg h, stepRound_honest]
      simp only [bind_map_left, free_bind, map_bind]
      exact bind_congr fun steps' => executeRounds_honest F reply state fuel steps'

theorem startSteps_honest (program : C.Party → PartyM C E (CallSpec I O) α) :
    startSteps worldRoles noCoalition program = free (honestStart program) := by
  simp [startSteps, honestStart, free_sequenceFin]

/-- The real execution with no corrupt operator and the honest adversary. -/
theorem realExecution_honest {Ih Oh Lh Rh : Type} (Fh : Functionality C Ih Oh Lh Rh) (replyH : Lh → Rh)
    (fuel : ℕ) (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O) (x : C.Party → I) :
    realExecution noCoalition (honestAdversary replyH) Fh fuel program x [] =
      (fun o => ((), o)) <$> free (honestStart (fun i => program i (x i)) >>= honestRounds Fh replyH fuel) := by
  unfold realExecution executePhase
  rw [startSteps_honest]
  simp only [free_bind, map_bind]
  exact (pure_bind _ _).trans (bind_congr fun steps => executeRounds_honest Fh replyH () fuel steps)

/-- The ideal execution with no corrupt operator and the honest simulator. -/
theorem idealExecution_honest (F : Functionality C I O L R) (reply : L → R) (x : C.Party → I) :
    idealExecution (fun oa => oa) noCoalition F (honestSimulator (S := WorldSpec C) reply) x [] =
      (fun o => ((), o)) <$> free (simulateQ (replyImpl reply) (F.run noCoalition fun i => some (x i))) := by
  unfold idealExecution
  simp only [noCoalition_val, Finset.notMem_empty, if_false]
  erw [pure_bind]
  rw [simulateQ_run_of_reply reply _ _ ?_ ?_]
  · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
    exact bind_congr fun o => pure_bind _ _
  · intro t
    exact (map_eq_bind_pure_comp (m := OracleComp (WorldSpec C)) _ _).symm
  · intro l
    rfl

/-- The honest outputs of a computation on the free copy, from the empty cache. -/
theorem snd_map_runWorld_free {σ' β : Type} (g : β → σ' × (C.Party → Option O)) (prims : Primitives)
    (oa : OracleComp (LocalSpec C) β) :
    (fun r => r.1.2) <$> runWorld prims (g <$> free oa) =
      (fun b => (g b).2) <$> (simulateQ (localAnswer prims) oa).run' ∅ := by
  calc (fun r => r.1.2) <$> runWorld prims (g <$> free oa)
      = Prod.snd <$> ((fun r => r.1) <$> runWorld prims (g <$> free oa)) := by rw [Functor.map_map]
    _ = _ := by
      rw [fst_map_runWorld, simulateQ_map, simulateQ_free]
      simp [StateT.run'_eq, Functor.map_map]

/-- The two sides of `Completes` as runs in the local oracles from the empty cache. -/
theorem completes_iff {Ih Oh Lh Rh : Type} (prims : Primitives)
    (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O) (fuel : ℕ) (Fh : Functionality C Ih Oh Lh Rh)
    (replyH : Lh → Rh) (F : Functionality C I O L R) (reply : L → R)
    (valid : C.Coalition → (C.Party → I) → Prop) (ε : ℝ) :
    Completes prims program fuel Fh replyH F reply valid ε ↔
      ∀ x : C.Party → I, valid noCoalition x →
        tvDist ((simulateQ (localAnswer prims)
            (honestStart (fun i => program i (x i)) >>= honestRounds Fh replyH fuel)).run' ∅)
          ((simulateQ (localAnswer prims)
            (simulateQ (replyImpl reply) (F.run noCoalition fun i => some (x i)))).run' ∅) ≤ ε := by
  unfold Completes
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [realExecution_honest, idealExecution_honest, snd_map_runWorld_free]
  erw [snd_map_runWorld_free]
  simp

/-- With no call, an honest step is one round, and each waiting operator reads what the others
deliver. -/
theorem honestStep_of_no_call (F : Functionality C I O L R) (reply : L → R)
    (steps : C.Party → Step C E (CallSpec I O) α) (h : ∀ i, (steps i).callInput = none) :
    honestStep F reply steps = Concrete.sequenceFin fun j => match steps j with
      | .done out => pure (Step.done out)
      | .wait _ resume => advance (resume fun k => (steps k).delivered j)
      | .call _ _ => pure (Step.done none) := by
  unfold honestStep
  rw [if_neg]
  rintro ⟨⟨i, hi⟩, -⟩
  simp [h i] at hi

/-- On the real network no operator calls a functionality. -/
theorem callInput_real (step : Step C E RealSpec α) : step.callInput = none := by
  cases step with
  | call input _ => exact input.elim
  | _ => rfl

/-- When every operator is done, the honest network returns the outputs for every fuel. -/
theorem honestRounds_done (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (steps : C.Party → Step C E (CallSpec I O) α) (h : ∀ i, (steps i).isDone) :
    honestRounds F reply fuel steps = pure fun i => (steps i).output := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [honestRounds, h]

theorem honestRounds_succ (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (steps : C.Party → Step C E (CallSpec I O) α) (h : ¬ ∀ i, (steps i).isDone) :
    honestRounds F reply (fuel + 1) steps = honestStep F reply steps >>= honestRounds F reply fuel := by
  simp [honestRounds, h]

/-- With no corrupt operator, the inbox of a round is what the operators deliver. -/
theorem roundInbox_noCoalition (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E G α) (j : C.Party) :
    roundInbox noCoalition sent steps j = fun k => (steps k).delivered j := by
  funext k
  simp [roundInbox]

/-- An inbox with no abort frame passes the check of `exchange`. -/
theorem exchangeResume_of_no_abort (f : Mail C E → PartyM C E G α) (inbox : Mail C E)
    (h : ∀ k, Msg.isAbort (inbox k) = false) : exchangeResume f inbox = (f inbox).run := by
  have : (C.parties.any fun j => Msg.isAbort (inbox j)) = false := by simp [h]
  simp [exchangeResume, this]

/-- A round of operators that all wait in `exchange`. Each one resumes with the messages to it. -/
theorem honestStep_exchange (F : Functionality C I O L R) (reply : L → R) (outbox : C.Party → Mail C E)
    (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α) :
    honestStep F reply (fun i => .wait (outbox i) (exchangeResume (f i))) =
      Concrete.sequenceFin fun j => advance (exchangeResume (f j) fun k => outbox k j) :=
  honestStep_of_no_call F reply _ fun _ => rfl

end Honest

/-! ## Identical until bad

Two implementations that agree on every state outside a bad set, where the bad set is closed under
both, are within the probability of the bad set. -/

section Coupling

variable {κ : Type} {spec : OracleSpec κ} {σ α : Type}

theorem probOutput_simulateQ_run_eq_zero_of_bad (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (h_mono : ∀ t s, bad s → ∀ x ∈ support ((impl t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀) (x : α) (s : σ) (hs : ¬ bad s) :
    Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff, not_and]
    rintro rfl rfl
    exact hs h_bad
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, probOutput_eq_zero_iff, support_bind, Set.mem_iUnion, exists_prop,
      Prod.exists, not_exists, not_and]
    intro u s' h_mem
    rw [← probOutput_eq_zero_iff]
    exact ih u s' (h_mono t s₀ h_bad (u, s') h_mem)

theorem probOutput_simulateQ_run_eq_of_not_bad (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) (h_agree : ∀ t s, ¬ bad s → 𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    (h_mono₁ : ∀ t s, bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ t s, bad s → ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬ bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] = Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a => rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ _ s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ _ s₀ h_bad x s hs]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr fun p => ?_
      rw [ih p.1 p.2]
      congr 1
      simp only [probOutput_def, h_agree t s₀ h_bad]

theorem probEvent_simulateQ_run_bad_eq (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) (h_agree : ∀ t s, ¬ bad s → 𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    (h_mono₁ : ∀ t s, bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ t s, bad s → ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] = Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  classical
  have hnot : Pr[fun x => ¬ (bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] =
      Pr[fun x => ¬ (bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    refine tsum_congr fun p => ?_
    split_ifs with h
    · rfl
    · exact probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀ p.1 p.2 h
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  simp only [probFailure_eq_zero, tsub_zero] at h1 h2
  have hne : Pr[fun x => ¬ (bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
  rw [hnot] at h1
  exact (ENNReal.add_left_inj hne).mp (h1.trans h2.symm)

/-- The fundamental lemma of game playing for implementations into `StateT σ ProbComp`. Outside the
bad set, the two implementations give the same distribution at each step. -/
theorem tvDist_simulateQ_le_probEvent_bad (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) (oa : OracleComp spec α) (s₀ : σ)
    (h_agree : ∀ t s, ¬ bad s → 𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    (h_mono₁ : ∀ t s, bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ t s, bad s → ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤
      Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  refine le_trans ?_ (tvDist_le_probEvent_of_probOutput_eq_of_not (bad ∘ Prod.snd)
    (fun p hp => probOutput_simulateQ_run_eq_of_not_bad impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀
      p.1 p.2 hp)
    (probEvent_simulateQ_run_bad_eq impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀))
  rw [StateT.run'_eq, StateT.run'_eq]
  exact tvDist_map_le Prod.fst _ _

/-- Two games whose good parts accept with the same probability differ by at most the larger
probability of their bad events. -/
theorem abs_probEvent_sub_le_of_eq_until_bad {β γ : Type} (mx : ProbComp β) (my : ProbComp γ)
    (A bad₁ : β → Prop) (B bad₂ : γ → Prop)
    (h : Pr[fun a => A a ∧ ¬ bad₁ a | mx] = Pr[fun b => B b ∧ ¬ bad₂ b | my]) :
    |Pr[A | mx].toReal - Pr[B | my].toReal| ≤ max Pr[bad₁ | mx].toReal Pr[bad₂ | my].toReal := by
  have split : ∀ {δ : Type} (mz : ProbComp δ) (P bad : δ → Prop),
      Pr[fun a => P a ∧ ¬ bad a | mz].toReal ≤ Pr[P | mz].toReal ∧
        Pr[P | mz].toReal ≤ Pr[fun a => P a ∧ ¬ bad a | mz].toReal + Pr[bad | mz].toReal := by
    intro δ mz P bad
    constructor
    · exact ENNReal.toReal_mono probEvent_ne_top (probEvent_mono fun a _ ha => ha.1)
    · rw [← ENNReal.toReal_add probEvent_ne_top probEvent_ne_top]
      refine ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) ?_
      refine le_trans (probEvent_mono fun a _ ha => ?_) (probEvent_or_le mz _ bad)
      by_cases hb : bad a
      · exact Or.inr hb
      · exact Or.inl ⟨ha, hb⟩
  obtain ⟨hA₁, hA₂⟩ := split mx A bad₁
  obtain ⟨hB₁, hB₂⟩ := split my B bad₂
  rw [h] at hA₁ hA₂
  rw [abs_le]
  constructor <;> linarith [le_max_left Pr[bad₁ | mx].toReal Pr[bad₂ | my].toReal,
    le_max_right Pr[bad₁ | mx].toReal Pr[bad₂ | my].toReal]

theorem runWorld_map {β γ : Type} (prims : Primitives) (f : β → γ) (oa : OracleComp (WorldSpec C) β) :
    runWorld prims (f <$> oa) = (fun r => (f r.1, r.2)) <$> runWorld prims oa := by
  simp only [runWorld, simulateQ_map, StateT.run'_eq, WriterT.run_map, StateT.run_map, Functor.map_map]
  erw [Functor.map_map]
  rfl

/-- Identical until bad in the world. Each game outputs its decision and a bad flag. When the two
games output `true` with no bad flag with the same probability, their acceptance differs by at most
the larger probability of the bad flag. -/
theorem abs_accepts_sub_le_of_eq_until_bad (prims : Primitives) (oa ob : OracleComp (WorldSpec C) (Bool × Bool))
    (h : Pr[fun r => r.1 = (true, false) | runWorld prims oa] = Pr[fun r => r.1 = (true, false) | runWorld prims ob]) :
    |accepts prims (Prod.fst <$> oa) - accepts prims (Prod.fst <$> ob)| ≤
      max Pr[fun r => r.1.2 = true | runWorld prims oa].toReal Pr[fun r => r.1.2 = true | runWorld prims ob].toReal := by
  unfold accepts
  rw [runWorld_map, runWorld_map, probEvent_map, probEvent_map]
  refine abs_probEvent_sub_le_of_eq_until_bad _ _ _ _ _ _ ?_
  convert h using 2 <;> funext r <;> simp [Prod.ext_iff]

end Coupling

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ### Runs with a fixed `H`

Every run of a local computation is a possible run with `H` fixed to any `h` that
agrees with the final cache. -/

section Fixed

variable {C : Committee} (prims : Primitives)

/-- The oracles with `H` fixed to `h`. -/
def fixedImpl (h : Query C → HashOutput) : QueryImpl (RoSpec C) Id :=
  (fun (q : Query C) => (pure (h q) : Id HashOutput)) +
    (fun (x : PrgInput C) => (pure (prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2) : Id Bit))

/-- A computation with `H` fixed to `h`. -/
def D (h : Query C → HashOutput) {α : Type} (oa : OracleComp (RoSpec C) α) : α :=
  Id.run (simulateQ (fixedImpl prims h) oa)

/-- The local oracles with `H` fixed to `h`, and private sampling. -/
def fixedLocal (h : Query C → HashOutput) : QueryImpl (LocalSpec C) ProbComp :=
  ((fun n => OracleComp.lift (OracleSpec.query (spec := unifSpec) n)) : QueryImpl unifSpec ProbComp) +
    ((fun t => pure (fixedImpl prims h t)) : QueryImpl (RoSpec C) ProbComp)

/-- `h` is `Th` on the inputs that the MPC evaluates. -/
def Good (h : Query C → HashOutput) : Prop := ∀ x, MpcInput x → h (.hash x) = prims.Th x

def Agrees (h : Query C → HashOutput) (s : HashCache C) : Prop := ∀ q v, s q = some v → h q = v

def NoMpc (s : HashCache C) : Prop := ∀ x, MpcInput x → s (.hash x) = none

/-- The cache as a function, with `Th` on the inputs that the MPC evaluates. -/
def hashOf (s : HashCache C) : Query C → HashOutput := fun q =>
  match q with
  | .hash x => if MpcInput x then prims.Th x else (s q).getD 0
  | q => (s q).getD 0

theorem good_hashOf (s : HashCache C) : Good prims (hashOf prims s) := fun x hx => by
  simp [hashOf, hx]

theorem agrees_hashOf {s : HashCache C} (hs : NoMpc s) : Agrees (hashOf prims s) s := fun q v hq => by
  cases q with
  | hash x =>
    by_cases hx : MpcInput x
    · rw [hs x hx] at hq; cases hq
    · simp [hashOf, hx, hq]
  | _ => simp [hashOf, hq]

theorem noMpc_empty : NoMpc (∅ : HashCache C) := fun _ _ => rfl

variable {prims}

theorem Agrees.mono {h : Query C → HashOutput} {s s' : HashCache C} (hle : s ≤ s') (ha : Agrees h s') :
    Agrees h s := fun q v hq => ha q v (hle hq)

theorem randomOracle_support (q : Query C) (s : HashCache C) (p : HashOutput × HashCache C)
    (hp : p ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s)) :
    s ≤ p.2 ∧ p.2 q = some p.1 ∧ ∀ q', q' ≠ q → p.2 q' = s q' := by
  rcases hs : s q with _ | u
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs] at hp
    erw [support_map, Set.mem_image] at hp
    obtain ⟨u, _, rfl⟩ := hp
    exact ⟨QueryCache.le_cacheQuery _ hs, by simp, fun q' hq' => by simp [QueryCache.cacheQuery_of_ne _ _ hq']⟩
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs] at hp
    simp at hp
    subst hp
    exact ⟨le_rfl, hs, fun _ _ => rfl⟩

theorem hashAnswer_support (q : Query C) (s : HashCache C) (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims q).run s)) :
    s ≤ p.2 ∧ (NoMpc s → NoMpc p.2) ∧ ∀ h, Good prims h → Agrees h p.2 → h q = p.1 := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm] at hp
    simp at hp
    subst hp
    exact ⟨le_rfl, id, fun h hg _ => hg input hm⟩
  · rw [hashAnswer_of_not_isFixed prims hq] at hp
    obtain ⟨hle, hself, hother⟩ := randomOracle_support q s p hp
    refine ⟨hle, fun hn x hx => ?_, fun h _ ha => ha q p.1 hself⟩
    rw [hother _ fun e => hq ⟨x, e.symm, hx⟩]
    exact hn x hx

theorem localAnswer_support (h : Query C → HashOutput) (t : (LocalSpec C).Domain) (s : HashCache C)
    (p : (LocalSpec C).Range t × HashCache C) (hp : p ∈ support ((localAnswer prims t).run s)) :
    s ≤ p.2 ∧ (NoMpc s → NoMpc p.2) ∧ (Good prims h → Agrees h p.2 → p.1 ∈ support (fixedLocal prims h t)) := by
  rcases t with n | q | x
  · change p ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s) at hp
    simp [unifFwdImpl] at hp
    obtain ⟨a, rfl⟩ := hp
    exact ⟨le_rfl, id, fun _ _ => by simp [fixedLocal]; exact Set.mem_univ _⟩
  · obtain ⟨hle, hn, hd⟩ := hashAnswer_support q s p hp
    refine ⟨hle, hn, fun hg ha => ?_⟩
    change p.1 ∈ support (pure (h q) : ProbComp _)
    rw [hd h hg ha]
    simp
  · change p ∈ support ((prgAnswer prims x).run s) at hp
    unfold prgAnswer at hp
    rw [StateT.run_bind] at hp
    simp only [support_bind] at hp
    obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨hle, hn, hd⟩ := hashAnswer_support _ s p' hp'
    refine ⟨hle, hn, fun hg ha => ?_⟩
    change _ ∈ support (pure (prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2) : ProbComp _)
    rw [hd h hg ha]
    simp

/-- Every run of a local computation is a possible run with `H` fixed to any `h` that agrees with
the final cache. -/
theorem localRun_support {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ s z, z ∈ support ((simulateQ (localAnswer prims) oa).run s) →
      s ≤ z.2 ∧ (NoMpc s → NoMpc z.2) ∧
        ∀ h, Good prims h → Agrees h z.2 → z.1 ∈ support (simulateQ (fixedLocal prims h) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s z hz
    simp at hz
    subst hz
    exact ⟨le_rfl, id, fun _ _ _ => by simp⟩
  | query_bind t k ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map] at hp
    obtain ⟨hle2, hn2, hd2⟩ := ih p.1 p.2 z hz
    refine ⟨fun q v hq => ?_, fun hn => hn2 ((localAnswer_support (fun _ => 0) t s p hp).2.1 hn), fun h hg ha => ?_⟩
    · exact hle2 ((localAnswer_support (fun _ => 0) t s p hp).1 hq)
    · obtain ⟨_, _, hd1⟩ := localAnswer_support h t s p hp
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        support_bind, Set.mem_iUnion]
      exact ⟨p.1, hd1 hg (ha.mono hle2), hd2 h hg ha⟩

theorem D_pure (h : Query C → HashOutput) {α : Type} (a : α) : D prims h (pure a : OracleComp (RoSpec C) α) = a := rfl

theorem D_bind (h : Query C → HashOutput) {α β : Type} (oa : OracleComp (RoSpec C) α)
    (f : α → OracleComp (RoSpec C) β) : D prims h (oa >>= f) = D prims h (f (D prims h oa)) := by
  simp [D, simulateQ_bind]

theorem D_hashQuery (h : Query C → HashOutput) (q : Query C) : D prims h (hashQuery q) = h q := by
  simp [D, hashQuery]
  rfl

theorem D_mapM (h : Query C → HashOutput) {α β : Type} (f : α → OracleComp (RoSpec C) β) :
    ∀ l : List α, D prims h (l.mapM f) = l.map fun a => D prims h (f a)
  | [] => rfl
  | a :: l => by rw [List.mapM_cons, D_bind, D_bind, D_mapM h f l, D_pure, List.map_cons]

theorem D_map (h : Query C → HashOutput) {α β : Type} (f : α → β) (oa : OracleComp (RoSpec C) α) :
    D prims h (f <$> oa) = f (D prims h oa) := by
  simp [D]

theorem D_ite (h : Query C → HashOutput) {α : Type} (c : Prop) [Decidable c] (a b : OracleComp (RoSpec C) α) :
    D prims h (if c then a else b) = if c then D prims h a else D prims h b := by
  split_ifs <;> rfl

/-- A lifted computation of `H` with `H` fixed is its value. -/
theorem simulateQ_fixedLocal_liftComp (h : Query C → HashOutput) {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (fixedLocal prims h) (liftComp oa (LocalSpec C)) = pure (D prims h oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [D_pure]
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, D_bind]
    simp only [ih]
    rcases t with q | x <;> rfl

end Fixed

end ThresholdLeanXmssSecurity

/-! ## Query counting

The counted queries of a computation. -/

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Cost

variable {C : Committee}

theorem free_liftComp_query (t : unifSpec.Domain) :
    free (C := C) (liftComp (liftM (unifSpec.query t) : ProbComp _) (LocalSpec C)) =
      (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _) := by
  rfl

theorem world_inr_inl (prims : Primitives) (t : unifSpec.Domain) (s : HashCache C) :
    (simulateQ (world prims) (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _)).run.run s =
      (fun a => ((a, 1), s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
  rw [simulateQ_query]
  simp [world, localAnswer, unifFwdImpl]
  done

theorem world_free_liftComp (prims : Primitives) {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (world prims) (free (C := C) (liftComp p (LocalSpec C)))).run.run s =
      (fun a => ((a, 1), s)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa ih =>
    rw [liftComp_bind, free_bind, simulateQ_bind, free_liftComp_query]
    simp only [WriterT.run_bind, StateT.run_bind]
    erw [world_inr_inl]
    simp only [bind_map_left, one_mul]
    rw [map_bind]
    congr 1; funext a
    rw [StateT.run_map, ih]
    simp

theorem world_inl_cost (prims : Primitives) (t : (LocalSpec C).Domain) (s : HashCache C) :
    ∀ r ∈ support ((simulateQ (world prims) (liftM ((WorldSpec C).query (.inl (.inl t))) :
        OracleComp (WorldSpec C) _)).run.run s),
      Multiplicative.toAdd r.1.2 = if Counted t then 1 else 0 := by
  intro r hr
  rw [simulateQ_query] at hr
  simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query] at hr
  simp only [world, QueryImpl.withAddCost_apply, WriterT.run_bind, AddWriterT.run_addTell] at hr
  simp at hr
  obtain ⟨p, -, rfl⟩ := hr
  simp only [toAdd_ofAdd]
  rcases t with t | (q | x)
  · simp [Counted]
  · cases q <;> simp [Counted]
  · simp [Counted]

theorem counted_bind {α β : Type} (oa : OracleComp (SimulatorSpec C) α) (f : α → OracleComp (SimulatorSpec C) β) :
    counted (oa >>= f) = counted oa >>= fun a => counted (f a) := simulateQ_bind _ _ _

theorem mem_support_world_bind (prims : Primitives) {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (k : α → OracleComp (WorldSpec C) β) (s : HashCache C) (r)
    (hr : r ∈ support ((simulateQ (world prims) (oa >>= k)).run.run s)) :
    ∃ p ∈ support ((simulateQ (world prims) oa).run.run s),
      ∃ q ∈ support ((simulateQ (world prims) (k p.1.1)).run.run p.2), r = ((q.1.1, p.1.2 * q.1.2), q.2) := by
  rw [simulateQ_bind, WriterT.run_bind, StateT.run_bind] at hr
  simp only [support_bind, Set.mem_iUnion, exists_prop, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, q, hq, rfl⟩ := hr
  exact ⟨p, hp, q, hq, rfl⟩

theorem cost_counted (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) (s : HashCache C) :
    ∀ r ∈ support ((simulateQ (world prims) (counted (liftComp oa (SimulatorSpec C)))).run.run s),
      Multiplicative.toAdd r.1.2 ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    intro r hr
    simp only [liftComp_pure] at hr
    change r ∈ support (pure ((x, 1), s) : ProbComp _) at hr
    simp at hr; subst hr; simp
  | query_bind t mx ih =>
    intro r hr
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftComp_bind, counted_bind] at hr
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_support_world_bind prims _ _ s r hr
    have e : counted (liftComp (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _) (SimulatorSpec C)) =
        (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
      rcases t with t | (q | x) <;> rfl
    rw [e] at hp
    have hp' := world_inl_cost prims t s p hp
    have hq' := ih _ _ (h.2 p.1.1) p.2 q hq
    simp only [toAdd_mul, hp']
    split_ifs at hq' ⊢ with hc
    · have := h.1.resolve_left (not_not.mpr hc); omega
    · omega

variable (prims : Primitives)

/-- Every run from every cache makes at most `n` counted queries. -/
def CostLe {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ) : Prop :=
  ∀ s, ∀ r ∈ support ((simulateQ (world prims) oa).run.run s), Multiplicative.toAdd r.1.2 ≤ n

theorem CostLe.mono {α : Type} {oa : OracleComp (WorldSpec C) α} {n m : ℕ} (h : CostLe prims oa n) (hnm : n ≤ m) :
    CostLe prims oa m := fun s r hr => (h s r hr).trans hnm

theorem CostLe.bind {α β : Type} {oa : OracleComp (WorldSpec C) α} {k : α → OracleComp (WorldSpec C) β} {n m : ℕ}
    (h : CostLe prims oa n) (hk : ∀ a, CostLe prims (k a) m) : CostLe prims (oa >>= k) (n + m) := fun s r hr => by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_support_world_bind prims oa k s r hr
  simp only [toAdd_mul]
  exact Nat.add_le_add (h s p hp) (hk p.1.1 p.2 q hq)

theorem CostLe.pure {α : Type} (a : α) : CostLe prims (C := C) (pure a) 0 := fun s r hr => by
  change r ∈ support (Pure.pure ((a, 1), s) : ProbComp _) at hr
  simp at hr; subst hr; simp

theorem CostLe.of_counted {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa Counted n) :
    CostLe prims (counted (liftComp oa (SimulatorSpec C))) n := cost_counted prims oa n h

theorem CostLe.free_sample {α : Type} (p : ProbComp α) : CostLe prims (free (C := C) (liftComp p (LocalSpec C))) 0 :=
  fun s r hr => by
    rw [world_free_liftComp] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨a, -, rfl⟩ := hr; simp

theorem hasHashQueryBound_of_costLe {α : Type} {oa : OracleComp (WorldSpec C) α} {n : ℕ} (h : CostLe prims oa n) :
    HasHashQueryBound (runWorld prims oa) n := fun r hr => by
  unfold runWorld at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact h ∅ r' hr'

theorem CostLe.free {α : Type} (oa : OracleComp (LocalSpec C) α) : CostLe prims (free oa) 0 := fun s r hr => by
  rw [simulateQ_world_free] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨z, -, rfl⟩ := hr
  simp

theorem CostLe.map {α β : Type} {oa : OracleComp (WorldSpec C) α} {n : ℕ} (f : α → β) (h : CostLe prims oa n) :
    CostLe prims (f <$> oa) n := by
  rw [map_eq_bind_pure_comp]
  exact (h.bind prims fun a => CostLe.pure prims (f a)).mono prims (by simp)

theorem CostLe.query_inl (t : (LocalSpec C).Domain) :
    CostLe prims (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
      (if Counted t then 1 else 0) := fun s r hr => (world_inl_cost prims t s r hr).le

theorem CostLe.program (q : Query C) (value : HashOutput) :
    CostLe prims (ThresholdLeanXmss.program q value) 1 := fun s r hr => by
  unfold ThresholdLeanXmss.program counted at hr
  erw [simulateQ_query] at hr
  simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query] at hr
  simp only [world, QueryImpl.withAddCost_apply, WriterT.run_bind, AddWriterT.run_addTell] at hr
  simp at hr
  rcases hr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp

theorem CostLe.mapM {α β : Type} (f : α → OracleComp (WorldSpec C) β) (k : ℕ) :
    ∀ l : List α, (∀ a ∈ l, CostLe prims (f a) k) → CostLe prims (l.mapM f) (l.length * k)
  | [], _ => by simpa using CostLe.pure prims ([] : List β)
  | a :: l, h => by
    rw [List.mapM_cons]
    refine ((h a (List.mem_cons_self ..)).bind prims fun b => ((CostLe.mapM f k l fun a' ha' =>
      h a' (List.mem_cons_of_mem _ ha')).bind prims fun bs => CostLe.pure prims (b :: bs))).mono prims ?_
    simp [Nat.succ_mul, Nat.add_comm]

theorem CostLe.sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α),
    (∀ i, CostLe prims (f i) 0) → CostLe prims (Concrete.sequenceFin f) 0
  | 0, f, _ => by simpa [Concrete.sequenceFin] using CostLe.pure prims (Fin.elim0 : Fin 0 → α)
  | n + 1, f, h => by
    simp only [Concrete.sequenceFin]
    exact ((h 0).bind prims fun a => ((CostLe.sequenceFin (fun i : Fin n => f i.succ) fun i => h i.succ).bind
      prims fun rest => CostLe.pure prims _)).mono prims (by simp)

/-- A simulation into a writer of the world whose steps cost what the queries cost on the counted copy. -/
theorem CostLe.simulateQ_writer {ω : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (impl : QueryImpl (LocalSpec C) (WriterT ω (OracleComp (WorldSpec C))))
    (himpl : ∀ t, CostLe prims (impl t).run (if Counted t then 1 else 0)) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ n, IsQueryBoundP oa Counted n → CostLe prims (simulateQ impl oa).run n := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; exact (CostLe.pure prims _).mono prims (Nat.zero_le _)
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_query, WriterT.run_bind]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    refine ((himpl t).bind prims fun p => CostLe.map prims _ (ih p.1 _ (h.2 p.1))).mono prims ?_
    split_ifs with hc
    · have := h.1.resolve_left (not_not.mpr hc); omega
    · omega

theorem adversary_query (t : (LocalSpec C).Domain) :
    worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) =
      (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
  rcases t with t | (q | x) <;> rfl

theorem adversary_hashQuery (q : Query C) :
    worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)) =
      (liftM ((WorldSpec C).query (.inl (.inl (.inr (.inl q))))) : OracleComp (WorldSpec C) _) := rfl

theorem CostLe.writer_bind {α β : Type} (x : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (f : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β) {n m : ℕ} (hx : CostLe prims x.run n)
    (hf : ∀ a, CostLe prims (f a).run m) : CostLe prims (x >>= f).run (n + m) := by
  rw [WriterT.run_bind]
  exact hx.bind prims fun p => CostLe.map prims _ (hf p.1)

theorem CostLe.writer_liftM {α : Type} (x : OracleComp (WorldSpec C) α) {n : ℕ} (hx : CostLe prims x n) :
    CostLe prims (liftM x : WriterT (CallLog C) (OracleComp (WorldSpec C)) α).run n :=
  CostLe.map prims _ hx

theorem CostLe.writer_tell (w : CallLog C) :
    CostLe prims (tell w : WriterT (CallLog C) (OracleComp (WorldSpec C)) PUnit).run 0 :=
  CostLe.pure prims _

theorem CostLe.writer_pure {α : Type} (a : α) :
    CostLe prims (Pure.pure a : WriterT (CallLog C) (OracleComp (WorldSpec C)) α).run 0 :=
  CostLe.pure prims _

/-- An observed computation costs what the computation costs on the counted copy. -/
theorem CostLe.observe {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa Counted n) :
    CostLe prims (ThresholdLeanXmss.observe oa) n := by
  unfold ThresholdLeanXmss.observe
  refine CostLe.simulateQ_writer prims _ (fun t => ?_) oa n h
  rcases t with u | q | x
  · refine CostLe.writer_liftM prims _ ?_
    rw [adversary_query]
    exact CostLe.query_inl prims _
  · dsimp only
    have hq : CostLe prims (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)))
        (if Counted (Sum.inr (Sum.inl q) : (LocalSpec C).Domain) then 1 else 0) := by
      rw [adversary_hashQuery]
      exact CostLe.query_inl prims _
    exact (CostLe.writer_bind prims _ _ (CostLe.writer_liftM prims _ hq) fun y =>
      (CostLe.writer_bind prims _ _ (CostLe.writer_tell prims _) fun _ => CostLe.writer_pure prims y)).mono prims
        (by simp)
  · refine CostLe.writer_liftM prims _ ?_
    rw [adversary_query]
    exact CostLe.query_inl prims _

theorem CostLe.writer_sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) α),
    (∀ i, CostLe prims (f i).run 0) → CostLe prims (Concrete.sequenceFin f).run 0
  | 0, f, _ => CostLe.writer_pure prims _
  | n + 1, f, h => by
    simp only [Concrete.sequenceFin]
    exact (CostLe.writer_bind prims _ _ (h 0) fun a => (CostLe.writer_bind prims _ _
      (CostLe.writer_sequenceFin (fun i : Fin n => f i.succ) fun i => h i.succ) fun rest =>
        CostLe.writer_pure prims _)).mono prims (by simp)

/-- A round with the observed adversary costs at most one round of the adversary. -/
theorem CostLe.stepRound_observed {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    CostLe prims (stepRound observedRoles D A noFunctionality state steps).run step := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine (CostLe.writer_bind prims _ _ (CostLe.observe prims _ step (hround _ _)) fun p =>
    (CostLe.writer_bind prims _ _ (CostLe.writer_sequenceFin prims _ fun j => ?_) fun steps' =>
      CostLe.writer_pure prims _)).mono prims (by simp)
  split
  · exact CostLe.writer_pure prims _
  · split_ifs
    · exact CostLe.writer_pure prims _
    · exact CostLe.writer_liftM prims _ (CostLe.free prims _)
  · exact CostLe.writer_pure prims _

/-- The rounds with the observed adversary cost at most `fuel` rounds of the adversary. -/
theorem CostLe.executeRounds_observed {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      CostLe prims (executeRounds observedRoles D A noFunctionality fuel state steps).run (fuel * step)
  | 0, state, steps => by
    rw [Nat.zero_mul]
    exact CostLe.writer_pure prims _
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · exact (CostLe.writer_pure prims _).mono prims (Nat.zero_le _)
    · refine (CostLe.writer_bind prims _ _ (CostLe.stepRound_observed prims D A step hround state steps) fun p =>
        CostLe.executeRounds_observed D A step hround fuel _ _).mono prims (by rw [Nat.succ_mul, Nat.add_comm])

end Cost

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

attribute [local instance] Classical.propDecidable

/-! ## Shared facts -/

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {L R : Type}

section Shared

theorem evalDist_eq_pure_of_support {α : Type} (mx : ProbComp α) (a : α) (h : ∀ y ∈ support mx, y = a) :
    𝒟[mx] = 𝒟[(pure a : ProbComp α)] := by
  refine evalDist_ext fun y => ?_
  rcases eq_or_ne y a with hy | hy
  · subst hy
    rw [probOutput_eq_one_of_support_subset_singleton (by simp) h, probOutput_pure_self]
  · rw [probOutput_eq_zero_of_not_mem_support fun hm => hy (h y hm),
      probOutput_eq_zero_of_not_mem_support (mx := (pure a : ProbComp α)) (by simpa using hy)]

theorem firstInput_some {α : Type} [Inhabited α] (x : C.Party → α) :
    firstInput (fun i => some (x i)) = default ∨ ∃ p, firstInput (fun i => some (x i)) = x p := by
  unfold firstInput
  generalize C.parties = l
  cases l with
  | nil => exact Or.inl rfl
  | cons a l => exact Or.inr ⟨a, by simp⟩

/-- A bind meets `q` only after a prefix that meets `p`, and then with probability at most `ε`. -/
theorem probEvent_bind_le_mul {α β : Type} {mx : ProbComp α} {my : α → ProbComp β} {p : α → Prop}
    {q : β → Prop} [DecidablePred p] {ε : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[q | my x] ≤ if p x then ε else 0) :
    Pr[q | mx >>= my] ≤ Pr[p | mx] * ε := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · refine (mul_le_mul' le_rfl (h x hx)).trans ?_
    split_ifs <;> simp
  · simp [probOutput_eq_zero_of_not_mem_support hx]

theorem simulateQ_replyImpl_liftComp {L R α : Type} (reply : L → R) (oa : OracleComp (LocalSpec C) α) :
    simulateQ (replyImpl reply) (liftComp oa (LocalSpec C + (L →ₒ R))) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind]
    simp only [ih]
    congr 1
    rw [liftComp_query]
    simp [replyImpl]
    refine (simulateQ_query _ _).trans ?_
    rcases t with n | x | x <;> rfl

theorem simulateQ_replyImpl_liftComp_prob {L R α : Type} (reply : L → R) (oa : ProbComp α) :
    simulateQ (replyImpl (C := C) reply) (liftComp oa (LocalSpec C + (L →ₒ R))) = liftComp oa (LocalSpec C) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, liftComp_bind]
    simp only [ih]
    congr 1

theorem simulateQ_replyImpl_leak (reply : L → R) (l : L) :
    simulateQ (replyImpl (C := C) reply) (leak l) = pure (reply l) := by
  unfold leak
  rw [simulateQ_query]
  rfl

theorem simulateQ_replyImpl_sample (reply : L → R) (β : Type) [SampleableType β] :
    simulateQ (replyImpl (C := C) reply) (sample β) = liftComp ($ᵗ β) (LocalSpec C) := by
  unfold sample
  exact simulateQ_replyImpl_liftComp_prob reply _

theorem exists_holder (T : C.Term) : ∃ i, i ∈ C.holders T := by
  have hcard : (C.holders T).card = C.t := by
    have h1 := Finset.card_compl T.1
    simp only [Fintype.card_fin, T.2] at h1
    simp only [Committee.holders, h1, Committee.n]
    have := C.one_le_t
    omega
  have : (C.holders T).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact C.one_le_t
  exact this

theorem length_bitsOfDigest (d : Digest) : (bitsOfDigest d).length = digestBits := by simp [bitsOfDigest]

theorem terms_nodup : C.terms.Nodup := Finset.nodup_toList _

theorem pairOf_comm (i j : C.Party) (h : i ≠ j) : C.pairOf i j h = C.pairOf j i h.symm := by
  unfold Committee.pairOf
  split_ifs with h1 h2 h2
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) h

/-- The keys of the chain rows of bottom tree `b`, in job order. -/
abbrev bottomKeys (b : Fin (2 ^ layerHeight)) : List (KeyIndex × ChainIndex) :=
  (List.finRange (2 ^ layerHeight)).flatMap fun k => (List.finRange numChains).map fun l => (bottomKey b k, l)

theorem run'_lift_bind {α β : Type} (c : PartyM C E G α) (f : α → RunM C E G β) (st : RunState C) :
    (StateT.lift c >>= f).run' st = c >>= fun r => (f r).run' st := by
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift]

/-- Relabeling oracle inputs also relabels the private cache. -/
def relabelHashCache (e : Query C ≃ Query C) (s : HashCache C) : HashCache C :=
  fun q => s (e.symm q)

end Shared

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

/-- All steps run in the local oracles. -/
def localRoles {C : Committee} : Roles C (OracleComp (LocalSpec C)) := ⟨fun oa => oa, fun oa => oa⟩

end ThresholdLeanXmssSecurity
