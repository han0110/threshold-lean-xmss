import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.RestCount
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Move

/-!
# The counted calls of the game with the keys of the dealer

`Logged` is a call of `H` on the counted copy, the only call that `loggedWorld` logs. A world program
with at most `n` such calls adds at most `n` cells to the log (`log_length_le`).

`LoggedCount.logged_dealtRun` counts the calls of `Logged` in `dealtRun` with no emulated run. The
start and each round of the adversary count their calls of `H`, and `forge` counts its calls of `H` by
`forgeCost`. So a game of an adversary with the budget `q` makes at most `q` such calls. The runs pay
from the potential `LoggedCount.runsLeft` of the runs that remain, as in `RestCost.lean`. `RCost` and
`RCostT` are the cost calculus `GameCost` of `RestCost.lean` on the state of the game over the world
programs. `simulateQ_congr_of_noCall` states that two worlds that agree off a set of calls run a program
with no call in that set the same way.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map
  noCall_query noCall_mapM noCall_sequenceFin)
open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-- A call of `H` on the local oracles. -/
def HashCall : (LocalSpec C).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

/-- A call of `H` on the counted copy. `loggedWorld` logs exactly these calls. -/
def Logged : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => HashCall t
  | _ => False

theorem countedCells_length_le (t : (WorldSpec C).Domain) :
    (countedCells t).length ≤ if Logged t then 1 else 0 := by
  rcases t with ((n | q | x) | y) | u <;> simp [countedCells, Logged, HashCall]

/-! ## The log of a world program -/

section Log

variable (prims : Primitives) (D : C.Coalition)

theorem loggedWorld_log (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ r ∈ support ((loggedWorld prims D t).run w), r.2.2 = w.2 ++ countedCells t := by
  intro r hr
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', -, rfl⟩ := hr
  rfl

/-- A world program with at most `n` calls of `Logged` adds at most `n` cells to the log. -/
theorem log_length_le {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ (n : ℕ), IsQueryBoundP oa Logged n → ∀ (w : LogState C),
      ∀ z ∈ support ((simulateQ (loggedWorld prims D) oa).run w), z.2.2.length ≤ w.2.length + n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ w z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    intro n hn w z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have h1 := ih r.1 _ (hn.2 r.1) r.2 z hz
    have hc := countedCells_length_le t
    rw [loggedWorld_log prims D t w r hr, List.length_append] at h1
    by_cases ht : Logged t
    · simp only [ht, ↓reduceIte] at hc h1
      have := hn.1.resolve_left (not_not.2 ht)
      omega
    · simp only [ht, ↓reduceIte] at hc h1
      omega

end Log

/-! ## The calls of the network -/

section Network

variable {E : Type}

theorem logged_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa HashCall n) : IsQueryBoundP (worldRoles.adversary oa) Logged n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, ThresholdLeanXmssSecurity.adversary_query]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem logged_free {β : Type} (oa : OracleComp (LocalSpec C) β) : NoCall Logged (free oa) := by
  rw [noCall_iff]
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl not_false, fun u => by simpa using ih u⟩

theorem logged_stepRound {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) HashCall step) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) Logged step := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  refine (isQueryBoundP_bind (logged_adversary _ step (hround _ _)) fun p _ => ?_).mono (Nat.add_zero _).le
  rw [← noCall_iff]
  obtain ⟨state', sent⟩ := p
  refine noCall_bind _ (noCall_sequenceFin _ _ fun j => ?_) fun _ => noCall_pure _ _
  split
  · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact logged_free _
  · exact noCall_pure _ _

theorem logged_executeRounds {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) HashCall step) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps) Logged (fuel * step)
  | 0, state, steps => trivial
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · trivial
    · refine (isQueryBoundP_bind (logged_stepRound D A step hround state steps) fun p _ => ?_).mono
        (by rw [Nat.succ_mul, Nat.add_comm])
      obtain ⟨state', steps', _⟩ := p
      exact logged_executeRounds D A step hround fuel state' steps'

theorem logged_startSteps {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α) :
    NoCall Logged (startSteps worldRoles D program) := by
  unfold startSteps
  refine noCall_sequenceFin _ _ fun i => ?_
  split_ifs
  · exact noCall_pure _ _
  · exact logged_free _

theorem logged_executePhase {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) HashCall step) (fuel : ℕ)
    (state : A.State) (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program) Logged (fuel * step) := by
  unfold executePhase
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_startSteps D program)) fun steps _ =>
    logged_executeRounds D A step hround fuel state steps).mono (Nat.zero_add _).le

theorem logged_observe {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) (h : IsQueryBoundP oa HashCall n) :
    IsQueryBoundP (observe oa) Logged n := by
  have h' := logged_adversary oa n h
  rw [← fst_observe] at h'
  exact (isQueryBoundP_map_iff _ _ _).1 h'

theorem logged_stepRound_observed (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) HashCall step) {α : Type} (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound observedRoles D A noFunctionality state steps).run Logged step := by
  have h := logged_stepRound D A step hround state steps
  rw [← seedGenEraseLog_stepRound] at h
  exact (isQueryBoundP_map_iff _ _ _).1 h

theorem logged_executeRounds_observed (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) HashCall step) {α : Type} (fuel : ℕ)
    (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (executeRounds observedRoles D A noFunctionality fuel state steps).run Logged (fuel * step) := by
  have h := logged_executeRounds D A step hround fuel state steps
  rw [← seedGenEraseLog_executeRounds] at h
  exact (isQueryBoundP_map_iff _ _ _).1 h

theorem logged_program (q : Query C) (value : HashOutput) : NoCall Logged (ThresholdLeanXmss.program q value) := by
  unfold ThresholdLeanXmss.program counted
  erw [simulateQ_query]
  rw [noCall_iff]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  exact (noCall_iff _ _).1 (noCall_query _ _ (by simp [Logged]))

/-- The seed generation of the simulator makes the calls of the start and of the `setupRounds` rounds of
the adversary. -/
theorem logged_worldSeedGen (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (net.start x z) HashCall start)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step) :
    IsQueryBoundP (worldSeedGen D net) Logged (start + setupRounds * step) := by
  unfold worldSeedGen
  refine isQueryBoundP_bind (logged_observe _ _ (hstart _ _)) fun p _ => ?_
  obtain ⟨state, early⟩ := p
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_free _)) fun x _ => ?_).mono
    (Nat.zero_add _).le
  obtain ⟨parameter, seeds, dealt⟩ := x
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_free _)) fun parts _ => ?_).mono
    (Nat.zero_add _).le
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_startSteps D _)) fun steps _ => ?_).mono
    (Nat.zero_add _).le
  refine (isQueryBoundP_bind (logged_stepRound_observed D net step hround state steps) fun r _ => ?_).mono
    (show step + (setupRounds - 1) * step ≤ setupRounds * step by simp [setupRounds]; omega)
  obtain ⟨⟨state', steps', sent⟩, calls⟩ := r
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_free _)) fun high _ => ?_).mono
    (Nat.zero_add _).le
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_program _ _)) fun _ _ => ?_).mono
    (Nat.zero_add _).le
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun T => ?_)) fun _ _ => ?_).mono
    (Nat.zero_add _).le
  · split
    · exact logged_program _ _
    · exact noCall_pure _ _
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_))
    fun _ _ => ?_).mono (Nat.zero_add _).le
  · split
    · exact logged_program _ _
    · exact noCall_pure _ _
  refine (isQueryBoundP_bind (logged_executeRounds_observed D net step hround _ state' steps') fun _ _ => ?_).mono
    (Nat.add_zero _).le
  exact (noCall_iff _ _).1 (noCall_pure _ _)

end Network

/-! ## Worlds that agree off a set of calls -/

/-- Two worlds that agree off the set `P` run a program with no call in `P` the same way. -/
theorem simulateQ_congr_of_noCall {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : ι → Prop) (impl impl' : QueryImpl spec m) (h : ∀ t, ¬ P t → impl t = impl' t) {α : Type}
    (X : OracleComp spec α) (hX : NoCall P X) : simulateQ impl X = simulateQ impl' X := by
  rw [noCall_iff] at hX
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hX
    have ht : ¬ P t := hX.1.resolve_right (by omega)
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, h t ht]
    exact bind_congr fun u => ih u (by simpa [ht] using hX.2 u)

/-! ## A cost calculus on the state of the game -/

section Calculus

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (c : ι → ℕ∞) {S T : Type}

/-- `m` costs at most `Φ s` from every state `s`, with the cost `k` of the result and of the end
state. -/
def RCost {α : Type} (m : StateT S (OracleComp spec) α) (k : α → S → ℕ∞) (Φ : S → ℕ∞) : Prop :=
  ∀ s, costWith c (m.run s) (fun p => k p.1 p.2) ≤ Φ s

/-- `RCost` from every outer state. -/
def RCostT {α : Type} (m : StateT T (StateT S (OracleComp spec)) α) (k : α → S → ℕ∞) (Φ : S → ℕ∞) : Prop :=
  ∀ t, RCost c (m.run t) (fun p s => k p.1 s) Φ

namespace RCost

variable {c} {α β : Type}

theorem mono {m : StateT S (OracleComp spec) α} {k k' : α → S → ℕ∞} {Φ Φ' : S → ℕ∞} (h : RCost c m k Φ)
    (hk : ∀ a s, k' a s ≤ k a s) (hΦ : ∀ s, Φ s ≤ Φ' s) : RCost c m k' Φ' := fun s =>
  (costWith_mono _ fun p : α × S => hk p.1 p.2).trans ((h s).trans (hΦ s))

theorem pure (a : α) (k : α → S → ℕ∞) : RCost c (Pure.pure a : StateT S (OracleComp spec) α) k (k a) :=
  fun _ => le_rfl

theorem bind {m : StateT S (OracleComp spec) α} {f : α → StateT S (OracleComp spec) β} {K : α → S → ℕ∞}
    {k : β → S → ℕ∞} {Φ : S → ℕ∞} (h : RCost c m K Φ) (hf : ∀ a, RCost c (f a) k (K a)) :
    RCost c (m >>= f) k Φ := fun s => by
  rw [StateT.run_bind, PFunctor.FreeM.costWith_bind']
  exact (costWith_mono _ fun p : α × S => hf p.1 p.2).trans (h s)

theorem frame {m : StateT S (OracleComp spec) α} {k : α → S → ℕ∞} {Φ : S → ℕ∞} (h : RCost c m k Φ) (r : ℕ∞) :
    RCost c m (fun a s => k a s + r) (fun s => Φ s + r) := fun s =>
  (costWith_add_le _ _ _ r).trans (add_le_add (h s) le_rfl)

theorem get_bind {f : S → StateT S (OracleComp spec) α} {k : α → S → ℕ∞} {Φ : S → ℕ∞}
    (h : ∀ s, costWith c ((f s).run s) (fun p => k p.1 p.2) ≤ Φ s) : RCost c (get >>= f) k Φ := fun s => by
  rw [StateT.run_bind]
  exact h s

theorem set (t : S) (k : PUnit → S → ℕ∞) :
    RCost c (MonadStateOf.set t : StateT S (OracleComp spec) PUnit) k fun _ => k () t := fun _ => le_rfl

theorem modify (f : S → S) (k : PUnit → S → ℕ∞) :
    RCost c (modify f : StateT S (OracleComp spec) PUnit) k (fun s => k () (f s)) := fun _ => le_rfl

theorem lift {x : OracleComp spec α} {B : ℕ∞} (h : cost c x ≤ B) (Ψ : S → ℕ∞) :
    RCost c (StateT.lift x : StateT S (OracleComp spec) α) (fun _ s => Ψ s) (fun s => B + Ψ s) := fun s => by
  rw [StateT.run_lift, PFunctor.FreeM.costWith_bind']
  exact (costWith_le_cost_add _ _).trans (add_le_add h (iSup_le fun _ => le_rfl))

theorem of_eq {m m' : StateT S (OracleComp spec) α} {k : α → S → ℕ∞} {Φ : S → ℕ∞} (h : RCost c m k Φ)
    (e : m = m') : RCost c m' k Φ := e ▸ h

theorem map_get (f : S → α) (k : α → S → ℕ∞) :
    RCost c (f <$> (get : StateT S (OracleComp spec) _)) k (fun s => k (f s) s) := by
  rw [map_eq_bind_pure_comp]
  exact get_bind fun _ => le_rfl

end RCost

namespace RCostT

variable {c} {α β : Type}

theorem mono {m : StateT T (StateT S (OracleComp spec)) α} {k k' : α → S → ℕ∞} {Φ Φ' : S → ℕ∞}
    (h : RCostT c m k Φ) (hk : ∀ a s, k' a s ≤ k a s) (hΦ : ∀ s, Φ s ≤ Φ' s) : RCostT c m k' Φ' := fun t =>
  (h t).mono (fun p s => hk p.1 s) hΦ

theorem pure (a : α) (k : α → S → ℕ∞) :
    RCostT c (Pure.pure a : StateT T (StateT S (OracleComp spec)) α) k (k a) := fun _ => RCost.pure _ _

theorem bind {m : StateT T (StateT S (OracleComp spec)) α} {f : α → StateT T (StateT S (OracleComp spec)) β}
    {K : α → S → ℕ∞} {k : β → S → ℕ∞} {Φ : S → ℕ∞} (h : RCostT c m K Φ) (hf : ∀ a, RCostT c (f a) k (K a)) :
    RCostT c (m >>= f) k Φ := fun t => by
  rw [StateT.run_bind]
  exact RCost.bind (h t) fun p => hf p.1 p.2

theorem frame {m : StateT T (StateT S (OracleComp spec)) α} {k : α → S → ℕ∞} {Φ : S → ℕ∞} (h : RCostT c m k Φ)
    (r : ℕ∞) : RCostT c m (fun a s => k a s + r) (fun s => Φ s + r) := fun t => (h t).frame r

theorem lift {m : StateT S (OracleComp spec) α} {k : α → S → ℕ∞} {Φ : S → ℕ∞} (h : RCost c m k Φ) :
    RCostT c (StateT.lift m : StateT T (StateT S (OracleComp spec)) α) k Φ := fun _ =>
  RCost.bind h fun _ => RCost.pure _ _

theorem get_bind {f : S → StateT T (StateT S (OracleComp spec)) α} {k : α → S → ℕ∞} {Φ : S → ℕ∞}
    (h : ∀ s t, costWith c (((f s).run t).run s) (fun p => k p.1.1 p.2) ≤ Φ s) :
    RCostT c (StateT.lift get >>= f) k Φ := fun t s => by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get]
  exact h s t

/-- A program through a stateful handler costs at most the charges `d` of its calls plus the
potential `Φ`, when each step costs at most its charge and the drop of `Φ`. -/
theorem simulateQ {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} (impl : QueryImpl spec' (StateT T (StateT S (OracleComp spec))))
    (d : ι' → ℕ∞) (Φ : S → ℕ∞) (hstep : ∀ t, RCostT c (impl t) (fun _ s => Φ s) (fun s => d t + Φ s))
    (oa : OracleComp spec' α) :
    RCostT c (simulateQ impl oa) (fun _ s => Φ s) (fun s => cost d oa + Φ s) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [cost] using RCostT.pure (c := c) (T := T) a fun _ s => Φ s
  | query_bind t f ih =>
    rw [simulateQ_query_bind, cost, costWith_query_bind]
    refine bind (K := fun u s => cost d (f u) + Φ s) ?_ ih
    refine ((hstep t).frame (⨆ u, cost d (f u))).mono (fun u s => ?_) (fun s => ?_)
    · rw [add_comm (cost d (f u))]
      exact add_le_add le_rfl (le_iSup (fun u => cost d (f u)) u)
    · rw [add_assoc, add_comm (Φ s), ← add_assoc]
      rfl

end RCostT

end Calculus

/-! ## The rest of the game with no emulated run -/

namespace LoggedCount

section Rest

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)
  (step : ℕ)

/-- The calls of the runs that remain, with `treeFuel * step + step` calls for each run and its vote. -/
def runsLeft {σ : Type} (s : RealState C σ) : ℕ∞ :=
  (FirstCounts.remaining runLimit (fun _ => treeFuel circuits settings * step + step) s.runs : ℕ)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A vote round makes at most `step` calls of `Logged`. -/
theorem cost_voteRound_logged (net : Adversary C E Unit PEmpty PEmpty)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step) (state : net.State)
    (input : C.Party → Option (Query C)) : cost (callCharge Logged) (voteRound worldRoles D net state input) ≤ step :=
  (cost_callCharge_le_iff _ _ _).2 (Vote.voteRound_isQueryBoundP D net state input Logged step hround
    fun _ _ _ h => h)

omit [Fintype E] [DecidableEq E] in
/-- One real run of `tree` from a state with fewer than `runLimit` runs of `tree` costs its part of
the potential. -/
theorem cost_treeRun (net : Adversary C E Unit PEmpty PEmpty)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step) (tree : Tree)
    (s : RealState C net.State) (hs : s.runs tree < runLimit) :
    costWith (callCharge Logged) ((treeRun K circuits settings noMonitor D net tree).run s)
      (fun p => runsLeft circuits settings runLimit step p.2) ≤ runsLeft circuits settings runLimit step s := by
  unfold treeRun
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  have hpot : ((treeFuel circuits settings * step + step : ℕ) : ℕ∞) +
      ((FirstCounts.remaining runLimit (fun _ => treeFuel circuits settings * step + step)
        (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞) = runsLeft circuits settings runLimit step s := by
    rw [runsLeft, ← FirstCounts.remaining_update runLimit _ s.runs tree hs]
    push_cast
    ring
  refine (?_ : RCost (callCharge Logged) _ (fun _ s' => runsLeft circuits settings runLimit step s')
    fun _ => runsLeft circuits settings runLimit step s) s
  refine RCost.bind (K := fun _ _ => (step : ℕ∞) + ((FirstCounts.remaining runLimit
      (fun _ => treeFuel circuits settings * step + step) (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((RCost.lift ((cost_callCharge_le_iff _ _ _).2 (logged_executePhase D net step hround _ _ _)) _).mono
      (fun _ _ => le_rfl) fun _ => by rw [← hpot, Nat.cast_add, add_assoc]) fun r => ?_
  obtain ⟨state, outputs⟩ := r
  refine RCost.bind (K := fun _ _ => (step : ℕ∞) + ((FirstCounts.remaining runLimit
      (fun _ => treeFuel circuits settings * step + step) (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((RCost.lift (cost_pure_le _ _ 0) _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _)) fun bad => ?_
  refine RCost.bind (K := fun _ _ => ((FirstCounts.remaining runLimit
      (fun _ => treeFuel circuits settings * step + step) (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞))
    ((RCost.lift (cost_voteRound_logged D step net hround _ _) _).mono (fun _ _ => le_rfl) fun _ => le_rfl)
    fun v => ?_
  exact (RCost.set _ _).mono (fun _ _ => le_rfl) fun _ => le_rfl

omit [Fintype E] [DecidableEq E] in
theorem cost_secRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) (s : RealState C net.State) (hs : s.runs tree < runLimit) :
    costWith (callCharge Logged) ((secRun K circuits settings m D net parameter seeds dealt emu tree).run s)
      (fun p => runsLeft circuits settings runLimit step p.2) ≤ runsLeft circuits settings runLimit step s := by
  unfold secRun
  rw [StateT.run_bind, StateT.run_get, pure_bind, ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]
  exact cost_treeRun K circuits settings runLimit D step net hround tree s hs

omit [Fintype E] [DecidableEq E] in
theorem rcost_secRuns (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (net : Adversary C E Unit PEmpty PEmpty)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, RCost (callCharge Logged) (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
      (fun _ s => runsLeft circuits settings runLimit step s) (runsLeft circuits settings runLimit step)
  | 0 => RCost.pure _ _
  | count + 1 => by
    have rest := rcost_secRuns m hm net hround parameter seeds dealt emu tree count
    unfold secRuns
    refine RCost.get_bind fun s => ?_
    by_cases h : mayRun runLimit D s tree
    · rw [ite_eq_left h, StateT.run_bind, PFunctor.FreeM.costWith_bind']
      refine le_trans (costWith_mono _ fun p => ?_)
        (cost_secRun K circuits settings runLimit D step m hm net hround parameter seeds dealt emu tree s
          (FirstCounts.mayRun_lt runLimit h))
      exact rest p.2
    · rw [ite_eq_right h]
      exact le_rfl

theorem cost_logged_free {β : Type} (oa : OracleComp (RoSpec C) β) :
    cost (callCharge Logged) (DkgCompletenessProof.freeHom oa) ≤ 0 :=
  (cost_callCharge_le_iff _ _ 0).2 ((noCall_iff _ _).1 (logged_free _))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signing oracles of a dealer on the computations of the world. -/
theorem rcostT_tsig {σ : Type} (d : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C)
    (htsig : ∀ st, cost (callCharge Logged) ((tsigOracles (fun oa => free (liftComp oa _)) d q).run st) ≤ 0)
    (Ψ : RealState C σ → ℕ∞) :
    RCostT (callCharge Logged)
      (tsigOracles (realLift (σ := σ)) (SeedHitProof.Dealt.hmap (realHom σ) d) q)
      (fun _ s => Ψ s) (fun s => 0 + Ψ s) := fun st =>
  (RCost.lift (htsig st) Ψ).of_eq
    (SeedHitProof.hom_tsigOracles (realHom σ) (fun oa => free (liftComp oa _)) d q st)

omit [Fintype E] [DecidableEq E] in
theorem rcostT_secOracles (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (hround : ∀ state sent, IsQueryBoundP (A.net.round state sent) HashCall step)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (top : TopTree) (q : TsigQuery C) :
    RCostT (callCharge Logged)
      (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu
        (SeedHitProof.Dealt.hmap (realHom A.net.State) (worldDealt₀ parameter seeds dealt top)) q)
      (fun _ s => runsLeft circuits settings runLimit step s) (fun s => 0 + runsLeft circuits settings runLimit step s) := by
  have htsig : ∀ q st, cost (callCharge Logged) ((tsigOracles (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q).run st) ≤ 0 :=
    cost_dealerOracles _ (fun oa _ => cost_logged_free oa) parameter seeds dealt top
  unfold secOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact (RCostT.pure _ _).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm
  · dsimp only
    unfold secTreeRequest
    refine RCostT.bind (K := fun _ s => runsLeft circuits settings runLimit step s)
      ((rcostT_tsig _ _ (htsig _) _).mono (fun _ _ => le_rfl) fun _ => le_rfl) fun answer => ?_
    have tail : RCostT (callCharge Logged) (StateT.lift get >>= fun s : RealState C A.net.State =>
        match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => pure (some (tree, ρ))
        | _, _ => pure none : StateT (TsigState C) (RealM C A.net.State) _)
        (fun _ s => runsLeft circuits settings runLimit step s) (fun s => runsLeft circuits settings runLimit step s) := by
      refine RCostT.get_bind fun s st => ?_
      split <;> exact le_rfl
    by_cases hc : m.skip = false ∨ answer.isSome
    · simp only [hc, ↓reduceIte]
      exact RCostT.bind (RCostT.lift (rcost_secRuns K circuits settings runLimit D step m hm A.net hround
        parameter seeds dealt emu _ 1)) fun _ => tail
    · simp only [hc, ↓reduceIte]
      exact tail
  all_goals
    dsimp only
    unfold secSignRequest
    refine RCostT.bind (K := fun _ s => runsLeft circuits settings runLimit step s)
      ((RCostT.lift (RCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_of_eq (zero_add _).symm) fun _ => ?_
    refine RCostT.get_bind fun s st => ?_
    cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
      first
        | exact ((rcostT_tsig _ _ (htsig _) _) st s).trans (le_of_eq (zero_add _))
        | exact le_rfl

theorem cost_adversary_query (t : (LocalSpec C).Domain) :
    cost (callCharge Logged) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) ≤ callCharge HashCall t := by
  rw [ThresholdLeanXmssSecurity.adversary_query]
  exact cost_query_le _

omit [Fintype E] [DecidableEq E] in
/-- The signing phase with the answers of the dealer costs the calls of `forge` and the runs that
remain. -/
theorem rcost_secSigning (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (hround : ∀ state sent, IsQueryBoundP (A.net.round state sent) HashCall step) (F : ℕ∞)
    (hforge : ∀ pk top, cost (forgeCharge (callCharge HashCall)) (A.forge pk top) ≤ F)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    RCost (callCharge Logged) (secSigning K circuits settings runLimit m D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun s => F + runsLeft circuits settings runLimit step s) := by
  unfold secSigning
  refine RCost.get_bind fun s => ?_
  cases topHolder D s.operators with
  | none => exact zero_le
  | some kt =>
    simp only
    unfold worldDealer
    simp only [bind_assoc, pure_bind]
    have e₂ : referenceTree (fun oa => realLift (σ := A.net.State) (tweakable oa)) (fun x => realLift (prfValue seeds x))
        parameter emptyTop .top = realHom A.net.State (referenceTree (fun oa => free (liftComp (tweakable oa) _))
          (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top) :=
      (SeedHitProof.hom_referenceTree (realHom A.net.State) (fun oa => free (liftComp (tweakable oa) _))
        (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
    rw [e₂]
    refine (?_ : RCost (callCharge Logged) _ (fun _ _ => 0) fun s => F + runsLeft circuits settings runLimit step s) s
    refine RCost.bind (K := fun _ s => F + runsLeft circuits settings runLimit step s)
      ((RCost.lift (cost_dealerTree _ (fun oa _ => cost_logged_free oa) _ _) _).mono (fun _ _ => le_rfl)
        fun _ => le_of_eq (zero_add _)) fun out => ?_
    have d₂ : dealtWith (realLift (σ := A.net.State)) parameter dealt ((TreeOutput.topTree out).getD emptyTop)
        (fun x => realLift (prfValue seeds x)) =
        SeedHitProof.Dealt.hmap (realHom A.net.State)
          (worldDealt₀ parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) :=
      (hmap_dealtWith_hom (realHom A.net.State) (fun oa => free (liftComp oa _)) parameter dealt
        ((TreeOutput.topTree out).getD emptyTop) fun x => free (liftComp (prfValue seeds x) _)).symm
    rw [d₂]
    refine RCost.bind (K := fun _ s => runsLeft circuits settings runLimit step s)
      (((RCostT.simulateQ (c := callCharge Logged) _ (forgeCharge (callCharge HashCall))
        (runsLeft circuits settings runLimit step) (fun t => ?_) _) _).mono
        (fun _ _ => le_rfl) fun s => add_le_add (hforge _ _) le_rfl) fun p => ?_
    · rcases t with t | q | q
      · exact RCostT.lift (RCost.lift (cost_adversary_query t) _)
      · exact rcostT_secOracles K circuits settings runLimit D step m hm A hround parameter seeds dealt emu _ q
      · rcases q with _ | state
        · exact (RCostT.lift (RCost.map_get _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
        · exact (RCostT.lift (RCost.modify _ _)).mono (fun _ _ => le_rfl) fun _ => le_add_self
    · rcases p with ⟨forgery, st⟩
      exact ((RCost.lift (cost_dealerWins _ (fun oa _ => cost_logged_free oa) _ _ _ _ st forgery) fun _ => 0).of_eq
        (hom_forgeryWins (realHom A.net.State) (fun oa => free (liftComp oa _)) _ st forgery)).mono
          (fun _ _ => le_rfl) fun _ => by simp

omit [Fintype E] [DecidableEq E] in
theorem rcost_secRest (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E)
    (hround : ∀ state sent, IsQueryBoundP (A.net.round state sent) HashCall step) (F : ℕ∞)
    (hforge : ∀ pk top, cost (forgeCharge (callCharge HashCall)) (A.forge pk top) ≤ F)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    RCost (callCharge Logged) (secRest K circuits settings runLimit m D A parameter seeds dealt emu)
      (fun _ _ => 0) (fun s => step + (F + runsLeft circuits settings runLimit step s)) := by
  unfold secRest
  refine RCost.get_bind fun s => ?_
  refine (RCost.bind (K := fun _ _ => F + runsLeft circuits settings runLimit step s) (k := fun _ _ => (0 : ℕ∞))
    (RCost.lift (cost_voteRound_logged D step A.net hround _ _) fun _ => F + runsLeft circuits settings runLimit step s)
    fun v => ?_) s
  obtain ⟨state, ok⟩ := v
  refine RCost.bind ((RCost.set _ (fun _ s => F + runsLeft circuits settings runLimit step s)).mono
    (fun _ _ => le_rfl) fun _ => le_rfl) fun _ => ?_
  exact RCost.bind (K := fun _ s => F + runsLeft circuits settings runLimit step s)
    ((rcost_secRuns K circuits settings runLimit D step m hm A.net hround parameter seeds dealt (committed ok emu) .top
      runLimit).frame F |>.mono (fun _ s => le_of_eq (add_comm _ _)) fun s => le_of_eq (add_comm _ _))
    fun _ => rcost_secSigning K circuits settings runLimit D step m hm A hround F hforge parameter seeds dealt
      (committed ok emu)

theorem hashCall_ownCost (t : (LocalSpec C).Domain) (h : HashCall t) : 1 ≤ ownCost t := by
  rcases t with n | q | x
  · exact h.elim
  · exact le_rfl
  · exact h.elim

theorem forgeCharge_le_forgeCost {σ : Type} (t : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain) :
    forgeCharge (callCharge HashCall) t ≤ (forgeCost t : ℕ∞) := by
  rcases t with ((n | q | x)) | t
  · simp [forgeCharge, callCharge, HashCall]
  · simp [forgeCharge, callCharge, HashCall, forgeCost, adversaryCost]
  · simp [forgeCharge, callCharge, HashCall]
  · exact zero_le

omit [Fintype E] [DecidableEq E] in
/-- `dealtRun` with no emulated run makes at most `q` calls of `Logged` for an adversary with the
budget `q`. -/
theorem logged_dealtRun (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    IsQueryBoundP (dealtRun K circuits settings runLimit m D A) Logged q := by
  obtain ⟨start, step, forge, hsum, hstart, hround, hforge⟩ := bounded
  have hstart' : ∀ x z, IsQueryBoundP (A.net.start x z) HashCall start := fun x z =>
    isQueryBoundP_of_queryCostAtMost (hstart x z) hashCall_ownCost
  have hround' : ∀ st sent, IsQueryBoundP (A.net.round st sent) HashCall step := fun st sent =>
    isQueryBoundP_of_queryCostAtMost (hround st sent) hashCall_ownCost
  have hforge' : ∀ pk top, cost (forgeCharge (callCharge HashCall)) (A.forge pk top) ≤ (forge : ℕ∞) :=
    fun pk top => (PFunctor.FreeM.cost_mono forgeCharge_le_forgeCost _).trans
      ((queryCostAtMost_iff_cost_le _ _ _).1 (hforge pk top))
  rw [← cost_callCharge_le_iff]
  unfold dealtRun
  refine (cost_bind_le_add ((cost_callCharge_le_iff _ _ _).2
    (logged_worldSeedGen D A.net start step hstart' hround'))
    (m := (((dkgTsigRounds circuits settings runLimit - setupRounds) * step + forge : ℕ) : ℕ∞)) fun x => ?_).trans ?_
  · obtain ⟨state, parameter, seeds, dealt, emu⟩ := x
    refine (cost_bind_le_add (m := 0) ?_ fun _ => cost_pure_le _ _ _).trans (le_of_eq (add_zero _))
    rw [StateT.run'_eq, cost_map_eq]
    have h := rcost_secRest K circuits settings runLimit D step m hm A hround' forge hforge' parameter seeds dealt emu
      (startState D state fun i => (emu i).map fun _ => dealt i)
    refine h.trans (le_of_eq ?_)
    change (step : ℕ∞) + ((forge : ℕ∞) + ((FirstCounts.remaining runLimit
      (fun _ => treeFuel circuits settings * step + step) (fun _ => 0) : ℕ) : ℕ∞)) = _
    rw [← remaining_start]
    push_cast
    ring
  · rw [← Nat.cast_add]
    exact_mod_cast budget_arith circuits settings runLimit start step forge q hsum

end Rest

end LoggedCount

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.LoggedCount.logged_dealtRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.LoggedCount.logged_dealtRun
