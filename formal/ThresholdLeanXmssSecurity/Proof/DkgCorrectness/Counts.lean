import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk

/-!
# The count of the cells of the first run by class

`Within c cache k` states that the cells of class `c` of a hash cache lie in a set of at most `k`
inputs. `firstRun_within` and `firstCount_of` count the cells of `firstRun` by class, and
`recordedBelow` states that the world of the first bad record is below the final world.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace FirstCounts

open GameCount (CellIn)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_sequenceFin)

attribute [local instance] Classical.propDecidable

/-! ## The cells of a class -/

section Cells

variable {C : Committee}

/-- The cells of class `c` of the hash cache `cache` lie in a set of at most `k` inputs. -/
def Within (c : HashClass) (cache : HashCache C) (k : ℕ) : Prop :=
  ∃ cells : Finset (Query C), cells.card ≤ k ∧ ∀ x, CellIn c x → cache x ≠ none → x ∈ cells

theorem Within.mono {c : HashClass} {cache : HashCache C} {k l : ℕ} (h : Within c cache k) (hkl : k ≤ l) :
    Within c cache l := by
  obtain ⟨cells, hcard, hcover⟩ := h
  exact ⟨cells, hcard.trans hkl, hcover⟩

theorem within_empty (c : HashClass) : Within c (∅ : HashCache C) 0 :=
  ⟨∅, le_rfl, fun _ _ hx => absurd rfl hx⟩

end Cells

/-! ## The calls that add a cell of a class -/

section Calls

variable {C : Committee} (prims : Primitives)

/-- A call of the world that can add a cell of class `c` to the hash cache. It is a local call in
class `c` on either copy, or a programming call. -/
def Adds (c : HashClass) : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => InClass c t
  | .inl (.inr _) => True
  | .inr t => InClass c t

/-- A call of a lazy random oracle adds at most the cell of its input. -/
theorem randomOracle_cells {α β : Type} [DecidableEq α] [SampleableType β] (q : α)
    (s : (α →ₒ β).QueryCache) (p : β × (α →ₒ β).QueryCache)
    (hp : p ∈ support (((α →ₒ β).randomOracle q).run s)) : ∀ x, p.2 x ≠ none → s x ≠ none ∨ x = q := by
  rcases hs : s q with _ | u
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs] at hp
    erw [support_map, Set.mem_image] at hp
    obtain ⟨u, _, rfl⟩ := hp
    intro x hx
    by_cases hxq : x = q
    · exact Or.inr hxq
    · left
      simpa [QueryCache.cacheQuery_of_ne _ _ hxq] using hx
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact fun x hx => Or.inl hx

/-- A call of `H` adds at most the cell of its input. -/
theorem hashAnswer_cells (q : Query C) (s : HashCache C) (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims q).run s)) : ∀ x, p.2 x ≠ none → s x ≠ none ∨ x = q := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm] at hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact fun x hx => Or.inl hx
  · rw [hashAnswer_of_not_isFixed prims hq] at hp
    exact randomOracle_cells q s p hp

/-- A local call adds at most the cell of its input, and a call of `PRG` the cell of its stream key. -/
theorem localAnswer_cells (c : HashClass) (t : (LocalSpec C).Domain) (s : HashCache C)
    (p : (LocalSpec C).Range t × HashCache C) (hp : p ∈ support ((localAnswer prims t).run s)) :
    ∃ key, ∀ x, CellIn c x → p.2 x ≠ none → s x ≠ none ∨ (InClass c t ∧ x = key) := by
  rcases t with n | q | y
  · change p ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s) at hp
    simp [unifFwdImpl] at hp
    obtain ⟨a, rfl⟩ := hp
    exact ⟨.copy [], fun x _ hx => Or.inl hx⟩
  · refine ⟨q, fun x hx hpx => ?_⟩
    rcases hashAnswer_cells prims q s p hp x hpx with h | rfl
    · exact Or.inl h
    · refine Or.inr ⟨?_, rfl⟩
      cases x <;> simp_all [CellIn, InClass]
  · change p ∈ support ((prgAnswer prims y).run s) at hp
    unfold prgAnswer at hp
    rw [StateT.run_bind, mem_support_bind_iff] at hp
    obtain ⟨p', hp', hp⟩ := hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨.streamKey y.2.1, fun x hx hpx => ?_⟩
    rcases hashAnswer_cells prims _ s p' hp' x hpx with h | rfl
    · exact Or.inl h
    · exact Or.inr ⟨by simpa [CellIn, queryClass, InClass, eq_comm] using hx, rfl⟩

/-- A programming call adds at most the cell of its input. -/
theorem programAnswer_cells (y : Query C × HashOutput) (s : HashCache C) (p : Bool × HashCache C)
    (hp : p ∈ support ((programAnswer y).run s)) : ∀ x, p.2 x ≠ none → s x ≠ none ∨ x = y.1 := by
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hp
  split_ifs at hp
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact fun x hx => Or.inl hx
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    intro x hx
    by_cases hxy : x = y.1
    · exact Or.inr hxy
    · left
      simpa [QueryCache.cacheQuery_of_ne _ _ hxy] using hx

theorem onHash_support {α : Type} {m : StateT (HashCache C) ProbComp α} {w : StreamState C}
    {z : α × StreamState C} (hz : z ∈ support ((onHash m).run w)) :
    ∃ r ∈ support (m.run w.1), z = (r.1, (r.2, w.2)) := by
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact ⟨r, hr, rfl⟩

/-- A call of `streamWorld` adds at most one cell of class `c` to the hash cache, and only if it is a
call of `Adds c`. -/
theorem streamWorld_cells (c : HashClass) (D : C.Coalition) (t : (WorldSpec C).Domain) (w : StreamState C) :
    ∀ z ∈ support ((streamWorld prims D t).run w),
      ∃ key, ∀ x, CellIn c x → z.2.1 x ≠ none → w.1 x ≠ none ∨ (Adds c t ∧ x = key) := by
  have hlocal : ∀ (u : (LocalSpec C).Domain), ∀ z ∈ support ((onHash (localAnswer prims u)).run w),
      ∃ key, ∀ x, CellIn c x → z.2.1 x ≠ none → w.1 x ≠ none ∨ (InClass c u ∧ x = key) := by
    intro u z hz
    obtain ⟨r, hr, rfl⟩ := onHash_support hz
    exact localAnswer_cells prims c u w.1 r hr
  rcases t with ((u | y) | (u | q | x))
  · exact hlocal u
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := onHash_support hz
    exact ⟨y.1, fun x _ hx => (programAnswer_cells y w.1 r hr x hx).imp_right fun h => ⟨trivial, h⟩⟩
  · exact hlocal (.inl u)
  · exact hlocal (.inr (.inl q))
  · show ∀ z ∈ support ((if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w), _
    split_ifs
    · intro z hz
      simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨r, _, rfl⟩ := hz
      exact ⟨.copy [], fun x _ hx => Or.inl hx⟩
    · exact hlocal (.inr (.inr x))

/-- One call of `streamWorld` keeps the cells of class `c` within one more cell for a call of
`Adds c`. -/
theorem streamWorld_within (c : HashClass) (D : C.Coalition) (t : (WorldSpec C).Domain) (w : StreamState C)
    (k : ℕ) (hw : Within c w.1 k) :
    ∀ z ∈ support ((streamWorld prims D t).run w), Within c z.2.1 (k + if Adds c t then 1 else 0) := by
  intro z hz
  obtain ⟨key, hkey⟩ := streamWorld_cells prims c D t w z hz
  obtain ⟨cells, hcard, hcover⟩ := hw
  split_ifs with ht
  · refine ⟨insert key cells, (Finset.card_insert_le _ _).trans (by omega), fun x hx hzx => ?_⟩
    rcases hkey x hx hzx with h | ⟨_, rfl⟩
    · exact Finset.mem_insert_of_mem (hcover x hx h)
    · exact Finset.mem_insert_self _ _
  · refine ⟨cells, by omega, fun x hx hzx => ?_⟩
    rcases hkey x hx hzx with h | ⟨h, _⟩
    · exact hcover x hx h
    · exact absurd h ht

/-- A computation of the world with at most `n` calls of `Adds c` adds at most `n` cells of class
`c` under `streamWorld`. -/
theorem simulateQ_within (c : HashClass) (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ n, IsQueryBoundP oa (Adds c) n → ∀ w k, Within c w.1 k →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run w), Within c z.2.1 (k + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ w k hw z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw.mono (Nat.le_add_right _ _)
  | query_bind t f ih =>
    intro n hn w k hw z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    refine (ih y.1 _ (hn.2 y.1) y.2 _ (streamWorld_within prims c D t w k hw y hy) z hz).mono ?_
    split_ifs with ht
    · have := hn.1.resolve_left (not_not.2 ht)
      omega
    · omega

/-- A count of two kinds of calls gives a count of the calls that are of one of the two kinds. -/
theorem isQueryBoundP_add {ι α : Type} {spec : OracleSpec ι} {p q r : ι → Prop} (h : ∀ t, r t → p t ∨ q t)
    (oa : OracleComp spec α) :
    ∀ a b, IsQueryBoundP oa p a → IsQueryBoundP oa q b → IsQueryBoundP oa r (a + b) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro a b _ _; trivial
  | query_bind t k ih =>
    intro a b ha hb
    rw [isQueryBoundP_query_bind_iff] at ha hb ⊢
    refine ⟨?_, fun u => (ih u _ _ (ha.2 u) (hb.2 u)).mono ?_⟩
    · by_cases hr : r t
      · rcases h t hr with hp | hq
        · exact Or.inr (by have := ha.1.resolve_left (not_not.2 hp); omega)
        · exact Or.inr (by have := hb.1.resolve_left (not_not.2 hq); omega)
      · exact Or.inl hr
    · by_cases hr : r t
      · simp only [hr, ↓reduceIte]
        rcases h t hr with hp | hq
        · have := ha.1.resolve_left (not_not.2 hp)
          simp only [hp, ↓reduceIte]
          split_ifs <;> omega
        · have := hb.1.resolve_left (not_not.2 hq)
          simp only [hq, ↓reduceIte]
          split_ifs <;> omega
      · simp only [hr, ↓reduceIte]
        split_ifs <;> omega

/-- A call of the monitor adds no cell of a class other than `signing`. -/
theorem monitorCall_not_adds {c : HashClass} (hc : c ≠ .signing) {t : (WorldSpec C).Domain}
    (h : GameCount.MonitorCall t) : ¬ Adds c t := by
  rcases t with _ | _ | (q | _)
  · exact fun h' => h.elim
  · exact h.elim
  · cases q <;> simp_all [GameCount.MonitorCall, GameCount.SignCall, Adds, InClass, queryClass, eq_comm]
  · exact h.elim

/-- A computation of `H` and `PRG` on `.hash` and `.prf` only, on the free copy, makes no call of
`Adds c` for a class other than `signing`. -/
theorem free_noAdds {c : HashClass} (hc : c ≠ .signing) {α : Type} {oa : OracleComp (RoSpec C) α}
    (h : GameCount.OnlySign oa) : IsQueryBoundP (free (liftComp oa (LocalSpec C))) (Adds c) 0 :=
  (isQueryBoundP_congr_pred fun _ => not_not).1
    ((isQueryBoundP_zero_iff _ _).2 ((GameCount.allQueries_free_liftComp h).mono
      fun _ ht => monitorCall_not_adds hc ht))

end Calls

/-! ## The own calls of the phases with the programming calls -/

section Own

variable {C : Committee} {E : Type} (c : HashClass)

/-- An own call in class `c` or a programming call. -/
def OwnAdds : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => InClass c t
  | .inl (.inr _) => True
  | .inr _ => False

theorem adds_or {t : (WorldSpec C).Domain} (h : Adds c t) : OwnAdds c t ∨ HonestIn c t := by
  rcases t with (t | t) | t
  · exact Or.inl h
  · exact Or.inl trivial
  · exact Or.inr h

/-- The bound on the calls of `OwnAdds` for a computation of the adversary. -/
theorem ownAdds_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (InClass c) n) : IsQueryBoundP (worldRoles.adversary oa) (OwnAdds c) n := by
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

/-- A free computation makes no call of `OwnAdds`. -/
theorem ownAdds_free {β : Type} (oa : OracleComp (LocalSpec C) β) : NoCall (OwnAdds c) (free oa) := by
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

/-- The bound on the calls of `OwnAdds` for one round on the network. -/
theorem ownAdds_stepRound {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass c) step) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) (OwnAdds c) step := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  refine (isQueryBoundP_bind (ownAdds_adversary c _ step (hround _ _)) fun p _ => ?_).mono (Nat.add_zero _).le
  rw [← noCall_iff]
  obtain ⟨state', sent⟩ := p
  refine noCall_bind _ (noCall_sequenceFin _ _ fun j => ?_) fun _ => noCall_pure _ _
  split
  · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact ownAdds_free c _
  · exact noCall_pure _ _

/-- The bound on the calls of `OwnAdds` for the rounds of a phase. -/
theorem ownAdds_executeRounds {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass c) step) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps) (OwnAdds c) (fuel * step)
  | 0, state, steps => trivial
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · trivial
    · refine (isQueryBoundP_bind (ownAdds_stepRound c D A step hround state steps) fun p _ => ?_).mono
        (by rw [Nat.succ_mul, Nat.add_comm])
      obtain ⟨state', steps', _⟩ := p
      exact ownAdds_executeRounds D A step hround fuel state' steps'

/-- The bound on the calls of `OwnAdds` for a phase. -/
theorem ownAdds_executePhase {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass c) step) (fuel : ℕ)
    (state : A.State) (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program) (OwnAdds c) (fuel * step) := by
  unfold executePhase startSteps
  refine (isQueryBoundP_bind (n := 0) ?_ fun steps _ =>
    ownAdds_executeRounds c D A step hround fuel state steps).mono (Nat.zero_add _).le
  rw [← noCall_iff]
  refine noCall_sequenceFin _ _ fun i => ?_
  split_ifs
  · exact noCall_pure _ _
  · exact ownAdds_free c _

/-- The bound on the calls of `OwnAdds` for a real execution. -/
theorem ownAdds_realExecution {I O : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) (InClass c) start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) (InClass c) step) (fuel : ℕ)
    (program : C.Party → I → PartyM C E RealSpec O) (x : C.Party → I) (z : Aux) :
    IsQueryBoundP (realExecution D A noFunctionality fuel program x z) (OwnAdds c) (start + fuel * step) := by
  unfold realExecution
  exact isQueryBoundP_bind (ownAdds_adversary c _ _ (hstart _ _)) fun state _ =>
    ownAdds_executePhase c D A step hround fuel state _

end Own

/-! ## A potential through the game after the PRF hop -/

section Moves

variable {C : Committee} {σ : Type} (I : ℕ → FirstState C σ → StreamState C → Prop)

/-- A computation of the game that moves the potential `I k` to `I (k + n)`. -/
def Moves {α : Type} (n : ℕ) (m : FirstM C σ α) : Prop :=
  ∀ k s w, I k s w → ∀ z ∈ support ((m.run s).run w), I (k + n) z.1.2 z.2

/-- A computation of the signing phase that moves the potential by `n` from each state of the signing
game. -/
def MovesT {α : Type} (n : ℕ) (m : StateT (TsigState C) (FirstM C σ) α) : Prop := ∀ t, Moves I n (m.run t)

variable {I}

theorem moves_pure {α : Type} (a : α) : Moves I 0 (pure a : FirstM C σ α) := by
  intro k s w hs z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hs

theorem moves_bind {α β : Type} {n l : ℕ} {m : FirstM C σ α} {f : α → FirstM C σ β} (hm : Moves I n m)
    (hf : ∀ a, Moves I l (f a)) : Moves I (n + l) (m >>= f) := by
  intro k s w hs z hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rw [← Nat.add_assoc]
  exact hf y.1.1 (k + n) y.1.2 y.2 (hm k s w hs y hy) z hz

theorem moves_mono (hI : ∀ k k' s w, k ≤ k' → I k s w → I k' s w) {α : Type} {n l : ℕ} {m : FirstM C σ α}
    (h : Moves I n m) (hnl : n ≤ l) : Moves I l m :=
  fun k s w hs z hz => hI _ _ _ _ (by omega) (h k s w hs z hz)

theorem movesT_lift {α : Type} {n : ℕ} {m : FirstM C σ α} (hm : Moves I n m) :
    MovesT I n (StateT.lift m : StateT (TsigState C) (FirstM C σ) α) := fun t => by
  rw [StateT.run_lift]
  exact moves_bind hm fun _ => moves_pure _

theorem movesT_bind {α β : Type} {n l : ℕ} {m : StateT (TsigState C) (FirstM C σ) α}
    {f : α → StateT (TsigState C) (FirstM C σ) β} (hm : MovesT I n m) (hf : ∀ a, MovesT I l (f a)) :
    MovesT I (n + l) (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact moves_bind (hm t) fun y => hf y.1 y.2

/-- A computation with at most `n` calls of `p` moves the potential by `n` when each call of `p`
moves it by one and each other call by zero. -/
theorem movesT_simulateQ (hI : ∀ k k' s w, k ≤ k' → I k s w → I k' s w) {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT (TsigState C) (FirstM C σ))) (p : ι → Prop)
    (h : ∀ q, MovesT I (if p q then 1 else 0) (impl q)) {α : Type} (oa : OracleComp spec α) :
    ∀ n, IsQueryBoundP oa p n → MovesT I n (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ t
    rw [simulateQ_pure, StateT.run_pure]
    exact moves_mono hI (moves_pure _) (Nat.zero_le _)
  | query_bind q k ih =>
    intro n hn t
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    refine moves_mono hI (moves_bind (h q t) fun y => ih y.1 _ (hn.2 y.1) y.2) ?_
    split_ifs with hq
    · have := hn.1.resolve_left (not_not.2 hq)
      omega
    · omega

theorem moves_get_bind {β : Type} {n : ℕ} {f : FirstState C σ → FirstM C σ β} (hf : ∀ s, Moves I n (f s)) :
    Moves I n (get >>= f) := by
  intro k s w hs z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf s k s w hs z hz

theorem moves_get : Moves I 0 (get : FirstM C σ _) := by
  intro k s w hs z hz
  simp only [StateT.run_get] at hz
  subst hz
  exact hs

theorem moves_modify (f : FirstState C σ → FirstState C σ) (h : ∀ k s w, I k s w → I k (f s) w) :
    Moves I 0 (modify f : FirstM C σ Unit) := by
  intro k s w hs z hz
  simp only [StateT.run_modify] at hz
  subst hz
  exact h k s w hs

end Moves

/-! ## The cells of a class through `firstRun` -/

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget) (c : HashClass) (cost : Tree → ℕ)

/-- The budget of the runs that remain, with the cost `cost tree` for each run of `tree`. -/
def remaining (runs : Tree → ℕ) : ℕ :=
  (runLimit - runs .top) * cost .top +
    ∑ b : Fin (2 ^ layerHeight), (runLimit - runs (.bottom b)) * cost (.bottom b)

/-- One more run of `tree` takes its cost from the budget of the runs that remain. -/
theorem remaining_update (runs : Tree → ℕ) (tree : Tree) (h : runs tree < runLimit) :
    remaining runLimit cost (Function.update runs tree (runs tree + 1)) + cost tree =
      remaining runLimit cost runs := by
  unfold remaining
  cases tree with
  | top =>
    have hb : ∀ b : Fin (2 ^ layerHeight),
        Function.update runs Tree.top (runs .top + 1) (.bottom b) = runs (.bottom b) :=
      fun b => Function.update_of_ne (by simp) _ _
    simp only [Function.update_self, hb]
    have e : runLimit - runs .top = (runLimit - (runs .top + 1)) + 1 := by omega
    rw [e]
    ring
  | bottom b =>
    have ht : Function.update runs (.bottom b) (runs (.bottom b) + 1) .top = runs .top :=
      Function.update_of_ne (by simp) _ _
    rw [ht, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    have he : ∀ b' ∈ Finset.univ.erase b,
        (runLimit - Function.update runs (.bottom b) (runs (.bottom b) + 1) (.bottom b')) * cost (.bottom b') =
          (runLimit - runs (.bottom b')) * cost (.bottom b') := by
      intro b' hb'
      rw [Function.update_of_ne]
      intro heq
      exact (Finset.mem_erase.1 hb').1 (Tree.bottom.inj heq)
    rw [Finset.sum_congr rfl he, Function.update_self]
    have e : runLimit - runs (.bottom b) = (runLimit - (runs (.bottom b) + 1)) + 1 := by omega
    rw [e]
    ring

/-- The potential of the count. The cells of class `c` lie within `k'`, and `k'` with the budget of the
runs that remain is at most `k`. -/
def Pot {σ : Type} (k : ℕ) (s : FirstState C σ) (w : StreamState C) : Prop :=
  ∃ k', Within c w.1 k' ∧ k' + remaining runLimit cost s.real.runs ≤ k

theorem pot_mono {σ : Type} :
    ∀ k k' (s : FirstState C σ) w, k ≤ k' → Pot runLimit c cost k s w → Pot runLimit c cost k' s w := by
  rintro k k' s w hkk' ⟨k'', hw, hk⟩
  exact ⟨k'', hw, hk.trans hkk'⟩

/-- The computation of the world of one run of `tree`, which `streamTreeRun` answers by
`streamWorld`. -/
def treeBlock (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State) :
    OracleComp (WorldSpec C) ((net.State × (C.Party → Option TreeOutput)) × Bool) := do
  let r ← executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary fun i =>
    treeProgram K circuits settings i (s.operators i) tree
  let bad ← wrongOutput D (fun i => (s.operators i).keys) tree r.2
  pure (r, bad)

/-- A computation of the world with at most `n` calls of `Adds c` moves the potential by `n`. -/
theorem inStream_moves (D : C.Coalition) {σ β : Type} (oa : OracleComp (WorldSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (Adds c) n) : Moves (Pot runLimit c cost) n (inStream (σ := σ) prims D oa) := by
  rintro k s w ⟨k', hw, hk⟩ z hz
  simp only [inStream, StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨k' + n, simulateQ_within prims c D oa n h w k' hw y hy, ?_⟩
  change k' + n + remaining runLimit cost s.real.runs ≤ k + n
  omega

omit [Field E] [Algebra Bit E] in
theorem mayRun_lt {σ : Type} {D : C.Coalition} {s : RealState C σ} {tree : Tree} (h : mayRun runLimit D s tree) :
    s.runs tree < runLimit := by
  cases tree with
  | top => exact h.1
  | bottom b => exact h.2.1

/-- A run of `tree` that the game allows keeps the potential, when the computation of its world has at
most `cost tree` calls of `Adds c`. -/
theorem firstTreeRun_pot (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (hblock : ∀ s, GameCount.Bound (Adds c) (treeBlock K circuits settings D net tree s) (cost tree))
    (k : ℕ) (s : FirstState C net.State) (w : StreamState C) (hs : Pot runLimit c cost k s w)
    (hrun : s.real.runs tree < runLimit) :
    ∀ z ∈ support (((firstTreeRun prims K circuits settings budget D net tree).run s).run w),
      Pot runLimit c cost k z.1.2 z.2 := by
  intro z hz
  unfold firstTreeRun at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  obtain ⟨k', hw, hk⟩ := hs
  refine ⟨k' + cost tree,
    simulateQ_within prims c D _ _ ((GameCount.bound_iff _ _ _).1 (hblock s.real)) w k' hw x hx, ?_⟩
  have := remaining_update runLimit cost s.real.runs tree hrun
  change k' + cost tree + remaining runLimit cost (Function.update s.real.runs tree (s.real.runs tree + 1)) ≤ k
  omega

theorem firstTreeRuns_moves (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (hblock : ∀ s, GameCount.Bound (Adds c) (treeBlock K circuits settings D net tree s) (cost tree)) :
    ∀ count, Moves (Pot runLimit c cost) 0 (firstTreeRuns prims K circuits settings runLimit budget D net tree count)
  | 0 => moves_pure _
  | count + 1 => by
    intro k s w hs z hz
    unfold firstTreeRuns at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz with hmay
    · simp only [StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      exact firstTreeRuns_moves D net tree hblock count k y.1.2 y.2
        (firstTreeRun_pot prims K circuits settings runLimit budget c cost D net tree hblock k s w hs
          (mayRun_lt runLimit hmay) y hy) z hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs

theorem firstTreeRequest_moves (hc : c ≠ .signing) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight))
    (hblock : ∀ s, GameCount.Bound (Adds c) (treeBlock K circuits settings D net (.bottom b) s) (cost (.bottom b))) :
    Moves (Pot runLimit c cost) 0 (firstTreeRequest prims K circuits settings runLimit budget D net b) := by
  unfold firstTreeRequest
  refine moves_bind (n := 0) (l := 0) (firstTreeRuns_moves prims K circuits settings runLimit budget c cost D net _
    hblock 1) fun _ => moves_get_bind fun s => ?_
  split
  · exact moves_bind (n := 0) (l := 0) (inStream_moves prims runLimit c cost D _ 0
      (free_noAdds hc (GameCount.onlySign_prfValue _ _))) fun _ => moves_pure _
  · exact moves_pure _

omit [Field E] [Algebra Bit E] in
/-- The answers of the honest operators to the signing requests on the free copy make no call of
`Adds c`. -/
def SignQuiet : Prop :=
  ∀ (D : C.Coalition) (operators : C.Party → OperatorState C) (keys : Keys C) (top : TopTree)
    (q : (TsigSpec C).Domain) (t : TsigState C),
    IsQueryBoundP ((tsigOracles (fun oa => free (liftComp oa (LocalSpec C)))
      (dealtWith (fun oa => free (liftComp oa (LocalSpec C))) keys.parameter (fun _ => keys) top
        fun x => free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))) q).run t)
      (Adds c) 0

omit [Field E] [Algebra Bit E] in
/-- The answer of an honest operator keeps the potential. It is `tsigOracles` on the free copy under
the monad maps of `streamWorld` and `streamLift`. -/
theorem operatorAnswer_moves (hsign : SignQuiet (C := C) c) {σ : Type} (D : C.Coalition)
    (operators : C.Party → OperatorState C) (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    MovesT (Pot runLimit c cost)  0
      (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q) := by
  intro t
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    let ψ := simulateQ' (streamWorld prims D)
    let freeLift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β :=
      fun oa => free (liftComp oa _)
    let value : Point → OracleComp (WorldSpec C) Digest :=
      fun x => freeLift (prfValue (gameSeeds D fun i => (operators i).keys) x)
    let dealt := dealtWith freeLift keys.parameter (fun _ => keys) top value
    have hdealt : SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt) =
        dealtWith (m := FirstM C σ) (fun oa => firstLift prims D oa) keys.parameter (fun _ => keys) top
          (firstValue prims D operators) := by
      simp only [SeedHitProof.Dealt.hmap, dealt, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
      rfl
    rw [← hdealt]
    let t' : TsigState C := { t with trees := fun b => some (operator.bottom b) }
    have hom₁ := SeedHitProof.hom_tsigOracles (streamLift C σ) (fun oa => ψ (freeLift oa))
      (SeedHitProof.Dealt.hmap ψ dealt) q t'
    have hom₂ := SeedHitProof.hom_tsigOracles ψ freeLift dealt q t'
    change Moves (Pot runLimit c cost) 0 ((tsigOracles (fun oa => streamLift C σ (ψ (freeLift oa)))
      (SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt)) q).run t')
    rw [← hom₁, ← hom₂]
    exact inStream_moves prims runLimit c cost D _ 0 (hsign D operators keys top q t')
  · exact moves_pure _

omit [Field E] [Algebra Bit E] in
theorem firstSignRequest_moves (hsign : SignQuiet (C := C) c) {σ : Type} (D : C.Coalition) (i : C.Party)
    (e : KeyIndex) (q : TsigQuery C) :
    MovesT (Pot runLimit c cost) 0 (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine movesT_bind (n := 0) (l := 0) (movesT_lift (moves_modify _ fun k s w hs => hs)) fun _ =>
    movesT_bind (n := 0) (l := 0) (movesT_lift moves_get) fun s => ?_
  exact operatorAnswer_moves prims runLimit c cost hsign D _ _ _ _

theorem firstSigning_moves (hc : c ≠ .signing) (D : C.Coalition) (A : DkgTsigAdversary C E) (forge : ℕ)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass c) forge)
    (hblock : ∀ tree s, GameCount.Bound (Adds c) (treeBlock K circuits settings D A.net tree s) (cost tree))
    (hsign : SignQuiet (C := C) c) :
    Moves (Pot runLimit c cost) forge (firstSigning prims K circuits settings runLimit budget D A) := by
  unfold firstSigning
  refine moves_get_bind fun s => ?_
  split
  · refine moves_mono (pot_mono runLimit c cost) (moves_bind (l := 0) (movesT_simulateQ (pot_mono runLimit c cost)
      _ (ForgeInClass c) (fun q => ?_) _ forge (hforge _ _) _) fun _ => moves_pure _) (by omega)
    rcases q with t | q | q
    · refine movesT_lift (inStream_moves prims runLimit c cost D _ _ ?_)
      rw [ThresholdLeanXmssSecurity.adversary_query]
      change IsQueryBoundP (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) (Adds c)
        (if InClass c t then 1 else 0)
      rw [isQueryBoundP_query_iff]
      split_ifs with ht
      · exact fun _ => Nat.one_pos
      · exact fun h => absurd h ht
    · simp only [ForgeInClass, ↓reduceIte]
      rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
      · exact fun t => moves_pure _
      · exact movesT_lift (firstTreeRequest_moves prims K circuits settings runLimit budget c cost hc D A.net b
          (hblock _))
      all_goals exact firstSignRequest_moves prims runLimit c cost hsign D i e _
    · simp only [ForgeInClass, ↓reduceIte]
      rcases q with _ | state
      · exact movesT_lift (moves_bind (n := 0) (l := 0) moves_get fun _ => moves_pure _)
      · exact movesT_lift (moves_modify _ fun k s w hs => hs)
  · exact moves_mono (pot_mono runLimit c cost) (moves_pure _) (Nat.zero_le _)

/-- The cells of class `c` at the end of `firstRun` lie within the calls of `Adds c` of the seed
generation, of `runLimit` runs of each tree and of `forge`. -/
theorem firstRun_within (hc : c ≠ .signing) (D : C.Coalition) (A : DkgTsigAdversary C E) (seed forge : ℕ)
    (hseed : GameCount.Bound (Adds c) (realExecution D A.net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) seed)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass c) forge)
    (hblock : ∀ tree s, GameCount.Bound (Adds c) (treeBlock K circuits settings D A.net tree s) (cost tree))
    (hsign : SignQuiet (C := C) c) :
    ∀ r ∈ support (firstRun prims K circuits settings runLimit budget D A),
      Within c r.2.1 (seed + remaining runLimit cost (fun _ => 0) + forge) := by
  intro r hr
  unfold firstRun at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hw : Within c world.1 (0 + seed) :=
    simulateQ_within prims c D _ seed ((GameCount.bound_iff _ _ _).1 hseed) (∅, ∅) 0 (within_empty c) _ hy
  have hstart : Pot runLimit c cost (seed + remaining runLimit cost (fun _ => 0))
      (⟨startState D state keys, if (startState D state keys).flag then some (.seeds, world) else none⟩ :
        FirstState C A.net.State) world :=
    ⟨seed, hw.mono (by omega), le_rfl⟩
  obtain ⟨k', hw', hk'⟩ := moves_bind (firstTreeRuns_moves prims K circuits settings runLimit budget c cost D A.net
    .top (hblock .top) runLimit) (fun _ => firstSigning_moves prims K circuits settings runLimit budget c cost hc D A
      forge hforge hblock hsign) _ _ world hstart x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)
  exact hw'.mono (by omega)

omit [Field E] [Algebra Bit E] in
/-- The honest calls of class `c` of the seed generation on the network are at most `seed`. -/
def SeedHonest (seed : ℕ) : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty),
    GameCount.Bound (HonestIn c) (realExecution D net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) seed

/-- The honest calls of class `c` of one run of `tree` on the network are at most `honestRun tree`. -/
def TreeHonest (honestRun : Tree → ℕ) : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State),
    GameCount.Bound (HonestIn c) (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
      s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (honestRun tree)

omit [Field E] [Algebra Bit E] in
theorem bound_of_noCall {ι α : Type} {spec : OracleSpec ι} {p : ι → Prop} {oa : OracleComp spec α}
    (h : NoCall p oa) : GameCount.Bound p oa 0 := by
  rw [GameCount.bound_iff, ← noCall_iff]
  exact h

omit [Field E] [Algebra Bit E] in
theorem seedBlock_bound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (start step seed : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (net.start x z) (InClass c) start)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass c) step)
    (hseed : SeedHonest (C := C) (E := E) c seed) :
    GameCount.Bound (Adds c) (realExecution D net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])
      (start + setupRounds * step + seed) := by
  rw [GameCount.bound_iff]
  exact isQueryBoundP_add (fun _ => adds_or c) _ _ _
    (ownAdds_realExecution c D net start step hstart hround _ _ _ _)
    ((GameCount.bound_iff _ _ _).1 (hseed D net))

theorem treeBlock_bound (hc : c ≠ .signing) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass c) step) (honestRun : Tree → ℕ)
    (htree : TreeHonest K circuits settings c honestRun) (tree : Tree) (s : RealState C net.State) :
    GameCount.Bound (Adds c) (treeBlock K circuits settings D net tree s)
      (treeFuel circuits settings * step + honestRun tree) := by
  unfold treeBlock
  refine GameCount.bound_mono (GameCount.bound_bind (m := 0) ((GameCount.bound_iff _ _ _).2
    (isQueryBoundP_add (fun _ => adds_or c) _ _ _ (ownAdds_executePhase c D net step hround _ _ _)
      ((GameCount.bound_iff _ _ _).1 (htree D net tree s)))) fun r => ?_) (Nat.add_zero _).le
  exact GameCount.bound_mono (GameCount.bound_bind (n := 0) (m := 0) (bound_of_noCall
    (GameCount.wrongOutput_noCall D (Adds c) (fun _ ht => monitorCall_not_adds hc ht) _ _ _))
    fun _ => GameCount.bound_pure _ _) le_rfl

/-- The count of class `c` at the end of `firstRun`. For each recording budget, coalition and
adversary with the class budget `own`, the final hash cache has the cells of class `c` within
`own c + honest`. -/
def FirstCount (honest : ℕ) : Prop :=
  ∀ (budget : StartBudget) (D : C.Coalition) (A : DkgTsigAdversary C E) (own : HashClass → ℕ),
    DkgTsigClassBounded circuits settings runLimit A own →
      ∀ r ∈ support (firstRun prims K circuits settings runLimit budget D A), Within c r.2.1 (own c + honest)

/-- The count of class `c` from the honest calls of the seed generation and of one run of each tree,
and from the answers of the signing requests. -/
theorem firstCount_of (hc : c ≠ .signing) (seed : ℕ) (honestRun : Tree → ℕ) (hseed : SeedHonest (C := C) (E := E) c seed)
    (htree : TreeHonest K circuits settings c honestRun) (hsign : SignQuiet (C := C) c) :
    FirstCount prims K circuits settings runLimit c
      (seed + runLimit * (honestRun .top + ∑ b : Fin (2 ^ layerHeight), honestRun (.bottom b))) := by
  intro budget D A own hA r hr
  obtain ⟨start, step, forge, hsum, hs, hround, hf⟩ := hA c
  have h := firstRun_within prims K circuits settings runLimit budget c
    (fun tree => treeFuel circuits settings * step + honestRun tree) hc D A (start + setupRounds * step + seed)
    forge (seedBlock_bound c D A.net start step seed hs hround hseed) hf
    (treeBlock_bound K circuits settings c hc D A.net step hround honestRun htree) hsign r hr
  have e : remaining runLimit (fun tree => treeFuel circuits settings * step + honestRun tree) (fun _ => 0) =
      runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step +
        runLimit * (honestRun .top + ∑ b : Fin (2 ^ layerHeight), honestRun (.bottom b)) := by
    simp only [remaining, Nat.sub_zero, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have e' : dkgTsigRounds circuits settings runLimit * step =
      setupRounds * step + runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step := by
    unfold dkgTsigRounds
    ring
  rw [e] at h
  exact h.mono (by omega)

end Game

/-! ## The count and its consumers -/

section Count

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- Each world that `firstRun` records with the first bad event is below the final world. -/
def RecordedBelow : Prop :=
  ∀ (budget : StartBudget) (D : C.Coalition) (A : DkgTsigAdversary C E),
    ∀ r ∈ support (firstRun prims K circuits settings runLimit budget D A),
      ∀ stage w, r.1.first = some (stage, w) → w ≤ r.2

end Count

end FirstCounts

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

namespace RecordedCache

open Ready (Keeps KeepsT keeps_pure keeps_bind keeps_get_bind keeps_get keeps_modify keeps_lift keepsT_lift
  keepsT_bind keepsT_simulateQ)

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

/-- The world of the first bad record of `s` is below `world`. -/
def Below {σ : Type} (s : FirstState C σ) (world : StreamState C) : Prop :=
  ∀ stage w, s.first = some (stage, w) → w ≤ world

theorem below_grow {σ : Type} (s : FirstState C σ) (w w' : StreamState C) (h : Below s w) (hle : w ≤ w') :
    Below s w' :=
  fun stage w₁ hw => le_trans (h stage w₁ hw) hle

theorem firstTreeRun_below (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    Keeps Below (firstTreeRun prims K circuits settings budget D net tree) := by
  intro s world hs z hz
  unfold firstTreeRun at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  have hgrow : world ≤ x.2 := Ready.streamTreeRun_le prims K circuits settings D net tree s.real world x hx
  intro stage w hw
  change ((s.first <|> if RunReady prims budget D s.real world then none
    else some (.unready tree (s.real.runs tree), world)) <|>
      if x.1.2 then some (.run tree (s.real.runs tree), x.2) else none) = some (stage, w) at hw
  cases hfirst : s.first with
  | some v =>
    rw [hfirst, Ready.some_orElse, Ready.some_orElse] at hw
    exact le_trans (hs stage w (hfirst.trans hw)) hgrow
  | none =>
    rw [hfirst, Ready.none_orElse] at hw
    by_cases hready : RunReady prims budget D s.real world
    · rw [ite_eq_left hready, Ready.none_orElse] at hw
      split_ifs at hw
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
        exact le_refl _
    · rw [ite_eq_right hready, Ready.some_orElse] at hw
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
      exact hgrow

omit [Field E] [Algebra Bit E] in
theorem inStream_below (D : C.Coalition) {σ β : Type} (oa : OracleComp (WorldSpec C) β) :
    Keeps Below (inStream (σ := σ) prims D oa) :=
  keeps_lift below_grow (Ready.simulateQ_le prims D oa)

theorem firstTreeRuns_below (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count, Keeps Below (firstTreeRuns prims K circuits settings runLimit budget D net tree count)
  | 0 => keeps_pure _
  | count + 1 => by
    unfold firstTreeRuns
    refine keeps_get_bind fun s => ?_
    split_ifs
    · exact keeps_bind (firstTreeRun_below prims K circuits settings budget D net tree) fun _ =>
        firstTreeRuns_below D net tree count
    · exact keeps_pure _

theorem firstTreeRequest_below (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) :
    Keeps Below (firstTreeRequest prims K circuits settings runLimit budget D net b) := by
  unfold firstTreeRequest
  refine keeps_bind (firstTreeRuns_below prims K circuits settings runLimit budget D net _ 1) fun _ =>
    keeps_get_bind fun s => ?_
  split
  · exact keeps_bind (inStream_below prims D _) fun _ => keeps_pure _
  · exact keeps_pure _

omit [Field E] [Algebra Bit E] in
/-- The answer of an honest operator keeps `Below`. -/
theorem operatorAnswer_below {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    KeepsT Below
      (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q) := by
  intro t
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    let ψ := simulateQ' (streamWorld prims D)
    let freeLift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β :=
      fun oa => free (liftComp oa _)
    let value : Point → OracleComp (WorldSpec C) Digest :=
      fun x => freeLift (prfValue (gameSeeds D fun i => (operators i).keys) x)
    let dealt := dealtWith freeLift keys.parameter (fun _ => keys) top value
    have hdealt : SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt) =
        dealtWith (m := FirstM C σ) (fun oa => firstLift prims D oa) keys.parameter (fun _ => keys) top
          (firstValue prims D operators) := by
      simp only [SeedHitProof.Dealt.hmap, dealt, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
      rfl
    rw [← hdealt]
    let t' : TsigState C := { t with trees := fun b => some (operator.bottom b) }
    have hom₁ := SeedHitProof.hom_tsigOracles (streamLift C σ) (fun oa => ψ (freeLift oa))
      (SeedHitProof.Dealt.hmap ψ dealt) q t'
    have hom₂ := SeedHitProof.hom_tsigOracles ψ freeLift dealt q t'
    change Keeps Below ((tsigOracles (fun oa => streamLift C σ (ψ (freeLift oa)))
      (SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt)) q).run t')
    rw [← hom₁, ← hom₂]
    exact keeps_lift below_grow (Ready.simulateQ_le prims D _)
  · exact keeps_pure _

omit [Field E] [Algebra Bit E] in
theorem firstSignRequest_below (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    KeepsT Below (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine keepsT_bind (keepsT_lift (keeps_modify _ fun s w hs => hs)) fun _ =>
    keepsT_bind (keepsT_lift keeps_get) fun s => ?_
  exact operatorAnswer_below prims D _ _ e q

theorem firstOracles_below (D : C.Coalition) (A : DkgTsigAdversary C E) (q : TsigQuery C) :
    KeepsT Below (firstOracles prims K circuits settings runLimit budget D A q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun t => keeps_pure _
  · exact keepsT_lift (firstTreeRequest_below prims K circuits settings runLimit budget D A.net b)
  · exact firstSignRequest_below prims D i e _
  · exact firstSignRequest_below prims D i e _

theorem firstSigning_below (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Keeps Below (firstSigning prims K circuits settings runLimit budget D A) := by
  unfold firstSigning
  refine keeps_get_bind fun s => ?_
  split
  · refine keeps_bind (keepsT_simulateQ _ (fun q => ?_) _ _) fun _ => keeps_pure _
    rcases q with t | q | q
    · exact keepsT_lift (inStream_below prims D _)
    · exact firstOracles_below prims K circuits settings runLimit budget D A q
    · rcases q with _ | state
      · exact keepsT_lift (keeps_bind keeps_get fun _ => keeps_pure _)
      · exact keepsT_lift (keeps_modify _ fun s w hs => hs)
  · exact keeps_pure _

/-- Each world that `firstRun` records with the first bad event is below the final world. -/
theorem recordedBelow : FirstCounts.RecordedBelow prims K circuits settings runLimit := by
  intro budget D A r hr
  unfold firstRun at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, -, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hstart : Below (⟨startState D state keys,
      if (startState D state keys).flag then some (.seeds, world) else none⟩ : FirstState C A.net.State) world := by
    intro stage w hw
    split_ifs at hw
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
    exact le_refl _
  exact keeps_bind (firstTreeRuns_below prims K circuits settings runLimit budget D A.net .top runLimit)
    (fun _ => firstSigning_below prims K circuits settings runLimit budget D A) _ world hstart x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)

end Game

end RecordedCache

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.firstRun_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.firstRun_within

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.firstCount_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.firstCount_of

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedCache.recordedBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedCache.recordedBelow
