import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Setup
import ThresholdLeanXmssSecurity.Proof.Pilot.Split

/-!
# The birthday bound of one domain of the hash cache through the game

`birthdaySum k N` is the sum `∑ j < N - k, (k + j) / 2^256`. `world_birthday` states it for a
computation of the world in `streamWorld` with a continuation. A cache with at most `k` cells of the
domain `P` and no collision in `P` gets a collision in `P` with probability at most
`birthdaySum k N`, when the computation and the continuation together add at most `N - k` cells of
`P`.

`Birth n m` states the same for a computation `m` of the game after the PRF hop, which adds at most
`n` cells of `P` beyond the budget of the runs that remain. The walk through `firstRunOf` for a block
run (`blockRun`) follows the walk of `firstRunOf_within` in `Counts.lean` and gives `firstRun_birthday`.
The network makes no programming call (`noProgram_realExecution`). `firstCollisionOf_le` gives the
bound `(q + H)² / 2^257` at the world of the first bad record, for each readiness test, from the honest
budget `H` of the domain, for each block that keeps the honest budgets (`KeepsBudget`). The block of
`streamTreeRun` keeps them (`treeBlock_keepsBudget`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace Collision

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The birthday sum -/

/-- The birthday sum `∑ j < N - k, (k + j) / 2^256` of the cells `k` to `N - 1`. -/
def birthdaySum (k N : ℕ) : ℝ≥0∞ := ∑ j ∈ Finset.range (N - k), ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- The birthday sum from no cell is at most `N² / 2^257`. -/
theorem birthdaySum_zero_le (N : ℕ) : (birthdaySum 0 N).toReal ≤ ((N ^ 2 : ℕ) : ℝ) / 2 ^ 257 := by
  have hfin : ∀ j ∈ Finset.range N, ((0 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 ≠ ⊤ := by
    intros; finiteness
  unfold birthdaySum
  rw [Nat.sub_zero, ENNReal.toReal_sum hfin]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ← Finset.sum_div, Nat.zero_add]
  have hsum : ∀ n : ℕ, 2 * (∑ j ∈ Finset.range n, (j : ℝ)) ≤ (n : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast at *
      nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h256 : (0 : ℝ) ≤ 2 ^ 256 := by positivity
  have e : (2 : ℝ) ^ 257 = 2 ^ 256 * 2 := pow_succ 2 256
  push_cast
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right (hsum N) h256]

/-! ## The birthday bound of a computation of the world -/

/-- The step of `world_birthday` at a local call on the hash cache. -/
theorem world_local_case (prims : Primitives) (D : C.Coalition) (P : Query C → Prop) {α γ : Type}
    (u : (LocalSpec C).Domain) (f : (LocalSpec C).Range u → OracleComp (WorldSpec C) α) (n : ℕ)
    (G : α → StateT (StreamState C) ProbComp γ) (N M : ℕ) (hn : ¬ SplitRegionCounted P u ∨ 0 < n)
    (hf : ∀ r, IsQueryBoundP (f r) (WorldRegionCounted P) (if SplitRegionCounted P u then n - 1 else n))
    (hp : ∀ r, IsQueryBoundP (f r) WorldProgramQuery 0)
    (ih : ∀ r n', IsQueryBoundP (f r) (WorldRegionCounted P) n' → IsQueryBoundP (f r) WorldProgramQuery 0 →
      ∀ (G : α → StateT (StreamState C) ProbComp γ) (N M : ℕ),
      (∀ a (cache : HashCache C) (hidden : HiddenCache C) k, ¬ DomainCollision P cache →
        SplitCacheBound (splitRegionCache P cache) k → k + M ≤ N →
        Pr{let z ← (G a).run (cache, hidden)}[DomainCollision P z.2.1] ≤ birthdaySum k N) →
      ∀ (cache : HashCache C) (hidden : HiddenCache C) k, ¬ DomainCollision P cache →
        SplitCacheBound (splitRegionCache P cache) k → k + n' + M ≤ N →
        Pr{let z ← (simulateQ (streamWorld prims D) (f r) >>= G).run (cache, hidden)}[
          DomainCollision P z.2.1] ≤ birthdaySum k N)
    (hG : ∀ a (cache : HashCache C) (hidden : HiddenCache C) k, ¬ DomainCollision P cache →
      SplitCacheBound (splitRegionCache P cache) k → k + M ≤ N →
      Pr{let z ← (G a).run (cache, hidden)}[DomainCollision P z.2.1] ≤ birthdaySum k N)
    (cache : HashCache C) (hidden : HiddenCache C) (k : ℕ) (hno : ¬ DomainCollision P cache)
    (hk : SplitCacheBound (splitRegionCache P cache) k) (hkN : k + n + M ≤ N) :
    Pr{let z ← (onHash (localAnswer prims u) >>= fun r =>
      simulateQ (streamWorld prims D) (f r) >>= G).run (cache, hidden)}[DomainCollision P z.2.1] ≤
      birthdaySum k N := by
  unfold birthdaySum
  refine streamRegion_local_step prims P u _ (N - k) k ?_ cache hidden hno hk ?_
  · rcases hn with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  intro n' k' h1 h2 r s hs hsk
  by_cases hc : SplitRegionCounted P u
  · obtain ⟨rfl, rfl⟩ := h1 hc
    have hpos : 0 < n := hn.resolve_left (not_not.2 hc)
    have h := ih r (n - 1) (by simpa [hc] using hf r) (hp r) G N M hG s hidden (k + 1) hs hsk (by omega)
    unfold birthdaySum at h
    rwa [Nat.sub_sub]
  · obtain ⟨rfl, rfl⟩ := h2 hc
    exact ih r _ (by simpa [hc] using hf r) (hp r) G N M hG s hidden _ hs hsk hkN

/-- A computation of the world in `streamWorld`, followed by a continuation, keeps the birthday sum.
The computation makes at most `n` calls that add a cell of `P` and no programming call. The
continuation has the birthday sum from each cache with no collision in `P` and with at most `k`
cells of `P`, for `k + M ≤ N`. -/
theorem world_birthday (prims : Primitives) (D : C.Coalition) (P : Query C → Prop) {α γ : Type}
    (oa : OracleComp (WorldSpec C) α) : ∀ n, IsQueryBoundP oa (WorldRegionCounted P) n →
    IsQueryBoundP oa WorldProgramQuery 0 →
    ∀ (G : α → StateT (StreamState C) ProbComp γ) (N M : ℕ),
    (∀ a (cache : HashCache C) (hidden : HiddenCache C) k, ¬ DomainCollision P cache →
      SplitCacheBound (splitRegionCache P cache) k → k + M ≤ N →
      Pr{let z ← (G a).run (cache, hidden)}[DomainCollision P z.2.1] ≤ birthdaySum k N) →
    ∀ (cache : HashCache C) (hidden : HiddenCache C) k, ¬ DomainCollision P cache →
      SplitCacheBound (splitRegionCache P cache) k → k + n + M ≤ N →
      Pr{let z ← (simulateQ (streamWorld prims D) oa >>= G).run (cache, hidden)}[DomainCollision P z.2.1] ≤
        birthdaySum k N := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ _ G N M hG cache hidden k hno hk hkN
    rw [simulateQ_pure, pure_bind]
    exact hG a cache hidden k hno hk (by omega)
  | query_bind t f ih =>
    intro n hn hp G N M hG cache hidden k hno hk hkN
    rw [isQueryBoundP_query_bind_iff] at hn hp
    have hp' : ∀ r, IsQueryBoundP (f r) WorldProgramQuery 0 := fun r => by
      simpa using hp.2 r
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      bind_assoc]
    rcases t with (u | y) | (v | q | x)
    · exact world_local_case prims D P u f n G N M hn.1 hn.2 hp' (fun r => ih r) hG cache hidden k hno hk hkN
    · exact absurd hp.1 (by simp [WorldProgramQuery])
    · exact world_local_case prims D P (.inl v) f n G N M hn.1 hn.2 hp' (fun r => ih r) hG cache hidden k hno
        hk hkN
    · exact world_local_case prims D P (.inr (.inl q)) f n G N M hn.1 hn.2 hp' (fun r => ih r) hG cache hidden
        k hno hk hkN
    · by_cases hx : Hidden D x.1
      · rw [show streamWorld prims D (Sum.inr (Sum.inr (Sum.inr x))) = _ from
          ite_eq_left_of_eq_true _ _ (eq_true hx), StateT.run_bind, StateT.run_mk, bind_map_left]
        apply prEvent_bind_le_of_forall_le_of_support
        intro r _
        exact ih r.1 n ((hn.2 r.1).mono (by split_ifs <;> omega)) (hp' r.1) G N M hG cache r.2 k hno hk hkN
      · rw [show streamWorld prims D (Sum.inr (Sum.inr (Sum.inr x))) =
          onHash (localAnswer prims (.inr (.inr x))) from ite_eq_right_of_eq_false _ _ (eq_false hx)]
        exact world_local_case prims D P (.inr (.inr x)) f n G N M hn.1 hn.2 hp' (fun r => ih r) hG cache
          hidden k hno hk hkN

/-! ## The birthday bound through the game after the PRF hop -/

section Walk

open FirstCounts (remaining)

variable {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (P : Query C → Prop) (cost : Tree → ℕ) (N : ℕ)

/-- From the state `s` of the game and a cache with no collision in `P` and at most `k` cells of `P`,
with `k`, the budget of the runs that remain and `L` at most `N`, the computation `m` gives a collision
in `P` with probability at most `birthdaySum k N`. -/
def SafeFrom {σ β : Type} (L : ℕ) (s : FirstState C σ) (m : FirstM C σ β) : Prop :=
  ∀ (cache : HashCache C) (hidden : HiddenCache C) k, ¬ DomainCollision P cache →
    SplitCacheBound (splitRegionCache P cache) k → k + remaining runLimit cost s.real.runs + L ≤ N →
    Pr{let z ← (m.run s).run (cache, hidden)}[DomainCollision P z.2.1] ≤ birthdaySum k N

/-- The computation `m` keeps the birthday sum from each state, with the room `L`. -/
def Safe {σ β : Type} (L : ℕ) (m : FirstM C σ β) : Prop := ∀ s, SafeFrom runLimit P cost N L s m

/-- From the state `s`, the computation `m` and then a continuation that keeps the birthday sum with
the room `L` keep it with the room `n + L`. So `m` adds at most `n` cells of `P` beyond the budget of
the runs that remain. -/
def BirthFrom {σ α : Type} (s : FirstState C σ) (n : ℕ) (m : FirstM C σ α) : Prop :=
  ∀ (β : Type) (F : α → FirstM C σ β) (L : ℕ), (∀ a, Safe runLimit P cost N L (F a)) →
    SafeFrom runLimit P cost N (n + L) s (m >>= F)

/-- `BirthFrom` from each state. -/
def Birth {σ α : Type} (n : ℕ) (m : FirstM C σ α) : Prop := ∀ s, BirthFrom runLimit P cost N s n m

/-- `Birth` of a computation of the signing phase from each state of the signing game. -/
def BirthT {σ α : Type} (n : ℕ) (m : StateT (TsigState C) (FirstM C σ) α) : Prop :=
  ∀ t, Birth runLimit P cost N n (m.run t)

variable {runLimit P cost N}

theorem safeFrom_mono {σ β : Type} {L L' : ℕ} {s : FirstState C σ} {m : FirstM C σ β}
    (h : SafeFrom runLimit P cost N L s m) (hL : L ≤ L') : SafeFrom runLimit P cost N L' s m :=
  fun cache hidden k hno hk hkN => h cache hidden k hno hk (by omega)

theorem birthFrom_mono {σ α : Type} {s : FirstState C σ} {n n' : ℕ} {m : FirstM C σ α}
    (h : BirthFrom runLimit P cost N s n m) (hn : n ≤ n') : BirthFrom runLimit P cost N s n' m :=
  fun β F L hF => safeFrom_mono (h β F L hF) (by omega)

theorem birth_mono {σ α : Type} {n n' : ℕ} {m : FirstM C σ α} (h : Birth runLimit P cost N n m) (hn : n ≤ n') :
    Birth runLimit P cost N n' m :=
  fun s => birthFrom_mono (h s) hn

theorem birth_pure {σ α : Type} (a : α) : Birth runLimit P cost N 0 (pure a : FirstM C σ α) := by
  intro s β F L hF
  rw [pure_bind, Nat.zero_add]
  exact hF a s

theorem birthFrom_bind {σ α β : Type} {s : FirstState C σ} {n l : ℕ} {m : FirstM C σ α}
    {f : α → FirstM C σ β} (hm : BirthFrom runLimit P cost N s n m) (hf : ∀ a, Birth runLimit P cost N l (f a)) :
    BirthFrom runLimit P cost N s (n + l) (m >>= f) := by
  intro γ F L hF
  rw [bind_assoc, Nat.add_assoc]
  exact hm γ (fun a => f a >>= F) (l + L) fun a s' => hf a s' γ F L hF

theorem birth_bind {σ α β : Type} {n l : ℕ} {m : FirstM C σ α} {f : α → FirstM C σ β}
    (hm : Birth runLimit P cost N n m) (hf : ∀ a, Birth runLimit P cost N l (f a)) :
    Birth runLimit P cost N (n + l) (m >>= f) :=
  fun s => birthFrom_bind (hm s) hf

theorem birth_get_bind {σ β : Type} {n : ℕ} {f : FirstState C σ → FirstM C σ β}
    (hf : ∀ s, BirthFrom runLimit P cost N s n (f s)) : Birth runLimit P cost N n (get >>= f) := by
  intro s γ F L hF cache hidden k hno hk hkN
  have h := hf s γ F L hF cache hidden k hno hk hkN
  simpa only [bind_assoc, StateT.run_bind, StateT.run_get, pure_bind] using h

theorem birth_get {σ : Type} : Birth runLimit P cost N 0 (get : FirstM C σ (FirstState C σ)) := by
  intro s β F L hF cache hidden k hno hk hkN
  have h := hF s s cache hidden k hno hk (by omega)
  simpa only [StateT.run_bind, StateT.run_get, pure_bind] using h

theorem birth_modify {σ : Type} (f : FirstState C σ → FirstState C σ) (hf : ∀ s, (f s).real.runs = s.real.runs) :
    Birth runLimit P cost N 0 (modify f : FirstM C σ Unit) := by
  intro s β F L hF cache hidden k hno hk hkN
  have h := hF () (f s) cache hidden k hno hk (by rw [hf]; omega)
  simpa only [StateT.run_bind, StateT.run_modify, pure_bind] using h

/-- A computation of the world with at most `n` calls that add a cell of `P` and no programming call
keeps the birthday sum with `n` more cells. -/
theorem inStream_birth (D : C.Coalition) {σ α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (hn : IsQueryBoundP oa (WorldRegionCounted P) n) (hp : IsQueryBoundP oa WorldProgramQuery 0) :
    Birth runLimit P cost N n (inStream (σ := σ) prims D oa) := by
  intro s β F L hF cache hidden k hno hk hkN
  simp only [inStream, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact world_birthday prims D P oa n hn hp (fun a => (F a).run s) N (remaining runLimit cost s.real.runs + L)
    (fun a cache hidden k hno hk hkN => hF a s cache hidden k hno hk (by omega)) cache hidden k hno hk
    (by omega)

/-- A computation of the state monad, followed by a continuation on its result and its final state. -/
theorem run_bind_mk {σ α γ : Type} (m : StateT σ ProbComp α) (w : σ) (H : α × σ → ProbComp (γ × σ)) :
    (m.run w >>= H) = (m >>= fun a => StateT.mk fun w' => H (a, w')).run w := by
  simp

/-- The world computation `block tree s` of each run of `tree` makes at most `cost tree` calls that add
a cell of `P` and no programming call. -/
def BlockBound {σ β : Type} (P : Query C → Prop) (cost : Tree → ℕ)
    (block : Tree → RealState C σ → OracleComp (WorldSpec C) β) (tree : Tree) : Prop :=
  ∀ s : RealState C σ,
    GameCount.Bound (WorldRegionCounted P) (block tree s) (cost tree) ∧
      GameCount.Bound WorldProgramQuery (block tree s) 0

omit [Field E] [Algebra Bit E] in
/-- A run of `tree` that the game allows takes its cells from the budget of the runs that remain. -/
theorem firstTreeRun_birthFrom (D : C.Coalition) {σ β : Type}
    (block : Tree → RealState C σ → OracleComp (WorldSpec C) β) (out : β → σ × (C.Party → Option TreeOutput))
    (event : StreamState C → β → StreamState C → Bool) (ready : RealState C σ → StreamState C → Prop) (tree : Tree)
    (hblock : BlockBound P cost block tree) (s : FirstState C σ) (hrun : s.real.runs tree < runLimit) :
    BirthFrom runLimit P cost N s 0 (firstTreeRunOf (blockRun prims D block out event) ready tree) := by
  intro γ F L hF cache hidden k hno hk hkN
  unfold firstTreeRunOf blockRun
  simp only [bind_assoc, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_set]
  rw [run_bind_mk]
  obtain ⟨h1, h2⟩ := hblock s.real
  have hrem := FirstCounts.remaining_update runLimit cost s.real.runs tree hrun
  refine world_birthday prims D P (block tree s.real) (cost tree)
    ((GameCount.bound_iff _ _ _).1 h1) ((GameCount.bound_iff _ _ _).1 h2) _ N
    (remaining runLimit cost (Function.update s.real.runs tree (s.real.runs tree + 1)) + L) ?_ cache hidden k
    hno hk (by omega)
  intro a c' h' k' hno' hk' hkN'
  rw [StateT.run_mk]
  dsimp only
  exact hF () _ c' h' k' hno' hk' (by dsimp only; omega)

omit [Field E] [Algebra Bit E] in
theorem firstTreeRuns_birth (D : C.Coalition) {σ β : Type}
    (block : Tree → RealState C σ → OracleComp (WorldSpec C) β) (out : β → σ × (C.Party → Option TreeOutput))
    (event : StreamState C → β → StreamState C → Bool) (ready : RealState C σ → StreamState C → Prop) (tree : Tree)
    (hblock : BlockBound P cost block tree) :
    ∀ count, Birth runLimit P cost N 0 (firstTreeRunsOf runLimit D (blockRun prims D block out event) ready tree count)
  | 0 => birth_pure _
  | count + 1 => by
    unfold firstTreeRunsOf
    refine birth_get_bind fun s => ?_
    split_ifs with hmay
    · exact birthFrom_bind (n := 0) (l := 0) (firstTreeRun_birthFrom prims D block out event ready tree
        hblock s (FirstCounts.mayRun_lt runLimit hmay)) fun _ => firstTreeRuns_birth D block out event ready tree hblock count
    · exact birth_pure () s

/-- A local call that adds a cell of `P` is in class `c` when each input of `P` is in class `c`. -/
theorem inClass_of_counted {c : HashClass} (hPc : ∀ q, P q → queryClass q = c) {u : (LocalSpec C).Domain}
    (h : SplitRegionCounted P u) : InClass c u := by
  obtain ⟨q, hq, hPq⟩ := h
  rcases u with n | r | x
  · simp [splitLocalHashInput] at hq
  · by_cases hr : IsFixed r
    · simp [splitLocalHashInput, hr] at hq
    · simp only [splitLocalHashInput, hr, ↓reduceIte, Option.some.injEq] at hq
      subst hq
      have hcls := hPc _ hPq
      rcases r with input | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      · exact ⟨fun hm => hr ⟨input, rfl, hm⟩, hcls.symm⟩
      all_goals exact hcls
  · simp only [splitLocalHashInput, Option.some.injEq] at hq
    subst hq
    exact (hPc _ hPq).symm

/-- A call of the world that adds a cell of `P` is a call of `Adds c`. -/
theorem adds_of_counted {c : HashClass} (hPc : ∀ q, P q → queryClass q = c) {t : (WorldSpec C).Domain}
    (h : WorldRegionCounted P t) : FirstCounts.Adds c t := by
  rcases t with (u | y) | u
  · exact inClass_of_counted hPc h
  · trivial
  · exact inClass_of_counted hPc h

/-- A programming call is a call of `Adds c`. -/
theorem adds_of_program {c : HashClass} {t : (WorldSpec C).Domain} (h : WorldProgramQuery t) :
    FirstCounts.Adds c t := by
  rcases t with (u | y) | u
  · exact h.elim
  · trivial
  · exact h.elim

/-- A computation of the world with no call of `Adds c` keeps the birthday sum with no more cell. -/
theorem inStream_birth_zero {c : HashClass} (hPc : ∀ q, P q → queryClass q = c) (D : C.Coalition) {σ α : Type}
    (oa : OracleComp (WorldSpec C) α) (h : IsQueryBoundP oa (FirstCounts.Adds c) 0) :
    Birth runLimit P cost N 0 (inStream (σ := σ) prims D oa) :=
  inStream_birth prims D oa 0 (h.of_imp fun _ ht => adds_of_counted hPc ht)
    (h.of_imp fun _ ht => adds_of_program ht)

omit [Field E] [Algebra Bit E] in
theorem firstTreeRequest_birth {c : HashClass} (hc : c ≠ .signing) (hPc : ∀ q, P q → queryClass q = c)
    (D : C.Coalition) {σ β : Type} (block : Tree → RealState C σ → OracleComp (WorldSpec C) β)
    (out : β → σ × (C.Party → Option TreeOutput)) (event : StreamState C → β → StreamState C → Bool)
    (ready : RealState C σ → StreamState C → Prop) (b : Fin (2 ^ layerHeight))
    (hblock : BlockBound P cost block (.bottom b)) :
    Birth runLimit P cost N 0 (firstTreeRequestOf prims runLimit D (blockRun prims D block out event) ready b) := by
  unfold firstTreeRequestOf
  refine birth_bind (n := 0) (l := 0) (firstTreeRuns_birth prims D block out event ready _ hblock 1)
    fun _ => birth_get_bind fun s => ?_
  split
  · exact birth_bind (n := 0) (l := 0) (inStream_birth_zero prims hPc D _
      (FirstCounts.free_noAdds hc (GameCount.onlySign_prfValue _ _))) (fun _ => birth_pure _) s
  · exact birth_pure _ s

theorem birthT_lift {σ α : Type} {n : ℕ} {m : FirstM C σ α} (hm : Birth runLimit P cost N n m) :
    BirthT runLimit P cost N n (StateT.lift m : StateT (TsigState C) (FirstM C σ) α) := fun t => by
  rw [StateT.run_lift, ← Nat.add_zero n]
  exact birth_bind hm fun _ => birth_pure _

theorem birthT_bind {σ α β : Type} {n l : ℕ} {m : StateT (TsigState C) (FirstM C σ) α}
    {f : α → StateT (TsigState C) (FirstM C σ) β} (hm : BirthT runLimit P cost N n m)
    (hf : ∀ a, BirthT runLimit P cost N l (f a)) : BirthT runLimit P cost N (n + l) (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact birth_bind (hm t) fun y => hf y.1 y.2

/-- A computation with at most `n` calls of `p` keeps the birthday sum with `n` more cells when each
call of `p` adds at most one cell and each other call none. -/
theorem birthT_simulateQ {σ : Type} {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT (TsigState C) (FirstM C σ))) (p : ι → Prop)
    (h : ∀ q, BirthT runLimit P cost N (if p q then 1 else 0) (impl q)) {α : Type} (oa : OracleComp spec α) :
    ∀ n, IsQueryBoundP oa p n → BirthT runLimit P cost N n (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ t
    rw [simulateQ_pure, StateT.run_pure]
    exact birth_mono (birth_pure _) (Nat.zero_le _)
  | query_bind q k ih =>
    intro n hn t
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    refine birth_mono (birth_bind (h q t) fun y => ih y.1 _ (hn.2 y.1) y.2) ?_
    split_ifs with hq
    · have := hn.1.resolve_left (not_not.2 hq)
      omega
    · omega

/-- The answer of an honest operator adds no cell of `P`. It is `tsigOracles` on the free copy under
the monad maps of `streamWorld` and `streamLift`. -/
theorem operatorAnswer_birth {c : HashClass} (hPc : ∀ q, P q → queryClass q = c)
    (hsign : FirstCounts.SignQuiet (C := C) c) {σ : Type} (D : C.Coalition)
    (operators : C.Party → OperatorState C) (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    BirthT runLimit P cost N 0
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
    change Birth runLimit P cost N 0 ((tsigOracles (fun oa => streamLift C σ (ψ (freeLift oa)))
      (SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt)) q).run t')
    rw [← hom₁, ← hom₂]
    exact inStream_birth_zero prims hPc D _ (hsign D operators keys top q t')
  · exact birth_pure _

theorem firstSignRequest_birth {c : HashClass} (hPc : ∀ q, P q → queryClass q = c)
    (hsign : FirstCounts.SignQuiet (C := C) c) {σ : Type} (D : C.Coalition) (i : C.Party) (e : KeyIndex)
    (q : TsigQuery C) : BirthT runLimit P cost N 0 (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine birthT_bind (n := 0) (l := 0) (birthT_lift (birth_modify _ fun _ => rfl)) fun _ =>
    birthT_bind (n := 0) (l := 0) (birthT_lift (birth_get_bind fun s => birth_pure s s)) fun s => ?_
  exact operatorAnswer_birth prims hPc hsign D _ _ _ _

omit [Field E] [Algebra Bit E] in
theorem firstSigning_birth {c : HashClass} (hc : c ≠ .signing) (hPc : ∀ q, P q → queryClass q = c)
    (D : C.Coalition) (A : DkgTsigAdversary C E) {β : Type}
    (block : Tree → RealState C A.net.State → OracleComp (WorldSpec C) β)
    (out : β → A.net.State × (C.Party → Option TreeOutput)) (event : StreamState C → β → StreamState C → Bool)
    (ready : RealState C A.net.State → StreamState C → Prop)
    (forge : ℕ) (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass c) forge)
    (hblock : ∀ tree, BlockBound P cost block tree)
    (hsign : FirstCounts.SignQuiet (C := C) c) :
    Birth runLimit P cost N forge (firstSigningOf prims runLimit D A (blockRun prims D block out event) ready) := by
  unfold firstSigningOf
  refine birth_get_bind fun s => ?_
  split
  · refine birthFrom_mono (birth_bind (l := 0) (birthT_simulateQ _ (ForgeInClass c) (fun q => ?_) _ forge
      (hforge _ _) _) (fun _ => birth_pure _) s) (by omega)
    rcases q with t | q | q
    · refine birthT_lift (inStream_birth prims D _ _ ?_ ?_)
      · rw [ThresholdLeanXmssSecurity.adversary_query]
        change IsQueryBoundP (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
          (WorldRegionCounted P) (if InClass c t then 1 else 0)
        rw [isQueryBoundP_query_iff]
        intro ht
        simp only [inClass_of_counted hPc ht, ↓reduceIte, Nat.one_pos]
      · rw [ThresholdLeanXmssSecurity.adversary_query, isQueryBoundP_query_iff]
        exact fun h => h.elim
    · simp only [ForgeInClass, ↓reduceIte]
      rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
      · exact fun t => birth_pure _
      · exact birthT_lift (firstTreeRequest_birth prims hc hPc D block out event ready b (hblock _))
      all_goals exact firstSignRequest_birth prims hPc hsign D i e _
    · simp only [ForgeInClass, ↓reduceIte]
      rcases q with _ | state
      · change BirthT runLimit P cost N 0 (StateT.lift ((fun x : FirstState C A.net.State => x.real.adversary) <$>
          (get : FirstM C A.net.State _)))
        rw [map_eq_bind_pure_comp]
        exact birthT_lift (birth_bind (n := 0) (l := 0) birth_get fun _ => birth_pure _)
      · change BirthT runLimit P cost N 0 (StateT.lift (modify fun s : FirstState C A.net.State =>
          { s with real := { s.real with adversary := state } }))
        exact birthT_lift (birth_modify _ fun _ => rfl)
  · exact birthFrom_mono (birth_pure () s) (Nat.zero_le _)

theorem safe_pure {σ β : Type} (L : ℕ) (b : β) : Safe runLimit P cost N L (pure b : FirstM C σ β) := by
  intro s cache hidden k hno _ _
  simp [hno]

end Walk

/-! ## The birthday bound of the game -/

section Game

variable {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Field E] [Algebra Bit E] in
/-- The birthday bound of the domain `P` at the end of `firstRunOf` for a block run. Each input of `P`
is in the class `c`, which is not `signing`. The seed generation makes at most `seed` calls that add a
cell of `P`, each run of `tree` at most `cost tree`, and `forge` at most `forge` calls in class `c`. No part makes a
programming call. Then a collision in `P` at the end has probability at most `birthdaySum 0 N`, with
`N` the sum of these counts over the game. -/
theorem firstRun_birthday {c : HashClass} (hc : c ≠ .signing) (P : Query C → Prop)
    (hPc : ∀ q, P q → queryClass q = c) (cost : Tree → ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) {β : Type}
    (block : Tree → RealState C A.net.State → OracleComp (WorldSpec C) β)
    (out : β → A.net.State × (C.Party → Option TreeOutput)) (event : StreamState C → β → StreamState C → Bool)
    (ready : RealState C A.net.State → StreamState C → Prop) (seed forge : ℕ)
    (hseed : IsQueryBoundP (realExecution D A.net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) (WorldRegionCounted P) seed)
    (hseedProgram : IsQueryBoundP (realExecution D A.net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) WorldProgramQuery 0)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass c) forge)
    (hblock : ∀ tree, BlockBound P cost block tree)
    (hsign : FirstCounts.SignQuiet (C := C) c) :
    Pr{let r ← firstRunOf prims runLimit D A (blockRun prims D block out event) ready}[DomainCollision P r.2.1] ≤
      birthdaySum 0 (seed + FirstCounts.remaining runLimit cost (fun _ => 0) + forge) := by
  unfold firstRunOf
  have hno : ¬ DomainCollision P (∅ : HashCache C) := by
    rintro ⟨_, _, _, _, _, h, _⟩
    simp [splitRegionCache] at h
  have hk : SplitCacheBound (splitRegionCache P (∅ : HashCache C)) 0 :=
    ⟨∅, le_rfl, fun q hq => by simp [splitRegionCache] at hq⟩
  refine world_birthday prims D P _ seed hseed hseedProgram _ _ (FirstCounts.remaining runLimit cost (fun _ => 0) + forge)
    ?_ ∅ ∅ 0 hno hk (by omega)
  rintro ⟨state, keys⟩ cache hidden k hno' hk' hkN
  have hB := birth_bind (N := seed + FirstCounts.remaining runLimit cost (fun _ => 0) + forge) (firstTreeRuns_birth prims D block out event ready .top (hblock .top) runLimit)
    (fun _ => firstSigning_birth prims hc hPc D A block out event ready forge hforge hblock hsign)
    ⟨startState D state keys, if (startState D state keys).flag then some (.seeds, (cache, hidden)) else none⟩
    Unit pure 0 (fun _ => safe_pure 0 ()) cache hidden k hno' hk' (by
      change k + FirstCounts.remaining runLimit cost (fun _ => 0) + (0 + forge + 0) ≤ _
      omega)
  rw [bind_pure] at hB
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp]
  rw [StateT.run_map, prEvent_map]
  exact hB

end Game

/-! ## The network makes no programming call -/

section Program

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_sequenceFin)

variable {E : Type}

theorem noProgram_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    NoCall WorldProgramQuery (worldRoles.adversary oa) := by
  rw [noCall_iff]
  suffices h : ∀ n, IsQueryBoundP (worldRoles.adversary oa) WorldProgramQuery n from h 0
  induction oa using OracleComp.inductionOn with
  | pure a => intro n; trivial
  | query_bind t k ih =>
    intro n
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, ThresholdLeanXmssSecurity.adversary_query]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

theorem noProgram_free {β : Type} (oa : OracleComp (LocalSpec C) β) : NoCall WorldProgramQuery (free oa) := by
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

theorem noProgram_stepRound {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    NoCall WorldProgramQuery (stepRound worldRoles D A noFunctionality state steps) := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  refine noCall_bind _ (noProgram_adversary _) fun p => ?_
  obtain ⟨state', sent⟩ := p
  refine noCall_bind _ (noCall_sequenceFin _ _ fun j => ?_) fun _ => noCall_pure _ _
  split
  · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact noProgram_free _
  · exact noCall_pure _ _

theorem noProgram_executeRounds {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      NoCall WorldProgramQuery (executeRounds worldRoles D A noFunctionality fuel state steps)
  | 0, state, steps => noCall_pure _ _
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · exact noCall_pure _ _
    · refine noCall_bind _ (noProgram_stepRound D A state steps) fun p => ?_
      obtain ⟨state', steps', _⟩ := p
      exact noProgram_executeRounds D A fuel state' steps'

theorem noProgram_executePhase {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ)
    (state : A.State) (program : C.Party → PartyM C E RealSpec α) :
    NoCall WorldProgramQuery (executePhase worldRoles D A noFunctionality fuel state program) := by
  unfold executePhase startSteps
  refine noCall_bind _ (noCall_sequenceFin _ _ fun i => ?_) fun steps => noProgram_executeRounds D A fuel state steps
  split_ifs
  · exact noCall_pure _ _
  · exact noProgram_free _

theorem noProgram_realExecution {I O : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → I → PartyM C E RealSpec O) (x : C.Party → I) (z : Aux) :
    NoCall WorldProgramQuery (realExecution D A noFunctionality fuel program x z) := by
  unfold realExecution
  exact noCall_bind _ (noProgram_adversary _) fun state => noProgram_executePhase D A fuel state _

end Program

/-! ## The collision hop from the honest budgets -/

section Hop

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- An honest call that adds a cell of `P`, namely a call on the free copy. -/
def HonestRegion (P : Query C → Prop) : (WorldSpec C).Domain → Prop
  | .inr u => SplitRegionCounted P u
  | _ => False

/-- The honest calls of the seed generation on the network add at most `seed` cells of `P`, and the
honest calls of each run of `tree` at most `honestRun tree`. -/
def HonestBudget (P : Query C → Prop) (seed : ℕ) (honestRun : Tree → ℕ) : Prop :=
  (∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty),
    GameCount.Bound (HonestRegion P) (realExecution D net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) seed) ∧
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State),
    GameCount.Bound (HonestRegion P) (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
      s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree) (honestRun tree)

omit [Fintype E] [DecidableEq E] in
/-- A class budget gives the budget of a domain of the class. -/
theorem honestBudget_of_class {c : HashClass} {P : Query C → Prop} (hPc : ∀ q, P q → queryClass q = c)
    (seed : ℕ) (honestRun : Tree → ℕ) (hseed : FirstCounts.SeedHonest (C := C) (E := E) c seed)
    (htree : FirstCounts.TreeHonest K circuits settings c honestRun) :
    HonestBudget K circuits settings P seed honestRun := by
  have himp : ∀ t : (WorldSpec C).Domain, HonestRegion P t → HonestIn c t := fun t ht => by
    rcases t with _ | u
    · exact ht.elim
    · exact inClass_of_counted hPc ht
  refine ⟨fun D net => ?_, fun D net tree s => ?_⟩
  · have := hseed D net
    rw [GameCount.bound_iff] at this ⊢
    exact this.of_imp himp
  · have := htree D net tree s
    rw [GameCount.bound_iff] at this ⊢
    exact this.of_imp himp

/-- A call that adds a cell of `P` is an own call of class `c` or an honest call that adds a cell. -/
theorem counted_or {c : HashClass} {P : Query C → Prop} (hPc : ∀ q, P q → queryClass q = c)
    {t : (WorldSpec C).Domain} (h : WorldRegionCounted P t) : FirstCounts.OwnAdds c t ∨ HonestRegion P t := by
  rcases t with (u | y) | u
  · exact Or.inl (inClass_of_counted hPc h)
  · exact h.elim
  · exact Or.inr h

/-- The birthday sum grows with its last cell. -/
theorem birthdaySum_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) : birthdaySum k N ≤ birthdaySum k M :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-- The block `block` keeps the honest budgets of the domain `P`. For each honest budget of the plain
runs and each bound `step` on the calls of class `c` of a round of the network, each run of the block
makes at most `treeFuel * step` calls of the network and the honest calls of the budget that add a cell
of `P`, and no programming call. -/
def KeepsBudget (c : HashClass) (P : Query C → Prop) (net : Adversary C E Unit PEmpty PEmpty) {β : Type}
    (block : Tree → RealState C net.State → OracleComp (WorldSpec C) β) : Prop :=
  ∀ seed honestRun, HonestBudget K circuits settings P seed honestRun → ∀ step,
    (∀ state sent, IsQueryBoundP (net.round state sent) (InClass c) step) → ∀ tree,
      BlockBound P (fun tree => treeFuel circuits settings * step + honestRun tree) block tree

omit [Fintype E] [DecidableEq E] in
/-- The block of `streamTreeRun` keeps the honest budgets of each domain of a class that is not
`signing`. The monitor `wrongOutput` adds no cell of the domain and makes no programming call. -/
theorem treeBlock_keepsBudget {c : HashClass} (hc : c ≠ .signing) {P : Query C → Prop}
    (hPc : ∀ q, P q → queryClass q = c) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    KeepsBudget K circuits settings c P net (FirstCounts.treeBlock K circuits settings D net) := by
  intro seed honestRun hbudget step hround tree s
  unfold FirstCounts.treeBlock
  refine ⟨GameCount.bound_mono (GameCount.bound_bind (m := 0) ((GameCount.bound_iff _ _ _).2
    (FirstCounts.isQueryBoundP_add (fun _ => counted_or hPc) _ _ _
      (FirstCounts.ownAdds_executePhase c D net step hround _ _ _)
      ((GameCount.bound_iff _ _ _).1 (hbudget.2 D net tree s)))) fun r => ?_) (Nat.add_zero _).le,
    GameCount.bound_bind (n := 0) (m := 0) (FirstCounts.bound_of_noCall
      (noProgram_executePhase D net _ _ _)) fun r => ?_⟩
  · exact GameCount.bound_mono (GameCount.bound_bind (n := 0) (m := 0) (FirstCounts.bound_of_noCall
      (GameCount.wrongOutput_noCall D (WorldRegionCounted P)
        (fun _ ht hw => FirstCounts.monitorCall_not_adds hc ht (adds_of_counted hPc hw)) _ _ _))
      fun _ => GameCount.bound_pure _ _) le_rfl
  · refine GameCount.bound_bind (n := 0) (m := 0) (FirstCounts.bound_of_noCall
      (GameCount.wrongOutput_noCall D WorldProgramQuery (fun t ht hp => ?_) _ _ _)) fun _ => GameCount.bound_pure _ _
    rcases t with (u | y) | u
    · exact ht.elim
    · exact ht.elim
    · exact hp.elim

omit [Fintype E] [DecidableEq E] in
/-- The collision hop of the domain `P` for each block run that keeps the honest budgets of `P`. Each
input of `P` is in the class `c`, which is not `signing`. At the world of the first bad record, two
cells of `P` collide with probability at most `(q + H)² / 2^257`, with `H` the honest cells of the seed
generation and of `runLimit` runs of each tree. -/
theorem firstCollisionOf_le {c : HashClass} (hc : c ≠ .signing) (P : Query C → Prop)
    (hPc : ∀ q, P q → queryClass q = c) (seed : ℕ) (honestRun : Tree → ℕ)
    (hbudget : HonestBudget K circuits settings P seed honestRun) (hsign : FirstCounts.SignQuiet (C := C) c)
    (prims : Primitives) (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (ready : RealState C A.net.State → StreamState C → Prop) (hA : DkgTsigBounded circuits settings runLimit A q)
    {β : Type} (block : Tree → RealState C A.net.State → OracleComp (WorldSpec C) β)
    (out : β → A.net.State × (C.Party → Option TreeOutput)) (event : StreamState C → β → StreamState C → Bool)
    (hblock : KeepsBudget K circuits settings c P A.net block) :
    (Pr{let r ← firstRunOf prims runLimit D A (blockRun prims D block out event) ready}[
        ∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision P world.1]).toReal ≤
      (((q + (seed + runLimit * (honestRun .top + ∑ b : Fin (2 ^ layerHeight), honestRun (.bottom b)))) ^ 2 : ℕ) : ℝ) /
        2 ^ 257 := by
  obtain ⟨start, step, forge, hsum, hs, hround, hf⟩ := dkgTsigBounded_classBounded circuits settings runLimit hA c
  let cost : Tree → ℕ := fun tree => treeFuel circuits settings * step + honestRun tree
  have hseedW : IsQueryBoundP (realExecution D A.net noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []) (WorldRegionCounted P)
      (start + setupRounds * step + seed) :=
    FirstCounts.isQueryBoundP_add (fun _ => counted_or hPc) _ _ _
      (FirstCounts.ownAdds_realExecution c D A.net start step hs hround _ _ _ _)
      ((GameCount.bound_iff _ _ _).1 (hbudget.1 D A.net))
  have hseedP := (noCall_iff _ _).1 (noProgram_realExecution (E := E) D A.net setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])
  have hbirth := firstRun_birthday prims runLimit hc P hPc cost D A block out event ready
    (start + setupRounds * step + seed) forge hseedW hseedP hf (hblock seed honestRun hbudget step hround) hsign
  have e : FirstCounts.remaining runLimit cost (fun _ => 0) =
      runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step +
        runLimit * (honestRun .top + ∑ b : Fin (2 ^ layerHeight), honestRun (.bottom b)) := by
    simp only [cost, FirstCounts.remaining, Nat.sub_zero, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have e' : dkgTsigRounds circuits settings runLimit * step =
      setupRounds * step + runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step := by
    unfold dkgTsigRounds
    ring
  set M := q + (seed + runLimit * (honestRun .top + ∑ b : Fin (2 ^ layerHeight), honestRun (.bottom b)))
  have hNM : start + setupRounds * step + seed + FirstCounts.remaining runLimit cost (fun _ => 0) + forge ≤ M := by
    have hq : start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q := hsum
    rw [e]
    omega
  have hfin : birthdaySum 0 M ≠ ⊤ := by
    unfold birthdaySum
    exact ENNReal.sum_ne_top.2 fun _ _ => by finiteness
  refine (prReal_mono _ _ (fun r => DomainCollision P r.2.1) fun r hr ⟨stage, world, hfirst, hcoll⟩ =>
    SetupAgree.domainCollision_mono (RecordedCache.recordedBelowOf prims runLimit D A _
      (RecordedCache.blockRun_grows prims D block out event) ready r hr stage world hfirst).1 hcoll).trans ?_
  exact (ENNReal.toReal_mono hfin (hbirth.trans (birthdaySum_mono 0 hNM))).trans (birthdaySum_zero_le M)


end Hop

end Collision

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Collision.firstCollisionOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Collision.firstCollisionOf_le
