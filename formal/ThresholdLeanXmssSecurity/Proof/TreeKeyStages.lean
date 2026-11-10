import ThresholdLeanXmssSecurity.Proof.TreeKey
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The stages of the stream-key bound

Stage 2 of `TreeKey.lean`, `TreeKeysApartBound`, is proved (`treeKeysApartBound`). Keys that are not
apart come from one of three events.

1. A hidden canonical derivation input is cached at the boundary (`EarlyCached`). This is
   `prob_prssEarlyCachedInput_le`, moved from the logged table to the world (`prob_earlyCached_le`).
2. Two sampled parts collide (`PartsCollide`). Then a derivation input of a row can equal the canonical
   input of another name (`prob_setupEarly_partsCollide_le`).
3. The fresh answer at a hidden input equals the answer at another row input (`rows_collision`,
   `prob_collision_finset_le`).

Events 2 and 3 fit in `streamKeyError` for at most `2 ^ 60` operators, and `streamKeyError` is at least
one for more operators.

Stage 3, `TreeKeyHitBound`, stays a hypothesis of `treeStreamKeyAfterDerivationFull` and
`treeSecurityOfSimFull`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

open scoped ENNReal

section Potential

variable {κ σ β : Type} {spec : OracleSpec κ}

/-- A potential `g` that bounds the indicator of `P` and does not grow in expectation over one call
bounds the probability that the run of a computation ends in `P`. -/
theorem probEvent_run_le_potential (impl : QueryImpl spec (StateT σ ProbComp)) (P : σ → Prop)
    (g : σ → ℝ≥0∞) (hP : ∀ s, P s → 1 ≤ g s)
    (hstep : ∀ t s, ∑' x, Pr[= x | (impl t).run s] * g x.2 ≤ g s) (oa : OracleComp spec β) :
    ∀ s, Pr[fun r => P r.2 | (simulateQ impl oa).run s] ≤ g s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
    split_ifs with h
    · exact hP s h
    · exact zero_le
  | query_bind t k ih =>
    intro s
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probEvent_bind_eq_tsum]
    exact le_trans (ENNReal.tsum_le_tsum fun x => by gcongr; exact ih x.1 x.2) (hstep t s)

end Potential

section Collision

variable {C : Committee}

/-- The potential of a collision of the answers at `x` and `y`. -/
def collisionPotential (x y : Query C) (s : HashCache C) : ℝ≥0∞ :=
  match s x, s y with
  | some u, some v => if u = v then 1 else 0
  | _, _ => (2 ^ 256)⁻¹

theorem collisionPotential_congr {x y : Query C} {s s' : HashCache C} (hx : s' x = s x) (hy : s' y = s y) :
    collisionPotential x y s' = collisionPotential x y s := by
  unfold collisionPotential
  rw [hx, hy]

theorem tsum_probOutput_mul_le_of_eq {α : Type} (mx : ProbComp α) (F : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ z ∈ support mx, F z = c) : ∑' z, Pr[= z | mx] * F z ≤ c :=
  le_of_eq (tsum_probOutput_mul_of_const_on_support mx h (by simp))

theorem collisionPotential_fresh (prims : Primitives) {x y : Query C}
    (hx : ∃ ph k v, x = .derive ph k v) (hxy : x ≠ y) (s : HashCache C) :
    ∑' r, Pr[= r | (localAnswer prims (.inr (.inl x))).run s] * collisionPotential x y r.2 ≤
      collisionPotential x y s := by
  obtain ⟨ph, k, v, rfl⟩ := hx
  change ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle (.derive ph k v)).run s] *
    collisionPotential _ y r.2 ≤ _
  cases hs : s (.derive ph k v) with
  | some u =>
    rw [randomOracle, QueryImpl.withCaching_run_some _ hs]
    simp
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ hs, tsum_probOutput_map_mul]
    simp only [collisionPotential, QueryCache.cacheQuery_self,
      QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy), hs]
    cases hy : s y with
    | none => exact tsum_probOutput_mul_le_of_eq _ _ _ fun _ _ => rfl
    | some w =>
      simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]
      simp [uniformSampleImpl, HashOutput, hashOutputBits]
      norm_num

theorem collisionPotential_comm (x y : Query C) (s : HashCache C) :
    collisionPotential x y s = collisionPotential y x s := by
  unfold collisionPotential
  cases s x <;> cases s y <;> simp [eq_comm]

/-- A call to `localAnswer` does not raise the collision potential of two distinct derivation inputs. -/
theorem collisionPotential_step (prims : Primitives) {x y : Query C}
    (hx : ∃ ph k v, x = .derive ph k v) (hy : ∃ ph k v, y = .derive ph k v) (hxy : x ≠ y)
    (t : (LocalSpec C).Domain) (s : HashCache C) :
    ∑' r, Pr[= r | (localAnswer prims t).run s] * collisionPotential x y r.2 ≤
      collisionPotential x y s := by
  by_cases htx : t = .inr (.inl x)
  · subst htx
    exact collisionPotential_fresh prims hx hxy s
  by_cases hty : t = .inr (.inl y)
  · subst hty
    simp only [collisionPotential_comm x y]
    exact collisionPotential_fresh prims hy (Ne.symm hxy) s
  have hout : ∀ z, (∃ ph k v, z = Query.derive ph k v) → t ≠ .inr (.inl z) →
      z ∉ prssCountedHashInputs t := by
    rintro z ⟨ph, k, v, rfl⟩ hz
    rcases t with n | q | w
    · simp [prssCountedHashInputs]
    · simp only [prssCountedHashInputs]
      split_ifs
      · simp only [List.mem_singleton]
        rintro rfl
        exact hz rfl
      · simp
    · simp [prssCountedHashInputs]
  exact tsum_probOutput_mul_le_of_eq _ _ _ fun r hr => collisionPotential_congr
    (prssLocalAnswer_other prims t x (hout x hx htx) s r hr)
    (prssLocalAnswer_other prims t y (hout y hy hty) s r hr)

/-- The answer at a fresh derivation input equals the answer at another derivation input with
probability at most `1 / 2 ^ 256`. -/
theorem prob_collision_le (prims : Primitives) {β : Type} (oa : OracleComp (LocalSpec C) β)
    {x y : Query C} (hx : ∃ ph k v, x = .derive ph k v) (hy : ∃ ph k v, y = .derive ph k v)
    (hxy : x ≠ y) (s : HashCache C) (hs : s x = none) :
    Pr[fun r => r.2 x ≠ none ∧ r.2 x = r.2 y | (simulateQ (localAnswer prims) oa).run s] ≤
      (2 ^ 256)⁻¹ := by
  have h := probEvent_run_le_potential (localAnswer prims) (fun s' => s' x ≠ none ∧ s' x = s' y)
    (collisionPotential x y) (fun s' hs' => ?_) (collisionPotential_step prims hx hy hxy) oa s
  · refine h.trans (le_of_eq ?_)
    simp [collisionPotential, hs]
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hs'.1
    have hv := hs'.2
    rw [hu] at hv
    simp [collisionPotential, hu, ← hv]

/-- Some fresh derivation input of `X` has the answer of another derivation input of `Y` with
probability at most `|X| |Y| / 2 ^ 256`. -/
theorem prob_collision_finset_le (prims : Primitives) {β : Type} (oa : OracleComp (LocalSpec C) β)
    (X Y : Finset (Query C)) (hX : ∀ x ∈ X, ∃ ph k v, x = .derive ph k v)
    (hY : ∀ y ∈ Y, ∃ ph k v, y = .derive ph k v) (s : HashCache C) (hs : ∀ x ∈ X, s x = none) :
    Pr[fun r => ∃ x ∈ X, ∃ y ∈ Y, x ≠ y ∧ r.2 x ≠ none ∧ r.2 x = r.2 y |
      (simulateQ (localAnswer prims) oa).run s] ≤ (X.card * Y.card : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_exists_finset_le_sum _ _ _).trans ?_
  have hx : ∀ x ∈ X, Pr[fun r => ∃ y ∈ Y, x ≠ y ∧ r.2 x ≠ none ∧ r.2 x = r.2 y |
      (simulateQ (localAnswer prims) oa).run s] ≤ Y.card * (2 ^ 256)⁻¹ := by
    intro x hxX
    refine (probEvent_exists_finset_le_sum _ _ _).trans ?_
    calc _ ≤ ∑ y ∈ Y, ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
          refine Finset.sum_le_sum fun y hyY => ?_
          by_cases hxy : x = y
          · simp [hxy]
          · simpa [hxy] using prob_collision_le prims oa (hX x hxX) (hY y hyY) hxy s (hs x hxX)
      _ = _ := by simp
  calc _ ≤ ∑ x ∈ X, (Y.card : ℝ≥0∞) * (2 ^ 256)⁻¹ := Finset.sum_le_sum hx
    _ = _ := by simp [div_eq_mul_inv, mul_assoc]

end Collision

section Bridge

variable {C : Committee} {E : Type}

/-- The joint data and the adversarial state at the boundary before honest derivation. -/
def setupEarly (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) :
    OracleComp (LocalSpec C)
      ((C.Party → Parts C × List HashOutput) × A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) := do
  let state ← start
  let data ← prssInitialData D
  let r ← prssEarlyDataRounds D A state data
  pure (data, r)

/-- The derivations of the reveal round from the boundary. -/
def setupReveal (D : C.Coalition) {σ : Type} :
    (C.Party → Parts C × List HashOutput) × σ × (C.Party → Mail C E) × Option (C.Party → Mail C E) →
      OracleComp (LocalSpec C) (σ × Option (RevealRows C))
  | (_, state', _, none) => pure (state', none)
  | (data, state', sent, some sent') => do
    let rows ← prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
      (prssCommitInbox D data sent) sent'
    pure (state', some rows)

theorem worldRun_setupPrefix (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    worldRun prims (setupPrefix D A x z) =
      (simulateQ (localAnswer prims) (setupEarly D A (A.start (corruptInputs D x) z) >>=
        setupReveal D)).run ∅ := by
  unfold worldRun setupPrefix setupEarly
  simp only [simulateQ_bind, bind_assoc, pure_bind, simulateQ_world_adversary]
  rw [show simulateQ (worldAnswer prims) (free (prssInitialData D)) =
    simulateQ (localAnswer prims) (prssInitialData D) from simulateQ_free _ _ _]
  congr 1
  refine bind_congr fun state => bind_congr fun data => bind_congr fun r => ?_
  rcases r with ⟨state', sent, _ | sent'⟩
  · simp [setupReveal]
  · simp only [setupReveal, simulateQ_bind, simulateQ_pure]
    rw [show simulateQ (worldAnswer prims) (free (prssRevealRows D (prssCommitActive D sent)
      (fun i => (data i).1) (prssCommitInbox D data sent) sent')) = _ from simulateQ_free _ _ _]

theorem prssEarlyDataRounds_logged (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : (prssLoggedAdversary A).State) (data : C.Party → Parts C × List HashOutput) :
    (fun r => (r.1.1, r.2)) <$> prssEarlyDataRounds D (prssLoggedAdversary A) state data =
      prssEarlyDataRounds D A state.1 data := by
  unfold prssEarlyDataRounds
  simp only [prssLoggedAdversary, map_bind, bind_assoc, pure_bind]
  conv_rhs => rw [← prssHashLog_fst (A.round state.1 _), bind_map_left]
  refine bind_congr fun r => ?_
  split_ifs
  · simp
  · simp only [map_bind, map_pure]
    conv_rhs => rw [← prssHashLog_fst (A.round _ _), bind_map_left]

/-- The cache at the boundary holds a hidden canonical derivation input. -/
def EarlyCached (D : C.Coalition) {σ : Type}
    (r : ((C.Party → Parts C × List HashOutput) × σ) × HashCache C) : Prop :=
  (∃ T : C.Term, Hidden D (.term T) ∧ r.2 (prssTermInput (fun i => (r.1.1 i).1) T) ≠ none) ∨
    (∃ p : C.Pair, Hidden D (.pair p) ∧ r.2 (prssPairInput (fun i => (r.1.1 i).1) p) ≠ none)

theorem setupEarly_logged (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) :
    (fun r => ((fun i => (r.1 i).1), r.2.1.1, r.2.2)) <$>
        setupEarly D (prssLoggedAdversary A) (prssHashLog start) =
      (fun r => ((fun i => (r.1 i).1), r.2)) <$> setupEarly D A start := by
  unfold setupEarly
  simp only [map_bind, map_pure]
  conv_rhs => rw [← prssHashLog_fst start, bind_map_left]
  refine bind_congr fun state => bind_congr fun data => ?_
  rw [← prssEarlyDataRounds_logged D A state data, bind_map_left]

/-- The prequery bound at the boundary, with the actual budget. -/
theorem prob_earlyCached_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) :
    Pr[EarlyCached D | (simulateQ (localAnswer prims) (setupEarly D A start)).run ∅] ≤
      (q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 := by
  have h := prob_prssEarlyCachedInput_le prims D A start initial step q hstart hstep hq
  have ht : prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start) =
      (fun r => ((fun i => (r.1 i).1), r.2)) <$> setupEarly D (prssLoggedAdversary A) (prssHashLog start) := by
    simp [prssEarlyTable, setupEarly, map_bind]
  have hu := congrArg (fun oa => (simulateQ (localAnswer prims) oa).run (∅ : HashCache C))
    (setupEarly_logged D A start)
  simp only [simulateQ_map, StateT.run_map] at hu
  rw [ht, simulateQ_map, StateT.run_map, probEvent_map] at h
  let Q : ((C.Party → Parts C) × A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) ×
      HashCache C → Prop := fun r =>
    (∃ T : C.Term, Hidden D (.term T) ∧ r.2 (prssTermInput r.1.1 T) ≠ none) ∨
      (∃ p : C.Pair, Hidden D (.pair p) ∧ r.2 (prssPairInput r.1.1 p) ≠ none)
  calc _ = Pr[Q | (fun p => ((fun i => (p.1.1 i).1, p.1.2), p.2)) <$>
        (simulateQ (localAnswer prims) (setupEarly D A start)).run ∅] := by
        rw [probEvent_map]
        rfl
    _ = _ := by rw [← hu, probEvent_map]; rfl
    _ ≤ _ := h

end Bridge

section Marginal

/-- A projection of a stateful sequence whose steps have state-free marginals has the marginal of the
sequence of the marginals. -/
theorem evalDist_map_sequenceFin_run {σ α β : Type} (φ : α → β) :
    ∀ {n : ℕ} (f : Fin n → StateT σ ProbComp α) (g : Fin n → ProbComp β),
      (∀ i s, 𝒟[(fun r => φ r.1) <$> (f i).run s] = 𝒟[g i]) → ∀ s,
        𝒟[(fun r => fun i => φ (r.1 i)) <$> (Concrete.sequenceFin f).run s] = 𝒟[Concrete.sequenceFin g]
  | 0, f, g, _, s => by
    simp only [Concrete.sequenceFin, StateT.run_pure, map_pure]
    congr 2
    funext i
    exact i.elim0
  | n + 1, f, g, h, s => by
    have ih := evalDist_map_sequenceFin_run φ (fun i : Fin n => f i.succ) (fun i => g i.succ)
      (fun i s => h i.succ s)
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    have e1 : ∀ a : α × σ, ((Concrete.sequenceFin fun index : Fin n => f index.succ).run a.2 >>= fun a_1 =>
        pure fun i => φ (Fin.cases (motive := fun _ => α) a.1 a_1.1 i)) =
          (fun (t : Fin n → β) (i : Fin (n + 1)) => Fin.cases (motive := fun _ => β) (φ a.1) t i) <$>
          ((fun r => fun i => φ (r.1 i)) <$> (Concrete.sequenceFin fun index : Fin n => f index.succ).run a.2) := by
      intro a
      rw [Functor.map_map, map_eq_bind_pure_comp]
      refine bind_congr fun b => ?_
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    have e2 : (g 0 >>= fun head => Concrete.sequenceFin (fun index : Fin n => g index.succ) >>= fun tail =>
        pure fun i => Fin.cases (motive := fun _ => β) head tail i) = g 0 >>= fun head =>
          (fun (t : Fin n → β) (i : Fin (n + 1)) => Fin.cases (motive := fun _ => β) head t i) <$> Concrete.sequenceFin (fun index : Fin n => g index.succ) := by
      refine bind_congr fun b => ?_
      rw [map_eq_bind_pure_comp]
      rfl
    simp only [e1, e2]
    rw [evalDist_bind, evalDist_bind]
    simp only [evalDist_map, ih]
    rw [← h 0 s, evalDist_map, bind_map_left]

theorem evalDist_prssInitialData_parts {C : Committee} (prims : Primitives) (D : C.Coalition)
    (s : HashCache C) :
    𝒟[(fun r => fun i => (r.1 i).1) <$> (simulateQ (localAnswer prims) (prssInitialData D)).run s] =
      𝒟[prssSampleParts D] := by
  rw [prssInitialData, simulateQ_sequenceFin, prssSampleParts]
  refine evalDist_map_sequenceFin_run Prod.fst _ _ (fun i s => ?_) s
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, if_false, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      simulateQ_local_sample, bind_map_left, map_bind, map_pure]
    conv_rhs => rw [← bind_pure (sampleParts : ProbComp (Parts C))]
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext a
    apply evalDist_ext
    intro y
    simp

/-- A sampled part equals a value that does not read it with probability at most `1 / 2 ^ 256`. -/
theorem prob_sampleParts_term_eq_le {C : Committee} (T' : C.Term) (W : Parts C → HashOutput)
    (hW : ∀ parts u, W {parts with term := Function.update parts.term T' u} = W parts) :
    Pr[fun parts => parts.term T' = W parts | (sampleParts : ProbComp (Parts C))] ≤ 1 / 2 ^ 256 := by
  have h := prob_sampleParts_hiddenTerm_guess_le T' W hW (fun w => pure {w}) 1 (by simp)
  simp only [pure_bind, Nat.cast_one] at h
  rw [← probEvent_eq_eq_probOutput] at h
  refine le_trans (le_of_eq ?_) h
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  simp

theorem prob_sampleParts_pair_eq_le {C : Committee} (j : C.Party) (W : Parts C → HashOutput)
    (hW : ∀ parts u, W {parts with pair := Function.update parts.pair j u} = W parts) :
    Pr[fun parts => parts.pair j = W parts | (sampleParts : ProbComp (Parts C))] ≤ 1 / 2 ^ 256 := by
  have h := prob_sampleParts_hiddenPair_guess_le j W hW (fun w => pure {w}) 1 (by simp)
  simp only [pure_bind, Nat.cast_one] at h
  rw [← probEvent_eq_eq_probOutput] at h
  refine le_trans (le_of_eq ?_) h
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  simp

/-- Splitting the sampled parts of operator `i` out of the sampled parts of all operators. -/
theorem prob_prssSampleParts_split {C : Committee} (D : C.Coalition) (i : C.Party) (hi : i ∉ D.1)
    (P : (C.Party → Parts C) → Prop) (ε : ℝ≥0∞)
    (h : ∀ xs : C.Party → Parts C, Pr[fun a => P (Function.update xs i a) | (sampleParts : ProbComp (Parts C))] ≤ ε) :
    Pr[P | prssSampleParts D] ≤ ε := by
  unfold prssSampleParts
  rw [← bind_pure (Concrete.sequenceFin _), probEvent_def,
    evalDist_sequenceFin_split _ i (⟨0, fun _ => 0, fun _ => 0⟩ : Parts C), ← probEvent_def]
  apply probEvent_bind_le_of_forall_le
  intro xs _
  simp only [if_neg hi]
  rw [probEvent_bind_eq_tsum]
  refine le_trans (le_of_eq ?_) (h xs)
  rw [probEvent_eq_tsum_ite]
  simp

/-- Two distinct coordinates of the parts of the terms collide with probability at most `1 / 2 ^ 256`,
when the first one is sampled by an honest operator. -/
theorem prob_prssSampleParts_term_eq_le {C : Committee} (D : C.Coalition) (i g : C.Party) (hi : i ∉ D.1)
    (T' T : C.Term) (hne : (i, T') ≠ (g, T)) :
    Pr[fun parts => (parts i).term T' = (parts g).term T | prssSampleParts D] ≤ 1 / 2 ^ 256 := by
  refine prob_prssSampleParts_split D i hi _ _ fun xs => ?_
  simp only [Function.update_self]
  by_cases hg : g = i
  · subst hg
    have hT : T ≠ T' := fun h => hne (by rw [h])
    simp only [Function.update_self]
    exact prob_sampleParts_term_eq_le T' (fun a => a.term T) fun a u => by
      simp [Function.update_of_ne hT]
  · simp only [Function.update_of_ne hg]
    exact prob_sampleParts_term_eq_le T' (fun _ => (xs g).term T) fun _ _ => rfl

theorem prob_prssSampleParts_pair_eq_le {C : Committee} (D : C.Coalition) (i j a b : C.Party) (hi : i ∉ D.1)
    (hne : (i, j) ≠ (a, b)) :
    Pr[fun parts => (parts i).pair j = (parts a).pair b | prssSampleParts D] ≤ 1 / 2 ^ 256 := by
  refine prob_prssSampleParts_split D i hi _ _ fun xs => ?_
  simp only [Function.update_self]
  by_cases ha : a = i
  · subst ha
    have hb : b ≠ j := fun h => hne (by rw [h])
    simp only [Function.update_self]
    exact prob_sampleParts_pair_eq_le j (fun c => c.pair b) fun c u => by
      simp [Function.update_of_ne hb]
  · simp only [Function.update_of_ne ha]
    exact prob_sampleParts_pair_eq_le j (fun _ => (xs a).pair b) fun _ _ => rfl

/-- Two coordinates of the sampled parts collide, the first one of an honest operator. -/
def PartsCollide {C : Committee} (D : C.Coalition) (parts : C.Party → Parts C) : Prop :=
  (∃ x : C.Party × C.Party × C.Term × C.Term, x.1 ∉ D.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
      (parts x.1).term x.2.2.1 = (parts x.2.1).term x.2.2.2) ∨
    (∃ x : C.Party × C.Party × C.Party × C.Party, x.1 ∉ D.1 ∧ (x.1, x.2.1) ≠ (x.2.2.1, x.2.2.2) ∧
      (parts x.1).pair x.2.1 = (parts x.2.2.1).pair x.2.2.2)

theorem prob_partsCollide_le {C : Committee} (D : C.Coalition) :
    Pr[PartsCollide D | prssSampleParts D] ≤
      ((Fintype.card (C.Party × C.Party × C.Term × C.Term) +
        Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_or_le _ _ _).trans ?_
  have h1 : Pr[fun parts => ∃ x : C.Party × C.Party × C.Term × C.Term, x.1 ∉ D.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
      (parts x.1).term x.2.2.1 = (parts x.2.1).term x.2.2.2 | prssSampleParts D] ≤
      (Fintype.card (C.Party × C.Party × C.Term × C.Term) : ℝ≥0∞) * (1 / 2 ^ 256) := by
    have he := probEvent_exists_finset_le_sum (Finset.univ : Finset (C.Party × C.Party × C.Term × C.Term))
      (prssSampleParts D) fun x parts => x.1 ∉ D.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
        (parts x.1).term x.2.2.1 = (parts x.2.1).term x.2.2.2
    simp only [Finset.mem_univ, true_and] at he
    refine he.trans ?_
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x.1 ∉ D.1 ∧ x.2.2.1 ≠ x.2.2.2
    · refine le_trans (probEvent_mono fun _ _ h => h.2.2) ?_
      exact prob_prssSampleParts_term_eq_le D _ _ hx.1 _ _ fun h => hx.2 (Prod.ext_iff.mp h).2
    · exact le_of_eq_of_le (probEvent_eq_zero fun _ _ h => hx ⟨h.1, h.2.1⟩) zero_le
  have h2 : Pr[fun parts => ∃ x : C.Party × C.Party × C.Party × C.Party, x.1 ∉ D.1 ∧
      (x.1, x.2.1) ≠ (x.2.2.1, x.2.2.2) ∧ (parts x.1).pair x.2.1 = (parts x.2.2.1).pair x.2.2.2 |
      prssSampleParts D] ≤ (Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℝ≥0∞) * (1 / 2 ^ 256) := by
    have he := probEvent_exists_finset_le_sum (Finset.univ : Finset (C.Party × C.Party × C.Party × C.Party))
      (prssSampleParts D) fun x parts => x.1 ∉ D.1 ∧ (x.1, x.2.1) ≠ (x.2.2.1, x.2.2.2) ∧
        (parts x.1).pair x.2.1 = (parts x.2.2.1).pair x.2.2.2
    simp only [Finset.mem_univ, true_and] at he
    refine he.trans ?_
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x.1 ∉ D.1 ∧ (x.1, x.2.1) ≠ (x.2.2.1, x.2.2.2)
    · refine le_trans (probEvent_mono fun _ _ h => h.2.2) ?_
      exact prob_prssSampleParts_pair_eq_le D _ _ _ _ hx.1 hx.2
    · exact le_of_eq_of_le (probEvent_eq_zero fun _ _ h => hx ⟨h.1, h.2.1⟩) zero_le
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  push_cast
  rw [← add_mul, mul_one_div]

/-- An event of a continuation that implies an event of its start is at most as likely as the latter. -/
theorem probEvent_bind_le_of_start {α β : Type} (m : ProbComp α) (k : α → ProbComp β) (Q : β → Prop)
    (P : α → Prop) (h : ∀ a ∈ support m, ∀ b ∈ support (k a), Q b → P a) : Pr[Q | m >>= k] ≤ Pr[P | m] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support m
  · split_ifs with hp
    · exact mul_le_of_le_one_right' probEvent_le_one
    · rw [probEvent_eq_zero fun b hb hq => hp (h a ha b hb hq), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul]
    exact zero_le

theorem prob_setupEarly_partsCollide_le (prims : Primitives) {C : Committee} {E : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State) :
    Pr[fun r => PartsCollide D (fun i => (r.1.1 i).1) |
      (simulateQ (localAnswer prims) (setupEarly D A start)).run ∅] ≤
      ((Fintype.card (C.Party × C.Party × C.Term × C.Term) +
        Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold setupEarly
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind]
  refine probEvent_bind_le_of_forall_le fun st _ => ?_
  refine (probEvent_bind_le_of_start _ _ _ (fun d => PartsCollide D (fun i => (d.1 i).1)) ?_).trans ?_
  · intro d _ b hb hq
    simp only [StateT.run_pure, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hb
    obtain ⟨_, _, rfl⟩ := hb
    exact hq
  · have he := evalDist_prssInitialData_parts prims D st.2
    calc _ = Pr[PartsCollide D | (fun r => fun i => (r.1 i).1) <$>
          (simulateQ (localAnswer prims) (prssInitialData D)).run st.2] := by
          rw [probEvent_map]
          rfl
      _ = Pr[PartsCollide D | prssSampleParts D] := by
          simp only [probEvent_def, he]
      _ ≤ _ := prob_partsCollide_le D

end Marginal


section Rows

variable {C : Committee}

/-- With no collision of the parts, the canonical input of a term differs from the derivation input of
another term at an honest holder. -/
theorem prssTermInput_ne_termQuery (D : C.Coalition) (parts view : C.Party → Parts C)
    (hc : ¬ PartsCollide D parts) (i : C.Party) (hi : i ∉ D.1) (hview : view i = parts i)
    (T T' : C.Term) (hiT : i ∈ C.holders T') (hTT : T' ≠ T) :
    prssTermInput parts T ≠ prssTermQuery view T' := by
  intro h
  simp only [prssTermInput, prssTermQuery, Query.derive.injEq, true_and] at h
  have hm : i ∈ C.parties.filter (· ∈ C.holders T') := by simp [Committee.parties, hiT]
  set l' := C.parties.filter (· ∈ C.holders T')
  set l := C.parties.filter (· ∈ C.holders T)
  have hidx : l'.idxOf i < l'.length := List.idxOf_lt_length_iff.mpr hm
  have hlen : l'.length = l.length := by
    simpa only [List.length_map] using (congrArg List.length h).symm
  have h2 := congrArg (fun L => L[l'.idxOf i]?) h
  simp only [List.getElem?_map, List.getElem?_idxOf hm, Option.map_some, hview] at h2
  rw [List.getElem?_eq_getElem (hlen ▸ hidx), Option.map_some, Option.some_inj] at h2
  exact hc (Or.inl ⟨(i, l[l'.idxOf i], T', T), hi, hTT, h2.symm⟩)

/-- With no collision of the parts, the canonical input of a pair differs from the derivation input
of another pair at an honest operator. -/
theorem prssPairInput_ne_pairQuery (D : C.Coalition) (parts view : C.Party → Parts C)
    (hc : ¬ PartsCollide D parts) (i j : C.Party) (hi : i ∉ D.1) (hview : view i = parts i)
    (hji : j ≠ i) (p : C.Pair) (hp : p ≠ C.pairOf i j (Ne.symm hji)) :
    prssPairInput parts p ≠ prssPairQuery i view j := by
  intro h
  simp only [prssPairInput, prssPairQuery, dif_neg hji, Committee.pairOf] at h hp
  split_ifs at h hp with hij
  · simp only [Query.derive.injEq, true_and, List.cons.injEq, hview] at h
    refine hc (Or.inr ⟨(i, j, p.1.1, p.1.2), hi, fun he => hp (Subtype.ext ?_), h.1.symm⟩)
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.1.symm he.2.symm
  · simp only [Query.derive.injEq, true_and, List.cons.injEq, hview] at h
    refine hc (Or.inr ⟨(i, j, p.1.2, p.1.1), hi, fun he => hp (Subtype.ext ?_), h.2.1.symm⟩)
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.2.symm he.1.symm

/-- The canonical derivation inputs of the hidden names. -/
def hiddenInputs (D : C.Coalition) (parts : C.Party → Parts C) : Finset (Query C) :=
  ((Finset.univ.filter fun T : C.Term => Hidden D (.term T)).image (prssTermInput parts)) ∪
    ((Finset.univ.filter fun p : C.Pair => Hidden D (.pair p)).image (prssPairInput parts))

/-- The derivation inputs of all rows. -/
def rowInputs (view : C.Party → C.Party → Parts C) : Finset (Query C) :=
  ((Finset.univ : Finset (C.Party × C.Term)).image fun x => prssTermQuery (view x.1) x.2) ∪
    ((Finset.univ : Finset (C.Party × C.Party)).image fun x => prssPairQuery x.1 (view x.1) x.2)

/-- The derivation input of a name in a row. -/
def RowQuery (view : C.Party → C.Party → Parts C) (i : C.Party) : KeyName C → Query C → Prop
  | .term T, y => i ∈ C.holders T ∧ y = prssTermQuery (view i) T
  | .pair p, y => ∃ j, ∃ h : j ≠ i, p = C.pairOf i j (Ne.symm h) ∧ y = prssPairQuery i (view i) j
  | .parameter, _ => False

theorem rowKey_query (prims : Primitives) {E : Type} (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : RevealRows C × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (prssRevealRows D active parts committed sent)).run s))
    (n : KeyName C) (k : HashOutput) (hk : RowKey r.1 n k) :
    ∃ i, i ∉ D.1 ∧ (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false ∧
      ∃ y, RowQuery (prssView parts (prssRevealInbox D active parts sent)) i n y ∧ r.2 y = some k := by
  obtain ⟨i, keys, shared, hrow, hv⟩ := hk
  obtain ⟨hi, -, ha, hdc⟩ := (prssRevealRows_cached prims D active parts committed sent s r hr).2 i _ hrow
  refine ⟨i, hi, ha, ?_⟩
  cases n with
  | parameter => exact hv.elim
  | term T =>
    obtain ⟨hiT, rfl⟩ := hv
    exact ⟨_, ⟨hiT, rfl⟩, hdc.1.1 T hiT⟩
  | pair p =>
    obtain ⟨j, hj, rfl, rfl⟩ := hv
    exact ⟨_, ⟨j, hj, rfl, rfl⟩, hdc.1.2 j hj⟩

theorem rowQuery_mem (view : C.Party → C.Party → Parts C) (i : C.Party) (n : KeyName C) (y : Query C)
    (h : RowQuery view i n y) : y ∈ rowInputs view := by
  unfold rowInputs
  cases n with
  | parameter => exact h.elim
  | term T =>
    obtain ⟨_, rfl⟩ := h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, T), Finset.mem_univ _, rfl⟩)
  | pair p =>
    obtain ⟨j, _, _, rfl⟩ := h
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)

/-- The canonical derivation input of a name. -/
def hiddenInput (parts : C.Party → Parts C) : KeyName C → Query C
  | .term T => prssTermInput parts T
  | .pair p => prssPairInput parts p
  | .parameter => .derive .prss .term []

theorem hidden_rowQuery {E : Type} (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false)
    (n : KeyName C) (hn : Hidden D n) (y : Query C)
    (hy : RowQuery (prssView parts (prssRevealInbox D active parts sent)) i n y) :
    y = hiddenInput parts n ∧ y ∈ hiddenInputs D parts := by
  unfold hiddenInputs
  cases n with
  | parameter => exact hy.elim
  | term T =>
    obtain ⟨hiT, rfl⟩ := hy
    have he : prssTermQuery (prssView parts (prssRevealInbox D active parts sent) i) T = prssTermInput parts T :=
      prssReveal_term_input D active parts sent i ha T hn hiT
    rw [he]
    exact ⟨rfl, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨T, by simpa using hn, rfl⟩)⟩
  | pair p =>
    obtain ⟨j, hj, rfl, rfl⟩ := hy
    have hi : i = (C.pairOf i j (Ne.symm hj)).1.1 ∨ i = (C.pairOf i j (Ne.symm hj)).1.2 := by
      unfold Committee.pairOf
      split_ifs <;> simp
    have he : prssPairQuery i (prssView parts (prssRevealInbox D active parts sent) i) j =
        prssPairInput parts (C.pairOf i j (Ne.symm hj)) := by
      simp only [prssPairQuery, dif_neg hj]
      exact prssReveal_pair_input D active parts sent i ha _ hn hi
    rw [he]
    exact ⟨rfl, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, by simpa using hn, rfl⟩)⟩

theorem prssPairQuery_kind (i : C.Party) (view : C.Party → Parts C) (j : C.Party) :
    ∃ v, prssPairQuery i view j = .derive .prss .pair v := by
  unfold prssPairQuery
  split_ifs <;> exact ⟨_, rfl⟩

theorem hiddenInput_ne_rowQuery (D : C.Coalition) (parts : C.Party → Parts C)
    (received : C.Party → Mail C E) (hc : ¬ PartsCollide D parts) (n n' : KeyName C)
    (hn : Hidden D n) (hnn : n ≠ n') (i : C.Party) (hi : i ∉ D.1) (y : Query C)
    (hy : RowQuery (prssView parts received) i n' y) : hiddenInput parts n ≠ y := by
  have hview : prssView parts received i i = parts i := by simp [prssView]
  cases n with
  | parameter => exact hn.elim
  | term T =>
    cases n' with
    | parameter => exact hy.elim
    | term T' =>
      obtain ⟨hiT, rfl⟩ := hy
      exact prssTermInput_ne_termQuery D parts _ hc i hi hview T T' hiT fun h => hnn (by rw [h])
    | pair p' =>
      obtain ⟨j, hj, -, rfl⟩ := hy
      obtain ⟨v, hv⟩ := prssPairQuery_kind i (prssView parts received i) j
      rw [hv]
      simp [hiddenInput, prssTermInput]
  | pair p =>
    cases n' with
    | parameter => exact hy.elim
    | term T' =>
      obtain ⟨_, rfl⟩ := hy
      simp [hiddenInput, prssPairInput, prssTermQuery]
    | pair p' =>
      obtain ⟨j, hj, rfl, rfl⟩ := hy
      exact prssPairInput_ne_pairQuery D parts _ hc i j hi hview hj p fun h => hnn (by rw [h])

/-- Keys that are not apart come from a collision of the answer at a hidden input with the answer at
another row input. -/
theorem rows_collision (prims : Primitives) {E : Type} (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : RevealRows C × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (prssRevealRows D active parts committed sent)).run s))
    (hc : ¬ PartsCollide D parts) (hka : ¬ KeysApart D r.1) :
    ∃ x ∈ hiddenInputs D parts, ∃ y ∈ rowInputs (prssView parts (prssRevealInbox D active parts sent)),
      x ≠ y ∧ r.2 x ≠ none ∧ r.2 x = r.2 y := by
  unfold KeysApart at hka
  push Not at hka
  obtain ⟨n, k, n', k', hk, hn, hk', hnn, rfl⟩ := hka
  obtain ⟨i, -, ha, x, hx, hxk⟩ := rowKey_query prims D active parts committed sent s r hr n k hk
  obtain ⟨i', hi', -, y, hy, hyk⟩ := rowKey_query prims D active parts committed sent s r hr n' k hk'
  obtain ⟨hxe, hxm⟩ := hidden_rowQuery D active parts sent i ha n hn x hx
  refine ⟨x, hxm, y, rowQuery_mem _ i' n' y hy, ?_, by simp [hxk], hxk.trans hyk.symm⟩
  rw [hxe]
  exact hiddenInput_ne_rowQuery D parts _ hc n n' hn hnn i' hi' y hy

theorem hiddenInputs_card (D : C.Coalition) (parts : C.Party → Parts C) :
    (hiddenInputs D parts).card ≤ Fintype.card C.Term + Fintype.card C.Pair := by
  unfold hiddenInputs
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ))
  · exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ))

theorem rowInputs_card (view : C.Party → C.Party → Parts C) :
    (rowInputs view).card ≤ Fintype.card (C.Party × C.Term) + Fintype.card (C.Party × C.Party) := by
  unfold rowInputs
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)
  · exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)

theorem hiddenInputs_derive (D : C.Coalition) (parts : C.Party → Parts C) :
    ∀ x ∈ hiddenInputs D parts, ∃ ph k v, x = .derive ph k v := by
  intro x hx
  simp only [hiddenInputs, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with ⟨T, -, rfl⟩ | ⟨p, -, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

theorem rowInputs_derive (view : C.Party → C.Party → Parts C) :
    ∀ y ∈ rowInputs view, ∃ ph k v, y = .derive ph k v := by
  intro y hy
  simp only [rowInputs, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · obtain ⟨v, hv⟩ := prssPairQuery_kind x.1 (view x.1) x.2
    exact ⟨_, _, _, hv⟩

end Rows

section RevealBound

variable {C : Committee} {E : Type}

/-- The number of the hidden inputs times the number of the row inputs. -/
def revealPairs (C : Committee) : ℕ :=
  (Fintype.card C.Term + Fintype.card C.Pair) *
    (Fintype.card (C.Party × C.Term) + Fintype.card (C.Party × C.Party))

theorem prob_setupReveal_le (prims : Primitives) (D : C.Coalition) {σ : Type}
    (t : (C.Party → Parts C × List HashOutput) × σ × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (s : HashCache C) (hfresh : ¬ EarlyCached D (t, s)) (hc : ¬ PartsCollide D (fun i => (t.1 i).1)) :
    Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | (simulateQ (localAnswer prims) (setupReveal D t)).run s] ≤
      (revealPairs C : ℝ≥0∞) / 2 ^ 256 := by
  rcases t with ⟨data, st, sent, _ | sent'⟩
  · refine le_of_eq_of_le (probEvent_eq_zero fun r hr hka => hka ?_) zero_le
    simp only [setupReveal, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rintro n k - - ⟨i, keys, shared, hrow, -⟩
    simp [rowsOf] at hrow
  · simp only [setupReveal, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    set parts : C.Party → Parts C := fun i => (data i).1
    set active := prssCommitActive D sent
    set X := hiddenInputs D parts
    set Y := rowInputs (prssView parts (prssRevealInbox D active parts sent'))
    refine (probEvent_bind_le_of_start _ _ _ (fun r => ∃ x ∈ X, ∃ y ∈ Y, x ≠ y ∧ r.2 x ≠ none ∧ r.2 x = r.2 y)
      fun r hr b hb hka => ?_).trans ?_
    · simp only [support_pure, Set.mem_singleton_iff] at hb
      subst hb
      exact rows_collision prims D active parts _ sent' s r hr hc hka
    · have hs : ∀ x ∈ X, s x = none := by
        intro x hx
        simp only [X, hiddenInputs, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hx
        by_contra hne
        rcases hx with ⟨T, ⟨-, hT⟩, rfl⟩ | ⟨p, ⟨-, hp⟩, rfl⟩
        · exact hfresh (Or.inl ⟨T, hT, hne⟩)
        · exact hfresh (Or.inr ⟨p, hp, hne⟩)
      refine (prob_collision_finset_le prims _ X Y (hiddenInputs_derive D parts) (rowInputs_derive _) s hs).trans ?_
      gcongr
      unfold revealPairs
      exact_mod_cast Nat.mul_le_mul (hiddenInputs_card D parts) (rowInputs_card _)

/-- An event of a run is at most a bad event of its start plus the bound of the continuation off it. -/
theorem probEvent_bind_le_add {α β : Type} (m : ProbComp α) (k : α → ProbComp β) (Q : β → Prop)
    (B : α → Prop) (ε : ℝ≥0∞) (h : ∀ a ∈ support m, ¬ B a → Pr[Q | k a] ≤ ε) :
    Pr[Q | m >>= k] ≤ Pr[B | m] + ε := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  calc _ ≤ ∑' a, ((if B a then Pr[= a | m] else 0) + Pr[= a | m] * ε) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ support m
        · split_ifs with hb
          · exact le_add_right (mul_le_of_le_one_right' probEvent_le_one)
          · rw [zero_add]
            gcongr
            exact h a ha hb
        · simp [probOutput_eq_zero_of_not_mem_support ha]
    _ ≤ _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite]
        exact add_le_add le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)

/-- Stage 2 in the extended reals, as a sum of the prequery term, the collisions of the parts and the
collisions of the derived keys. -/
theorem prob_notKeysApart_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (initial step q : ℕ) (hstart : IsQueryBoundP (A.start (corruptInputs D x) z) Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) :
    Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)] ≤
      (q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 +
        ((Fintype.card (C.Party × C.Party × C.Term × C.Term) +
          Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (revealPairs C : ℝ≥0∞) / 2 ^ 256 := by
  rw [worldRun_setupPrefix, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_add _ _ _ (fun r => EarlyCached D r ∨ PartsCollide D (fun i => (r.1.1 i).1))
    ((revealPairs C : ℝ≥0∞) / 2 ^ 256) fun r _ hb => ?_).trans ?_
  · push Not at hb
    exact prob_setupReveal_le prims D r.1 r.2 hb.1 hb.2
  · gcongr
    refine (probEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · exact prob_earlyCached_le prims D A _ initial step q hstart hstep hq
    · exact prob_setupEarly_partsCollide_le prims D A _

theorem one_le_termCount (C : Committee) : 1 ≤ termCount C := by
  unfold termCount Committee.n
  exact Nat.choose_pos (by have := C.one_le_t; omega)

theorem n_sq_le_prssKeyCount (C : Committee) : C.n * C.n ≤ 4 * prssKeyCount C := by
  unfold prssKeyCount
  have h1 := one_le_termCount C
  have h2 : C.n * (C.n - 1) = 2 * C.n.choose 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self C.n)).symm
  rcases Nat.lt_or_ge C.n 2 with h | h
  · have h3 : C.n * C.n ≤ 1 := by interval_cases C.n <;> simp
    omega
  · have : C.n * C.n ≤ 2 * (C.n * (C.n - 1)) := by
      have : C.n ≤ 2 * (C.n - 1) := by omega
      calc C.n * C.n ≤ C.n * (2 * (C.n - 1)) := Nat.mul_le_mul_left _ this
        _ = 2 * (C.n * (C.n - 1)) := by ring
    omega

/-- For at most `2 ^ 60` operators the collisions of the parts and of the derived keys fit in
`streamKeyError`. -/
theorem keysApartCount_le (C : Committee) (hn : C.n ≤ 2 ^ 60) :
    Fintype.card (C.Party × C.Party × C.Term × C.Term) + Fintype.card (C.Party × C.Party × C.Party × C.Party) +
      revealPairs C ≤ 2 ^ 127 * prssKeyCount C ^ 2 := by
  have hT := card_term C
  have hP := card_pair_le C
  have hsq := n_sq_le_prssKeyCount C
  simp only [revealPairs, Fintype.card_prod, Fintype.card_fin, hT]
  set m := prssKeyCount C
  set a := C.n.choose (C.t - 1)
  set n := C.n
  have ha : a ≤ m := by simp [m, a, prssKeyCount, termCount]
  have hab : a + Fintype.card C.Pair ≤ m := by simp only [m, a, prssKeyCount, termCount]; omega
  have hnn : n * n ≤ 2 ^ 120 := by
    calc n * n ≤ 2 ^ 60 * 2 ^ 60 := Nat.mul_le_mul hn hn
      _ = 2 ^ 120 := by norm_num
  have h1 : n * (n * (a * a)) ≤ 2 ^ 120 * (m * m) := by
    calc n * (n * (a * a)) = (n * n) * (a * a) := by ring
      _ ≤ 2 ^ 120 * (m * m) := Nat.mul_le_mul hnn (Nat.mul_le_mul ha ha)
  have h2 : n * (n * (n * n)) ≤ 16 * (m * m) := by
    calc n * (n * (n * n)) = (n * n) * (n * n) := by ring
      _ ≤ (4 * m) * (4 * m) := Nat.mul_le_mul hsq hsq
      _ = 16 * (m * m) := by ring
  have h3 : (a + Fintype.card C.Pair) * (n * a + n * n) ≤ (2 ^ 60 + 4) * (m * m) := by
    calc (a + Fintype.card C.Pair) * (n * a + n * n) ≤ m * (2 ^ 60 * m + 4 * m) :=
          Nat.mul_le_mul hab (Nat.add_le_add (Nat.mul_le_mul hn ha) hsq)
      _ = (2 ^ 60 + 4) * (m * m) := by ring
  calc _ ≤ 2 ^ 120 * (m * m) + 16 * (m * m) + (2 ^ 60 + 4) * (m * m) :=
        Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ ≤ 2 ^ 127 * m ^ 2 := by
      rw [sq, ← add_mul, ← add_mul]
      exact Nat.mul_le_mul_right _ (by norm_num)

end RevealBound

section KeysApart

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Stage 2. -/
theorem treeKeysApartBound : TreeKeysApartBound (C := C) (E := E) prims circuits settings := by
  intro _ D A x z Z q _ hq
  obtain ⟨st, stp, fin, hsum, hS, hR, -, -⟩ := hq
  have hfuel : 2 ≤ ceremonyFuel circuits settings := by unfold ceremonyFuel setupRounds; omega
  have hq2 : st + 2 * stp ≤ q := by
    have := Nat.mul_le_mul_right stp hfuel
    omega
  have hE := prob_notKeysApart_le prims D A x z st stp q (hS _ _) hR hq2
  have hsq := n_sq_le_prssKeyCount C
  have hm : prssKeyCount C = C.n.choose (C.t - 1) + C.n.choose 2 := rfl
  have hse : streamKeyError C = ((prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 129 := rfl
  rw [hse]
  have hq0 : (0 : ℝ) ≤ ((q * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256 :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _)
  by_cases hn : C.n ≤ 2 ^ 60
  · have hK := keysApartCount_le C hn
    set K1 := Fintype.card (C.Party × C.Party × C.Term × C.Term) + Fintype.card (C.Party × C.Party × C.Party × C.Party)
    have hE' : Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)] ≤
        ((q * prssKeyCount C + K1 + revealPairs C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
      refine hE.trans (le_of_eq ?_)
      rw [hm]
      push_cast
      rw [ENNReal.add_div, ENNReal.add_div]
    have hr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)) hE'
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
    refine hr.trans ?_
    have hK' : ((K1 + revealPairs C : ℕ) : ℝ) ≤ 2 ^ 127 * ((prssKeyCount C ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hK
    rw [show ((q * prssKeyCount C + K1 + revealPairs C : ℕ) : ℝ) =
      ((q * prssKeyCount C : ℕ) : ℝ) + ((K1 + revealPairs C : ℕ) : ℝ) by push_cast; ring]
    rw [add_div, add_comm]
    refine add_le_add_left (α := ℝ) ?_ _
    calc ((K1 + revealPairs C : ℕ) : ℝ) / 2 ^ 256 ≤ 2 ^ 127 * ((prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 256 :=
          div_le_div_of_nonneg_right hK' (pow_nonneg zero_le_two _)
      _ = _ := by
          rw [show (2 : ℝ) ^ 256 = 2 ^ 127 * 2 ^ 129 by norm_num, mul_div_mul_left _ _ (by norm_num)]
  · have hbig : (1 : ℝ) ≤ ((prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 129 := by
      have h1 : 2 ^ 60 * 2 ^ 60 < C.n * C.n := Nat.mul_lt_mul'' (by omega) (by omega)
      have h2 : 2 ^ 129 ≤ prssKeyCount C ^ 2 := by
        have : 2 ^ 118 ≤ prssKeyCount C := by omega
        calc 2 ^ 129 ≤ 2 ^ 118 * 2 ^ 118 := by norm_num
          _ ≤ prssKeyCount C * prssKeyCount C := Nat.mul_le_mul this this
          _ = prssKeyCount C ^ 2 := (sq _).symm
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast h2
    have hp : (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)]).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
    linarith

end KeysApart

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- `TreeStreamKeyAfterDerivation` from the two stages. -/
theorem treeStreamKeyAfterDerivationFull
    (hHit : TreeKeyHitBound prims K circuits settings) :
    TreeStreamKeyAfterDerivation prims K circuits settings :=
  treeStreamKeyAfterDerivation prims K circuits settings (treeKeysApartBound prims circuits settings) hHit

/-- `TreeSecurityStatement` from the simulation hop. -/
theorem treeSecurityOfSimFull
    (hHit : TreeKeyHitBound prims K circuits settings)
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityOfSim prims K circuits settings (treeKeysApartBound prims circuits settings) hHit hSim

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.treeKeysApartBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeysApartBound

/-- info: 'ThresholdLeanXmssSecurity.treeStreamKeyAfterDerivationFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStreamKeyAfterDerivationFull

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityOfSimFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityOfSimFull

end ThresholdLeanXmssSecurity
