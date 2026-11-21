import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepCommitCore

/-!
# Designated reads with a pad per cell

`cell : ι → Query C` is a finite injective family of designated cells.

* `padWorld cell π P` is `writeWorld` where the first private value of `cell ι` is the shared value of
  the cell plus `π ι`. Each `π ι` is read at most once, at the first designated read of `cell ι`. So
  `writeWorld` is `padWorld` on a uniform `π` (`wp_writeWorld_eq_pad`, hop B).
* `padCells cell π` adds `π ι` to the answer of each free call at `cell ι`. `padWorld` on a program is
  the shared world on the padded program (`wp_padWorld_eq`, hop C), since the private value of
  `cell ι` is always the shared value plus `π ι`.
* `wp_shared_eq_des` joins the three hops. For a program that the pad does not change and that makes
  no programming call at a designated cell, the shared world and `desWorld` give one law of the result
  and of the flag, from each world state.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_mono)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The uniform value under a shift -/

theorem wp_uniform_xor (a : HashOutput) (f : HashOutput → ℝ≥0∞) :
    wp ($ᵗ HashOutput) (fun u => f (a ^^^ u)) = wp ($ᵗ HashOutput) f := by
  have hU : ((fun u => u ^^^ a) <$> ($ᵗ HashOutput)) =ᵈ $ᵗ HashOutput :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective (xor_bijective _)
  have e : wp ($ᵗ HashOutput) (fun u => f (a ^^^ u)) = wp ((fun u => u ^^^ a) <$> ($ᵗ HashOutput)) f := by
    rw [wp_map]
    refine congrArg _ (funext fun u => ?_)
    simp [BitVec.xor_comm]
  rw [e]
  exact wp_congr_evalDist_map _ (hU.map f).evalDist_eq

/-! ## The world with the pads -/

section Pad

variable (prims : Primitives) (D : C.Coalition) {ι : Type} (cell : ι → Query C)

/-- The designated cells of the family. -/
def InFamily (q : Query C) : Prop := ∃ i, cell i = q

/-- `writeWorld` where the first private value of `cell i` is the shared value of the cell plus `π i`. -/
def padWorld (π : ι → HashOutput) (P : (WorldSpec C).Domain → Prop) :
    QueryImpl (WorldSpec C) (StateT (PairState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if h : InFamily cell q then StateT.mk fun s => do
        let a ← ((Query C →ₒ HashOutput).randomOracle q).run s.1.1.1
        pure ((s.2.1 q).getD (a.1 ^^^ π h.choose), (((a.2, s.1.1.2), s.1.2),
          (if (s.2.1 q).isSome then s.2.1 else s.2.1.cacheQuery q (a.1 ^^^ π h.choose)), s.2.2))
      else desWorld prims D (InFamily cell) P (.inr (.inr (.inl q)))
  | t => desWorld prims D (InFamily cell) P t

/-- Each free call at `cell i` sees its answer plus `π i`. -/
def padCells (π : ι → HashOutput) : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if h : InFamily cell q then
        (fun a => a ^^^ π h.choose) <$>
          (liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) HashOutput)
      else liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q))))
  | t => liftM (OracleSpec.query t)

variable (P : (WorldSpec C).Domain → Prop)

theorem choose_cell (hcell : Function.Injective cell) (i : ι) (h : InFamily cell (cell i)) : h.choose = i :=
  hcell h.choose_spec

theorem padWorld_cell (π : ι → HashOutput) (hcell : Function.Injective cell) (i : ι) (s : PairState C) :
    (padWorld prims D cell π P (.inr (.inr (.inl (cell i))))).run s = (do
      let a ← ((Query C →ₒ HashOutput).randomOracle (cell i)).run s.1.1.1
      pure ((s.2.1 (cell i)).getD (a.1 ^^^ π i), (((a.2, s.1.1.2), s.1.2),
        (if (s.2.1 (cell i)).isSome then s.2.1 else s.2.1.cacheQuery (cell i) (a.1 ^^^ π i)), s.2.2))) := by
  have h : InFamily cell (cell i) := ⟨i, rfl⟩
  simp only [padWorld, h, dite_true, StateT.run_mk, choose_cell cell hcell i h]

theorem padWorld_of_not (π : ι → HashOutput) (t : (WorldSpec C).Domain)
    (h : ∀ q, t = .inr (.inr (.inl q)) → ¬ InFamily cell q) :
    padWorld prims D cell π P t = desWorld prims D (InFamily cell) P t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  simp only [padWorld, h q rfl, dite_false]

/-- A step of `padWorld` reads no pad of a cell whose private value is set. -/
theorem padWorld_update [DecidableEq ι] (π : ι → HashOutput) (hcell : Function.Injective cell) (i : ι) (w : HashOutput)
    (t : (WorldSpec C).Domain) (s : PairState C) (hs : (s.2.1 (cell i)).isSome) :
    (padWorld prims D cell (Function.update π i w) P t).run s = (padWorld prims D cell π P t).run s := by
  by_cases ht : ∃ j, t = .inr (.inr (.inl (cell j)))
  · obtain ⟨j, rfl⟩ := ht
    rw [padWorld_cell prims D cell P _ hcell, padWorld_cell prims D cell P _ hcell]
    by_cases hij : j = i
    · subst hij
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
      simp only [hv, Option.getD_some, Option.isSome_some, ite_true]
    · simp only [Function.update_of_ne hij]
  · rw [padWorld_of_not prims D cell P _ t (fun q e ⟨j, hj⟩ => ht ⟨j, by rw [e, hj]⟩),
      padWorld_of_not prims D cell P _ t (fun q e ⟨j, hj⟩ => ht ⟨j, by rw [e, hj]⟩)]

/-- Each step of `padWorld` grows the private cache. -/
theorem padWorld_mono (π : ι → HashOutput) (hcell : Function.Injective cell) (t : (WorldSpec C).Domain)
    (s : PairState C) : ∀ z ∈ support ((padWorld prims D cell π P t).run s), s.2.1 ≤ z.2.2.1 := by
  intro z hz
  by_cases ht : ∃ j, t = .inr (.inr (.inl (cell j)))
  · obtain ⟨j, rfl⟩ := ht
    rw [padWorld_cell prims D cell P _ hcell] at hz
    simp only [support_bind, Set.mem_iUnion] at hz
    obtain ⟨a, -, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    cases hc : s.2.1 (cell j) with
    | some v =>
      simp only [Option.isSome_some, ite_true]
      exact le_rfl
    | none =>
      simp only [Option.isSome_none]
      intro q' u hu
      have hne : q' ≠ cell j := fun e => by rw [e, hc] at hu; cases hu
      simpa [QueryCache.cacheQuery_of_ne _ _ hne] using hu
  · rw [padWorld_of_not prims D cell P _ t (fun q e ⟨j, hj⟩ => ht ⟨j, by rw [e, hj]⟩)] at hz
    by_cases hf : ∃ q, t = .inr (.inr (.inl q))
    · obtain ⟨q, rfl⟩ := hf
      have hq : ¬ InFamily cell q := fun ⟨j, hj⟩ => ht ⟨j, by rw [hj]⟩
      rw [desWorld_free prims D _ P hq] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact le_rfl
    · push Not at hf
      rw [desWorld_other prims D _ P t hf] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact le_rfl

theorem wp_padWorld_update [DecidableEq ι] (π : ι → HashOutput) (hcell : Function.Injective cell) (i : ι) (w : HashOutput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) : ∀ (s : PairState C), (s.2.1 (cell i)).isSome →
      ∀ F : α × PairState C → ℝ≥0∞,
      wp ((simulateQ (padWorld prims D cell (Function.update π i w) P) oa).run s) F =
        wp ((simulateQ (padWorld prims D cell π P) oa).run s) F := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _ F; simp
  | query_bind t k ih =>
    intro s hs F
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self,
      StateT.run_bind, wp_bind]
    rw [padWorld_update prims D cell P π hcell i w t s hs]
    refine wp_congr_of_support _ fun z hz => ih z.1 z.2 ?_ F
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    rw [padWorld_mono prims D cell P π hcell t s z hz hv]
    rfl

/-- The second hop. `writeWorld` is `padWorld` on a uniform pad. -/
theorem wp_writeWorld_eq_pad [Fintype ι] [DecidableEq ι] [SampleableType (ι → HashOutput)]
    (hcell : Function.Injective cell) {α : Type} (oa : OracleComp (WorldSpec C) α) : ∀ (s : PairState C)
    (F : α × PairState C → ℝ≥0∞),
    wp ((simulateQ (writeWorld prims D (InFamily cell) P) oa).run s) F =
      wp ($ᵗ (ι → HashOutput)) fun π => wp ((simulateQ (padWorld prims D cell π P) oa).run s) F := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s F; simp
  | query_bind t k ih =>
    intro s F
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self,
      StateT.run_bind, wp_bind]
    simp only [ih]
    by_cases hC : ∃ i, t = .inr (.inr (.inl (cell i))) ∧ s.2.1 (cell i) = none
    · obtain ⟨i, rfl, hc⟩ := hC
      rw [writeWorld_des prims D _ P ⟨i, rfl⟩]
      simp only [padWorld_cell prims D cell P _ hcell, hc, randomOracle.run_eq (cache := s.2.1), wp_bind, wp_pure,
        id, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [DkgSecurityProof.wp_swap ($ᵗ (ι → HashOutput))]
      refine congrArg _ (funext fun a => ?_)
      rw [SeedCompare.wp_uniform_update i]
      refine (wp_uniform_xor a.1 _).symm.trans ?_
      refine congrArg _ (funext fun u => congrArg _ (funext fun g => ?_))
      rw [Function.update_self]
      exact (wp_padWorld_update prims D cell P g hcell i u (k (a.1 ^^^ u))
        (((a.2, s.1.1.2), s.1.2), s.2.1.cacheQuery (cell i) (a.1 ^^^ u), s.2.2)
        (by simp only [QueryCache.cacheQuery_self, Option.isSome_some]) F).symm
    · have e : ∀ π, (padWorld prims D cell π P t).run s = (writeWorld prims D (InFamily cell) P t).run s := by
        intro π
        by_cases ht : ∃ i, t = .inr (.inr (.inl (cell i)))
        · obtain ⟨i, rfl⟩ := ht
          obtain ⟨v, hv⟩ : ∃ v, s.2.1 (cell i) = some v := by
            rcases h : s.2.1 (cell i) with _ | v
            · exact absurd ⟨i, rfl, h⟩ hC
            · exact ⟨v, rfl⟩
          rw [padWorld_cell prims D cell P _ hcell, writeWorld_des prims D _ P ⟨i, rfl⟩, randomOracle.run_eq _ s.2.1, hv]
          simp only [pure_bind, Option.getD_some, Option.isSome_some, ite_true]
        · rw [padWorld_of_not prims D cell P _ t (fun q e ⟨j, hj⟩ => ht ⟨j, by rw [e, hj]⟩),
            writeWorld_of_not prims D _ P t (fun q e ⟨j, hj⟩ => ht ⟨j, by rw [e, hj]⟩)]
      simp only [e]
      exact (DkgSecurityProof.wp_swap _ _ _).symm

end Pad

/-! ## A run that follows another run by a map of each step -/

/-- Two handlers whose steps agree on the answer, where each step of the first is a map of the step of
the second, keep a relation `R` of the states. Then the runs give one law of the result and of the
projections `proj₁` and `proj₂`, which agree under `R`. -/
theorem wp_simulateQ_of_map {ι' σ₁ σ₂ β : Type} {spec : OracleSpec ι'} (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp)) (R : σ₁ → σ₂ → Prop) (proj₁ : σ₁ → β) (proj₂ : σ₂ → β)
    (hproj : ∀ s₁ s₂, R s₁ s₂ → proj₁ s₁ = proj₂ s₂)
    (hstep : ∀ t s₁ s₂, R s₁ s₂ → ∃ g : spec.Range t × σ₂ → σ₁,
      (impl₁ t).run s₁ = (fun z => (z.1, g z)) <$> (impl₂ t).run s₂ ∧ ∀ z ∈ support ((impl₂ t).run s₂), R (g z) z.2)
    {α : Type} (G : α → β → ℝ≥0∞) (oa : OracleComp spec α) :
    ∀ s₁ s₂, R s₁ s₂ → wp ((simulateQ impl₁ oa).run s₁) (fun z => G z.1 (proj₁ z.2)) =
      wp ((simulateQ impl₂ oa).run s₂) (fun z => G z.1 (proj₂ z.2)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s₁ s₂ h; simp [hproj s₁ s₂ h]
  | query_bind t k ih =>
    intro s₁ s₂ h
    obtain ⟨g, hg, hR⟩ := hstep t s₁ s₂ h
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self,
      StateT.run_bind, wp_bind, hg, wp_map, Function.comp_def]
    exact wp_congr_of_support _ fun z hz => ih z.1 (g z) z.2 (hR z hz)

/-! ## Hop C, the pad world is the shared world on the padded program -/

section HopC

variable (prims : Primitives) (D : C.Coalition) {ι : Type} (cell : ι → Query C) (P : (WorldSpec C).Domain → Prop)

/-- The private value of `cell i` is the shared value of the cell plus `π i`, the world states agree, and
the flags agree. -/
def PadSync (π : ι → HashOutput) (s₁ s₂ : PairState C) : Prop :=
  s₁.1 = s₂.1 ∧ s₁.2.2 = s₂.2.2 ∧ ∀ i v, s₁.2.1 (cell i) = some v → ∃ a, s₁.1.1.1 (cell i) = some a ∧ v = a ^^^ π i

theorem randomOracle_stored (q : Query C) (c : HashCache C) :
    ∀ a ∈ support (((Query C →ₒ HashOutput).randomOracle q).run c), a.2 q = some a.1 ∧ Grows c a.2 := by
  intro a ha
  refine ⟨?_, (randomOracle_grows q c a ha).1⟩
  rw [randomOracle.run_eq] at ha
  cases hc : c q with
  | some v =>
    rw [hc] at ha
    simp only [support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact hc
  | none =>
    rw [hc] at ha
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ha
    obtain ⟨u, _, rfl⟩ := ha
    simp

theorem padCells_other (π : ι → HashOutput) (t : (WorldSpec C).Domain) (h : ∀ q, t ≠ .inr (.inr (.inl q))) :
    padCells cell π t = liftM (OracleSpec.query t) := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  exact absurd rfl (h q)

theorem padWorld_step (π : ι → HashOutput) (hcell : Function.Injective cell) (hfix : ∀ i, ¬ IsFixed (cell i))
    (t : (WorldSpec C).Domain) (s₁ s₂ : PairState C) (h : PadSync cell π s₁ s₂) :
    ∃ g : (WorldSpec C).Range t × PairState C → PairState C,
      (padWorld prims D cell π P t).run s₁ =
        (fun z => (z.1, g z)) <$> ((desWorld prims D (fun _ => False) P ∘ₛ padCells cell π) t).run s₂ ∧
      ∀ z ∈ support (((desWorld prims D (fun _ => False) P ∘ₛ padCells cell π) t).run s₂),
        PadSync cell π (g z) z.2 := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hc : ∃ i, t = .inr (.inr (.inl (cell i)))
  · obtain ⟨i, rfl⟩ := hc
    have hf : InFamily cell (cell i) := ⟨i, rfl⟩
    have e₂ : ((desWorld prims D (fun _ => False) P ∘ₛ padCells cell π) (.inr (.inr (.inl (cell i))))).run s₂ =
        (fun r => (r.1 ^^^ π i, (((r.2, s₂.1.1.2), s₂.1.2), s₂.2))) <$>
          ((Query C →ₒ HashOutput).randomOracle (cell i)).run s₂.1.1.1 := by
      simp only [QueryImpl.apply_compose, padCells, hf, dite_true, choose_cell cell hcell i hf, simulateQ_map,
        simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, StateT.run_map,
        desWorld_free prims D (fun _ => False) P (not_false), loggedWorld_freeHash, Functor.map_map,
        hashAnswer_of_not_isFixed prims (hfix i)]
    rw [e₂, padWorld_cell prims D cell P π hcell, h1]
    cases hv : s₁.2.1 (cell i) with
    | some v =>
      obtain ⟨a₀, ha₀, rfl⟩ := h3 i v hv
      rw [h1] at ha₀
      refine ⟨fun z => (z.2.1, s₁.2.1, s₁.2.2), ?_, fun z hz => ?_⟩
      · rw [randomOracle.run_eq, ha₀]
        simp only [pure_bind, map_pure, Option.getD_some, Option.isSome_some, ite_true]
      · rw [randomOracle.run_eq, ha₀] at hz
        simp only [map_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨rfl, h2, fun j v' hv' => ?_⟩
        obtain ⟨a, ha, rfl⟩ := h3 j v' hv'
        exact ⟨a, by rw [← h1]; exact ha, rfl⟩
    | none =>
      refine ⟨fun z => (z.2.1, s₁.2.1.cacheQuery (cell i) z.1, s₁.2.2), ?_, fun z hz => ?_⟩
      · simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false, Functor.map_map,
          bind_pure_comp]
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        obtain ⟨hst, hg⟩ := randomOracle_stored (cell i) s₂.1.1.1 a ha
        refine ⟨rfl, h2, fun j v' hv' => ?_⟩
        by_cases hji : j = i
        · subst hji
          simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv'
          exact ⟨a.1, hst, hv'.symm⟩
        · have hne : cell j ≠ cell i := fun e => hji (hcell e)
          rw [QueryCache.cacheQuery_of_ne _ _ hne] at hv'
          obtain ⟨a', ha', rfl⟩ := h3 j v' hv'
          rw [h1] at ha'
          exact ⟨a', hg _ a' ha', rfl⟩
  · have hnot : ∀ q, t = .inr (.inr (.inl q)) → ¬ InFamily cell q := fun q e ⟨j, hj⟩ => hc ⟨j, by rw [e, hj]⟩
    rw [padWorld_of_not prims D cell P π t hnot]
    by_cases hfree : ∃ q, t = .inr (.inr (.inl q))
    · obtain ⟨q, rfl⟩ := hfree
      have hq := hnot q rfl
      have e₂ : ((desWorld prims D (fun _ => False) P ∘ₛ padCells cell π) (.inr (.inr (.inl q)))).run s₂ =
          (desWorld prims D (fun _ => False) P (.inr (.inr (.inl q)))).run s₂ := by
        simp only [QueryImpl.apply_compose, padCells, hq, dite_false, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map]
      rw [e₂, desWorld_free prims D _ P hq, desWorld_free prims D _ P (not_false), h1]
      refine ⟨fun z => (z.2.1, s₁.2), by rw [Functor.map_map], fun z hz => ?_⟩
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      refine ⟨rfl, h2, fun j v hv => ?_⟩
      obtain ⟨a, ha, rfl⟩ := h3 j v hv
      rw [h1] at ha
      exact ⟨a, (loggedWorld_grows prims D _ _ r hr).1 _ a ha, rfl⟩
    · push Not at hfree
      have e₂ : ((desWorld prims D (fun _ => False) P ∘ₛ padCells cell π) t).run s₂ =
          (desWorld prims D (fun _ => False) P t).run s₂ := by
        simp only [QueryImpl.apply_compose, padCells_other cell π t hfree, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map]
      rw [e₂, desWorld_other prims D _ P t hfree, desWorld_other prims D _ P t hfree, h1, h2]
      refine ⟨fun z => (z.2.1, s₁.2.1, z.2.2.2), by rw [Functor.map_map], fun z hz => ?_⟩
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      refine ⟨rfl, rfl, fun j v hv => ?_⟩
      obtain ⟨a, ha, rfl⟩ := h3 j v hv
      rw [h1] at ha
      exact ⟨a, (loggedWorld_grows prims D _ _ r hr).1 _ a ha, rfl⟩

/-- The general lemma. For a program that a pad per designated cell does not change and that makes no
programming call at a designated cell, the shared world and `desWorld` of the designated cells give one
law of the result and of the flag, from each world state. -/
theorem wp_shared_eq_des [Fintype ι] [DecidableEq ι] [SampleableType (ι → HashOutput)]
    (hcell : Function.Injective cell) (hfix : ∀ i, ¬ IsFixed (cell i)) (hstream : ∀ i k, cell i ≠ .streamKey k)
    {α : Type} (G : α → Bool → ℝ≥0∞) (oa : OracleComp (WorldSpec C) α) (hprog : NoCall (ProgDes (InFamily cell)) oa)
    (hpad : ∀ π, simulateQ (padCells cell π) oa = oa) (w : LogState C) (b : Bool) :
    wp ((simulateQ (desWorld prims D (fun _ => False) P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2) =
      wp ((simulateQ (desWorld prims D (InFamily cell) P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2) := by
  have hD : DesFacts (InFamily cell) :=
    ⟨fun q ⟨i, hi⟩ => hi ▸ hfix i, fun q ⟨i, hi⟩ k => hi ▸ hstream i k⟩
  have hC : ∀ π : ι → HashOutput,
      wp ((simulateQ (desWorld prims D (fun _ => False) P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2) =
        wp ((simulateQ (padWorld prims D cell π P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2) := by
    intro π
    conv_lhs => rw [← hpad π]
    rw [← QueryImpl.simulateQ_compose]
    exact (wp_simulateQ_of_map _ _ (PadSync cell π) (fun s => s.2.2) (fun s => s.2.2) (fun _ _ h => h.2.1)
      (fun t s₁ s₂ h => padWorld_step prims D cell P π hcell hfix t s₁ s₂ h) G oa _ _
      ⟨rfl, rfl, fun i v hv => by simp at hv⟩).symm
  calc _ = wp ($ᵗ (ι → HashOutput)) (fun _ =>
        wp ((simulateQ (desWorld prims D (fun _ => False) P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2)) :=
          (wp_const _ _).symm
    _ = wp ($ᵗ (ι → HashOutput)) (fun π =>
        wp ((simulateQ (padWorld prims D cell π P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2)) :=
          congrArg _ (funext hC)
    _ = wp ((simulateQ (writeWorld prims D (InFamily cell) P) oa).run (w, ∅, b)) (fun z => G z.1 z.2.2.2) :=
          (wp_writeWorld_eq_pad prims D cell P hcell oa _ _).symm
    _ = _ := wp_writeWorld prims D (InFamily cell) P hD G oa hprog _

end HopC

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.wp_shared_eq_des' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.wp_shared_eq_des
