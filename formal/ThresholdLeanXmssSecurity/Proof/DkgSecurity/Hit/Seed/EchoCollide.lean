import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoLocal

/-!
# Two cells of the lazy random oracle with equal values

`collidePot a b c` is `1` when the cache `c` holds equal values at `a` and `b`, `0` when it holds
different values, and `1 / 2^256` when one of the two cells has no value. Each atom of the lazy random
oracle keeps it in expectation (`wp_isAtom_collidePot`). So after a run of `compLocal` from a cache with
no value at `a` and at `b`, with `a ≠ b`, the two cells hold equal values with probability at most
`1 / 2^256` (`prEvent_collide_le`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-- The potential of a collision of the cells `a` and `b`. -/
def collidePot (a b : Query C) (c : HashCache C) : ℝ≥0∞ :=
  match c a, c b with
  | some u, some v => if u = v then 1 else 0
  | _, _ => (Fintype.card HashOutput : ℝ≥0∞)⁻¹

theorem collidePot_comm (a b : Query C) (c : HashCache C) : collidePot a b c = collidePot b a c := by
  unfold collidePot
  rcases c a with _ | u <;> rcases c b with _ | v
  · rfl
  · rfl
  · rfl
  · by_cases h : u = v
    · simp [h]
    · simp [h, Ne.symm h]

theorem collidePot_of_eq (a b : Query C) {c c' : HashCache C} (ha : c' a = c a) (hb : c' b = c b) :
    collidePot a b c' = collidePot a b c := by
  unfold collidePot
  rw [ha, hb]

/-- A fresh value at `a` keeps the potential in expectation. -/
theorem wp_fresh_collidePot (a b : Query C) (hab : a ≠ b) (c : HashCache C) (ha : c a = none) :
    wp ($ᵗ HashOutput) (fun u => collidePot a b (c.cacheQuery a u)) ≤ collidePot a b c := by
  have e : ∀ u, collidePot a b (c.cacheQuery a u) =
      match c b with
      | some v => if u = v then 1 else 0
      | none => (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := fun u => by
    unfold collidePot
    rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hab)]
    generalize c b = o
    cases o <;> rfl
  have hc : collidePot a b c = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    unfold collidePot
    rw [ha]
  simp only [e, hc]
  rcases c b with _ | v
  · exact (wp_const _ _).le
  · rw [← prEvent_eq_wp_indicator, SampleableType.prEvent_uniformSample]
    have h1 : (Finset.univ.filter fun u : HashOutput => u = v).card = 1 := by
      rw [Finset.filter_eq' Finset.univ v]
      simp
    rw [h1]
    simp

/-- A call of the lazy random oracle keeps the potential in expectation. -/
theorem wp_randomOracle_collidePot (a b : Query C) (hab : a ≠ b) (x : Query C) (c : HashCache C) :
    wp (((Query C →ₒ HashOutput).randomOracle x).run c) (fun z => collidePot a b z.2) ≤ collidePot a b c := by
  rcases hx : c x with _ | v
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hx]
    simp only [wp_map]
    by_cases hxa : x = a
    · subst hxa
      exact wp_fresh_collidePot x b hab c hx
    by_cases hxb : x = b
    · subst hxb
      simp only [collidePot_comm a x]
      exact wp_fresh_collidePot x a (Ne.symm hab) c hx
    · refine (wp_mono _ fun u => le_of_eq ?_).trans_eq (wp_const _ _)
      exact collidePot_of_eq a b (QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxa))
        (QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxb))
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hx, wp_pure]

/-- An atom of the lazy random oracle keeps the potential in expectation. -/
theorem wp_isAtom_collidePot (a b : Query C) (hab : a ≠ b) {α : Type} {m : StateT (HashCache C) ProbComp α}
    (hm : IsAtom m) (c : HashCache C) : wp (m.run c) (fun z => collidePot a b z.2) ≤ collidePot a b c := by
  rcases hm with ⟨p, rfl⟩ | ⟨x, f, rfl⟩
  · rw [StateT.run_lift, wp_bind]
    simp only [wp_pure]
    exact (wp_const _ _).le
  · rw [StateT.run_map, wp_map]
    exact wp_randomOracle_collidePot a b hab x c

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

/-- After a run of `compLocal` from a cache with no value at `a` and at `b`, with `a ≠ b`, the two cells
hold one value with probability at most `1 / 2^256`. -/
theorem prEvent_collide_le {α : Type} (X : OracleComp (LocalSpec C) α) (a b : Query C) (hab : a ≠ b)
    (c : HashCache C) (ha : c a = none) :
    Pr{let z ← (simulateQ (compLocal prims D parts seed) X).run c}[z.2 a ≠ none ∧ z.2 a = z.2 b] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [prEvent_eq_wp_indicator]
  have hc : collidePot a b c = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    unfold collidePot
    rw [ha]
  refine le_trans (wp_mono _ fun z => ?_) ((wp_simulateQ_le (compLocal prims D parts seed) (fun _ => True)
    (collidePot a b) (fun t _ w => wp_isAtom_collidePot a b hab (isAtom_compLocal prims D parts seed t) w) X
    (allQueriesSatisfy_of_forall (fun _ => trivial) X) c).trans_eq hc)
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 h1
    unfold collidePot
    rw [hu, ← h2, hu]
    simp
  · exact zero_le

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.prEvent_collide_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.prEvent_collide_le
