import ThresholdLeanXmssSecurity.Proof.Execution
import VCVio.ProgramLogic.Relational.Basic

/-!
# Couplings and query bounds

This module holds small lemmas on couplings and on counted calls.

* `relTriple_of_support_left` gives a coupling from a postcondition that holds on every left output.
  The signing proof uses it.
* `probEvent_uniform_coord_eq` bounds the probability that one coordinate of uniform secret points
  equals a fixed point. `SeedGenAlias` uses it.
* `WorldCounted`, `isQueryBoundP_adversary`, `isQueryBoundP_free` and `isQueryBoundP_sequenceFin`
  count the calls of a world computation. `PrssRand/KeyHop` uses them.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Couplings up to bad -/

section UpToBad

variable {α β : Type}

/-- A postcondition that holds for every left output and every right value holds on a coupling. -/
theorem relTriple_of_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    (h : ∀ a ∈ support oa, ∀ b, R a b) : RelTriple oa ob R :=
  relTriple_post_mono (relTriple_prod (P := fun a => ∀ b, R a b) (Q := fun _ => True) h fun _ _ => trivial)
    fun _ b hab => hab.1 b

end UpToBad

/-! ## Hitting a hidden secret -/

section Hit

open ENNReal

variable {κ σ S β : Type} {spec : OracleSpec κ}

variable {P : Type} [Fintype P] [DecidableEq P] [SampleableType P]

/-- One coordinate of `k` uniform secret points equals a fixed point with probability `1 / |P|`. -/
theorem probEvent_uniform_coord_eq {k : ℕ} (j : Fin k) (x : P) :
    Pr{let s ← $ᵗ (Fin k → P)}[s j = x] = (Fintype.card P : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
  have hfil : (Finset.univ.filter fun s : Fin k → P => s j = x).card = Fintype.card P ^ (k - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset P) j (Finset.mem_univ x)
    simpa using this
  have hk : k = (k - 1) + 1 := by have := j.2; omega
  have hP : (Fintype.card P : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨x⟩
    exact_mod_cast this.ne'
  rw [hfil, Fintype.card_fun, Fintype.card_fin, hk, pow_succ, Nat.cast_mul, Nat.add_sub_cancel]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP))))
    (Or.inl (by simp))]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP)))
    (ENNReal.natCast_ne_top _), one_mul]

end Hit

/-! ## Acceptance in the world -/

section World

variable (prims : Primitives) {C : Committee}

/-- The calls of a world computation that the budget counts, namely the counted calls of the counted
copy and its programming queries. -/
def WorldCounted : (WorldSpec C).Domain → Prop
  | .inl (.inl u) => Counted u
  | .inl (.inr _) => True
  | .inr _ => False

/-- The adversary role keeps the counted calls of a computation. -/
theorem isQueryBoundP_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) : IsQueryBoundP (worldRoles.adversary oa) WorldCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- The honest role makes no counted call. -/
theorem isQueryBoundP_free {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) :
    IsQueryBoundP (free oa) WorldCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

/-- A sequence of computations without counted calls makes no counted call. -/
theorem isQueryBoundP_sequenceFin {κ β : Type} {spec : OracleSpec κ} {p : κ → Prop} [DecidablePred p] :
    ∀ {N : ℕ} (f : Fin N → OracleComp spec β), (∀ i, IsQueryBoundP (f i) p 0) →
      IsQueryBoundP (OverPermutation.sequenceFin f) p 0
  | 0, f, _ => by simp [OverPermutation.sequenceFin]
  | N + 1, f, h => by
    simp only [OverPermutation.sequenceFin]
    exact isQueryBoundP_bind (h 0) fun _ _ => isQueryBoundP_bind
      (m := 0) (isQueryBoundP_sequenceFin (fun i : Fin N => f i.succ) fun i => h i.succ) fun _ _ => isQueryBoundP_pure _ _ 0

variable {E Ia I O L R α : Type} {C : Committee}

end World

end ThresholdLeanXmssSecurity
