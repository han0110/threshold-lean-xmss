import ThresholdLeanXmss.Statement
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Lagrange

/-!
# The steps of the proofs

The intermediate results of the cited papers, each named after its source. The proofs of
`ThresholdLeanXmss/Statement.lean` combine them as follows.

* The key generation follows GS20, Theorem 2.
* Its gadget steps are `F_rand` from PRSS (CDI05), the reshare (GS20, Lemma 4) and the coin (GS20,
  Lemma 3).
* Its check steps are the digests (CGH+18, Protocol 3.3), the check (GS20, Lemmas 8 to 11), the word
  weights of `src/check.rs`, and the slice steps (Gruen 2024). The challenges come from
  `E \ {0, 1}`, so a step with at most two bad challenges fails with probability at most
  `2 / (|E| - 2)`.
* The outputs open as in MPClan, App. B. The keygen adds the extraction and programming of CDG+18.
* The signing follows the proof of leanVM, with the hidden keys in place of its seed (the signing
  plan in the module docstring of `ThresholdLeanXmssSecurity.lean`).
-/

open OracleComp OracleSpec LeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Uniform sampling of the check field. -/
@[reducible] def sampleableField : SampleableType E := SampleableType.ofFintype E

attribute [local instance] sampleableField

/-! ## Terms and quorums -/

theorem quorum_sdiff_term_nonempty (J : C.Quorum) (T : C.Term) : (J.1 \ T.1).Nonempty := by
  rw [← Finset.card_pos]
  have h := Finset.le_card_sdiff T.1 J.1
  have := C.one_le_t
  rw [J.2, T.2] at h
  omega

/-- A quorum holds every term (PRAWNS, Section 5, first key fact). -/
theorem prawns_quorum_holds_term (J : C.Quorum) (T : C.Term) : ∃ i ∈ J.1, i ∈ C.holders T := by
  obtain ⟨i, hi⟩ := quorum_sdiff_term_nonempty J T
  rw [Finset.mem_sdiff] at hi
  exact ⟨i, hi.1, by simpa [Committee.holders] using hi.2⟩

/-- Each term goes to exactly one signer of the quorum, so the parts combine (PRAWNS, Section 5). -/
theorem prawns_L_partition (J : C.Quorum) (T : C.Term) : ∃! i, i ∈ J.1 ∧ T ∈ L J i := by
  obtain ⟨i, hi⟩ := Finset.min_of_nonempty (quorum_sdiff_term_nonempty J T)
  refine ⟨i, ⟨(Finset.mem_sdiff.mp (Finset.mem_of_min hi)).1, by simpa [L] using hi⟩, fun j hj => ?_⟩
  have hj2 := hj.2
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hj2
  exact WithTop.coe_injective (hj2.symm.trans hi)

/-- A coalition lacks a term (PRAWNS, Section 5, second key fact, and CDI05, Section 3). -/
theorem prawns_coalition_lacks_term (D : C.Coalition) : ∃ T : C.Term, ∀ j ∈ D.1, j ∉ C.holders T := by
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq D.2
    (by simp [Committee.n]; omega)
  exact ⟨⟨T, hT⟩, fun j hj => by simpa [Committee.holders] using hDT hj⟩

/-- Two terms have a common holder, so `pairs_i` exists (CDI05, Section 4, with `2t - 2 < n`). -/
theorem cdi05_pair_has_holder (A B : C.Term) : ∃ i, i ∈ C.holders A ∧ i ∈ C.holders B := by
  have hcard : (A.1 ∪ B.1).card < Fintype.card C.Party := by
    have h := Finset.card_union_le A.1 B.1
    have := C.one_le_t
    rw [A.2, B.2] at h
    simp only [Fintype.card_fin, Committee.n]
    omega
  obtain ⟨i, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := A.1 ∪ B.1) (t := Finset.univ)
    (by simpa using hcard)
  exact ⟨i, by simp_all [Committee.holders]⟩

omit [Fintype E] [DecidableEq E] in
/-- The owner of a term is honest, or another holder is honest. This is a local ingredient of
MPClan, Appendix B, and not its full theorem. -/
theorem mpclan_honest_holder (K : Constants C E) (D : C.Coalition) (T : C.Term) :
    K.owner T ∉ D.1 ∨ ∃ h, h ∈ C.holders T ∧ h ∉ D.1 ∧ h ≠ K.owner T := by
  by_cases hown : K.owner T ∈ D.1
  · right
    have hcard : D.1.card < (C.holders T).card := by
      have hT : (C.holders T).card = C.t := by
        simp only [Committee.holders, Finset.card_compl, Fintype.card_fin, T.2, Committee.n]
        have := C.one_le_t
        omega
      have := D.2
      have := C.one_le_t
      omega
    obtain ⟨h, hh, hD⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨h, hh, hD, fun heq => hD (heq ▸ hown)⟩
  · exact Or.inl hown

/-! ## Sharings -/

omit [Fintype E] [DecidableEq E] in
open Polynomial in
/-- `Conv` of a replicated sharing is a Shamir sharing of degree `t - 1` of the same value (CDI05,
Section 4). -/
theorem cdi05_conv_correct [CharP E 2] (K : Constants C E) (x : C.Term → E) :
    ∃ V : Polynomial E, V.natDegree ≤ C.t - 1 ∧ V.eval 0 = ∑ T, x T ∧
      ∀ i, conv K (localContext i) (fun T _ => x T) 0 = V.eval (K.point i) := by
  classical
  refine ⟨∑ T, Polynomial.C (x T) * ∏ j ∈ T.1, (X + Polynomial.C (K.point j)) * Polynomial.C (K.point j)⁻¹,
    ?_, ?_, fun i => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun T _ =>
      (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    calc ∑ j ∈ T.1, ((X + Polynomial.C (K.point j)) * Polynomial.C (K.point j)⁻¹).natDegree
        ≤ ∑ _j ∈ T.1, 1 := Finset.sum_le_sum (f := fun j =>
          ((X + Polynomial.C (K.point j)) * Polynomial.C (K.point j)⁻¹).natDegree) fun j _ =>
          (natDegree_mul_C_le _ _).trans (natDegree_X_add_C _).le
      _ = C.t - 1 := by simp [T.2]
  · simp [eval_finsetSum, eval_prod, K.point_ne_zero]
  · simp only [conv, psi, localContext, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add,
      eval_X, ← div_eq_mul_inv]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs with hi
    · ring
    · have hiT : i ∈ T.1 := by simpa [Committee.holders] using hi
      rw [Finset.prod_eq_zero hiT (by rw [CharTwo.add_self_eq_zero, zero_div]), mul_zero]

omit [Fintype E] [DecidableEq E] in
theorem sum_sum_pairs {R : Type} [AddCommMonoid R] (K : Constants C E)
    (f : C.Term × C.Term → R) : ∑ i, ∑ AB ∈ K.pairs i, f AB = ∑ AB, f AB := by
  classical
  have h : ∀ i, ∑ AB ∈ K.pairs i, f AB = ∑ AB, if AB ∈ K.pairs i then f AB else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun AB _ => ?_
  obtain ⟨i, hi, hunique⟩ := K.pairs_unique AB
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg fun hj' => hj (hunique j hj')) (by simp)]
  exact if_pos hi

omit [Fintype E] [DecidableEq E] in
/-- The shares of `MulRep` sum to the product. This is a local ingredient of CDI05, Section 4, and
not its full theorem. -/
theorem cdi05_mulRep_correct {R : Type} [CommRing R] (K : Constants C E) (x y : C.Term → R) :
    ∑ i, mulRep K (localContext i) (fun T _ => x T) (fun T _ => y T) 0 = (∑ T, x T) * ∑ T, y T := by
  simp only [mulRep, localContext]
  rw [sum_sum_pairs K (fun AB => x AB.1 * y AB.2), Finset.sum_mul_sum,
    ← Finset.sum_product', Finset.univ_product_univ]

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
open Polynomial in
theorem Lagrange.eval_basis_eq_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → E) (i : ι)
    (x : E) : (Lagrange.basis s v i).eval x = ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C, eval_sub, eval_X]
  exact Finset.prod_congr rfl fun _ _ => by rw [div_eq_inv_mul]

omit [Fintype E] [DecidableEq E] in
open Polynomial in
theorem sum_lagrangeAll_mul_eval [CharP E 2] (K : Constants C E) (P : Polynomial E)
    (hP : P.natDegree ≤ C.n - 1) : ∑ i, lagrangeAll K i * P.eval (K.point i) = P.eval 0 := by
  have hn : 1 ≤ C.n := by have := C.one_le_t; simp only [Committee.n]; omega
  have hdeg : P.degree < (univ : Finset C.Party).card := by
    rw [card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hP).trans_lt (by exact_mod_cast (by omega : C.n - 1 < C.n))
  conv_rhs => rw [Lagrange.eq_interpolate K.point.injective.injOn hdeg]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.eval_basis_eq_prod, lagrangeAll]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zero_sub, CharTwo.neg_eq, CharTwo.sub_eq_add, add_comm]

omit [Fintype E] [DecidableEq E] in
open Polynomial in
/-- The shares of `MulSh` sum to the inner product, since the product of two polynomials of degree
`t - 1` has degree `n - 1` (GS20, Section 3.2). -/
theorem gs20_mulSh_correct [CharP E 2] (K : Constants C E) (count : ℕ) (X Y : ℕ → Polynomial E)
    (hX : ∀ g, (X g).natDegree ≤ C.t - 1) (hY : ∀ g, (Y g).natDegree ≤ C.t - 1) :
    ∑ i, mulSh K (localContext i) (fun g => (X g).eval (K.point i)) (fun g => (Y g).eval (K.point i)) count =
      ∑ g ∈ range count, (X g).eval 0 * (Y g).eval 0 := by
  simp only [mulSh, localContext, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hdeg : (X g * Y g).natDegree ≤ C.n - 1 :=
    (natDegree_mul_le).trans (by have := hX g; have := hY g; simp only [Committee.n]; omega)
  simpa [eval_mul] using sum_lagrangeAll_mul_eval K (X g * Y g) hdeg

/-! ## The check -/

omit [Fintype E] [DecidableEq E] in
/-- A nonzero word of bit differences keeps a nonzero weight, because the weights `x^q` are linearly
independent over `F_2` (`src/check.rs`). -/
theorem check_word_weight_ne_zero (K : Constants C E) (b : Fin (2 ^ wordBits) → Bit) (hb : b ≠ 0) :
    ∑ q, b q • K.weight q ≠ 0 := by
  intro h
  exact hb (funext fun q => Fintype.linearIndependent_iff.mp K.weight_independent b h q)

omit [Algebra Bit E] in
theorem card_filter_quadratic_eq_zero_le_two (c₀ c₁ c₂ : E) (h : c₀ ≠ 0 ∨ c₁ ≠ 0 ∨ c₂ ≠ 0) :
    (univ.filter fun ρ : E => c₀ + c₁ * ρ + c₂ * ρ ^ 2 = 0).card ≤ 2 := by
  let p : Polynomial E := .C c₀ + .C c₁ * .X + .C c₂ * .X ^ 2
  have hp : p ≠ 0 := by
    intro h0
    have h0' := fun n => congrArg (fun q : Polynomial E => q.coeff n) h0
    have e0 := h0' 0
    have e1 := h0' 1
    have e2 := h0' 2
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at e0 e1 e2
    rcases h with h | h | h <;> simp_all
  have hdeg : p.natDegree ≤ 2 := by
    simp only [p]
    compute_degree!
  calc (univ.filter fun ρ : E => c₀ + c₁ * ρ + c₂ * ρ ^ 2 = 0).card
      = (univ.filter fun ρ : E => p.eval ρ = 0).card := by
        congr 1; apply filter_congr; intro ρ _; simp [p]
    _ ≤ p.roots.toFinset.card := by
        apply card_le_card
        intro ρ hρ
        simp only [mem_filter] at hρ
        simpa [Multiset.mem_toFinset, Polynomial.mem_roots hp] using hρ.2
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ 2 := hdeg

omit [Algebra Bit E] in
theorem card_filter_le_two_of_quadratic {P : E → Prop} [DecidablePred P] (c₀ c₁ c₂ : E)
    (h : c₀ ≠ 0 ∨ c₁ ≠ 0 ∨ c₂ ≠ 0) (hP : ∀ ρ, P ρ → c₀ + c₁ * ρ + c₂ * ρ ^ 2 = 0) :
    (univ.filter P).card ≤ 2 :=
  (card_le_card fun ρ hρ => by simp only [mem_filter] at hρ ⊢; exact ⟨hρ.1, hP ρ hρ.2⟩).trans
    (card_filter_quadratic_eq_zero_le_two c₀ c₁ c₂ h)

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sum_zipWith_fold_eq [CharP E 2] (ρ : E) (lo hi lo' hi' : List E)
    (hlen : lo.length = hi.length ∧ lo'.length = hi'.length ∧ lo.length = lo'.length) :
    (List.zipWith (· * ·) (List.zipWith (fun a b => a + ρ * (a + b)) lo hi)
        (List.zipWith (fun a b => a + ρ * (a + b)) lo' hi')).sum =
      (List.zipWith (· * ·) lo lo').sum +
        ((List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum +
          (List.zipWith (· * ·) lo lo').sum + (List.zipWith (· * ·) hi hi').sum) * ρ +
        (List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum * ρ ^ 2 := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  induction lo generalizing hi lo' hi' with
  | nil =>
    obtain ⟨h1, h2, h3⟩ := hlen
    obtain rfl : hi = [] := List.eq_nil_of_length_eq_zero h1.symm
    obtain rfl : lo' = [] := List.eq_nil_of_length_eq_zero h3.symm
    obtain rfl : hi' = [] := List.eq_nil_of_length_eq_zero h2.symm
    simp
  | cons a lo ih =>
    obtain ⟨h1, h2, h3⟩ := hlen
    cases hi with
    | nil => simp at h1
    | cons b hi =>
      cases lo' with
      | nil => simp at h3
      | cons a' lo' =>
        cases hi' with
        | nil => simp at h2
        | cons b' hi' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
          simp only [List.zipWith_cons_cons, List.sum_cons]
          linear_combination ih hi lo' hi' ⟨h1, h2, h3⟩ - ρ * b * b' * two

omit [Algebra Bit E] in
/-- A halving step keeps a wrong claim wrong for all but two challenges (GS20, Protocol 14 and Lemma
9 with `k = 2`). -/
theorem gs20_lemma9_halving_step [CharP E 2] (lo hi lo' hi' : List E) (claim e0 e2 : E)
    (hwrong : claim ≠ (List.zipWith (· * ·) lo lo').sum + (List.zipWith (· * ·) hi hi').sum)
    (hlen : lo.length = hi.length ∧ lo'.length = hi'.length ∧ lo.length = lo'.length) :
    (univ.filter fun ρ : E =>
      (List.zipWith (· * ·) lo lo').sum + e0 +
          (claim + (List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum + e2) * ρ +
          ((List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum + e2) * ρ ^ 2 =
        (List.zipWith (· * ·) (List.zipWith (fun a b => a + ρ * (a + b)) lo hi)
          (List.zipWith (fun a b => a + ρ * (a + b)) lo' hi')).sum).card ≤ 2 := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  apply card_filter_le_two_of_quadratic e0
    (claim + e2 - (List.zipWith (· * ·) lo lo').sum - (List.zipWith (· * ·) hi hi').sum) e2
  · by_contra! h
    obtain ⟨h0, h1, h2⟩ := h
    subst h0 h2
    exact hwrong (by linear_combination h1)
  · intro ρ h
    linear_combination h + sum_zipWith_fold_eq ρ lo hi lo' hi' hlen

omit [Algebra Bit E] in
/-- A slice step keeps a wrong claim wrong for all but two challenges. It keeps the slice coin `c`
out of `x`, so the claim is `D = t(0) + c t(1)` for the quadratic `t(X) = t₀ + t₁ X + t₂ X²` of the
folded inner product. The step reshares `t(0)` and the leading coefficient with additive errors and
interpolates `t(r)` at `0`, `1` and `∞` (Gruen 2024, and `doc/dkg.md` 3.3). -/
theorem gruen_slice_step [CharP E 2] (c D t₀ t₁ t₂ e₀ eInf : E) (hc : c ≠ 0)
    (hwrong : D ≠ t₀ + c * (t₀ + t₁ + t₂)) :
    (univ.filter fun r : E =>
      (1 + r) * (t₀ + e₀) + r * ((D + (t₀ + e₀)) / c) + r * (1 + r) * (t₂ + eInf) =
        t₀ + t₁ * r + t₂ * r ^ 2).card ≤ 2 := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  apply card_filter_le_two_of_quadratic e₀ (t₀ + e₀ + (D + (t₀ + e₀)) / c + t₂ + eInf - t₁) eInf
  · by_contra! h
    obtain ⟨h0, h1, h2⟩ := h
    subst h0 h2
    apply hwrong
    field_simp at h1
    linear_combination h1 - t₀ * two - c * t₀ * two - c * t₂ * two
  · intro r h
    linear_combination h

omit [Algebra Bit E] in
/-- The final step accepts a wrong claim `D ≠ a b` for at most two challenges (GS20, Protocol 15 and
Lemma 10). -/
theorem gs20_lemma10_final_step [CharP E 2] (a b a0 b0 D e0 e2 : E) (hwrong : D ≠ a * b) :
    (univ.filter fun ρ : E =>
      (a0 + ρ * (a0 + a)) * (b0 + ρ * (b0 + b)) =
        (a0 * b0 + e0) + (D + (a0 * b0 + e0) + ((a0 + a) * (b0 + b) + e2)) * ρ +
          ((a0 + a) * (b0 + b) + e2) * ρ ^ 2).card ≤ 2 := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  apply card_filter_le_two_of_quadratic e0 (D + a * b + e0 + e2) e2
  · by_contra! h
    obtain ⟨h0, h1, h2⟩ := h
    apply hwrong
    linear_combination h1 - h0 - h2 + (-(a*b)) * two
  · intro ρ h
    linear_combination (norm := ring_nf) -h

omit [DecidableEq E] [Algebra Bit E] in
theorem final_opening_bijective [CharP E 2] (a ρ : E) (hρ : ρ ≠ 1) :
    Function.Bijective fun a0 : E => a0 + ρ * (a0 + a) := by
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  have hunit : (1 + ρ) ≠ 0 := by
    intro h
    exact hρ (by linear_combination h - CharTwo.add_self_eq_zero (1 : E))
  have : (1 + ρ) * (x - y) = 0 := by linear_combination hxy
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hunit)

omit [DecidableEq E] [Algebra Bit E] in
/-- With a uniform mask and `ρ ≠ 1`, the opened `a^(0) + ρ (a^(0) + a)` is uniform, so it hides `a`
(GS20, Lemma 11, Hybrid 2). -/
theorem gs20_lemma11_final_hides [CharP E 2] (a a' ρ : E) (hρ : ρ ≠ 1) :
    𝒟[(fun a0 : E => a0 + ρ * (a0 + a)) <$> ($ᵗ E)] = 𝒟[(fun a0 : E => a0 + ρ * (a0 + a')) <$> ($ᵗ E)] := by
  rw [evalDist_map_bijective_uniform_cross E _ (final_opening_bijective a ρ hρ),
    evalDist_map_bijective_uniform_cross E _ (final_opening_bijective a' ρ hρ)]

section Weights

open MvPolynomial

/-- `X_j` for `j < d`, else `0`, so `eval τ` gives `τ.getD j 0`. -/
def coinVariable (d j : ℕ) : MvPolynomial (Fin d) E := if h : j < d then X ⟨j, h⟩ else 0

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem eval_coinVariable (d j : ℕ) (τ : Fin d → E) :
    eval τ (coinVariable d j) = (List.ofFn τ).getD j 0 := by
  unfold coinVariable
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- `coinProduct` with variables in place of the coins. -/
def coinProductPoly (d offset width a : ℕ) : MvPolynomial (Fin d) E :=
  ∏ b ∈ range width, if a.testBit b then coinVariable d (offset + b) else 1

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem eval_coinProductPoly (d offset width a : ℕ) (τ : Fin d → E) :
    eval τ (coinProductPoly d offset width a) = coinProduct (List.ofFn τ) offset width a := by
  simp [coinProductPoly, coinProduct, map_prod, apply_ite, eval_coinVariable]

/-- The exponent of `X_j` for `j < d`. -/
def coinExponent (d j : ℕ) : Fin d →₀ ℕ := if h : j < d then Finsupp.single ⟨j, h⟩ 1 else 0

/-- The exponent of `coinProductPoly`. -/
def coinProductExponent (d offset width a : ℕ) : Fin d →₀ ℕ :=
  ∑ b ∈ range width, if a.testBit b then coinExponent d (offset + b) else 0

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem coinProductPoly_eq_monomial (d offset width a : ℕ) (hd : offset + width ≤ d) :
    coinProductPoly (E := E) d offset width a = monomial (coinProductExponent d offset width a) 1 := by
  rw [coinProductExponent, monomial_sum_one]
  refine Finset.prod_congr rfl fun b hb => ?_
  have hb : offset + b < d := by simp at hb; omega
  split_ifs
  · simp [coinVariable, coinExponent, hb, X]
  · simp

theorem coinProductExponent_apply (d offset width a : ℕ) (i : Fin d) :
    coinProductExponent d offset width a i =
      if offset ≤ i.val ∧ i.val < offset + width ∧ a.testBit (i.val - offset) then 1 else 0 := by
  simp only [coinProductExponent, Finsupp.finsetSum_apply]
  have hterm : ∀ b, (if a.testBit b then coinExponent d (offset + b) else 0) i =
      if a.testBit b ∧ offset + b = i.val then 1 else 0 := by
    intro b
    by_cases hab : a.testBit b
    · by_cases hbi : offset + b = i.val
      · simp [coinExponent, hab, hbi, i.2]
      · simp only [coinExponent, hab, if_true, hbi, and_false, if_false]
        split_ifs with h
        · rw [Finsupp.single_apply, if_neg]; intro hc; exact hbi (by rw [← hc])
        · rfl
    · simp [hab]
  simp_rw [hterm]
  by_cases hmem : offset ≤ i.val ∧ i.val < offset + width
  · rw [Finset.sum_eq_single_of_mem (i.val - offset) (by simp; omega)]
    · by_cases hbit : a.testBit (i.val - offset) <;> simp [hbit, hmem]
    · intro b _ hb; rw [if_neg]; omega
  · rw [Finset.sum_eq_zero, if_neg (by tauto)]
    intro b hb; simp at hb; rw [if_neg]; omega

theorem coinProductExponent_injective (d : ℕ) {a a' : ℕ} (ha : a < 2 ^ d) (ha' : a' < 2 ^ d)
    (h : coinProductExponent d 0 d a = coinProductExponent d 0 d a') : a = a' := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < d
  · have := congrArg (· ⟨j, hj⟩) h
    simp only [coinProductExponent_apply, Nat.sub_zero, zero_le, zero_add, hj, true_and] at this
    cases hb : a.testBit j <;> cases hb' : a'.testBit j <;> simp_all
  · have hle : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hle), Nat.testBit_lt_two_pow (ha'.trans_le hle)]

/-- The de-linearization keeps a wrong tuple, except with probability `s / (|E| - 1) + (d - s) / |E|`
over its coins. The weight `τ^a` of word `a < 2^d` is multilinear in the `d` coins. The first `s`
coins are the slice coins, which are nonzero because the check aborts on a zero slice coin, and the
expansion draws the other coins from all of `E` (GS20, Lemma 8, with the multilinear weights of the
prototype and Schwartz and Zippel). -/
theorem gs20_lemma8_delinearization (s d : ℕ) (hs : s ≤ d) (δ : ℕ → E) (hδ : ∃ a < 2 ^ d, δ a ≠ 0) :
    ((univ.filter fun τ : (Fin s → {c : E // c ≠ 0}) × (Fin (d - s) → E) =>
        ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn (fun b => (τ.1 b).1) ++ List.ofFn τ.2) 0 d a * δ a = 0).card : ℝ) /
      ((Fintype.card E - 1 : ℝ) ^ s * (Fintype.card E : ℝ) ^ (d - s)) ≤
      s / (Fintype.card E - 1 : ℝ) + (d - s : ℕ) / (Fintype.card E : ℝ) := by
  classical
  set N := Fintype.card E
  have hN : 1 < N := Fintype.one_lt_card
  let e := fun a => coinProductExponent d 0 d a
  let P : MvPolynomial (Fin d) E := ∑ a ∈ range (2 ^ d), monomial (e a) (δ a)
  have heval : ∀ x : Fin d → E,
      eval x P = ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn x) 0 d a * δ a := by
    intro x
    simp only [P, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← eval_coinProductPoly, coinProductPoly_eq_monomial _ _ _ _ (by omega)]
    simp [e, eval_monomial, mul_comm]
  have hnonzero : P ≠ 0 := by
    obtain ⟨a₀, ha₀, hne⟩ := hδ
    intro hP
    have h := congrArg (coeff (e a₀)) hP
    simp only [P, coeff_sum, coeff_monomial, coeff_zero] at h
    rw [Finset.sum_eq_single_of_mem a₀ (by simpa using ha₀), if_pos rfl] at h
    · exact hne h
    · intro a ha hne'
      rw [if_neg fun heq => hne' (coinProductExponent_injective d (by simpa using ha) ha₀ heq)]
  have hdegree : ∀ i, P.degreeOf i ≤ 1 := by
    intro i
    rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp (support_sum hm)
    rw [Finset.mem_singleton.mp (support_monomial_subset ha), coinProductExponent_apply]
    split_ifs <;> omega
  let S : Fin d → Finset E := fun i => if i.val < s then univ.erase 0 else univ
  let Φ : (Fin s → {c : E // c ≠ 0}) × (Fin (d - s) → E) → Fin d → E := fun τ i =>
    if h : i.val < s then (τ.1 ⟨i, h⟩).1 else τ.2 ⟨i.val - s, by omega⟩
  have hlist : ∀ τ, List.ofFn (Φ τ) = List.ofFn (fun b => (τ.1 b).1) ++ List.ofFn τ.2 := by
    intro τ
    refine List.ext_getElem (by simp; omega) fun j h1 h2 => ?_
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, Φ]
  have hcard : (univ.filter fun τ : (Fin s → {c : E // c ≠ 0}) × (Fin (d - s) → E) =>
      ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn (fun b => (τ.1 b).1) ++ List.ofFn τ.2) 0 d a * δ a = 0).card =
      #{x ∈ Fintype.piFinset S | eval x P = 0} := by
    refine Finset.card_bij (fun τ _ => Φ τ) ?_ ?_ ?_
    · intro τ hτ
      simp only [mem_filter, mem_univ, true_and] at hτ
      simp only [mem_filter, Fintype.mem_piFinset, heval, hlist, hτ, and_true]
      intro i
      simp only [S, Φ]
      split_ifs with h
      · simpa using (τ.1 ⟨i, h⟩).2
      · simp
    · intro τ _ τ' _ h
      ext b
      · simpa [Φ] using congrFun h ⟨b, by omega⟩
      · have := congrFun h ⟨s + b, by omega⟩
        simpa [Φ] using this
    · intro x hx
      simp only [mem_filter, Fintype.mem_piFinset] at hx
      refine ⟨(fun b => ⟨x ⟨b, by omega⟩, ?_⟩, fun b => x ⟨s + b, by omega⟩), ?_, ?_⟩
      · have := hx.1 ⟨b, by omega⟩
        simpa [S, b.2] using this
      · simp only [mem_filter, mem_univ, true_and, ← hlist, ← heval]
        convert hx.2
        funext i
        simp only [Φ]
        split_ifs with h
        · rfl
        · congr 1; ext; simp; omega
      · funext i
        simp only [Φ]
        split_ifs with h
        · rfl
        · congr 1; ext; simp; omega
  have hS : ∀ i, (#(S i) : ℚ≥0) = if i.val < s then ((N - 1 : ℕ) : ℚ≥0) else (N : ℚ≥0) := by
    intro i
    simp only [S]
    split_ifs
    · rw [card_erase_of_mem (mem_univ _), card_univ]
    · rw [card_univ]
  have hsz := schwartz_zippel_sum_degreeOf hnonzero S
  have hprod : ∏ i, (#(S i) : ℚ≥0) = ((N - 1 : ℕ) : ℚ≥0) ^ s * (N : ℚ≥0) ^ (d - s) := by
    simp_rw [hS]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < s then ((N - 1 : ℕ) : ℚ≥0) else (N : ℚ≥0)) d,
      show d = s + (d - s) by omega, Finset.prod_range_add]
    rw [Finset.prod_congr rfl (fun i hi => if_pos (mem_range.mp hi)),
      Finset.prod_congr rfl (fun i _ => if_neg (by omega))]
    simp
  have hsum : ∑ i, (P.degreeOf i / #(S i) : ℚ≥0) ≤
      (s : ℚ≥0) / ((N - 1 : ℕ) : ℚ≥0) + ((d - s : ℕ) : ℚ≥0) / (N : ℚ≥0) := by
    calc ∑ i, (P.degreeOf i / #(S i) : ℚ≥0) ≤ ∑ i, (1 / #(S i) : ℚ≥0) := by
          gcongr with i; exact_mod_cast hdegree i
      _ = _ := by
          simp_rw [hS]
          rw [Fin.sum_univ_eq_sum_range (fun i => 1 / if i < s then ((N - 1 : ℕ) : ℚ≥0) else (N : ℚ≥0)) d,
            show d = s + (d - s) by omega, Finset.sum_range_add]
          have h1 : ∑ i ∈ range s, (1 / if i < s then ((N - 1 : ℕ) : ℚ≥0) else (N : ℚ≥0)) =
              ∑ _i ∈ range s, 1 / ((N - 1 : ℕ) : ℚ≥0) :=
            Finset.sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
          have h2 : ∑ i ∈ range (d - s), (1 / if s + i < s then ((N - 1 : ℕ) : ℚ≥0) else (N : ℚ≥0)) =
              ∑ _i ∈ range (d - s), 1 / (N : ℚ≥0) :=
            Finset.sum_congr rfl fun i _ => by rw [if_neg (by omega)]
          rw [h1, h2]
          simp [div_eq_mul_inv]
  rw [hprod] at hsz
  have hfinal := NNRat.cast_le (K := ℝ) |>.mpr (hsz.trans hsum)
  rw [hcard]
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN.le, Nat.cast_one]
  simp only [NNRat.cast_div, NNRat.cast_add, NNRat.cast_mul, NNRat.cast_pow, NNRat.cast_natCast] at hfinal
  rw [hN1] at hfinal
  exact hfinal

end Weights

/-! ## Signing -/

/-- A uniform guess of the `t - 1` corrupt operators is right with probability `1 / C(n, t - 1)`,
independently of the game. This is the second fact of the proof of PRAWNS, Lemma 5.2, and not the
full lemma. -/
theorem prawns_lemma52_guess (game : ProbComp (Bool × C.Term)) [Nonempty C.Term] :
    letI := SampleableType.ofFintype C.Term
    Pr[fun r => r.1.1 = true ∧ r.2 = r.1.2 | do let g ← game; let T ← $ᵗ C.Term; pure (g, T)] *
        (C.n.choose (C.t - 1) : ℝ≥0∞) = Pr[fun g => g.1 = true | game] := by
  letI := SampleableType.ofFintype C.Term
  have hcard : (Fintype.card C.Term : ℝ≥0∞) = C.n.choose (C.t - 1) := by
    simp [Committee.Term, Fintype.card_finset_len]
  have hpos : (C.n.choose (C.t - 1) : ℝ≥0∞) ≠ 0 := by
    rw [← hcard]; exact_mod_cast Fintype.card_ne_zero
  have hguess : ∀ g : Bool × C.Term,
      Pr[fun r => r.1.1 = true ∧ r.2 = r.1.2 | (fun T => (g, T)) <$> ($ᵗ C.Term)] *
        (C.n.choose (C.t - 1) : ℝ≥0∞) = if g.1 = true then 1 else 0 := by
    intro g
    rw [probEvent_map]
    by_cases hg : g.1 = true
    · simp only [Function.comp_def, hg, true_and, if_true]
      rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, hcard]
      exact ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _)
    · simp [Function.comp_def, hg]
  simp only [bind_pure_comp]
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right, probEvent_eq_tsum_ite]
  refine tsum_congr fun g => ?_
  rw [mul_assoc, hguess]
  split_ifs <;> simp

/-- A codeword covers another only if they are equal, since all codewords have the same digit sum
(PRAWNS, Definition 3.1, for the codewords of leanXMSS). -/
theorem prawns_cover_free (d d' : Digest) (hd : Codeword.Valid d) (hd' : Codeword.Valid d')
    (hcover : ∀ l, Codeword.encoding d l ≤ Codeword.encoding d' l) :
    Codeword.encoding d = Codeword.encoding d' := by
  have hsum : ∑ l, (Codeword.encoding d l).val = ∑ l, (Codeword.encoding d' l).val := by
    have h1 := hd.2
    have h2 := hd'.2
    simp only [Codeword.sum] at h1 h2
    rw [h1, h2]
  have hle : ∀ l ∈ Finset.univ, (Codeword.encoding d l).val ≤ (Codeword.encoding d' l).val :=
    fun l _ => hcover l
  funext l
  exact Fin.ext ((Finset.sum_eq_sum_iff_of_le hle).mp hsum l (Finset.mem_univ l))

end ThresholdLeanXmssSecurity
