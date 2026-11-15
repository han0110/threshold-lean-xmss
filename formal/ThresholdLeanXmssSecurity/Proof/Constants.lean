import ThresholdLeanXmss.Scheme
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Public constants for every committee

`constants_nonempty_of` states that `Constants` has a value over `GF(2^128)` for each committee
with fewer than `2 ^ 128` operators. It does not state that the constants of the implementation are
such a value.

Its only project import is `Scheme.lean`.
-/

set_option autoImplicit false

open ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

/-- A basis of `GF(2^128)` over `F_2`. -/
private def galoisBasis : Module.Basis (Fin elementBits) Bit (GaloisField 2 elementBits) :=
  Module.finBasisOfFinrankEq Bit (GaloisField 2 elementBits) (GaloisField.finrank 2 (by decide))

local instance (C : Committee) : NeZero C.n := ⟨by have := C.one_le_t; unfold Committee.n; omega⟩

open Fin.CommRing in
/-- `x ↦ c • x` is injective on `Fin n` when `2 c + 1 = n`, because `-2` is the inverse of `c`. -/
private theorem nsmul_injective_of_two_mul_add_one {n c : ℕ} [NeZero n] (hc : 2 * c + 1 = n) :
    Function.Injective fun x : Fin n => c • x := by
  intro i j h
  have h' : (c : Fin n) * i = c * j := by simpa only [nsmul_eq_mul] using h
  have h2 : 2 * (c : Fin n) + 1 = 0 := by
    have : ((2 * c + 1 : ℕ) : Fin n) = 0 := by rw [hc]; exact Fin.natCast_self n
    exact_mod_cast this
  linear_combination (-2 : Fin n) * h' + (i - j) * h2

/-- `Constants` has a value for every committee with fewer than `2 ^ 128` operators. -/
theorem constants_nonempty_of (C : Committee) (h : C.n < 2 ^ elementBits) :
    Nonempty (Constants C (GaloisField 2 elementBits)) := by
  classical
  have hn : C.n = 2 * C.t - 1 := rfl
  have ht := C.one_le_t
  -- The points are distinct units of the field.
  let _ := Fintype.ofFinite (GaloisField 2 elementBits)
  obtain ⟨point⟩ : Nonempty (C.Party ↪ (GaloisField 2 elementBits)ˣ) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_units,
      GaloisField.card 2 elementBits (by decide), Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.le_sub_one_of_lt h
  -- Two terms cover at most `2 (t - 1) < n` operators, so one operator holds both.
  have outside : ∀ A B : C.Term, (A.1 ∪ B.1)ᶜ.Nonempty := by
    intro A B
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_union_le A.1 B.1
    rw [A.2, B.2] at this
    omega
  choose chosen hchosen using outside
  have chosen_held : ∀ A B, chosen A B ∈ C.holders A ∧ chosen A B ∈ C.holders B := by
    intro A B
    have := hchosen A B
    simp only [Finset.mem_compl, Finset.mem_union, not_or] at this
    exact ⟨Finset.mem_compl.mpr this.1, Finset.mem_compl.mpr this.2⟩
  -- Operator `i` fills the translate `S₀ + i` of one term `S₀` that does not contain `0`.
  obtain ⟨S₀, hS₀, hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ.erase (0 : C.Party))
    (n := C.t - 1) (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]; omega)
  have zero_not_mem : (0 : C.Party) ∉ S₀ := fun h0 => by simpa using hS₀ h0
  let shift (i : C.Party) : C.Term :=
    ⟨S₀.map (addRightEmbedding i), by rw [Finset.card_map, hcard]⟩
  have shift_held : ∀ i, i ∈ C.holders (shift i) := by
    intro i
    simp only [Committee.holders, shift, Finset.mem_compl, Finset.mem_map, addRightEmbedding_apply,
      not_exists, not_and]
    intro x hx hxi
    have : x = 0 := by simpa using hxi
    exact zero_not_mem (this ▸ hx)
  -- The sum of `S₀ + i` is `∑ S₀ + (t - 1) • i`, and `t - 1` is a unit of `Fin n`.
  have shift_sum : ∀ i, ∑ x ∈ (shift i).1, x = ∑ x ∈ S₀, x + (C.t - 1) • i := by
    intro i
    simp only [shift, Finset.sum_map, addRightEmbedding_apply, Finset.sum_add_distrib,
      Finset.sum_const, hcard]
  have shift_injective : Function.Injective shift := by
    intro i j hij
    have := shift_sum i
    rw [hij, shift_sum j] at this
    exact (nsmul_injective_of_two_mul_add_one (n := C.n) (c := C.t - 1) (by omega)
      (add_left_cancel this)).symm
  exact ⟨{
    point := point.trans ⟨Units.val, Units.val_injective⟩
    point_ne_zero := fun i => (point i).ne_zero
    pairs := fun i => Finset.univ.filter fun AB => chosen AB.1 AB.2 = i
    pairs_unique := fun AB =>
      ⟨chosen AB.1 AB.2, by simp, fun j hj => (Finset.mem_filter.mp hj).2.symm⟩
    pairs_held := fun i AB hAB => by
      obtain rfl : chosen AB.1 AB.2 = i := (Finset.mem_filter.mp hAB).2
      exact chosen_held AB.1 AB.2
    filled := ⟨shift, shift_injective⟩
    filled_held := shift_held
    collector := fun _ => (shift 0, 0)
    collector_held := fun _ => shift_held 0
    owner := fun T => chosen T T
    owner_held := fun T => (chosen_held T T).1
    publicTerm := shift 0
    weight := fun q => galoisBasis (Fin.castLE (by decide) q)
    weight_independent := galoisBasis.linearIndependent.comp _ (Fin.castLE_injective (by decide))
    encode := galoisBasis.equivFun.toEquiv }⟩

end ThresholdLeanXmssSecurity
