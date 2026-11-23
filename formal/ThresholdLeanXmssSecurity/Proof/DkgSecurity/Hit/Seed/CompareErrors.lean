import ThresholdLeanXmss.Statement.Theorems

/-!
# The two errors of the comparison game

`compCloseError C q` is the error of the step from the game with the keys of the dealer to the
comparison game. It counts the counted calls that name the derive input of a hidden term, `q` tests
of `termCount C` vectors of `t` parts, and the aliases of a hidden derive input against another
hidden input, a programming input or a derivation of a known term at one of the `n` operators.

`compHitError C q` is the error of the hit in the comparison game. It counts the counted calls that
name the independent seed of a hidden term, and the comparison of the echo hashes of each pair of
honest holders.

`errors_le` states that the two errors fit in `hitSeedError C q` for `q ≥ 1` when that bound is below
one. The case `t = 1` has one operator, one hidden term and no known term. For `t ≥ 2` the middle
binomial `termCount C` is at least `n`.
-/

set_option autoImplicit false

open ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- The error of the step to the comparison game. -/
def compCloseError (C : Committee) (q : ℕ) : ℝ :=
  ((q * termCount C + (C.n + 2) * termCount C * (termCount C - 1) : ℕ) : ℝ) / 2 ^ (256 * C.t)

/-- The error of the hit in the comparison game. -/
def compHitError (C : Committee) (q : ℕ) : ℝ := ((q * termCount C + C.n.choose 2 * (q + 1) : ℕ) : ℝ) / 2 ^ 256

theorem n_le_termCount (C : Committee) (ht : 2 ≤ C.t) : C.n ≤ termCount C := by
  have h : C.n / 2 = C.t - 1 := by
    unfold Committee.n
    omega
  unfold termCount
  rw [← h]
  have := Nat.choose_le_middle 1 C.n
  rwa [Nat.choose_one_right] at this

private theorem close_numerator_le {q n m B : ℕ} (hq : 1 ≤ q) (hn : 3 ≤ n) (hnm : n ≤ m)
    (hB : 2 * q * (n * m) ≤ B) :
    q * m + (n + 2) * m * (m - 1) ≤ q * n * m * B := by
  have hqm : q * m ≤ q * n * m := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hnmq : n * m ≤ q * n * m := by
    simpa only [Nat.mul_assoc, Nat.one_mul] using Nat.mul_le_mul_right (n * m) hq
  have hpos : 0 < q * n * m := Nat.mul_pos (Nat.mul_pos hq (by omega)) (by omega)
  have hfirst := hqm.trans (Nat.le_mul_of_pos_right (q * n * m) hpos)
  have hn2 : n + 2 ≤ n * n := by
    have := Nat.mul_le_mul_left n hn
    omega
  have hsecond : (n + 2) * m * (m - 1) ≤ q * n * m * (q * n * m) := calc
    _ ≤ (n * n) * m * m := Nat.mul_le_mul (Nat.mul_le_mul_right _ hn2) (Nat.sub_le _ _)
    _ = (n * m) * (n * m) := by ring
    _ ≤ _ := Nat.mul_le_mul hnmq hnmq
  calc
    _ ≤ q * n * m * (q * n * m) + q * n * m * (q * n * m) := add_le_add hfirst hsecond
    _ = q * n * m * (2 * q * (n * m)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hB

private theorem hit_numerator_le {q n m : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (hnm : n ≤ m) :
    q * m + n.choose 2 * (q + 1) ≤ q * n * m := by
  have hpair : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hpairs : n.choose 2 * (q + 1) ≤ m * (n - 1) * q := calc
    _ ≤ n.choose 2 * (2 * q) := Nat.mul_le_mul_left _ (by omega)
    _ = (2 * n.choose 2) * q := by ring
    _ ≤ _ := by rw [hpair]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hnm)
  calc
    _ ≤ q * m + m * (n - 1) * q := Nat.add_le_add_left hpairs _
    _ = q * ((n - 1) + 1) * m := by ring
    _ = _ := by rw [Nat.sub_add_cancel hn]

-- Keep elaboration of the hash-space bound from reducing real comparison on powers of two.
attribute [local irreducible] Real.instLT in
theorem errors_le (C : Committee) (q : ℕ) (hq : 1 ≤ q)
    (hsmall : ((2 * q * (C.n * termCount C) : ℕ) : ℝ) / 2 ^ 256 < 1) :
    compCloseError C q + compHitError C q ≤ ((2 * q * (C.n * termCount C) : ℕ) : ℝ) / 2 ^ 256 := by
  rcases Nat.lt_or_ge C.t 2 with ht | ht
  · have ht1 : C.t = 1 := by have := C.one_le_t; omega
    have hn : C.n = 1 := by unfold Committee.n; omega
    have hm : termCount C = 1 := by unfold termCount; rw [hn, ht1]; rfl
    unfold compCloseError compHitError
    rw [hm, hn, ht1]
    simp only [mul_one, Nat.sub_self, mul_zero, add_zero, Nat.choose_succ_self, zero_mul]
    rw [← add_div]
    push_cast
    ring_nf
    exact le_rfl
  · set m := termCount C with hm
    set n := C.n with hn
    have hnm : n ≤ m := n_le_termCount C ht
    have hn3 : 3 ≤ n := by rw [hn]; unfold Committee.n; omega
    have hM : (0 : ℝ) < 2 ^ 256 := by positivity
    have hB : 2 * q * (n * m) ≤ 2 ^ 256 := by
      rw [div_lt_one hM] at hsmall
      exact_mod_cast hsmall.le
    have hclose_nat := close_numerator_le hq hn3 hnm hB
    have hclose : compCloseError C q ≤ ((q * n * m : ℕ) : ℝ) / 2 ^ 256 := by
      unfold compCloseError
      rw [← hm, ← hn]
      have hpow : (2 : ℝ) ^ 512 ≤ 2 ^ (256 * C.t) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc ((q * m + (n + 2) * m * (m - 1) : ℕ) : ℝ) / 2 ^ (256 * C.t)
          ≤ ((q * m + (n + 2) * m * (m - 1) : ℕ) : ℝ) / 2 ^ 512 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ ≤ ((q * n * m * 2 ^ 256 : ℕ) : ℝ) / 2 ^ 512 := by
            exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hclose_nat) (by positivity)
        _ = ((q * n * m : ℕ) : ℝ) / 2 ^ 256 := by
            push_cast
            field_simp
            ring
    -- the hit error is at most `q n m / 2^256`
    have hhit_nat := hit_numerator_le hq (by omega : 1 ≤ n) hnm
    have hhit : compHitError C q ≤ ((q * n * m : ℕ) : ℝ) / 2 ^ 256 := by
      unfold compHitError
      rw [← hm, ← hn]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hhit_nat) hM.le
    calc compCloseError C q + compHitError C q ≤ ((q * n * m : ℕ) : ℝ) / 2 ^ 256 + ((q * n * m : ℕ) : ℝ) / 2 ^ 256 :=
          add_le_add hclose hhit
      _ = ((2 * q * (n * m) : ℕ) : ℝ) / 2 ^ 256 := by
          push_cast
          ring

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.errors_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.errors_le
