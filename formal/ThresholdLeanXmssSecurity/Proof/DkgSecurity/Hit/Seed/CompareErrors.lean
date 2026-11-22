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
    have hsmall' : 2 * q * (n * m) < 2 ^ 256 := by
      have h := (div_lt_one hM).1 hsmall
      exact_mod_cast h
    -- the close error is at most `q n m / 2^256`
    have hclose_nat : q * m + (n + 2) * m * (m - 1) ≤ q * n * m * 2 ^ 256 := by
      have h1 : q * m + (n + 2) * m * (m - 1) ≤ 2 * (q * n * m) * (q * n * m) := by
        have hm1 : 1 ≤ m := le_trans (by omega) hnm
        have hqm : q * m ≤ q * n * m * (q * n * m) := by
          have : 1 ≤ q * n * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
          calc q * m ≤ q * n * m := by
                have := Nat.mul_le_mul_right m (Nat.le_mul_of_pos_right q (by omega : 0 < n))
                simpa [Nat.mul_assoc] using this
            _ ≤ q * n * m * (q * n * m) := Nat.le_mul_of_pos_right _ this
        have hsq : (n + 2) * m * (m - 1) ≤ q * n * m * (q * n * m) := by
          have h2 : (n + 2) * m * (m - 1) ≤ (n * n) * (m * m) := by
            have : m - 1 ≤ m := Nat.sub_le m 1
            have hn2 : n + 2 ≤ n * n := by nlinarith
            calc (n + 2) * m * (m - 1) ≤ (n + 2) * m * m := Nat.mul_le_mul_left _ this
              _ ≤ (n * n) * m * m := by gcongr
              _ = (n * n) * (m * m) := by ring
          have h3 : (n * n) * (m * m) ≤ q * n * m * (q * n * m) := by
            have : (n * n) * (m * m) = (n * m) * (n * m) := by ring
            rw [this]
            have hq' : n * m ≤ q * n * m := by
              have := Nat.mul_le_mul_right (n * m) hq
              simpa [Nat.mul_assoc] using this
            exact Nat.mul_le_mul hq' hq'
          exact h2.trans h3
        calc q * m + (n + 2) * m * (m - 1) ≤ q * n * m * (q * n * m) + q * n * m * (q * n * m) :=
              add_le_add hqm hsq
          _ = 2 * (q * n * m) * (q * n * m) := by ring
      have h2 : 2 * (q * n * m) * (q * n * m) ≤ q * n * m * 2 ^ 256 := by
        have : 2 * (q * n * m) ≤ 2 ^ 256 := by
          have : 2 * q * (n * m) = 2 * (q * n * m) := by ring
          omega
        calc 2 * (q * n * m) * (q * n * m) = (q * n * m) * (2 * (q * n * m)) := by ring
          _ ≤ q * n * m * 2 ^ 256 := Nat.mul_le_mul_left _ this
      exact h1.trans h2
    have hclose : compCloseError C q ≤ ((q * n * m : ℕ) : ℝ) / 2 ^ 256 := by
      unfold compCloseError
      rw [← hm, ← hn]
      have hpow : (2 : ℝ) ^ 512 ≤ 2 ^ (256 * C.t) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc ((q * m + (n + 2) * m * (m - 1) : ℕ) : ℝ) / 2 ^ (256 * C.t)
          ≤ ((q * m + (n + 2) * m * (m - 1) : ℕ) : ℝ) / 2 ^ 512 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ ≤ ((q * n * m * 2 ^ 256 : ℕ) : ℝ) / 2 ^ 512 := by
            gcongr
        _ = ((q * n * m : ℕ) : ℝ) / 2 ^ 256 := by
            push_cast
            field_simp
            ring
    -- the hit error is at most `q n m / 2^256`
    have hhit_nat : q * m + n.choose 2 * (q + 1) ≤ q * n * m := by
      have h2 : 2 * n.choose 2 = n * (n - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
      have h3 : n.choose 2 * (q + 1) ≤ n * (n - 1) * q := by
        have : n.choose 2 * (q + 1) ≤ n.choose 2 * (2 * q) := Nat.mul_le_mul_left _ (by omega)
        calc n.choose 2 * (q + 1) ≤ n.choose 2 * (2 * q) := this
          _ = 2 * n.choose 2 * q := by ring
          _ = n * (n - 1) * q := by rw [h2]
      have h4 : n * (n - 1) * q ≤ m * (n - 1) * q := by gcongr
      have h5 : q * m + m * (n - 1) * q = q * n * m := by
        have e : q * n * m = q * ((n - 1) + 1) * m := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
        rw [e]
        ring
      omega
    have hhit : compHitError C q ≤ ((q * n * m : ℕ) : ℝ) / 2 ^ 256 := by
      unfold compHitError
      rw [← hm, ← hn]
      gcongr
    calc compCloseError C q + compHitError C q ≤ ((q * n * m : ℕ) : ℝ) / 2 ^ 256 + ((q * n * m : ℕ) : ℝ) / 2 ^ 256 :=
          add_le_add hclose hhit
      _ = ((2 * q * (n * m) : ℕ) : ℝ) / 2 ^ 256 := by
          push_cast
          ring

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.errors_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.errors_le
