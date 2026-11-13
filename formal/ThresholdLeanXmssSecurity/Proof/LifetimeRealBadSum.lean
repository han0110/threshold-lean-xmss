import ThresholdLeanXmssSecurity.Proof.LifetimeRunEstimates
import ThresholdLeanXmssSecurity.Proof.LifetimeIdealEarlyCache
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The real stream-key allowance of each lifetime run

The separation and hit counts fit the real share under the original lifetime
budget. Combining the real and ideal shares gives the chronological PRF transport.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeRealBadSum

open LifetimePrfTransportProof LifetimeRunEstimates

variable {C : Committee}

/-- The reveal-pair count in terms of the committee and PRSS-key counts. -/
theorem revealPairs_eq : revealPairs C = prssKeyCount C * C.n * (termCount C + C.n) := by
  simp only [revealPairs, Fintype.card_prod, Committee.Party, Fintype.card_fin,
    keygenFinish_card_term, keygenFinish_card_pair, prssKeyCount, termCount]
  ring

/-- The complete real-boundary numerator fits the allocated real share. -/
theorem runCost_le (attempts Q F q : ℕ) (h : keySplit C q < 2) (hattempts : 1 ≤ attempts) :
    runCost C Q ≤ realShare C attempts Q F := by
  have hB0 := bottomTreeCalls_eq (C := C)
  have hO0 := runs_le_lifetimeOverhead (C := C) attempts Q
  have hna : C.n ≤ termCount C := n_le_termCount
  have ham : termCount C ≤ prssKeyCount C := by unfold prssKeyCount; omega
  have hn : C.n ≤ 255 := n_le_of_keySplit q h
  have hR : 1 ≤ lifetimeRuns attempts := by
    unfold lifetimeRuns
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))
  rw [runCost, revealPairs_eq, realShare]
  set n := C.n
  set a := termCount C
  set m := prssKeyCount C
  set B := bottomTreeCalls C
  set O := lifetimeOverhead C attempts Q
  have hB : 510 * a ≤ B := by omega
  have h6n : 6 * n ≤ B := by omega
  have hO : n * B ≤ O := by
    calc n * B ≤ (lifetimeRuns attempts * (n + 1)) * B := by
           gcongr
           calc n ≤ n + 1 := by omega
                _ = 1 * (n + 1) := by simp
                _ ≤ lifetimeRuns attempts * (n + 1) := Nat.mul_le_mul_right _ hR
         _ ≤ O := hO0
  clear_value n a m B O
  -- The U1 and U2 bounds are the arithmetic steps of designCounts_le.
  have hU1 : n ^ 2 * a ^ 2 + n ^ 4 ≤ n * B * m := by
    have e1 : n ^ 4 ≤ n ^ 2 * a ^ 2 := by
      calc n ^ 4 = n ^ 2 * n ^ 2 := by ring
           _ ≤ n ^ 2 * a ^ 2 := by gcongr
    have e2 : 2 * (n ^ 2 * a ^ 2) ≤ n * B * m := by
      calc 2 * (n ^ 2 * a ^ 2) = n * (2 * n * a) * a := by ring
           _ ≤ n * (510 * a) * m := by gcongr; omega
           _ ≤ n * B * m := by gcongr
    omega
  have hU2 : m * n * (a + n) ≤ n * B * m := by
    calc m * n * (a + n) ≤ m * n * (2 * a) := by gcongr; omega
         _ = n * (2 * a) * m := by ring
         _ ≤ n * B * m := by gcongr; omega
  have hU0 : 6 * n ^ 2 * m ≤ n * B * m := by
    calc 6 * n ^ 2 * m = n * (6 * n) * m := by ring
         _ ≤ n * B * m := by gcongr
  have hX : 3 * (n * B * m) ≤ 3 * O * m := by
    calc 3 * (n * B * m) = 3 * (n * B) * m := by ring
         _ ≤ 3 * O * m := by gcongr
  have hF : 6 * Q * m ≤ 4 * (F + 2) * Q * m := by gcongr; omega
  nlinarith [Nat.zero_le (n ^ 2 * m)]

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- Each actual reduction's bad event fits the original real-side allocation. -/
theorem realBadBound (Q : ℕ) : RealBadBound K settings attempts aes circuitsOf D A Q := by
  intro hQ hsplit n values
  have hattempts : 1 ≤ attempts := by
    by_contra h
    have hz : attempts = 0 := by omega
    have hn := n.isLt
    simp [hz, lifetimeRuns] at hn
  refine (reduction_bad_le K settings attempts D n A circuitsOf aes Q hQ values).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast runCost_le attempts Q (ceremonyFuel (circuitsOf fun _ => 0) settings) _ hsplit hattempts

/-- The checked real and ideal estimates give the small-split chronological transport. -/
theorem lifetimePrfTransportSmallSplit (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q) :
    LifetimeAllowance.LifetimePrfTransportSmallSplit K settings attempts aes circuitsOf D A Q :=
  smallSplit_of_bounds K settings attempts aes circuitsOf D A Q hQ
    (realBadBound K settings attempts aes circuitsOf D A Q)
    (LifetimeIdealEarlyCache.idealBadBound K settings attempts D A aes circuitsOf Q)

/-- The chronological PRF transport with the original lifetime query budget. -/
theorem lifetimePrfTransport (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q) :
    LifetimeAllowance.LifetimePrfTransport K settings attempts aes circuitsOf D A Q :=
  LifetimeAllowance.lifetimePrfTransport_of_smallSplit K settings attempts aes circuitsOf D A Q
    (lifetimePrfTransportSmallSplit K settings attempts aes circuitsOf D A Q hQ)

end ThresholdLeanXmssSecurity.LifetimeRealBadSum

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBadSum.revealPairs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRealBadSum.revealPairs_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBadSum.runCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRealBadSum.runCost_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBadSum.realBadBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRealBadSum.realBadBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBadSum.lifetimePrfTransportSmallSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRealBadSum.lifetimePrfTransportSmallSplit

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBadSum.lifetimePrfTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeRealBadSum.lifetimePrfTransport
