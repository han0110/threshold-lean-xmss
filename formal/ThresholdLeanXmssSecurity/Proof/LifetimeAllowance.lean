import ThresholdLeanXmssSecurity.Proof.LifetimeHybridOrder
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# Lifetime allowance with the stream-key error in the slot pass

This module gives a second split of the error of `LifetimeSecurityStatementSampled`. It uses the
worlds, the reductions and `LifetimeKeygenHop` of `LifetimeHybridOrder` without change.

* `LifetimePrfTransport` bounds the two transports of each chronological PRF hop by
  `keySplit (q₀ + q)` only.
* `LifetimeAfterKeygen` bounds the dealer-keygen world. Each slot term has one more
  `streamKeyError`. This term pays the move from the shared stream table of the dealer world
  to the separate table of each slot.
* `lifetimeSecurity_of_sources` gives the original statement from these two Props and
  `LifetimeKeygenHop`.
* `LifetimePrfTransportSmallSplit` is the transport with the added hypothesis
  `keySplit (q₀ + q) < 2`. If `2 ≤ keySplit (q₀ + q)`, the transport holds because each side
  is a difference of two probabilities. `lifetimePrfTransport_of_smallSplit` gives the full
  transport from it.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeAllowance

open LifetimeJointLink

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The shared-table and separate-table transports of each PRF hop fit in `keySplit`. -/
def LifetimePrfTransport (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  ∀ n : Fin (lifetimeRuns attempts),
    |LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n -
      LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A true n| +
    |LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A false n -
      LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A
        (n + 1)| ≤
      keySplit C (q₀ + q)

/-- The transport of `LifetimePrfTransport` when `keySplit (q₀ + q) < 2`. -/
def LifetimePrfTransportSmallSplit (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  keySplit C (q₀ + q) < 2 →
  ∀ n : Fin (lifetimeRuns attempts),
    |LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n -
      LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A true n| +
    |LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A false n -
      LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A
        (n + 1)| ≤
      keySplit C (q₀ + q)

theorem toReal_le_one {x : ℝ≥0∞} (h : x ≤ 1) : x.toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h

theorem chronologicalProbability_mem (n : ℕ) :
    0 ≤ LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n ∧
      LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, by
    unfold LifetimeHybridOrder.chronologicalProbability
    exact toReal_le_one probEvent_le_one⟩

theorem reductionProbability_mem (real : Bool) (n : ℕ) :
    0 ≤ LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A real n ∧
      LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A real n ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, by
    unfold LifetimeHybridOrder.reductionProbability
    exact toReal_le_one probOutput_le_one⟩

/-- If `2 ≤ keySplit (q₀ + q)`, the transport holds, so the case `keySplit (q₀ + q) < 2` is
sufficient. -/
theorem lifetimePrfTransport_of_smallSplit (Q : ℕ)
    (h : LifetimePrfTransportSmallSplit K settings attempts aes circuitsOf D A Q) :
    LifetimePrfTransport K settings attempts aes circuitsOf D A Q := by
  intro n
  by_cases hsplit : keySplit C (Q + lifetimeOverhead C attempts Q +
      (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q) < 2
  · exact h hsplit n
  · have h0 := chronologicalProbability_mem K settings attempts aes circuitsOf D A n
    have h1 := chronologicalProbability_mem K settings attempts aes circuitsOf D A (n + 1)
    have ht := reductionProbability_mem K settings attempts aes circuitsOf D A true n
    have hf := reductionProbability_mem K settings attempts aes circuitsOf D A false n
    have ha : |LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n -
        LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A true n| ≤
        1 := abs_sub_le_iff.2 ⟨by linarith [h0.2, ht.1], by linarith [h0.1, ht.2]⟩
    have hb : |LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A
        false n - LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf
          D A (n + 1)| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hf.2, h1.1], by linarith [hf.1, h1.2]⟩
    exact (add_le_add ha hb).trans (by linarith [not_lt.1 hsplit])

/-- One chronological PRF hop with only `keySplit` as the transport error. -/
def LifetimePrfHop (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  ∀ n : Fin (lifetimeRuns attempts),
    |LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n -
      LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A
        (n + 1)| ≤
      PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) + keySplit C (q₀ + q)

theorem lifetimePrfHop_of_transport (Q : ℕ)
    (h : LifetimePrfTransport K settings attempts aes circuitsOf D A Q) :
    LifetimePrfHop K settings attempts aes circuitsOf D A Q := by
  intro n
  have ht := h n
  have hreal := abs_sub_le
    (LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n)
    (LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A true n)
    (LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A false n)
  have hideal := abs_sub_le
    (LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A n)
    (LifetimeHybridOrder.reductionProbability K settings attempts aes circuitsOf D A false n)
    (LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A (n + 1))
  rw [LifetimeHybridOrder.reductionProbability_gap] at hreal
  linarith

/-- The entire PRF pass in time order, with one `keySplit` for each run. -/
theorem lifetimePrfPass (Q : ℕ)
    (h : LifetimePrfHop K settings attempts aes circuitsOf D A Q) :
    |lifetimeAdvantageSampled K settings attempts aes circuitsOf D A -
      LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A
        (lifetimeRuns attempts)| ≤
      (∑ n : Fin (lifetimeRuns attempts), PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)) +
      (lifetimeRuns attempts : ℝ) * keySplit C (Q + lifetimeOverhead C attempts Q +
        (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q) := by
  let e : ℕ → ℝ := fun n => PRFScheme.prfAdvantage (hiddenStreams aes)
    (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) +
    keySplit C (Q + lifetimeOverhead C attempts Q +
      (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)
  have ht := abs_sub_le_sum_of_hybrid
    (LifetimeHybridOrder.chronologicalProbability K settings attempts aes circuitsOf D A)
    (lifetimeRuns attempts) e (fun n hn => h ⟨n, hn⟩)
  rw [LifetimeHybridOrder.chronologicalProbability_zero] at ht
  have he : (∑ n ∈ Finset.range (lifetimeRuns attempts), e n) =
      (∑ n : Fin (lifetimeRuns attempts), PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)) +
      (lifetimeRuns attempts : ℝ) * keySplit C (Q + lifetimeOverhead C attempts Q +
        (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rwa [he] at ht

/-- The simulation and forger bound on the fixed dealer-keygen world. Each slot term has
`streamKeyError` for the move from the shared stream table to the table of that slot. -/
def LifetimeAfterKeygen (Q : ℕ) : Prop :=
  let circuits := circuitsOf fun _ => 0
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel circuits settings + 2) * Q
  LifetimeHybridOrder.dealerKeygenProbability K settings attempts aes circuitsOf D A ≤
    (∑ slot : Slot attempts,
      (treeCheckError (E := E) circuits settings (slotTree slot) (q₀ + q) +
        (treeHashError circuits settings C (slotTree slot) (q₀ + q) - keySplit C (q₀ + q)) +
        streamKeyError C + seedHitError C (q₀ + q))) +
      2 ^ layerHeight * searchFailure + signingHashError q₀ +
      seedHitError C q₀ + seedCollisionError C

/-- The key split occurs equally often in time order and in the fixed slot order. -/
theorem slot_split_cancel (circuits : Circuits) (q₀ q : ℕ) :
    (lifetimeRuns attempts : ℝ) * keySplit C (q₀ + q) +
      (∑ slot : Slot attempts,
        (treeCheckError (E := E) circuits settings (slotTree slot) (q₀ + q) +
          (treeHashError circuits settings C (slotTree slot) (q₀ + q) - keySplit C (q₀ + q)) +
          streamKeyError C + seedHitError C (q₀ + q))) =
      (let runError := fun tree => (attempts : ℝ) *
        (treeCheckError (E := E) circuits settings tree (q₀ + q) +
          treeHashError circuits settings C tree (q₀ + q) + streamKeyError C +
          seedHitError C (q₀ + q))
       runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) := by
  rw [← sum_lifetime_slot_error (C := C) (E := E) attempts circuits settings q₀ q]
  have hc : (∑ _ : Slot attempts, keySplit C (q₀ + q)) =
      (lifetimeRuns attempts : ℝ) * keySplit C (q₀ + q) := by
    rw [Finset.sum_const, Finset.card_univ, slot_card, nsmul_eq_mul]
  rw [← hc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro slot _
  ring

/-- The statement's exact inequality follows from the chronological pass, one keygen hop,
and the fixed dealer-world simulation contract. -/
theorem lifetime_bound_of_hops (Q : ℕ)
    (hprf : LifetimePrfHop K settings attempts aes circuitsOf D A Q)
    (hkeygen : LifetimeHybridOrder.LifetimeKeygenHop K settings attempts aes circuitsOf D A Q)
    (hrest : LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q) :
    let circuits := circuitsOf fun _ => 0
    let q₀ := Q + lifetimeOverhead C attempts Q
    let q := (ceremonyFuel circuits settings + 2) * Q
    let runError := fun tree => (attempts : ℝ) *
      (treeCheckError (E := E) circuits settings tree (q₀ + q) +
        treeHashError circuits settings C tree (q₀ + q) + streamKeyError C +
        seedHitError C (q₀ + q))
    lifetimeAdvantageSampled K settings attempts aes circuitsOf D A ≤
      keygenHashError C ((setupRounds + 2) * Q) +
        (runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) +
        ∑ n : Fin (lifetimeRuns attempts),
          PRFScheme.prfAdvantage (hiddenStreams aes)
            (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) +
        2 ^ layerHeight * searchFailure + signingHashError q₀ +
        seedHitError C q₀ + seedCollisionError C := by
  dsimp only
  have hp := (le_abs_self _).trans (lifetimePrfPass K settings attempts aes circuitsOf D A Q hprf)
  have hk := (le_abs_self _).trans hkeygen
  have hs := slot_split_cancel (C := C) (E := E) settings attempts
    (circuitsOf fun _ => 0) (Q + lifetimeOverhead C attempts Q)
    ((ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)
  dsimp only [LifetimeAfterKeygen] at hrest
  linarith

/-- Full quantifiers of the original target, from the transport with `keySplit` only, the
keygen hop and the dealer-world contract with `streamKeyError` in each slot. -/
theorem lifetimeSecurity_of_sources
    (hsource : (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf →
      0 < settings.batchSize → ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
        HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
        LifetimePrfTransport K settings attempts aes circuitsOf D A Q ∧
        LifetimeHybridOrder.LifetimeKeygenHop K settings attempts aes circuitsOf D A Q ∧
        LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q) :
    LifetimeSecurityStatementSampled K settings attempts aes circuitsOf := by
  intro hcompute hshape hbatch D A Q hQ
  obtain ⟨hp, hk, hr⟩ := hsource hcompute hshape hbatch D A Q hQ
  exact lifetime_bound_of_hops K settings attempts aes circuitsOf D A Q
    (lifetimePrfHop_of_transport K settings attempts aes circuitsOf D A Q hp) hk hr

/-- The original target from the transport in the case `keySplit (q₀ + q) < 2`, the keygen hop
and the dealer-world contract. -/
theorem lifetimeSecurity_of_smallSplit
    (hsource : (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf →
      0 < settings.batchSize → ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
        HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
        LifetimePrfTransportSmallSplit K settings attempts aes circuitsOf D A Q ∧
        LifetimeHybridOrder.LifetimeKeygenHop K settings attempts aes circuitsOf D A Q ∧
        LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q) :
    LifetimeSecurityStatementSampled K settings attempts aes circuitsOf :=
  lifetimeSecurity_of_sources K settings attempts aes circuitsOf
    fun hcompute hshape hbatch D A Q hQ =>
      let ⟨hp, hk, hr⟩ := hsource hcompute hshape hbatch D A Q hQ
      ⟨lifetimePrfTransport_of_smallSplit K settings attempts aes circuitsOf D A Q hp, hk, hr⟩

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.lifetimePrfTransport_of_smallSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimePrfTransport_of_smallSplit

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.lifetimePrfHop_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimePrfHop_of_transport

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.lifetimePrfPass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimePrfPass

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.slot_split_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slot_split_cancel

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.lifetime_bound_of_hops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetime_bound_of_hops

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.lifetimeSecurity_of_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeSecurity_of_sources

/-- info: 'ThresholdLeanXmssSecurity.LifetimeAllowance.lifetimeSecurity_of_smallSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeSecurity_of_smallSplit

end ThresholdLeanXmssSecurity.LifetimeAllowance
