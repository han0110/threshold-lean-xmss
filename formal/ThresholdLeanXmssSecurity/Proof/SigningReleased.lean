import ThresholdLeanXmssSecurity.Proof.SigningSupport
import ThresholdLeanXmssSecurity.Proof.SigningUnchargedLogged

/-!
# The receipts of a released signature

This module holds two receipt lemmas. `verifyRun_released_receipt` of
`Proof/SigningReleasedTransfer.lean` uses them.

* `openingRun_receipts` moves the run of `openingOracles` to a run of `flaggedReceiptOracles` with
  the same state and cache.
* `receiptRun_released` gives the receipt of a release. A release needs `t` signers. The corrupt
  operators are at most `t - 1`, so an honest round 2 released the chain parts at the key. Its
  receipt has supported runs below the cache.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningReleasedProof

open HashSig LeanXmss ThresholdLeanXmss SigningOpeningProof

variable {C : Committee}

section Receipts

variable (prims : Primitives)

/-- A counted run of `openingOracles` has a counted run of `flaggedReceiptOracles` with the same
result, state and cache. -/
theorem openingRun_receipts (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) (flag : Bool)
    (s : HashCache C × ℕ)
    (q : (α × (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ)
    (hq : q ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (openingOracles x dealt) source).run ((st, flag), ∅, []))).run s)) :
    ∃ q' : (α × (TsigState C × Bool) × List (SigningGuessProof.Round2Receipt C)) × HashCache C × ℕ,
      q' ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((simulateQ (SigningGuessProof.flaggedReceiptOracles x dealt) source).run ((st, flag), []))).run s) ∧
      q'.1.1 = q.1.1 ∧ q'.1.2.1 = q.1.2.1 ∧ q'.2 = q.2 := by
  have hopening := SigningCoreProof.simulateQ_run_forget _ _ (openingOracles_forget x dealt) source
    (st, flag) ((∅ : Finset (Fin (2 ^ layerHeight))), ([] : List (HiddenKey × Digest)))
  have hreceipt := SigningGuessProof.flaggedReceiptOracles_forget x dealt source st flag []
  have hmem : ((q.1.1, q.1.2.1), q.2) ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (SigningCoreProof.flaggedOracles x dealt) source).run (st, flag))).run s) := by
    rw [← hopening, simulateQ_map, StateT.run_map, support_map]
    exact ⟨q, hq, rfl⟩
  rw [← hreceipt, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨q', hq', heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  exact ⟨q', hq', heq.1.1, heq.1.2, heq.2⟩

/-- At least `t` signers at `e` for `message` hold an honest release. Its receipt has supported
runs below the cache. -/
theorem receiptRun_released (x : SigningSecurityProof.Keys3 C) (top : TopTree) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : HashCache C × ℕ)
    (q : (α × (TsigState C × Bool) × List (SigningGuessProof.Round2Receipt C)) × HashCache C × ℕ)
    (hq : q ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (SigningGuessProof.flaggedReceiptOracles x (SigningGuessProof.receiptDealt x top)) source).run
        ((SigningCoreProof.tsigInit, false), []))).run s))
    (e : KeyIndex) (message : Message) (ht : C.t ≤ (signersAt q.1.2.1.1 e message).card) :
    ∃ receipt ∈ q.1.2.2, receipt.key = e ∧ receipt.message = message ∧
      SigningGuessProof.ReceiptRuns prims x top q.2.1 receipt := by
  have hin := SigningGuessProof.countRun_support prims _ s q hq
  have hcorrupt := SigningGuessProof.flaggedReceiptOracles_corrupt_le x _ source q.1 hin
  have hreleased : q.1.2.1.1.released = q.1.2.2.map SigningGuessProof.Round2Receipt.release := by
    apply SigningGuessProof.signingReceiptOracles_released _ source (q.1.1, q.1.2.1.1, q.1.2.2)
    rw [← SigningGuessProof.flaggedReceiptOracles_forgetFlag x _ source SigningCoreProof.tsigInit false [],
      support_map]
    exact ⟨q.1, hin, rfl⟩
  have hruns := SigningGuessProof.flaggedReceiptOracles_runs prims x top source
    (SigningCoreProof.tsigInit, false) [] s
    (by simp [SigningGuessProof.StoredTreeRuns, SigningCoreProof.tsigInit]) (by simp) q hq
  have hhonest : (((q.1.2.1.1.released.filter fun r => r.1 = e ∧ r.2.1 = message).map
      (·.2.2)).toFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    unfold signersAt at ht
    rw [hempty, Finset.union_empty] at ht
    have := C.one_le_t
    omega
  obtain ⟨i, hi⟩ := hhonest
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨a, ⟨ha, hae, ham⟩, -⟩ := hi
  rw [hreleased] at ha
  obtain ⟨receipt, hreceipt, rfl⟩ := List.mem_map.mp ha
  exact ⟨receipt, hreceipt, hae, ham, hruns receipt hreceipt⟩

end Receipts

end SigningReleasedProof

end ThresholdLeanXmssSecurity
