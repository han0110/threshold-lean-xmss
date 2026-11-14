import ThresholdLeanXmssSecurity.Proof.SigningOwnGate

/-!
# The block bound of a top key with the own budget

- `GoodSize` is `GateProbability.Good` with `SizeTerminal` in place of `Terminal`. The bound on the
  number of the edges replaces the bound on the count of the calls.
- `inner_bound_size` to `after_private_bound_size` follow `inner_bound` to `after_private_bound` of
  `SigningHitProof.lean`. Each one reads the edges of the public rows and no call counter.
- `reset_size_le` bounds the edges of the reset public run after the selected block by the own
  budget and `topChainSlack`. The private record of the selected block is not in that run.
- `logged_block_bound_own` is `GateProbability.logged_block_bound` with the own budget.
- `keyGateBoundOwn_of_block` gives the gate bound of each top key from the block bound.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnGateBlock

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitProof SigningHitLaneProof SigningCostProof
open SigningOwnForger SigningOwnGate

variable {C : Committee} (prims : Primitives)

open Classical

theorem size_emptyRows {State : Type} [Fintype State] {Index : Type} [Fintype Index] :
    LayeredGraph.size (LayeredGraph.emptyRows : Index → List (State → Option State)) = 0 := by
  simp [LayeredGraph.size, LayeredGraph.emptyRows, SigningHitProof.LayeredGraph.edge]
  right
  intro i x
  fin_cases i <;> rfl

/-- `GateProbability.Good` with the number of the edges of the public rows in place of the count. -/
def GoodSize (b : XmssSecurity.TopIndex) (target : ChainIndex → Digest) (q : ℕ)
    {α : Type} (r : α × PublicContinuation.State C) (table : ProtectedSlot C → HashOutput) : Prop :=
  (∃ D : Finset C.Party, D.card ≤ C.t - 1 ∧
    UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b) r.2.1) ∧
  PosteriorCompletion.markedEvent r.2.1 (List.finRange 3) target
    (SelectedKeygen.starts table b, (ProtectedTable.split table).2) ∧
  LayeredGraph.SizeTerminal target q (PublicContinuation.rows r.2.1)

set_option backward.isDefEq.respectTransparency false in
theorem inner_bound_size (b : XmssSecurity.TopIndex) (target : ChainIndex → Digest) (q : ℕ)
    {α : Type} (r : α × PublicContinuation.State C) :
    Pr[fun h => GoodSize b target q r (tableExtending r.2.1 h) |
      $ᵗ (ProtectedSlot C → HashOutput)] ≤
      if LayeredGraph.SizeTerminal target q (PublicContinuation.rows r.2.1)
      then ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ else 0 := by
  classical
  by_cases ht : LayeredGraph.SizeTerminal target q (PublicContinuation.rows r.2.1)
  · rw [if_pos ht]
    by_cases ha : ∃ D : Finset C.Party, D.card ≤ C.t - 1 ∧
        UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b) r.2.1
    · obtain ⟨D, hD, hallowed⟩ := ha
      apply le_trans (probEvent_mono (p := fun h => GoodSize b target q r (tableExtending r.2.1 h))
        (fun _ _ h => h.2.1))
      exact PosteriorCompletion.marked_density D hD b r.2.1 hallowed (List.finRange 3)
        (List.nodup_finRange 3) target
    · simp [GoodSize, ha]
  · simp [GoodSize, ht]

set_option backward.isDefEq.respectTransparency false in
theorem posterior_bound_size {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C) α)
    (s : PublicContinuation.State C) (b : XmssSecurity.TopIndex)
    (target : ChainIndex → Digest) (q : ℕ) :
    Pr[fun p => GoodSize b target q p.1 p.2 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run s
      pure (r, table)] ≤
      ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ *
        Pr[fun r => LayeredGraph.SizeTerminal target q (PublicContinuation.rows r.2.1) |
          (simulateQ (FinitePosterior.lazy CountedPosterior.aux) oa).run s] := by
  have hd := FinitePosterior.joint_table_mixed CountedPosterior.aux CountedPosterior.aux_preserves oa s
  have hp := probEvent_congr' (p := fun p => GoodSize b target q p.1 p.2)
    (q := fun p => GoodSize b target q p.1 p.2) (fun _ _ => Iff.rfl) hd
  rw [hp, probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map]
  calc
    _ ≤ ∑' r, Pr[= r | (simulateQ (FinitePosterior.lazy CountedPosterior.aux) oa).run s] *
        (if LayeredGraph.SizeTerminal target q (PublicContinuation.rows r.2.1)
          then ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ else 0) :=
      ENNReal.tsum_le_tsum fun r => mul_le_mul_left' (inner_bound_size b target q r) _
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro r
      split <;> simp only [zero_mul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem counted_terminal_probability_size (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (target : ChainIndex → Digest) (q : ℕ) (hq : q < 2 ^ 127) :
    Pr[fun r => LayeredGraph.SizeTerminal target q (PublicContinuation.rows r.2.1) |
      (simulateQ (FinitePosterior.lazy CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) oa)).run
          ((ProtectedRouting.split (protectedInput x b) cache).1,
            (ProtectedRouting.split (protectedInput x b) cache).2, n)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [← PublicContinuation.counted_run prims x b hno oa cache n]
  exact PublicContinuation.terminal_probability_size _ target _ (PublicContinuation.rows_empty _ hempty) q hq

set_option backward.isDefEq.respectTransparency false in
theorem fixed_endpoint_bound_size (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (target : ChainIndex → Digest) (q : ℕ) (hq : q < 2 ^ 127) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => GoodSize b target q p.1 p.2 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) oa)).run s
      pure (r, table)] ≤ ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply le_trans (posterior_bound_size _ _ b target q)
  exact mul_le_mul_left' (counted_terminal_probability_size prims x b hno oa
    cache n hempty target q hq) _

set_option backward.isDefEq.respectTransparency false in
theorem adaptive_endpoint_bound_size (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (next : (ChainIndex → Digest) → OracleComp (LocalSpec C) α)
    (choose : (ProtectedSlot C → HashOutput) → (ChainIndex → Digest))
    (cache : HashCache C) (n : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (q : ℕ) (hq : q < 2 ^ 127) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => GoodSize b (choose p.2) q p.1 p.2 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) (next (choose table)))).run s
      pure (r, table)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  let s : PublicContinuation.State C :=
    ((ProtectedRouting.split (protectedInput x b) cache).1,
      (ProtectedRouting.split (protectedInput x b) cache).2, n)
  let prior := tableExtending s.1 <$> ($ᵗ (ProtectedSlot C → HashOutput))
  let run := fun target table =>
    (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
      (simulateQ (CountedPosterior.localQuery prims x b) (next target))).run s
  have hs := GateProbability.adaptive_le_sum prior choose run
    (fun target table r => GoodSize b target q r table)
  simp only [prior, bind_map_left] at hs
  apply le_trans hs
  calc
    _ ≤ ∑ _target : ChainIndex → Digest,
        ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro target _
      exact fixed_endpoint_bound_size prims x b hno (next target) cache n hempty target q hq
    _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        show Fintype.card Digest = 2 ^ 128 by simp [digestBits],
        show Fintype.card ChainIndex = 58 from rfl, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem after_private_bound_size (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (next : List (List Bit) → OracleComp (LocalSpec C) α)
    (cache : HashCache C) (n q : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hq : q < 2 ^ 127)
    (event : (ProtectedSlot C → HashOutput) → α × PublicContinuation.State C → Prop)
    (htransport : ∀ h : ProtectedSlot C → HashOutput,
      let s : PublicContinuation.State C :=
        ((ProtectedRouting.split (protectedInput x b) cache).1,
          (ProtectedRouting.split (protectedInput x b) cache).2, n)
      let table := tableExtending s.1 h
      ∀ p ∈ support (CountedPosterior.run prims x b table
        (liftComp ((SelectedKeygen.jobs b).mapM
          (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)) s),
      ∀ r ∈ support (CountedPosterior.run prims x b table
        (next ((List.finRange numChains).map fun l => bitsOfDigest (SelectedKeygen.endpoints table b l)))
        (s.1, s.2.1, 0)),
      event table (PrivateRecord.restoreOutcome p.2.1 p.2.2.2 r) →
        GoodSize b (SelectedKeygen.endpoints table b) q r table) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => event p.2 p.1 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← CountedPosterior.run prims x b table (do
        let outputs ← liftComp ((SelectedKeygen.jobs b).mapM
          (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)
        next outputs) s
      pure (r, table)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  dsimp only
  let s : PublicContinuation.State C :=
    ((ProtectedRouting.split (protectedInput x b) cache).1,
      (ProtectedRouting.split (protectedInput x b) cache).2, n)
  let visible := fun target : ChainIndex → Digest =>
    next ((List.finRange numChains).map fun l => bitsOfDigest (target l))
  apply le_trans (b := Pr[fun p => GoodSize b (SelectedKeygen.endpoints p.2 b) q p.1 p.2 | do
    let h ← $ᵗ (ProtectedSlot C → HashOutput)
    let table := tableExtending s.1 h
    let r ← CountedPosterior.run prims x b table (visible (SelectedKeygen.endpoints table b))
      (s.1, s.2.1, 0)
    pure (r, table)])
  · simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map]
    apply ENNReal.tsum_le_tsum
    intro h
    apply mul_le_mul_left'
    apply PrivateRecord.private_bind_bound prims x b _ _ _ _ s (FinitePosterior.extending_agrees _ _)
    · intro p hp
      rw [(SelectedKeygen.counted_jobs_support prims x b hno _ s p hp).1]
    · intro p hp
      exact (SelectedKeygen.counted_jobs_support prims x b hno _ s p hp).2
    · exact htransport h
  · exact adaptive_endpoint_bound_size prims x b hno visible
      (fun table => SelectedKeygen.endpoints table b) cache 0 hempty q hq

/-- The reset public run after the selected block adds at most `q + topChainSlack` edges to empty
public rows. -/
theorem reset_size_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (target : ChainIndex → Digest) (q : ℕ) (hown : HasSigningOwnBound A q)
    (table : ProtectedSlot C → HashOutput) (s : PublicContinuation.State C)
    (hempty : ∀ l k v, s.1 (.inr (l, k, v)) = none) :
    ∀ r ∈ support (CountedPosterior.run prims x b table
      (PublicVerification.afterSelected A x b after left target) s),
      LayeredGraph.size (PublicContinuation.rows r.2.1) ≤ q + topChainSlack := by
  intro r hr
  have h := run_size_le prims x b hno table _ s _
    (afterSelected_topChainBound A q x b after hb left target hown) r hr
  rw [PublicContinuation.rows_empty _ hempty, size_emptyRows] at h
  simpa only [Nat.zero_add] using h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
/-- Every supported restored exception yields `GoodSize` on the reset public run. -/
theorem restored_exception_good_size (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (cache : HashCache C) (n q : ℕ) (hown : HasSigningOwnBound A q)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1)
    (h : ProtectedSlot C → HashOutput) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    let table := tableExtending s.1 h
    ∀ p ∈ support (CountedPosterior.run prims x b table
      (liftComp ((SelectedKeygen.jobs b).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)) s),
    ∀ r ∈ support (CountedPosterior.run prims x b table
      (PublicVerification.afterSelected A x b after left (SelectedKeygen.endpoints table b))
      (s.1, s.2.1, 0)),
    GateProbability.SupportedException prims A x b (PrivateRecord.restoreOutcome p.2.1 p.2.2.2 r) →
      GoodSize b (SelectedKeygen.endpoints table b) (q + topChainSlack) r table := by
  intro s table p hp r hr hex
  obtain ⟨z, hz, hex, he⟩ := hex
  have hout := congrArg Prod.fst he
  have hrecord := congrArg (fun u => u.2.1) he
  have hraw := congrArg (fun u => u.2.2.1) he
  change r.1 = z.1 at hout
  change PrivateRecord.merge p.2.1 r.2.1 = (ProtectedRouting.split (protectedInput x b) z.2.1.1).1 at hrecord
  change r.2.2.1 = (ProtectedRouting.split (protectedInput x b) z.2.1.1).2 at hraw
  have hpCache := (FinitePosterior.eager_cache CountedPosterior.aux CountedPosterior.aux_preserves table
    (simulateQ (CountedPosterior.localQuery prims x b) _) s (FinitePosterior.extending_agrees _ _) p hp).2
  have hrCache := (FinitePosterior.eager_cache CountedPosterior.aux CountedPosterior.aux_preserves table
    (simulateQ (CountedPosterior.localQuery prims x b) _) (s.1, s.2.1, 0)
    (FinitePosterior.extending_agrees _ _) r hr).2
  obtain ⟨observed, hobsRecord, hobsRaw, hverified⟩ := PublicVerification.reset_observed_witness
    prims A x b hno after left _ cache h r hr
  have hobs : observed ≤ z.2.1.1 := by
    apply ProtectedRouting.split_le (protectedInput x b)
    · rw [← hobsRecord, ← hrecord]
      exact PrivateRecord.observed_le_merge _ _
    · rw [← hobsRaw, ← hraw]
  have hagree : (ProtectedRouting.split (protectedInput x b) z.2.1.1).1.AgreesWithFn table := by
    rw [← hrecord]
    exact PrivateRecord.merge_agrees _ _ table hpCache hrCache
  obtain ⟨top, state, forgery, hsome, hfresh⟩ := forestException_fresh prims A x z hz hex.1
  have hsome' : r.1.2 = some (top, state, forgery) := (congrArg Prod.snd hout).trans hsome
  have hview := PublicVerification.afterOutputs_counted_view prims A x b hno table after hb left _
    (s.1, s.2.1, 0) hallowed r hr top state forgery hsome' hfresh
  have hflag : r.1.1.2 = false := by
    rw [hout]
    exact congrArg Prod.snd hex.1.1.1
  have hg := GateProbability.good_of_exception prims A x b hno z hz hex observed hobs table hagree
    ⟨state.corrupt, hview.1, by rw [← hobsRecord]; exact hview.2 hflag⟩
    (fun top state forgery hh => hverified top state forgery ((congrArg Prod.snd hout).trans hh))
    r.1 0 0 le_rfl
  have hsize := reset_size_le prims A x b hno after hb left _ q hown table (s.1, s.2.1, 0) hempty r hr
  rw [← hobsRecord] at hg
  exact ⟨hg.1, hg.2.1, hsize, hg.2.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem private_afterOutputs_bound_size (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (cache : HashCache C) (n q : ℕ) (hown : HasSigningOwnBound A q)
    (hsmall : q + topChainSlack < 2 ^ 127)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => GateProbability.SupportedException prims A x b p.1 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← CountedPosterior.run prims x b table (do
        let selected ← liftComp ((SelectedKeygen.jobs b).mapM
          (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)
        simulateQ worldLocalize (PublicVerification.afterOutputs A x b after left selected)) s
      pure (r, table)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply after_private_bound_size prims x b hno _ cache n (q + topChainSlack) hempty hsmall
    (fun _ => GateProbability.SupportedException prims A x b)
  intro h
  exact restored_exception_good_size prims A x b hno after hb left cache n q hown hempty hallowed h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem raw_block_bound_size (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (cache : HashCache C) (n q : ℕ) (hown : HasSigningOwnBound A q)
    (hsmall : q + topChainSlack < 2 ^ 127)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1) :
    Pr[GateProbability.RawException prims A x b |
      (simulateQ (SigningCacheProof.countImpl prims) (PublicVerification.block A x b after left)).run
        (cache, n)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply le_trans (b := Pr[fun r => GateProbability.SupportedException prims A x b
    (r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
      (ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2) |
      (simulateQ (SigningCacheProof.countImpl prims) (PublicVerification.block A x b after left)).run (cache, n)])
  · apply probEvent_mono
    intro r _ hr
    obtain ⟨log, hz, hex⟩ := hr
    exact ⟨(r.1, r.2, log), hz, hex, rfl⟩
  · rw [CountedPosterior.prior_marginal prims x b hno _ (PublicVerification.programFree_block A x b after left)]
    simpa only [PublicVerification.block, simulateQ_bind, PublicVerification.localize_liftFree] using
      private_afterOutputs_bound_size prims A x b hno after hb left cache n q hown hsmall hempty hallowed

set_option maxRecDepth 100000 in
/-- `GateProbability.logged_block_bound` with the own budget. The all-party cap is replaced by the own
budget and the fixed `topChainSlack`. -/
theorem logged_block_bound_own (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (s : LoggedState C) (q : ℕ) (hown : HasSigningOwnBound A q)
    (hsmall : q + topChainSlack < 2 ^ 127)
    (hempty : ∀ l k v, s.1.1 (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) s.1.1).1) :
    Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
      (simulateQ (loggedImpl prims) (PublicVerification.block A x b after left)).run s] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have he := congrArg (fun oa => Pr[GateProbability.RawException prims A x b | oa])
    (logged_forget prims (PublicVerification.block A x b after left) s)
  simp only [probEvent_map, Function.comp_def] at he
  apply he.le.trans
  exact raw_block_bound_size prims A x b hno after hb left s.1.1 s.1.2 q hown hsmall hempty hallowed

/-- `KeyGateBound` with the own budget. -/
def KeyGateBoundOwn (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    HasSigningOwnBound A q → q + signingSlack < 2 ^ 127 → ∃ T : C.Term, ∀ (b : XmssSecurity.TopIndex) s,
      RawReachable prims s → ¬GateSeen (.inr (.inr (.inl (topGateInput x T b)))) s.2 →
      (∑' r, Pr[= r | (loggedImpl prims (.inr (.inr (.inl (topGateInput x T b))))).run s] *
        continuationReserve prims (SigningDescentProof.finalRun A x) (ForestExceptionAt prims x b) r.2) ≤
          (2 ^ 128 : ℝ≥0∞)⁻¹

set_option maxRecDepth 100000 in
/-- The gate bound with the own budget from `logged_block_bound_own`. The proof is the proof of
`keyGateBound`. -/
theorem keyGateBoundOwn_of_block : KeyGateBoundOwn prims C := by
  intro A q x _ hno hown hsmall
  obtain ⟨T, terms, hterms⟩ := terms_cons C
  refine ⟨T, ?_⟩
  intro b s hs hseen
  apply gate_bound_of_prefix prims (SigningDescentProof.finalRun A x)
    (ForestExceptionAt prims x b) (.inr (.inr (.inl (topGateInput x T b))))
    ((2 ^ 128 : ℝ≥0∞)⁻¹) _ s hs hseen
  intro n initial k hp hnotseen
  obtain ⟨after, hb, left, hresidual⟩ := SelectedKeygen.gate_residual_block
    prims A x b T terms hterms n initial k hp hnotseen
  have hfresh := SelectedKeygen.gate_prefix_fresh prims A x b T terms hterms n initial k hp hnotseen
  have hbound := logged_block_bound_own prims A x b hno after hb left initial q hown
    (by unfold signingSlack at hsmall; unfold topChainSlack; omega)
    (fun l step value => hfresh _ (by exact ⟨l, step, value, rfl⟩))
    (SelectedKeygen.fresh_record_allowed x b initial.1.1 hfresh)
  rw [← PublicVerification.liveBlock_exception_probability prims A x b after left initial] at hbound
  apply le_trans (b := Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
    (simulateQ (loggedImpl prims) (OracleComp.queryBind (.inr (.inr (.inl (topGateInput x T b)))) k)).run initial])
  · apply probEvent_mono
    intro r hr hex
    exact ⟨r.2.2, prefixRun_support_resume prims (SigningDescentProof.finalRun A x)
      n _ initial hp r hr, hex⟩
  · rw [hresidual]
    exact hbound

end ThresholdLeanXmssSecurity.SigningOwnGateBlock

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.size_emptyRows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.size_emptyRows

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.inner_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.inner_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.posterior_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.posterior_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.counted_terminal_probability_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.counted_terminal_probability_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.fixed_endpoint_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.fixed_endpoint_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.adaptive_endpoint_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.adaptive_endpoint_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.after_private_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.after_private_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.reset_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.reset_size_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.restored_exception_good_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.restored_exception_good_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.private_afterOutputs_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.private_afterOutputs_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.raw_block_bound_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.raw_block_bound_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.logged_block_bound_own' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.logged_block_bound_own

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGateBlock.keyGateBoundOwn_of_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGateBlock.keyGateBoundOwn_of_block
