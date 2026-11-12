import ThresholdLeanXmssSecurity.Proof.LifetimeTailKernel

/-!
# Refresh estimates for a state-dependent tail

The reference tail is the actual driver applied to the chosen reference rows.
Refresh comparison and fresh-key guessing use a budget on that complete tail,
with no per-state round or final-observer allowance. The proof ports the
refresh argument of `TreeKeyAimed` and its path-budget version in
`LifetimePathCount`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeTailRefresh
open LifetimeTailKernel
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E σ : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (T : TailDriver C E σ) (lawful : T.Lawful D)

-- Port of TreeKeyAimed.aimedRefresh_referenceAfter (3608).
theorem refresh_referenceAfterG (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S) (hc : ¬ KeygenClash D parts)
    (a echo : S → HashOutput) (u : KeygenFresh C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : σ)
    (hd : ∀ i j : C.Party, j ≠ i → ¬ AimedEchoCell D u
      (.sharedKeys .prss ((sharedTerms i j).map
        (aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a)) (fun _ => 0) parts
          (fun i j => sentReveal j i) i).term))) :
    referenceAfterG K circuits settings D T prims state
      (prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u))) normal active parts
      sentCommit sentReveal =
      referenceAfterG K circuits settings D T prims state
        (prssHashAt prims (prssExtend S a)) normal active parts sentCommit sentReveal := by
  apply referenceAfterG_oracle_congr K circuits settings D T prims state _ _ normal active
    parts sentCommit sentReveal
  · intro i j values
    apply aimedRefresh_off
    rintro (⟨n, hn, he⟩ | he)
    · cases n with
      | parameter => exact hn.elim
      | term T => cases he
      | pair p => cases he
    · obtain ⟨l, hl⟩ := aimedEchoCell_sharedKeys he
      cases hl
  · intro table i hi
    exact aimedRefresh_referenceKeys prims D S parts hmem hc a echo u table _ i hi
  · intro i j hi hji
    simp only [prssEcho, aimedRefresh_referenceKeys prims D S parts hmem hc a echo u _ _ i hi]
    apply aimedRefresh_off
    rintro (⟨n, hn, he⟩ | he)
    · cases n with
      | parameter => exact hn.elim
      | term T => cases he
      | pair p => cases he
    · exact hd i j hji he

-- Port of TreeKeyAimed.probEvent_aimedRefresh_reference (4296).
include lawful in
theorem probEvent_refresh_referenceG (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : σ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hz : ∀ n, Hidden D n → keygenTableOf u.1 u.2 n ≠ 0)
    (hd : ∀ i j : C.Party, j ≠ i → ¬ AimedEchoCell D u
      (.sharedKeys .prss ((sharedTerms i j).map
        (aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a)) (fun _ => 0) parts
          (fun i j => sentReveal j i) i).term)))
    (he : ¬ AimedEchoCollision
      (fun i j => (⟨.sharedKeys .prss ((sharedTerms i j).map
        (aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a)) (keygenTableOf u.1 u.2)
          parts (fun i j => sentReveal j i) i).term), hsk i j _⟩ : S)) echo)
    (ha : KeysApart D (rowsOf (aimedFixedBoundary prims D
      (prssExtend S (aimedRefresh D S parts hmem a echo u))
      (prssDataMask D (prssDataAt (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts))
      (state, sentCommit, some sentReveal)).2)) :
    let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
    let r := aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts))
      (state, sentCommit, some sentReveal)
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h (rowsOf r.2)
      (T.tail K circuits settings r)] =
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h (rowsOf r.2)
      (referenceAfterG K circuits settings D T prims state
        (prssHashAt prims (prssExtend S a)) normal (prssCommitActive D sentCommit) parts
        sentCommit sentReveal)] := by
  dsimp only
  rw [aimedFixedBoundary_fullRows] at ha ⊢
  simp only [rowsOf] at ha ⊢
  let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
  have hkeys (i : C.Party) := aimedReferenceKeys_table_congr prims D (prssHashAt prims h)
    (fun n => prssHashAt prims h (hiddenInput parts n)) (keygenTableOf u.1 u.2) parts
    (fun i j => sentReveal j i) (fun n hn => aimedRefresh_canonical prims D S parts hmem hc a echo u n hn) i
  have hregular := aimedRefresh_echo_regular prims D S parts hmem hsk hc a echo u
    (fun i j => sentReveal j i) he
  have hn := probEvent_tail_eager_reference K circuits settings D T lawful prims
    (prssHashAt prims h) normal (prssCommitActive D sentCommit) parts sentCommit sentReveal state
    (aimedRevealRowsFixed prims D (prssHashAt prims h) (prssCommitActive D sentCommit) parts
      (prssCommitInbox D (prssDataAt (prssHashAt prims h) parts) sentCommit) sentReveal)
    ha (fun n hn => by rw [aimedRefresh_canonical prims D S parts hmem hc a echo u n hn]; exact hz n hn)
    hni hn0 (by simpa only [hkeys] using hregular)
  rw [refresh_referenceAfterG prims K circuits settings D T S normal
    (prssCommitActive D sentCommit) parts hmem hc a echo u sentCommit sentReveal state hd] at hn
  simpa only [aimedEagerFlag_hashAt, Option.getD_some, h] using hn

def eagerFinishG (keys : KeyName C × HashOutput → Digest)
    (h : Query C → HashOutput) (r : σ × Option (RevealRows C)) :
    ProbComp ((σ × Option (RevealRows C)) × (Bool × Bool)) :=
  (fun y => (r, y)) <$> simulateQ (prssLocalAt prims h)
    (simulateQ (aimedKeyLocal prims D keys) ((simulateQ (aimedFlagQueries D (rowsOf r.2))
      (T.tail K circuits settings r)).run false))

def finishProbabilityG (h : Query C → HashOutput)
    (r : σ × Option (RevealRows C)) : ℝ≥0∞ :=
  Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
    ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
      eagerFinishG prims K circuits settings D T keys h r]

omit [Fintype E] [DecidableEq E] in
theorem finishProbabilityG_eq (h : Query C → HashOutput)
    (r : σ × Option (RevealRows C)) :
    finishProbabilityG prims K circuits settings D T h r =
      if KeysApart D (rowsOf r.2) then Pr[fun y => y.2 = true |
        aimedEagerFlag prims D h (rowsOf r.2) (T.tail K circuits settings r)]
      else 0 := by
  unfold finishProbabilityG eagerFinishG aimedEagerFlag
  by_cases ha : KeysApart D (rowsOf r.2)
  · simp only [probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, ha, true_and, if_true]
  · simp only [probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, ha, false_and, if_false,
      probEvent_False, mul_zero, tsum_zero]

omit [Fintype E] [DecidableEq E] in
theorem finishProbabilityG_none (h : Query C → HashOutput) (state : σ) :
    finishProbabilityG prims K circuits settings D T h (state, none) = 0 := by
  rw [finishProbabilityG_eq]
  split_ifs
  · simp only [rowsOf, Option.getD_none, aimedEagerFlag, aimedFlagQueries_empty,
      simulateQ_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
      Bool.false_eq_true, probEvent_False, mul_zero, tsum_zero]
  · rfl

-- Port of TreeKeyAimed.probEvent_aimedRefresh_finish_le (4463).
include lawful in
theorem probEvent_refresh_finish_leG (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0) :
    let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
    let boundary := aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r
    let game := referenceTailG K circuits settings D T prims
      (prssHashAt prims (prssExtend S a)) normal parts r
    finishProbabilityG prims K circuits settings D T h boundary ≤
      (if AimedBoundaryException prims D S hsk (prssHashAt prims (prssExtend S a)) parts r u echo then 1 else 0) +
      Pr[fun y => y.2 = true | aimedEagerFlag prims D (prssExtend S a) (rowsOf boundary.2) game] +
      aimedMean ($ᵗ (KeyName C × HashOutput → Digest)) (fun keys =>
        Pr[fun y => ∃ v ∈ y.2, AimedPrefixCell D parts u v |
          simulateQ (prssLocalAt prims (prssExtend S a))
            (keygenHashLog (simulateQ (aimedKeyLocal prims D keys) game))]) := by
  dsimp only
  by_cases hb : AimedBoundaryException prims D S hsk (prssHashAt prims (prssExtend S a)) parts r u echo
  · rw [if_pos hb]
    exact le_trans probEvent_le_one ((le_add_right le_rfl).trans (le_add_right le_rfl))
  rw [if_neg hb, zero_add]
  rcases r with ⟨state, sentCommit, _ | sentReveal⟩
  · rw [show aimedFixedBoundary prims D _ _ (state, sentCommit, none) = (state, none) from rfl,
      finishProbabilityG_none]
    exact zero_le
  · rw [finishProbabilityG_eq]
    split_ifs with ha
    · rw [probEvent_refresh_referenceG prims K circuits settings D T lawful S normal parts
        hmem hsk hc a echo u sentCommit sentReveal state hni hn0
        (fun n hn he => hb (Or.inl ⟨n, hn, he⟩))
        (fun i j hij he => hb (Or.inr (Or.inl ⟨i, j, hij, he⟩)))
        (fun he => hb (Or.inr (Or.inr he))) ha]
      simp only [aimedEagerFlag, ← aimedMean_probEvent, referenceTailG]
      rw [← aimedMean_add]
      exact aimedMean_mono _ fun keys => probEvent_aimedFlag_swap_le prims D _ _ _
        (AimedPrefixCell D parts u) (aimedRefresh_off prims D S parts hmem a echo u) keys _
    · exact zero_le

def tailHitG (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (u : KeygenFresh C) : ℝ≥0∞ :=
  aimedMean ($ᵗ (KeyName C × HashOutput → Digest)) (fun keys =>
    Pr[fun y => ∃ v ∈ y.2, AimedPrefixCell D parts u v |
      simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
        (referenceTailG K circuits settings D T prims h normal parts r)))])

-- Path-budget ports of LifetimePathCount:492–547.
theorem refresh_guess_leG (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (tailQ : ℕ)
    (htail : IsQueryBoundP (referenceTailG K circuits settings D T prims
      (prssHashAt prims (prssExtend S a)) normal parts r) WorldCounted tailQ) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => Pr[fun y => y.2 = true |
      aimedEagerFlag prims D (prssExtend S a)
        (rowsOf (aimedFixedBoundary prims D (prssExtend S (aimedRefresh D S parts hmem a echo u))
          (prssDataMask D (prssDataAt (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts)) r).2)
        (referenceTailG K circuits settings D T prims
          (prssHashAt prims (prssExtend S a)) normal parts r)]) ≤
      ((tailQ : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  rw [aimedMean_probEvent]
  exact probEvent_aimedEagerFresh_le prims D (prssExtend S a) _
    (fun u n k hk hn => aimedRefresh_boundary_hidden prims D S parts hmem hc a echo u r n k hk hn) _ _
    htail

include lawful in
theorem refresh_finish_leG (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a : S → HashOutput)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (tailQ : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (htail : IsQueryBoundP (referenceTailG K circuits settings D T prims
      (prssHashAt prims (prssExtend S a)) normal parts r) WorldCounted tailQ) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo =>
      let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
      finishProbabilityG prims K circuits settings D T h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r))) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    ((tailQ : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (KeygenFresh C))
      (tailHitG prims K circuits settings D T (prssHashAt prims (prssExtend S a)) normal parts r) := by
  have hb := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => probEvent_refresh_finish_leG prims K circuits settings D T lawful S normal
      parts hmem hsk hc a echo u r hni hn0))
  simp only [aimedMean_add, aimedMean_const] at hb
  refine hb.trans (add_le_add (add_le_add
    (probEvent_aimedBoundaryException_le prims D S hsk (prssHashAt prims (prssExtend S a)) parts r) ?_) ?_)
  · rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun echo => refresh_guess_leG prims K circuits settings D T S normal parts hmem hc a echo r tailQ htail)
  · unfold tailHitG
    rw [aimed_prssLocalAt_hashAt]

end ThresholdLeanXmssSecurity.LifetimeTailRefresh

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailRefresh.refresh_referenceAfterG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailRefresh.refresh_referenceAfterG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailRefresh.probEvent_refresh_referenceG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailRefresh.probEvent_refresh_referenceG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailRefresh.finishProbabilityG_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailRefresh.finishProbabilityG_none

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailRefresh.probEvent_refresh_finish_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailRefresh.probEvent_refresh_finish_leG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailRefresh.refresh_guess_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailRefresh.refresh_guess_leG

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailRefresh.refresh_finish_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailRefresh.refresh_finish_leG
