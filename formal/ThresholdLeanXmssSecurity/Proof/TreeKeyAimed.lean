import ThresholdLeanXmssSecurity.Proof.TreeKeyAfter
import ThresholdLeanXmssSecurity.Proof.Coupling
import ThresholdLeanXmssSecurity.Proof.KeygenFinish

/-!
The continuation swap, finite eager representation of the actual flagged experiment, canonical
cell resampling, individual guessing bounds, and full prefix accounting are proved.
The protocol coupling from the eager experiment to a private-invariant reference kernel remains
open. Thus `TreeKeyAimedFreshBound` and the `hFresh` arguments at the end remain obligations;
this file does not claim unconditional closure.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

open scoped ENNReal

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

-- Target: TreeKeyAimedBound prims K circuits settings.
-- Keep the full prefix budget: a prefix call can query a hidden canonical input.

/-- The echo-cell test from key generation, on the PRSS echo domain. -/
def aimedEchoDomain : Query C → Query C
  | .sharedKeys .prss values => .sharedKeys .keygen values
  | .sharedKeys .keygen values => .sharedKeys .prss values
  | q => q

def AimedEchoCell (D : C.Coalition) (u : KeygenFresh C) (q : Query C) : Prop :=
  KeygenEchoCell D u (aimedEchoDomain q)

theorem probEvent_aimedEchoCell_le_pair (D : C.Coalition) (q : Query C) :
    Pr[fun u => AimedEchoCell D u q | $ᵗ (KeygenFresh C)] ≤
      (C.n.choose 2 : ℝ≥0∞) / 2 ^ 256 := by
  simpa only [AimedEchoCell, keygenFinish_card_pair, card_hashOutput, Nat.cast_pow, Nat.cast_ofNat,
    div_eq_mul_inv] using probEvent_keygenEchoCell_le D (aimedEchoDomain q)

theorem probEvent_aimedEchoCell_le (D : C.Coalition) (q : Query C) :
    Pr[fun u => AimedEchoCell D u q | $ᵗ (KeygenFresh C)] ≤
      (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_keygenEchoCell_le D (aimedEchoDomain q)).trans ?_
  have hc : Fintype.card C.Pair ≤ prssKeyCount C := by
    have := card_pair_le C
    unfold prssKeyCount
    omega
  rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  gcongr

theorem aimedEchoCell_sharedKeys {D : C.Coalition} {u : KeygenFresh C} {q : Query C}
    (h : AimedEchoCell D u q) : ∃ values, q = .sharedKeys .prss values := by
  obtain ⟨values, hv⟩ := keygenEchoCell_sharedKeys h
  cases q <;> simp only [aimedEchoDomain] at hv <;> try cases hv
  rename_i phase values'
  cases phase <;> cases hv
  exact ⟨values, rfl⟩

theorem aimedEchoCell_of (D : C.Coalition) (u : KeygenFresh C) {i j : C.Party}
    (hij : i ≠ j) (hi : i ∉ D.1) (hj : j ∉ D.1) (hs : KeygenShareHidden D i j)
    (keys : C.Term → HashOutput)
    (hk : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → keys T = u.1 T) :
    AimedEchoCell D u (.sharedKeys .prss ((sharedTerms i j).map keys)) :=
  keygenEchoCell_of D u hij hi hj hs keys hk

/-- The honest boundary has at most one echo input per ordered pair. When these inputs are
independent of the fresh table, their union contributes the required `4*m^2` term. -/
theorem probEvent_aimedEchoBoundary_le (D : C.Coalition)
    (point : C.Party × C.Party → Query C) :
    Pr[fun u => ∃ p, AimedEchoCell D u (point p) | $ᵗ (KeygenFresh C)] ≤
      ((4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset (C.Party × C.Party))
    ($ᵗ (KeygenFresh C)) (fun p u => AimedEchoCell D u (point p))
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ((Finset.sum_le_sum (fun p _ => probEvent_aimedEchoCell_le D (point p))).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Committee.Party,
    Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc]
  apply ENNReal.div_le_div_right
  have hn := Nat.mul_le_mul_right (prssKeyCount C) (n_sq_le_prssKeyCount C)
  have he : (C.n * C.n) * prssKeyCount C ≤ 4 * prssKeyCount C ^ 2 := by
    nlinarith [hn]
  exact_mod_cast he

/-- There are two delivered echo positions for each unordered pair; self positions are unused. -/
theorem probEvent_aimedEchoDelivered_le (D : C.Coalition)
    (point : C.Pair × Bool → Query C) :
    Pr[fun u => ∃ p, AimedEchoCell D u (point p) | $ᵗ (KeygenFresh C)] ≤
      ((2 * C.n.choose 2 ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset (C.Pair × Bool))
    ($ᵗ (KeygenFresh C)) (fun p u => AimedEchoCell D u (point p))
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ((Finset.sum_le_sum (fun p _ => probEvent_aimedEchoCell_le_pair D (point p))).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    keygenFinish_card_pair, nsmul_eq_mul, ← mul_div_assoc]
  apply le_of_eq
  push_cast
  congr 1
  ring

/-- Derivation clashes, delivered echo hits, and one echo collision per unordered pair fit
inside the fixed quadratic allowance. This does not charge any prefix call twice. -/
theorem aimed_boundary_error_arith :
    keygenClashCount C + 2 * C.n.choose 2 ^ 2 + C.n.choose 2 ≤ 4 * prssKeyCount C ^ 2 := by
  have ht := one_le_termCount C
  unfold keygenClashCount prssKeyCount
  rw [keygenFinish_card_term, keygenFinish_card_pair]
  nlinarith [Nat.mul_le_mul_right (C.n.choose 2) ht]

theorem aimed_after_error_arith (q : ℕ) :
    q * prssKeyCount C + q * C.n.choose 2 + q * prssKeyCount C ≤
      3 * q * prssKeyCount C := by
  have hp : C.n.choose 2 ≤ prssKeyCount C := by unfold prssKeyCount; omega
  nlinarith [Nat.mul_le_mul_left q hp]

/-- The normalization's zero-key exclusion also fits in the quadratic boundary budget. -/
theorem aimed_boundary_zero_error_arith :
    keygenClashCount C + 2 * (C.n.choose 2) ^ 2 + C.n.choose 2 + prssKeyCount C ≤
      4 * prssKeyCount C ^ 2 := by
  have ht := one_le_termCount C
  unfold keygenClashCount prssKeyCount
  rw [keygenFinish_card_term, keygenFinish_card_pair]
  nlinarith [Nat.mul_le_mul_right (C.n.choose 2) ht]

/-- The reference view retains actual corrupt reveals and uses the honest parts directly. -/
def aimedCorruptView (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ D.1 then readReveal .prss (Msg.hashesOf (revealed i j)) i j else parts j

theorem aimed_derived_corruptView (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1)
    (hreceived : ∀ j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .prss (parts j) j i)
    (h : Query C → HashOutput) :
    ThresholdLeanXmssSecurity.D prims h (deriveKeys .prss i (prssView parts revealed i)) =
      ThresholdLeanXmssSecurity.D prims h
        (deriveKeys .prss i (aimedCorruptView D parts revealed i)) := by
  have corrupt (j : C.Party) (hj : j ∈ D.1) :
      prssView parts revealed i j = aimedCorruptView D parts revealed i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp [prssView, aimedCorruptView, hj, hji]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party)
      (hjT : j ∈ C.holders T) :
      (prssView parts revealed i j).term T =
        (aimedCorruptView D parts revealed i j).term T := by
    by_cases hj : j ∈ D.1
    · rw [corrupt j hj]
    · by_cases hji : j = i
      · subst j; simp [prssView, aimedCorruptView, hi]
      · simp only [prssView, if_neg hji, hreceived j hj hji,
          prss_readReveal_term _ _ _ _ hiT hjT, aimedCorruptView, if_neg hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (prssView parts revealed i a).pair b =
        (aimedCorruptView D parts revealed i a).pair b := by
    by_cases ha : a ∈ D.1
    · rw [corrupt a ha]
    · by_cases hai : a = i
      · subst a; simp [prssView, aimedCorruptView, hi]
      · have hbi := hab.resolve_left hai
        subst b
        simp only [prssView, if_neg hai, hreceived a ha hai,
          prss_readReveal_pair, aimedCorruptView, if_neg ha]
  rw [D_deriveKeys, D_deriveKeys]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive .prss .term)
        apply List.map_congr_left
        intro j hj
        exact term T hiT j (by simpa using (List.mem_filter.mp hj).2)
      · simp [hiT]
    · funext j
      by_cases hji : j = i
      · simp [hji]
      · simp only [dif_neg hji]
        have hp := pairOf_left_or_right i j (Ne.symm hji)
        apply congrArg h
        apply congrArg (Query.derive .prss .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

/-- Fresh named keys replace hidden derivations; exposed derivations use the actual reveals. -/
def aimedReferenceKeys (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) : PrssKeys C :=
  let keys := keygenMaskKeys D table i
    (ThresholdLeanXmssSecurity.D prims h (deriveKeys .prss i (aimedCorruptView D parts revealed i)))
  ⟨keys.2.1, keys.2.2⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The reference derivation never reads an honest private contribution. -/
theorem aimedReferenceKeys_exposed (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) :
    aimedReferenceKeys prims D h table (keygenExposedParts D parts) revealed i =
      aimedReferenceKeys prims D h table parts revealed i := by
  have ht (T : C.Term) (hT : KnownTo D.1 T) (j : C.Party) :
      (aimedCorruptView D (keygenExposedParts D parts) revealed i j).term T =
        (aimedCorruptView D parts revealed i j).term T := by
    unfold aimedCorruptView
    split_ifs <;> simp [keygenExposedParts, hT]
  have hp (a b : C.Party) (hab : a ∈ D.1 ∨ b ∈ D.1) :
      (aimedCorruptView D (keygenExposedParts D parts) revealed i a).pair b =
        (aimedCorruptView D parts revealed i a).pair b := by
    unfold aimedCorruptView
    split_ifs <;> simp [keygenExposedParts, hab]
  simp only [aimedReferenceKeys, keygenMaskKeys, D_deriveKeys]
  congr 1
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp only [if_pos hT, ht T hT]
    · simp only [if_neg hT]
  · funext j
    by_cases hj : j = i
    · simp [hj]
    · simp only [dif_neg hj]
      by_cases hc : i ∈ D.1 ∨ j ∈ D.1
      · simp only [if_pos hc]
        have he : (C.pairOf i j (Ne.symm hj)).1.1 ∈ D.1 ∨
            (C.pairOf i j (Ne.symm hj)).1.2 ∈ D.1 := by
          unfold Committee.pairOf
          split_ifs <;> simp_all [or_comm]
        simp only [hp _ _ he, hp _ _ he.symm]
      · simp only [if_neg hc]

/-- Installing the canonical hash answers in the named table leaves the actual keys unchanged. -/
theorem aimedReferenceKeys_canonical (D : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1)
    (hreceived : ∀ j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .prss (parts j) j i) :
    aimedReferenceKeys prims D h (fun n => h (hiddenInput parts n)) parts revealed i =
      let keys := ThresholdLeanXmssSecurity.D prims h (deriveKeys .prss i (prssView parts revealed i))
      (⟨keys.2.1, keys.2.2⟩ : PrssKeys C) := by
  rw [aimed_derived_corruptView prims D parts revealed i hi hreceived h]
  simp only [aimedReferenceKeys, keygenMaskKeys, D_deriveKeys]
  congr 1
  · funext T
    by_cases hT : KnownTo D.1 T
    · simp only [if_pos hT]
    · simp only [if_neg hT]
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT, hiddenInput, prssTermInput]
        apply congrArg h
        apply congrArg (Query.derive .prss .term)
        apply List.map_congr_left
        intro j hj
        have hjT : j ∈ C.holders T := of_decide_eq_true (List.mem_filter.mp hj).2
        simp only [aimedCorruptView, if_neg (hidden_term_holders D hT j hjT)]
      · simp only [if_neg hiT]
  · funext j
    by_cases hji : j = i
    · simp only [dif_pos hji]
    · simp only [dif_neg hji]
      by_cases hj : j ∈ D.1
      · simp only [if_pos (Or.inr hj)]
      · have hp : Hidden D (.pair (C.pairOf i j (Ne.symm hji))) := by
          unfold Hidden Committee.pairOf
          split_ifs <;> simp [hi, hj]
        simp only [if_neg (not_or.mpr ⟨hi, hj⟩), hiddenInput, prssPairInput,
          aimedCorruptView, if_neg hp.1, if_neg hp.2]

def aimedPrssSwap (D : C.Coalition) (a b : HashOutput) (i : C.Party)
    (out : PrssKeys C) : PrssKeys C :=
  { term := fun T => if Hidden D (.term T) then Equiv.swap a b (out.term T) else out.term T
    pair := fun j => if h : j = i then out.pair j else
      if Hidden D (.pair (C.pairOf i j (Ne.symm h))) then Equiv.swap a b (out.pair j)
      else out.pair j }

/-- Renaming changes the hidden row keys, retaining the already sent echo hashes. -/
def aimedRowsSwap (D : C.Coalition) (a b : HashOutput) (rows : RevealRows C) : RevealRows C :=
  fun i => (rows i).map (fun row => (aimedPrssSwap D a b i row.1, row.2))

theorem aimedPrssSwap_validKey (D : C.Coalition) (a b : HashOutput) (i : C.Party)
    (out : PrssKeys C) (n : KeyName C) (k : HashOutput) :
    ValidKey i (aimedPrssSwap D a b i out) n
      (if Hidden D n then Equiv.swap a b k else k) ↔ ValidKey i out n k := by
  cases n with
  | parameter => rfl
  | term T =>
    simp only [ValidKey, aimedPrssSwap]
    split_ifs <;> simp
  | pair p =>
    simp only [ValidKey, aimedPrssSwap]
    constructor
    · rintro ⟨j, hj, he, hk⟩
      refine ⟨j, hj, he, ?_⟩
      subst p
      simp only [dif_neg hj] at hk
      split_ifs at hk <;> simpa using hk
    · rintro ⟨j, hj, he, hk⟩
      refine ⟨j, hj, he, ?_⟩
      subst p
      simp only [dif_neg hj]
      split_ifs <;> simp [hk]

theorem aimedRowsSwap_rowKey (D : C.Coalition) (a b : HashOutput)
    (rows : RevealRows C) (n : KeyName C) (k : HashOutput) :
    RowKey (aimedRowsSwap D a b rows) n
      (if Hidden D n then Equiv.swap a b k else k) ↔ RowKey rows n k := by
  constructor
  · rintro ⟨i, keys, shared, hr, hv⟩
    unfold aimedRowsSwap at hr
    obtain ⟨⟨out, echo⟩, he, he'⟩ := Option.map_eq_some_iff.mp hr
    cases he'
    exact ⟨i, out, echo, he, (aimedPrssSwap_validKey D a b i out n k).mp hv⟩
  · rintro ⟨i, keys, shared, hr, hv⟩
    refine ⟨i, aimedPrssSwap D a b i keys, shared, ?_,
      (aimedPrssSwap_validKey D a b i keys n k).mpr hv⟩
    simp only [aimedRowsSwap, hr, Option.map_some]

omit [Fintype E] [DecidableEq E] in
theorem renameStep_suspend_prssFinish (top : TopTree) (tree : Tree) (D : C.Coalition)
    (a b : HashOutput) (x : C.Party → Keys C) (i : C.Party)
    (row : Option (PrssKeys C × List HashOutput)) :
    renameStep D a b (suspendStep (fun prss =>
      (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree : PartyM C E RealSpec TreeOutput))
        (prssFinishStep i row)) =
    suspendStep (fun prss =>
      (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree : PartyM C E RealSpec TreeOutput))
        (prssFinishStep i (row.map (fun r => (aimedPrssSwap D a b i r.1, r.2)))) := by
  cases row with
  | none => rfl
  | some row =>
    rcases row with ⟨out, shared⟩
    simp only [prssFinishStep, suspendStep, renameStep, Option.map_some]
    congr 1
    funext inbox
    unfold exchangeResume
    split_ifs
    · simp
    · change (renameParty D a b
        (((do require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0])
              pure out) >>= fun prss => ceremonyAfterSetup K circuits settings
            ⟨i, x i, prss⟩ top tree) : PartyM C E RealSpec TreeOutput)).run = _
      simp only [bind_assoc, pure_bind, renameParty_bind, renameParty_require]
      rw [rename_ceremonyAfterSetup]
      change _ = ((do
        require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0])
        pure (aimedPrssSwap D a b i out)) >>= fun prss =>
          (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree :
            PartyM C E RealSpec TreeOutput)).run
      simp only [bind_assoc, pure_bind]
      rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Self echoes are neither sent nor checked, so only distinct-party positions matter. -/
theorem aimedFinishStep_echo_congr (i : C.Party) (out : PrssKeys C)
    (shared shared' : List HashOutput)
    (he : ∀ j : C.Party, j ≠ i → shared.getD j.val 0 = shared'.getD j.val 0) :
    prssFinishStep (E := E) i (some (out, shared)) = prssFinishStep i (some (out, shared')) := by
  simp only [prssFinishStep]
  congr 1
  · funext j
    by_cases hj : j = i
    · simp only [if_pos hj]
    · simp only [if_neg hj, he j hj]
  · funext received
    have hc : (∀ j, j ≠ i → Msg.hashesOf (received j) = [shared.getD j.val 0]) ↔
        (∀ j, j ≠ i → Msg.hashesOf (received j) = [shared'.getD j.val 0]) := by
      apply forall_congr'
      intro j
      by_cases hj : j = i
      · simp only [hj, ne_eq, not_true_eq_false, false_implies]
      · simp only [he j hj]
    simp only [exchangeResume, hc]

omit [Fintype E] [DecidableEq E] in
/-- The complete continuation commutes with a swap of hidden keys, including the echo round. -/
theorem afterDerivation_rename (top : TopTree) (tree : Tree) (D : C.Coalition)
    (a b : HashOutput) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (rows : RevealRows C) :
    simulateQ (worldStreamRename D a b)
      (afterDerivation K circuits settings top tree D A x Z (st, some rows)) =
    afterDerivation K circuits settings top tree D A x Z (st, some (aimedRowsSwap D a b rows)) := by
  simp only [afterDerivation, simulateQ_bind, worldStreamRename_adversary,
    ← executeRounds_rename]
  simp only [renameStep_suspend_prssFinish, aimedRowsSwap]

omit [Fintype E] [DecidableEq E] in
/-- The swap transports the private AES cache while preserving the hash cache and the flag.
The watched keys remain those of `watched`, even when the executing rows are renamed. -/
theorem evalDist_afterDerivation_aimed_swap (top : TopTree) (tree : Tree) (D : C.Coalition)
    (a b : HashOutput) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (watched rows : RevealRows C)
    (s : (HashCache C × KeyCache C) × Bool) :
    𝒟[Prod.map id (aimedStateSwap D a b) <$>
      (simulateQ (lazyAimedImpl prims D watched)
        (afterDerivation K circuits settings top tree D A x Z (st, some rows))).run s] =
    𝒟[(simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (st, some (aimedRowsSwap D a b rows)))).run (aimedStateSwap D a b s)] := by
  rw [evalDist_lazyAimed_rename, afterDerivation_rename]

omit [Fintype E] [DecidableEq E] in
/-- At the boundary the private cache is empty, so the flag's law is invariant under the swap. -/
theorem probEvent_afterDerivation_aimed_swap (top : TopTree) (tree : Tree) (D : C.Coalition)
    (a b : HashOutput) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (st, some (aimedRowsSwap D a b rows)))).run ((h, ∅), false)] := by
  have he := evalDist_afterDerivation_aimed_swap prims K circuits settings top tree D a b A x Z st
    watched rows ((h, ∅), false)
  have hp := probEvent_congr' (p := fun y => y.2.2 = true) (fun _ _ => Iff.rfl) he
  simpa only [probEvent_map, Function.comp_def, Prod.map, aimedStateSwap,
    keyCacheSwap, involutionCache_empty] using hp

omit [Fintype E] [DecidableEq E] in
/-- Any finite chain of swaps preserves the flag probability. -/
theorem probEvent_afterDerivation_aimed_swaps (top : TopTree) (tree : Tree) (D : C.Coalition)
    (swaps : List (HashOutput × HashOutput)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (st, some (swaps.foldl (fun rs ab => aimedRowsSwap D ab.1 ab.2 rs) rows)))).run
          ((h, ∅), false)] := by
  induction swaps generalizing rows with
  | nil => rfl
  | cons ab swaps ih =>
    exact (probEvent_afterDerivation_aimed_swap prims K circuits settings top tree D ab.1 ab.2 A x Z
      st watched rows h).trans (ih (aimedRowsSwap D ab.1 ab.2 rows))

omit [Fintype E] [DecidableEq E] in
/-- The chain may be selected using fresh independent uniform values. This preserves the
flag's law; showing that the resulting computation is independent of the watched keys is separate. -/
theorem probEvent_afterDerivation_aimed_randomSwaps (top : TopTree) (tree : Tree) (D : C.Coalition)
    (m : ℕ) (swaps : (Fin m → HashOutput) → List (HashOutput × HashOutput))
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | $ᵗ (Fin m → HashOutput) >>= fun u =>
      (simulateQ (lazyAimedImpl prims D watched)
        (afterDerivation K circuits settings top tree D A x Z
          (st, some ((swaps u).foldl (fun rs ab => aimedRowsSwap D ab.1 ab.2 rs) rows)))).run
            ((h, ∅), false)] := by
  rw [probEvent_bind_of_const _ (fun u _ =>
    (probEvent_afterDerivation_aimed_swaps prims K circuits settings top tree D (swaps u)
      A x Z st watched rows h).symm)]
  simp

def aimedPrssPerm (D : C.Coalition) (σ : Equiv.Perm HashOutput) (i : C.Party)
    (out : PrssKeys C) : PrssKeys C :=
  { term := fun T => if Hidden D (.term T) then σ (out.term T) else out.term T
    pair := fun j => if h : j = i then out.pair j else
      if Hidden D (.pair (C.pairOf i j (Ne.symm h))) then σ (out.pair j) else out.pair j }

def aimedRowsPerm (D : C.Coalition) (σ : Equiv.Perm HashOutput) (rows : RevealRows C) : RevealRows C :=
  fun i => (rows i).map (fun row => (aimedPrssPerm D σ i row.1, row.2))

theorem aimedRowsPerm_one (D : C.Coalition) (rows : RevealRows C) :
    aimedRowsPerm D 1 rows = rows := by
  funext i
  cases hrow : rows i with
  | none => simp [aimedRowsPerm, hrow]
  | some row =>
    simp only [aimedRowsPerm, hrow, Option.map_some]
    congr 2
    rcases row with ⟨⟨term, pair⟩, shared⟩
    simp [aimedPrssPerm]

theorem aimedRowsPerm_swap_mul (D : C.Coalition) (σ : Equiv.Perm HashOutput)
    (a b : HashOutput) (rows : RevealRows C) :
    aimedRowsPerm D (Equiv.swap a b * σ) rows =
      aimedRowsSwap D a b (aimedRowsPerm D σ rows) := by
  funext i
  cases hrow : rows i with
  | none => simp [aimedRowsPerm, aimedRowsSwap, hrow]
  | some row =>
    simp only [aimedRowsPerm, aimedRowsSwap, hrow, Option.map_some]
    congr 2
    unfold aimedPrssPerm aimedPrssSwap
    congr 1
    · funext T
      dsimp only
      split_ifs <;> rfl
    · funext j
      dsimp only
      split_ifs <;> rfl

def aimedRowsMask (D : C.Coalition) (table : KeyName C → HashOutput) (rows : RevealRows C) : RevealRows C :=
  fun i => (rows i).map fun row =>
    let masked := keygenMaskKeys D table i (0, row.1.term, row.1.pair)
    (⟨masked.2.1, masked.2.2⟩, row.2)

theorem aimedRowsPerm_mask (D : C.Coalition) (σ : Equiv.Perm HashOutput)
    (hs : σ 0 = 0) (left right : KeyName C → HashOutput) (rows : RevealRows C)
    (ht : ∀ n, Hidden D n → (∃ k, RowKey rows n k) → σ (left n) = right n) :
    aimedRowsPerm D σ (aimedRowsMask D left rows) = aimedRowsMask D right rows := by
  funext i
  cases hrow : rows i with
  | none => simp [aimedRowsMask, aimedRowsPerm, hrow]
  | some row =>
    simp only [aimedRowsMask, aimedRowsPerm, hrow, Option.map_some]
    congr 2
    unfold aimedPrssPerm keygenMaskKeys
    congr 1
    · funext T
      dsimp only
      by_cases hT : KnownTo D.1 T
      · simp only [Hidden, hT, not_true_eq_false, if_false, if_true]
      · simp only [Hidden, hT, not_false_eq_true, if_true, if_false]
        by_cases hiT : i ∈ C.holders T
        · simp only [if_pos hiT]
          exact ht (.term T) hT ⟨row.1.term T, i, row.1, row.2, hrow, hiT, rfl⟩
        · simp only [if_neg hiT, hs]
    · funext j
      dsimp only
      by_cases hji : j = i
      · simp only [dif_pos hji]
      · simp only [dif_neg hji]
        have he : Hidden D (.pair (C.pairOf i j (Ne.symm hji))) ↔ ¬(i ∈ D.1 ∨ j ∈ D.1) := by
          unfold Hidden Committee.pairOf
          split_ifs <;> simp [not_or, and_comm]
        by_cases hc : i ∈ D.1 ∨ j ∈ D.1
        · simp only [if_pos hc, if_neg (fun h => (he.mp h) hc)]
        · simp only [if_neg hc, if_pos (he.mpr hc)]
          exact ht (.pair (C.pairOf i j (Ne.symm hji))) (he.mpr hc)
            ⟨row.1.pair j, i, row.1, row.2, hrow, j, hji, rfl, rfl⟩

theorem aimedRowsMask_hiddenKey (D : C.Coalition) (table : KeyName C → HashOutput)
    (rows : RevealRows C) (n : KeyName C) (hn : Hidden D n)
    (hr : ∃ k, RowKey rows n k) : RowKey (aimedRowsMask D table rows) n (table n) := by
  obtain ⟨k, i, keys, shared, hi, hk⟩ := hr
  let masked := keygenMaskKeys D table i (0, keys.term, keys.pair)
  refine ⟨i, ⟨masked.2.1, masked.2.2⟩, shared, ?_, ?_⟩
  · simp only [aimedRowsMask, hi, Option.map_some, masked]
  · cases n with
    | parameter => exact hn.elim
    | term T =>
      refine ⟨hk.1, ?_⟩
      simp only [masked, keygenMaskKeys, if_neg hn, if_pos hk.1]
    | pair p =>
      obtain ⟨j, hji, rfl, he⟩ := hk
      have hc : ¬(i ∈ D.1 ∨ j ∈ D.1) := by
        have hh := hn
        unfold Hidden Committee.pairOf at hh
        split_ifs at hh <;> simp_all
      exact ⟨j, hji, rfl, by simp only [masked, keygenMaskKeys, dif_neg hji, if_neg hc]⟩

theorem aimedRowsMask_injective (D : C.Coalition) (table : KeyName C → HashOutput)
    (rows : RevealRows C) (ha : KeysApart D (aimedRowsMask D table rows)) :
    Function.Injective (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => table n) := by
  intro a b hab
  apply Subtype.ext
  by_contra hn
  exact ha a (table a) b (table b)
    (aimedRowsMask_hiddenKey D table rows a a.property.1 a.property.2) a.property.1
    (aimedRowsMask_hiddenKey D table rows b b.property.1 b.property.2) hn hab

theorem aimed_exists_perm_fix_zero {ι : Type} [Finite ι]
    (f g : ι → HashOutput) (hf : Function.Injective f) (hg : Function.Injective g)
    (hf0 : ∀ i, f i ≠ 0) (hg0 : ∀ i, g i ≠ 0) :
    ∃ σ : Equiv.Perm HashOutput, σ 0 = 0 ∧ ∀ i, σ (f i) = g i := by
  let f' : Option ι → HashOutput := fun i => i.elim 0 f
  let g' : Option ι → HashOutput := fun i => i.elim 0 g
  have hf' : Function.Injective f' := by
    intro i j he
    cases i with
    | none => cases j with
      | none => rfl
      | some j => exact (hf0 j he.symm).elim
    | some i => cases j with
      | none => exact (hf0 i he).elim
      | some j => exact congrArg some (hf he)
  have hg' : Function.Injective g' := by
    intro i j he
    cases i with
    | none => cases j with
      | none => rfl
      | some j => exact (hg0 j he.symm).elim
    | some i => cases j with
      | none => exact (hg0 i he).elim
      | some j => exact congrArg some (hg he)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f' g' hf' hg'
  exact ⟨σ, hσ none, fun i => hσ (some i)⟩

omit [Fintype E] [DecidableEq E] in
/-- Every permutation of hidden raw keys preserves the continuation's flag probability. -/
theorem probEvent_afterDerivation_aimed_perm (top : TopTree) (tree : Tree) (D : C.Coalition)
    (σ : Equiv.Perm HashOutput) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (watched rows : RevealRows C) (h : HashCache C) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z (st, some rows))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (st, some (aimedRowsPerm D σ rows)))).run ((h, ∅), false)] := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [aimedRowsPerm_one]
  | swap_mul σ a b hab ih =>
    rw [aimedRowsPerm_swap_mul]
    exact ih.trans (probEvent_afterDerivation_aimed_swap prims K circuits settings top tree D a b
      A x Z st watched (aimedRowsPerm D σ rows) h)

omit [Fintype E] [DecidableEq E] in
/-- With distinct nonzero hidden keys, the executing keys may be replaced by any injective
named table. The watched keys and stored echo hashes stay fixed. -/
theorem probEvent_afterDerivation_aimed_mask (top : TopTree) (tree : Tree) (D : C.Coalition)
    (left right : KeyName C → HashOutput) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (st : A.State) (watched rows : RevealRows C) (h : HashCache C)
    (ha : KeysApart D (aimedRowsMask D left rows))
    (hr : Function.Injective
      (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => right n))
    (hl0 : ∀ n, Hidden D n → (∃ k, RowKey rows n k) → left n ≠ 0)
    (hr0 : ∀ n, Hidden D n → (∃ k, RowKey rows n k) → right n ≠ 0) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (st, some (aimedRowsMask D left rows)))).run ((h, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (st, some (aimedRowsMask D right rows)))).run ((h, ∅), false)] := by
  obtain ⟨σ, hs, ht⟩ := aimed_exists_perm_fix_zero
    (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => left n)
    (fun n : {n : KeyName C // Hidden D n ∧ ∃ k, RowKey rows n k} => right n)
    (aimedRowsMask_injective D left rows ha) hr
    (fun n => hl0 n n.property.1 n.property.2) (fun n => hr0 n n.property.1 n.property.2)
  have he := probEvent_afterDerivation_aimed_perm prims K circuits settings top tree D σ A x Z
    st watched (aimedRowsMask D left rows) h
  rw [aimedRowsPerm_mask D σ hs left right rows (fun n hn hrow => ht ⟨n, hn, hrow⟩)] at he
  exact he

/-- The single stream-key candidate of a counted call. -/
def aimedPoint : (WorldSpec C).Domain → HashOutput
  | .inl (.inl (.inr (.inl (.streamKey k)))) => k
  | .inl (.inl (.inr (.inr x))) => x.2.1
  | .inl (.inr (.streamKey k, _)) => k
  | _ => 0

theorem aimedCall_point (D : C.Coalition) (rows : RevealRows C) (t : (WorldSpec C).Domain) :
    AimedCall D rows t →
      WorldCounted t ∧ ∃ n, RowKey rows n (aimedPoint t) ∧ Hidden D n := by
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  all_goals simp only [AimedCall, Caches]
  · simp
  · cases q <;> simp [aimedPoint, WorldCounted, Counted]
  · rintro ⟨n, k, hk, hn, he⟩
    have he' := Query.streamKey.inj he
    subst k
    exact ⟨trivial, n, hk, hn⟩
  · cases q <;> simp [aimedPoint, WorldCounted]
  all_goals simp

/-- Once the watched row keys are independent uniform coordinates, a call aims at one of them
with probability at most `m / 2^256`. -/
theorem probEvent_aimedCall_uniform_le (D : C.Coalition) (m : ℕ)
    (rows : (Fin m → HashOutput) → RevealRows C)
    (hrows : ∀ u n k, RowKey (rows u) n k → Hidden D n → ∃ j, u j = k)
    (t : (WorldSpec C).Domain) :
    Pr[fun u => AimedCall D (rows u) t | $ᵗ (Fin m → HashOutput)] ≤ (m : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_mono (q := fun u => ∃ j, u j = aimedPoint t) (fun u _ hu => ?_)).trans ?_
  · obtain ⟨_, n, hk, hn⟩ := aimedCall_point D (rows u) t hu
    exact hrows u n _ hk hn
  · have hc : Fintype.card HashOutput = 2 ^ 256 := by
      unfold HashOutput hashOutputBits
      exact card_bitVec 256
    simpa only [hc, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using
      probEvent_uniform_exists_eq_le m (aimedPoint t)

/-- Adaptive calls obey the uniform bound when the computation and handler do not read the
watched coordinates. Establishing this independence for the boundary cache is still necessary. -/
theorem probEvent_aimed_uniform_le {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition) (m : ℕ)
    (rows : (Fin m → HashOutput) → RevealRows C)
    (hrows : ∀ u n k, RowKey (rows u) n k → Hidden D n → ∃ j, u j = k)
    (game : OracleComp (WorldSpec C) α) (q : ℕ) (hq : IsQueryBoundP game WorldCounted q)
    (s : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (Fin m → HashOutput) >>= fun u =>
      (simulateQ (flagImpl impl (fun t u => AimedCall D (rows u) t) u) game).run (s, false)] ≤
      (q : ℝ≥0∞) * m / 2 ^ 256 := by
  refine (probEvent_flag_le impl _ _ WorldCounted ((m : ℝ≥0∞) / 2 ^ 256)
    (fun t u hu => (aimedCall_point D (rows u) t hu).1)
    (fun t _ => probEvent_aimedCall_uniform_le D m rows hrows t) game q s hq).trans ?_
  exact le_of_eq (mul_div_assoc _ _ _).symm

omit [Fintype E] [DecidableEq E] in
/-- Only adversary rounds and the final distinguisher contribute counted calls after derivation. -/
theorem isQueryBoundP_afterDerivation (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final)
    (r : A.State × Option (RevealRows C)) :
    IsQueryBoundP (afterDerivation K circuits settings top tree D A x Z r) WorldCounted
      ((ceremonyFuel circuits settings - 2) * step + final) := by
  rcases r with ⟨st, _ | rows⟩
  · exact (isQueryBoundP_adversary _ final (hfinal _)).mono (Nat.le_add_left _ _)
  · simp only [afterDerivation]
    generalize ceremonyFuel circuits settings - 2 = fuel
    apply isQueryBoundP_bind
    · exact
      (isQueryBoundP_executeRounds D A noFunctionality step hround
        (fun state inputs => isQueryBoundP_runFunctionality_noFunctionality D A state inputs step)
        _ st _)
    · exact fun r _ => isQueryBoundP_adversary _ final (hfinal r)

/-- Every hidden row key is the answer at its canonical derivation input. -/
theorem aimed_hidden_rowKey_cached {E : Type} (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : RevealRows C × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s))
    (n : KeyName C) (k : HashOutput) (hk : RowKey r.1 n k) (hn : Hidden D n) :
    r.2 (hiddenInput parts n) = some k := by
  obtain ⟨i, _, ha, y, hy, hc⟩ := rowKey_query prims D active parts committed sent s r hr n k hk
  obtain ⟨he, _⟩ := hidden_rowQuery D active parts sent i ha n hn y hy
  exact he ▸ hc

/-- Different honest rows cannot disagree on a hidden name's key. -/
theorem aimed_hidden_rowKey_unique {E : Type} (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : RevealRows C × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s))
    (n : KeyName C) (k k' : HashOutput) (hk : RowKey r.1 n k) (hk' : RowKey r.1 n k')
    (hn : Hidden D n) : k = k' := by
  exact Option.some.inj
    ((aimed_hidden_rowKey_cached prims D active parts committed sent s r hr n k hk hn).symm.trans
      (aimed_hidden_rowKey_cached prims D active parts committed sent s r hr n k' hk' hn))

/-- Instrument the program itself, so that its flag survives elimination of oracle caches. -/
def aimedFlagQueries (D : C.Coalition) (rows : RevealRows C) :
    QueryImpl (WorldSpec C) (StateT Bool (OracleComp (WorldSpec C))) :=
  fun t => StateT.mk fun b => (fun a => (a, b || decide (AimedCall D rows t))) <$>
    OracleComp.lift (OracleSpec.query (spec := WorldSpec C) t)

theorem run_aimedFlagQueries {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (rows : RevealRows C) (game : OracleComp (WorldSpec C) α)
    (b : Bool) (s : σ) :
    (simulateQ impl ((simulateQ (aimedFlagQueries D rows) game).run b)).run s =
      (fun r => ((r.1, r.2.2), r.2.1)) <$>
        (simulateQ (flagImpl impl (fun t (_ : Unit) => AimedCall D rows t) ()) game).run (s, b) := by
  induction game using OracleComp.inductionOn generalizing b s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, aimedFlagQueries,
      StateT.run_mk, flagImpl, bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 (b || decide (AimedCall D rows t)) r.2

theorem evalDist_lazyKeyWorld_noFreeStream {α : Type} (D : C.Coalition)
    (game : OracleComp (WorldSpec C) α) (hg : IsQueryBoundP game FreeStream 0)
    (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D) game).run (s, ∅)] =
      𝒟[(fun r => (r.1, (r.2, (∅ : KeyCache C)))) <$>
        (simulateQ (worldAnswer prims) game).run s] := by
  have he := evalDist_simulateQ_state_projection (jointKeyWorld prims D false) (lazyKeyWorld prims D)
    keyJointIdealProjection (jointKeyWorld_false_query_projection prims D) game (boundaryState s)
  rw [jointKeyWorld_false_simulate_eq prims D game hg (boundaryState s) (by intro k; rfl)] at he
  have hempty : truncateKeyCache (∅ : FullKeyCache C) = ∅ := by funext y; rfl
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq,
    keyJointIdealProjection, boundaryState, hempty] using he.symm

def aimedFlagProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (WorldSpec C) ((A.State × Option (RevealRows C)) × (Bool × Bool)) := do
  let r ← setupPrefix D A x z
  (fun y => (r, y)) <$> (simulateQ (aimedFlagQueries D (rowsOf r.2))
    (afterDerivation K circuits settings top tree D A x Z r)).run false

omit [Fintype E] [DecidableEq E] in
/-- The eager-AES theorem can now be applied to a program whose output contains the flag. -/
theorem evalDist_aimedFlagProgram_keys (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    𝒟[(simulateQ (lazyKeyWorld prims D)
      (aimedFlagProgram K circuits settings top tree D A x z Z)).run' (∅, ∅)] =
    𝒟[($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
      (simulateQ (keyWorld prims D keys)
        (aimedFlagProgram K circuits settings top tree D A x z Z)).run' ∅] := by
  simpa only [tableExtending_empty] using
    evalDist_lazyKeyWorld prims D (aimedFlagProgram K circuits settings top tree D A x z Z) ∅ ∅

omit [Fintype E] [DecidableEq E] in
theorem evalDist_aimedFlagProgram_projection (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    𝒟[(simulateQ (lazyKeyWorld prims D)
      (aimedFlagProgram K circuits settings top tree D A x z Z)).run' (∅, ∅)] =
    𝒟[(fun y => (y.1.1, (y.2.1, y.2.2.2))) <$>
      lazyAimedBoundaryRun prims K circuits settings top tree D A x z Z] := by
  simp only [aimedFlagProgram, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, lazyAimedBoundaryRun]
  rw [evalDist_bind, evalDist_lazyKeyWorld_noFreeStream prims D _ (qb0_setupPrefix D A x z)]
  simp only [evalDist_map, bind_map_left, evalDist_bind, worldRun]
  congr 1
  funext r
  rw [run_aimedFlagQueries]
  simp only [evalDist_map, Functor.map_map, lazyAimedImpl]

/-- Programming belongs to the simulator interface; the real experiment never uses it. -/
def AimedProgramCall : (WorldSpec C).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

theorem aimed_noProgram_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) (AimedProgramCall (C := C)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [worldRoles, counted, liftComp_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

theorem aimed_noProgram_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (free oa) (AimedProgramCall (C := C)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [free]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem aimed_noProgram_rounds {Ia α : Type} (D : C.Coalition)
    (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps)
        AimedProgramCall 0
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    rw [executeRounds_succ]
    split_ifs
    · simp
    · refine qb0_bind ?_ fun r => aimed_noProgram_rounds D A fuel r.1 r.2.1
      unfold stepRound
      split_ifs
      · refine qb0_bind ?_ fun _ => qb0_bind (isQueryBoundP_sequenceFin _ fun i => ?_) fun _ => by simp
        · simp [runFunctionality, noFunctionality]
        · rcases steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
          · simp
          · simp
          · dsimp only; split_ifs <;> first | exact aimed_noProgram_free _ | simp
      · refine qb0_bind (aimed_noProgram_adversary _) fun _ =>
          qb0_bind (isQueryBoundP_sequenceFin _ fun i => ?_) fun _ => by simp
        rcases steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
        · simp
        · dsimp only; split_ifs <;> first | exact aimed_noProgram_free _ | simp
        · simp

omit [Fintype E] [DecidableEq E] in
theorem aimed_noProgram_afterDerivation (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (r : A.State × Option (RevealRows C)) :
    IsQueryBoundP (afterDerivation K circuits settings top tree D A x Z r) AimedProgramCall 0 := by
  rcases r with ⟨st, rows⟩
  cases rows with
  | none => exact aimed_noProgram_adversary _
  | some rows =>
    unfold afterDerivation
    generalize ceremonyFuel circuits settings - 2 = fuel
    exact qb0_bind (aimed_noProgram_rounds D A fuel _ _) fun r => aimed_noProgram_adversary _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem aimed_noProgram_setupPrefix (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    IsQueryBoundP (setupPrefix D A x z) AimedProgramCall 0 := by
  unfold setupPrefix
  refine qb0_bind (aimed_noProgram_adversary _) fun _ =>
    qb0_bind (aimed_noProgram_free _) fun _ => qb0_bind (aimed_noProgram_adversary _) fun r => ?_
  rcases r with ⟨st, sent, revealed⟩
  cases revealed with
  | none => simp
  | some sent' => exact qb0_bind (aimed_noProgram_free _) fun _ => by simp

theorem aimed_noProgram_flag {α : Type} (D : C.Coalition) (rows : RevealRows C)
    (game : OracleComp (WorldSpec C) α) (hg : IsQueryBoundP game AimedProgramCall 0) (b : Bool) :
    IsQueryBoundP ((simulateQ (aimedFlagQueries D rows) game).run b) AimedProgramCall 0 := by
  induction game using OracleComp.inductionOn generalizing b with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hg
    have ht : ¬ AimedProgramCall t := hg.1.resolve_right (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, aimedFlagQueries,
      StateT.run_mk, bind_map_left]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ht, fun u => ?_⟩
    simpa only [Nat.zero_sub, ite_self] using ih u (by simpa using hg.2 u) (b || decide (AimedCall D rows t))

omit [Fintype E] [DecidableEq E] in
theorem aimed_noProgram_flagProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (aimedFlagProgram K circuits settings top tree D A x z Z) AimedProgramCall 0 := by
  unfold aimedFlagProgram
  refine qb0_bind (aimed_noProgram_setupPrefix D A x z) fun r => ?_
  rw [map_eq_bind_pure_comp]
  exact qb0_bind (aimed_noProgram_flag D _ _
    (aimed_noProgram_afterDerivation K circuits settings top tree D A x Z r) false) fun _ => by simp

/-- Fixed-oracle evaluation of the reveal computation. -/
theorem aimed_prssLocalAt_eq (h : Query C → HashOutput) :
    prssLocalAt prims h = fixedLocal prims (prssHashAt prims h) := by
  funext t
  rcases t with n | q | x <;> rfl

def aimedRevealDataFixed (h : Query C → HashOutput) (i : C.Party)
    (own : Parts C) (committed revealed : Mail C E) : Option (PrssKeys C × List HashOutput) :=
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then none else
    if prssOpenCheck i own committed revealed
        (C.parties.map fun j => h (.commit .prss j i (Msg.hashesOf (revealed j)))) then
      let keys := ThresholdLeanXmssSecurity.D prims h
        (deriveKeys .prss i (fun j => if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j))
      some (⟨keys.2.1, keys.2.2⟩,
        C.parties.map fun j => h (.sharedKeys .prss ((sharedTerms i j).map keys.2.1)))
    else none

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem aimedRevealDataFixed_run (h : Query C → HashOutput) (i : C.Party)
    (own : Parts C) (committed revealed : Mail C E) :
    simulateQ (fixedLocal prims h) (prssRevealData i own committed revealed) =
      pure (aimedRevealDataFixed prims h i own committed revealed) := by
  unfold prssRevealData aimedRevealDataFixed
  by_cases ha : (C.parties.any fun j => Msg.isAbort (revealed j)) = true
  · simp only [if_pos ha, simulateQ_pure]
  · simp only [if_neg ha, prssPostRevealData, simulateQ_bind, simulateQ_fixedLocal_liftComp,
      D_mapM, D_hashQuery, pure_bind]
    split_ifs <;> simp only [simulateQ_bind, simulateQ_fixedLocal_liftComp,
      D_mapM, D_hashQuery, pure_bind, simulateQ_pure]

/-- Honest abort messages depend on activity, never on the revealed contribution. -/
def aimedRevealAborted (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ D.1 then Msg.isAbort (sent j i) else decide (¬ active j)

theorem aimedRevealInbox_aborted (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) =
      aimedRevealAborted D active sent i := by
  unfold aimedRevealAborted
  congr 1
  funext j
  by_cases hj : j ∈ D.1 <;> by_cases ha : active j <;>
    simp [prssRevealInbox, prssRevealOutbox, hj, ha, Msg.isAbort]

def aimedReferenceOpenCheck (D : C.Coalition) (h : Query C → HashOutput)
    (sentCommit sentReveal : C.Party → Mail C E) (i : C.Party) : Prop :=
  ∀ j, j ∈ D.1 → j ≠ i →
    (Msg.hashesOf (sentReveal j i)).length = (sharedTerms j i).length + 1 ∧
      [h (.commit .prss j i (Msg.hashesOf (sentReveal j i)))] = Msg.hashesOf (sentCommit j i)

theorem aimedOpenCheck_corrupt_iff (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (i : C.Party)
    (ha : aimedRevealAborted D active sentReveal i = false) :
    prssOpenCheck i (parts i) (prssCommitInbox D (prssDataAt h parts) sentCommit i)
      (prssRevealInbox D active parts sentReveal i)
      (C.parties.map fun j => h (.commit .prss j i
        (Msg.hashesOf (prssRevealInbox D active parts sentReveal i j)))) ↔
      aimedReferenceOpenCheck D h sentCommit sentReveal i := by
  have hc := prssOpenCheck_from_cache D i (prssDataAt h parts) active sentCommit sentReveal
    (C.parties.map fun j => h (.commit .prss j i
      (Msg.hashesOf (prssRevealInbox D active parts sentReveal i j)))) (fun q => some (h q))
    (by simpa only [prssDataAt, aimedRevealInbox_aborted] using ha)
    (by intro j hj; simp only [prssDataAt_commit]; rfl)
    (by intro j; simp [prssDataAt, Committee.parties, List.getD_eq_getElem?_getD])
  refine hc.trans ?_
  unfold prssCorruptOpenCheck aimedReferenceOpenCheck
  apply forall_congr'
  intro j
  by_cases hj : j ∈ D.1
  · simp [hj, Committee.parties, List.getD_eq_getElem?_getD, prssRevealInbox]
  · simp [hj]

def aimedReferenceRows (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sentCommit sentReveal : C.Party → Mail C E) : RevealRows C :=
  fun i => if i ∈ D.1 then none else if active i then
    if aimedRevealAborted D active sentReveal i then none else
      if aimedReferenceOpenCheck D h sentCommit sentReveal i then
        let keys := aimedReferenceKeys prims D h table parts (fun i j => sentReveal j i) i
        some (keys, C.parties.map fun j => h (.sharedKeys .prss ((sharedTerms i j).map keys.term)))
      else none
    else none

theorem aimedReferenceRows_exposed (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sentCommit sentReveal : C.Party → Mail C E) :
    aimedReferenceRows prims D h table active (keygenExposedParts D parts) sentCommit sentReveal =
      aimedReferenceRows prims D h table active parts sentCommit sentReveal := by
  funext i
  simp only [aimedReferenceRows, aimedReferenceKeys_exposed]

def aimedRevealRowsFixed (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) : RevealRows C :=
  fun i => if i ∈ D.1 then none else if active i then
    aimedRevealDataFixed prims h i (parts i) (committed i) (prssRevealInbox D active parts sent i)
    else none

theorem aimedRevealRowsFixed_canonical (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    aimedRowsMask D (fun n => h (hiddenInput parts n))
      (aimedRevealRowsFixed prims D h active parts committed sent) =
      aimedRevealRowsFixed prims D h active parts committed sent := by
  funext i
  unfold aimedRowsMask aimedRevealRowsFixed
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, Option.map_none]
  · simp only [if_neg hi]
    by_cases hac : active i
    · simp only [if_pos hac, aimedRevealDataFixed]
      by_cases ha : (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = true
      · simp only [if_pos ha, Option.map_none]
      · simp only [if_neg ha]
        split_ifs with ho
        · simp only [Option.map_some]
          have hreceived := prssRevealInbox_honest D active parts sent i (Bool.eq_false_iff.mpr ha)
          have he := aimedReferenceKeys_canonical prims D h parts
            (prssRevealInbox D active parts sent) i hi hreceived
          unfold aimedReferenceKeys at he
          rw [← aimed_derived_corruptView prims D parts _ i hi hreceived h] at he
          have hzero : (ThresholdLeanXmssSecurity.D prims h
              (deriveKeys .prss i (prssView parts (prssRevealInbox D active parts sent) i))).1 = 0 := by
            simp only [D_deriveKeys, reduceCtorEq, if_false]
          rw [← hzero]
          congr 2
        · rfl
    · simp only [if_neg hac, Option.map_none]

theorem aimedRevealRowsFixed_mask (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sentCommit sentReveal : C.Party → Mail C E) (i : C.Party) :
    Option.map (fun row : PrssKeys C × List HashOutput =>
      let masked := keygenMaskKeys D table i (0, row.1.term, row.1.pair)
      let keys : PrssKeys C := ⟨masked.2.1, masked.2.2⟩
      (keys, C.parties.map fun j => h (.sharedKeys .prss ((sharedTerms i j).map keys.term))))
      (aimedRevealRowsFixed prims D h active parts
        (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal i) =
      aimedReferenceRows prims D h table active parts sentCommit sentReveal i := by
  unfold aimedRevealRowsFixed aimedReferenceRows
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, Option.map_none]
  · simp only [if_neg hi]
    by_cases hac : active i
    · simp only [if_pos hac, aimedRevealDataFixed, aimedRevealInbox_aborted]
      by_cases ha : aimedRevealAborted D active sentReveal i = true
      · simp only [if_pos ha, Option.map_none]
      · simp only [if_neg ha]
        rw [aimedOpenCheck_corrupt_iff D h active parts sentCommit sentReveal i
          (Bool.eq_false_iff.mpr ha)]
        split_ifs with ho
        · simp only [Option.map_some]
          have hreceived := prssRevealInbox_honest D active parts sentReveal i
            (by rw [aimedRevealInbox_aborted]; exact Bool.eq_false_iff.mpr ha)
          have hv : aimedCorruptView D parts (prssRevealInbox D active parts sentReveal) i =
              aimedCorruptView D parts (fun i j => sentReveal j i) i := by
            funext j
            unfold aimedCorruptView
            split_ifs with hj
            · simp only [prssRevealInbox, if_pos hj]
            · rfl
          have hd := aimed_derived_corruptView prims D parts _ i hi hreceived h
          rw [hv] at hd
          change ThresholdLeanXmssSecurity.D prims h
            (deriveKeys .prss i (fun j => if j = i then parts i else
              readReveal .prss (Msg.hashesOf (prssRevealInbox D active parts sentReveal i j)) i j)) = _ at hd
          rw [hd]
          rfl
        · rfl
    · simp only [if_neg hac, Option.map_none]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem aimedRevealRowsFixed_run (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (prssRevealRows D active parts committed sent) =
      pure (aimedRevealRowsFixed prims D h active parts committed sent) := by
  rw [prssRevealRows, simulateQ_sequenceFin]
  trans Concrete.sequenceFin (fun i =>
    (pure (aimedRevealRowsFixed prims D h active parts committed sent i) : ProbComp _))
  · congr 1
    funext i
    unfold aimedRevealRowsFixed
    split_ifs
    · exact simulateQ_pure _ _
    · exact aimedRevealDataFixed_run prims h i _ _ _
    · exact simulateQ_pure _ _
  · exact sequenceFin_pure _

/-- Translate the real world to local queries after choosing the private AES table. -/
def aimedKeyLocal (D : C.Coalition) (keys : KeyName C × HashOutput → Digest) :
    QueryImpl (WorldSpec C) (OracleComp (LocalSpec C))
  | .inl (.inl t) => OracleComp.lift (OracleSpec.query t)
  | .inl (.inr _) => pure false
  | .inr (.inr (.inr x)) => if Hidden D x.1 then pure (prims.aes.eval (keys (x.1, x.2.1)) x.2.2)
      else OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))
  | .inr t => OracleComp.lift (OracleSpec.query t)

theorem simulateQ_aimedKeyLocal {α : Type} (D : C.Coalition)
    (keys : KeyName C × HashOutput → Digest) (game : OracleComp (WorldSpec C) α)
    (hg : IsQueryBoundP game AimedProgramCall 0) :
    simulateQ (localAnswer prims) (simulateQ (aimedKeyLocal prims D keys) game) =
      simulateQ (keyWorld prims D keys) game := by
  induction game using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hg
    have ht : ¬ AimedProgramCall t := hg.1.resolve_right (Nat.lt_irrefl 0)
    have hk : ∀ u, simulateQ (localAnswer prims) (simulateQ (aimedKeyLocal prims D keys) (k u)) =
        simulateQ (keyWorld prims D keys) (k u) := fun u => ih u (by simpa using hg.2 u)
    simp only [simulateQ_bind, simulateQ_spec_query, hk]
    congr 1
    rcases t with ((n | q | x) | p) | (n | q | x)
    all_goals simp only [aimedKeyLocal, keyWorld]
    all_goals try exact simulateQ_spec_query _ _
    · exact (ht trivial).elim
    · split_ifs
      · exact simulateQ_pure _ _
      · exact simulateQ_spec_query _ _

theorem aimedKeyLocal_adversary {α : Type} (D : C.Coalition)
    (keys : KeyName C × HashOutput → Digest) (oa : OracleComp (LocalSpec C) α) :
    simulateQ (aimedKeyLocal prims D keys) (worldRoles.adversary oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query, simulateQ_bind]
    simp only [ih]
    rfl

theorem aimedKeyLocal_free_noStream {α : Type} (D : C.Coalition)
    (keys : KeyName C × HashOutput → Digest) (oa : OracleComp (LocalSpec C) α)
    (hg : IsQueryBoundP oa LocalStream 0) :
    simulateQ (aimedKeyLocal prims D keys) (free oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hg
    have ht : ¬ LocalStream t := hg.1.resolve_right (Nat.lt_irrefl 0)
    have hk : ∀ u, simulateQ (aimedKeyLocal prims D keys) (free (k u)) = k u :=
      fun u => ih u (by simpa using hg.2 u)
    rw [free_bind, simulateQ_bind]
    simp only [hk]
    congr 1
    rcases t with n | q | x
    · exact simulateQ_spec_query _ _
    · exact simulateQ_spec_query _ _
    · exact (ht trivial).elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem aimedKeyLocal_setupPrefix (D : C.Coalition)
    (keys : KeyName C × HashOutput → Digest)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    simulateQ (aimedKeyLocal prims D keys) (setupPrefix D A x z) =
      (setupEarly D A (A.start (corruptInputs D x) z) >>= setupReveal D) := by
  simp only [setupPrefix, setupEarly, simulateQ_bind, aimedKeyLocal_adversary,
    aimedKeyLocal_free_noStream prims D keys _ (qb0_prssInitialData D), bind_assoc, pure_bind]
  refine bind_congr fun st => bind_congr fun data => bind_congr fun r => ?_
  rcases r with ⟨st', sent, revealed⟩
  cases revealed with
  | none => rfl
  | some sent' =>
    simp only [setupReveal, simulateQ_bind, simulateQ_pure,
      aimedKeyLocal_free_noStream prims D keys _ (qb0_prssRevealRows D _ _ _ _)]

def aimedFixedBoundary {σ : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (data : C.Party → Parts C × List HashOutput) :
    σ × (C.Party → Mail C E) × Option (C.Party → Mail C E) → σ × Option (RevealRows C)
  | (st, _, none) => (st, none)
  | (st, sent, some revealed) =>
    (st, some (aimedRevealRowsFixed prims D (prssHashAt prims h) (prssCommitActive D sent)
      (fun i => (data i).1) (prssCommitInbox D data sent) revealed))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem aimedFixedBoundary_run {σ : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (data : C.Party → Parts C × List HashOutput)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    simulateQ (prssLocalAt prims h) (setupReveal D (data, r)) =
      pure (aimedFixedBoundary prims D h data r) := by
  rcases r with ⟨st, sent, revealed⟩
  cases revealed with
  | none => rfl
  | some revealed =>
    simp only [setupReveal, simulateQ_bind, aimed_prssLocalAt_eq, aimedRevealRowsFixed_run,
      pure_bind, simulateQ_pure, aimedFixedBoundary]

def aimedEagerFinish (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (keys : KeyName C × HashOutput → Digest)
    (h : Query C → HashOutput) (r : A.State × Option (RevealRows C)) :
    ProbComp ((A.State × Option (RevealRows C)) × (Bool × Bool)) :=
  (fun y => (r, y)) <$> simulateQ (prssLocalAt prims h)
    (simulateQ (aimedKeyLocal prims D keys) ((simulateQ (aimedFlagQueries D (rowsOf r.2))
      (afterDerivation K circuits settings top tree D A x Z r)).run false))

omit [Fintype E] [DecidableEq E] in
theorem aimedFlagProgram_at (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (keys : KeyName C × HashOutput → Digest)
    (h : Query C → HashOutput) :
    simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
      (aimedFlagProgram K circuits settings top tree D A x z Z)) = (do
      let st ← simulateQ (prssLocalAt prims h) (A.start (corruptInputs D x) z)
      let parts ← prssSampleParts D
      let r ← simulateQ (prssLocalAt prims h) (prssEarlyRounds D A st h parts)
      aimedEagerFinish prims K circuits settings top tree D A x Z keys h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)) := by
  simp only [aimedFlagProgram, simulateQ_bind, simulateQ_map, aimedKeyLocal_setupPrefix,
    bind_assoc, setupEarly, pure_bind, prssInitialData_at,
    prssEarlyDataRounds_mask, prssEarlyDataRounds_at, aimedFixedBoundary_run, aimedEagerFinish]

omit [Fintype E] [DecidableEq E] in
/-- Both oracle tables can be sampled eagerly; the finite hash envelope covers all branches. -/
theorem evalDist_aimedFlagProgram_eager_cover (cover : Finset (Query C))
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ∃ S : Finset (Query C), cover ⊆ S ∧
    𝒟[(fun y => (y.1.1, (y.2.1, y.2.2.2))) <$>
      lazyAimedBoundaryRun prims K circuits settings top tree D A x z Z] =
    𝒟[do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h))
        (simulateQ (aimedKeyLocal prims D keys)
          (aimedFlagProgram K circuits settings top tree D A x z Z))] := by
  let game := aimedFlagProgram K circuits settings top tree D A x z Z
  have hg : IsQueryBoundP game AimedProgramCall 0 :=
    aimed_noProgram_flagProgram K circuits settings top tree D A x z Z
  have hs : ∀ keys : KeyName C × HashOutput → Digest, ∃ S : Finset (Query C),
      PrssLocalCovered S (simulateQ (aimedKeyLocal prims D keys) game) :=
    fun keys => prssLocalCovered_exists _
  choose S hS using hs
  let T := cover ∪ Finset.univ.biUnion S
  refine ⟨T, Finset.subset_union_left, ?_⟩
  rw [← evalDist_aimedFlagProgram_projection, evalDist_aimedFlagProgram_keys]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro keys
  rw [← simulateQ_aimedKeyLocal prims D keys game hg]
  apply evalDist_prssLocal_at
  exact (hS keys).mono fun q hq =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨keys, Finset.mem_univ _, hq⟩)

omit [Fintype E] [DecidableEq E] in
/-- An upper bound for this finite experiment suffices for the original aimed event. No
independence of the boundary cache is assumed, and no prefix call is removed. -/
theorem probEvent_lazyAimedBoundary_le_eager (cover : Finset (Query C))
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ∃ S : Finset (Query C), cover ⊆ S ∧
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧
      y.2.2.2 = true | lazyAimedBoundaryRun prims K circuits settings top tree D A x z Z] ≤
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true | do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h))
        (simulateQ (aimedKeyLocal prims D keys)
          (aimedFlagProgram K circuits settings top tree D A x z Z))] := by
  obtain ⟨S, hs, he⟩ := evalDist_aimedFlagProgram_eager_cover prims K circuits settings cover
    top tree D A x z Z
  refine ⟨S, hs, ?_⟩
  have hp := probEvent_congr' (p := fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true)
    (fun _ _ => Iff.rfl) he
  rw [probEvent_map] at hp
  rw [← hp]
  exact probEvent_mono fun _ _ h => ⟨h.1, h.2.2⟩

/-- Exchange the PRSS and key-generation derivation tags, without changing an input's contents. -/
def aimedDeriveDomain : Query C → Query C
  | .derive .prss kind values => .derive .keygen kind values
  | .derive .keygen kind values => .derive .prss kind values
  | q => q

theorem aimedDeriveDomain_hiddenInput (D : C.Coalition) (parts : C.Party → Parts C)
    (n : KeyName C) (hn : Hidden D n) :
    aimedDeriveDomain (hiddenInput parts n) = keygenNamedInput parts n := by
  cases n with
  | parameter => exact hn.elim
  | term T => rfl
  | pair p => rfl

theorem aimed_hiddenInput_injective (D : C.Coalition) (parts : C.Party → Parts C)
    (hc : ¬ KeygenClash D parts) :
    Function.Injective (fun n : {n : KeyName C // Hidden D n} => hiddenInput parts n.val) := by
  intro a b hab
  apply Subtype.ext
  apply keygenNamedInput_injective_of_clash D parts hc
  simpa only [aimedDeriveDomain_hiddenInput D parts a.val a.property,
    aimedDeriveDomain_hiddenInput D parts b.val b.property] using congrArg aimedDeriveDomain hab

theorem aimedDeriveDomain_involutive : Function.Involutive (aimedDeriveDomain (C := C)) := by
  intro q
  cases q <;> try rfl
  rename_i phase kind values
  cases phase <;> rfl

def AimedHiddenInput (D : C.Coalition) (parts : C.Party → Parts C) (q : Query C) : Prop :=
  ∃ n, Hidden D n ∧ hiddenInput parts n = q

theorem aimedHiddenInput_iff (D : C.Coalition) (parts : C.Party → Parts C) (q : Query C) :
    AimedHiddenInput D parts q ↔ KeygenHiddenInput D parts (aimedDeriveDomain q) := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (aimedDeriveDomain_hiddenInput D parts n hn).symm⟩
  · rintro ⟨n, hn, he⟩
    refine ⟨n, hn, aimedDeriveDomain_involutive.injective ?_⟩
    exact (aimedDeriveDomain_hiddenInput D parts n hn).trans he

/-- A private-coordinate guess retains the weight of any transcript event. This permits
different query constructors to share one prefix budget, even for adaptive transcripts. -/
theorem probEvent_aimedCoordinate_weighted {α : Type}
    (kernel : (C.Party → Parts C) → ProbComp α) (X : (C.Party → Parts C) → HashOutput)
    (Y : α → HashOutput) (P : α → Prop) (a : C.Party)
    (term : Option C.Term) (pair : Option C.Party)
    (hX : ∀ c parts, X (shiftAt a term pair c parts) = X parts ^^^ c)
    (hK : ∀ c parts, kernel (shiftAt a term pair c parts) = kernel parts) :
    Pr[fun r => X r.1 = Y r.2 ∧ P r.2 | keygenPartsKernel kernel] =
      Pr[fun r => P r.2 | keygenPartsKernel kernel] * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let run := keygenPartsKernel kernel
  have he : 𝒟[run] = 𝒟[($ᵗ HashOutput) >>= fun c =>
      (fun r => (shiftAt a term pair c r.1, r.2)) <$> run] := by
    calc
      _ = 𝒟[($ᵗ HashOutput) >>= fun _ => run] :=
        (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) run).symm
      _ = _ := OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun c =>
        (evalDist_keygenPartsKernel_shift kernel a term pair c (hK c)).symm
  have he' : 𝒟[run] = 𝒟[run >>= fun r => ($ᵗ HashOutput) >>= fun c =>
      pure (shiftAt a term pair c r.1, r.2)] := by
    rw [he]
    simp only [map_eq_bind_pure_comp]
    exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  have hone (r : (C.Party → Parts C) × α) :
      Pr[fun s => X s.1 = Y s.2 ∧ P s.2 |
        ($ᵗ HashOutput) >>= fun c => pure (shiftAt a term pair c r.1, r.2)] =
      (if P r.2 then 1 else 0) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    change Pr[fun s => X s.1 = Y s.2 ∧ P s.2 |
      (fun c => (shiftAt a term pair c r.1, r.2)) <$> ($ᵗ HashOutput)] = _
    rw [probEvent_map]
    simp only [Function.comp_def, hX]
    by_cases hp : P r.2
    · simp only [hp, and_true, if_true, one_mul]
      have hx : ∀ c : HashOutput, X r.1 ^^^ c = Y r.2 ↔ c = X r.1 ^^^ Y r.2 := by
        intro c
        constructor
        · intro hc
          simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using
            congrArg (fun v => X r.1 ^^^ v) hc
        · rintro rfl
          simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      rw [probEvent_congr' (fun c _ => hx c) rfl, probEvent_eq_eq_probOutput,
        probOutput_uniformSample]
    · simp [hp]
  calc
    _ = Pr[fun s => X s.1 = Y s.2 ∧ P s.2 |
        run >>= fun r => ($ᵗ HashOutput) >>= fun c => pure (shiftAt a term pair c r.1, r.2)] :=
      probEvent_congr' (fun _ _ => Iff.rfl) he'
    _ = _ := by
      rw [probEvent_bind_eq_tsum]
      simp only [hone, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro r
      split_ifs <;> simp [run]

theorem probEvent_aimedHiddenInput_weighted {α : Type} (D : C.Coalition)
    (kernel : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant D kernel)
    (target : α → Query C) (P : α → Prop) :
    Pr[fun r => AimedHiddenInput D r.1 (target r.2) ∧ P r.2 | keygenPartsKernel kernel] ≤
      Pr[fun r => P r.2 | keygenPartsKernel kernel] *
        ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256) := by
  let w := Pr[fun r => P r.2 | keygenPartsKernel kernel] * (Fintype.card HashOutput : ℝ≥0∞)⁻¹
  have ht (T : C.Term) :
      Pr[fun r => (¬ KnownTo D.1 T ∧ termInput .prss r.1 T = target r.2) ∧ P r.2 |
        keygenPartsKernel kernel] ≤ w := by
    by_cases hh : ¬ KnownTo D.1 T
    · obtain ⟨a, rest, ha⟩ := exists_first_holder T
      calc
        _ ≤ Pr[fun r => (r.1 a).term T = keygenDeriveHead (target r.2) ∧ P r.2 |
            keygenPartsKernel kernel] := probEvent_mono fun r _ hr => by
          refine ⟨?_, hr.2⟩
          rw [← hr.1.2]
          simp [termInput, ha, keygenDeriveHead]
        _ = w := probEvent_aimedCoordinate_weighted kernel (fun parts => (parts a).term T)
          (fun r => keygenDeriveHead (target r)) P a (some T) none
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.1 a T hh)
    · simp [hh, w]
  have hp (p : C.Pair) :
      Pr[fun r => (p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ pairInput .prss r.1 p = target r.2) ∧ P r.2 |
        keygenPartsKernel kernel] ≤ w := by
    by_cases hh : p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1
    · calc
        _ ≤ Pr[fun r => (r.1 p.1.1).pair p.1.2 = keygenDeriveHead (target r.2) ∧ P r.2 |
            keygenPartsKernel kernel] := probEvent_mono fun r _ hr => by
          refine ⟨?_, hr.2⟩
          rw [← hr.1.2.2]
          simp [pairInput, keygenDeriveHead]
        _ = w := probEvent_aimedCoordinate_weighted kernel (fun parts => (parts p.1.1).pair p.1.2)
          (fun r => keygenDeriveHead (target r)) P p.1.1 none (some p.1.2)
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.2 p hh.1 hh.2)
    · have he : ∀ r : (C.Party → Parts C) × α,
          ¬ ((p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ pairInput .prss r.1 p = target r.2) ∧ P r.2) :=
        fun _ hr => hh ⟨hr.1.1, hr.1.2.1⟩
      simp only [he, probEvent_False, zero_le]
  have hm : ∀ r : (C.Party → Parts C) × α, AimedHiddenInput D r.1 (target r.2) ∧ P r.2 →
      (∃ T ∈ (Finset.univ : Finset C.Term),
        (¬ KnownTo D.1 T ∧ termInput .prss r.1 T = target r.2) ∧ P r.2) ∨
      (∃ p ∈ (Finset.univ : Finset C.Pair),
        (p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ pairInput .prss r.1 p = target r.2) ∧ P r.2) := by
    rintro r ⟨⟨n, hn, he⟩, hP⟩
    cases n with
    | parameter => exact hn.elim
    | term T => exact Or.inl ⟨T, Finset.mem_univ _, ⟨hn, he⟩, hP⟩
    | pair p => exact Or.inr ⟨p, Finset.mem_univ _, ⟨hn.1, hn.2, he⟩, hP⟩
  refine (probEvent_mono fun r _ => hm r).trans ((probEvent_or_le _ _ _).trans ?_)
  calc
    _ ≤ (∑ _ : C.Term, w) + ∑ _ : C.Pair, w :=
      add_le_add ((probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T _ => ht T))
        ((probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p _ => hp p))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, keygenFinish_card_term,
        keygenFinish_card_pair, w, card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, prssKeyCount,
        Nat.cast_add, div_eq_mul_inv]
      ring

def AimedPrefixCell (D : C.Coalition) (parts : C.Party → Parts C)
    (u : KeygenFresh C) (q : Query C) : Prop :=
  AimedHiddenInput D parts q ∨ AimedEchoCell D u q

/-- Canonical and echo guesses share the prefix charge: they require disjoint query tags. -/
theorem probEvent_aimedPrefixCell_kernel_le {α : Type} (D : C.Coalition)
    (kernel : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant D kernel)
    (target : α → Query C) :
    Pr[fun r => AimedPrefixCell D r.1.1 r.2 (target r.1.2) |
      (do let r ← keygenPartsKernel kernel
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤ (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 := by
  let P : α → Prop := fun a => ∃ kind values, target a = .derive .prss kind values
  let ε : ℝ≥0∞ := (prssKeyCount C : ℝ≥0∞) / 2 ^ 256
  have hc (parts : C.Party → Parts C) (a : α) : AimedHiddenInput D parts (target a) → P a := by
    rintro ⟨n, hn, he⟩
    cases n with
    | parameter => exact hn.elim
    | term T => exact ⟨.term, _, he.symm⟩
    | pair p => exact ⟨.pair, _, he.symm⟩
  have hd (a : α) (u : KeygenFresh C) : AimedEchoCell D u (target a) → ¬ P a := by
    intro hu hp
    obtain ⟨values, hv⟩ := aimedEchoCell_sharedKeys hu
    obtain ⟨kind, values', hp⟩ := hp
    rw [hv] at hp
    cases hp
  have hcanon :
      Pr[fun r => AimedHiddenInput D r.1.1 (target r.1.2) |
        (do let r ← keygenPartsKernel kernel
            let u ← $ᵗ (KeygenFresh C)
            pure (r, u))] ≤ Pr[fun r => P r.2 | keygenPartsKernel kernel] * ε := by
    have he : Pr[fun r => AimedHiddenInput D r.1.1 (target r.1.2) |
        (do let r ← keygenPartsKernel kernel
            let u ← $ᵗ (KeygenFresh C)
            pure (r, u))] =
        Pr[fun r => AimedHiddenInput D r.1 (target r.2) ∧ P r.2 | keygenPartsKernel kernel] := by
      rw [probEvent_bind_eq_tsum]
      simp only [probEvent_bind_eq_tsum, probEvent_pure]
      conv_rhs => rw [probEvent_eq_tsum_ite]
      apply tsum_congr
      intro r
      by_cases hh : AimedHiddenInput D r.1 (target r.2)
      · simp only [hh, hc r.1 r.2 hh, and_self, if_true, mul_one,
          tsum_probOutput_eq_sub, probFailure_eq_zero, tsub_zero]
      · simp [hh]
    rw [he]
    exact probEvent_aimedHiddenInput_weighted D kernel hinv target P
  have hecho :
      Pr[fun r => AimedEchoCell D r.2 (target r.1.2) |
        (do let r ← keygenPartsKernel kernel
            let u ← $ᵗ (KeygenFresh C)
            pure (r, u))] ≤ Pr[fun r => ¬ P r.2 | keygenPartsKernel kernel] * ε := by
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hp : P r.2
    · have hn : ∀ u, ¬ AimedEchoCell D u (target r.2) := fun u hu => hd r.2 u hu hp
      simp [hp, probEvent_bind_eq_tsum, probEvent_pure, hn]
    · simp only [hp, not_false_eq_true, if_true]
      apply mul_le_mul_left'
      change Pr[fun s => AimedEchoCell D s.2 (target s.1.2) |
        (fun u => (r, u)) <$> ($ᵗ (KeygenFresh C))] ≤ ε
      rw [probEvent_map]
      exact probEvent_aimedEchoCell_le D (target r.2)
  refine (probEvent_or_le _ _ _).trans ((add_le_add hcanon hecho).trans ?_)
  rw [← add_mul, probEvent_compl]
  simp only [probFailure_eq_zero, tsub_zero, one_mul]
  exact le_rfl

/-- The canonical-input part of the after-boundary query charge, for every private-invariant
reference kernel, not just for the first two rounds. -/
theorem probEvent_aimedHiddenInput_kernel_le {α : Type} (D : C.Coalition)
    (kernel : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant D kernel)
    (target : α → Query C) :
    Pr[fun r => AimedHiddenInput D r.1 (target r.2) | keygenPartsKernel kernel] ≤
      (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 := by
  have he : Pr[fun r => AimedHiddenInput D r.1 (target r.2) | keygenPartsKernel kernel] =
      Pr[fun r => KeygenHiddenInput D r.1 (aimedDeriveDomain (target r.2)) | keygenPartsKernel kernel] :=
    probEvent_congr' (fun r _ => aimedHiddenInput_iff D r.1 (target r.2)) rfl
  rw [he]
  simpa only [keygenFinish_card_term, keygenFinish_card_pair, card_hashOutput,
    Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, prssKeyCount] using
    probEvent_keygenHiddenInput_kernel_one D kernel hinv (fun r => aimedDeriveDomain (target r))

def aimedHiddenName (D : C.Coalition) : {n : KeyName C // Hidden D n} → C.Term ⊕ C.Pair
  | ⟨.parameter, h⟩ => h.elim
  | ⟨.term T, _⟩ => .inl T
  | ⟨.pair p, _⟩ => .inr p

theorem aimedHiddenName_injective (D : C.Coalition) : Function.Injective (aimedHiddenName D) := by
  intro a b he
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;> simp_all [Hidden, aimedHiddenName]
  all_goals first | exact ha.elim | exact hb.elim

theorem aimed_hidden_card (D : C.Coalition) :
    Fintype.card {n : KeyName C // Hidden D n} ≤ prssKeyCount C := by
  have he := Fintype.card_le_of_injective _ (aimedHiddenName_injective D)
  simpa only [Fintype.card_sum, keygenFinish_card_term, keygenFinish_card_pair, prssKeyCount] using he

theorem aimed_normalTable_exists (D : C.Coalition) (hm : prssKeyCount C < 2 ^ 256) :
    ∃ table : KeyName C → HashOutput,
      Function.Injective (fun n : {n : KeyName C // Hidden D n} => table n) ∧
      ∀ n, Hidden D n → table n ≠ 0 := by
  have hcard : Fintype.card (Option {n : KeyName C // Hidden D n}) ≤ Fintype.card HashOutput := by
    rw [Fintype.card_option, card_hashOutput]
    have hc := aimed_hidden_card D
    change _ ≤ 2 ^ 256
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let σ := Equiv.swap (e none) (0 : HashOutput)
  let table : KeyName C → HashOutput := fun n => if hn : Hidden D n then σ (e (some ⟨n, hn⟩)) else 0
  refine ⟨table, ?_, ?_⟩
  · intro a b hab
    have he : σ (e (some a)) = σ (e (some b)) := by
      simpa only [table, dif_pos a.property, dif_pos b.property] using hab
    exact Option.some.inj (e.injective (σ.injective he))
  · intro n hn he
    have hz : σ (e (some ⟨n, hn⟩)) = σ (e none) := by
      simpa only [table, dif_pos hn, σ, Equiv.swap_apply_left] using he
    have hh := e.injective (σ.injective hz)
    cases hh

theorem probEvent_aimedNamedKey_le (D : C.Coalition) (k : HashOutput) :
    Pr[fun u => ∃ n, u n = k | $ᵗ ({n : KeyName C // Hidden D n} → HashOutput)] ≤
      (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 := by
  have he := probEvent_exists_finset_le_sum (Finset.univ : Finset {n : KeyName C // Hidden D n})
    ($ᵗ ({n : KeyName C // Hidden D n} → HashOutput)) (fun n u => u n = k)
  simp only [Finset.mem_univ, true_and] at he
  refine he.trans ?_
  simp only [probEvent_fun_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  gcongr
  exact_mod_cast aimed_hidden_card D

def aimedCanonicalPoint (D : C.Coalition) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S) :
    {n : KeyName C // Hidden D n} → S :=
  fun n => ⟨hiddenInput parts n.val, hmem n.val n.property⟩

/-- Resample all hidden canonical answers jointly with the oracle, preserving the full joint law.
The continuation sees the installed table, so this makes no independence claim about the cache. -/
theorem evalDist_aimedCanonical_refresh {α : Type} (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hinj : Function.Injective (fun n : {n : KeyName C // Hidden D n} => hiddenInput parts n.val))
    (k : (S → HashOutput) → ({n : KeyName C // Hidden D n} → HashOutput) → ProbComp α) :
    𝒟[do
      let h ← $ᵗ (S → HashOutput)
      k h (fun n => h (aimedCanonicalPoint D S parts hmem n))] =
    𝒟[do
      let h ← $ᵗ (S → HashOutput)
      let u ← $ᵗ ({n : KeyName C // Hidden D n} → HashOutput)
      k (keygenExchangeTable (aimedCanonicalPoint D S parts hmem) h u) u] := by
  let points := aimedCanonicalPoint D S parts hmem
  have hp : Function.Injective points := fun a b hab => hinj (congrArg Subtype.val hab)
  have he := evalDist_keygenTableKeyExchange_bind points hp
    (fun h (_ : {n : KeyName C // Hidden D n} → HashOutput) => k h (fun n => h (points n)))
  have hx (h : S → HashOutput) (u : {n : KeyName C // Hidden D n} → HashOutput) :
      (fun n => keygenExchangeTable points h u (points n)) = u := by
    funext n
    exact keygenExchangeTable_at points hp h u n
  simp only [keygenTableKeyExchange, hx] at he
  refine Eq.symm (he.trans ?_)
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro h
  exact evalDist_uniform_bind_const _

theorem aimedCanonical_refresh_off (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (h : S → HashOutput) (u : {n : KeyName C // Hidden D n} → HashOutput) (q : S)
    (hq : ∀ n, Hidden D n → hiddenInput parts n ≠ q.val) :
    keygenExchangeTable (aimedCanonicalPoint D S parts hmem) h u q = h q := by
  apply keygenExchangeTable_outside
  intro n he
  exact hq n.val n.property (congrArg Subtype.val he)

/-- The same lazy boundary experiment, retaining whether a canonical input was queried early. -/
def lazyAimedEarlyRun (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ProbComp (Bool × (((A.State × Option (RevealRows C)) × HashCache C) ×
      (Bool × ((HashCache C × KeyCache C) × Bool)))) := do
  let e ← (simulateQ (localAnswer prims) (setupEarly D A (A.start (corruptInputs D x) z))).run ∅
  let r ← (simulateQ (localAnswer prims) (setupReveal D e.1)).run e.2
  (fun y => (decide (EarlyCached D e), (r, y))) <$>
    (simulateQ (lazyAimedImpl prims D (rowsOf r.1.2))
      (afterDerivation K circuits settings top tree D A x Z r.1)).run ((r.2, ∅), false)

omit [Fintype E] [DecidableEq E] in
theorem lazyAimedEarlyRun_projection (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Prod.snd <$> lazyAimedEarlyRun prims K circuits settings top tree D A x z Z =
      lazyAimedBoundaryRun prims K circuits settings top tree D A x z Z := by
  simp only [lazyAimedEarlyRun, lazyAimedBoundaryRun, worldRun_setupPrefix, simulateQ_bind,
    StateT.run_bind, bind_assoc, map_bind, Functor.map_map]

omit [Fintype E] [DecidableEq E] in
theorem probEvent_lazyAimedEarlyRun_early_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    Pr[fun y => y.1 = true | lazyAimedEarlyRun prims K circuits settings top tree D A x z Z] ≤
      ((start + 2 * step : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  unfold lazyAimedEarlyRun
  refine (probEvent_bind_le_of_start _ _ _ (EarlyCached D) ?_).trans ?_
  rotate_left
  · simpa only [prssKeyCount, termCount, Nat.cast_add] using
      prob_earlyCached_le prims D A (A.start (corruptInputs D x) z) start step
        (start + 2 * step) (hstart _ _) hround le_rfl
  intro e he b hb hbad
  simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hb
  obtain ⟨r, _, y, _, rfl⟩ := hb
  exact of_decide_eq_true hbad

/-- Remaining secrecy obligation. This is an unconditional joint probability, restricted to
traces with no early canonical prequery; it does not condition on a particular boundary cache.
The missing proof must account for canonical derive queries, shared-key inputs, and the
`4*m^2` term before the uniform-key bound can be applied. -/
def TreeKeyAimedFreshBound : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (start step final : ℕ), DealtInputs D x →
    (∀ x z, IsQueryBoundP (A.start x z) Counted start) →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    (∀ r, IsQueryBoundP (Z r) Counted final) →
    Pr[fun y => y.1 = false ∧ KeysApart D (rowsOf y.2.1.1.2) ∧
      ¬ KeyHit D (rowsOf y.2.1.1.2) y.2.1.2 ∧ y.2.2.2.2 = true |
      lazyAimedEarlyRun prims K circuits settings top tree D A x z Z] ≤
      (((3 * ((ceremonyFuel circuits settings - 2) * step + final)) * prssKeyCount C +
        4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

omit [Fintype E] [DecidableEq E] in
/-- The prefix term is retained in full. The fresh secrecy obligation remains explicit. -/
theorem treeKeyAimedBound (hFresh : TreeKeyAimedFreshBound prims K circuits settings) :
    TreeKeyAimedBound prims K circuits settings := by
  intro hb top tree D A x z Z start step final hx hstart hround hfinal
  rw [← lazyAimedEarlyRun_projection prims K circuits settings top tree D A x z Z, probEvent_map]
  refine (probEvent_mono (q := fun y => y.1 = true ∨ (y.1 = false ∧
    KeysApart D (rowsOf y.2.1.1.2) ∧ ¬ KeyHit D (rowsOf y.2.1.1.2) y.2.1.2 ∧
      y.2.2.2.2 = true)) ?_).trans ((probEvent_or_le _ _ _).trans ?_)
  · intro y _ hy
    cases he : y.1
    · exact Or.inr ⟨rfl, hy⟩
    · exact Or.inl rfl
  · refine (add_le_add
      (probEvent_lazyAimedEarlyRun_early_le prims K circuits settings top tree D A x z Z start step
        hstart hround)
      (hFresh hb top tree D A x z Z start step final hx hstart hround hfinal)).trans ?_
    rw [← ENNReal.add_div]
    apply le_of_eq
    congr 1
    push_cast
    ring

/-- Conditional closure: `hFresh` is the remaining secrecy proof, not an established bound. -/
theorem treeSecurityOfSimClosed (hFresh : TreeKeyAimedFreshBound prims K circuits settings)
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityOfSimAimed prims K circuits settings
    (treeKeyAimedBound prims K circuits settings hFresh) hSim

/-- info: 'ThresholdLeanXmssSecurity.afterDerivation_rename' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterDerivation_rename

/-- info: 'ThresholdLeanXmssSecurity.probEvent_afterDerivation_aimed_randomSwaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_afterDerivation_aimed_randomSwaps

/-- info: 'ThresholdLeanXmssSecurity.probEvent_aimed_uniform_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_aimed_uniform_le

/-- info: 'ThresholdLeanXmssSecurity.treeKeyAimedBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeyAimedBound

/-- info: 'ThresholdLeanXmssSecurity.probEvent_lazyAimedBoundary_le_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_lazyAimedBoundary_le_eager

/-- info: 'ThresholdLeanXmssSecurity.evalDist_aimedCanonical_refresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_aimedCanonical_refresh

/-- info: 'ThresholdLeanXmssSecurity.probEvent_aimedHiddenInput_kernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_aimedHiddenInput_kernel_le

/-- info: 'ThresholdLeanXmssSecurity.probEvent_aimedEchoDelivered_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_aimedEchoDelivered_le

/-- info: 'ThresholdLeanXmssSecurity.aimed_boundary_error_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aimed_boundary_error_arith

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityOfSimClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityOfSimClosed

end ThresholdLeanXmssSecurity
