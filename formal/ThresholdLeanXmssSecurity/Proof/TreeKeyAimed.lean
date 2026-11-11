import ThresholdLeanXmssSecurity.Proof.TreeKeyAfter
import ThresholdLeanXmssSecurity.Proof.Coupling
import ThresholdLeanXmssSecurity.Proof.KeygenFinish

/-!
The aimed-call bound follows by finite eager sampling, canonical-key and echo-cell refresh,
and hidden-key normalization to a reference continuation. Its execution is independent of
the fresh watched keys and invariant under private-part shifts. Separate prefix and continuation
logs retain the full prefix allowance. Derivation clashes, zero keys, delivered echo hits,
and echo collisions fit inside the fixed quadratic allowance.

`treeKeyAimedBound` is unconditional. `treeSecurityOfSimClosed` requires only the simulation hop.
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

/-- The echo decision after removing coherent private terms. Corrupt echoes retain their
actual hashes; honest echoes compare only the exposed terms. -/
def AimedEchoCheck (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i : C.Party) : Prop :=
  ∀ j, j ≠ i → if j ∈ D.1 then Msg.hashesOf (sent j i) = [prssEcho h keys i j]
    else if active j then
      if KeygenShareHidden D i j then
        ∀ T, KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T
      else prssEcho h keys i j = prssEcho h keys j i
    else False

theorem aimedEchoCheck_eq (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i : C.Party) (hi : i ∉ D.1)
    (hh : ∀ j T, j ∉ D.1 → ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T →
      keys i T = keys j T)
    (hn : ∀ j, j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      prssEcho h keys i j = prssEcho h keys j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
        Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    prssEchoCheck h keys i (prssEchoInbox D active sent h keys i) ↔
      AimedEchoCheck D active sent h keys i := by
  unfold prssEchoCheck AimedEchoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj, prssEchoInbox]
  · simp only [if_neg hj, prssEchoInbox]
    by_cases ha : active j
    · simp only [if_pos ha, if_neg hji.symm, Msg.hashesOf, List.cons.injEq, and_true]
      rw [eq_comm]
      by_cases hs : KeygenShareHidden D i j
      · rw [if_pos hs, prssEcho_eq_iff h keys i j (hn j hj hji hs)]
        constructor
        · intro he T _ hiT hjT
          exact he T hiT hjT
        · intro he T hiT hjT
          by_cases hT : KnownTo D.1 T
          · exact he T hT hiT hjT
          · exact hh j T hj hT hiT hjT
      · simp only [if_neg hs]
    · simp [ha, Msg.hashesOf]

theorem aimedEcho_noHidden_congr (D : C.Coalition) (h : Query C → HashOutput)
    (keys keys' : C.Party → C.Term → HashOutput)
    (hk : ∀ i T, KnownTo D.1 T → keys i T = keys' i T)
    (i j : C.Party) (hs : ¬ KeygenShareHidden D i j) :
    prssEcho h keys i j = prssEcho h keys' i j := by
  unfold prssEcho
  congr 2
  apply List.map_congr_left
  intro T hT
  apply hk i T
  by_contra hn
  have hm := of_decide_eq_true (List.mem_filter.mp hT).2
  exact hs ⟨T, hn, hm.1, hm.2⟩

theorem aimedEchoCheck_known_congr (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys keys' : C.Party → C.Term → HashOutput)
    (hk : ∀ i T, KnownTo D.1 T → keys i T = keys' i T) (i : C.Party) :
    AimedEchoCheck D active sent h keys i ↔ AimedEchoCheck D active sent h keys' i := by
  unfold AimedEchoCheck
  apply forall_congr'
  intro j
  by_cases hj : j ∈ D.1
  · have he : prssEcho h keys i j = prssEcho h keys' i j :=
      congrArg h (sharedKeys_prss_congr D (keys i) (keys' i) i j hj (hk i))
    simp only [if_pos hj, he]
  · simp only [if_neg hj]
    by_cases ha : active j
    · simp only [if_pos ha]
      apply forall_congr'
      intro _
      by_cases hs : KeygenShareHidden D i j
      · simp only [if_pos hs]
        apply forall_congr'
        intro T
        apply forall_congr'
        intro hT
        simp only [hk i T hT, hk j T hT]
      · have hs' : ¬ KeygenShareHidden D j i := fun hh => hs (keygenShareHidden_comm hh)
        simp only [if_neg hs, aimedEcho_noHidden_congr D h keys keys' hk i j hs,
          aimedEcho_noHidden_congr D h keys keys' hk j i hs']
    · simp only [if_neg ha]

def AimedEchoAccepted (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i : C.Party) : Prop :=
  i ∉ D.1 ∧ active i ∧
    ¬ C.parties.any (fun j => Msg.isAbort
      (prssEchoInbox D active sent (fun _ => 0) (fun _ _ => 0) i j)) ∧
    AimedEchoCheck D active sent h keys i

theorem aimedEchoAccepted_eq (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput)
    (hh : ∀ i j T, i ∉ D.1 → j ∉ D.1 → ¬ KnownTo D.1 T →
      i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      prssEcho h keys i j = prssEcho h keys j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
        Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) (i : C.Party) :
    prssEchoAccepted D active sent h keys i ↔ AimedEchoAccepted D active sent h keys i := by
  by_cases hi : i ∈ D.1
  · simp [prssEchoAccepted, AimedEchoAccepted, hi]
  · have hb : (fun j => Msg.isAbort (prssEchoInbox D active sent h keys i j)) =
        fun j => Msg.isAbort (prssEchoInbox D active sent (fun _ => 0) (fun _ _ => 0) i j) := by
      funext j
      exact prssEchoInbox_abort_invariant D active sent h (fun _ => 0) keys (fun _ _ => 0) i j
    simp only [prssEchoAccepted, AimedEchoAccepted, hb,
      aimedEchoCheck_eq D active sent h keys i hi (fun j T => hh i j T hi) (hn i · hi)]

/-- Once honest echo collisions are excluded, the last setup round hands the continuation
only decisions computed from exposed keys. The returned hidden keys are ignored. -/
theorem aimedEchoRound_reference {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (next : C.Party → PartyM C E RealSpec α) (state : A.State)
    (hh : ∀ i j T, i ∉ D.1 → j ∉ D.1 → ¬ KnownTo D.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (out i).term T = (out j).term T)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      prssEcho h (fun i => (out i).term) i j = prssEcho h (fun i => (out i).term) j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (out i).term) =
        Query.sharedKeys .prss ((sharedTerms j i).map (out j).term)) :
    stepRound worldRoles D A noFunctionality state
      (prssEchoStepWith D active h out (fun i _ => next i)) =
      (do let (state', sent) ← worldRoles.adversary
            (A.round state (prssEchoVisible D active h (fun i => (out i).term)))
          let steps ← Concrete.sequenceFin fun i => free
            (if AimedEchoAccepted D active sent h (fun i => (out i).term) i then
              advance (next i).run else pure (.done none))
          pure (state', steps, sent)) := by
  rw [stepRound_prssEchoWith_split, stepRound_prssEcho]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨state', sent⟩
  congr 2
  funext i
  rw [aimedEchoAccepted_eq D active sent h (fun i => (out i).term) hh hn i]
  split_ifs <;> rfl

theorem aimedReferenceKeys_known (D : C.Coalition) (h : Query C → HashOutput)
    (left right : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) (T : C.Term) (hT : KnownTo D.1 T) :
    (aimedReferenceKeys prims D h left parts revealed i).term T =
      (aimedReferenceKeys prims D h right parts revealed i).term T := by
  simp only [aimedReferenceKeys, keygenMaskKeys, if_pos hT]

theorem aimedReferenceKeys_coherent (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i j : C.Party) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    (aimedReferenceKeys prims D h table parts revealed i).term T =
      (aimedReferenceKeys prims D h table parts revealed j).term T := by
  simp only [aimedReferenceKeys, keygenMaskKeys, if_neg hT, if_pos hiT, if_pos hjT]

def aimedEchoReferenceRound {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) (state : A.State) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) := do
  let known := fun i => (aimedReferenceKeys prims D h (fun _ => 0) parts revealed i).term
  let (state', sent) ← worldRoles.adversary (A.round state (prssEchoVisible D active h known))
  let steps ← Concrete.sequenceFin fun i => free
    (if AimedEchoAccepted D active sent h known i then advance (next i).run else pure (.done none))
  pure (state', steps, sent)

theorem aimedEchoRound_named {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) (state : A.State)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h table parts revealed i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    stepRound worldRoles D A noFunctionality state
      (prssEchoStepWith D active h (aimedReferenceKeys prims D h table parts revealed)
        (fun i _ => next i)) =
      aimedEchoReferenceRound prims D A active h parts revealed next state := by
  rw [aimedEchoRound_reference D A active h _ next state
    (fun i j T _ _ hT hiT hjT => aimedReferenceKeys_coherent prims D h table parts revealed i j T hT hiT hjT) hn]
  have hk := aimedReferenceKeys_known prims D h table (fun _ => 0) parts revealed
  have hv := prssEchoVisible_congr (E := E) D active h h
    (fun i => (aimedReferenceKeys prims D h table parts revealed i).term)
    (fun i => (aimedReferenceKeys prims D h (fun _ => 0) parts revealed i).term)
    (fun i j _ hj => congrArg h (sharedKeys_prss_congr D _ _ i j hj (hk i)))
  rw [hv]
  unfold aimedEchoReferenceRound
  apply bind_congr
  rintro ⟨state', sent⟩
  dsimp only
  congr 2
  funext i
  have hc := aimedEchoCheck_known_congr D active sent h _ _ hk i
  simp only [AimedEchoAccepted, hc]
  split_ifs <;> rfl

def aimedEchoReferenceExecution {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) :
    ℕ → A.State → OracleComp (WorldSpec C) (A.State × (C.Party → Option α))
  | 0, state => pure (state, fun _ => none)
  | fuel + 1, state =>
    if ∀ i, i ∉ D.1 → ¬ active i then pure (state, fun _ => none) else do
      let (state', steps, _) ← aimedEchoReferenceRound prims D A active h parts revealed next state
      executeRounds worldRoles D A noFunctionality fuel state' steps

theorem aimedEchoExecution_named {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) (fuel : ℕ) (state : A.State)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h table parts revealed i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    executeRounds worldRoles D A noFunctionality fuel state
      (prssEchoStepWith D active h (aimedReferenceKeys prims D h table parts revealed)
        (fun i _ => next i)) =
      aimedEchoReferenceExecution prims D A active h parts revealed next fuel state := by
  have hout : (fun i => (prssEchoStepWith D active h
      (aimedReferenceKeys prims D h table parts revealed) (fun i _ => next i) i).output) =
      fun _ => none := by
    funext i
    unfold prssEchoStepWith
    split_ifs <;> rfl
  have hdone : (∀ i, i ∉ D.1 → (prssEchoStepWith D active h
      (aimedReferenceKeys prims D h table parts revealed) (fun i _ => next i) i).isDone) ↔
      ∀ i, i ∉ D.1 → ¬ active i := by
    apply forall_congr'
    intro i
    by_cases hi : i ∈ D.1 <;> by_cases ha : active i <;>
      simp [prssEchoStepWith, hi, ha, Step.isDone]
  cases fuel with
  | zero => simp only [executeRounds, aimedEchoReferenceExecution, hout]
  | succ fuel =>
    simp only [executeRounds, aimedEchoReferenceExecution, hdone, hout]
    split_ifs
    · rfl
    · rw [aimedEchoRound_named prims D A active h table parts revealed next state hn]

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

def AimedReferenceActive (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (sentCommit sentReveal : C.Party → Mail C E) (i : C.Party) : Prop :=
  i ∉ D.1 ∧ active i ∧ aimedRevealAborted D active sentReveal i = false ∧
    aimedReferenceOpenCheck D h sentCommit sentReveal i

theorem aimedReferenceRows_active (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sentCommit sentReveal : C.Party → Mail C E) (i : C.Party) :
    aimedReferenceRows prims D h table active parts sentCommit sentReveal i =
      if AimedReferenceActive D h active sentCommit sentReveal i then
        let keys := aimedReferenceKeys prims D h table parts (fun i j => sentReveal j i) i
        some (keys, C.parties.map fun j => h (.sharedKeys .prss ((sharedTerms i j).map keys.term)))
      else none := by
  unfold aimedReferenceRows AimedReferenceActive
  split_ifs <;> simp_all

theorem aimedMask_referenceKeys (D : C.Coalition) (h : Query C → HashOutput)
    (left right : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) :
    let keys := aimedReferenceKeys prims D h left parts revealed i
    let masked := keygenMaskKeys D right i (0, keys.term, keys.pair)
    (⟨masked.2.1, masked.2.2⟩ : PrssKeys C) = aimedReferenceKeys prims D h right parts revealed i := by
  simp only [aimedReferenceKeys, keygenMaskKeys]
  congr 1
  · funext T
    split_ifs <;> rfl
  · funext j
    split_ifs <;> rfl

theorem aimedReferenceRows_steps (top : TopTree) (tree : Tree) (D : C.Coalition)
    (h : Query C → HashOutput) (table normal : KeyName C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (x : C.Party → Keys C) (i : C.Party) :
    suspendStep (fun prss =>
      (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree : PartyM C E RealSpec TreeOutput))
      (prssFinishStep i (aimedRowsMask D normal
        (aimedReferenceRows prims D h table active parts sentCommit sentReveal) i)) =
      prssEchoStepWith D (AimedReferenceActive D h active sentCommit sentReveal) h
        (aimedReferenceKeys prims D h table parts (fun i j => sentReveal j i))
        (fun i _ => ceremonyAfterSetup K circuits settings
          ⟨i, x i, aimedReferenceKeys prims D h normal parts (fun i j => sentReveal j i) i⟩ top tree) i := by
  unfold aimedRowsMask
  rw [aimedReferenceRows_active]
  by_cases hi : i ∈ D.1
  · have ha : ¬ AimedReferenceActive D h active sentCommit sentReveal i := fun hh => hh.1 hi
    simp only [if_neg ha, Option.map_none, prssFinishStep, suspendStep, prssEchoStepWith, if_pos hi]
  · simp only [prssEchoStepWith, if_neg hi]
    by_cases ha : AimedReferenceActive D h active sentCommit sentReveal i
    · simp only [if_pos ha, Option.map_some, aimedMask_referenceKeys,
        prssFinishStep, suspendStep, prssEchoOutbox, prssEcho]
      have hd (j : C.Party) (f : C.Party → HashOutput) : (C.parties.map f).getD j.val 0 = f j := by
        simp [Committee.parties, List.getD_eq_getElem?_getD]
      simp only [hd]
      congr 1
      funext inbox
      simp only [exchangeResume, prssEchoResume, prssEchoCheck, prssEcho]
      split_ifs <;> simp [bind_assoc, pure_bind, Option.elimM, Function.comp_def]
    · simp only [if_neg ha, Option.map_none, prssFinishStep, suspendStep]

def aimedReferenceAfter (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State) : OracleComp (WorldSpec C) Bool := do
  let r ← aimedEchoReferenceExecution prims D A (AimedReferenceActive D h active sentCommit sentReveal)
    h parts (fun i j => sentReveal j i)
    (fun i => ceremonyAfterSetup K circuits settings
      ⟨i, x i, aimedReferenceKeys prims D h normal parts (fun i j => sentReveal j i) i⟩ top tree)
    (ceremonyFuel circuits settings - 2) state
  worldRoles.adversary (Z r)

theorem afterDerivation_aimedReference (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (table normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h table parts (fun i j => sentReveal j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    afterDerivation K circuits settings top tree D A x Z
      (state, some (aimedRowsMask D normal
        (aimedReferenceRows prims D h table active parts sentCommit sentReveal))) =
      aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
        sentCommit sentReveal state := by
  unfold afterDerivation aimedReferenceAfter
  simp only [aimedReferenceRows_steps]
  rw [aimedEchoExecution_named prims D A _ h table parts _ _ _ state hn]

theorem aimedReferenceAfter_exposed (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State) :
    aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active
      (keygenExposedParts D parts) sentCommit sentReveal state =
    aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
      sentCommit sentReveal state := by
  unfold aimedReferenceAfter
  simp only [aimedReferenceKeys_exposed]
  generalize ceremonyFuel circuits settings - 2 = fuel
  cases fuel <;> simp only [aimedEchoReferenceExecution, aimedEchoReferenceRound, aimedReferenceKeys_exposed]

theorem aimedEarlyRounds_exposed (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    prssEarlyRounds D A state h (keygenExposedParts D parts) = prssEarlyRounds D A state h parts := by
  apply prssEarlyRounds_congr
  intro i c hi hc
  apply revealTo_prss_congr D _ _ i c hc
  · intro T hT
    simp only [keygenExposedParts, if_pos hT]
  · simp only [keygenExposedParts, if_pos (Or.inr hc)]

def aimedReferenceProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) : OracleComp (WorldSpec C) Bool := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  let (state', sent, revealed) ← worldRoles.adversary (prssEarlyRounds D A state h parts)
  match revealed with
  | none => worldRoles.adversary (Z (state', fun _ => none))
  | some sent' =>
    aimedReferenceAfter prims K circuits settings top tree D A x Z h normal
      (prssCommitActive D sent) parts sent sent' state'

theorem aimedReferenceProgram_exposed (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) :
    aimedReferenceProgram prims K circuits settings top tree D A x z Z h normal (keygenExposedParts D parts) =
      aimedReferenceProgram prims K circuits settings top tree D A x z Z h normal parts := by
  unfold aimedReferenceProgram
  simp only [aimedEarlyRounds_exposed, aimedReferenceAfter_exposed]

theorem aimedReferenceProgram_privateInvariant {α : Type}
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (observe : OracleComp (WorldSpec C) Bool → α) :
    KeygenPrivateInvariant D (fun parts => observe
      (aimedReferenceProgram prims K circuits settings top tree D A x z Z h normal parts)) := by
  have he := aimedReferenceProgram_exposed prims K circuits settings top tree D A x z Z h normal
  have hp := keygenExposedParts_privateInvariant D
  constructor
  · intro a T hT c parts
    dsimp only
    rw [← he (shiftAt a (some T) none c parts), hp.1 a T hT c parts, he parts]
  · intro p hp₁ hp₂ c parts
    dsimp only
    rw [← he (shiftAt p.1.1 none (some p.1.2) c parts), hp.2 p hp₁ hp₂ c parts, he parts]

theorem aimedEchoReferenceRound_bound {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) (state : A.State) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (aimedEchoReferenceRound prims D A active h parts revealed next state) WorldCounted step := by
  unfold aimedEchoReferenceRound
  refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_adversary _ _ (hround _ _)) fun r _ => ?_).mono (by simp)
  rcases r with ⟨state', sent⟩
  exact isQueryBoundP_bind (isQueryBoundP_sequenceFin _ fun _ => isQueryBoundP_free _ 0)
    fun _ _ => isQueryBoundP_pure _ _ 0

theorem aimedEchoReferenceExecution_bound {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next : C.Party → PartyM C E RealSpec α) (fuel : ℕ) (state : A.State) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (aimedEchoReferenceExecution prims D A active h parts revealed next fuel state)
      WorldCounted (fuel * step) := by
  cases fuel with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ fuel =>
    unfold aimedEchoReferenceExecution
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine (isQueryBoundP_bind (m := fuel * step)
        (aimedEchoReferenceRound_bound prims D A active h parts revealed next state step hround)
        fun r _ => ?_).mono (by simp [Nat.succ_mul, Nat.add_comm])
      exact isQueryBoundP_executeRounds D A noFunctionality step hround
        (fun state inputs => isQueryBoundP_runFunctionality_noFunctionality D A state inputs step)
        fuel r.1 r.2.1

theorem aimedReferenceAfter_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State) (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    IsQueryBoundP (aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
      sentCommit sentReveal state) WorldCounted ((ceremonyFuel circuits settings - 2) * step + final) := by
  unfold aimedReferenceAfter
  generalize ceremonyFuel circuits settings - 2 = fuel
  exact isQueryBoundP_bind
    (aimedEchoReferenceExecution_bound prims D A _ h parts _ _ fuel state step hround)
    fun r _ => isQueryBoundP_adversary _ _ (hfinal r)

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

def aimedRowsRehash (h : Query C → HashOutput) (rows : RevealRows C) : RevealRows C :=
  fun i => (rows i).map fun row =>
    (row.1, C.parties.map fun j => h (.sharedKeys .prss ((sharedTerms i j).map row.1.term)))

theorem aimedRevealRowsFixed_rehash (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    aimedRowsRehash h (aimedRevealRowsFixed prims D h active parts committed sent) =
      aimedRevealRowsFixed prims D h active parts committed sent := by
  funext i
  simp only [aimedRowsRehash, aimedRevealRowsFixed, aimedRevealDataFixed]
  split_ifs <;> rfl

theorem aimedRevealRowsFixed_reference (D : C.Coalition) (h : Query C → HashOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) :
    aimedRevealRowsFixed prims D h active parts
      (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal =
    aimedReferenceRows prims D h (fun n => h (hiddenInput parts n)) active parts sentCommit sentReveal := by
  have he : aimedRowsRehash h (aimedRowsMask D (fun n => h (hiddenInput parts n))
      (aimedRevealRowsFixed prims D h active parts
        (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)) =
      aimedReferenceRows prims D h (fun n => h (hiddenInput parts n)) active parts sentCommit sentReveal := by
    funext i
    simp only [aimedRowsRehash, aimedRowsMask, Option.map_map, Function.comp_def]
    exact aimedRevealRowsFixed_mask prims D h (fun n => h (hiddenInput parts n)) active parts sentCommit sentReveal i
  rw [aimedRevealRowsFixed_canonical, aimedRevealRowsFixed_rehash] at he
  exact he

theorem probEvent_aimedFixed_reference (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State)
    (watched : RevealRows C) (cache : HashCache C)
    (ha : KeysApart D (aimedRevealRowsFixed prims D h active parts
      (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal))
    (hzero : ∀ n, Hidden D n → h (hiddenInput parts n) ≠ 0)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hecho : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h (fun n => h (hiddenInput parts n))
        parts (fun i j => sentReveal j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (afterDerivation K circuits settings top tree D A x Z
        (state, some (aimedRevealRowsFixed prims D h active parts
          (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)))).run ((cache, ∅), false)] =
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched)
      (aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
        sentCommit sentReveal state)).run ((cache, ∅), false)] := by
  have he := aimedRevealRowsFixed_canonical prims D h active parts
    (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal
  have hm := probEvent_afterDerivation_aimed_mask prims K circuits settings top tree D
    (fun n => h (hiddenInput parts n)) normal A x Z state watched
    (aimedRevealRowsFixed prims D h active parts (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)
    cache (by rwa [he])
    (by intro a b hab; apply Subtype.ext; exact congrArg (fun n : {n : KeyName C // Hidden D n} => n.val) (hni (a₁ := ⟨a, a.property.1⟩)
      (a₂ := ⟨b, b.property.1⟩) hab))
    (fun n hn _ => hzero n hn) (fun n hn _ => hn0 n hn)
  rw [he] at hm
  rw [aimedRevealRowsFixed_reference, afterDerivation_aimedReference prims K circuits settings
    top tree D A x Z h _ normal active parts sentCommit sentReveal state hecho] at hm
  rw [aimedRevealRowsFixed_reference]
  exact hm

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

/-- A total table is a cache in which every random-oracle answer is already fixed. -/
def aimedFullCache (h : Query C → HashOutput) : HashCache C := fun q => some (h q)

theorem aimedFullCache_hash (h : Query C → HashOutput) (q : Query C) :
    (hashAnswer prims q).run (aimedFullCache h) =
      pure (prssHashAt prims h q, aimedFullCache h) := by
  have hr (q : Query C) : ((Query C →ₒ HashOutput).randomOracle q).run (aimedFullCache h) =
      pure (h q, aimedFullCache h) := by
    exact QueryImpl.withCaching_run_some _ rfl
  cases q <;> simp only [hashAnswer, prssHashAt]
  all_goals first | exact hr _ | (split_ifs <;> first | rfl | exact hr _)

theorem aimedFullCache_local (h : Query C → HashOutput) (t : (LocalSpec C).Domain) :
    (localAnswer prims t).run (aimedFullCache h) =
      (fun a => (a, aimedFullCache h)) <$> prssLocalAt prims h t := by
  rcases t with n | q | x
  · rfl
  · change (hashAnswer prims q).run _ = _
    rw [aimedFullCache_hash]
    rfl
  · simp only [localAnswer, QueryImpl.add_apply_inr, prgAnswer, StateT.run_bind,
      aimedFullCache_hash, pure_bind, StateT.run_pure, prssLocalAt, map_pure]
    rfl

theorem aimedFullCache_keyWorld (D : C.Coalition) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (t : (WorldSpec C).Domain) :
    (keyWorld prims D keys t).run (aimedFullCache h) =
      (fun a => (a, aimedFullCache h)) <$>
        simulateQ (prssLocalAt prims h) (aimedKeyLocal prims D keys t) := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  · exact aimedFullCache_local prims h (.inl n)
  · exact aimedFullCache_local prims h (.inr (.inl q))
  · exact aimedFullCache_local prims h (.inr (.inr x))
  · change (programAnswer p).run _ = _
    simp [programAnswer, aimedFullCache, StateT.run_bind, StateT.run_get, StateT.run_pure,
      aimedKeyLocal]
  · exact aimedFullCache_local prims h (.inl n)
  · exact aimedFullCache_local prims h (.inr (.inl q))
  · simp only [keyWorld, aimedKeyLocal]
    split_ifs
    · simp
    · exact aimedFullCache_local prims h _

theorem aimedFullCache_run {α : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (game : OracleComp (WorldSpec C) α) :
    (simulateQ (keyWorld prims D keys) game).run (aimedFullCache h) =
      (fun a => (a, aimedFullCache h)) <$>
        simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys) game) := by
  induction game using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      aimedFullCache_keyWorld, bind_map_left, ih, map_bind]

/-- Eliminate both lazy caches while retaining the query flag. -/
theorem probEvent_aimedFullCache {α : Type} (D : C.Coalition)
    (h : Query C → HashOutput) (watched : RevealRows C) (game : OracleComp (WorldSpec C) α) :
    Pr[fun y => y.2.2 = true | (simulateQ (lazyAimedImpl prims D watched) game).run
      ((aimedFullCache h, ∅), false)] =
    Pr[fun y => y.2 = true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
      simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
        ((simulateQ (aimedFlagQueries D watched) game).run false))] := by
  have he := evalDist_lazyKeyWorld prims D
    ((simulateQ (aimedFlagQueries D watched) game).run false) (aimedFullCache h) ∅
  simp only [tableExtending_empty, StateT.run'_eq, aimedFullCache_run,
    Functor.map_map, Function.comp_def, id_map] at he
  rw [run_aimedFlagQueries] at he
  simp only [Functor.map_map, Function.comp_def] at he
  have hid (oa : ProbComp (α × Bool)) : (fun a => a) <$> oa = oa := by
    exact id_map oa
  simp only [hid] at he
  have hp := probEvent_congr' (p := fun y => y.2 = true) (fun _ _ => Iff.rfl) he
  simpa only [probEvent_map, Function.comp_def, lazyAimedImpl] using hp

/-- Eager private AES sampling, with a fixed public oracle and the watched-row flag. -/
def aimedEagerFlag {α : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (watched : RevealRows C) (game : OracleComp (WorldSpec C) α) : ProbComp (α × Bool) :=
  ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
    simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
      ((simulateQ (aimedFlagQueries D watched) game).run false))

theorem probEvent_aimedEager_reference (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State)
    (watched : RevealRows C)
    (ha : KeysApart D (aimedRevealRowsFixed prims D h active parts
      (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal))
    (hzero : ∀ n, Hidden D n → h (hiddenInput parts n) ≠ 0)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hecho : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let keys := fun i => (aimedReferenceKeys prims D h (fun n => h (hiddenInput parts n))
        parts (fun i j => sentReveal j i) i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h watched
      (afterDerivation K circuits settings top tree D A x Z
        (state, some (aimedRevealRowsFixed prims D h active parts
          (prssCommitInbox D (prssDataAt h parts) sentCommit) sentReveal)))] =
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h watched
      (aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
        sentCommit sentReveal state)] := by
  unfold aimedEagerFlag
  rw [← probEvent_aimedFullCache, ← probEvent_aimedFullCache]
  exact probEvent_aimedFixed_reference prims K circuits settings top tree D A x Z h normal
    active parts sentCommit sentReveal state watched (aimedFullCache h) ha hzero hni hn0 hecho

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

theorem aimedReferenceKeys_oracle_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (hc : ¬ KeygenClash D parts) (hh : ∀ v, ¬ AimedHiddenInput D parts v → h₁ v = h₂ v)
    (i : C.Party) (hi : i ∉ D.1) :
    aimedReferenceKeys prims D h₁ table parts revealed i =
      aimedReferenceKeys prims D h₂ table parts revealed i := by
  have hview : ∀ k, k ∉ D.1 → aimedCorruptView D parts revealed i k = parts k := by
    intro k hk
    simp [aimedCorruptView, hk]
  simp only [aimedReferenceKeys, keygenMaskKeys, D_deriveKeys]
  congr 1
  · funext T
    split_ifs with hT hiT
    · apply hh
      intro hv
      apply not_keygenHiddenInput_knownTerm D parts hc _ T hT
        (hview _ (keygenFirstHonest_holder D T).2)
      exact (aimedHiddenInput_iff D parts _).mp hv
    · rfl
    · rfl
    · rfl
  · funext j
    split_ifs with hji hj
    · rfl
    · apply hh
      intro hv
      have hj' : j ∈ D.1 := hj.resolve_left hi
      apply not_keygenHiddenInput_crossPair D parts hc
        (aimedCorruptView D parts revealed i) (C.pairOf i j (Ne.symm hji))
      · unfold Committee.pairOf
        split_ifs <;> simp [hj']
      · unfold Committee.pairOf
        split_ifs
        · exact Or.inl (hview i hi)
        · exact Or.inr (hview i hi)
      · exact (aimedHiddenInput_iff D parts _).mp hv
    · rfl

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

/-- Hash domains used only by PRSS setup. -/
def aimedSetupQuery : Query C → Prop
  | .derive .prss _ _ => True
  | .sharedKeys .prss _ => True
  | _ => False

namespace AimedSetupDomain


variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β σ : Type}

/-- Post-setup calls exclude the PRSS setup hash domains and preserve stream names. -/
def RoBad (ctx : Context C) : (RoSpec C).Domain → Prop
  | .inl q => aimedSetupQuery q
  | .inr x => ¬ ValidKey ctx.self ctx.prss x.1 x.2.1

/-- The bad calls of a program of operator `ctx`. -/
def PartyBad (ctx : Context C) : (PartySpec C E G).Domain → Prop
  | .inl (.inl (.inr t)) => RoBad ctx t
  | _ => False

def ROk (ctx : Context C) (oa : OracleComp (RoSpec C) α) : Prop := IsQueryBoundP oa (RoBad ctx) 0

def POk (ctx : Context C) (p : PartyM C E G α) : Prop :=
  IsQueryBoundP p.run (PartyBad (E := E) (G := G) ctx) 0

def SOk (ctx : Context C) (p : StateT σ (PartyM C E G) α) : Prop := ∀ s, POk ctx (p.run s)

variable {ctx : Context C}

theorem ROk.bind {oa : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    (h : ROk ctx oa) (hf : ∀ a, ROk ctx (f a)) : ROk ctx (oa >>= f) := qb0_bind h hf

theorem ROk.pure (a : α) : ROk ctx (pure a : OracleComp (RoSpec C) α) := by simp [ROk]

theorem ROk.map {oa : OracleComp (RoSpec C) α} (f : α → β) (h : ROk ctx oa) : ROk ctx (f <$> oa) := by
  simpa [ROk] using h

theorem ROk.mapM (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, ROk ctx (f a)) (xs : List α) :
    ROk ctx (xs.mapM f) := qb0_mapM f hf xs

theorem ROk.hashQuery (q : Query C) (hq : ¬ aimedSetupQuery q) : ROk ctx (hashQuery q) := by
  unfold ROk ThresholdLeanXmss.hashQuery
  erw [isQueryBoundP_query_iff]
  exact fun h => (hq h).elim

theorem ROk.stream (x : PrgInput C) (hx : ValidKey ctx.self ctx.prss x.1 x.2.1) :
    ROk ctx (query (spec := RoSpec C) (.inr x)) := by
  unfold ROk
  erw [isQueryBoundP_query_iff]
  intro h
  exact absurd hx h

theorem ROk.prgBits (name : KeyName C) (key : HashOutput) (hv : ValidKey ctx.self ctx.prss name key)
    (ρ idx count : ℕ) : ROk ctx (prgBits name key ρ idx count) := by
  unfold ThresholdLeanXmss.prgBits
  exact ROk.bind (ROk.mapM _ (fun position => ROk.stream (name, key, ρ, idx, position) hv) _)
    fun _ => ROk.pure _

theorem ROk.tweakable (oa : OracleComp HashSpec α) : ROk ctx (tweakable oa) := by
  unfold ThresholdLeanXmss.tweakable ROk
  refine qb0_simulateQ (p := fun _ => False) _ (fun t _ => ?_) oa (by
    induction oa using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl not_false, fun u => by simpa using ih u⟩)
  exact ROk.hashQuery _ ((by simp [aimedSetupQuery]))

/-- The bad local calls of operator `ctx`. -/
def LocalBad (ctx : Context C) : (LocalSpec C).Domain → Prop
  | .inr t => RoBad ctx t
  | _ => False

theorem qb0_liftComp_local {oa : OracleComp (RoSpec C) α} (h : ROk ctx oa) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (LocalBad ctx) 0 := by
  refine qb0_liftComp oa h fun t ht => ?_
  erw [isQueryBoundP_query_iff]
  exact fun h' => (ht h').elim

theorem qb0_liftComp_party {oa : OracleComp (LocalSpec C) α} (h : IsQueryBoundP oa (LocalBad ctx) 0) :
    IsQueryBoundP (liftComp oa (PartySpec C E G)) (PartyBad (E := E) (G := G) ctx) 0 := by
  refine qb0_liftComp oa h fun t ht => ?_
  erw [isQueryBoundP_query_iff]
  intro h'
  rcases t with u | t
  · exact h'.elim
  · rcases t with q | x
    · exact (ht h').elim
    · exact (ht h').elim

theorem POk.pure (a : α) : POk (E := E) (G := G) ctx (pure a) := by simp [POk]

theorem POk.failure : POk (E := E) (G := G) (α := α) ctx failure := by
  simp [POk, OptionT.run_failure]

theorem POk.bind {p : PartyM C E G α} {f : α → PartyM C E G β} (h : POk ctx p)
    (hf : ∀ a, POk ctx (f a)) : POk ctx (p >>= f) := by
  unfold POk
  rw [OptionT.run_bind]
  refine qb0_bind h fun o => ?_
  cases o with
  | none => simp
  | some a => exact hf a

theorem POk.lift {oa : OracleComp (PartySpec C E G) α}
    (h : IsQueryBoundP oa (PartyBad (E := E) (G := G) ctx) 0) : POk ctx (OptionT.lift oa) := by
  unfold POk
  rw [OptionT.run_lift]
  exact qb0_bind h fun _ => by simp

theorem POk.oracleStep {oa : OracleComp (RoSpec C) α} (h : ROk ctx oa) :
    POk (E := E) (G := G) ctx (oracleStep oa) :=
  POk.lift (qb0_liftComp_party (qb0_liftComp_local h))

theorem POk.exchange (outbox : Mail C E) : POk (G := G) ctx (exchange outbox) := by
  unfold ThresholdLeanXmss.exchange
  refine POk.bind (POk.lift ?_) fun inbox => ?_
  · erw [isQueryBoundP_query_iff]
    exact fun h => h.elim
  · split_ifs
    · exact POk.failure
    · exact POk.pure _

theorem POk.require (c : Prop) : POk (E := E) (G := G) ctx (require c) := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact POk.pure _
  · exact POk.failure

theorem POk.map {p : PartyM C E G α} (f : α → β) (h : POk ctx p) : POk ctx (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact POk.bind h fun _ => POk.pure _

theorem POk.mapM (f : α → PartyM C E G β) (hf : ∀ a, POk ctx (f a)) :
    ∀ xs : List α, POk ctx (xs.mapM f)
  | [] => POk.pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact POk.bind (hf x) fun _ => POk.bind (POk.mapM f hf xs) fun _ => POk.pure _

theorem SOk.bind {p : StateT σ (PartyM C E G) α} {f : α → StateT σ (PartyM C E G) β}
    (h : SOk ctx p) (hf : ∀ a, SOk ctx (f a)) : SOk ctx (p >>= f) := by
  intro s
  rw [StateT.run_bind]
  exact POk.bind (h s) fun x => hf x.1 x.2

theorem SOk.pure (a : α) : SOk (σ := σ) (E := E) (G := G) ctx (pure a) := fun s => by
  rw [StateT.run_pure]; exact POk.pure _

theorem SOk.lift {p : PartyM C E G α} (h : POk ctx p) : SOk (σ := σ) ctx (StateT.lift p) := fun s => by
  rw [StateT.run_lift]
  exact POk.bind h fun _ => POk.pure _

theorem SOk.get : SOk (σ := σ) (E := E) (G := G) ctx get := fun s => by
  rw [StateT.run_get]; exact POk.pure _

theorem SOk.set (s' : σ) : SOk (E := E) (G := G) ctx (set s' : StateT σ (PartyM C E G) PUnit) := fun s => by
  rw [StateT.run_set]; exact POk.pure _

theorem SOk.modify (f : σ → σ) : SOk (E := E) (G := G) ctx (modify f : StateT σ (PartyM C E G) PUnit) := fun s => by
  rw [StateT.run_modify]; exact POk.pure _

theorem SOk.modifyGet (f : σ → α × σ) : SOk (E := E) (G := G) ctx (modifyGet f : StateT σ (PartyM C E G) α) := fun s => by
  rw [StateT.run_modifyGet]; exact POk.pure _

theorem SOk.map {p : StateT σ (PartyM C E G) α} (f : α → β) (h : SOk ctx p) : SOk ctx (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact SOk.bind h fun _ => SOk.pure _

theorem SOk.failure : SOk (σ := σ) (E := E) (G := G) (α := α) ctx (StateT.lift failure) :=
  SOk.lift POk.failure

theorem SOk.foldlM {γ : Type} (f : β → γ → StateT σ (PartyM C E G) β) (hf : ∀ b c, SOk ctx (f b c)) :
    ∀ (xs : List γ) (init : β), SOk ctx (xs.foldlM f init)
  | [], init => SOk.pure _
  | x :: xs, init => by
    rw [List.foldlM_cons]
    exact SOk.bind (hf init x) fun b => SOk.foldlM f hf xs b

theorem SOk.mapM (f : α → StateT σ (PartyM C E G) β) (hf : ∀ a, SOk ctx (f a)) :
    ∀ xs : List α, SOk ctx (xs.mapM f)
  | [] => SOk.pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact SOk.bind (hf x) fun _ => SOk.bind (SOk.mapM f hf xs) fun _ => SOk.pure _

/-- A codec that draws only under the key of its name. -/
def CodecOk {R : Type} (ctx : Context C) (codec : Codec C E R) : Prop :=
  ∀ name key ρ idx count, ValidKey ctx.self ctx.prss name key → ROk ctx (codec.draw name key ρ idx count)

theorem codecOk_bit : CodecOk (E := E) ctx bitCodec :=
  fun name key ρ idx count hv => ROk.prgBits name key hv ρ idx count

theorem codecOk_element [Field E] [Algebra Bit E] (K : Constants C E) : CodecOk ctx (elementCodec K) :=
  fun name key ρ idx count hv => ROk.bind (ROk.prgBits name key hv ρ idx _) fun _ => ROk.pure _

theorem SOk.prssRandomness {R : Type} [Zero R] (codec : Codec C E R) (hc : CodecOk ctx codec)
    (idx count : ℕ) : SOk (G := G) ctx (prssRandomness ctx codec idx count) := by
  unfold ThresholdLeanXmss.prssRandomness freshLabel
  refine SOk.bind (SOk.modifyGet _) fun ρ => ?_
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.mapM _ (fun T => ?_) _))) fun r => ?_
  · split_ifs with hT
    · exact hc _ _ _ _ _ ⟨hT, rfl⟩
    · exact ROk.pure _
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.mapM _ (fun j => ?_) _))) fun Z => SOk.pure _
  split_ifs with hj
  · exact ROk.pure _
  · exact hc _ _ _ _ _ ⟨j, hj, rfl, rfl⟩

section Gadgets

variable [Field E] [Algebra Bit E] (K : Constants C E)

theorem SOk.reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R)
    (v : ℕ → R) (count : ℕ) : SOk (G := G) ctx (reshare K ctx codec randomness v count) := by
  unfold ThresholdLeanXmss.reshare record
  exact SOk.bind (SOk.lift (POk.exchange _)) fun _ => SOk.bind (SOk.modify _) fun _ => SOk.pure _

theorem SOk.reshareCollector (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    SOk (G := G) ctx (reshareCollector K ctx randomness v count) := by
  unfold ThresholdLeanXmss.reshareCollector record
  exact SOk.bind (SOk.lift (POk.exchange _)) fun _ => SOk.bind (SOk.lift (POk.exchange _)) fun _ =>
    SOk.bind (SOk.modify _) fun _ => SOk.pure _

theorem SOk.reshareWith (mode : ReshareMode) (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    SOk (G := G) ctx (reshareWith K ctx mode randomness v count) := by
  cases mode
  · exact SOk.reshare K _ _ _ _
  · exact SOk.reshareCollector K _ _ _

theorem POk.openRep (v : Shares C Bit) (count : ℕ) : POk (G := G) ctx (openRep K ctx v count) := by
  unfold ThresholdLeanXmss.openRep
  refine POk.bind (POk.oracleStep (ROk.mapM _ (fun T => ROk.hashQuery _ (by simp [aimedSetupQuery])) _)) fun _ => ?_
  refine POk.bind (POk.exchange _) fun _ => ?_
  refine POk.bind (POk.oracleStep (ROk.mapM _ (fun T => ROk.hashQuery _ (by simp [aimedSetupQuery])) _)) fun _ => ?_
  exact POk.bind (POk.require _) fun _ => POk.pure _

theorem POk.openSh (v : ℕ → E) (count : ℕ) : POk (G := G) ctx (openSh K ctx v count) := by
  unfold ThresholdLeanXmss.openSh
  exact POk.bind (POk.exchange _) fun _ => POk.bind (POk.require _) fun _ => POk.pure _

theorem SOk.coinWith (randomness : PrssOutput C E) (count : ℕ) :
    SOk (G := G) ctx (coinWith K ctx randomness count) := by
  unfold ThresholdLeanXmss.coinWith
  exact SOk.bind (SOk.lift (POk.openSh K _ _)) fun _ => SOk.pure _

theorem SOk.compareDigests (salts : Shares C Bit) :
    SOk (E := E) (G := G) ctx (compareDigests ctx salts) := by
  unfold ThresholdLeanXmss.compareDigests
  refine SOk.bind SOk.get fun st => ?_
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.mapM _ (fun T => ?_) _))) fun _ => ?_
  · split_ifs
    · exact ROk.bind (ROk.hashQuery _ (by simp [aimedSetupQuery])) fun _ => ROk.hashQuery _ (by simp [aimedSetupQuery])
    · exact ROk.pure _
  exact SOk.bind (SOk.lift (POk.exchange _)) fun _ => SOk.lift (POk.require _)

/-- Check gadgets whose calls are all allowed. -/
def CheckOk (ctx : Context C) (gadgets : CheckGadgets C E G) : Prop :=
  (∀ n, SOk ctx (gadgets.coin n)) ∧ (∀ xs, SOk ctx (gadgets.extendMult xs)) ∧
    (∀ n, SOk ctx (gadgets.randElements n)) ∧ (∀ n, SOk ctx (gadgets.randBits n))

theorem SOk.coinKey {gadgets : CheckGadgets C E G} (hg : CheckOk ctx gadgets) :
    SOk ctx (coinKey K gadgets) := by
  unfold ThresholdLeanXmss.coinKey
  exact SOk.bind SOk.get fun _ => SOk.bind (hg.1 1) fun _ =>
    SOk.lift (POk.oracleStep (ROk.hashQuery _ (by simp [aimedSetupQuery])))

theorem SOk.expand (key : HashOutput) (count : ℕ) :
    SOk (G := G) ctx (ThresholdLeanXmss.expand K key count) := by
  unfold ThresholdLeanXmss.expand
  exact SOk.lift (POk.oracleStep (ROk.mapM _ (fun k => ROk.map _ (ROk.hashQuery _ (by simp [aimedSetupQuery]))) _))

theorem ROk.findChallenge (key : HashOutput) :
    ∀ tries index, ROk ctx (findChallenge K key tries index)
  | 0, _ => ROk.pure _
  | tries + 1, index => by
    unfold ThresholdLeanXmss.findChallenge
    refine ROk.bind (ROk.hashQuery _ (by simp [aimedSetupQuery])) fun h => ?_
    dsimp only
    rcases Classical.propDecidable (elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1) with hr | hr
    · exact ROk.findChallenge key tries (index + 1)
    · exact ROk.pure _

theorem SOk.challenge {gadgets : CheckGadgets C E G} (hg : CheckOk ctx gadgets) :
    SOk ctx (challenge K gadgets) := by
  unfold ThresholdLeanXmss.challenge
  refine SOk.bind (SOk.coinKey K hg) fun key => ?_
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.findChallenge K key _ _))) fun r => ?_
  split
  · exact SOk.pure _
  · exact SOk.failure

theorem SOk.check {gadgets : CheckGadgets C E G} (hg : CheckOk ctx gadgets) (tuples : List (Tuple C)) :
    SOk ctx (check K ctx gadgets tuples) := by
  unfold ThresholdLeanXmss.check
  dsimp only
  split_ifs
  · exact SOk.pure _
  refine SOk.bind (SOk.pure _) fun _ => ?_
  refine SOk.bind (SOk.coinKey K hg) fun key => ?_
  refine SOk.bind (SOk.expand K _ _) fun τ => ?_
  refine SOk.bind (SOk.lift (POk.require _)) fun _ => ?_
  refine SOk.bind (SOk.foldlM _ (fun x j => ?_) _ _) fun d₁ => ?_
  · exact SOk.bind (hg.2.1 _) fun _ => SOk.bind (SOk.challenge K hg) fun _ => SOk.pure _
  refine SOk.bind (SOk.foldlM _ (fun x j => ?_) _ _) fun d₂ => ?_
  · exact SOk.bind (hg.2.1 _) fun _ => SOk.bind (SOk.challenge K hg) fun _ => SOk.pure _
  refine SOk.bind (hg.2.2.1 _) fun w => ?_
  refine SOk.bind (hg.2.1 _) fun q => ?_
  refine SOk.bind (hg.2.2.2 _) fun salts => ?_
  refine SOk.bind (SOk.compareDigests _) fun _ => ?_
  refine SOk.bind (SOk.challenge K hg) fun r => ?_
  exact SOk.bind (SOk.lift (POk.openSh K _ _)) fun _ => SOk.lift (POk.require _)

theorem checkOk_real : CheckOk (G := G) ctx (realCheckGadgets K ctx) := by
  refine ⟨fun n => ?_, fun xs => ?_, fun n => ?_, fun n => ?_⟩
  · exact SOk.bind (SOk.prssRandomness _ (codecOk_element K) _ _) fun _ => SOk.coinWith K _ _
  · exact SOk.bind (SOk.prssRandomness _ (codecOk_element K) _ _) fun _ => SOk.reshare K _ _ _ _
  · exact SOk.prssRandomness _ (codecOk_element K) _ _
  · exact SOk.prssRandomness _ codecOk_bit _ _

/-- Run gadgets whose calls are all allowed. -/
def RunOk (ctx : Context C) (gadgets : RunGadgets C E G) : Prop :=
  (∀ x y n, SOk ctx (gadgets.mult x y n)) ∧ (∀ v n, SOk ctx (gadgets.rerand v n)) ∧
    (∀ xs, SOk ctx (gadgets.verify xs)) ∧ (∀ v n, SOk ctx (gadgets.output v n))

theorem runOk_real (mode : ReshareMode) : RunOk (G := G) ctx (realRunGadgets K ctx mode) := by
  refine ⟨fun x y n => ?_, fun v n => ?_, fun xs => ?_, fun v n => ?_⟩
  · exact SOk.bind (SOk.prssRandomness _ codecOk_bit _ _) fun _ => SOk.reshareWith K _ _ _ _
  · exact SOk.bind (SOk.prssRandomness _ codecOk_bit _ _) fun _ => SOk.reshare K _ _ _ _
  · exact SOk.check K (checkOk_real K) xs
  · exact SOk.lift (POk.openRep K _ _)

theorem SOk.runJobs {gadgets : RunGadgets C E G} (hg : RunOk ctx gadgets) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) : SOk ctx (runJobs K gadgets jobs inputs) := by
  unfold ThresholdLeanXmss.runJobs
  dsimp only
  refine SOk.bind (SOk.foldlM _ (fun x layer => ?_) _ _) fun d => ?_
  · exact SOk.bind (hg.1 _ _ _) fun _ => SOk.pure _
  exact SOk.bind (hg.2.1 _ _) fun _ => SOk.bind (hg.2.2.1 _) fun _ =>
    SOk.bind (hg.2.2.2 _ _) fun _ => SOk.pure _

end Gadgets

theorem ROk.flatMapM (f : α → OracleComp (RoSpec C) (List β)) (hf : ∀ a, ROk ctx (f a)) :
    ∀ xs : List α, ROk ctx (xs.flatMapM f)
  | [] => by simpa using ROk.pure (ctx := ctx) ([] : List β)
  | x :: xs => by
    rw [List.flatMapM_cons]
    exact ROk.bind (hf x) fun _ => ROk.bind (ROk.flatMapM f hf xs) fun _ => ROk.pure _

theorem POk.inputShares (job : Job) : POk (E := E) (G := G) ctx (inputShares ctx job) := by
  unfold ThresholdLeanXmss.inputShares
  refine POk.bind (POk.oracleStep (ROk.mapM _ (fun T => ?_) _)) fun _ => POk.pure _
  split_ifs
  · exact ROk.flatMapM _ (fun x => ROk.map _ (ROk.map _ (ROk.hashQuery _ (by simp [aimedSetupQuery])))) _
  · exact ROk.pure _

section Ceremony

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem SOk.ceremonyBatch (jobs : List Job) :
    SOk (G := G) ctx (ceremonyBatch K circuits settings ctx jobs) := by
  unfold ThresholdLeanXmssSecurity.ceremonyBatch
  refine SOk.bind SOk.get fun lk => ?_
  refine SOk.bind (SOk.lift (POk.mapM _ (fun job => POk.inputShares job) _)) fun inputs => ?_
  refine SOk.bind (SOk.lift (SOk.runJobs K (runOk_real K _) _ _ _)) fun out => ?_
  exact SOk.bind (SOk.set _) fun _ => SOk.pure _

theorem SOk.batched (size : ℕ) (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hrun : ∀ jobs, SOk ctx (run jobs)) (jobs : List Job) : SOk ctx (batched size run jobs) := by
  unfold ThresholdLeanXmss.batched
  exact SOk.bind (SOk.mapM _ hrun _) fun _ => SOk.pure _

theorem SOk.ceremonyOutput (parameter : PublicParameter)
    (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hrun : ∀ jobs, SOk ctx (run jobs)) (top : TopTree) (tree : Tree) :
    SOk ctx (ceremonyOutput (m := StateT σ (PartyM C E G))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter run top tree) := by
  have hl : ∀ {γ : Type} (oa : OracleComp HashSpec γ),
      SOk (σ := σ) ctx (StateT.lift (oracleStep (E := E) (G := G) (tweakable oa))) :=
    fun oa => SOk.lift (POk.oracleStep (ROk.tweakable oa))
  cases tree with
  | top =>
    unfold ThresholdLeanXmss.ceremonyOutput
    refine SOk.bind (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact SOk.pure _
    · dsimp only
      generalize merkleNode _ _ _ _ _ = M
      apply SOk.bind
      · exact hl _
      · intro _
        exact SOk.pure _
  | bottom b =>
    unfold ThresholdLeanXmss.ceremonyOutput
    dsimp only
    refine SOk.bind (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact SOk.pure _
    dsimp only
    generalize merkleNode _ _ _ _ _ = M
    refine SOk.bind (hl _) fun root => ?_
    generalize (truncateHash <$> Concrete.oracleHash _ : OracleComp HashSpec _) = M'
    refine SOk.bind (hl _) fun base => ?_
    generalize grind _ _ _ _ _ _ _ = M''
    refine SOk.bind (hl _) fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · exact SOk.pure _
    refine SOk.bind (hrun _) fun o' => ?_
    rcases o' with _ | values
    · exact SOk.pure _
    dsimp only
    generalize merklePath _ _ _ _ = P
    refine SOk.bind (hl _) fun path => ?_
    generalize (Concrete.layerRoot _ _ _ _ _ : OracleComp HashSpec _) = P'
    refine SOk.bind (hl _) fun topRoot => ?_
    split_ifs
    · exact SOk.pure _
    · exact SOk.pure _

/-- The honest continuation never returns to a PRSS setup hash domain. -/
theorem POk.ceremonyAfterSetup (top : TopTree) (tree : Tree) :
    POk (G := G) ctx (ceremonyAfterSetup K circuits settings ctx top tree) := by
  unfold ThresholdLeanXmssSecurity.ceremonyAfterSetup
  refine POk.bind ?_ fun o => ?_
  · rw [StateT.run'_eq]
    exact POk.map _ (SOk.ceremonyOutput _ _ (fun jobs => SOk.batched _ _
      (fun jobs => SOk.ceremonyBatch K circuits settings jobs) jobs) top tree (0, 0))
  · rcases o with _ | output
    · exact POk.failure
    · exact POk.pure _

end Ceremony

def Allowed (rows : RevealRows C) : (LocalSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.inl q) => ¬ aimedSetupQuery q
  | .inr (.inr x) => RowKey rows x.1 x.2.1

def Unallowed (rows : RevealRows C) : (WorldSpec C).Domain → Prop
  | .inl _ => False
  | .inr t => ¬ Allowed rows t

section Execution

/-- The local calls of an operator that the rows do not allow. -/
def PartyUnallowed (rows : RevealRows C) : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => ¬ Allowed rows t
  | _ => False

/-- A pending step whose continuations make only allowed calls. -/
def StepOk (rows : RevealRows C) : Step C E G α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, IsQueryBoundP (resume inbox) (PartyUnallowed (E := E) (G := G) rows) 0
  | .call _ resume => ∀ r, IsQueryBoundP (resume r) (PartyUnallowed (E := E) (G := G) rows) 0

theorem advance_ok (rows : RevealRows C) (p : OracleComp (PartySpec C E G) (Option α))
    (h : IsQueryBoundP p (PartyUnallowed (E := E) (G := G) rows) 0) :
    IsQueryBoundP (advance p) (fun t => ¬ Allowed rows t) 0 ∧
      ∀ s ∈ support (advance p), StepOk rows s := by
  induction p using OracleComp.inductionOn with
  | pure out =>
    refine ⟨by simp [advance_pure], fun s hs => ?_⟩
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ PartyUnallowed rows t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (PartyUnallowed rows) 0 := fun u => by
      have := h.2 u
      rwa [if_neg ht] at this
    rcases t with (u | outbox) | input
    · have e : advance (liftM (OracleSpec.query (spec := PartySpec C E G) (.inl (.inl u))) >>= k) =
          OracleComp.lift (OracleSpec.query (spec := LocalSpec C) u) >>= fun r => advance (k r) := rfl
      rw [e]
      refine ⟨?_, fun s hs => ?_⟩
      · erw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl ht, fun r => by simpa [if_neg ht] using (ih r (hk r)).1⟩
      · simp only [support_bind, Set.mem_iUnion] at hs
        obtain ⟨r, -, hs⟩ := hs
        exact (ih r (hk r)).2 s hs
    · have e : advance (liftM (OracleSpec.query (spec := PartySpec C E G) (.inl (.inr outbox))) >>= k) =
          pure (.wait outbox k) := rfl
      rw [e]
      refine ⟨by simp, fun s hs => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact hk
    · have e : advance (liftM (OracleSpec.query (spec := PartySpec C E G) (.inr input)) >>= k) =
          pure (.call input k) := rfl
      rw [e]
      refine ⟨by simp, fun s hs => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact hk

theorem qb0_free_unallowed (rows : RevealRows C) {oa : OracleComp (LocalSpec C) α}
    (h : IsQueryBoundP oa (fun t => ¬ Allowed rows t) 0) : IsQueryBoundP (free oa) (Unallowed rows) 0 :=
  qb0_simulateQ _ (fun t ht => by
    erw [isQueryBoundP_query_iff]
    exact fun h' => absurd h' ht) oa h

theorem qb0_adversary_unallowed (rows : RevealRows C) (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) (Unallowed rows) 0 :=
  qb0_simulateQ _ (fun t _ => by
    erw [isQueryBoundP_query_iff]
    exact fun h' => h'.elim) _ (qb0_false _)

variable (rows : RevealRows C) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)

theorem stepRound_ok (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ j, StepOk rows (steps j)) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) (Unallowed rows) 0 ∧
      ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps), ∀ j, StepOk rows (r.2.1 j) := by
  unfold stepRound
  split_ifs with hc
  · obtain ⟨⟨i, -, hi⟩, -⟩ := hc
    obtain ⟨e, -⟩ := Option.isSome_iff_exists.mp hi
    exact e.elim
  · constructor
    · refine qb0_bind (qb0_adversary_unallowed _ _) fun x => ?_
      rcases x with ⟨st, sent⟩
      refine qb0_bind (isQueryBoundP_sequenceFin _ fun j => ?_) fun _ => by simp
      have hsj := hs j
      rcases hstep : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
      · simp
      · rw [hstep] at hsj
        dsimp only
        split_ifs
        · simp
        · exact qb0_free_unallowed rows (advance_ok rows _ (hsj _)).1
      · simp
    · intro r hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨⟨st, sent⟩, -, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨steps', hsteps', hr⟩ := hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      intro j
      have hm := mem_support_sequenceFin' _ steps' hsteps' j
      have hsj := hs j
      dsimp only at hm ⊢
      revert hm
      rcases hstep : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
      · intro hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        rw [hm]; exact trivial
      · rw [hstep] at hsj
        dsimp only
        split_ifs
        · intro hm
          simp only [support_pure, Set.mem_singleton_iff] at hm
          rw [hm]; exact trivial
        · intro hm
          exact (advance_ok rows _ (hsj _)).2 _ (support_simulateQ_subset _ _ hm)
      · intro hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        rw [hm]; exact trivial

theorem executeRounds_ok :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      (∀ j, StepOk rows (steps j)) →
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps) (Unallowed rows) 0
  | 0, state, steps, _ => by simp [executeRounds]
  | fuel + 1, state, steps, hs => by
    rw [executeRounds_succ]
    split_ifs
    · simp
    · have h := stepRound_ok rows D A state steps hs
      exact qb0_bind_support h.1 fun r hr => executeRounds_ok fuel _ _ (h.2 r hr)

/-- A program of operator `ctx` makes only calls that the rows allow, when the rows give `ctx` its
keys. -/
theorem partyUnallowed_of_bad {ctx : Context C} {shared : List HashOutput}
    (hrow : rows ctx.self = some (ctx.prss, shared)) (t : (PartySpec C E G).Domain)
    (ht : PartyUnallowed rows t) : PartyBad ctx t := by
  rcases t with ((u | (q | x)) | outbox) | input
  · exact ht trivial
  · by_contra hk
    exact ht hk
  · intro hv
    exact ht ⟨ctx.self, ctx.prss, shared, hrow, hv⟩
  · exact ht.elim
  · exact ht.elim

end Execution

theorem afterDerivation_allowed [Field E] [Algebra Bit E]
    (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (r : A.State × Option (RevealRows C)) :
    IsQueryBoundP (afterDerivation K circuits settings top tree D A x Z r)
      (Unallowed (rowsOf r.2)) 0 := by
  rcases r with ⟨st, _ | rows⟩
  · exact qb0_adversary_unallowed _ _
  · have hr : rowsOf (some rows) = rows := rfl
    unfold afterDerivation
    rw [hr]
    dsimp only
    generalize ceremonyFuel circuits settings - 2 = n
    have h2 : ∀ i, StepOk rows (suspendStep (fun prss => (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree :
          PartyM C E RealSpec TreeOutput)) (prssFinishStep i (rows i))) := by
      intro i
      rcases hrow : rows i with _ | ⟨out, shared⟩
      · exact trivial
      · intro inbox
        unfold exchangeResume
        dsimp only
        split_ifs
        · simp
        · have hp : POk (G := RealSpec) (⟨i, x i, out⟩ : Context C)
              ((do require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0]); pure out) >>=
                fun prss => (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree :
                  PartyM C E RealSpec TreeOutput)) := by
            rw [bind_assoc]
            refine POk.bind (POk.require _) fun _ => ?_
            rw [pure_bind]
            exact POk.ceremonyAfterSetup K circuits settings top tree
          exact IsQueryBoundP.of_imp (partyUnallowed_of_bad rows (ctx := ⟨i, x i, out⟩) hrow) hp
    exact qb0_bind (executeRounds_ok rows D A n st _ h2) fun _ => qb0_adversary_unallowed _ _


theorem echoReferenceRound_allowed [Field E] [Algebra Bit E] (prims : Primitives)
    (rows : RevealRows C) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (next : C.Party → PartyM C E RealSpec α)
    (state : A.State) (hn : ∀ i, IsQueryBoundP (next i).run (PartyUnallowed (G := RealSpec) rows) 0) :
    IsQueryBoundP (aimedEchoReferenceRound prims D A active h parts revealed next state)
      (Unallowed rows) 0 ∧
      ∀ r ∈ support (aimedEchoReferenceRound prims D A active h parts revealed next state),
        ∀ i, StepOk rows (r.2.1 i) := by
  unfold aimedEchoReferenceRound
  constructor
  · refine qb0_bind (qb0_adversary_unallowed rows _) fun r => ?_
    refine qb0_bind (isQueryBoundP_sequenceFin _ fun i => ?_) fun _ => by simp
    apply qb0_free_unallowed
    split_ifs
    · exact (advance_ok rows _ (hn i)).1
    · simp
  · intro r hr
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨s, _, steps, hs, rfl⟩ := hr
    intro i
    have hi := mem_support_sequenceFin' _ steps hs i
    have hi' : steps i ∈ support (if AimedEchoAccepted D active s.2 h
        (fun i => (aimedReferenceKeys prims D h (fun _ => 0) parts revealed i).term) i
        then advance (next i).run else (pure (.done none) : OracleComp (LocalSpec C) _)) :=
      support_simulateQ_subset _ _ hi
    split_ifs at hi'
    · exact (advance_ok rows _ (hn i)).2 _ hi'
    · simp only [support_pure, Set.mem_singleton_iff] at hi'
      change StepOk rows (steps i)
      rw [hi']
      trivial

theorem echoReferenceExecution_allowed [Field E] [Algebra Bit E] (prims : Primitives)
    (rows : RevealRows C) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (next : C.Party → PartyM C E RealSpec α)
    (fuel : ℕ) (state : A.State)
    (hn : ∀ i, IsQueryBoundP (next i).run (PartyUnallowed (G := RealSpec) rows) 0) :
    IsQueryBoundP (aimedEchoReferenceExecution prims D A active h parts revealed next fuel state)
      (Unallowed rows) 0 := by
  cases fuel with
  | zero => simp [aimedEchoReferenceExecution]
  | succ fuel =>
    unfold aimedEchoReferenceExecution
    split_ifs
    · simp
    · have he := echoReferenceRound_allowed prims rows D A active h parts revealed next state hn
      exact qb0_bind_support he.1 fun r hr => executeRounds_ok rows D A fuel _ _ (he.2 r hr)

end AimedSetupDomain

/-- Protected setup cells can be read by counted calls only after the boundary. -/
def aimedFreeSetup : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inl q)) => aimedSetupQuery q
  | _ => False

theorem aimedFreeSetup_unallowed (rows : RevealRows C) (t : (WorldSpec C).Domain) :
    aimedFreeSetup t → AimedSetupDomain.Unallowed rows t := by
  rcases t with ((n | q | x) | p) | (n | q | x) <;>
    simp [aimedFreeSetup, AimedSetupDomain.Unallowed, AimedSetupDomain.Allowed]

theorem afterDerivation_noSetup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (r : A.State × Option (RevealRows C)) :
    IsQueryBoundP (afterDerivation K circuits settings top tree D A x Z r) aimedFreeSetup 0 :=
  IsQueryBoundP.of_imp (aimedFreeSetup_unallowed _) (AimedSetupDomain.afterDerivation_allowed
    K circuits settings top tree D A x Z r)

set_option linter.constructorNameAsVariable false in
theorem aimedReferenceAfter_noSetup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State) :
    IsQueryBoundP (aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
      sentCommit sentReveal state) aimedFreeSetup 0 := by
  let rows : RevealRows C := fun i => some
    (aimedReferenceKeys prims D h normal parts (fun i j => sentReveal j i) i, [])
  have hb : IsQueryBoundP (aimedReferenceAfter prims K circuits settings top tree D A x Z
      h normal active parts sentCommit sentReveal state) (AimedSetupDomain.Unallowed rows) 0 := by
    unfold aimedReferenceAfter
    generalize ceremonyFuel circuits settings - 2 = fuel
    refine qb0_bind (AimedSetupDomain.echoReferenceExecution_allowed prims rows D A
      (AimedReferenceActive D h active sentCommit sentReveal) h parts
      (fun i j => sentReveal j i)
      (fun i => ceremonyAfterSetup K circuits settings
        ⟨i, x i, aimedReferenceKeys prims D h normal parts (fun i j => sentReveal j i) i⟩ top tree)
      fuel state ?_)
      fun _ => AimedSetupDomain.qb0_adversary_unallowed rows _
    intro i
    exact IsQueryBoundP.of_imp (AimedSetupDomain.partyUnallowed_of_bad rows (ctx :=
      ⟨i, x i, aimedReferenceKeys prims D h normal parts (fun i j => sentReveal j i) i⟩) rfl)
        (AimedSetupDomain.POk.ceremonyAfterSetup K circuits settings top tree)
  generalize aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
    sentCommit sentReveal state = game at hb ⊢
  exact IsQueryBoundP.of_imp (aimedFreeSetup_unallowed rows) hb

theorem evalDist_aimedFresh_hidden (D : C.Coalition) :
    𝒟[(fun u : KeygenFresh C => fun n : {n : KeyName C // Hidden D n} =>
      keygenTableOf u.1 u.2 n.val) <$> ($ᵗ (KeygenFresh C))] =
      𝒟[$ᵗ ({n : KeyName C // Hidden D n} → HashOutput)] := by
  rw [evalDist_map, ← evalDist_keygenRestrict, ← evalDist_map, Functor.map_map]
  have hf : (fun u : KeygenFresh C => fun n : {n : KeyName C // Hidden D n} =>
      keygenTableOf u.1 u.2 n.val) ∘ keygenRestrict =
      (fun u : KeyName C → HashOutput => u ∘ Subtype.val) := by
    funext u n
    obtain ⟨n, hn⟩ := n
    cases n with
    | parameter => exact hn.elim
    | term T => rfl
    | pair p => rfl
  change 𝒟[((fun u : KeygenFresh C => fun n : {n : KeyName C // Hidden D n} =>
    keygenTableOf u.1 u.2 n.val) ∘ keygenRestrict) <$> ($ᵗ (KeyName C → HashOutput))] = _
  rw [hf]
  exact evalDist_uniformSample_map_comp_injective (R := HashOutput) Subtype.val_injective

theorem probEvent_aimedFreshKey_le (D : C.Coalition) (k : HashOutput) :
    Pr[fun u : KeygenFresh C => ∃ n, Hidden D n ∧ keygenTableOf u.1 u.2 n = k |
      $ᵗ (KeygenFresh C)] ≤ (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 := by
  have he := probEvent_congr_evalDist (evalDist_aimedFresh_hidden D) (fun u => ∃ n, u n = k)
  simp only [probEvent_map, Function.comp_def, Subtype.exists, exists_prop] at he
  rw [he]
  simpa only [Subtype.exists] using probEvent_aimedNamedKey_le D k

theorem aimedReferenceKeys_hidden (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) (n : KeyName C) (k : HashOutput)
    (hn : Hidden D n) (hk : ValidKey i (aimedReferenceKeys prims D h table parts revealed i) n k) :
    k = table n := by
  cases n with
  | parameter => exact hn.elim
  | term T =>
    rcases hk with ⟨hi, rfl⟩
    simp only [aimedReferenceKeys, keygenMaskKeys, if_neg hn, if_pos hi]
  | pair p =>
    obtain ⟨j, hj, rfl, rfl⟩ := hk
    have hc : ¬ (i ∈ D.1 ∨ j ∈ D.1) := by
      unfold Hidden Committee.pairOf at hn
      split_ifs at hn <;> simp_all
    simp only [aimedReferenceKeys, keygenMaskKeys, dif_neg hj, if_neg hc]

theorem aimedReferenceRows_hidden (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (n : KeyName C) (k : HashOutput)
    (hk : RowKey (aimedReferenceRows prims D h table active parts sentCommit sentReveal) n k)
    (hn : Hidden D n) : k = table n := by
  obtain ⟨i, keys, shared, hr, hk⟩ := hk
  rw [aimedReferenceRows_active] at hr
  split_ifs at hr with ha
  · cases Option.some.inj hr
    exact aimedReferenceKeys_hidden prims D h table parts (fun i j => sentReveal j i) i n k hn hk

/-- The reference continuation can guess the fresh watched keys only through counted calls. -/
theorem probEvent_aimedFresh_uniform_le {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition)
    (rows : KeygenFresh C → RevealRows C)
    (hrows : ∀ u n k, RowKey (rows u) n k → Hidden D n → k = keygenTableOf u.1 u.2 n)
    (game : OracleComp (WorldSpec C) α) (q : ℕ) (hq : IsQueryBoundP game WorldCounted q) (s : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (KeygenFresh C) >>= fun u =>
      (simulateQ (flagImpl impl (fun t u => AimedCall D (rows u) t) u) game).run (s, false)] ≤
      (q : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  refine (probEvent_flag_le impl _ ($ᵗ (KeygenFresh C)) WorldCounted
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256)
    (fun t u hu => (aimedCall_point D (rows u) t hu).1)
    (fun t _ => ?_) game q s hq).trans (le_of_eq (mul_div_assoc _ _ _).symm)
  refine (probEvent_mono fun u _ hu => ?_).trans (probEvent_aimedFreshKey_le D (aimedPoint t))
  obtain ⟨_, n, hk, hn⟩ := aimedCall_point D (rows u) t hu
  exact ⟨n, hn, (hrows u n _ hk hn).symm⟩

theorem probEvent_aimedEagerFresh_le {α : Type} (D : C.Coalition)
    (h : Query C → HashOutput) (rows : KeygenFresh C → RevealRows C)
    (hrows : ∀ u n k, RowKey (rows u) n k → Hidden D n → k = keygenTableOf u.1 u.2 n)
    (game : OracleComp (WorldSpec C) α) (q : ℕ) (hq : IsQueryBoundP game WorldCounted q) :
    Pr[fun y => y.2 = true | ($ᵗ (KeygenFresh C)) >>= fun u =>
      aimedEagerFlag prims D h (rows u) game] ≤ (q : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  have hb := probEvent_aimedFresh_uniform_le (lazyKeyWorld prims D) D rows hrows game q hq
    (aimedFullCache h, ∅)
  rw [probEvent_bind_eq_tsum] at hb ⊢
  simp only [aimedEagerFlag, ← probEvent_aimedFullCache, lazyAimedImpl] at ⊢
  exact hb

section ReferenceGuess

attribute [local irreducible] aimedReferenceAfter

theorem probEvent_aimedReferenceFresh_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State) (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    Pr[fun y => y.2 = true | ($ᵗ (KeygenFresh C)) >>= fun u =>
      aimedEagerFlag prims D h
        (aimedReferenceRows prims D h (keygenTableOf u.1 u.2) active parts sentCommit sentReveal)
        (aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
          sentCommit sentReveal state)] ≤
      (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  have hq : IsQueryBoundP
      (aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
        sentCommit sentReveal state) WorldCounted ((ceremonyFuel circuits settings - 2) * step + final) := by
    exact aimedReferenceAfter_bound prims K circuits settings top tree D A x Z h normal active
      parts sentCommit sentReveal state step final (by exact hround) (by exact hfinal)
  generalize aimedReferenceAfter prims K circuits settings top tree D A x Z h normal active parts
    sentCommit sentReveal state = game at hq ⊢
  exact probEvent_aimedEagerFresh_le prims D h _
    (fun u n k hk hn => aimedReferenceRows_hidden prims D h _ active parts sentCommit sentReveal n k hk hn)
    game _ hq

end ReferenceGuess

theorem probEvent_aimedPrefixCells_kernel_le {α : Type} (D : C.Coalition)
    (kernel : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant D kernel)
    (q : ℕ) (targets : α → Fin q → Query C) :
    Pr[fun r => ∃ i, AimedPrefixCell D r.1.1 r.2 (targets r.1.2 i) |
      (do let r ← keygenPartsKernel kernel
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤ ((q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin q))
    (do let r ← keygenPartsKernel kernel
        let u ← $ᵗ (KeygenFresh C)
        pure (r, u)) (fun i r => AimedPrefixCell D r.1.1 r.2 (targets r.1.2 i))
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ((Finset.sum_le_sum fun i _ =>
    probEvent_aimedPrefixCell_kernel_le D kernel hinv (fun a => targets a i)).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, mul_div_assoc]
  exact le_rfl

/-- Install the independently named hidden seeds at their canonical PRSS inputs. -/
def aimedInstall (D : C.Coalition) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a : S → HashOutput) (u : KeygenFresh C) : S → HashOutput :=
  keygenExchangeTable (aimedCanonicalPoint D S parts hmem) a
    (fun n => keygenTableOf u.1 u.2 n.val)

theorem evalDist_aimedInstall {α : Type} (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (k : (S → HashOutput) → ProbComp α) :
    𝒟[($ᵗ (S → HashOutput)) >>= k] =
    𝒟[do let a ← $ᵗ (S → HashOutput)
          let u ← $ᵗ (KeygenFresh C)
          k (aimedInstall D S parts hmem a u)] := by
  have he := evalDist_aimedCanonical_refresh D S parts hmem (aimed_hiddenInput_injective D parts hc)
    (fun a _ => k a)
  refine he.trans ?_
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro a
  rw [evalDist_bind, ← evalDist_aimedFresh_hidden D, ← evalDist_bind, bind_map_left]
  rfl

def aimedRefresh (D : C.Coalition) (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) : S → HashOutput :=
  aimedInstall D S parts hmem (keygenMix (fun q : S => AimedEchoCell D u q.val) a echo) u

/-- Canonical installation and echo refresh preserve the unconditional random-oracle law. -/
theorem evalDist_aimedRefresh {α : Type} (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (k : (S → HashOutput) → ProbComp α) :
    𝒟[($ᵗ (S → HashOutput)) >>= k] =
    𝒟[do let u ← $ᵗ (KeygenFresh C)
          let a ← $ᵗ (S → HashOutput)
          let echo ← $ᵗ (S → HashOutput)
          k (aimedRefresh D S parts hmem a echo u)] := by
  rw [evalDist_aimedInstall D S parts hmem hc k]
  rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro u
  have he := evalDist_bind_keygenMix (fun q : S => AimedEchoCell D u q.val)
    (fun a => k (aimedInstall D S parts hmem a u))
  rw [uniformSample_prod_bind] at he
  exact he.symm

theorem aimedRefresh_off (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) (q : Query C)
    (hq : ¬ AimedPrefixCell D parts u q) :
    prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u)) q =
      prssHashAt prims (prssExtend S a) q := by
  have ho : prssExtend S (aimedRefresh D S parts hmem a echo u) q = prssExtend S a q := by
    unfold prssExtend
    split_ifs with hqS
    · unfold aimedRefresh aimedInstall
      rw [aimedCanonical_refresh_off D S parts hmem _ _ ⟨q, hqS⟩ (by
        intro n hn he
        exact hq (Or.inl ⟨n, hn, he⟩))]
      exact if_neg (fun he => hq (Or.inr he))
    · rfl
  cases q <;> simp only [prssHashAt] <;> first | exact ho | (split_ifs <;> first | rfl | exact ho)

theorem aimedRefresh_canonical (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (n : KeyName C) (hn : Hidden D n) :
    prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u))
      (hiddenInput parts n) = keygenTableOf u.1 u.2 n := by
  have he := keygenExchangeTable_at (aimedCanonicalPoint D S parts hmem)
    (fun x y hxy => aimed_hiddenInput_injective D parts hc (congrArg Subtype.val hxy))
    (keygenMix (fun q : S => AimedEchoCell D u q.val) a echo)
    (fun n : {n : KeyName C // Hidden D n} => keygenTableOf u.1 u.2 n.val) ⟨n, hn⟩
  cases n with
  | parameter => exact hn.elim
  | term T =>
    change prssExtend S (aimedRefresh D S parts hmem a echo u) (hiddenInput parts (.term T)) = _
    rw [prssExtend, dif_pos (hmem _ hn)]
    exact he
  | pair p =>
    change prssExtend S (aimedRefresh D S parts hmem a echo u) (hiddenInput parts (.pair p)) = _
    rw [prssExtend, dif_pos (hmem _ hn)]
    exact he

theorem aimedRefresh_echo (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) (q : Query C)
    (hq : AimedEchoCell D u q) (hS : q ∈ S) :
    prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u)) q = echo ⟨q, hS⟩ := by
  obtain ⟨values, rfl⟩ := aimedEchoCell_sharedKeys hq
  simp only [prssHashAt, prssExtend, dif_pos hS, aimedRefresh, aimedInstall]
  rw [aimedCanonical_refresh_off D S parts hmem _ _ _ (by
    intro n hn he
    cases n with
    | parameter => exact hn.elim
    | term T => cases he
    | pair p => cases he)]
  exact if_pos hq

theorem aimedReferenceKeys_derive_congr (D : C.Coalition) (h₁ h₂ : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (hc : ¬ KeygenClash D parts)
    (hh : ∀ kind values, ¬ AimedHiddenInput D parts (.derive .prss kind values) →
      h₁ (.derive .prss kind values) = h₂ (.derive .prss kind values))
    (i : C.Party) (hi : i ∉ D.1) :
    aimedReferenceKeys prims D h₁ table parts revealed i =
      aimedReferenceKeys prims D h₂ table parts revealed i := by
  have hview : ∀ k, k ∉ D.1 → aimedCorruptView D parts revealed i k = parts k := by
    intro k hk
    simp [aimedCorruptView, hk]
  simp only [aimedReferenceKeys, keygenMaskKeys, D_deriveKeys]
  congr 1
  · funext T
    split_ifs with hT hiT
    · apply hh
      intro hv
      apply not_keygenHiddenInput_knownTerm D parts hc _ T hT
        (hview _ (keygenFirstHonest_holder D T).2)
      exact (aimedHiddenInput_iff D parts _).mp hv
    · rfl
    · rfl
    · rfl
  · funext j
    split_ifs with hji hj
    · rfl
    · apply hh
      intro hv
      have hj' : j ∈ D.1 := hj.resolve_left hi
      apply not_keygenHiddenInput_crossPair D parts hc
        (aimedCorruptView D parts revealed i) (C.pairOf i j (Ne.symm hji))
      · unfold Committee.pairOf
        split_ifs <;> simp [hj']
      · unfold Committee.pairOf
        split_ifs
        · exact Or.inl (hview i hi)
        · exact Or.inr (hview i hi)
      · exact (aimedHiddenInput_iff D parts _).mp hv
    · rfl

theorem aimedRefresh_referenceKeys (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (table : KeyName C → HashOutput) (revealed : C.Party → Mail C E)
    (i : C.Party) (hi : i ∉ D.1) :
    aimedReferenceKeys prims D (prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u)))
      table parts revealed i =
      aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a)) table parts revealed i := by
  apply aimedReferenceKeys_derive_congr prims D _ _ table parts revealed hc _ i hi
  intro kind values hn
  apply aimedRefresh_off
  rintro (hc | he)
  · exact hn hc
  · obtain ⟨l, hl⟩ := aimedEchoCell_sharedKeys he
    cases hl

def AimedEchoCollision {ι : Type} (point : C.Party → C.Party → ι) (echo : ι → HashOutput) : Prop :=
  ∃ p : C.Pair, point p.1.1 p.1.2 ≠ point p.1.2 p.1.1 ∧
    echo (point p.1.1 p.1.2) = echo (point p.1.2 p.1.1)

theorem probEvent_aimedEchoCollision_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (point : C.Party → C.Party → ι) :
    Pr[AimedEchoCollision point | $ᵗ (ι → HashOutput)] ≤
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256 := by
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset C.Pair)
    ($ᵗ (ι → HashOutput)) (fun p echo => point p.1.1 p.1.2 ≠ point p.1.2 p.1.1 ∧
      echo (point p.1.1 p.1.2) = echo (point p.1.2 p.1.1))
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ((Finset.sum_le_sum (g := fun _ => (Fintype.card HashOutput : ℝ≥0∞)⁻¹)
    (fun p _ => ?_)).trans ?_)
  · by_cases hp : point p.1.1 p.1.2 = point p.1.2 p.1.1
    · simp [hp]
    · exact (probEvent_mono fun _ _ h => h.2).trans_eq (probEvent_fun_collide hp)
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_hashOutput,
      Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
    exact le_rfl

theorem aimedRefresh_echo_regular (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (revealed : C.Party → Mail C E)
    (hn : ¬ AimedEchoCollision
      (fun i j => (⟨.sharedKeys .prss ((sharedTerms i j).map
        (aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a)) (keygenTableOf u.1 u.2)
          parts revealed i).term), hsk i j _⟩ : S)) echo) :
    ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i → KeygenShareHidden D i j →
      let h := prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u))
      let keys := fun i => (aimedReferenceKeys prims D h (keygenTableOf u.1 u.2) parts revealed i).term
      prssEcho h keys i j = prssEcho h keys j i →
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
          Query.sharedKeys .prss ((sharedTerms j i).map (keys j)) := by
  intro i j hi hj hji hs
  dsimp only
  simp only [prssEcho]
  rw [aimedRefresh_referenceKeys prims D S parts hmem hc a echo u _ revealed i hi,
    aimedRefresh_referenceKeys prims D S parts hmem hc a echo u _ revealed j hj]
  let keys := fun i => (aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a))
    (keygenTableOf u.1 u.2) parts revealed i).term
  have hx := aimedEchoCell_of D u hji.symm hi hj hs (keys i) (fun T hT hiT _ =>
    aimedReferenceKeys_hidden prims D _ _ parts revealed i (.term T) _ hT ⟨hiT, rfl⟩)
  have hy := aimedEchoCell_of D u hji hj hi (keygenShareHidden_comm hs) (keys j) (fun T hT hjT _ =>
    aimedReferenceKeys_hidden prims D _ _ parts revealed j (.term T) _ hT ⟨hjT, rfl⟩)
  change prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u))
      (.sharedKeys .prss ((sharedTerms i j).map (keys i))) =
    prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u))
      (.sharedKeys .prss ((sharedTerms j i).map (keys j))) → _
  rw [aimedRefresh_echo prims D S parts hmem a echo u _ hx (hsk i j _),
    aimedRefresh_echo prims D S parts hmem a echo u _ hy (hsk j i _)]
  intro he
  by_contra hne
  apply hn
  rcases lt_or_gt_of_ne hji.symm with hij | hji'
  · exact ⟨⟨(i, j), hij⟩, fun he => hne (congrArg Subtype.val he), he⟩
  · exact ⟨⟨(j, i), hji'⟩, fun he => hne (congrArg Subtype.val he).symm, he.symm⟩

theorem aimedEchoCheck_oracle_congr (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h₁ h₂ : Query C → HashOutput)
    (keys₁ keys₂ : C.Party → C.Term → HashOutput)
    (hk : ∀ i, i ∉ D.1 → keys₁ i = keys₂ i)
    (he : ∀ i j, i ∉ D.1 → j ≠ i → prssEcho h₁ keys₁ i j = prssEcho h₂ keys₂ i j)
    (i : C.Party) (hi : i ∉ D.1) :
    AimedEchoCheck D active sent h₁ keys₁ i ↔ AimedEchoCheck D active sent h₂ keys₂ i := by
  unfold AimedEchoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj, he i j hi hji]
  · simp only [if_neg hj]
    split_ifs
    · rw [hk i hi, hk j hj]
    · rw [he i j hi hji, he j i hj hji.symm]
    · rfl

theorem aimedEchoReferenceRound_oracle_congr {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h₁ h₂ : Query C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next₁ next₂ : C.Party → PartyM C E RealSpec α) (state : A.State)
    (hk : ∀ i, i ∉ D.1 →
      aimedReferenceKeys prims D h₁ (fun _ => 0) parts revealed i =
        aimedReferenceKeys prims D h₂ (fun _ => 0) parts revealed i)
    (he : ∀ i j, i ∉ D.1 → j ≠ i →
      prssEcho h₁ (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts revealed i).term) i j =
        prssEcho h₂ (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts revealed i).term) i j)
    (hn : ∀ i, i ∉ D.1 → next₁ i = next₂ i) :
    aimedEchoReferenceRound prims D A active h₁ parts revealed next₁ state =
      aimedEchoReferenceRound prims D A active h₂ parts revealed next₂ state := by
  unfold aimedEchoReferenceRound
  dsimp only
  rw [prssEchoVisible_congr D active h₁ h₂ _ _ (fun i j hi hj =>
    he i j hi (fun hij => hi (hij ▸ hj)))]
  apply bind_congr
  rintro ⟨state', sent⟩
  congr 1
  congr 1
  funext i
  have ha : AimedEchoAccepted D active sent h₁
      (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts revealed i).term) i ↔
      AimedEchoAccepted D active sent h₂
      (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts revealed i).term) i := by
    by_cases hi : i ∈ D.1
    · simp [AimedEchoAccepted, hi]
    · simp only [AimedEchoAccepted, aimedEchoCheck_oracle_congr D active sent h₁ h₂ _ _
        (fun i hi => congrArg PrssKeys.term (hk i hi)) he i hi]
  simp only [ha]
  by_cases hh : AimedEchoAccepted D active sent h₂
      (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts revealed i).term) i
  · rw [if_pos hh, if_pos hh, hn i hh.1]
  · rw [if_neg hh, if_neg hh]

theorem aimedEchoReferenceExecution_oracle_congr {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h₁ h₂ : Query C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (next₁ next₂ : C.Party → PartyM C E RealSpec α) (fuel : ℕ) (state : A.State)
    (hk : ∀ i, i ∉ D.1 →
      aimedReferenceKeys prims D h₁ (fun _ => 0) parts revealed i =
        aimedReferenceKeys prims D h₂ (fun _ => 0) parts revealed i)
    (he : ∀ i j, i ∉ D.1 → j ≠ i →
      prssEcho h₁ (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts revealed i).term) i j =
        prssEcho h₂ (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts revealed i).term) i j)
    (hn : ∀ i, i ∉ D.1 → next₁ i = next₂ i) :
    aimedEchoReferenceExecution prims D A active h₁ parts revealed next₁ fuel state =
      aimedEchoReferenceExecution prims D A active h₂ parts revealed next₂ fuel state := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [aimedEchoReferenceExecution]
    split_ifs
    · rfl
    · rw [aimedEchoReferenceRound_oracle_congr prims D A active h₁ h₂ parts revealed
        next₁ next₂ state hk he hn]

section ReferenceCongruence

attribute [local irreducible] aimedReferenceAfter

set_option maxHeartbeats 20000 in
set_option linter.constructorNameAsVariable false in
theorem aimedReferenceAfter_oracle_congr (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h₁ h₂ : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State)
    (hc : ∀ i j values, h₁ (.commit .prss i j values) = h₂ (.commit .prss i j values))
    (hk : ∀ table i, i ∉ D.1 →
      aimedReferenceKeys prims D h₁ table parts (fun i j => sentReveal j i) i =
        aimedReferenceKeys prims D h₂ table parts (fun i j => sentReveal j i) i)
    (he : ∀ i j, i ∉ D.1 → j ≠ i →
      prssEcho h₁ (fun i => (aimedReferenceKeys prims D h₁ (fun _ => 0) parts
        (fun i j => sentReveal j i) i).term) i j =
        prssEcho h₂ (fun i => (aimedReferenceKeys prims D h₂ (fun _ => 0) parts
          (fun i j => sentReveal j i) i).term) i j) :
    aimedReferenceAfter prims K circuits settings top tree D A x Z h₁ normal active parts
      sentCommit sentReveal state =
      aimedReferenceAfter prims K circuits settings top tree D A x Z h₂ normal active parts
        sentCommit sentReveal state := by
  have ha : AimedReferenceActive D h₁ active sentCommit sentReveal =
      AimedReferenceActive D h₂ active sentCommit sentReveal := by
    funext i
    simp only [AimedReferenceActive, aimedReferenceOpenCheck, hc]
  unfold aimedReferenceAfter
  generalize ceremonyFuel circuits settings - 2 = fuel
  rw [ha]
  exact congrArg (fun game => game >>= fun r => worldRoles.adversary (Z r))
    (aimedEchoReferenceExecution_oracle_congr prims D A _ h₁ h₂ parts
      (fun i j => sentReveal j i)
      (fun i => ceremonyAfterSetup K circuits settings
        ⟨i, x i, aimedReferenceKeys prims D h₁ normal parts (fun i j => sentReveal j i) i⟩ top tree)
      (fun i => ceremonyAfterSetup K circuits settings
        ⟨i, x i, aimedReferenceKeys prims D h₂ normal parts (fun i j => sentReveal j i) i⟩ top tree)
      fuel state (hk _) he (fun i hi => congrArg
        (fun keys => ceremonyAfterSetup K circuits settings ⟨i, x i, keys⟩ top tree)
        (hk normal i hi)))

end ReferenceCongruence

theorem aimed_sequenceFin_map {α β : Type} :
    ∀ {n : ℕ} (f : Fin n → ProbComp α) (g : Fin n → α → β),
      Concrete.sequenceFin (fun i => g i <$> f i) =
        (fun a i => g i (a i)) <$> Concrete.sequenceFin f
  | 0, f, g => by
    simp only [Concrete.sequenceFin, map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f, g => by
    simp only [Concrete.sequenceFin, bind_map_left, map_bind, map_pure,
      aimed_sequenceFin_map (fun i : Fin n => f i.succ) (fun i => g i.succ)]
    apply bind_congr
    intro a
    apply bind_congr
    intro tail
    congr 1
    funext i
    cases i using Fin.cases <;> rfl

def aimedPartsMask (D : C.Coalition) (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => if i ∈ D.1 then ⟨0, fun _ => 0, fun _ => 0⟩ else parts i

/-- Dummy corrupt parts can be sampled too: masking them recovers the actual setup sampler. -/
theorem evalDist_aimedPartsMask (D : C.Coalition) :
    𝒟[aimedPartsMask D <$> (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))] =
      𝒟[prssSampleParts D] := by
  unfold aimedPartsMask prssSampleParts
  rw [← aimed_sequenceFin_map]
  apply evalDist_sequenceFin_congr
  intro i
  change 𝒟[(fun own : Parts C => if i ∈ D.1 then ⟨0, fun _ => 0, fun _ => 0⟩ else own) <$>
    sampleParts] = _
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
    rw [map_eq_bind_pure_comp]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _
  · simp only [if_neg hi]
    rw [show (fun own : Parts C => own) <$> (sampleParts : ProbComp (Parts C)) =
      sampleParts from id_map _]

theorem aimedPartsMask_data (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    prssDataMask D (prssDataAt h (aimedPartsMask D parts)) = prssDataMask D (prssDataAt h parts) := by
  funext i
  unfold prssDataMask
  split_ifs with hi
  · rfl
  · simp only [prssDataAt, aimedPartsMask, if_neg hi]

theorem aimedPartsMask_early (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    prssEarlyRounds D A state h (aimedPartsMask D parts) = prssEarlyRounds D A state h parts := by
  rw [← prssEarlyDataRounds_at, ← prssEarlyDataRounds_at,
    ← prssEarlyDataRounds_mask D A state (prssDataAt h (aimedPartsMask D parts)),
    aimedPartsMask_data, prssEarlyDataRounds_mask]

/-- All parts are uniform in the eager experiment; corrupt parts remain absent from the view. -/
theorem evalDist_aimedFlagProgram_at_fullParts (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (keys : KeyName C × HashOutput → Digest)
    (h : Query C → HashOutput) :
    𝒟[simulateQ (prssLocalAt prims h) (simulateQ (aimedKeyLocal prims D keys)
      (aimedFlagProgram K circuits settings top tree D A x z Z))] =
    𝒟[do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let state ← simulateQ (prssLocalAt prims h) (A.start (corruptInputs D x) z)
      let r ← simulateQ (prssLocalAt prims h) (prssEarlyRounds D A state h parts)
      aimedEagerFinish prims K circuits settings top tree D A x Z keys h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)] := by
  rw [aimedFlagProgram_at]
  conv_rhs => rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro state
  rw [evalDist_bind, ← evalDist_aimedPartsMask D, ← evalDist_bind, bind_map_left]
  simp only [aimedPartsMask_early, aimedPartsMask_data]

section RefreshedReference

attribute [local irreducible] aimedReferenceAfter

theorem aimedRefresh_referenceAfter (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S) (hc : ¬ KeygenClash D parts)
    (a echo : S → HashOutput) (u : KeygenFresh C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State)
    (hd : ∀ i j : C.Party, j ≠ i → ¬ AimedEchoCell D u
      (.sharedKeys .prss ((sharedTerms i j).map
        (aimedReferenceKeys prims D (prssHashAt prims (prssExtend S a)) (fun _ => 0) parts
          (fun i j => sentReveal j i) i).term))) :
    aimedReferenceAfter prims K circuits settings top tree D A x Z
      (prssHashAt prims (prssExtend S (aimedRefresh D S parts hmem a echo u))) normal active parts
      sentCommit sentReveal state =
      aimedReferenceAfter prims K circuits settings top tree D A x Z
        (prssHashAt prims (prssExtend S a)) normal active parts sentCommit sentReveal state := by
  apply aimedReferenceAfter_oracle_congr prims K circuits settings top tree D A x Z _ _ normal active
    parts sentCommit sentReveal state
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

end RefreshedReference

theorem probEvent_aimedDelivered_le (D : C.Coalition) (point : C.Party → C.Party → Query C) :
    Pr[fun u => ∃ i j, j ≠ i ∧ AimedEchoCell D u (point i j) | $ᵗ (KeygenFresh C)] ≤
      ((2 * Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let targets : C.Pair × Bool → Query C := fun p =>
    if p.2 then point p.1.1.1 p.1.1.2 else point p.1.1.2 p.1.1.1
  refine (probEvent_mono (q := fun u => ∃ p, AimedEchoCell D u (targets p)) ?_).trans
    (by simpa only [keygenFinish_card_pair] using probEvent_aimedEchoDelivered_le D targets)
  rintro u _ ⟨i, j, hji, he⟩
  rcases lt_or_gt_of_ne hji.symm with hij | hji'
  · exact ⟨(⟨(i, j), hij⟩, true), he⟩
  · exact ⟨(⟨(j, i), hji'⟩, false), he⟩

def aimedLocalSetup : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => aimedSetupQuery q
  | _ => False

theorem aimedKeyLocal_setup_step (D : C.Coalition) (keys : KeyName C × HashOutput → Digest)
    (t : (WorldSpec C).Domain) (ht : ¬ aimedFreeSetup t) :
    IsQueryBoundP (aimedKeyLocal prims D keys t) aimedLocalSetup
      (if WorldCounted t then 1 else 0) := by
  have hquery (t : (LocalSpec C).Domain) (n : ℕ) (ht : aimedLocalSetup t → 0 < n) :
      IsQueryBoundP (OracleComp.lift (OracleSpec.query t)) aimedLocalSetup n := by
    erw [isQueryBoundP_query_iff]
    exact ht
  rcases t with ((n | q | x) | p) | (n | q | x)
  · exact hquery _ _ fun h => h.elim
  · apply hquery
    intro hq
    cases q <;> simp_all [aimedLocalSetup, aimedSetupQuery, WorldCounted, Counted]
  · exact hquery _ _ fun h => h.elim
  · simp [aimedKeyLocal]
  · exact hquery _ _ fun h => h.elim
  · exact hquery _ _ fun h => (ht h).elim
  · simp only [aimedKeyLocal, WorldCounted, if_false]
    split_ifs
    · simp
    · exact hquery (.inr (.inr x)) _ fun h => h.elim

theorem aimedKeyLocal_setup_bound {α : Type} (D : C.Coalition)
    (keys : KeyName C × HashOutput → Digest) (game : OracleComp (WorldSpec C) α) (q : ℕ)
    (hq : IsQueryBoundP game WorldCounted q) (hn : IsQueryBoundP game aimedFreeSetup 0) :
    IsQueryBoundP (simulateQ (aimedKeyLocal prims D keys) game) aimedLocalSetup q := by
  induction game using OracleComp.inductionOn generalizing q with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq hn
    have ht : ¬ aimedFreeSetup t := hn.1.resolve_right (Nat.lt_irrefl 0)
    rw [simulateQ_bind, simulateQ_spec_query]
    refine (isQueryBoundP_bind (aimedKeyLocal_setup_step prims D keys t ht)
      (fun u _ => ih u _ (hq.2 u) (by simpa only [if_neg ht] using hn.2 u))).mono ?_
    split_ifs with hc
    · have hp := hq.1.resolve_left (not_not.mpr hc)
      omega
    · omega

theorem aimedLocalHashInputs_setup (t : (LocalSpec C).Domain) :
    ((keygenLocalHashInputs t).filter fun q => decide (aimedSetupQuery q)).length =
      if aimedLocalSetup t then 1 else 0 := by
  rcases t with n | q | x
  · simp [keygenLocalHashInputs, aimedLocalSetup]
  · by_cases hq : aimedSetupQuery q <;> simp [keygenLocalHashInputs, aimedLocalSetup, hq]
  · simp [keygenLocalHashInputs, aimedLocalSetup, aimedSetupQuery]

theorem aimedSetupLog_length_le {α : Type} (oa : OracleComp (LocalSpec C) α)
    (n : ℕ) (hq : IsQueryBoundP oa aimedLocalSetup n) (r : α × List (Query C))
    (hr : r ∈ support (keygenHashLog oa)) :
    (r.2.filter fun q => decide (aimedSetupQuery q)).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure a =>
    simp only [keygenHashLog_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [keygenHashLog_bind, keygenHashLog_query] at hr
    simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
      support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, l, ⟨v, _, he⟩, a, rest, hk, hr⟩ := hr
    cases he
    cases hr
    have hrest := ih u _ (hq.2 u) (a, rest) hk
    simp only [List.filter_append, List.length_append, aimedLocalHashInputs_setup]
    split_ifs at hrest ⊢ with ht <;> simp_all <;> omega

theorem aimed_adversary_noSetup {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) aimedFreeSetup 0 :=
  IsQueryBoundP.of_imp (aimedFreeSetup_unallowed (fun _ => none))
    (AimedSetupDomain.qb0_adversary_unallowed (fun _ => none) oa)

section ReferenceLog

attribute [local irreducible] aimedReferenceAfter

theorem aimedReferenceProgram_noSetup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) :
    IsQueryBoundP (aimedReferenceProgram prims K circuits settings top tree D A x z Z h normal parts)
      aimedFreeSetup 0 := by
  unfold aimedReferenceProgram
  refine qb0_bind (aimed_adversary_noSetup _) fun state => ?_
  refine qb0_bind (aimed_adversary_noSetup _) fun r => ?_
  rcases r with ⟨state', sent, _ | revealed⟩
  · exact aimed_adversary_noSetup _
  · exact aimedReferenceAfter_noSetup prims K circuits settings top tree D A x Z h normal _ parts
      sent revealed state'

theorem aimedEarlyRounds_bound (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (prssEarlyRounds D A state h parts) Counted (2 * step) := by
  unfold prssEarlyRounds
  refine (isQueryBoundP_bind (m := step) (hround _ _) (fun r _ => ?_)).mono (by omega)
  rcases r with ⟨state', sent⟩
  dsimp only
  split_ifs
  · exact isQueryBoundP_pure _ _ _
  · simp only [pure_bind]
    exact (isQueryBoundP_bind (m := 0) (hround _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by simp)

theorem aimedReferenceProgram_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) (start step final : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    IsQueryBoundP (aimedReferenceProgram prims K circuits settings top tree D A x z Z h normal parts)
      WorldCounted (start + 2 * step + ((ceremonyFuel circuits settings - 2) * step + final)) := by
  unfold aimedReferenceProgram
  refine (isQueryBoundP_bind (m := 2 * step + ((ceremonyFuel circuits settings - 2) * step + final))
    (isQueryBoundP_adversary _ _ (hstart _ _)) (fun state _ => ?_)).mono (by omega)
  refine isQueryBoundP_bind (isQueryBoundP_adversary _ _ (aimedEarlyRounds_bound D A state h parts step hround))
    (fun r _ => ?_)
  rcases r with ⟨state', sent, _ | revealed⟩
  · exact (isQueryBoundP_adversary _ _ (hfinal _)).mono (Nat.le_add_left _ _)
  · exact aimedReferenceAfter_bound prims K circuits settings top tree D A x Z h normal _ parts
      sent revealed state' step final (by exact hround) (by exact hfinal)

end ReferenceLog

theorem probEvent_aimedPrefixLog_kernel_le {α : Type} (D : C.Coalition)
    (kernel : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant D kernel)
    (q : ℕ) (log : α → List (Query C))
    (hlen : ∀ parts r, r ∈ support (kernel parts) → (log r).length ≤ q) :
    Pr[fun r => ∃ v ∈ log r.1.2, AimedPrefixCell D r.1.1 r.2 v |
      (do let r ← keygenPartsKernel kernel
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤ ((q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let targets : α → Fin q → Query C := fun a i => (log a).getD i.val (.streamKey 0)
  have hb := probEvent_aimedPrefixCells_kernel_le D kernel hinv q targets
  refine le_trans ?_ hb
  apply probEvent_mono
  rintro r hr ⟨v, hv, hbad⟩
  simp only [keygenPartsKernel, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, ⟨parts, _, out, ho, rfl⟩, u, _, rfl⟩ := hr
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hv
  refine ⟨⟨i, hi.trans_le (hlen parts out ho)⟩, ?_⟩
  simpa only [targets, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he] using hbad

theorem aimedPrefixCell_setup (D : C.Coalition) (parts : C.Party → Parts C)
    (u : KeygenFresh C) (q : Query C) : AimedPrefixCell D parts u q → aimedSetupQuery q := by
  rintro (⟨n, hn, rfl⟩ | he)
  · cases n with
    | parameter => exact hn.elim
    | term T => trivial
    | pair p => trivial
  · obtain ⟨values, rfl⟩ := aimedEchoCell_sharedKeys he
    trivial

def aimedReferenceLog (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) : ProbComp (Bool × List (Query C)) :=
  simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
    (aimedReferenceProgram prims K circuits settings top tree D A x z Z h normal parts)))

section ReferenceLogBound

attribute [local irreducible] aimedReferenceProgram aimedReferenceAfter

theorem aimedReferenceLog_privateInvariant (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput) :
    KeygenPrivateInvariant D (aimedReferenceLog prims K circuits settings top tree D A x z Z h keys normal) :=
  aimedReferenceProgram_privateInvariant prims K circuits settings top tree D A x z Z h normal
    (fun game => simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys) game)))

theorem aimedReferenceLog_length_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (start step final : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final)
    (r : Bool × List (Query C))
    (hr : r ∈ support (aimedReferenceLog prims K circuits settings top tree D A x z Z h keys normal parts)) :
    (r.2.filter fun q => decide (aimedSetupQuery q)).length ≤
      start + 2 * step + ((ceremonyFuel circuits settings - 2) * step + final) := by
  exact aimedSetupLog_length_le _ _
    (aimedKeyLocal_setup_bound prims D keys _ _
      (aimedReferenceProgram_bound prims K circuits settings top tree D A x z Z h normal parts
        start step final hstart hround hfinal)
      (aimedReferenceProgram_noSetup prims K circuits settings top tree D A x z Z h normal parts)) r
    (support_simulateQ_subset _ _ hr)

theorem probEvent_aimedReferenceLog_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput)
    (start step final : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v |
      (do let r ← keygenPartsKernel (aimedReferenceLog prims K circuits settings top tree D A x z Z h keys normal)
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤
      (((start + 2 * step + ((ceremonyFuel circuits settings - 2) * step + final)) * prssKeyCount C : ℕ) : ℝ≥0∞) /
        2 ^ 256 := by
  have hb := probEvent_aimedPrefixLog_kernel_le D
    (aimedReferenceLog prims K circuits settings top tree D A x z Z h keys normal)
    (aimedReferenceLog_privateInvariant prims K circuits settings top tree D A x z Z h keys normal)
    (start + 2 * step + ((ceremonyFuel circuits settings - 2) * step + final))
    (fun r => r.2.filter fun q => decide (aimedSetupQuery q))
    (fun parts r hr => aimedReferenceLog_length_le prims K circuits settings top tree D A x z Z h keys normal
      parts start step final hstart hround hfinal r hr)
  refine le_trans ?_ hb
  apply probEvent_mono
  rintro r _ ⟨v, hv, hb⟩
  exact ⟨v, List.mem_filter.mpr ⟨hv, decide_eq_true (aimedPrefixCell_setup D _ _ _ hb)⟩, hb⟩

end ReferenceLogBound

theorem aimed_prssHashAt_idem (h : Query C → HashOutput) :
    prssHashAt prims (prssHashAt prims h) = prssHashAt prims h := by
  funext q
  cases q <;> simp only [prssHashAt]
  split_ifs <;> rfl

theorem aimed_prssLocalAt_hashAt (h : Query C → HashOutput) :
    prssLocalAt prims (prssHashAt prims h) = prssLocalAt prims h := by
  funext t
  rcases t with n | q | x
  · rfl
  · exact congrArg pure (congrFun (aimed_prssHashAt_idem prims h) q)
  · rfl

theorem aimedReferenceKeys_table_congr (D : C.Coalition) (h : Query C → HashOutput)
    (left right : KeyName C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (ht : ∀ n, Hidden D n → left n = right n) (i : C.Party) :
    aimedReferenceKeys prims D h left parts revealed i = aimedReferenceKeys prims D h right parts revealed i := by
  simp only [aimedReferenceKeys, keygenMaskKeys]
  congr 1
  · funext T
    split_ifs with hT hiT
    · rfl
    · exact ht (.term T) hT
    · rfl
  · funext j
    split_ifs with hji hc
    · rfl
    · rfl
    · apply ht
      unfold Hidden Committee.pairOf
      split_ifs <;> simp_all

theorem aimedReferenceKeys_maskParts (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (i : C.Party) :
    aimedReferenceKeys prims D h table (aimedPartsMask D parts) revealed i =
      aimedReferenceKeys prims D h table parts revealed i := by
  have hv : aimedCorruptView D (aimedPartsMask D parts) revealed i = aimedCorruptView D parts revealed i := by
    funext j
    unfold aimedCorruptView aimedPartsMask
    split_ifs <;> rfl
  simp only [aimedReferenceKeys, hv]

theorem aimedReferenceRows_maskParts (D : C.Coalition) (h : Query C → HashOutput)
    (table : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E) :
    aimedReferenceRows prims D h table active (aimedPartsMask D parts) sentCommit sentReveal =
      aimedReferenceRows prims D h table active parts sentCommit sentReveal := by
  funext i
  simp only [aimedReferenceRows, aimedReferenceKeys_maskParts]

theorem aimedPartsMask_hiddenInput (D : C.Coalition) (parts : C.Party → Parts C)
    (n : KeyName C) (hn : Hidden D n) : hiddenInput (aimedPartsMask D parts) n = hiddenInput parts n := by
  cases n with
  | parameter => exact hn.elim
  | term T =>
    simp only [hiddenInput, prssTermInput]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiT := of_decide_eq_true (List.mem_filter.mp hi).2
    simp only [aimedPartsMask, if_neg (hidden_term_holders D hn i hiT)]
  | pair p => simp [hiddenInput, prssPairInput, aimedPartsMask, hn.1, hn.2]

theorem aimedFixedBoundary_reference {σ : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (state : σ) (sentCommit sentReveal : C.Party → Mail C E) :
    aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts))
      (state, sentCommit, some sentReveal) =
    (state, some (aimedReferenceRows prims D (prssHashAt prims h)
      (fun n => h (hiddenInput parts n)) (prssCommitActive D sentCommit) parts sentCommit sentReveal)) := by
  have hc : prssCommitInbox (E := E) D (prssDataMask D (prssDataAt h parts)) sentCommit =
      prssCommitInbox D (prssDataAt (prssHashAt prims h) (aimedPartsMask D parts)) sentCommit := by
    funext i j
    unfold prssCommitInbox
    split_ifs with hj
    · rfl
    · simp only [prssDataMask, if_neg hj, prssDataAt, aimedPartsMask]
      simp only [if_neg hj, prssHashAt]
  simp only [aimedFixedBoundary]
  rw [hc]
  have hp : (fun i => (prssDataMask D (prssDataAt h parts) i).1) = aimedPartsMask D parts := by
    funext i
    unfold prssDataMask aimedPartsMask
    split_ifs <;> rfl
  rw [hp]
  rw [aimedRevealRowsFixed_reference, aimedReferenceRows_maskParts]
  have hk (i : C.Party) := aimedReferenceKeys_table_congr prims D (prssHashAt prims h)
    (fun n => prssHashAt prims h (hiddenInput (aimedPartsMask D parts) n))
    (fun n => h (hiddenInput parts n)) parts (fun i j => sentReveal j i)
    (by
      intro n hn
      rw [aimedPartsMask_hiddenInput D parts n hn]
      cases n with
      | parameter => exact hn.elim
      | term T => rfl
      | pair p => rfl) i
  congr 2
  funext i
  simp only [aimedReferenceRows, hk]

open OracleComp.ProgramLogic.Relational

/-- A prefix oracle change is charged once, even when the later experiment is arbitrary. -/
theorem probEvent_aimedPrefix_swap_le {α β : Type} (h₁ h₂ : Query C → HashOutput)
    (P : Query C → Prop) (hP : ∀ v, ¬ P v → h₁ v = h₂ v)
    (early : OracleComp (LocalSpec C) α) (next : α → ProbComp β) (event : β → Prop) :
    Pr[event | simulateQ (fixedLocal prims h₁) early >>= next] ≤
      Pr[event | simulateQ (fixedLocal prims h₂) early >>= next] +
        Pr[fun r => ∃ v ∈ r.2, P v | simulateQ (fixedLocal prims h₂) (keygenHashLog early)] := by
  let ref := simulateQ (fixedLocal prims h₂) (keygenHashLog early) >>= fun r =>
    (fun b => (r, b)) <$> next r.1
  have hc : RelTriple ref (simulateQ (fixedLocal prims h₁) early >>= next)
      (fun a b => (∃ v ∈ a.1.2, P v) ∨ a.2 = b) := by
    refine relTriple_bind (relTriple_fixedLocal_swap prims h₁ h₂ P hP early) fun a b hab => ?_
    rcases hab with hbad | he
    · apply relTriple_of_support_left
      intro y hy _
      simp only [support_map, Set.mem_image] at hy
      obtain ⟨out, _, rfl⟩ := hy
      exact Or.inl hbad
    · subst b
      rw [map_eq_bind_pure_comp]
      conv => arg 2; rw [← bind_pure (next a.1)]
      refine relTriple_bind (relTriple_refl _) fun y y' hy => relTriple_pure_pure (Or.inr hy)
  have he : Pr[fun r => event r.2 | ref] =
      Pr[event | simulateQ (fixedLocal prims h₂) early >>= next] := by
    rw [← fst_simulateQ_keygenHashLog prims h₂ early, bind_map_left]
    simp only [ref, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  calc
    _ ≤ Pr[fun r => event r.2 ∨ ∃ v ∈ r.1.2, P v | ref] :=
      probEvent_le_of_relTriple (relTriple_symm hc) (fun b a hab hb => by
        rcases hab with hbad | hsame
        · exact Or.inr hbad
        · exact Or.inl (hsame ▸ hb))
    _ ≤ Pr[fun r => event r.2 | ref] + Pr[fun r => ∃ v ∈ r.1.2, P v | ref] := probEvent_or_le _ _ _
    _ ≤ _ := by
      rw [he]
      exact add_le_add le_rfl (probEvent_pair_fst_le
        (simulateQ (fixedLocal prims h₂) (keygenHashLog early))
        (fun r : α × List (Query C) => next r.1) (fun r => ∃ v ∈ r.2, P v))

theorem aimedFlagQueries_fst {α : Type} (D : C.Coalition) (rows : RevealRows C)
    (game : OracleComp (WorldSpec C) α) (b : Bool) :
    Prod.fst <$> (simulateQ (aimedFlagQueries D rows) game).run b = game := by
  induction game using OracleComp.inductionOn generalizing b with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, aimedFlagQueries,
      StateT.run_mk, bind_map_left, map_bind, ih]

theorem aimedHashLog_map {α β : Type} (f : α → β) (game : OracleComp (LocalSpec C) α) :
    keygenHashLog (f <$> game) = (fun r => (f r.1, r.2)) <$> keygenHashLog game := by
  rw [map_eq_bind_pure_comp, keygenHashLog_bind]
  simp only [Function.comp_def, keygenHashLog_pure, pure_bind, List.append_nil]
  rfl

/-- Flag instrumentation does not change the distribution of the oracle-input log. -/
theorem aimedFlagQueries_log {α : Type} (D : C.Coalition) (rows : RevealRows C)
    (keys : KeyName C × HashOutput → Digest) (game : OracleComp (WorldSpec C) α) (b : Bool) :
    Prod.snd <$> keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
      ((simulateQ (aimedFlagQueries D rows) game).run b)) =
    Prod.snd <$> keygenHashLog (simulateQ (aimedKeyLocal prims D keys) game) := by
  conv_rhs => rw [← aimedFlagQueries_fst D rows game b]
  rw [simulateQ_map, aimedHashLog_map, Functor.map_map]

/-- Change a continuation oracle while charging its uninstrumented input log. -/
theorem probEvent_aimedFlag_swap_le {α : Type} (D : C.Coalition) (rows : RevealRows C)
    (h₁ h₂ : Query C → HashOutput) (P : Query C → Prop)
    (hP : ∀ v, ¬ P v → prssHashAt prims h₁ v = prssHashAt prims h₂ v)
    (keys : KeyName C × HashOutput → Digest) (game : OracleComp (WorldSpec C) α) :
    Pr[fun r => r.2 = true | simulateQ (prssLocalAt prims h₁)
      (simulateQ (aimedKeyLocal prims D keys) ((simulateQ (aimedFlagQueries D rows) game).run false))] ≤
    Pr[fun r => r.2 = true | simulateQ (prssLocalAt prims h₂)
      (simulateQ (aimedKeyLocal prims D keys) ((simulateQ (aimedFlagQueries D rows) game).run false))] +
    Pr[fun r => ∃ v ∈ r.2, P v | simulateQ (prssLocalAt prims h₂)
      (keygenHashLog (simulateQ (aimedKeyLocal prims D keys) game))] := by
  let oa := simulateQ (aimedKeyLocal prims D keys)
    ((simulateQ (aimedFlagQueries D rows) game).run false)
  have hb := (probOutput_fixedLocal_swap_le prims (prssHashAt prims h₁)
    (prssHashAt prims h₂) P hP (Prod.snd <$> oa)).1
  simp only [simulateQ_map, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def,
    aimedHashLog_map] at hb
  have he : Pr[fun r => ∃ v ∈ r.2, P v |
      simulateQ (prssLocalAt prims h₂) (keygenHashLog oa)] =
      Pr[fun r => ∃ v ∈ r.2, P v | simulateQ (prssLocalAt prims h₂)
        (keygenHashLog (simulateQ (aimedKeyLocal prims D keys) game))] := by
    have hl := congrArg (simulateQ (prssLocalAt prims h₂))
      (aimedFlagQueries_log prims D rows keys game false)
    simp only [simulateQ_map] at hl
    have hp := congrArg (fun oc => Pr[fun l => ∃ v ∈ l, P v | oc]) hl
    simpa only [probEvent_map, Function.comp_def] using hp
  simp only [← aimed_prssLocalAt_eq] at hb
  rw [he] at hb
  exact hb

theorem aimedPrivateInvariant_of_exposed {α : Type} (D : C.Coalition)
    (f : (C.Party → Parts C) → α)
    (hf : ∀ parts, f (keygenExposedParts D parts) = f parts) : KeygenPrivateInvariant D f := by
  have hp := keygenExposedParts_privateInvariant D
  constructor
  · intro a T hT c parts
    rw [← hf (shiftAt a (some T) none c parts), hp.1 a T hT c parts, hf parts]
  · intro p hp₁ hp₂ c parts
    rw [← hf (shiftAt p.1.1 none (some p.1.2) c parts), hp.2 p hp₁ hp₂ c parts, hf parts]

def aimedEarlyProgram (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :=
  A.start (corruptInputs D x) z >>= fun state => prssEarlyRounds D A state h parts

theorem aimedEarlyProgram_exposed (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    aimedEarlyProgram D A x z h (keygenExposedParts D parts) = aimedEarlyProgram D A x z h parts := by
  simp only [aimedEarlyProgram, aimedEarlyRounds_exposed]

theorem probEvent_aimedProtectedLog_kernel_le {α : Type} (D : C.Coalition)
    (kernel : (C.Party → Parts C) → ProbComp (α × List (Query C)))
    (hinv : KeygenPrivateInvariant D kernel) (q : ℕ)
    (hlen : ∀ parts r, r ∈ support (kernel parts) →
      (r.2.filter fun v => decide (aimedSetupQuery v)).length ≤ q) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v |
      (do let r ← keygenPartsKernel kernel
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤ ((q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hb := probEvent_aimedPrefixLog_kernel_le D kernel hinv q
    (fun r => r.2.filter fun v => decide (aimedSetupQuery v)) hlen
  refine le_trans ?_ hb
  apply probEvent_mono
  rintro r _ ⟨v, hv, hb⟩
  exact ⟨v, List.mem_filter.mpr ⟨hv, decide_eq_true (aimedPrefixCell_setup D _ _ _ hb)⟩, hb⟩

theorem probEvent_aimedEarlyLog_le (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (h : Query C → HashOutput) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v |
      (do let r ← keygenPartsKernel (fun parts => simulateQ (prssLocalAt prims h)
            (keygenHashLog (aimedEarlyProgram D A x z h parts)))
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤ (((start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by rw [aimedEarlyProgram_exposed]))
  intro parts r hr
  apply aimedSetupLog_length_le _ _ _ r (support_simulateQ_subset _ _ hr)
  apply IsQueryBoundP.of_imp (p' := Counted)
  · intro t ht
    rcases t with n | v | a
    · exact ht.elim
    · cases v <;> simp_all [aimedLocalSetup, aimedSetupQuery, Counted]
    · exact ht.elim
  · exact isQueryBoundP_bind (hstart _ _) (fun state _ => aimedEarlyRounds_bound D A state h parts step hround)

def aimedReferenceTail (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) :
    A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E) → OracleComp (WorldSpec C) Bool
  | (_, _, none) => pure false
  | (state, sent, some revealed) =>
    aimedReferenceAfter prims K circuits settings top tree D A x Z h normal
      (prssCommitActive D sent) parts sent revealed state

section ReferenceTail

attribute [local irreducible] aimedReferenceAfter

theorem aimedReferenceTail_exposed (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    aimedReferenceTail prims K circuits settings top tree D A x Z h normal (keygenExposedParts D parts) r =
      aimedReferenceTail prims K circuits settings top tree D A x Z h normal parts r := by
  rcases r with ⟨state, sent, _ | revealed⟩
  · rfl
  · exact aimedReferenceAfter_exposed prims K circuits settings top tree D A x Z h normal _ parts _ _ _

theorem aimedReferenceTail_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    IsQueryBoundP (aimedReferenceTail prims K circuits settings top tree D A x Z h normal parts r)
      WorldCounted ((ceremonyFuel circuits settings - 2) * step + final) := by
  rcases r with ⟨state, sent, _ | revealed⟩
  · exact isQueryBoundP_pure _ _ _
  · exact aimedReferenceAfter_bound prims K circuits settings top tree D A x Z h normal _ parts _ _ _
      step final (by exact hround) (by exact hfinal)

theorem aimedReferenceTail_noSetup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    IsQueryBoundP (aimedReferenceTail prims K circuits settings top tree D A x Z h normal parts r)
      aimedFreeSetup 0 := by
  rcases r with ⟨state, sent, _ | revealed⟩
  · exact isQueryBoundP_pure _ _ _
  · exact aimedReferenceAfter_noSetup prims K circuits settings top tree D A x Z h normal _ parts _ _ _

end ReferenceTail

def aimedTailLog (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput)
    (parts : C.Party → Parts C) : ProbComp (Bool × List (Query C)) := do
  let r ← simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts)
  simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
    (aimedReferenceTail prims K circuits settings top tree D A x Z h normal parts r)))

section TailLogBound

attribute [local irreducible] aimedReferenceTail

theorem probEvent_aimedTailLog_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (keys : KeyName C × HashOutput → Digest) (normal : KeyName C → HashOutput)
    (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v |
      (do let r ← keygenPartsKernel
            (aimedTailLog prims K circuits settings top tree D A x z Z h keys normal)
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] ≤
      ((((ceremonyFuel circuits settings - 2) * step + final) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  apply probEvent_aimedProtectedLog_kernel_le D _
    (aimedPrivateInvariant_of_exposed D _ (fun parts => by
      simp only [aimedTailLog, aimedEarlyProgram_exposed, aimedReferenceTail_exposed]))
  intro parts out hout
  simp only [aimedTailLog, support_bind, Set.mem_iUnion] at hout
  obtain ⟨r, _, hr⟩ := hout
  exact aimedSetupLog_length_le _ _
    (aimedKeyLocal_setup_bound prims D keys _ _
      (aimedReferenceTail_bound prims K circuits settings top tree D A x Z h normal parts r
        step final hround hfinal)
      (aimedReferenceTail_noSetup prims K circuits settings top tree D A x Z h normal parts r)) out
    (support_simulateQ_subset _ _ hr)

end TailLogBound

theorem aimedReferenceRows_table_congr (D : C.Coalition) (h : Query C → HashOutput)
    (left right : KeyName C → HashOutput) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sentCommit sentReveal : C.Party → Mail C E)
    (he : ∀ n, Hidden D n → left n = right n) :
    aimedReferenceRows prims D h left active parts sentCommit sentReveal =
      aimedReferenceRows prims D h right active parts sentCommit sentReveal := by
  funext i
  simp only [aimedReferenceRows, aimedReferenceKeys_table_congr prims D h left right parts _ he]

theorem aimedFixedBoundary_fullRows {σ : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (state : σ) (sentCommit sentReveal : C.Party → Mail C E) :
    aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts))
      (state, sentCommit, some sentReveal) =
    (state, some (aimedRevealRowsFixed prims D (prssHashAt prims h) (prssCommitActive D sentCommit)
      parts (prssCommitInbox D (prssDataAt (prssHashAt prims h) parts) sentCommit) sentReveal)) := by
  rw [aimedFixedBoundary_reference, aimedRevealRowsFixed_reference]
  congr 2

include prims in
theorem aimedRefresh_commit (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) (i j : C.Party) (values : List HashOutput) :
    prssExtend S (aimedRefresh D S parts hmem a echo u) (.commit .prss i j values) =
      prssExtend S a (.commit .prss i j values) := by
  apply aimedRefresh_off prims D S parts hmem a echo u (.commit .prss i j values)
  rintro (⟨n, hn, he⟩ | he)
  · cases n with
    | parameter => exact hn.elim
    | term T => cases he
    | pair p => cases he
  · obtain ⟨values, he⟩ := aimedEchoCell_sharedKeys he
    cases he

include prims in
theorem aimedRefresh_early (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) :
    aimedEarlyProgram D A x z (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts =
      aimedEarlyProgram D A x z (prssExtend S a) parts := by
  have hd : prssDataAt (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts =
      prssDataAt (prssExtend S a) parts := by
    funext i
    simp only [prssDataAt, aimedRefresh_commit prims]
  simp only [aimedEarlyProgram, prssEarlyRounds, hd]

theorem aimedEarlyProgram_hashAt (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    aimedEarlyProgram D A x z (prssHashAt prims h) parts = aimedEarlyProgram D A x z h parts := by
  have hd : prssDataAt (prssHashAt prims h) parts = prssDataAt h parts := by
    funext i
    simp only [prssDataAt, prssHashAt]
  simp only [aimedEarlyProgram, prssEarlyRounds, hd]

theorem aimedEagerFlag_hashAt {α : Type} (D : C.Coalition) (h : Query C → HashOutput)
    (rows : RevealRows C) (game : OracleComp (WorldSpec C) α) :
    aimedEagerFlag prims D (prssHashAt prims h) rows game = aimedEagerFlag prims D h rows game := by
  simp only [aimedEagerFlag, aimed_prssLocalAt_hashAt]

section RefreshContinuation

attribute [local irreducible] aimedReferenceAfter

theorem probEvent_aimedRefresh_reference (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (sentCommit sentReveal : C.Party → Mail C E) (state : A.State)
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
      (afterDerivation K circuits settings top tree D A x Z r)] =
    Pr[fun y => y.2 = true | aimedEagerFlag prims D h (rowsOf r.2)
      (aimedReferenceAfter prims K circuits settings top tree D A x Z
        (prssHashAt prims (prssExtend S a)) normal (prssCommitActive D sentCommit) parts
        sentCommit sentReveal state)] := by
  dsimp only
  rw [aimedFixedBoundary_fullRows] at ha ⊢
  simp only [rowsOf] at ha ⊢
  let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
  have hkeys (i : C.Party) := aimedReferenceKeys_table_congr prims D (prssHashAt prims h)
    (fun n => prssHashAt prims h (hiddenInput parts n)) (keygenTableOf u.1 u.2) parts
    (fun i j => sentReveal j i) (fun n hn => aimedRefresh_canonical prims D S parts hmem hc a echo u n hn) i
  have hregular := aimedRefresh_echo_regular prims D S parts hmem hsk hc a echo u
    (fun i j => sentReveal j i) he
  have hn := probEvent_aimedEager_reference prims K circuits settings top tree D A x Z
    (prssHashAt prims h) normal (prssCommitActive D sentCommit) parts sentCommit sentReveal state
    (aimedRevealRowsFixed prims D (prssHashAt prims h) (prssCommitActive D sentCommit) parts
      (prssCommitInbox D (prssDataAt (prssHashAt prims h) parts) sentCommit) sentReveal)
    ha (fun n hn => by rw [aimedRefresh_canonical prims D S parts hmem hc a echo u n hn]; exact hz n hn)
    hni hn0 (by simpa only [hkeys] using hregular)
  rw [aimedRefresh_referenceAfter prims K circuits settings top tree D A x Z S normal
    (prssCommitActive D sentCommit) parts hmem hc a echo u sentCommit sentReveal state hd] at hn
  simpa only [aimedEagerFlag_hashAt, Option.getD_some, h] using hn

end RefreshContinuation

/-- Discrete expectation, used only to keep the hybrid's independent samplers explicit. -/
def aimedMean {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, Pr[= a | p] * f a

theorem aimedMean_mono {α : Type} (p : ProbComp α) {f g : α → ℝ≥0∞}
    (h : ∀ a, f a ≤ g a) : aimedMean p f ≤ aimedMean p g :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_left' (h a) _

theorem aimedMean_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    aimedMean p (fun a => f a + g a) = aimedMean p f + aimedMean p g := by
  simp only [aimedMean, mul_add, ENNReal.tsum_add]

theorem aimedMean_const {α : Type} (p : ProbComp α) (c : ℝ≥0∞) : aimedMean p (fun _ => c) = c := by
  rw [aimedMean, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, probFailure_eq_zero, tsub_zero, one_mul]

theorem aimedMean_probEvent {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (event : β → Prop) :
    aimedMean p (fun a => Pr[event | k a]) = Pr[event | p >>= k] := by
  rw [probEvent_bind_eq_tsum]
  rfl

theorem aimedMean_event {α : Type} (p : ProbComp α) (event : α → Prop) :
    aimedMean p (fun a => if event a then 1 else 0) = Pr[event | p] := by
  simp only [aimedMean, mul_ite, mul_one, mul_zero, probEvent_eq_tsum_ite]

theorem aimedMean_comm {α β : Type} (p : ProbComp α) (q : ProbComp β) (f : α → β → ℝ≥0∞) :
    aimedMean p (fun a => aimedMean q (f a)) = aimedMean q (fun b => aimedMean p (fun a => f a b)) := by
  simp only [aimedMean, ← ENNReal.tsum_mul_left, ← mul_assoc]
  rw [ENNReal.tsum_comm]
  simp only [mul_comm]

theorem aimedMean_bind {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (f : β → ℝ≥0∞) :
    aimedMean (p >>= k) f = aimedMean p (fun a => aimedMean (k a) f) := by
  simp only [aimedMean, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_left, mul_assoc]
  rw [ENNReal.tsum_comm]

theorem aimedMean_le_const {α : Type} (p : ProbComp α) (c : ℝ≥0∞) (f : α → ℝ≥0∞)
    (hf : ∀ a, f a ≤ c) : aimedMean p f ≤ c := by
  simpa only [aimedMean_const] using aimedMean_mono p hf

def aimedFinishProbability (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (r : A.State × Option (RevealRows C)) : ℝ≥0∞ :=
  Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true |
    ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
      aimedEagerFinish prims K circuits settings top tree D A x Z keys h r]

theorem aimedFinishProbability_eq (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (r : A.State × Option (RevealRows C)) :
    aimedFinishProbability prims K circuits settings top tree D A x Z h r =
      if KeysApart D (rowsOf r.2) then Pr[fun y => y.2 = true |
        aimedEagerFlag prims D h (rowsOf r.2) (afterDerivation K circuits settings top tree D A x Z r)]
      else 0 := by
  unfold aimedFinishProbability aimedEagerFinish aimedEagerFlag
  by_cases ha : KeysApart D (rowsOf r.2)
  · simp only [probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, ha, true_and, if_true]
  · simp only [probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, ha, false_and, if_false,
      probEvent_False, mul_zero, tsum_zero]

theorem aimedFlagQueries_empty {α : Type} (D : C.Coalition)
    (game : OracleComp (WorldSpec C) α) (b : Bool) :
    (simulateQ (aimedFlagQueries D (fun _ => none)) game).run b = (fun a => (a, b)) <$> game := by
  induction game using OracleComp.inductionOn generalizing b with
  | pure a => simp
  | query_bind t k ih =>
    have ht : ¬ AimedCall D (fun _ => none) t := by
      rcases t with ((n | q | x) | p) | (n | q | x)
      all_goals simp [AimedCall, RowKey]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, aimedFlagQueries,
      StateT.run_mk, bind_map_left, map_bind, ht, decide_false, Bool.or_false, ih]

theorem aimedFinishProbability_none (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput) (state : A.State) :
    aimedFinishProbability prims K circuits settings top tree D A x Z h (state, none) = 0 := by
  rw [aimedFinishProbability_eq]
  split_ifs
  · simp only [rowsOf, Option.getD_none, aimedEagerFlag, aimedFlagQueries_empty,
      simulateQ_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
      Bool.false_eq_true, probEvent_False, mul_zero, tsum_zero]
  · rfl

def AimedFreshZero (D : C.Coalition) (u : KeygenFresh C) : Prop :=
  ∃ n, Hidden D n ∧ keygenTableOf u.1 u.2 n = 0

def AimedDelivered (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (sentReveal : C.Party → Mail C E) (u : KeygenFresh C) : Prop :=
  ∃ i j : C.Party, j ≠ i ∧ AimedEchoCell D u (.sharedKeys .prss ((sharedTerms i j).map
    (aimedReferenceKeys prims D h (fun _ => 0) parts (fun i j => sentReveal j i) i).term))

def aimedCollisionPoints (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (sentReveal : C.Party → Mail C E) (u : KeygenFresh C) (i j : C.Party) : S :=
  ⟨.sharedKeys .prss ((sharedTerms i j).map
    (aimedReferenceKeys prims D h (keygenTableOf u.1 u.2) parts (fun i j => sentReveal j i) i).term), hsk i j _⟩

def AimedBoundaryException {σ : Type} (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (u : KeygenFresh C) (echo : S → HashOutput) : Prop :=
  AimedFreshZero D u ∨ match r.2.2 with
    | none => False
    | some sent => AimedDelivered prims D h parts sent u ∨
        AimedEchoCollision (aimedCollisionPoints prims D S hsk h parts sent u) echo

section RefreshFinish

attribute [local irreducible] aimedReferenceAfter aimedReferenceTail

theorem probEvent_aimedRefresh_finish_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0) :
    let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
    let boundary := aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r
    let game := aimedReferenceTail prims K circuits settings top tree D A x Z
      (prssHashAt prims (prssExtend S a)) normal parts r
    aimedFinishProbability prims K circuits settings top tree D A x Z h boundary ≤
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
      aimedFinishProbability_none]
    exact zero_le
  · rw [aimedFinishProbability_eq]
    split_ifs with ha
    · rw [probEvent_aimedRefresh_reference prims K circuits settings top tree D A x Z S normal parts
        hmem hsk hc a echo u sentCommit sentReveal state hni hn0
        (fun n hn he => hb (Or.inl ⟨n, hn, he⟩))
        (fun i j hij he => hb (Or.inr (Or.inl ⟨i, j, hij, he⟩)))
        (fun he => hb (Or.inr (Or.inr he))) ha]
      simp only [aimedEagerFlag, ← aimedMean_probEvent, aimedReferenceTail]
      rw [← aimedMean_add]
      exact aimedMean_mono _ fun keys => probEvent_aimedFlag_swap_le prims D _ _ _
        (AimedPrefixCell D parts u) (aimedRefresh_off prims D S parts hmem a echo u) keys _
    · exact zero_le

end RefreshFinish

theorem aimedRefresh_boundary_hidden (D : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput) (u : KeygenFresh C)
    {σ : Type} (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (n : KeyName C) (k : HashOutput)
    (hk : RowKey (rowsOf (aimedFixedBoundary prims D
      (prssExtend S (aimedRefresh D S parts hmem a echo u))
      (prssDataMask D (prssDataAt (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts)) r).2) n k)
    (hn : Hidden D n) : k = keygenTableOf u.1 u.2 n := by
  rcases r with ⟨state, sentCommit, _ | sentReveal⟩
  · simp [aimedFixedBoundary, rowsOf, RowKey] at hk
  · rw [aimedFixedBoundary_reference] at hk
    have he := aimedReferenceRows_hidden prims D _ _ _ _ _ _ n k hk hn
    refine he.trans ?_
    have hc' := aimedRefresh_canonical prims D S parts hmem hc a echo u n hn
    cases n with
    | parameter => exact hn.elim
    | term T => exact hc'
    | pair p => exact hc'

section RefreshGuess

attribute [local irreducible] aimedReferenceTail

theorem probEvent_aimedRefresh_guess_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) (a echo : S → HashOutput)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (step final : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => Pr[fun y => y.2 = true |
      aimedEagerFlag prims D (prssExtend S a)
        (rowsOf (aimedFixedBoundary prims D (prssExtend S (aimedRefresh D S parts hmem a echo u))
          (prssDataMask D (prssDataAt (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts)) r).2)
        (aimedReferenceTail prims K circuits settings top tree D A x Z
          (prssHashAt prims (prssExtend S a)) normal parts r)]) ≤
      (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 := by
  rw [aimedMean_probEvent]
  exact probEvent_aimedEagerFresh_le prims D (prssExtend S a) _
    (fun u n k hk hn => aimedRefresh_boundary_hidden prims D S parts hmem hc a echo u r n k hk hn) _ _
    (aimedReferenceTail_bound prims K circuits settings top tree D A x Z _ normal parts r step final
      hround hfinal)

end RefreshGuess

theorem aimedIndicator_or_le (P Q R : Prop) :
    (if P ∨ Q ∨ R then (1 : ℝ≥0∞) else 0) ≤
      (if P then 1 else 0) + (if Q then 1 else 0) + (if R then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

theorem probEvent_aimedBoundaryException_le {σ : Type} (D : C.Coalition) (S : Finset (Query C))
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (r : σ × (C.Party → Mail C E) × Option (C.Party → Mail C E)) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput))
      (fun echo => if AimedBoundaryException prims D S hsk h parts r u echo then 1 else 0)) ≤
      (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 +
        (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256 := by
  have hz : aimedMean ($ᵗ (KeygenFresh C)) (fun u => if AimedFreshZero D u then 1 else 0) ≤
      (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 := by
    rw [aimedMean_event]
    exact probEvent_aimedFreshKey_le D 0
  rcases r with ⟨state, sentCommit, _ | sentReveal⟩
  · simp only [AimedBoundaryException, or_false, aimedMean_const]
    exact hz.trans ((le_add_right le_rfl).trans (le_add_right le_rfl))
  · have hb := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u =>
      aimedMean_mono ($ᵗ (S → HashOutput)) (fun echo =>
        show (if AimedBoundaryException prims D S hsk h parts (state, sentCommit, some sentReveal) u echo
            then (1 : ℝ≥0∞) else 0) ≤
          (if AimedFreshZero D u then 1 else 0) + (if AimedDelivered prims D h parts sentReveal u then 1 else 0) +
            (if AimedEchoCollision (aimedCollisionPoints prims D S hsk h parts sentReveal u) echo then 1 else 0) from by
          by_cases hz : AimedFreshZero D u <;>
            by_cases hd : AimedDelivered prims D h parts sentReveal u <;>
            by_cases he : AimedEchoCollision (aimedCollisionPoints prims D S hsk h parts sentReveal u) echo <;>
            simp [AimedBoundaryException, hz, hd, he]))
    simp only [aimedMean_add, aimedMean_const, aimedMean_event] at hb
    have hb' : _ ≤ (prssKeyCount C : ℝ≥0∞) / 2 ^ 256 +
        (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256 := hb.trans (add_le_add (add_le_add
          (by simpa only [aimedMean_event] using hz)
          (by unfold AimedDelivered; simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
            probEvent_aimedDelivered_le D (fun i j => Query.sharedKeys .prss ((sharedTerms i j).map
              (aimedReferenceKeys prims D h (fun _ => 0) parts (fun i j => sentReveal j i) i).term)))) (aimedMean_le_const _ _ _
            (fun u => probEvent_aimedEchoCollision_le _)))
    simpa only [aimedMean_event] using hb'

def aimedTailHit (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (u : KeygenFresh C) : ℝ≥0∞ :=
  aimedMean ($ᵗ (KeyName C × HashOutput → Digest)) (fun keys =>
    Pr[fun y => ∃ v ∈ y.2, AimedPrefixCell D parts u v |
      simulateQ (prssLocalAt prims h) (keygenHashLog (simulateQ (aimedKeyLocal prims D keys)
        (aimedReferenceTail prims K circuits settings top tree D A x Z h normal parts r)))])

theorem aimedRefresh_finish_mean_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (a : S → HashOutput)
    (r : A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) (step final : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo =>
      let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
      aimedFinishProbability prims K circuits settings top tree D A x Z h
        (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r))) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (KeygenFresh C))
      (aimedTailHit prims K circuits settings top tree D A x Z (prssHashAt prims (prssExtend S a)) normal parts r) := by
  have hb := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => probEvent_aimedRefresh_finish_le prims K circuits settings top tree D A x Z S normal
      parts hmem hsk hc a echo u r hni hn0))
  simp only [aimedMean_add, aimedMean_const] at hb
  refine hb.trans (add_le_add (add_le_add
    (probEvent_aimedBoundaryException_le prims D S hsk (prssHashAt prims (prssExtend S a)) parts r) ?_) ?_)
  · rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun echo => probEvent_aimedRefresh_guess_le prims K circuits settings
      top tree D A x Z S normal parts hmem hc a echo r step final hround hfinal)
  · unfold aimedTailHit
    rw [aimed_prssLocalAt_hashAt]

def aimedActualProbability (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) : ℝ≥0∞ :=
  aimedMean (simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts)) (fun r =>
    aimedFinishProbability prims K circuits settings top tree D A x Z h
      (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r))

def aimedPrefixHit (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (u : KeygenFresh C) : ℝ≥0∞ :=
  Pr[fun y => ∃ v ∈ y.2, AimedPrefixCell D parts u v |
    simulateQ (prssLocalAt prims h) (keygenHashLog (aimedEarlyProgram D A x z h parts))]

theorem aimedActualProbability_le_one (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) :
    aimedActualProbability prims K circuits settings top tree D A x z Z h parts ≤ 1 := by
  exact aimedMean_le_const _ _ _ fun _ => probEvent_le_one

theorem aimedActualProbability_refresh (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hc : ¬ KeygenClash D parts) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      aimedActualProbability prims K circuits settings top tree D A x z Z (prssExtend S a) parts) =
    aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      aimedMean ($ᵗ (S → HashOutput)) (fun echo =>
        aimedActualProbability prims K circuits settings top tree D A x z Z
          (prssExtend S (aimedRefresh D S parts hmem a echo u)) parts))) := by
  unfold aimedActualProbability aimedFinishProbability
  simp only [aimedMean_probEvent]
  apply probEvent_congr_evalDist
  exact evalDist_aimedRefresh D S parts hmem hc _

theorem aimedActualProbability_prefix_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput) (u : KeygenFresh C) :
    let h := prssExtend S (aimedRefresh D S parts hmem a echo u)
    aimedActualProbability prims K circuits settings top tree D A x z Z h parts ≤
      aimedMean (simulateQ (prssLocalAt prims (prssExtend S a))
        (aimedEarlyProgram D A x z (prssExtend S a) parts)) (fun r =>
          aimedFinishProbability prims K circuits settings top tree D A x Z h
            (aimedFixedBoundary prims D h (prssDataMask D (prssDataAt h parts)) r)) +
      aimedPrefixHit prims D A x z (prssExtend S a) parts u := by
  dsimp only
  unfold aimedActualProbability aimedFinishProbability aimedPrefixHit
  rw [aimedRefresh_early prims]
  simp only [aimedMean_probEvent, aimed_prssLocalAt_eq]
  exact probEvent_aimedPrefix_swap_le prims _ _ (AimedPrefixCell D parts u)
    (aimedRefresh_off prims D S parts hmem a echo u) _ _ _

def aimedReferenceError (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C) : ℝ≥0∞ :=
  aimedMean ($ᵗ (KeygenFresh C)) (aimedPrefixHit prims D A x z h parts) +
  aimedMean (simulateQ (prssLocalAt prims h) (aimedEarlyProgram D A x z h parts)) (fun r =>
    aimedMean ($ᵗ (KeygenFresh C)) (aimedTailHit prims K circuits settings top tree D A x Z h normal parts r))

theorem aimedPrefixHit_hashAt (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (u : KeygenFresh C) :
    aimedPrefixHit prims D A x z (prssHashAt prims h) parts u = aimedPrefixHit prims D A x z h parts u := by
  simp only [aimedPrefixHit, aimedEarlyProgram_hashAt, aimed_prssLocalAt_hashAt]

section PartsComparison
attribute [local irreducible] aimedActualProbability aimedFinishProbability aimedReferenceTail
  aimedReferenceError aimedTailHit aimedPrefixHit

theorem aimedActualProbability_parts_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (hmem : ∀ n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (hc : ¬ KeygenClash D parts) (step final : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      aimedActualProbability prims K circuits settings top tree D A x z Z (prssExtend S a) parts) ≤
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256 +
    aimedMean ($ᵗ (S → HashOutput)) (fun a =>
      aimedReferenceError prims K circuits settings top tree D A x z Z
        (prssHashAt prims (prssExtend S a)) normal parts) := by
  rw [aimedActualProbability_refresh prims K circuits settings top tree D A x z Z S parts hmem hc,
    aimedMean_comm]
  rw [← aimedMean_const ($ᵗ (S → HashOutput))
    (((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
      (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256),
    ← aimedMean_add]
  apply aimedMean_mono
  intro a
  have hp := aimedMean_mono ($ᵗ (KeygenFresh C)) (fun u => aimedMean_mono ($ᵗ (S → HashOutput))
    (fun echo => aimedActualProbability_prefix_le prims K circuits settings top tree D A x z Z S
      parts hmem a echo u))
  simp only [aimedMean_add, aimedMean_const] at hp
  let early := simulateQ (prssLocalAt prims (prssExtend S a))
    (aimedEarlyProgram D A x z (prssExtend S a) parts)
  have hf := aimedMean_mono early (fun r => aimedRefresh_finish_mean_le prims K circuits settings
    top tree D A x Z S normal parts hmem hsk hc a r step final hni hn0 hround hfinal)
  simp only [aimedMean_add, aimedMean_const] at hf
  have hmove {f : KeygenFresh C → (S → HashOutput) →
      (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → ℝ≥0∞} :
      aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo => aimedMean early (f u echo))) =
      aimedMean early (fun r => aimedMean ($ᵗ (KeygenFresh C)) (fun u => aimedMean ($ᵗ (S → HashOutput)) (fun echo => f u echo r))) := by
    simp_rw [aimedMean_comm ($ᵗ (S → HashOutput)) early]
    rw [aimedMean_comm]
  rw [hmove] at hp
  have hb := hp.trans (add_le_add hf le_rfl)
  unfold aimedReferenceError
  simp only [aimedEarlyProgram_hashAt, aimed_prssLocalAt_hashAt]
  have he : (aimedPrefixHit prims D A x z (prssHashAt prims (prssExtend S a)) parts) =
      aimedPrefixHit prims D A x z (prssExtend S a) parts := funext fun u => aimedPrefixHit_hashAt prims D A x z _ parts u
  rw [he]
  exact hb.trans_eq ((add_right_comm _ _ _).trans (add_assoc _ _ _))

end PartsComparison

theorem aimedMean_parts_event {α : Type} (kernel : (C.Party → Parts C) → ProbComp α)
    (event : (C.Party → Parts C) → KeygenFresh C → α → Prop) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (KeygenFresh C)) (fun u => Pr[event parts u | kernel parts])) =
    Pr[fun r => event r.1.1 r.2 r.1.2 |
      (do let r ← keygenPartsKernel kernel
          let u ← $ᵗ (KeygenFresh C)
          pure (r, u))] := by
  simp only [keygenPartsKernel, bind_assoc, pure_bind, ← aimedMean_probEvent, probEvent_pure]
  apply congrArg (aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)))
  funext parts
  simp_rw [← aimedMean_event]
  exact aimedMean_comm _ _ _

section ReferenceErrorBound

attribute [local irreducible] aimedTailHit aimedReferenceTail

theorem aimedReferenceError_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (h : Query C → HashOutput)
    (normal : KeyName C → HashOutput) (start step final : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (aimedReferenceError prims K circuits settings top tree D A x z Z h normal) ≤
      (((start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      ((((ceremonyFuel circuits settings - 2) * step + final) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold aimedReferenceError
  rw [aimedMean_add]
  apply add_le_add
  · unfold aimedPrefixHit
    rw [aimedMean_parts_event]
    exact probEvent_aimedEarlyLog_le prims D A x z h start step hstart hround
  · unfold aimedTailHit
    have hmove {α β γ : Type} (p : ProbComp α) (q : ProbComp β) (k : α → ProbComp γ)
        (f : α → γ → β → ℝ≥0∞) :
        aimedMean p (fun a => aimedMean (k a) (fun c => aimedMean q (f a c))) =
        aimedMean q (fun b => aimedMean p (fun a => aimedMean (k a) (fun c => f a c b))) := by
      simp_rw [aimedMean_comm (k _) q]
      rw [aimedMean_comm]
    simp_rw [aimedMean_comm ($ᵗ (KeygenFresh C)) ($ᵗ (KeyName C × HashOutput → Digest))]
    rw [hmove (p := Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (q := $ᵗ (KeyName C × HashOutput → Digest))]
    apply aimedMean_le_const
    intro keys
    have hb := probEvent_aimedTailLog_le prims K circuits settings top tree D A x z Z h keys normal
      step final hround hfinal
    rw [← aimedMean_parts_event
      (aimedTailLog prims K circuits settings top tree D A x z Z h keys normal)
      (fun parts u out => ∃ v ∈ out.2, AimedPrefixCell D parts u v)] at hb
    unfold aimedTailLog at hb
    simp only [← aimedMean_probEvent] at hb
    simpa only [aimedMean_comm ($ᵗ (KeygenFresh C))] using hb

end ReferenceErrorBound

theorem aimed_total_error_arith (start step final fuel : ℕ) :
    keygenClashCount C + (prssKeyCount C + 2 * Fintype.card C.Pair ^ 2 + Fintype.card C.Pair) +
      ((fuel - 2) * step + final) * prssKeyCount C +
      ((start + 2 * step) * prssKeyCount C + ((fuel - 2) * step + final) * prssKeyCount C) ≤
    (start + (3 * (fuel - 2) + 2) * step + 3 * final) * prssKeyCount C + 4 * prssKeyCount C ^ 2 := by
  have hb := aimed_boundary_zero_error_arith (C := C)
  rw [keygenFinish_card_pair]
  nlinarith [Nat.zero_le (((fuel - 2) * step + final) * prssKeyCount C)]

section TotalComparison

attribute [local irreducible] aimedActualProbability aimedReferenceError

theorem aimedActualProbability_total_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C))
    (normal : KeyName C → HashOutput)
    (hmem : ∀ parts n, Hidden D n → hiddenInput parts n ∈ S)
    (hsk : ∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ S)
    (start step final : ℕ)
    (hni : Function.Injective (fun n : {n : KeyName C // Hidden D n} => normal n))
    (hn0 : ∀ n, Hidden D n → normal n ≠ 0)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (hfinal : ∀ r, IsQueryBoundP (Z r) Counted final) :
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        aimedActualProbability prims K circuits settings top tree D A x z Z (prssExtend S a) parts)) ≤
      (((start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C +
        4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let cost : ℝ≥0∞ :=
    ((prssKeyCount C : ℝ≥0∞) / 2 ^ 256 + (2 * (Fintype.card C.Pair : ℝ≥0∞) ^ 2) / 2 ^ 256 +
      (Fintype.card C.Pair : ℝ≥0∞) / 2 ^ 256) +
    (((ceremonyFuel circuits settings - 2) * step + final : ℕ) : ℝ≥0∞) * prssKeyCount C / 2 ^ 256
  have hp (parts : C.Party → Parts C) :
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        aimedActualProbability prims K circuits settings top tree D A x z Z (prssExtend S a) parts) ≤
      (if KeygenClash D parts then 1 else 0) + (cost + aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        aimedReferenceError prims K circuits settings top tree D A x z Z
          (prssHashAt prims (prssExtend S a)) normal parts)) := by
    by_cases hc : KeygenClash D parts
    · rw [if_pos hc]
      exact (aimedMean_le_const _ 1 _ (fun a => aimedActualProbability_le_one prims K circuits settings
        top tree D A x z Z _ parts)).trans (le_add_right le_rfl)
    · rw [if_neg hc, zero_add]
      exact aimedActualProbability_parts_le prims K circuits settings top tree D A x z Z S normal parts
        (hmem parts) hsk hc step final hni hn0 hround hfinal
  have hb := aimedMean_mono (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) hp
  simp only [aimedMean_add, aimedMean_const, aimedMean_event] at hb
  have hc : Pr[KeygenClash D | Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)] ≤
      (keygenClashCount C : ℝ≥0∞) / 2 ^ 256 := by
    simpa only [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using probEvent_keygenClash_le D
  have he : aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a => aimedReferenceError prims K circuits settings
        top tree D A x z Z (prssHashAt prims (prssExtend S a)) normal parts)) ≤
      (((start + 2 * step) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((((ceremonyFuel circuits settings - 2) * step + final) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [aimedMean_comm]
    exact aimedMean_le_const _ _ _ (fun a => aimedReferenceError_le prims K circuits settings top tree D A x z Z
      (prssHashAt prims (prssExtend S a)) normal start step final hstart hround hfinal)
  refine (hb.trans (add_le_add hc (add_le_add le_rfl he))).trans ?_
  dsimp only [cost]
  simp only [← ENNReal.add_div]
  gcongr
  norm_cast
  have ha := aimed_total_error_arith (C := C) start step final (ceremonyFuel circuits settings)
  omega

end TotalComparison

theorem aimedEagerProbability_eq (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (S : Finset (Query C)) :
    Pr[fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true | do
      let keys ← $ᵗ (KeyName C × HashOutput → Digest)
      let h ← $ᵗ (S → HashOutput)
      simulateQ (prssLocalAt prims (prssExtend S h)) (simulateQ (aimedKeyLocal prims D keys)
        (aimedFlagProgram K circuits settings top tree D A x z Z))] =
    aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
      aimedMean ($ᵗ (S → HashOutput)) (fun a =>
        aimedActualProbability prims K circuits settings top tree D A x z Z (prssExtend S a) parts)) := by
  have he (keys : KeyName C × HashOutput → Digest) (a : S → HashOutput) :=
    probEvent_congr_evalDist (evalDist_aimedFlagProgram_at_fullParts prims K circuits settings
      top tree D A x z Z keys (prssExtend S a)) (fun y => KeysApart D (rowsOf y.1.2) ∧ y.2.2 = true)
  simp only [← aimedMean_probEvent] at he ⊢
  simp_rw [he]
  rw [aimedMean_comm]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))]
  rw [aimedMean_comm]
  unfold aimedActualProbability aimedFinishProbability aimedEarlyProgram
  simp only [simulateQ_bind, aimedMean_bind, ← aimedMean_probEvent]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (simulateQ (prssLocalAt prims _) (A.start (corruptInputs D x) z))]
  simp_rw [aimedMean_comm ($ᵗ (KeyName C × HashOutput → Digest))
    (simulateQ (prssLocalAt prims _) (prssEarlyRounds D A _ _ _))]

theorem aimedCover_exists : ∃ cover : Finset (Query C),
    (∀ parts n, hiddenInput parts n ∈ cover) ∧
    (∀ i j (f : C.Term → HashOutput), Query.sharedKeys .prss ((sharedTerms i j).map f) ∈ cover) := by
  letI : Finite (Parts C) := keygenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  let canonical := (Finset.univ : Finset ((C.Party → Parts C) × KeyName C)).image (fun p => hiddenInput p.1 p.2)
  let echoes : Finset (Query C) := (Finset.univ : Finset (C.Party × C.Party × (C.Term → HashOutput))).image
    (fun p => Query.sharedKeys .prss ((sharedTerms p.1 p.2.1).map p.2.2))
  refine ⟨canonical ∪ echoes, ?_, ?_⟩
  · intro parts n
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(parts, n), Finset.mem_univ _, rfl⟩)
  · intro i j f
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j, f), Finset.mem_univ _, rfl⟩)

/-- The unconditional aimed-call bound retains every prefix query and the fixed quadratic allowance. -/
theorem treeKeyAimedBound : TreeKeyAimedBound prims K circuits settings := by
  intro _ top tree D A x z Z start step final _ hstart hround hfinal
  by_cases hm : prssKeyCount C < 2 ^ 256
  · obtain ⟨normal, hni, hn0⟩ := aimed_normalTable_exists D hm
    obtain ⟨cover, hcanonical, hecho⟩ := aimedCover_exists (C := C)
    obtain ⟨S, hS, hbound⟩ := probEvent_lazyAimedBoundary_le_eager prims K circuits settings cover
      top tree D A x z Z
    rw [aimedEagerProbability_eq] at hbound
    exact hbound.trans (aimedActualProbability_total_le prims K circuits settings top tree D A x z Z S normal
      (fun parts n _ => hS (hcanonical parts n)) (fun i j f => hS (hecho i j f))
      start step final hni hn0 hstart hround hfinal)
  · have hm' : 2 ^ 256 ≤ prssKeyCount C := Nat.le_of_not_gt hm
    have hpos : 0 < prssKeyCount C := lt_of_lt_of_le (by positivity) hm'
    have hn : 2 ^ 256 ≤
        (start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C +
          4 * prssKeyCount C ^ 2 := by
      nlinarith [Nat.zero_le ((start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C)]
    calc
      _ ≤ 1 := probEvent_le_one
      _ = (2 ^ 256 : ℝ≥0∞) / 2 ^ 256 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := by
        gcongr
        exact_mod_cast hn

/-- The simulation hop closes tree security with the unconditional aimed-call bound. -/
theorem treeSecurityOfSimClosed
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityOfSimAimed prims K circuits settings
    (treeKeyAimedBound prims K circuits settings) hSim

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

/-- info: 'ThresholdLeanXmssSecurity.probEvent_aimedFixed_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_aimedFixed_reference

/-- info: 'ThresholdLeanXmssSecurity.probEvent_aimedPrefixCell_kernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_aimedPrefixCell_kernel_le

/-- info: 'ThresholdLeanXmssSecurity.aimedReferenceProgram_privateInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aimedReferenceProgram_privateInvariant

/-- info: 'ThresholdLeanXmssSecurity.aimedReferenceAfter_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aimedReferenceAfter_bound

/-- info: 'ThresholdLeanXmssSecurity.aimed_boundary_zero_error_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aimed_boundary_zero_error_arith

end ThresholdLeanXmssSecurity
