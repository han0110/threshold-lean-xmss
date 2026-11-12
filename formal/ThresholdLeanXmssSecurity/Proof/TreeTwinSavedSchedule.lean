import ThresholdLeanXmssSecurity.Proof.TreeTwinLinked2
import ThresholdLeanXmssSecurity.Proof.CheckFinish
import ThresholdLeanXmssSecurity.Proof.TreeTwinLocalSum

/-!
# The saved check schedule

A saved phase retains its actual range suffix and bounded index. Its witness
keeps the original caller, field products, batch position and conditional
slice or halving relation together. Every advancing phase retains that caller
under its actual reduction. All-holder history agreement is needed only for
the relation; shapes and the hidden term's common history are unconditional.
-/

set_option linter.unusedSectionVars false
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinSavedSchedule
open TreeTwinLinked2 TreeTwinLocalSum
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

def halvSteps (count : ℕ) : ℕ := halvingSteps (sliceWidth count)
def sliceSuffix (j : ℕ) : List ℕ := (List.range sliceBits).drop (j + 1)
def halvSuffix (count j : ℕ) : List ℕ := (List.range (halvSteps count)).drop (j + 1)

theorem range_halvings_sub (c : ℕ) :
    List.range (halvings c - sliceBits) = List.range (halvSteps c) := by
  simp [halvings, halvSteps]

theorem sliceSuffix_zero : (List.range sliceBits).drop 1 = sliceSuffix 0 := rfl

private theorem range_drop_cons {j n : ℕ} (h : j < n) :
    (List.range n).drop j = j :: (List.range n).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem sliceSuffix_cons {j : ℕ} (h : j + 1 < sliceBits) :
    sliceSuffix j = (j + 1) :: sliceSuffix (j + 1) := range_drop_cons h

theorem sliceSuffix_eq_nil {j : ℕ} (h : j < sliceBits) :
    sliceSuffix j = [] ↔ j + 1 = sliceBits := by
  simp only [sliceSuffix, List.drop_eq_nil_iff, List.length_range]
  omega

theorem halvSuffix_cons {c j : ℕ} (h : j + 1 < halvSteps c) :
    halvSuffix c j = (j + 1) :: halvSuffix c (j + 1) := range_drop_cons h

theorem halvSuffix_eq_nil {c j : ℕ} (h : j < halvSteps c) :
    halvSuffix c j = [] ↔ j + 1 = halvSteps c := by
  simp only [halvSuffix, List.drop_eq_nil_iff, List.length_range]
  omega

theorem one_lt_sliceWidth {c : ℕ} (h : c ≠ 0) : 1 < sliceWidth c := by
  have hp := sliceWidth_pos h
  simp only [sliceWidth, wordBits] at hp ⊢
  omega

theorem halvSteps_pos {c : ℕ} (h : c ≠ 0) : 0 < halvSteps c := by
  unfold halvSteps
  rw [halvingSteps, if_pos (one_lt_sliceWidth h)]
  omega

theorem range_halvSteps {c : ℕ} (h : c ≠ 0) :
    List.range (halvSteps c) = 0 :: halvSuffix c 0 := by
  simpa [halvSuffix] using range_drop_cons (halvSteps_pos h)

theorem halv_last_length {c j : ℕ} (h : c ≠ 0) (hj : j + 1 = halvSteps c) :
    halvedLength (halvedLength^[j] (sliceWidth c)) = 1 := by
  rw [← Function.iterate_succ_apply' halvedLength j (sliceWidth c)]
  change halvedLength^[j + 1] (sliceWidth c) = 1
  rw [hj]
  exact iterate_halvingSteps _ (Nat.le_of_lt (one_lt_sliceWidth h))

inductive SavedPhase (C : Committee) (E : Type) where
  | slice (τ : List E) (j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
  | halving (j : ℕ) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)

namespace SavedPhase
def index : SavedPhase C E → ℕ
  | .slice _ j _ _ => j
  | .halving j _ _ => sliceBits + j

def remaining (c : ℕ) : SavedPhase C E → List ℕ
  | .slice _ j _ _ => sliceSuffix j
  | .halving j _ _ => halvSuffix c j

def Bound (c : ℕ) : SavedPhase C E → Prop
  | .slice _ j _ _ => j < sliceBits
  | .halving j _ _ => j < halvSteps c

def Finishing (c : ℕ) : SavedPhase C E → Prop
  | .slice _ j _ _ => sliceSuffix j = [] ∧ halvSteps c = 0
  | .halving j _ _ => halvSuffix c j = []
end SavedPhase

def savedOffset (circs : List Circuit) (φ : SavedPhase C E) : ℕ :=
  depth circs + 2 + 2 * φ.index

theorem savedOffset_le (circuits : Circuits) (parameter : PublicParameter) (jobs : List Job)
    {c : ℕ} {φ : SavedPhase C E} (h : c = tupleCount (runCircuits circuits parameter jobs))
    (hc : c ≠ 0) (hb : φ.Bound c) :
    savedOffset (runCircuits circuits parameter jobs) φ ≤ batchLabels circuits parameter jobs := by
  subst c
  change depth (runCircuits circuits parameter jobs) + 2 + 2 * φ.index ≤
    depth (runCircuits circuits parameter jobs) + 1 + checkLabels (tupleCount (runCircuits circuits parameter jobs))
  rw [checkLabels, if_neg hc]
  cases φ <;> simp only [SavedPhase.Bound] at hb <;>
    simp only [SavedPhase.index, halvings, halvSteps] at * <;> omega

theorem position_shift (circuits : Circuits) (settings : Settings) (tree : Tree)
    (D : C.Coalition) (parameter : PublicParameter) (circs : List Circuit) (off m : ℕ)
    (st st' : C.Party → RunState C)
    (hpos : Position circuits settings tree D parameter circs off st)
    (tag : ∀ i, i ∉ D.1 → (st' i).tag = (st i).tag)
    (lab : ∀ i, i ∉ D.1 → (st' i).label = (st i).label + m)
    (le : ∀ jobs, circs = runCircuits circuits parameter jobs →
      off + m ≤ batchLabels circuits parameter jobs) :
    Position circuits settings tree D parameter circs (off + m) st' := by
  obtain ⟨enc, k, hk, hc, _, hs⟩ := hpos
  refine ⟨enc, k, hk, hc, le _ hc, ?_⟩
  intro i hi
  exact ⟨(tag i hi).trans (hs i hi).1, by rw [lab i hi, (hs i hi).2]; omega⟩

/-- The honest holders of each term have one history. -/
def AllHistory (D : C.Coalition) (st : C.Party → RunState C) : Prop :=
  ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T → (st i).history T = (st j).history T

/-- The two slice states differ only on the lacked term. -/
def SliceShape (D : C.Coalition) (v₁ v₂ : C.Party → Shares C E × Shares C E × E) : Prop :=
  ∃ (dx dy : ℕ → E) (e : E),
    (∀ i, i ∉ D.1 → ∀ T k, (v₂ i).1 T k = (v₁ i).1 T k +
      if i ∈ C.holders T ∧ lackedTerm D.1 = some T then dx k else 0) ∧
    (∀ i, i ∉ D.1 → ∀ T k, (v₂ i).2.1 T k = (v₁ i).2.1 T k +
      if i ∈ C.holders T ∧ lackedTerm D.1 = some T then dy k else 0) ∧
    (∀ i, i ∉ D.1 → (v₁ i).2.2 - (v₂ i).2.2 = lackedShare K D i e)

/-- The two halving states differ only by Shamir shares of values on the lacked term. -/
def HalvShape (D : C.Coalition) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E) : Prop :=
  ∃ (dA dB : ℕ → E) (e : E),
    (∀ i, i ∉ D.1 → ∀ k, (v₁ i).1 k - (v₂ i).1 k = lackedShare K D i (dA k)) ∧
    (∀ i, i ∉ D.1 → ∀ k, (v₁ i).2.1 k - (v₂ i).2.1 k = lackedShare K D i (dB k)) ∧
    (∀ i, i ∉ D.1 → (v₁ i).2.2 - (v₂ i).2.2 = lackedShare K D i e)

/-- The histories at an earlier label agree when the later histories agree and each holder
appended a block of the same length. -/
theorem allHistory_of_append (D : C.Coalition) (st st' : C.Party → RunState C) (n : C.Term → ℕ)
    (block : ∀ T i, i ∉ D.1 → i ∈ C.holders T → ∃ l : List Bit, l.length = n T ∧
      (st' i).history T = (st i).history T ++ l)
    (h : AllHistory D st') : AllHistory D st := by
  intro T i j hi hj hiT hjT
  obtain ⟨l₁, len₁, e₁⟩ := block T i hi hiT
  obtain ⟨l₂, len₂, e₂⟩ := block T j hj hjT
  have := h T i j hi hj hiT hjT
  rw [e₁, e₂] at this
  exact (List.append_inj' this (len₁.trans len₂.symm)).1


/-- Arbitrary values at the first `t` parties determine a degree-bounded sharing. -/
theorem isShamir_lagrangeFirst (s : C.Party → E) :
    IsShamir K (fun m => ∑ l ∈ firstParties C, lagrangeFirst K (K.point m) l * s l)
      (∑ l ∈ firstParties C, lagrangeFirst K 0 l * s l) := by
  let P := Lagrange.interpolate (firstParties C) K.point s
  have degree : P.degree < (C.t : WithBot ℕ) := by
    simpa only [card_firstParties] using
      Lagrange.degree_interpolate_lt s (K.point.injective.injOn (s := firstParties C))
  refine ⟨P, ?_, eval_interpolate_first K s 0, fun i => (eval_interpolate_first K s (K.point i)).symm⟩
  by_cases hz : P = 0
  · simp [hz]
  · have hn := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr degree
    omega

/-- Any two accepting honest Coin openers obtain the same list, even when
all local PRSS values are unrelated. -/
theorem coinOutput_agree (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C E)
    (sent : C.Party → Mail C E) {i j : C.Party} (hi : i ∉ D.1) (hj : j ∉ D.1)
    {a b : List E} (ha : treeSimCoinOutput K D c rnd sent i = some a)
    (hb : treeSimCoinOutput K D c rnd sent j = some b) : a = b := by
  let share := fun l => conv K (localContext l) (rnd l).1
  let inbox := fun k l => if l ∈ D.1 then sent l k else coinOut K l c (rnd l) k
  have honest (k l : C.Party) (hl : l ∉ D.1) (g : ℕ) (hg : g < c) :
      openShare k (share k) (inbox k) l g = share l g := by
    by_cases he : l = k
    · subst l; simp [openShare]
    · simp only [openShare, if_neg he, inbox, if_neg hl, coinOut, openOut, localContext]
      rw [if_neg (Ne.symm he)]
      exact vector_getD c _ g hg
  have accepted (k : C.Party) (hk : k ∉ D.1) (v : List E)
      (hv : treeSimCoinOutput K D c rnd sent k = some v) :
      (∀ l : C.Party, ∀ g < c, openShare k (share k) (inbox k) l g =
        ∑ m ∈ firstParties C, lagrangeFirst K (K.point l) m * openShare k (share k) (inbox k) m g) ∧
      v = vector c (fun g => ∑ m ∈ firstParties C,
        lagrangeFirst K 0 m * openShare k (share k) (inbox k) m g) := by
    simp only [treeSimCoinOutput, if_neg hk, coinRes] at hv
    split at hv
    · cases hv
    · change (openRes K k (share k) c (inbox k)).map (vector c) = some v at hv
      unfold openRes at hv
      split at hv
      · rename_i hp
        exact ⟨hp, (Option.some.inj hv).symm⟩
      · cases hv
  obtain ⟨hai, rfl⟩ := accepted i hi a ha
  obtain ⟨hbj, rfl⟩ := accepted j hj b hb
  apply vector_congr
  intro g hg
  have he : Lagrange.interpolate (firstParties C) K.point
      (fun l => openShare i (share i) (inbox i) l g) =
      Lagrange.interpolate (firstParties C) K.point
        (fun l => openShare j (share j) (inbox j) l g) := by
    apply poly_eq_of_honest K D
    · simpa only [card_firstParties] using Lagrange.degree_interpolate_lt
        (r := fun l => openShare i (share i) (inbox i) l g) (K.point.injective.injOn (s := firstParties C))
    · simpa only [card_firstParties] using Lagrange.degree_interpolate_lt
        (r := fun l => openShare j (share j) (inbox j) l g) (K.point.injective.injOn (s := firstParties C))
    · intro l hl
      rw [eval_interpolate_first, eval_interpolate_first, ← hai l g hg, ← hbj l g hg,
        honest i l hl g hg, honest j l hl g hg]
  rw [← eval_interpolate_first, ← eval_interpolate_first, he]

/-- The context contributes only its party identity to field conversion. -/
theorem conv_self (ctx : Context C) (i : C.Party) (self : ctx.self = i) (v : Shares C E) :
    conv K ctx v = conv K (localContext i) v := by
  funext g
  simp only [conv, self, localContext]

theorem productShare_self (ctx : Context C) (i : C.Party) (self : ctx.self = i) (p : Product C E) :
    productShare K ctx p = productShare K (localContext i) p := by
  cases p <;> simp only [productShare, mulRep, mulSh, self, localContext]

/-- The exact two-product output translation of ExtendMult. -/
def OutputShift (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (products₁ products₂ : C.Party → List (Product C E))
    (out₁ out₂ : C.Party → Shares C E) : Prop :=
  ∀ i, i ∉ D.1 → out₂ i = treeSimFieldHeldShift D i 2
    (fun g => ∑ j ∈ univ.filter (· ∉ D.1),
      (contextProductValues K (ctx₁ j) (products₁ j) g -
        contextProductValues K (ctx₂ j) (products₂ j) g)) (out₁ i)

theorem OutputShift.congr_products (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (p₁ p₂ p₁' p₂' : C.Party → List (Product C E)) (out₁ out₂ : C.Party → Shares C E)
    (h : OutputShift K D ctx₁ ctx₂ p₁ p₂ out₁ out₂)
    (h₁ : ∀ i, i ∉ D.1 → p₁ i = p₁' i) (h₂ : ∀ i, i ∉ D.1 → p₂ i = p₂' i) :
    OutputShift K D ctx₁ ctx₂ p₁' p₂' out₁ out₂ := by
  intro i hi
  rw [h i hi]
  congr 1
  funext g
  apply Finset.sum_congr rfl
  intro j hj
  rw [h₁ j (Finset.mem_filter.mp hj).2, h₂ j (Finset.mem_filter.mp hj).2]

theorem outputShift_sub (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (products₁ products₂ : C.Party → List (Product C E)) (out₁ out₂ : C.Party → Shares C E)
    (h : OutputShift K D ctx₁ ctx₂ products₁ products₂ out₁ out₂)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (held : i ∈ C.holders T) (g : ℕ) (hg : g < 2) :
    out₁ i T g - out₂ i T g = if lackedTerm D.1 = some T then
      ∑ j ∈ univ.filter (· ∉ D.1), (contextProductValues K (ctx₁ j) (products₁ j) g -
        contextProductValues K (ctx₂ j) (products₂ j) g) else 0 := by
  letI : CharP E 2 := charTwo
  rw [h i hi]
  simp [treeSimFieldHeldShift, held, hg, CharTwo.neg_eq]

/-- Port of `CheckFinish.sliceRel_halvRel`; its proof uses no sampling instance. -/
theorem sliceRel_halvRel' (K : Constants C E) (D : C.Coalition) (τ : List E) (count : ℕ)
    (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E)
    (h : SliceRel K D τ count sliceBits xsR ysR xsD ysD DR DD) :
    ∃ AR BR AD BD : C.Party → ℕ → E,
      (∀ i, i ∉ D.1 → conv K (localContext i) (xsR i) = AR i ∧ conv K (localContext i) (ysR i) = BR i ∧
        conv K (localContext i) (xsD i) = AD i ∧ conv K (localContext i) (ysD i) = BD i) ∧
      HalvRel K D (sliceWidth count) AR BR AD BD DR DD := by
  letI : CharP E 2 := charP_two
  obtain ⟨xR, yR, xD, yD, dD, hv, hk, hl, hsum⟩ := h
  refine ⟨fun i => conv K (localContext i) xR, fun i => conv K (localContext i) yR,
    fun i => conv K (localContext i) xD, fun i => conv K (localContext i) yD, ?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_, ?_, ?_⟩ <;> funext k <;> apply conv_congr <;> intro T hT
    · exact congrFun (hv i hi T hT).1 k
    · exact congrFun (hv i hi T hT).2.1 k
    · exact congrFun (hv i hi T hT).2.2.1 k
    · exact congrFun (hv i hi T hT).2.2.2 k
  refine ⟨shareValue xR, shareValue yR, shareValue xD, shareValue yD,
    fun k T => xR T k - xD T k, fun k T => yR T k - yD T k, dD,
    fun k => isShamir_conv xR k, fun k => isShamir_conv yR k, fun k => isShamir_conv xD k,
    fun k => isShamir_conv yD k, ?_, ?_, ?_, ?_, fun T hT => (hk T hT).2.2, ?_, ?_, ?_, ?_, hl, ?_⟩
  · intro k i hi
    exact conv_congr i _ _ k fun T hT => by rw [(hk T ⟨i, hi, hT⟩).1]
  · intro k i hi
    exact conv_congr i _ _ k fun T hT => by rw [(hk T ⟨i, hi, hT⟩).2.1]
  · intro k T hT; simp [(hk T hT).1]
  · intro k T hT; simp [(hk T hT).2.1]
  · intro k; simp only [shareValue, Finset.sum_sub_distrib]
  · intro k; simp only [shareValue, Finset.sum_sub_distrib]
  · intro k i _; exact conv_sub_const K i xR xD k
  · intro k i _; exact conv_sub_const K i yR yD k
  · rw [hsum]
    have hl0 : sliceLen count sliceBits = sliceWidth count := by simp [sliceLen]
    rw [hl0]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sliceWeight, coinProduct]


/-- The claim coordinates of `HalvRel` constrain honest parties only. -/
theorem HalvRel.congr_claims (D : C.Coalition) (len : ℕ)
    (AR BR AD BD : C.Party → ℕ → E) (DR DD DR' DD' : C.Party → E)
    (h : HalvRel K D len AR BR AD BD DR DD)
    (hR : ∀ i, i ∉ D.1 → DR i = DR' i) (hD : ∀ i, i ∉ D.1 → DD i = DD' i) :
    HalvRel K D len AR BR AD BD DR' DD' := by
  obtain ⟨a, b, a', b', dA, dB, dD, hA, hB, hA', hB', hCA, hCB, hkA, hkB, hkD,
    hsA, hsB, hlA, hlB, hlD, hsum⟩ := h
  exact ⟨a, b, a', b', dA, dB, dD, hA, hB, hA', hB', hCA, hCB, hkA, hkB, hkD,
    hsA, hsB, hlA, hlB, fun i hi => by rw [← hR i hi, ← hD i hi]; exact hlD i hi, hsum⟩

/-- Contextual product sums coincide with the inputs of the checked slice step. -/
theorem sliceProducts_total (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i) (τ : List E) (count j g : ℕ)
    (v : C.Party → Shares C E × Shares C E × E) :
    (∑ i ∈ univ.filter (· ∉ D.1), contextProductValues K (ctx i)
      (treeStagesSliceProducts τ count j (v i)) g) =
    extendTotal K D (sliceInputs D τ count j (fun i => (v i).1) (fun i => (v i).2.1)) g := by
  rw [sliceInputs_total]
  apply Finset.sum_congr rfl
  intro i hi
  have hs := self i (Finset.mem_filter.mp hi).2
  change contextProductValues K (ctx i) (sliceProducts τ count j (v i).1 (v i).2.1) g = _
  unfold contextProductValues
  cases he : (sliceProducts τ count j (v i).1 (v i).2.1)[g]? with
  | none => simp [productShare, mulRep]
  | some p => exact productShare_self K _ i hs p

theorem SliceRel.congr_claims (D : C.Coalition) (τ : List E) (count j : ℕ)
    (AR BR AD BD : C.Party → Shares C E) (DR DD DR' DD' : C.Party → E)
    (h : SliceRel K D τ count j AR BR AD BD DR DD)
    (hR : ∀ i, i ∉ D.1 → DR i = DR' i) (hD : ∀ i, i ∉ D.1 → DD i = DD' i) :
    SliceRel K D τ count j AR BR AD BD DR' DD' := by
  obtain ⟨xR, yR, xD, yD, dD, hv, hk, hl, hs⟩ := h
  exact ⟨xR, yR, xD, yD, dD, hv, hk,
    fun i hi => by rw [← hR i hi, ← hD i hi]; exact hl i hi, hs⟩

/-- The exact slice update preserves the relation for every common challenge. -/
theorem sliceFold_rel [CharP E 2] (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (τ : List E) (count j : ℕ) (hj : j < sliceBits) (hc : count ≠ 0)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E) (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesSliceProducts τ count j (v₁ i))
      (fun i => treeStagesSliceProducts τ count j (v₂ i)) out₁ out₂) (r : E)
    (h : SliceRel K D τ count j (fun i => (v₁ i).1) (fun i => (v₁ i).2.1)
      (fun i => (v₂ i).1) (fun i => (v₂ i).2.1) (fun i => (v₁ i).2.2) (fun i => (v₂ i).2.2)) :
    let u₁ := fun i => treeStagesSliceUpdate K (ctx₁ i) τ count j (v₁ i) (out₁ i) r
    let u₂ := fun i => treeStagesSliceUpdate K (ctx₂ i) τ count j (v₂ i) (out₂ i) r
    SliceRel K D τ count (j + 1) (fun i => (u₁ i).1) (fun i => (u₁ i).2.1)
      (fun i => (u₂ i).1) (fun i => (u₂ i).2.1) (fun i => (u₁ i).2.2) (fun i => (u₂ i).2.2) := by
  let d := fun g => ∑ i ∈ univ.filter (· ∉ D.1),
    (contextProductValues K (ctx₁ i) (treeStagesSliceProducts τ count j (v₁ i)) g -
      contextProductValues K (ctx₂ i) (treeStagesSliceProducts τ count j (v₂ i)) g)
  have hd (g : ℕ) : d g =
      extendTotal K D (sliceInputs D τ count j (fun i => (v₁ i).1) (fun i => (v₁ i).2.1)) g -
      extendTotal K D (sliceInputs D τ count j (fun i => (v₂ i).1) (fun i => (v₂ i).2.1)) g := by
    dsimp only [d]
    rw [Finset.sum_sub_distrib, sliceProducts_total K D ctx₁ self₁, sliceProducts_total K D ctx₂ self₂]
  have step := sliceRel_step K D τ count j hj (sliceWidth_pos hc) (hτ _ (by omega))
    _ _ _ _ _ _ h r out₁ out₂ (d 0) (d 1) (fun i hi T ht g hg => by
      rw [outputShift_sub K D ctx₁ ctx₂ _ _ out₁ out₂ hz i hi T ht g hg]
      interval_cases g <;> rfl) (hd 0) (hd 1)
  apply SliceRel.congr_claims K D τ count (j + 1) _ _ _ _ _ _ _ _ step
  · intro i hi
    simp only [sliceClaim, treeStagesSliceUpdate, conv_self K _ i (self₁ i hi)]
  · intro i hi
    simp only [sliceClaim, treeStagesSliceUpdate, conv_self K _ i (self₂ i hi)]

/-- The exact halving update preserves the relation for every common challenge.
Corrupt vector entries also use that common challenge. -/
theorem halvFold_rel [CharP E 2] (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (width j : ℕ) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesHalvingProducts width j (v₁ i))
      (fun i => treeStagesHalvingProducts width j (v₂ i)) out₁ out₂) (r : E)
    (h : HalvRel K D (halvedLength^[j] width) (fun i => (v₁ i).1) (fun i => (v₁ i).2.1)
      (fun i => (v₂ i).1) (fun i => (v₂ i).2.1) (fun i => (v₁ i).2.2) (fun i => (v₂ i).2.2)) :
    let u₁ := fun i => treeStagesHalvingUpdate K (ctx₁ i) width j (v₁ i) (out₁ i) r
    let u₂ := fun i => treeStagesHalvingUpdate K (ctx₂ i) width j (v₂ i) (out₂ i) r
    HalvRel K D (halvedLength^[j + 1] width) (fun i => (u₁ i).1) (fun i => (u₁ i).2.1)
      (fun i => (u₂ i).1) (fun i => (u₂ i).2.1) (fun i => (u₁ i).2.2) (fun i => (u₂ i).2.2) := by
  let d := fun g => ∑ i ∈ univ.filter (· ∉ D.1),
    (contextProductValues K (ctx₁ i) (treeStagesHalvingProducts width j (v₁ i)) g -
      contextProductValues K (ctx₂ i) (treeStagesHalvingProducts width j (v₂ i)) g)
  have hs (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
      (v : C.Party → (ℕ → E) × (ℕ → E) × E) (i : C.Party) (hi : i ∉ D.1) (g : ℕ) :
      contextProductValues K (ctx i) (treeStagesHalvingProducts width j (v i)) g =
      contextProductValues K (localContext i) (treeStagesHalvingProducts width j (v i)) g := by
    unfold contextProductValues
    split <;> simp only [productShare_self K _ i (self i hi)]
  have step := halvRel_step K D (halvedLength^[j] width) _ _ _ _ _ _ h r out₁ out₂ (d 0) (d 1)
    (fun i hi T ht g hg => by
      rw [outputShift_sub K D ctx₁ ctx₂ _ _ out₁ out₂ hz i hi T ht g hg]
      interval_cases g <;> rfl)
    (by
      dsimp only [d]
      rw [Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      · rw [hs ctx₁ self₁ v₁ i (Finset.mem_filter.mp hi).2]; rfl
      · rw [hs ctx₂ self₂ v₂ i (Finset.mem_filter.mp hi).2]; rfl)
    (by
      dsimp only [d]
      rw [Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      · rw [hs ctx₁ self₁ v₁ i (Finset.mem_filter.mp hi).2]; rfl
      · rw [hs ctx₂ self₂ v₂ i (Finset.mem_filter.mp hi).2]; rfl)
  dsimp only
  rw [Function.iterate_succ_apply']
  apply HalvRel.congr_claims K D _ _ _ _ _ _ _ _ _ step
  · intro i hi
    simp only [treeStagesHalvingUpdate, conv_self K _ i (self₁ i hi)]
  · intro i hi
    simp only [treeStagesHalvingUpdate, conv_self K _ i (self₂ i hi)]

theorem lackedShare_add (D : C.Coalition) (i : C.Party) (x y : E) :
    lackedShare K D i (x + y) = lackedShare K D i x + lackedShare K D i y := by
  simp only [lackedShare, conv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T ht
  split_ifs <;> ring

theorem lackedShare_mul (D : C.Coalition) (i : C.Party) (a x : E) :
    lackedShare K D i (a * x) = a * lackedShare K D i x := by
  simp only [lackedShare, conv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T ht
  split_ifs <;> ring

theorem convShift_sub (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (products₁ products₂ : C.Party → List (Product C E)) (out₁ out₂ : C.Party → Shares C E)
    (h : OutputShift K D ctx₁ ctx₂ products₁ products₂ out₁ out₂)
    (i : C.Party) (hi : i ∉ D.1) (g : ℕ) (hg : g < 2) :
    conv K (ctx₁ i) (out₁ i) g - conv K (ctx₂ i) (out₂ i) g =
      lackedShare K D i (∑ j ∈ univ.filter (· ∉ D.1),
        (contextProductValues K (ctx₁ j) (products₁ j) g -
          contextProductValues K (ctx₂ j) (products₂ j) g)) := by
  rw [conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)]
  exact conv_sub_eq K i _ _ _ _ (fun T ht => outputShift_sub K D ctx₁ ctx₂ _ _ _ _ h i hi T ht g hg)

/-- The slice shape needs no holder agreement. -/
theorem sliceFold_shape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (τ : List E) (count j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesSliceProducts τ count j (v₁ i))
      (fun i => treeStagesSliceProducts τ count j (v₂ i)) out₁ out₂) (r : E)
    (h : SliceShape K D v₁ v₂) :
    SliceShape K D (fun i => treeStagesSliceUpdate K (ctx₁ i) τ count j (v₁ i) (out₁ i) r)
      (fun i => treeStagesSliceUpdate K (ctx₂ i) τ count j (v₂ i) (out₂ i) r) := by
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  let d := fun g => ∑ i ∈ univ.filter (· ∉ D.1),
    (contextProductValues K (ctx₁ i) (treeStagesSliceProducts τ count j (v₁ i)) g -
      contextProductValues K (ctx₂ i) (treeStagesSliceProducts τ count j (v₂ i)) g)
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  refine ⟨fun k => dx k + r * (dx k + dx (k + half)),
    fun k => dy k + r * (dy k + dy (k + half)),
    (1 + r) * d 0 + r * ((e + d 0) / τ.getD (sliceBits - 1 - j) 0) + r * (1 + r) * d 1,
    ?_, ?_, ?_⟩
  · intro i hi T k
    dsimp only [treeStagesSliceUpdate]
    rw [hx i hi T k, hx i hi T (k + half)]
    split_ifs <;> ring
  · intro i hi T k
    dsimp only [treeStagesSliceUpdate]
    rw [hy i hi T k, hy i hi T (k + half)]
    split_ifs <;> ring
  · intro i hi
    have h0 := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ hz i hi 0 (by omega)
    have h1 := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ hz i hi 1 (by omega)
    change _ = lackedShare K D i (d 0) at h0
    change _ = lackedShare K D i (d 1) at h1
    dsimp only [treeStagesSliceUpdate]
    simp only [div_eq_mul_inv, mul_comm (e + d 0), lackedShare_add, lackedShare_mul]
    linear_combination (1 + r + r * (τ.getD (sliceBits - 1 - j) 0)⁻¹) * h0 +
      (r * (τ.getD (sliceBits - 1 - j) 0)⁻¹) * he i hi + (r * (1 + r)) * h1

/-- The halving shape needs no holder agreement. -/
theorem halvFold_shape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (width j : ℕ) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesHalvingProducts width j (v₁ i))
      (fun i => treeStagesHalvingProducts width j (v₂ i)) out₁ out₂) (r : E)
    (h : HalvShape K D v₁ v₂) :
    HalvShape K D (fun i => treeStagesHalvingUpdate K (ctx₁ i) width j (v₁ i) (out₁ i) r)
      (fun i => treeStagesHalvingUpdate K (ctx₂ i) width j (v₂ i) (out₂ i) r) := by
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  let d := fun g => ∑ i ∈ univ.filter (· ∉ D.1),
    (contextProductValues K (ctx₁ i) (treeStagesHalvingProducts width j (v₁ i)) g -
      contextProductValues K (ctx₂ i) (treeStagesHalvingProducts width j (v₂ i)) g)
  let len := halvedLength^[j] width
  let half := halvedLength len
  refine ⟨fun k => dx k + r * (dx k + if k + half < len then dx (k + half) else 0),
    fun k => dy k + r * (dy k + if k + half < len then dy (k + half) else 0),
    d 0 + r * (e + d 1) + r ^ 2 * d 1, ?_, ?_, ?_⟩
  · intro i hi k
    dsimp only [treeStagesHalvingUpdate]
    split_ifs with hb
    · simp only [lackedShare_add, lackedShare_mul]
      linear_combination (1 + r) * hx i hi k + r * hx i hi (k + half)
    · simp only [add_zero, lackedShare_add, lackedShare_mul]
      linear_combination (1 + r) * hx i hi k
  · intro i hi k
    dsimp only [treeStagesHalvingUpdate]
    split_ifs with hb
    · simp only [lackedShare_add, lackedShare_mul]
      linear_combination (1 + r) * hy i hi k + r * hy i hi (k + half)
    · simp only [add_zero, lackedShare_add, lackedShare_mul]
      linear_combination (1 + r) * hy i hi k
  · intro i hi
    have h0 := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ hz i hi 0 (by omega)
    have h1 := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ hz i hi 1 (by omega)
    change _ = lackedShare K D i (d 0) at h0
    change _ = lackedShare K D i (d 1) at h1
    dsimp only [treeStagesHalvingUpdate]
    simp only [lackedShare_add, lackedShare_mul]
    linear_combination h0 + r * he i hi + (r + r ^ 2) * h1

/-- Converting held replicated shares preserves their lacked-term shape. -/
theorem sliceShape_to_halvShape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E) (h : SliceShape K D v₁ v₂) :
    HalvShape K D (fun i => (conv K (ctx₁ i) (v₁ i).1, conv K (ctx₁ i) (v₁ i).2.1, (v₁ i).2.2))
      (fun i => (conv K (ctx₂ i) (v₂ i).1, conv K (ctx₂ i) (v₂ i).2.1, (v₂ i).2.2)) := by
  letI : CharP E 2 := charTwo
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  refine ⟨dx, dy, e, ?_, ?_, he⟩
  · intro i hi k
    dsimp only
    rw [conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)]
    apply conv_sub_eq
    intro T ht
    rw [hx i hi T k]
    simp [ht, CharTwo.neg_eq]
  · intro i hi k
    dsimp only
    rw [conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)]
    apply conv_sub_eq
    intro T ht
    rw [hy i hi T k]
    simp [ht, CharTwo.neg_eq]

/-- The conversion at the slice boundary has the halving shape without an agreement premise. -/
theorem lastSlice_shape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (τ : List E) (count j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesSliceProducts τ count j (v₁ i))
      (fun i => treeStagesSliceProducts τ count j (v₂ i)) out₁ out₂) (r : E)
    (h : SliceShape K D v₁ v₂) :
    HalvShape K D (fun i => treeTwinSliceShamir K (ctx₁ i) τ count j (v₁ i) (out₁ i) r)
      (fun i => treeTwinSliceShamir K (ctx₂ i) τ count j (v₂ i) (out₂ i) r) :=
  sliceShape_to_halvShape K D ctx₁ ctx₂ self₁ self₂ _ _
    (sliceFold_shape K D ctx₁ ctx₂ self₁ self₂ τ count j v₁ v₂ out₁ out₂ hz r h)

/-- At the last slice, globally valid Shamir vectors extend the honest conversions. -/
theorem lastSlice_rel [CharP E 2] (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (τ : List E) (count j : ℕ) (hj : j + 1 = sliceBits) (hc : count ≠ 0)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E) (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesSliceProducts τ count j (v₁ i))
      (fun i => treeStagesSliceProducts τ count j (v₂ i)) out₁ out₂) (r : E)
    (h : SliceRel K D τ count j (fun i => (v₁ i).1) (fun i => (v₁ i).2.1)
      (fun i => (v₂ i).1) (fun i => (v₂ i).2.1) (fun i => (v₁ i).2.2) (fun i => (v₂ i).2.2)) :
    let u₁ := fun i => treeStagesSliceUpdate K (ctx₁ i) τ count j (v₁ i) (out₁ i) r
    let u₂ := fun i => treeStagesSliceUpdate K (ctx₂ i) τ count j (v₂ i) (out₂ i) r
    ∃ AR BR AD BD : C.Party → ℕ → E,
      (∀ i, i ∉ D.1 → conv K (ctx₁ i) (u₁ i).1 = AR i ∧ conv K (ctx₁ i) (u₁ i).2.1 = BR i ∧
        conv K (ctx₂ i) (u₂ i).1 = AD i ∧ conv K (ctx₂ i) (u₂ i).2.1 = BD i) ∧
      HalvRel K D (sliceWidth count) AR BR AD BD (fun i => (u₁ i).2.2) (fun i => (u₂ i).2.2) := by
  have step := sliceFold_rel K D ctx₁ ctx₂ self₁ self₂ τ count j (by omega) hc hτ v₁ v₂ out₁ out₂ hz r h
  rw [hj] at step
  obtain ⟨AR, BR, AD, BD, hs, hr⟩ := sliceRel_halvRel' K D τ count _ _ _ _ _ _ step
  refine ⟨AR, BR, AD, BD, ?_, hr⟩
  intro i hi
  simpa only [conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)] using hs i hi

/-- Every honest holder appends exactly the same number of encoded field elements. -/
theorem recordPeer_block (i : C.Party) (hist : C.Term → List Bit) (z : Shares C E)
    (count : ℕ) (T : C.Term) (held : i ∈ C.holders T) :
    ∃ block : List Bit,
      block.length = (((List.range count).filter fun g => (filler K .peer T g).isSome).length * elementBits) ∧
      recordPeer K (elementCodec K) i hist z count T = hist T ++ block := by
  refine ⟨((List.range count).filter fun g => (filler K .peer T g).isSome).flatMap
    ((elementCodec K).toBits ∘ z T), ?_, by simp only [recordPeer, if_pos held]⟩
  have length (gs : List ℕ) :
      (gs.flatMap (fun g => List.ofFn (K.encode (z T g)))).length = gs.length * elementBits := by
    induction gs with
    | nil => simp
    | cons g gs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  exact length _

/-- An unfilled term contributes no block to a peer history. -/
theorem filler_none (T : C.Term) (ht : T ∉ filledTerms K) (g : ℕ) : filler K .peer T g = none := by
  simp only [filler, List.find?_eq_none]
  intro i _ he
  apply ht
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, of_decide_eq_true he⟩

/-- The field returned by a successful reshare, with the honest inbox expanded. -/
theorem extendMultOutput_value {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) (out : Shares C E × RunState C)
    (ho : treeSimExtendMultOutputs K D ctx count rnd v st k sent i = some out) :
    out.1 = reshareZ K (ctx i) (elementCodec K) (rnd i).1 (rnd i).2 (v i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) (elementCodec K) (rnd j).1 (rnd j).2 (v j) count i) ∧
    out.2.history = recordPeer K (elementCodec K) (ctx i).self (st i).history out.1 count := by
  simp only [treeSimExtendMultOutputs, if_neg hi, treeSimExtendMultReturn] at ho
  split at ho
  · cases ho
  · have he := Option.some.inj ho
    subst out
    refine ⟨?_, rfl⟩
    apply congrArg (reshareZ K (ctx i) (elementCodec K) (rnd i).1 (rnd i).2 (v i) count)
    funext j
    by_cases hj : j ∈ D.1 <;>
      simp [treeSimExtendMultWaiting, treeSimPeerStep, Step.delivered, hj]

/-- Hidden filled terms are supplied only by honest holders, so their recorded blocks agree. -/
theorem commonHistory_extendMult {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (out : C.Party → Shares C E × RunState C)
    (ho : ∀ i, i ∉ D.1 → treeSimExtendMultOutputs K D ctx count rnd v st k sent i = some (out i))
    (hist : CommonHistory D (fun _ => true) st) :
    CommonHistory D (fun _ => true) (fun i => (out i).2) := by
  intro T ht i j hi hj _ _ hit hjt
  have ei := extendMultOutput_value K D ctx count rnd v st k sent i hi (out i) (ho i hi)
  have ej := extendMultOutput_value K D ctx count rnd v st k sent j hj (out j) (ho j hj)
  rw [ei.2, ej.2, self i hi, self j hj]
  simp only [recordPeer, if_pos hit, if_pos hjt]
  rw [hist T ht i j hi hj rfl rfl hit hjt]
  congr 1
  apply List.flatMap_congr
  intro g hg
  have hg' := (List.mem_filter.mp hg).1
  have hgcount := List.mem_range.mp hg'
  have filled : T ∈ filledTerms K := by
    by_contra hf
    have hsome := (List.mem_filter.mp hg).2
    simp [filler_none K T hf g] at hsome
  have honest (l : C.Party) (hl : K.filled l = T) : l ∉ D.1 := by
    intro corrupt
    exact lackedTerm_unknown D T ht ⟨l, corrupt, hl ▸ K.filled_held l⟩
  have values : (out i).1 T g = (out j).1 T g := by
    rw [ei.1, ej.1, treeSim_fieldReshareZ_value K D ctx self rnd v count sent i hi,
      treeSim_fieldReshareZ_value K D ctx self rnd v count sent j hj]
    simp only [hit, hjt, not_true_eq_false, Nat.not_le.mpr hgcount, or_self, if_false,
      treeSimFieldPeerValue, if_pos filled]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [if_neg (honest l (Finset.mem_filter.mp hl).2)]
  simp only [Function.comp_apply, values]

theorem HalvShape.congr_honest (D : C.Coalition)
    (v₁ v₂ u₁ u₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (h : HalvShape K D v₁ v₂) (h₁ : ∀ i, i ∉ D.1 → v₁ i = u₁ i)
    (h₂ : ∀ i, i ∉ D.1 → v₂ i = u₂ i) : HalvShape K D u₁ u₂ := by
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  exact ⟨dx, dy, e, fun i hi k => by rw [← h₁ i hi, ← h₂ i hi]; exact hx i hi k,
    fun i hi k => by rw [← h₁ i hi, ← h₂ i hi]; exact hy i hi k,
    fun i hi => by rw [← h₁ i hi, ← h₂ i hi]; exact he i hi⟩

section Saved
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (parameter : PublicParameter) (openings : List (List (List Bit)))

structure SavedWitness where
  caller : Caller K circuits settings top tree D parameter openings
  phase : SavedPhase C E

def SavedState (q : TreeStagesExtendMultChallenge K D)
    (w : SavedWitness K circuits settings top tree D parameter openings) : Prop :=
  let c := w.caller; let count := tupleCount c.rest.circs
    let data := c.checkData K circuits settings top tree D parameter openings
    match w.phase with
    | .slice τ j v₁ v₂ => (∀ b < sliceBits, τ.getD b 0 ≠ 0) ∧
      (∀ i, i ∉ D.1 → q.body₁ i = treeStagesSliceBody K (q.ctx₁ i) τ
        (c.count₁ K circuits settings top tree D parameter openings i) j (sliceSuffix j) (v₁ i) (data.finish₁ i)) ∧
      (∀ i, i ∉ D.1 → q.body₂ i = treeStagesSliceBody K (q.ctx₂ i) τ
        (c.count₁ K circuits settings top tree D parameter openings i) j (sliceSuffix j) (v₂ i) (data.finish₂ i)) ∧
      (∀ i, i ∉ D.1 → q.products₁ i = treeStagesSliceProducts τ count j (v₁ i)) ∧
      (∀ i, i ∉ D.1 → q.products₂ i = treeStagesSliceProducts τ count j (v₂ i)) ∧
      SliceShape K D v₁ v₂ ∧
      (AllHistory D q.st₁ → SliceRel K D τ count j (fun i => (v₁ i).1) (fun i => (v₁ i).2.1)
        (fun i => (v₂ i).1) (fun i => (v₂ i).2.1) (fun i => (v₁ i).2.2) (fun i => (v₂ i).2.2))
    | .halving j v₁ v₂ =>
      (∀ i, i ∉ D.1 → q.body₁ i = treeStagesHalvingBody K (q.ctx₁ i)
        (sliceWidth (c.count₁ K circuits settings top tree D parameter openings i)) j
        (halvSuffix count j) (v₁ i) (data.finish₁ i)) ∧
      (∀ i, i ∉ D.1 → q.body₂ i = treeStagesHalvingBody K (q.ctx₂ i)
        (sliceWidth (c.count₁ K circuits settings top tree D parameter openings i)) j
        (halvSuffix count j) (v₂ i) (data.finish₂ i)) ∧
      (∀ i, i ∉ D.1 → q.products₁ i = treeStagesHalvingProducts (sliceWidth count) j (v₁ i)) ∧
      (∀ i, i ∉ D.1 → q.products₂ i = treeStagesHalvingProducts (sliceWidth count) j (v₂ i)) ∧
      HalvShape K D v₁ v₂ ∧
      (AllHistory D q.st₁ → HalvRel K D (halvedLength^[j] (sliceWidth count))
        (fun i => (v₁ i).1) (fun i => (v₁ i).2.1) (fun i => (v₂ i).1) (fun i => (v₂ i).2.1)
        (fun i => (v₁ i).2.2) (fun i => (v₂ i).2.2))

/-- One caller and one phase supply every saved-state condition. -/
structure SavedRelAt (q : TreeStagesExtendMultChallenge K D)
    (w : SavedWitness K circuits settings top tree D parameter openings) : Prop where
  tags : ∀ i, i ∉ D.1 → (q.st₁ i).tag = (q.st₂ i).tag
  ctx₁ : q.ctx₁ = w.caller.peer.ctx₁
  ctx₂ : q.ctx₂ = w.caller.peer.ctx₂
  counts : ∀ i, i ∉ D.1 → w.caller.count₁ K circuits settings top tree D parameter openings i =
    tupleCount w.caller.rest.circs
  bound : w.phase.Bound (tupleCount w.caller.rest.circs)
  position : Position circuits settings tree D parameter w.caller.rest.circs
    (savedOffset w.caller.rest.circs w.phase) q.st₁
  history₁ : CommonHistory D (fun _ => true) q.st₁
  history₂ : CommonHistory D (fun _ => true) q.st₂
  state : SavedState K circuits settings top tree D parameter openings q w

def SavedRel (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, SavedRelAt K circuits settings top tree D parameter openings q w

def SavedAdvancing (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, SavedRelAt K circuits settings top tree D parameter openings q w ∧
    ¬ w.phase.Finishing (tupleCount w.caller.rest.circs)

def SavedFinishing (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, SavedRelAt K circuits settings top tree D parameter openings q w ∧
    w.phase.Finishing (tupleCount w.caller.rest.circs)

variable {K circuits settings top tree D parameter openings}

theorem savedRel_cases {q : TreeStagesExtendMultChallenge K D}
    (h : SavedRel K circuits settings top tree D parameter openings q) :
    SavedAdvancing K circuits settings top tree D parameter openings q ∨
      SavedFinishing K circuits settings top tree D parameter openings q := by
  obtain ⟨w, hw⟩ := h
  by_cases hf : w.phase.Finishing (tupleCount w.caller.rest.circs)
  · exact Or.inr ⟨w, hw, hf⟩
  · exact Or.inl ⟨w, hw, hf⟩

namespace SavedRelAt
variable {q : TreeStagesExtendMultChallenge K D}
    {w : SavedWitness K circuits settings top tree D parameter openings}

theorem count_ne_zero (h : SavedRelAt K circuits settings top tree D parameter openings q w) :
    tupleCount w.caller.rest.circs ≠ 0 := by
  have hn := w.caller.nonzero₁ q.pivotParty q.pivot.honest
  rw [← h.counts q.pivotParty q.pivot.honest]
  simpa [Caller.count₁, Caller.checkData, TreeStagesRerandTail.checkCoinData,
    treeStagesRerandTuples, q.pivot.honest] using hn

theorem savedPlus (h : SavedRelAt K circuits settings top tree D parameter openings q w) :
    SavedPlus K circuits settings top tree D parameter openings q := by
  refine ⟨h.tags, w.caller, w.phase.remaining (tupleCount w.caller.rest.circs),
    savedOffset w.caller.rest.circs w.phase, h.ctx₁, h.ctx₂, ?_, h.position, h.counts,
    h.history₁, h.history₂⟩
  obtain ⟨c, phase⟩ := w
  cases phase with
  | slice τ j v₁ v₂ =>
    obtain ⟨_, b₁, b₂, _⟩ := h.state
    exact Or.inl ⟨fun _ => τ, fun _ => τ, j, v₁, v₂, b₁, b₂⟩
  | halving j v₁ v₂ =>
    obtain ⟨b₁, b₂, _⟩ := h.state
    exact Or.inr ⟨j, v₁, v₂, b₁, b₂⟩

theorem finishing_halving (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (hf : w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    ∃ j v₁ v₂, w.phase = .halving j v₁ v₂ ∧ j + 1 = halvSteps (tupleCount w.caller.rest.circs) := by
  have hb := h.bound
  have hp := halvSteps_pos h.count_ne_zero
  cases he : w.phase with
  | slice τ j v₁ v₂ => simp only [he, SavedPhase.Finishing] at hf; omega
  | halving j v₁ v₂ =>
    refine ⟨j, v₁, v₂, rfl, ?_⟩
    simp only [he, SavedPhase.Finishing, SavedPhase.Bound] at hf hb
    exact (halvSuffix_eq_nil hb).mp hf

theorem finishing_length (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (hf : w.phase.Finishing (tupleCount w.caller.rest.circs)) (j : ℕ)
    (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E) (he : w.phase = .halving j v₁ v₂) :
    halvedLength (halvedLength^[j] (sliceWidth (tupleCount w.caller.rest.circs))) = 1 := by
  obtain ⟨k, u₁, u₂, hk, hend⟩ := h.finishing_halving hf
  rw [he] at hk
  cases hk
  exact halv_last_length h.count_ne_zero hend


theorem source (h : SavedRelAt K circuits settings top tree D parameter openings q w) :
    match w.phase with
    | .slice _ j _ _ => w.caller.Slice K circuits settings top tree D parameter openings q (sliceSuffix j)
    | .halving j _ _ => w.caller.Halving K circuits settings top tree D parameter openings q
        (halvSuffix (tupleCount w.caller.rest.circs) j) := by
  obtain ⟨c, phase⟩ := w
  cases phase with
  | slice τ j v₁ v₂ =>
    obtain ⟨_, b₁, b₂, _⟩ := h.state
    exact ⟨fun _ => τ, fun _ => τ, j, v₁, v₂, b₁, b₂⟩
  | halving j v₁ v₂ =>
    obtain ⟨b₁, b₂, _⟩ := h.state
    exact ⟨j, v₁, v₂, b₁, b₂⟩

theorem advancing_old (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (ha : ¬ w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    Advancing K circuits settings top tree D parameter openings q := by
  refine ⟨w.caller, h.ctx₁, h.ctx₂, ?_⟩
  have hs := h.source
  have hb := h.bound
  cases he : w.phase with
  | slice τ j v₁ v₂ =>
    simp only [he] at hs
    simp only [he, SavedPhase.Bound] at hb
    by_cases hj : j + 1 < sliceBits
    · rw [sliceSuffix_cons hj] at hs
      exact Or.inl ⟨j + 1, sliceSuffix (j + 1), Or.inl hs⟩
    · have hn := (sliceSuffix_eq_nil hb).mpr (by omega)
      rw [hn] at hs
      refine Or.inr ⟨hs, 0, halvSuffix (tupleCount w.caller.rest.circs) 0, ?_⟩
      intro i hi
      rw [h.counts i hi, range_halvings_sub, range_halvSteps h.count_ne_zero]
  | halving j v₁ v₂ =>
    simp only [he, SavedPhase.Finishing] at ha
    simp only [he, SavedPhase.Bound] at hb
    simp only [he] at hs
    have hj : j + 1 < halvSteps (tupleCount w.caller.rest.circs) := by
      have hn := (halvSuffix_eq_nil hb).not.mp ha
      omega
    rw [halvSuffix_cons hj] at hs
    exact Or.inl ⟨j + 1, halvSuffix (tupleCount w.caller.rest.circs) (j + 1), Or.inr hs⟩

theorem finishing_old (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (hf : w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    Finishing K circuits settings top tree D parameter openings q := by
  obtain ⟨j, v₁, v₂, he, _⟩ := h.finishing_halving hf
  have hs := h.source
  simp only [he] at hs
  simp only [he, SavedPhase.Finishing] at hf
  rw [hf] at hs
  exact ⟨w.caller, h.ctx₁, h.ctx₂, Or.inl hs⟩

theorem address (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (i : C.Party) (hi : i ∉ D.1) :
    let x := q.reductionContext K D rnd δ sent
    (x.tag i, x.hashLabel i) = ((q.st₁ q.pivotParty).tag, q.label + 1) ∧
      (x.tag i, x.hashLabel i) ∈ tagLabels circuits settings tree parameter := by
  dsimp only
  rw [q.reductionContext_address K D rnd δ sent i]
  constructor
  · obtain ⟨enc, k, _, _, _, pos⟩ := h.position
    rw [(pos i hi).1, (pos q.pivotParty q.pivot.honest).1, q.lab₁ i hi]
  · exact position_mem circuits settings tree D parameter _ _ _ h.position 1 (by omega) i hi

theorem count_eq_two (h : SavedRelAt K circuits settings top tree D parameter openings q w) : q.count = 2 := by
  have hs := h.state
  have len := q.len₁ q.pivotParty
  obtain ⟨c, phase⟩ := w
  cases phase with
  | slice τ j v₁ v₂ =>
    obtain ⟨_, _, _, prod, _⟩ := hs
    rw [prod q.pivotParty q.pivot.honest] at len
    exact len.symm
  | halving j v₁ v₂ =>
    obtain ⟨_, _, prod, _⟩ := hs
    rw [prod q.pivotParty q.pivot.honest] at len
    exact len.symm

/-- All-live prevents the default branch from replacing any honest field output. -/
theorem coinNext_exit (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit)
    (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) (i : C.Party) (hi : i ∉ D.1) :
    TreeSimExtendMultExitRel K D (q.data K D rnd δ) i
      ((q.coinNext K D rnd δ sent).x₁ i) ((q.coinNext K D rnd δ sent).x₂ i) := by
  let n := q.coinNext K D rnd δ sent
  have a := n.shape₁ i
  have b := n.shape₂ i
  have hl : n.live i = true := live i hi
  simp only [if_neg hi, hl, ↓reduceIte] at a b
  have rel := (q.data K D rnd δ).outputs K D sent i
  change Option.Rel _
    (treeSimExtendMultOutputs K D q.ctx₁ q.count rnd
      (fun i => contextProductValues K (q.ctx₁ i) (q.products₁ i)) q.st₁ (q.k₁ K D) sent i)
    (treeSimExtendMultOutputs K D q.ctx₂ q.count (q.data K D rnd δ).rnd₂
      (fun i => contextProductValues K (q.ctx₂ i) (q.products₂ i)) q.st₂ (q.k₂ K D) sent i) at rel
  rw [a, b] at rel
  cases rel with
  | some h => exact h

theorem outputShift (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) :
    OutputShift K D q.ctx₁ q.ctx₂ q.products₁ q.products₂
      (fun i => ((q.coinNext K D rnd δ sent).x₁ i).1)
      (fun i => ((q.coinNext K D rnd δ sent).x₂ i).1) := by
  intro i hi
  have he := (coinNext_exit rnd δ sent live i hi).1
  change _ = treeSimFieldHeldShift D i q.count _ _ at he
  exact he.trans (congrArg (fun cnt => treeSimFieldHeldShift D i cnt _ _) h.count_eq_two)

/-- A later all-holder history equality cancels the exact field-record blocks. -/
theorem history_before (_h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (recipe : TreeTwinHonestReductionRecipe K D q) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true)
    (values : C.Party → E)
    (hist : AllHistory D ((recipe.reduction K D rnd δ sent).step K D values).st₁) :
    AllHistory D q.st₁ := by
  apply allHistory_of_append D q.st₁ _
    (fun T => ((List.range q.count).filter fun g => (filler K .peer T g).isSome).length * elementBits) _ hist
  intro T i hi held
  have he := (coinNext_exit rnd δ sent live i hi).2.1
  change (q.coinNext K D rnd δ sent).st₁ i = _ at he
  change ∃ l : List Bit, l.length = _ ∧ ((q.coinNext K D rnd δ sent).st₁ i).history T = _
  rw [he]
  change ∃ l : List Bit, l.length = _ ∧ recordPeer K (elementCodec K) (q.ctx₁ i).self (q.st₁ i).history _ q.count T = _
  rw [q.self₁ i hi]
  exact recordPeer_block K i _ _ _ T held

/-- The same caller, position and histories accompany any next saved phase
with the actual incremented index and its bounded schedule. -/
theorem advance (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (recipe : TreeTwinHonestReductionRecipe K D q) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) (values : C.Party → E)
    (phase : SavedPhase C E) (bound : phase.Bound (tupleCount w.caller.rest.circs))
    (index : phase.index = w.phase.index + 1)
    (state : SavedState K circuits settings top tree D parameter openings
      ((recipe.reduction K D rnd δ sent).step K D values) ⟨w.caller, phase⟩) :
    SavedRelAt K circuits settings top tree D parameter openings
      ((recipe.reduction K D rnd δ sent).step K D values) ⟨w.caller, phase⟩ := by
  let n := q.coinNext K D rnd δ sent
  have outputs₁ (i : C.Party) (hi : i ∉ D.1) := n.shape₁ i
  have outputs₂ (i : C.Party) (hi : i ∉ D.1) := n.shape₂ i
  have live₁ (i : C.Party) (hi : i ∉ D.1) : treeSimExtendMultOutputs K D q.ctx₁ q.count rnd
      (fun i => contextProductValues K (q.ctx₁ i) (q.products₁ i)) q.st₁ (q.k₁ K D) sent i = some (n.x₁ i) := by
    have hl : n.live i = true := live i hi
    simpa only [if_neg hi, hl, ↓reduceIte] using outputs₁ i hi
  have live₂ (i : C.Party) (hi : i ∉ D.1) : treeSimExtendMultOutputs K D q.ctx₂ q.count (q.data K D rnd δ).rnd₂
      (fun i => contextProductValues K (q.ctx₂ i) (q.products₂ i)) q.st₂ (q.k₂ K D) sent i = some (n.x₂ i) := by
    have hl : n.live i = true := live i hi
    simpa only [if_neg hi, hl, ↓reduceIte] using outputs₂ i hi
  refine ⟨recipe.step_tags K D rnd δ sent values h.tags, h.ctx₁, h.ctx₂, h.counts,
    bound, ?_, ?_, ?_, state⟩
  · have off : savedOffset w.caller.rest.circs phase = savedOffset w.caller.rest.circs w.phase + 2 := by
      simp only [savedOffset, index]; omega
    rw [off]
    apply position_shift circuits settings tree D parameter _ _ 2 _ _ h.position
    · intro i hi; exact (q.coinNext_tag K D rnd δ sent i).1
    · intro i hi
      change (n.st₁ i).label + 1 = (q.st₁ i).label + 2
      rw [n.lab₁ i hi, q.lab₁ i hi]
      rfl
    · intro jobs hj
      rw [← off, hj]
      exact savedOffset_le circuits parameter jobs (congrArg tupleCount hj) (hj ▸ h.count_ne_zero) (hj ▸ bound)
  · exact commonHistory_extendMult K D q.ctx₁ q.self₁ q.count rnd _ q.st₁ _ sent n.x₁ live₁ h.history₁
  · exact commonHistory_extendMult K D q.ctx₂ q.self₂ q.count (q.data K D rnd δ).rnd₂ _ q.st₂ _ sent n.x₂ live₂ h.history₂

set_option maxHeartbeats 1600000 in
/-- Every advancing saved phase closes under its concrete recipe, with the
same caller and exactly the next schedule index. -/
theorem closure (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (adv : ¬ w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    ∃ recipe : TreeTwinHonestReductionRecipe K D q, ∀ rnd δ sent,
      (∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) →
      ∀ (values : C.Party → E) (r : E), (∀ i, i ∉ D.1 → values i = r) →
      ∃ w', SavedRelAt K circuits settings top tree D parameter openings
        ((recipe.reduction K D rnd δ sent).step K D values) w' ∧
        w'.caller = w.caller ∧ w'.phase.index = w.phase.index + 1 := by
  letI : CharP E 2 := charTwo
  obtain ⟨c, phase⟩ := w
  cases phase with
  | slice τ j v₁ v₂ =>
    have bound : j < sliceBits := h.bound
    obtain ⟨hτ, b₁, b₂, p₁, p₂, shape, rel⟩ := h.state
    by_cases hj : j + 1 < sliceBits
    · have b₁' := b₁
      have b₂' := b₂
      simp only [sliceSuffix_cons hj] at b₁' b₂'
      let recipe := TreeTwinHonestReductionRecipe.slice K D q (fun _ => τ) (fun _ => τ)
        (c.count₁ K circuits settings top tree D parameter openings)
        (c.count₁ K circuits settings top tree D parameter openings) j (j + 1) (sliceSuffix (j + 1)) v₁ v₂
        (c.checkData K circuits settings top tree D parameter openings).finish₁
        (c.checkData K circuits settings top tree D parameter openings).finish₂ b₁' b₂'
      refine ⟨recipe, ?_⟩
      intro rnd δ sent live values r hr
      let n := q.coinNext K D rnd δ sent
      let u₁ := fun i => treeStagesSliceUpdate K (q.ctx₁ i) τ (tupleCount c.rest.circs) j (v₁ i) (n.x₁ i).1 r
      let u₂ := fun i => treeStagesSliceUpdate K (q.ctx₂ i) τ (tupleCount c.rest.circs) j (v₂ i) (n.x₂ i).1 r
      have hz := OutputShift.congr_products K D q.ctx₁ q.ctx₂ _ _ _ _ _ _
        (h.outputShift rnd δ sent live) p₁ p₂
      refine ⟨⟨c, .slice τ (j + 1) u₁ u₂⟩, h.advance recipe rnd δ sent live values _ hj rfl ?_, rfl, rfl⟩
      refine ⟨hτ, ?_, ?_, ?_, ?_,
        sliceFold_shape K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ τ _ j v₁ v₂ _ _ hz r shape, ?_⟩
      · intro i hi
        change treeStagesSliceBody K (q.ctx₁ i) τ _ (j + 1) _
          (treeStagesSliceUpdate K (q.ctx₁ i) τ _ j (v₁ i) (n.x₁ i).1 (values i)) _ = _
        dsimp only
        rw [hr i hi, h.counts i hi]; rfl
      · intro i hi
        change treeStagesSliceBody K (q.ctx₂ i) τ _ (j + 1) _
          (treeStagesSliceUpdate K (q.ctx₂ i) τ _ j (v₂ i) (n.x₂ i).1 (values i)) _ = _
        dsimp only
        rw [hr i hi, h.counts i hi]; rfl
      · intro i hi
        change treeStagesSliceProducts τ _ (j + 1)
          (treeStagesSliceUpdate K (q.ctx₁ i) τ _ j (v₁ i) (n.x₁ i).1 (values i)) = _
        dsimp only
        rw [hr i hi, h.counts i hi]
      · intro i hi
        change treeStagesSliceProducts τ _ (j + 1)
          (treeStagesSliceUpdate K (q.ctx₂ i) τ _ j (v₂ i) (n.x₂ i).1 (values i)) = _
        dsimp only
        rw [hr i hi, h.counts i hi]
      · intro hist
        exact sliceFold_rel K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ τ _ j bound h.count_ne_zero hτ
          v₁ v₂ _ _ hz r (rel (h.history_before recipe rnd δ sent live values hist))
    · have last : j + 1 = sliceBits := by omega
      have suffix : sliceSuffix j = [] := (sliceSuffix_eq_nil bound).mpr last
      have b₁' := b₁
      have b₂' := b₂
      simp only [suffix] at b₁' b₂'
      have schedule (i : C.Party) (hi : i ∉ D.1) :
          List.range (halvings (c.count₁ K circuits settings top tree D parameter openings i) - sliceBits) =
          0 :: halvSuffix (tupleCount c.rest.circs) 0 := by
        rw [h.counts i hi, range_halvings_sub, range_halvSteps h.count_ne_zero]
      let recipe := TreeTwinHonestReductionRecipe.sliceHalving K D q (fun _ => τ) (fun _ => τ)
        (c.count₁ K circuits settings top tree D parameter openings)
        (c.count₁ K circuits settings top tree D parameter openings) j 0 (halvSuffix (tupleCount c.rest.circs) 0)
        schedule schedule v₁ v₂ (c.checkData K circuits settings top tree D parameter openings).finish₁
        (c.checkData K circuits settings top tree D parameter openings).finish₂ b₁' b₂'
      refine ⟨recipe, ?_⟩
      intro rnd δ sent live values r hr
      let n := q.coinNext K D rnd δ sent
      let next := (recipe.reduction K D rnd δ sent).step K D values
      let actual₁ := fun i => treeTwinSliceShamir K (q.ctx₁ i) τ (tupleCount c.rest.circs) j (v₁ i) (n.x₁ i).1 r
      let actual₂ := fun i => treeTwinSliceShamir K (q.ctx₂ i) τ (tupleCount c.rest.circs) j (v₂ i) (n.x₂ i).1 r
      have hz := OutputShift.congr_products K D q.ctx₁ q.ctx₂ _ _ _ _ _ _
        (h.outputShift rnd δ sent live) p₁ p₂
      have hs := lastSlice_shape K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ τ _ j v₁ v₂ _ _ hz r shape
      have construct (u₁ u₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
          (eq₁ : ∀ i, i ∉ D.1 → actual₁ i = u₁ i) (eq₂ : ∀ i, i ∉ D.1 → actual₂ i = u₂ i)
          (relation : AllHistory D next.st₁ → HalvRel K D (sliceWidth (tupleCount c.rest.circs))
            (fun i => (u₁ i).1) (fun i => (u₁ i).2.1) (fun i => (u₂ i).1) (fun i => (u₂ i).2.1)
            (fun i => (u₁ i).2.2) (fun i => (u₂ i).2.2)) :
          SavedRelAt K circuits settings top tree D parameter openings next ⟨c, .halving 0 u₁ u₂⟩ := by
        apply h.advance recipe rnd δ sent live values (.halving 0 u₁ u₂) (halvSteps_pos h.count_ne_zero)
          (by simp only [SavedPhase.index, Nat.add_zero]; exact last.symm)
        refine ⟨?_, ?_, ?_, ?_, HalvShape.congr_honest K D actual₁ actual₂ u₁ u₂ hs eq₁ eq₂, ?_⟩
        · intro i hi
          change treeStagesHalvingBody K (q.ctx₁ i) (sliceWidth _) 0 _
            (treeTwinSliceShamir K (q.ctx₁ i) τ _ j (v₁ i) (n.x₁ i).1 (values i)) _ = _
          dsimp only
          rw [hr i hi, h.counts i hi]
          change treeStagesHalvingBody K (q.ctx₁ i) _ 0 _ (actual₁ i) _ = _
          rw [eq₁ i hi]
          rfl
        · intro i hi
          change treeStagesHalvingBody K (q.ctx₂ i) (sliceWidth _) 0 _
            (treeTwinSliceShamir K (q.ctx₂ i) τ _ j (v₂ i) (n.x₂ i).1 (values i)) _ = _
          dsimp only
          rw [hr i hi, h.counts i hi]
          change treeStagesHalvingBody K (q.ctx₂ i) _ 0 _ (actual₂ i) _ = _
          rw [eq₂ i hi]
          rfl
        · intro i hi
          change treeStagesHalvingProducts (sliceWidth _) 0
            (treeTwinSliceShamir K (q.ctx₁ i) τ _ j (v₁ i) (n.x₁ i).1 (values i)) = _
          dsimp only
          rw [hr i hi, h.counts i hi]
          change treeStagesHalvingProducts _ 0 (actual₁ i) = _
          rw [eq₁ i hi]
        · intro i hi
          change treeStagesHalvingProducts (sliceWidth _) 0
            (treeTwinSliceShamir K (q.ctx₂ i) τ _ j (v₂ i) (n.x₂ i).1 (values i)) = _
          dsimp only
          rw [hr i hi, h.counts i hi]
          change treeStagesHalvingProducts _ 0 (actual₂ i) = _
          rw [eq₂ i hi]
        · exact relation
      by_cases hist : AllHistory D next.st₁
      · obtain ⟨AR, BR, AD, BD, he, hrel⟩ := lastSlice_rel K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ τ _ j
          last h.count_ne_zero hτ v₁ v₂ _ _ hz r (rel (h.history_before recipe rnd δ sent live values hist))
        let u₁ := fun i => (AR i, BR i, (actual₁ i).2.2)
        let u₂ := fun i => (AD i, BD i, (actual₂ i).2.2)
        have eq₁ (i : C.Party) (hi : i ∉ D.1) : actual₁ i = u₁ i := by
          exact Prod.ext (he i hi).1 (Prod.ext (he i hi).2.1 rfl)
        have eq₂ (i : C.Party) (hi : i ∉ D.1) : actual₂ i = u₂ i := by
          exact Prod.ext (he i hi).2.2.1 (Prod.ext (he i hi).2.2.2 rfl)
        exact ⟨⟨c, .halving 0 u₁ u₂⟩, construct u₁ u₂ eq₁ eq₂ (fun _ => hrel), rfl,
          by simp only [SavedPhase.index, Nat.add_zero]; exact last.symm⟩
      · exact ⟨⟨c, .halving 0 actual₁ actual₂⟩,
          construct actual₁ actual₂ (fun _ _ => rfl) (fun _ _ => rfl) (fun hh => (hist hh).elim), rfl,
          by simp only [SavedPhase.index, Nat.add_zero]; exact last.symm⟩
  | halving j v₁ v₂ =>
    have bound : j < halvSteps (tupleCount c.rest.circs) := h.bound
    have hn : halvSuffix (tupleCount c.rest.circs) j ≠ [] := adv
    have hj : j + 1 < halvSteps (tupleCount c.rest.circs) := by
      have he := (halvSuffix_eq_nil bound).not.mp hn
      omega
    obtain ⟨b₁, b₂, p₁, p₂, shape, rel⟩ := h.state
    simp only [halvSuffix_cons hj] at b₁ b₂
    let recipe := TreeTwinHonestReductionRecipe.halving K D q
      (fun i => sliceWidth (c.count₁ K circuits settings top tree D parameter openings i))
      (fun i => sliceWidth (c.count₁ K circuits settings top tree D parameter openings i))
      j (j + 1) (halvSuffix (tupleCount c.rest.circs) (j + 1)) v₁ v₂
      (c.checkData K circuits settings top tree D parameter openings).finish₁
      (c.checkData K circuits settings top tree D parameter openings).finish₂ b₁ b₂
    refine ⟨recipe, ?_⟩
    intro rnd δ sent live values r hr
    let n := q.coinNext K D rnd δ sent
    let u₁ := fun i => treeStagesHalvingUpdate K (q.ctx₁ i) (sliceWidth (tupleCount c.rest.circs)) j (v₁ i) (n.x₁ i).1 r
    let u₂ := fun i => treeStagesHalvingUpdate K (q.ctx₂ i) (sliceWidth (tupleCount c.rest.circs)) j (v₂ i) (n.x₂ i).1 r
    have hz := OutputShift.congr_products K D q.ctx₁ q.ctx₂ _ _ _ _ _ _
      (h.outputShift rnd δ sent live) p₁ p₂
    refine ⟨⟨c, .halving (j + 1) u₁ u₂⟩,
      h.advance recipe rnd δ sent live values _ hj (by simp [SavedPhase.index, Nat.add_assoc]) ?_, rfl,
      by simp [SavedPhase.index, Nat.add_assoc]⟩
    refine ⟨?_, ?_, ?_, ?_, halvFold_shape K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ _ j v₁ v₂ _ _ hz r shape, ?_⟩
    · intro i hi
      change treeStagesHalvingBody K (q.ctx₁ i) _ (j + 1) _
        (treeStagesHalvingUpdate K (q.ctx₁ i) _ j (v₁ i) (n.x₁ i).1 (values i)) _ = _
      dsimp only
      rw [hr i hi, h.counts i hi]; rfl
    · intro i hi
      change treeStagesHalvingBody K (q.ctx₂ i) _ (j + 1) _
        (treeStagesHalvingUpdate K (q.ctx₂ i) _ j (v₂ i) (n.x₂ i).1 (values i)) _ = _
      dsimp only
      rw [hr i hi, h.counts i hi]; rfl
    · intro i hi
      change treeStagesHalvingProducts _ (j + 1)
        (treeStagesHalvingUpdate K (q.ctx₁ i) _ j (v₁ i) (n.x₁ i).1 (values i)) = _
      dsimp only
      rw [hr i hi, h.counts i hi]
    · intro i hi
      change treeStagesHalvingProducts _ (j + 1)
        (treeStagesHalvingUpdate K (q.ctx₂ i) _ j (v₂ i) (n.x₂ i).1 (values i)) = _
      dsimp only
      rw [hr i hi, h.counts i hi]
    · intro hist
      exact halvFold_rel K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ _ j v₁ v₂ _ _ hz r
        (rel (h.history_before recipe rnd δ sent live values hist))

end SavedRelAt

/-- Agreement of the actual tuple copies at every honest holder. -/
def EntryTuplesAgree (D : C.Coalition) (tuples : C.Party → List (Tuple C)) : Prop :=
  ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T → ∀ (k : ℕ) (t t' : Tuple C),
    (tuples i)[k]? = some t → (tuples j)[k]? = some t' →
      t.x T = t'.x T ∧ t.y T = t'.y T ∧ t.z T = t'.z T

/-- The entry implication concerns the caller's actual saved histories and tuples. -/
def EntryLink (c : Caller K circuits settings top tree D parameter openings) : Prop :=
  AllHistory D (fun i => nextLabel ((c.checkData K circuits settings top tree D parameter openings).st₁ i)) →
    EntryTuplesAgree D (c.checkData K circuits settings top tree D parameter openings).tuples₁

end Saved

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.halv_last_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halv_last_length

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.savedOffset_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms savedOffset_le

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.allHistory_of_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allHistory_of_append

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.isShamir_lagrangeFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isShamir_lagrangeFirst

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.coinOutput_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinOutput_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.sliceFold_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceFold_rel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.halvFold_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halvFold_rel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.lastSlice_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastSlice_rel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.commonHistory_extendMult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonHistory_extendMult

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.SavedRelAt.finishing_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SavedRelAt.finishing_length

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.SavedRelAt.address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SavedRelAt.address

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.SavedRelAt.closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SavedRelAt.closure

end ThresholdLeanXmssSecurity.TreeTwinSavedSchedule
