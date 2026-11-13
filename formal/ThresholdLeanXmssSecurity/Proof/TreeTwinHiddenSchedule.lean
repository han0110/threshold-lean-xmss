import ThresholdLeanXmssSecurity.Proof.TreeTwinHiddenEntry

/-!
# Hidden-term shapes through the saved check schedule

Slice and halving updates preserve common coefficients on every hidden term,
without history agreement. The claim and ExtendMult output shifts retain the
original lacked-term form. The saved relation keeps one actual caller and
phase for both these unconditional shapes and the conditional check relation.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinLocalSum TreeTwinHiddenEntry
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- Conversion of one common coefficient for each hidden term. -/
def hiddenShare (D : C.Coalition) (i : C.Party) (a : C.Term → E) : E :=
  conv K (localContext i) (fun T _ => if KnownTo D.1 T then 0 else a T) 0

/-- The A/B differences have common hidden-term coefficients; the claim stays single-pivot. -/
def HiddenHalvShape (D : C.Coalition) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E) : Prop :=
  ∃ (dA dB : C.Term → ℕ → E) (e : E),
    (∀ i, i ∉ D.1 → ∀ k, (v₁ i).1 k - (v₂ i).1 k = hiddenShare K D i (fun T => dA T k)) ∧
    (∀ i, i ∉ D.1 → ∀ k, (v₁ i).2.1 k - (v₂ i).2.1 k = hiddenShare K D i (fun T => dB T k)) ∧
    (∀ i, i ∉ D.1 → (v₁ i).2.2 - (v₂ i).2.2 = lackedShare K D i e)

-- Ports of TreeTwinSavedSchedule.lackedShare_add/mul to term-indexed coefficients.
theorem hiddenShare_add (D : C.Coalition) (i : C.Party) (x y : C.Term → E) :
    hiddenShare K D i (fun T => x T + y T) = hiddenShare K D i x + hiddenShare K D i y := by
  simp only [hiddenShare, conv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T ht
  split_ifs <;> ring

theorem hiddenShare_mul (D : C.Coalition) (i : C.Party) (a : E) (x : C.Term → E) :
    hiddenShare K D i (fun T => a * x T) = a * hiddenShare K D i x := by
  simp only [hiddenShare, conv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T ht
  split_ifs <;> ring

-- Ports of TreeTwinSavedSchedule.sliceFold_shape through lastSlice_shape.
/-- The slice shape needs no holder agreement. -/
theorem sliceFold_shape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (τ : List E) (count j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesSliceProducts τ count j (v₁ i))
      (fun i => treeStagesSliceProducts τ count j (v₂ i)) out₁ out₂) (r : E)
    (h : HiddenSliceShape K D v₁ v₂) :
    HiddenSliceShape K D (fun i => treeStagesSliceUpdate K (ctx₁ i) τ count j (v₁ i) (out₁ i) r)
      (fun i => treeStagesSliceUpdate K (ctx₂ i) τ count j (v₂ i) (out₂ i) r) := by
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  let d := fun g => ∑ i ∈ univ.filter (· ∉ D.1),
    (contextProductValues K (ctx₁ i) (treeStagesSliceProducts τ count j (v₁ i)) g -
      contextProductValues K (ctx₂ i) (treeStagesSliceProducts τ count j (v₂ i)) g)
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  refine ⟨fun T k => dx T k + r * (dx T k + dx T (k + half)),
    fun T k => dy T k + r * (dy T k + dy T (k + half)),
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
    (h : HiddenHalvShape K D v₁ v₂) :
    HiddenHalvShape K D (fun i => treeStagesHalvingUpdate K (ctx₁ i) width j (v₁ i) (out₁ i) r)
      (fun i => treeStagesHalvingUpdate K (ctx₂ i) width j (v₂ i) (out₂ i) r) := by
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  let d := fun g => ∑ i ∈ univ.filter (· ∉ D.1),
    (contextProductValues K (ctx₁ i) (treeStagesHalvingProducts width j (v₁ i)) g -
      contextProductValues K (ctx₂ i) (treeStagesHalvingProducts width j (v₂ i)) g)
  let len := halvedLength^[j] width
  let half := halvedLength len
  refine ⟨fun T k => dx T k + r * (dx T k + if k + half < len then dx T (k + half) else 0),
    fun T k => dy T k + r * (dy T k + if k + half < len then dy T (k + half) else 0),
    d 0 + r * (e + d 1) + r ^ 2 * d 1, ?_, ?_, ?_⟩
  · intro i hi k
    dsimp only [treeStagesHalvingUpdate]
    split_ifs with hb
    · simp only [hiddenShare_add, hiddenShare_mul]
      linear_combination (1 + r) * hx i hi k + r * hx i hi (k + half)
    · simp only [add_zero, hiddenShare_add, hiddenShare_mul]
      linear_combination (1 + r) * hx i hi k
  · intro i hi k
    dsimp only [treeStagesHalvingUpdate]
    split_ifs with hb
    · simp only [hiddenShare_add, hiddenShare_mul]
      linear_combination (1 + r) * hy i hi k + r * hy i hi (k + half)
    · simp only [add_zero, hiddenShare_add, hiddenShare_mul]
      linear_combination (1 + r) * hy i hi k
  · intro i hi
    have h0 := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ hz i hi 0 (by omega)
    have h1 := convShift_sub K D ctx₁ ctx₂ self₁ self₂ _ _ out₁ out₂ hz i hi 1 (by omega)
    change _ = lackedShare K D i (d 0) at h0
    change _ = lackedShare K D i (d 1) at h1
    dsimp only [treeStagesHalvingUpdate]
    simp only [lackedShare_add, lackedShare_mul]
    linear_combination h0 + r * he i hi + (r + r ^ 2) * h1

/-- Converting held replicated shares preserves their common hidden-term shape. -/
theorem sliceShape_to_halvShape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E) (h : HiddenSliceShape K D v₁ v₂) :
    HiddenHalvShape K D (fun i => (conv K (ctx₁ i) (v₁ i).1, conv K (ctx₁ i) (v₁ i).2.1, (v₁ i).2.2))
      (fun i => (conv K (ctx₂ i) (v₂ i).1, conv K (ctx₂ i) (v₂ i).2.1, (v₂ i).2.2)) := by
  letI : CharP E 2 := charTwo
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  refine ⟨dx, dy, e, ?_, ?_, he⟩
  · intro i hi k
    dsimp only
    rw [conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)]
    rw [conv_sub_const]
    unfold hiddenShare
    apply conv_congr
    intro T ht
    dsimp only
    rw [hx i hi T k]
    by_cases known : KnownTo D.1 T <;> simp [ht, known, CharTwo.neg_eq]
  · intro i hi k
    dsimp only
    rw [conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)]
    rw [conv_sub_const]
    unfold hiddenShare
    apply conv_congr
    intro T ht
    dsimp only
    rw [hy i hi T k]
    by_cases known : KnownTo D.1 T <;> simp [ht, known, CharTwo.neg_eq]

/-- The conversion at the slice boundary has the halving shape without an agreement premise. -/
theorem lastSlice_shape (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (τ : List E) (count j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (out₁ out₂ : C.Party → Shares C E)
    (hz : OutputShift K D ctx₁ ctx₂ (fun i => treeStagesSliceProducts τ count j (v₁ i))
      (fun i => treeStagesSliceProducts τ count j (v₂ i)) out₁ out₂) (r : E)
    (h : HiddenSliceShape K D v₁ v₂) :
    HiddenHalvShape K D (fun i => treeTwinSliceShamir K (ctx₁ i) τ count j (v₁ i) (out₁ i) r)
      (fun i => treeTwinSliceShamir K (ctx₂ i) τ count j (v₂ i) (out₂ i) r) := by
  exact sliceShape_to_halvShape K D ctx₁ ctx₂ self₁ self₂ _ _ (sliceFold_shape K D ctx₁ ctx₂ self₁ self₂ τ count j v₁ v₂ out₁ out₂ hz r h)

-- Port of TreeTwinSavedSchedule.HalvShape.congr_honest and its same-witness definitions.
theorem HiddenHalvShape.congr_honest (D : C.Coalition)
    (v₁ v₂ u₁ u₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (h : HiddenHalvShape K D v₁ v₂) (h₁ : ∀ i, i ∉ D.1 → v₁ i = u₁ i)
    (h₂ : ∀ i, i ∉ D.1 → v₂ i = u₂ i) : HiddenHalvShape K D u₁ u₂ := by
  obtain ⟨dx, dy, e, hx, hy, he⟩ := h
  refine ⟨dx, dy, e, ?_, ?_, ?_⟩
  · intro i hi k
    rw [← h₁ i hi, ← h₂ i hi]
    exact hx i hi k
  · intro i hi k
    rw [← h₁ i hi, ← h₂ i hi]
    exact hy i hi k
  · intro i hi
    rw [← h₁ i hi, ← h₂ i hi]
    exact he i hi

section Saved
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (parameter : PublicParameter) (openings : List (List (List Bit)))

structure HiddenSavedWitness where
  caller : HiddenCaller K circuits settings top tree D parameter openings
  phase : SavedPhase C E

def HiddenSavedState (q : TreeStagesExtendMultChallenge K D)
    (w : HiddenSavedWitness K circuits settings top tree D parameter openings) : Prop :=
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
      HiddenSliceShape K D v₁ v₂ ∧
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
      HiddenHalvShape K D v₁ v₂ ∧
      (AllHistory D q.st₁ → HalvRel K D (halvedLength^[j] (sliceWidth count))
        (fun i => (v₁ i).1) (fun i => (v₁ i).2.1) (fun i => (v₂ i).1) (fun i => (v₂ i).2.1)
        (fun i => (v₁ i).2.2) (fun i => (v₂ i).2.2))

/-- One caller and one phase supply every saved-state condition. -/
structure HiddenSavedRelAt (q : TreeStagesExtendMultChallenge K D)
    (w : HiddenSavedWitness K circuits settings top tree D parameter openings) : Prop where
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
  state : HiddenSavedState K circuits settings top tree D parameter openings q w

def SavedRelHS (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, HiddenSavedRelAt K circuits settings top tree D parameter openings q w

end Saved

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.hiddenShare_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenShare_add

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.hiddenShare_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenShare_mul

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.sliceFold_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceFold_shape

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.halvFold_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halvFold_shape

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.sliceShape_to_halvShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceShape_to_halvShape

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.lastSlice_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastSlice_shape

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule.HiddenHalvShape.congr_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HiddenHalvShape.congr_honest

end ThresholdLeanXmssSecurity.TreeTwinHiddenSchedule
