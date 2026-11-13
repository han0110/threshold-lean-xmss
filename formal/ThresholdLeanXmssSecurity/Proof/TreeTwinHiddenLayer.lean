import ThresholdLeanXmssSecurity.Proof.TreeTwinHiddenData
import ThresholdLeanXmssSecurity.Proof.TreeTwinKinds

/-!
# Hidden-term saved data through one multiplication layer

Affine gate inputs retain common per-term differences at held hidden terms.
Appending the reshared results extends each term's difference by the full
appended width, with zero coefficients away from the lacked term. The saved
list lengths, tuple count/mode clauses and single-pivot z relation are preserved
under the original alignment, mode and product-link hypotheses.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinHiddenLayer
open TreeTwinHiddenData

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

-- Port of TreeTwinKinds.treeTwin_layer_shift with a separate difference at each hidden term.
theorem layer_shift (D : C.Coalition) (i : C.Party) (circs : List Circuit) (layer : ℕ)
    (select : Affine × Affine → Affine) (publicTerm : C.Term)
    (wires₁ wires₂ : List (C.Term → List Bit)) (differences : ℕ → C.Term → List Bit)
    (length : wires₂.length = wires₁.length)
    (outside : ∀ k, wires₁.length ≤ k → ∀ T, differences k T = [])
    (related : ∀ k w₁ w₂, wires₁[k]? = some w₁ → wires₂[k]? = some w₂ →
      HiddenWireRel D i (differences k) w₁ w₂) :
    (fun T g => match (gatesAt circs layer)[g]? with
      | some (k, ab) => (select ab).share (wires₂.getD k fun _ => []) publicTerm T | none => 0) =
    hiddenShift D i (gatesAt circs layer).length (fun T => treeTwinLayerShift circs layer select (fun k => differences k T))
      (fun T g => match (gatesAt circs layer)[g]? with
        | some (k, ab) => (select ab).share (wires₁.getD k fun _ => []) publicTerm T | none => 0) := by
  funext T g
  simp only [hiddenShift, treeTwinLayerShift]
  cases hg : (gatesAt circs layer)[g]? with
  | none => simp
  | some gate =>
    obtain ⟨k, ab⟩ := gate
    have glt : g < (gatesAt circs layer).length := (List.getElem?_eq_some_iff.1 hg).1
    simp only [Affine.share, glt, true_and]
    by_cases hk : k < wires₁.length
    · have h₁ : wires₁[k]? = some wires₁[k] := List.getElem?_eq_getElem hk
      have h₂ : wires₂[k]? = some wires₂[k] := List.getElem?_eq_getElem (length ▸ hk)
      have rel := related k _ _ h₁ h₂ T
      simp only [List.getD_eq_getElem?_getD, h₁, h₂, Option.getD_some]
      by_cases held : i ∈ C.holders T ∧ ¬ KnownTo D.1 T
      · rw [if_pos held] at rel
        rw [if_pos held, rel.2, treeTwin_zipWith_sum _ _ rel.1]
        abel
      · rw [if_neg held] at rel
        rw [if_neg held, rel, add_zero]
    · have h₁ : wires₁[k]? = none := List.getElem?_eq_none (by omega)
      have h₂ : wires₂[k]? = none := List.getElem?_eq_none (by omega)
      simp only [List.getD_eq_getElem?_getD, h₁, h₂, Option.getD_none, outside k (by omega) T]
      simp

-- Port of TreeTwinKinds.treeTwin_appendLayer_rel; nonpivot hidden terms append zero coefficients.
theorem appendLayer_rel (D : C.Coalition) (i : C.Party) (circs : List Circuit) (layer : ℕ)
    (wires₁ wires₂ : List (C.Term → List Bit)) (differences : ℕ → C.Term → List Bit)
    (z₁ z₂ : Shares C Bit) (shift : ℕ → Bit)
    (related : ∀ k w₁ w₂, wires₁[k]? = some w₁ → wires₂[k]? = some w₂ →
      HiddenWireRel D i (differences k) w₁ w₂)
    (shifted : z₂ = treeSimHeldShift D i (gatesAt circs layer).length shift z₁) :
    ∀ k w₁ w₂, (appendLayer circs layer wires₁ z₁)[k]? = some w₁ →
      (appendLayer circs layer wires₂ z₂)[k]? = some w₂ →
      HiddenWireRel D i (fun T => differences k T ++ treeTwinAppended circs layer k
        (fun g => if lackedTerm D.1 = some T then shift g else 0)) w₁ w₂ := by
  intro k w₁ w₂ h₁ h₂
  rw [treeTwin_appendLayer_getElem?] at h₁ h₂
  obtain ⟨v₁, hv₁, rfl⟩ := Option.map_eq_some_iff.1 h₁
  obtain ⟨v₂, hv₂, rfl⟩ := Option.map_eq_some_iff.1 h₂
  have rel := related k v₁ v₂ hv₁ hv₂
  intro T
  have relT := rel T
  have entries : ∀ x ∈ (gatesAt circs layer).zipIdx.filter (·.1.1 = k),
      x.2 < (gatesAt circs layer).length := by
    intro x hx
    have := (List.mem_filter.1 hx).1
    have := (List.mem_zipIdx this).2.1
    omega
  beta_reduce
  by_cases held : i ∈ C.holders T ∧ ¬ KnownTo D.1 T
  · rw [if_pos held] at relT ⊢
    refine ⟨by simp [treeTwinAppended, relT.1], ?_⟩
    rw [relT.2, List.zipWith_append relT.1]
    congr 1
    simp only [treeTwinAppended, shifted, treeSimHeldShift, List.zipWith_map, List.zipWith_self]
    refine List.map_congr_left fun x hx => ?_
    by_cases pivot : lackedTerm D.1 = some T <;> simp [held.1, pivot, entries x hx]
  · rw [if_neg held] at relT ⊢
    rw [relT]
    congr 1
    simp only [treeTwinAppended, shifted, treeSimHeldShift]
    refine List.map_congr_left fun x _ => ?_
    rw [if_neg (fun h => held ⟨h.1, main_lacked_unknown D T h.2.2⟩), add_zero]

-- Port of TreeTwinKinds.treeTwinRunData_layer with the same alignment and reshared-product premises.
theorem runData_layer (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (circs : List Circuit) (layer : ℕ) (mode₁ mode₂ : C.Party → ReshareMode)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)) (z₁ z₂ : C.Party → Shares C Bit)
    (data : HiddenRunData K D ctx₁ ctx₂ p₁ p₂)
    (wiresAligned : ∀ i j, i ∉ D.1 → j ∉ D.1 → (p₁ i).1.length = (p₁ j).1.length)
    (tuplesAligned : ∀ i j, i ∉ D.1 → j ∉ D.1 → (p₁ i).2.length = (p₁ j).2.length)
    (modes : ∀ i, i ∉ D.1 → mode₂ i = mode₁ i)
    (shifted : ∀ i, i ∉ D.1 → z₂ i = treeSimHeldShift D i (gatesAt circs layer).length
      (treeTwinProductShift K D ctx₁ ctx₂ circs layer p₁ p₂) (z₁ i)) :
    HiddenRunData K D ctx₁ ctx₂ (fun i => treeTwinLayerShares K circs layer (mode₁ i) (p₁ i) (z₁ i))
      (fun i => treeTwinLayerShares K circs layer (mode₂ i) (p₂ i) (z₂ i)) := by
  obtain ⟨lengths, sharings, tuples⟩ := data
  obtain ⟨L, hL⟩ := treeTwin_common_length D (fun i => (p₁ i).1.length) wiresAligned
  obtain ⟨N, hN⟩ := treeTwin_common_length D (fun i => (p₁ i).2.length) tuplesAligned
  choose differences hdifferences using sharings
  let inside : ℕ → C.Term → List Bit := fun k T => if k < L then differences k T else []
  have insideRel : ∀ i, i ∉ D.1 → ∀ k w₁ w₂, (p₁ i).1[k]? = some w₁ → (p₂ i).1[k]? = some w₂ →
      HiddenWireRel D i (inside k) w₁ w₂ := by
    intro i hi k w₁ w₂ h₁ h₂
    have hk : k < L := hL i hi ▸ (List.getElem?_eq_some_iff.1 h₁).1
    simp only [inside, if_pos hk]
    exact hdifferences k i hi w₁ w₂ h₁ h₂
  have insideOut : ∀ i, i ∉ D.1 → ∀ k, (p₁ i).1.length ≤ k → ∀ T, inside k T = [] := by
    intro i hi k hk T
    simp only [inside, if_neg (by rw [← hL i hi]; omega : ¬ k < L)]
  refine ⟨fun i hi => ?_, fun k => ⟨fun T => inside k T ++ treeTwinAppended circs layer k
    (fun g => if lackedTerm D.1 = some T then
      treeTwinProductShift K D ctx₁ ctx₂ circs layer p₁ p₂ g else 0), fun i hi w₁ w₂ h₁ h₂ => ?_⟩, fun k => ?_⟩
  · simp [treeTwinLayerShares, treeTwin_appendLayer_length, (lengths i hi).1, (lengths i hi).2]
  · exact appendLayer_rel D i circs layer (p₁ i).1 (p₂ i).1 inside (z₁ i) (z₂ i) _
      (insideRel i hi) (shifted i hi) k w₁ w₂ h₁ h₂
  · have length₂ : ∀ j, j ∉ D.1 → (p₂ j).2.length = N := fun j hj => (lengths j hj).2.trans (hN j hj)
    rcases lt_trichotomy k N with hk | rfl | hk
    · have old₁ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₁ j) (p₁ j) (z₁ j)).2[k]? = (p₁ j).2[k]? :=
        fun j hj => List.getElem?_append_left (by rw [hN j hj]; exact hk)
      have old₂ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₂ j) (p₂ j) (z₂ j)).2[k]? = (p₂ j).2[k]? :=
        fun j hj => List.getElem?_append_left (by rw [length₂ j hj]; exact hk)
      obtain ⟨dx, dy, old⟩ := tuples k
      refine ⟨dx, dy, fun i hi t₁ t₂ h₁ h₂ => ?_⟩
      obtain ⟨count, mode, x, y, z⟩ := old i hi t₁ t₂ ((old₁ i hi).symm.trans h₁) ((old₂ i hi).symm.trans h₂)
      refine ⟨count, mode, x, y, ?_⟩
      rw [z]
      congr 1
      funext g
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [old₁ j (Finset.mem_filter.1 hj).2, old₂ j (Finset.mem_filter.1 hj).2]
    · have new₁ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₁ j) (p₁ j) (z₁ j)).2[k]? =
            some ⟨layerX K circs layer (p₁ j).1, layerY K circs layer (p₁ j).1, z₁ j,
              (gatesAt circs layer).length, mode₁ j⟩ := by
        intro j hj
        simp [treeTwinLayerShares, hN j hj]
      have new₂ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₂ j) (p₂ j) (z₂ j)).2[k]? =
            some ⟨layerX K circs layer (p₂ j).1, layerY K circs layer (p₂ j).1, z₂ j,
              (gatesAt circs layer).length, mode₂ j⟩ := by
        intro j hj
        simp [treeTwinLayerShares, length₂ j hj]
      refine ⟨(fun T => treeTwinLayerShift circs layer Prod.fst (fun k => inside k T)),
        (fun T => treeTwinLayerShift circs layer Prod.snd (fun k => inside k T)),
        fun i hi t₁ t₂ h₁ h₂ => ?_⟩
      rw [new₁ i hi] at h₁
      rw [new₂ i hi] at h₂
      cases h₁
      cases h₂
      refine ⟨rfl, modes i hi, layer_shift D i circs layer Prod.fst K.publicTerm (p₁ i).1 (p₂ i).1
        inside (lengths i hi).1 (insideOut i hi) (insideRel i hi),
        layer_shift D i circs layer Prod.snd K.publicTerm (p₁ i).1 (p₂ i).1
        inside (lengths i hi).1 (insideOut i hi) (insideRel i hi), ?_⟩
      rw [shifted i hi]
      dsimp only
      congr 1
      funext g
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [new₁ j (Finset.mem_filter.1 hj).2, new₂ j (Finset.mem_filter.1 hj).2]
      rfl
    · refine ⟨0, 0, fun i hi t₁ t₂ h₁ h₂ => ?_⟩
      have none : (treeTwinLayerShares K circs layer (mode₁ i) (p₁ i) (z₁ i)).2[k]? = none :=
        List.getElem?_eq_none (by simp [treeTwinLayerShares, hN i hi]; omega)
      rw [none] at h₁
      cases h₁

-- Port of TreeTwinKinds.treeTwinRunData_exit with the original TreeTwinLayerLink.
theorem runData_exit (D : C.Coalition) (d : TreeSimCollectorData K D)
    (ctx₁ ctx₂ : C.Party → Context C) (gadgets₁ gadgets₂ : C.Party → RunGadgets C E RealSpec)
    (circs : List Circuit) (layer : ℕ) (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (data : HiddenRunData K D ctx₁ ctx₂ p₁ p₂)
    (link : TreeTwinLayerLink K D d ctx₁ ctx₂ gadgets₁ gadgets₂ circs layer p₁ p₂)
    (x₁ x₂ : C.Party → Shares C Bit × RunState C)
    (exits : ∀ i, i ∉ D.1 → (x₂ i).1 = treeSimHeldShift D i d.count
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g) (x₁ i).1) :
    HiddenRunData K D ctx₁ ctx₂
      (fun i => treeTwinLayerShares K circs layer (gadgets₁ i).mode (p₁ i) (x₁ i).1)
      (fun i => treeTwinLayerShares K circs layer (gadgets₂ i).mode (p₂ i) (x₂ i).1) := by
  obtain ⟨count, v₁, v₂, modes, wires, tuples⟩ := link
  refine runData_layer K D ctx₁ ctx₂ circs layer _ _ p₁ p₂ _ _ data wires tuples modes
    fun i hi => ?_
  rw [exits i hi, count]
  congr 1
  funext g
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Pi.sub_apply, Pi.sub_apply, v₁ j (Finset.mem_filter.1 hj).2, v₂ j (Finset.mem_filter.1 hj).2]

-- Port of TreeTwinLater.treeTwinRunData_counts_modes; its proof reads only counts, modes and lengths.
theorem counts_modes (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (data : HiddenRunData K D ctx₁ ctx₂ p₁ p₂) (i : C.Party) (hi : i ∉ D.1) :
    (p₂ i).2.map (·.count) = (p₁ i).2.map (·.count) ∧
      (p₂ i).2.map (·.mode) = (p₁ i).2.map (·.mode) := by
  have length := (data.1 i hi).2
  have entry (k : ℕ) (hk₂ : k < (p₂ i).2.length) (hk₁ : k < (p₁ i).2.length) :
      ((p₂ i).2[k]).count = ((p₁ i).2[k]).count ∧
        ((p₂ i).2[k]).mode = ((p₁ i).2[k]).mode := by
    obtain ⟨dx, dy, h⟩ := data.2.2 k
    have h' := h i hi _ _ (List.getElem?_eq_getElem hk₁) (List.getElem?_eq_getElem hk₂)
    exact ⟨h'.1, h'.2.1⟩
  constructor
  · apply List.ext_getElem (by simpa)
    intro k hk₂ hk₁
    simpa using (entry k (by simpa using hk₂) (by simpa using hk₁)).1
  · apply List.ext_getElem (by simpa)
    intro k hk₂ hk₁
    simpa using (entry k (by simpa using hk₂) (by simpa using hk₁)).2

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayer.layer_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layer_shift

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayer.appendLayer_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms appendLayer_rel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayer.runData_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runData_layer

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayer.runData_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runData_exit

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenLayer.counts_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counts_modes

end ThresholdLeanXmssSecurity.TreeTwinHiddenLayer
