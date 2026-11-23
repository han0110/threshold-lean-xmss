module

public import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD

public section

/-! # Indexing lists related to `finRange` -/

namespace ThresholdLeanXmssSecurity.SigningOwnWalkBuild

/-- A relation on `List.finRange n` gives the corresponding relation at each index. -/
theorem forall₂_finRange {β : Type} {n : ℕ} {R : Fin n → β → Prop} {bs : List β} (d : β)
    (h : List.Forall₂ R (List.finRange n) bs) (k : Fin n) : R k (bs.getD k.val d) := by
  have hk : k.val < (List.finRange n).length := by simpa only [List.length_finRange] using k.isLt
  have hb : k.val < bs.length := h.length_eq ▸ hk
  rw [List.getD_eq_getElem _ _ hb]
  have hindex : (List.finRange n).get ⟨k.val, hk⟩ = k := List.getElem_finRange hk
  simpa only [hindex, List.get_eq_getElem] using h.get hk hb

end ThresholdLeanXmssSecurity.SigningOwnWalkBuild

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.forall₂_finRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.forall₂_finRange
