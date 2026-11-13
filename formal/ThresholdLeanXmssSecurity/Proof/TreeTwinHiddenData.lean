import ThresholdLeanXmssSecurity.Proof.TreeTwinOther
import ThresholdLeanXmssSecurity.Proof.TreeTwinHolderKeys

/-!
# Hidden-term saved input data

`HiddenRunData` permits common per-term differences at every held hidden input
term. Its saved-list lengths, tuple counts and modes, and single-pivot reshared
z clause are those of `TreeTwinRunData`. `cached_entry` establishes this relation
for the canonical cached inputs in the actual real and dummy setup contexts,
for every cache, job list, setup-row table and coalition.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeTwinHiddenData

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- A common term-indexed shift, restricted to held hidden terms and the tuple width. -/
def hiddenShift (D : C.Coalition) (i : C.Party) (count : ℕ)
    (difference : C.Term → ℕ → Bit) (v : Shares C Bit) : Shares C Bit := fun T g =>
  v T g + if i ∈ C.holders T ∧ g < count ∧ ¬ KnownTo D.1 T then difference T g else 0

/-- Input wire differences have the exact list length at each held hidden term. -/
def HiddenWireRel (D : C.Coalition) (i : C.Party) (difference : C.Term → List Bit)
    (h₁ h₂ : C.Term → List Bit) : Prop :=
  ∀ T, if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then
    (h₁ T).length = (difference T).length ∧
      h₂ T = List.zipWith (· + ·) (h₁ T) (difference T)
  else h₂ T = h₁ T

/-- Saved input data with hidden-term wire and x/y differences. The length,
count/mode and z clauses are verbatim from `TreeTwinRunData` in `TreeTwinOther.lean`. -/
def HiddenRunData (K : Constants C E) (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)) : Prop :=
  (∀ i, i ∉ D.1 → (p₂ i).1.length = (p₁ i).1.length ∧ (p₂ i).2.length = (p₁ i).2.length) ∧
  (∀ k : ℕ, ∃ difference : C.Term → List Bit, ∀ i, i ∉ D.1 → ∀ w₁ w₂, (p₁ i).1[k]? = some w₁ →
    (p₂ i).1[k]? = some w₂ → HiddenWireRel D i difference w₁ w₂) ∧
  (∀ k : ℕ, ∃ dx dy : C.Term → ℕ → Bit, ∀ i, i ∉ D.1 → ∀ t₁ t₂ : Tuple C, (p₁ i).2[k]? = some t₁ →
    (p₂ i).2[k]? = some t₂ →
    t₂.count = t₁.count ∧ t₂.mode = t₁.mode ∧
    t₂.x = hiddenShift D i t₁.count dx t₁.x ∧ t₂.y = hiddenShift D i t₁.count dy t₁.y ∧
    t₂.z = treeSimHeldShift D i t₁.count (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1),
      (((p₁ j).2[k]?.map fun t : Tuple C => mulRep K (ctx₁ j) t.x t.y g).getD 0 -
        ((p₂ j).2[k]?.map fun t : Tuple C => mulRep K (ctx₂ j) t.x t.y g).getD 0)) t₁.z)

/-- Adding the pointwise bit difference recovers the second list at equal lengths. -/
theorem zipWith_add_cancel (a b : List Bit) (length : a.length = b.length) :
    List.zipWith (· + ·) a (List.zipWith (· + ·) a b) = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at length
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at length
      simp only [List.zipWith_cons_cons, ← add_assoc, bit_add_self, zero_add, ih ys length]

/-- Each term's two input lists have equal length, so their bit sum is an exact shift. -/
theorem inputBits_difference (h : Query C → HashOutput) (seeds₁ seeds₂ : C.Term → HashOutput)
    (job : Job) (T : C.Term) :
    (inputBits h seeds₁ job T).length =
      (List.zipWith (· + ·) (inputBits h seeds₁ job T) (inputBits h seeds₂ job T)).length ∧
    inputBits h seeds₂ job T = List.zipWith (· + ·) (inputBits h seeds₁ job T)
      (List.zipWith (· + ·) (inputBits h seeds₁ job T) (inputBits h seeds₂ job T)) := by
  have length : (inputBits h seeds₁ job T).length = (inputBits h seeds₂ job T).length := by
    rw [length_inputBits, length_inputBits]
  exact ⟨by simp only [List.length_zipWith, length, min_self],
    (zipWith_add_cancel _ _ length).symm⟩

/-- The actual cached real/dummy input wires have a common difference at every hidden term. -/
theorem cached_inputs_hiddenWireRel (D : C.Coalition) (cache : HashCache C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (rows : C.Party → Option (PrssKeys C)) (job : Job) (i : C.Party) :
    HiddenWireRel D i
      (fun T => List.zipWith (· + ·)
        (inputBits (fun q => (cache q).getD 0) seeds job T)
        (inputBits (fun q => (cache q).getD 0)
          (fun T => if KnownTo D.1 T then seeds T else 0) job T))
      (treeStagesCachedInputs cache (TreeTwinHolderKeys.setupCtx parameter seeds pairs rows i) job)
      (treeStagesCachedInputs cache
        ⟨i, ⟨parameter, fun T => if KnownTo D.1 T then seeds T else 0, fun _ => 0⟩,
          TreeCheckWalkRecipe.setupKeys rows i⟩ job) := by
  intro T
  dsimp only
  by_cases held : i ∈ C.holders T
  · have real : treeStagesCachedInputs cache
        (TreeTwinHolderKeys.setupCtx parameter seeds pairs rows i) job T =
        inputBits (fun q => (cache q).getD 0) seeds job T := by
      simp only [treeStagesCachedInputs, TreeTwinHolderKeys.setupCtx, if_pos held]
      unfold inputBits
      dsimp only [dealtKeys]
      rw [if_pos held]
    rw [real]
    simp only [treeStagesCachedInputs, held, if_true, true_and]
    by_cases known : KnownTo D.1 T
    · simp only [known, not_true_eq_false, if_false]
      unfold inputBits
      dsimp only
      rw [if_pos known]
    · simp only [known, not_false_eq_true, if_true]
      exact inputBits_difference _ _ _ _ _
  · simp [treeStagesCachedInputs, TreeTwinHolderKeys.setupCtx, held]

/-- Canonical cached-input entry data for every cache and job list. -/
theorem cached_entry (K : Constants C E) (D : C.Coalition) (cache : HashCache C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (rows : C.Party → Option (PrssKeys C)) (jobs : List Job) :
    let ctx₁ := TreeTwinHolderKeys.setupCtx parameter seeds pairs rows
    let ctx₂ := fun i => (⟨i,
      ⟨parameter, fun T => if KnownTo D.1 T then seeds T else 0, fun _ => 0⟩,
      TreeCheckWalkRecipe.setupKeys rows i⟩ : Context C)
    HiddenRunData K D ctx₁ ctx₂
      (fun i => (jobs.map (treeStagesCachedInputs cache (ctx₁ i)), []))
      (fun i => (jobs.map (treeStagesCachedInputs cache (ctx₂ i)), [])) := by
  dsimp only
  refine ⟨fun i _ => ⟨by simp, rfl⟩, ?_, ?_⟩
  · intro k
    by_cases hk : k < jobs.length
    · refine ⟨fun T => List.zipWith (· + ·)
        (inputBits (fun q => (cache q).getD 0) seeds jobs[k] T)
        (inputBits (fun q => (cache q).getD 0)
          (fun T => if KnownTo D.1 T then seeds T else 0) jobs[k] T), ?_⟩
      intro i _ w₁ w₂ h₁ h₂
      simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
        Option.some.injEq] at h₁ h₂
      subst w₁
      subst w₂
      exact cached_inputs_hiddenWireRel D cache parameter seeds pairs rows jobs[k] i
    · refine ⟨fun _ => [], ?_⟩
      intro i _ w₁ w₂ h₁ _
      simp [List.getElem?_eq_none (Nat.le_of_not_gt hk)] at h₁
  · intro k
    refine ⟨0, 0, ?_⟩
    intro i _ t₁ t₂ h₁ _
    simp at h₁

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenData.zipWith_add_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zipWith_add_cancel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenData.inputBits_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inputBits_difference

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenData.cached_inputs_hiddenWireRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cached_inputs_hiddenWireRel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenData.cached_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cached_entry

end TreeTwinHiddenData
end ThresholdLeanXmssSecurity
