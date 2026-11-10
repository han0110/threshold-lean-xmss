import ThresholdLeanXmssSecurity.Proof.CheckFinish
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The last stages of the check proof

`CheckSoundStage` (step 2) and `CheckSplitStage` (steps 3 and 4) of `Proof/CheckCore.lean`, and from
them `MultVerifyStatement` through `multVerifyStatementFull`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

section Final

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- `MultVerifyStatement` from the two open stages. -/
theorem multVerifyOfStages (prims : Primitives) (K : Constants C E)
    (hsound : CheckSoundStage prims K) (hsplit : CheckSplitStage prims K) : MultVerifyStatement prims K :=
  multVerifyStatementFull prims K hsound hsplit

end Final

/-! ## A route for the split case

When the honest copies disagree, `F_multVerify` rejects, so the ideal run outputs nothing to the
honest operators. `CheckSplitDistance` bounds the real run against the ideal run by `checkHashError`
alone, with one bad event. Off the bad event the coupling of the real run with the run on
`canonicalDummyTuples` keeps the known terms equal at each honest operator, and every honest operator
aborts at `compareDigests` in both runs. The bad event is a hit of a hidden digest point or a
collision of the two honest history or digest points of a split term. The collision is a birthday
event, since a corrupt operator chooses the offsets that each honest holder appends to its history
(`multFinish`). It replaces `CheckSplitStage` in the assembly of `checkCoreDistance`. -/

section SplitRoute

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- Steps 3 and 4 with one bad event: with split copies, the real run and the ideal run differ by at
most `checkHashError`. -/
def CheckSplitDistance (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (z : Aux) (Z : Distinguisher C A.State Unit) (q : ℕ),
    TupleInputs K counts D x → IsQueryBounded A Z (checkRounds counts.sum) q →
    counts.sum ≠ 0 → q < 2 ^ 128 →
    ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    |localAccepts prims (checkRealLocal K (checkRounds counts.sum) D A x z Z) -
      localAccepts prims (checkIdealLocal K (checkRounds counts.sum) D A x z Z)| ≤
      checkHashError C counts.sum q

/-- `CheckSplitStage` gives `CheckSplitDistance`. -/
theorem checkSplitDistance_of_stage (prims : Primitives) (K : Constants C E) (h : CheckSplitStage prims K) :
    CheckSplitDistance prims K :=
  fun counts D A x z Z q hx hq hpos hq128 hagree => (h counts D A x z Z q hx hq hpos hq128 hagree).abs_sub_le

/-- `CheckCoreDistance` from the soundness stage and the split distance, with `checkCoupleStage`. -/
theorem checkCoreDistanceSplit (prims : Primitives) (K : Constants C E) (hsound : CheckSoundStage prims K)
    (hsplit : CheckSplitDistance prims K) : CheckCoreDistance prims K := by
  intro counts D A x z Z q hx hq hpos hq128
  have hE := checkErrorOf_nonneg K (coins counts.sum) (halvings counts.sum) q
  by_cases hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))
  · have hc := checkCoupleStage prims K counts D A x z Z q hx hq hpos hq128 hagree
    have hcl := coupleHashError_le (C := C) counts.sum q
    by_cases hacc : (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2 = true
    · rw [← checkMasked_eq_real_of_accept prims K _ D A x z Z hacc]
      linarith
    · have hm := checkReal_masked_le prims K (checkRounds counts.sum) D A x z Z
      have hs := hsound counts D A x z Z q hx hq hpos hq128 hagree (by simpa using hacc)
      have hsum := soundHash_add_coupleHash_le (C := C) counts.sum q
      have htri := abs_sub_le (localAccepts prims (checkRealLocal K (checkRounds counts.sum) D A x z Z))
        (localAccepts prims (checkMaskedLocal K (checkRounds counts.sum) D A x z Z))
        (localAccepts prims (checkIdealLocal K (checkRounds counts.sum) D A x z Z))
      linarith
  · have h := hsplit counts D A x z Z q hx hq hpos hq128 hagree
    linarith

/-- The relation of the two slice states with split copies: each honest operator holds the same
known terms on the two sides, and on each side the honest holders of a hidden term agree. -/
def SplitSliceRel (D : C.Coalition) (xsR ysR xsD ysD : C.Party → Shares C E) : Prop :=
  (∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → xsR i T = xsD i T ∧ ysR i T = ysD i T) ∧
  ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    xsR i T = xsR j T ∧ ysR i T = ysR j T ∧ xsD i T = xsD j T ∧ ysD i T = ysD j T

/-- The leak of the multiplication of a slice step is the same on the two sides. -/
lemma splitSliceInputs_view (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ)
    (xsR ysR xsD ysD : C.Party → Shares C E) (hrel : SplitSliceRel D xsR ysR xsD ysD) :
    extendView K D.1 (sliceInputs D τ count j xsR ysR) = extendView K D.1 (sliceInputs D τ count j xsD ysD) := by
  have hsame := hrel.1
  apply extendView_eq_of_relation
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, _, ha⟩ := firstInput_honest D (fun i => sliceProducts (C := C) τ count j (xsR i) (ysR i))
    obtain ⟨b, _, hb⟩ := firstInput_honest D (fun i => sliceProducts (C := C) τ count j (xsD i) (ysD i))
    change (firstInput (fun i => if i ∈ D.1 then none else some (sliceProducts τ count j (xsR i) (ysR i)))).map
      Product.shape = (firstInput (fun i => if i ∈ D.1 then none else
        some (sliceProducts τ count j (xsD i) (ysD i)))).map Product.shape
    rw [ha, hb]
    rfl
  · intro g T hT i hiT
    by_cases hi : i ∈ D.1
    · simp [sliceInputs, hi]
    · obtain ⟨e1, e2⟩ := hsame i hi T hT hiT
      simp only [sliceInputs, hi, if_false, Option.bind_some]
      rcases g with _ | _ | g
      · simp [sliceProducts, Product.replicatedParts, e1]
      · simp [sliceProducts, Product.replicatedParts, e1]
      · simp [sliceProducts]
  · intro g T hT i hiT
    by_cases hi : i ∈ D.1
    · simp [sliceInputs, hi]
    · obtain ⟨e1, e2⟩ := hsame i hi T hT hiT
      simp only [sliceInputs, hi, if_false, Option.bind_some]
      rcases g with _ | _ | g
      · simp [sliceProducts, Product.replicatedParts, e2]
      · simp [sliceProducts, Product.replicatedParts, e2]
      · simp [sliceProducts]
  · intro g k
    convert ShamirDifference.refl K D (fun _ => (0 : E)) using 2 <;>
    · rename_i i
      by_cases hi : i ∈ D.1
      · simp [sliceInputs, hi]
      · simp only [sliceInputs, hi, if_false, Option.bind_some]
        rcases g with _ | _ | g <;> simp [sliceProducts, Product.shamirParts]
  · intro g k
    convert ShamirDifference.refl K D (fun _ => (0 : E)) using 2 <;>
    · rename_i i
      by_cases hi : i ∈ D.1
      · simp [sliceInputs, hi]
      · simp only [sliceInputs, hi, if_false, Option.bind_some]
        rcases g with _ | _ | g <;> simp [sliceProducts, Product.shamirParts]

/-- A slice step keeps the split relation. -/
lemma splitSliceRel_fold (D : C.Coalition) (count j : ℕ) (r : E) (xsR ysR xsD ysD : C.Party → Shares C E)
    (h : SplitSliceRel D xsR ysR xsD ysD) :
    SplitSliceRel D (fun i => sliceFold count j r (xsR i)) (fun i => sliceFold count j r (ysR i))
      (fun i => sliceFold count j r (xsD i)) (fun i => sliceFold count j r (ysD i)) := by
  refine ⟨fun i hi T hT hiT => ?_, fun T hT i j' hi hj' hiT hjT => ?_⟩
  · obtain ⟨e1, e2⟩ := h.1 i hi T hT hiT
    refine ⟨?_, ?_⟩ <;> funext k <;> simp only [sliceFold, e1, e2]
  · obtain ⟨e1, e2, e3, e4⟩ := h.2 T hT i j' hi hj' hiT hjT
    refine ⟨?_, ?_, ?_, ?_⟩ <;> funext k <;> simp only [sliceFold, e1, e2, e3, e4]

/-- The history relation after a slice step, for any honest views. -/
lemma splitSlice_hist {σ' : Type} (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ)
    (xsR ysR xsD ysD : C.Party → Shares C E) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2) :
    HistRel D tg (L + 1 + 1)
      (fun i => ⟨recordHistory K i (hsR i).history (sliceOut K D τ count j xsR ysR pa fresh i) 2,
        (hsR i).label + 1 + 1, (hsR i).tag⟩)
      (fun i => ⟨recordHistory K i (hsD i).history (sliceOut K D τ count j xsD ysD pa fresh i) 2,
        (hsD i).label + 1 + 1, (hsD i).tag⟩) := by
  obtain ⟨htagR, htagD, hknownHist, hcommonR, hcommonD⟩ := hh
  refine ⟨fun i hi => by simp [htagR i hi], fun i hi => by simp [htagD i hi], ?_, ?_, ?_⟩
  · intro T hT i hi hiT
    simp only [recordHistory, if_pos hiT, hknownHist T hT i hi hiT]
    unfold sliceOut
    rw [multFinish_known D 2 _ _ _ _ _ _ fresh i hi (hrec i hi) T hT]
  · intro T hT i j' hi hj' hiT hjT
    simp only [recordHistory, if_pos hiT, if_pos hjT, hcommonR T hT i j' hi hj' hiT hjT]
    unfold sliceOut
    rw [multFinish_unknown K D 2 _ _ _ _ fresh T hT i j' hi hj' (hrec i hi) (hrec j' hj') hiT hjT]
  · intro T hT i j' hi hj' hiT hjT
    simp only [recordHistory, if_pos hiT, if_pos hjT, hcommonD T hT i j' hi hj' hiT hjT]
    unfold sliceOut
    rw [multFinish_unknown K D 2 _ _ _ _ fresh T hT i j' hi hj' (hrec i hi) (hrec j' hj') hiT hjT]

/-- `MultVerifyStatement` from the soundness stage and the split distance. -/
theorem multVerifyOfSplitRoute (prims : Primitives) (K : Constants C E) (hsound : CheckSoundStage prims K)
    (hsplit : CheckSplitDistance prims K) : MultVerifyStatement prims K :=
  multVerifyStatementProof prims K (checkCoreDistanceSplit prims K hsound hsplit)

end SplitRoute

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.checkCoreDistanceSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.checkCoreDistanceSplit

/-- info: 'ThresholdLeanXmssSecurity.multVerifyOfSplitRoute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.multVerifyOfSplitRoute
