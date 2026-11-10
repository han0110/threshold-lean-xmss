import ThresholdLeanXmssSecurity.Proof.CheckSound
import ThresholdLeanXmssSecurity.Proof.Coupling
import VCVio.OracleComp.QueryTracking.Birthday

/-!
The split case of the multiplication check. Polynomial differences preserve
the shared adversarial views without assuming consistent known shares. A
shared ghost digest computation forces every honest operator to abort unless
its history/digest cache collides. The adaptive birthday bound and the two
salt-hiding bounds together fit `checkHashError`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra Bit E] [SampleableType E]

/-- The split relation gives polynomial differences without requiring either view to be Shamir. -/
lemma splitSliceRel_hiddenDifference (K : Constants C E) (D : C.Coalition)
    {xsR ysR xsD ysD : C.Party → Shares C E}
    (h : SplitSliceRel D xsR ysR xsD ysD) :
    HiddenDifference D xsR xsD ∧ HiddenDifference D ysR ysD := by
  constructor
  · exact HiddenDifference.of_consistent K D _ _
      (fun T hT i hi hiT => (h.1 i hi T hT hiT).1)
      (fun T hT i hiT j hjT hi hj => (h.2 T hT i j hi hj hiT hjT).1)
      (fun T hT i hiT j hjT hi hj => (h.2 T hT i j hi hj hiT hjT).2.2.1)
  · exact HiddenDifference.of_consistent K D _ _
      (fun T hT i hi hiT => (h.1 i hi T hT hiT).2)
      (fun T hT i hiT j hjT hi hj => (h.2 T hT i j hi hj hiT hjT).2.1)
      (fun T hT i hiT j hjT hi hj => (h.2 T hT i j hi hj hiT hjT).2.2.2)

/-- Only differences are polynomial in the split case. -/
def SplitHalvRel (K : Constants C E) (D : C.Coalition)
    (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E) : Prop :=
  (∀ k, ShamirDifference K D (fun i => AR i k) (fun i => AD i k)) ∧
  (∀ k, ShamirDifference K D (fun i => BR i k) (fun i => BD i k)) ∧
  ShamirDifference K D DR DD

lemma splitSliceRel_halvRel (K : Constants C E) (D : C.Coalition)
    {xsR ysR xsD ysD : C.Party → Shares C E} {DR DD : C.Party → E}
    (h : SplitSliceRel D xsR ysR xsD ysD) (hd : ShamirDifference K D DR DD) :
    SplitHalvRel K D (fun i => conv K (localContext i) (xsR i))
      (fun i => conv K (localContext i) (ysR i))
      (fun i => conv K (localContext i) (xsD i))
      (fun i => conv K (localContext i) (ysD i)) DR DD := by
  obtain ⟨hx, hy⟩ := splitSliceRel_hiddenDifference K D h
  exact ⟨fun k => hx.conv K D k, fun k => hy.conv K D k, hd⟩

lemma ShamirDifference.add_split (K : Constants C E) (D : C.Coalition)
    {a b c d : C.Party → E} (h : ShamirDifference K D a b)
    (h' : ShamirDifference K D c d) :
    ShamirDifference K D (fun i => a i + c i) (fun i => b i + d i) := by
  simpa only [one_mul] using h.lin K D h' 1 1

lemma ShamirDifference.scale_split (K : Constants C E) (D : C.Coalition)
    {a b : C.Party → E} (h : ShamirDifference K D a b) (r : E) :
    ShamirDifference K D (fun i => r * a i) (fun i => r * b i) := by
  simpa only [zero_mul, add_zero] using h.lin K D h r 0

lemma splitHalvRel_inputs_view (K : Constants C E) (D : C.Coalition) (len : ℕ)
    {AR BR AD BD : C.Party → ℕ → E} {DR DD : C.Party → E}
    (h : SplitHalvRel K D AR BR AD BD DR DD) :
    extendView K D.1 (halvInputs D len AR BR) =
      extendView K D.1 (halvInputs D len AD BD) := by
  apply extendView_eq_of_relation
  have hs : ∀ (X : C.Party → ℕ → E), halvInputs D len X =
      fun Y => shamirPairInputs D X Y
        (fun i k => X i k + (if k + halvedLength len < len then X i (k + halvedLength len) else 0))
        (fun i k => Y i k + (if k + halvedLength len < len then Y i (k + halvedLength len) else 0))
        (halvedLength len) (halvedLength len) := by
    intro X; funext Y i; rfl
  rw [hs AR, hs AD]
  apply shamirPair_viewRelation K D _ _ _ _ _ _ _ _ _ _ h.1 h.2.1
  · intro k
    split_ifs
    · exact (h.1 k).add_split K D (h.1 _)
    · simpa only [add_zero] using h.1 k
  · intro k
    split_ifs
    · exact (h.2.1 k).add_split K D (h.2.1 _)
    · simpa only [add_zero] using h.2.1 k

lemma ShamirDifference.halvFold_split (K : Constants C E) (D : C.Coalition)
    {AR AD : C.Party → ℕ → E}
    (h : ∀ k, ShamirDifference K D (fun i => AR i k) (fun i => AD i k))
    (len : ℕ) (r : E) (k : ℕ) :
    ShamirDifference K D (fun i => halvFold len r (AR i) k)
      (fun i => halvFold len r (AD i) k) := by
  unfold halvFold
  apply (h k).add_split K D
  apply ShamirDifference.scale_split
  split_ifs
  · exact (h k).add_split K D (h _)
  · simpa only [add_zero] using h k

lemma HiddenDifference.consistent_right_split (D : C.Coalition)
    {a b : C.Party → Shares C E} (h : HiddenDifference D a b) (T : C.Term)
    (ha : ConsistentAt D a T) : ConsistentAt D b T := by
  obtain ⟨delta, _, hd⟩ := h
  intro i hiT j hjT hi hj
  funext k
  have he := congrFun (ha i hiT j hjT hi hj) k
  have hdi := hd i hi T hiT k
  have hdj := hd j hj T hjT k
  linear_combination he - hdi + hdj

lemma splitInit_hiddenDifference (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (part : Tuple C → Shares C Bit) (hp : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    HiddenDifference D (fun i => liftedPart (E := E) (x i) part)
      (fun i => liftedPart (dummyOf D x i) part) := by
  exact canonicalDummyTuples_hiddenDifference K counts D x hx _ part hp

/-- Initial slice shares retain the split copies on known terms. -/
lemma splitInit_sliceRel (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (τ : List E) :
    SplitSliceRel D
      (fun i T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k)
      (fun i => liftedPart (x i) (·.y))
      (fun i T k => wordWeightOf K τ counts.sum k * liftedPart (dummyOf D x i) (·.x) T k)
      (fun i => liftedPart (dummyOf D x i) (·.y)) := by
  refine ⟨?_, ?_⟩
  · intro i hi T hT _
    dsimp only
    rw [dummy_known_lifted D x i hi T hT _ (Or.inl rfl),
      dummy_known_lifted D x i hi T hT _ (Or.inr (Or.inl rfl))]
    exact ⟨rfl, rfl⟩
  · intro T hT i j hi hj hiT hjT
    have hxR := tupleInputs_unknown_lifted K hx T hT (·.x) (Or.inl rfl)
    have hyR := tupleInputs_unknown_lifted K hx T hT (·.y) (Or.inr (Or.inl rfl))
    have hxD := (splitInit_hiddenDifference K counts D x hx (·.x) (Or.inl rfl)).consistent_right_split D T hxR
    have hyD := (splitInit_hiddenDifference K counts D x hx (·.y) (Or.inr (Or.inl rfl))).consistent_right_split D T hyR
    refine ⟨?_, hyR i hiT j hjT hi hj, ?_, hyD i hiT j hjT hi hj⟩
    · funext k
      exact congrArg (wordWeightOf K τ counts.sum k * ·) (congrFun (hxR i hiT j hjT hi hj) k)
    · funext k
      exact congrArg (wordWeightOf K τ counts.sum k * ·) (congrFun (hxD i hiT j hjT hi hj) k)

lemma HiddenDifference.claimOf_split (K : Constants C E) (D : C.Coalition)
    {a b : C.Party → Shares C E} (h : HiddenDifference D a b) (τ : List E) (count : ℕ) :
    HiddenDifference D (fun i => claimOf K τ count (a i))
      (fun i => claimOf K τ count (b i)) := by
  obtain ⟨delta, hk, hd⟩ := h
  refine ⟨claimOf K τ count delta, ?_, ?_⟩
  · intro T hT g
    simp [claimOf, hk T hT]
  · intro i hi T hiT g
    simp only [claimOf, ← Finset.sum_sub_distrib, ← mul_sub, hd i hi T hiT]

lemma splitInit_claim (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (τ : List E) :
    ShamirDifference K D
      (fun i => conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0)
      (fun i => conv K (localContext i) (claimOf K τ counts.sum (liftedPart (dummyOf D x i) (·.z))) 0) := by
  exact ((splitInit_hiddenDifference K counts D x hx (·.z) (Or.inr (Or.inr rfl))).claimOf_split
    K D τ counts.sum).conv K D 0

/-- Equal salted digests of different histories imply a cache collision, even with different salts. -/
lemma splitHistories_cacheCollision (cache : HashCache C)
    (a b s t : List Bit) (ha hb d : HashOutput) (hab : a ≠ b)
    (hha : cache (.history a) = some ha) (hhb : cache (.history b) = some hb)
    (hda : cache (.digest s ha) = some d) (hdb : cache (.digest t hb) = some d) :
    CacheHasCollision cache := by
  by_cases hh : ha = hb
  · exact ⟨.history a, .history b, ha, hb, by simpa using hab, hha, hhb, heq_of_eq hh⟩
  · exact ⟨.digest s ha, .digest t hb, d, d,
      fun he => hh (Query.digest.inj he).2, hda, hdb, HEq.rfl⟩

section BirthdayPure

local instance : (Query C →ₒ HashOutput).IsUniformSpec :=
  OracleSpec.IsUniformSpec.ofFintypeInhabited _

/-- The birthday estimate for an entire adaptive hash computation, from the empty cache. -/
theorem splitHash_birthday {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (n : ℕ) (hn : IsTotalQueryBound oa n) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * 2 ^ 256) := by
  letI : Inhabited (Query C) := ⟨.history []⟩
  have hcard : Fintype.card HashOutput = 2 ^ 256 := by
    unfold HashOutput hashOutputBits
    exact card_bitVec 256
  have h := probEvent_cacheCollision_le_birthday_total oa n hn (fun _ => le_rfl)
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using h

end BirthdayPure

/-- Equal recorded prefixes determine all values that a corrupt filler supplied. -/
lemma split_filledValues_of_history (K : Constants C E) (D : C.Coalition) (T : C.Term)
    (a b : List (Tuple C)) (hc : a.map (·.count) = b.map (·.count))
    (hm : a.map (·.mode) = b.map (·.mode))
    (hh : (a.flatMap fun τ => ((List.range τ.count).filter fun g =>
        (filler K τ.mode T g).isSome).map (τ.z T)) =
      (b.flatMap fun τ => ((List.range τ.count).filter fun g =>
        (filler K τ.mode T g).isSome).map (τ.z T))) :
    a.map (fun τ => vector τ.count fun g =>
      if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0) =
    b.map (fun τ => vector τ.count fun g =>
      if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0) := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp at hc
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hc hm
      simp only [List.flatMap_cons] at hh
      have hl : (((List.range a.count).filter fun g => (filler K a.mode T g).isSome).map (a.z T)).length =
          (((List.range b.count).filter fun g => (filler K b.mode T g).isSome).map (b.z T)).length := by
        simp only [List.length_map, hc.1, hm.1]
      obtain ⟨hhead, htail⟩ := List.append_inj hh hl
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih bs hc.2 hm.2 htail⟩
      rw [hc.1]
      unfold vector
      apply List.map_congr_left
      intro g hg
      rw [hm.1]
      by_cases hf : ∃ j ∈ D.1, filler K b.mode T g = some j
      · simp only [if_pos hf]
        rw [hc.1, hm.1] at hhead
        apply List.map_inj_left.mp hhead g
        obtain ⟨j, _, hj⟩ := hf
        simp only [List.mem_filter, hj, Option.isSome_some, and_true]
        exact hg
      · simp only [if_neg hf]

lemma split_filledHistory_consistent (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (T : C.Term) (hh : ConsistentAt D (fun i T => filledHistory K i (x i) T) T) :
    ConsistentAt D (fun i T => (x i).map fun τ =>
      (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) T := by
  apply hx.2.2 T
  intro i hiT j hjT hi hj
  apply split_filledValues_of_history K D T (x i) (x j)
    ((hx.1 i hi).trans (hx.1 j hj).symm) (hx.2.1 i j hi hj)
  simpa only [filledHistory, if_pos hiT, if_pos hjT] using hh i hiT j hjT hi hj

lemma split_agree_of_vectors (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hv : ∀ T, ConsistentAt D (fun i T => (x i).map fun τ =>
      (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) T) :
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) := by
  intro k hk T i hiT j hjT hi hj g hg
  have hk' : k < counts.length := by simpa only [firstInput_length K hx] using hk
  have hi' : k < (x i).length := by
    rw [← List.length_map (f := (·.count)), hx.1 i hi]
    exact hk'
  have hj' : k < (x j).length := by
    rw [← List.length_map (f := (·.count)), hx.1 j hj]
    exact hk'
  have hci : ((x i)[k]).count = counts.getD k 0 := by
    have h := tupleInputs_count_at K hx i hi k
    simpa only [List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some,
      ← List.getD_eq_getElem?_getD] using congrArg (fun o => o.getD 0) h
  have hcj : ((x j)[k]).count = counts.getD k 0 := by
    have h := tupleInputs_count_at K hx j hj k
    simpa only [List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some,
      ← List.getD_eq_getElem?_getD] using congrArg (fun o => o.getD 0) h
  have hg' : g < counts.getD k 0 := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some, tupleAt_count K hx] using hg
  have he := congrArg (fun l => l[k]?) (hv T i hiT j hjT hi hj)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
    Option.map_some, Option.some.injEq] at he
  have hgi : g < ((x i)[k]).count := by rw [hci]; exact hg'
  have he' : ((x i)[k].x T g, (x i)[k].y T g, (x i)[k].z T g) =
      ((x j)[k].x T g, (x j)[k].y T g, (x j)[k].z T g) :=
    Prod.ext (vector_point (congrArg Prod.fst he) hgi)
    (Prod.ext (vector_point (congrArg (fun p => p.2.1) he) hgi)
      (vector_point (congrArg (fun p => p.2.2) he) hgi))
  simpa only [if_neg hi, if_neg hj, Option.bind_some, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hj', Option.map_some, Option.some.injEq] using he'

/-- Split copies already give unequal recorded histories on a known term. -/
lemma splitInit_histories_ne (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hsplit : ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    ∃ T, KnownTo D.1 T ∧ ∃ i j, i ∉ D.1 ∧ j ∉ D.1 ∧
      i ∈ C.holders T ∧ j ∈ C.holders T ∧
      filledHistory K i (x i) T ≠ filledHistory K j (x j) T := by
  by_contra h
  push Not at h
  apply hsplit
  apply split_agree_of_vectors K counts D x hx
  intro T
  by_cases hT : KnownTo D.1 T
  · apply split_filledHistory_consistent K counts D x hx T
    intro i hiT j hjT hi hj
    exact h T hT i j hi hj hiT hjT
  · exact tupleInputs_unknown_vectors K hx T hT

lemma splitInit_history_length (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (T : C.Term) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    (filledHistory K i (x i) T).length = (filledHistory K j (x j) T).length := by
  have hp := map_pair_eq (x i) (x j) (·.count) (·.mode)
    ((hx.1 i hi).trans (hx.1 j hj).symm) (hx.2.1 i j hi hj)
  have he := congrArg (fun l : List (ℕ × ReshareMode) =>
    (l.map fun p => ((List.range p.1).filter fun g => (filler K p.2 T g).isSome).length).sum) hp
  simpa only [filledHistory, if_pos hiT, if_pos hjT, List.length_flatMap,
    List.length_map, List.map_map, Function.comp_def] using he

/-- A split prefix cannot be repaired by choosing separate suffixes at the two holders. -/
lemma split_history_append_ne {α : Type} {a b : List α}
    (hlen : a.length = b.length) (hne : a ≠ b) (c d : List α) : a ++ c ≠ b ++ d := by
  exact fun h => hne (List.append_inj_left h hlen)

lemma splitMult_hiddenDifference (K : Constants C E) (D : C.Coalition) (w : ℕ)
    (resR resD : ℕ → E) (known : Shares C E) (offset : C.Party → Shares C E)
    (rec : Finset C.Party) (fresh : C.Term → Fin w → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ rec) :
    HiddenDifference D
      (fun i => (multFinish D w (filler K .peer) resR known offset rec fresh i).getD 0)
      (fun i => (multFinish D w (filler K .peer) resD known offset rec fresh i).getD 0) := by
  apply HiddenDifference.of_consistent K D
  · intro T hT i hi _
    exact multFinish_known D w _ _ _ _ _ _ fresh i hi (hrec i hi) T hT
  · intro T hT i hiT j hjT hi hj
    exact multFinish_unknown K D w _ _ _ _ fresh T hT i j hi hj (hrec i hi) (hrec j hj) hiT hjT
  · intro T hT i hiT j hjT hi hj
    exact multFinish_unknown K D w _ _ _ _ fresh T hT i j hi hj (hrec i hi) (hrec j hj) hiT hjT

lemma splitSlice_claim {σ : Type} (K : Constants C E) (D : C.Coalition)
    (τ : List E) (count j : ℕ) (xsR ysR xsD ysD : C.Party → Shares C E)
    {DR DD : C.Party → E} (hd : ShamirDifference K D DR DD)
    (pa : σ × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2) (r : E) :
    ShamirDifference K D
      (fun i => sliceClaim τ j r (DR i)
        (conv K (localContext i) (sliceOut K D τ count j xsR ysR pa fresh i) 0)
        (conv K (localContext i) (sliceOut K D τ count j xsR ysR pa fresh i) 1))
      (fun i => sliceClaim τ j r (DD i)
        (conv K (localContext i) (sliceOut K D τ count j xsD ysD pa fresh i) 0)
        (conv K (localContext i) (sliceOut K D τ count j xsD ysD pa fresh i) 1)) := by
  have hout : HiddenDifference D (sliceOut K D τ count j xsR ysR pa fresh)
      (sliceOut K D τ count j xsD ysD pa fresh) :=
    splitMult_hiddenDifference K D 2 _ _ _ _ _ fresh hrec
  have h0 := hout.conv K D 0
  have h1 := hout.conv K D 1
  have h := ((h0.scale_split K D (1 + r)).add_split K D
    ((hd.add_split K D h0).scale_split K D (r / τ.getD (sliceBits - 1 - j) 0))).add_split
    K D (h1.scale_split K D (r * (1 + r)))
  simpa only [sliceClaim, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

lemma splitHalv_after {σ : Type} (K : Constants C E) (D : C.Coalition) (len : ℕ)
    {AR BR AD BD : C.Party → ℕ → E} {DR DD : C.Party → E}
    (h : SplitHalvRel K D AR BR AD BD DR DD)
    (pa : σ × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2) (r : E) :
    SplitHalvRel K D (fun i => halvFold len r (AR i)) (fun i => halvFold len r (BR i))
      (fun i => halvFold len r (AD i)) (fun i => halvFold len r (BD i))
      (fun i => conv K (localContext i) (halvOut K D len AR BR pa fresh i) 0 +
        (DR i + conv K (localContext i) (halvOut K D len AR BR pa fresh i) 1) * r +
        conv K (localContext i) (halvOut K D len AR BR pa fresh i) 1 * r ^ 2)
      (fun i => conv K (localContext i) (halvOut K D len AD BD pa fresh i) 0 +
        (DD i + conv K (localContext i) (halvOut K D len AD BD pa fresh i) 1) * r +
        conv K (localContext i) (halvOut K D len AD BD pa fresh i) 1 * r ^ 2) := by
  refine ⟨ShamirDifference.halvFold_split K D h.1 len r,
    ShamirDifference.halvFold_split K D h.2.1 len r, ?_⟩
  have hout : HiddenDifference D (halvOut K D len AR BR pa fresh)
      (halvOut K D len AD BD pa fresh) :=
    splitMult_hiddenDifference K D 2 _ _ _ _ _ fresh hrec
  have h0 := hout.conv K D 0
  have h1 := hout.conv K D 1
  simpa only [mul_comm] using
    (h0.add_split K D ((h.2.2.add_split K D h1).scale_split K D r)).add_split
      K D (h1.scale_split K D (r ^ 2))

/-- Two honest holders of a known term have distinct histories of equal length. -/
def SplitHistories (D : C.Coalition) (h : C.Party → C.Term → List Bit) : Prop :=
  ∃ T, KnownTo D.1 T ∧ ∃ i j, i ∉ D.1 ∧ j ∉ D.1 ∧ i ∈ C.holders T ∧ j ∈ C.holders T ∧
    (h i T).length = (h j T).length ∧ h i T ≠ h j T

lemma splitInit_histories (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hsplit : ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    SplitHistories D (fun i => filledHistory K i (x i)) := by
  obtain ⟨T, hT, i, j, hi, hj, hiT, hjT, hne⟩ := splitInit_histories_ne K counts D x hx hsplit
  exact ⟨T, hT, i, j, hi, hj, hiT, hjT,
    splitInit_history_length K counts D x hx T i j hi hj hiT hjT, hne⟩

lemma SplitHistories.transfer (D : C.Coalition) {a b : C.Party → C.Term → List Bit}
    (h : SplitHistories D a)
    (he : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → a i T = b i T) :
    SplitHistories D b := by
  obtain ⟨T, hT, i, j, hi, hj, hiT, hjT, hlen, hne⟩ := h
  exact ⟨T, hT, i, j, hi, hj, hiT, hjT,
    by simpa only [← he T hT i hi hiT, ← he T hT j hj hjT] using hlen,
    by simpa only [← he T hT i hi hiT, ← he T hT j hj hjT] using hne⟩

/-- Recording arbitrary offsets preserves the split, since every field encoding has the same length. -/
lemma SplitHistories.record (K : Constants C E) (D : C.Coalition)
    {h : C.Party → C.Term → List Bit} (hs : SplitHistories D h)
    (z : C.Party → Shares C E) (count : ℕ) :
    SplitHistories D (fun i => recordHistory K i (h i) (z i) count) := by
  obtain ⟨T, hT, i, j, hi, hj, hiT, hjT, hlen, hne⟩ := hs
  refine ⟨T, hT, i, j, hi, hj, hiT, hjT, ?_, ?_⟩
  · simp only [recordHistory, if_pos hiT, if_pos hjT, List.length_append, List.length_flatMap,
      Function.comp_apply, elementCodec, List.length_ofFn, hlen]
  · simpa only [recordHistory, if_pos hiT, if_pos hjT] using split_history_append_ne hlen hne _ _

lemma split_digestLive_false (D : C.Coalition) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (T : C.Term) (a b : C.Party)
    (ha : a ∉ D.1) (hb : b ∉ D.1) (haT : a ∈ C.holders T) (hbT : b ∈ C.holders T)
    (hne : (ds a)[C.terms.idxOf T]? ≠ (ds b)[C.terms.idxOf T]?) (i : C.Party) :
    ¬ digestLive D ds sent i := by
  intro h
  have he := (h.2 T a haT b hbT).1
  have hread : ∀ j, j ∉ D.1 →
      (if j = i then ds i else Msg.hashesOf (digestInbox D ds sent i j)) = ds j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · simp [digestInbox, digestOutbox, hj, hji, Ne.symm hji, Msg.hashesOf]
  rw [hread a ha, hread b hb] at he
  exact hne he

/-- Off the collision event every honest operator rejects the digest round. -/
lemma splitHistories_abort (D : C.Coalition) (h : C.Party → C.Term → List Bit)
    (hsplit : SplitHistories D h) (cache : HashCache C) (hno : ¬ CacheHasCollision cache)
    (ds : C.Party → List HashOutput)
    (hds : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → ∃ salt hist d,
      cache (.history (h i T)) = some hist ∧ cache (.digest salt hist) = some d ∧
      (ds i)[C.terms.idxOf T]? = some d)
    (sent : C.Party → Mail C E) (i : C.Party) : ¬ digestLive D ds sent i := by
  obtain ⟨T, hknown, a, b, ha, hb, haT, hbT, _, hne⟩ := hsplit
  apply split_digestLive_false D ds sent T a b ha hb haT hbT _ i
  intro he
  obtain ⟨sa, hha, da, hca, hda, hea⟩ := hds a ha T hknown haT
  obtain ⟨sb, hhb, db, hcb, hdb, heb⟩ := hds b hb T hknown hbT
  have hd : da = db := Option.some.inj (hea.symm.trans (he.trans heb))
  subst db
  exact hno (splitHistories_cacheCollision cache _ _ sa sb hha hhb da hne hca hcb hda hdb)

theorem split_afterDigests_abort {Ia α : Type} (K : Constants C E) (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (ds : C.Party → List HashOutput)
    (next : C.Party → PartyM C E (CheckSpec C E) α)
    (hstop : ∀ sent i, i ∉ D.1 → ¬ digestLive (E := E) D ds sent i) :
    executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
      (fun i => afterDigests i (ds i) (next i)) = (do
        let p ← A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then digestOutbox i (ds i) c else none)
        pure (p.1, fun _ => none)) := by
  rw [executePhase_afterDigests_round]
  apply bind_congr
  intro p
  rw [executePhase_congr_honest D A (checkFunctionalities K) fuel p.1 _ (fun _ => failure),
    executePhase_failure]
  intro i hi
  simp only [if_neg (hstop p.2 i hi)]

def SplitCacheBound (cache : HashCache C) (k : ℕ) : Prop :=
  ∃ S : Finset (Query C), S.card ≤ k ∧ ∀ q, cache q ≠ none → q ∈ S

lemma SplitCacheBound.insert {cache : HashCache C} {k : ℕ}
    (h : SplitCacheBound cache k) (q : Query C) (u : HashOutput) :
    SplitCacheBound (cache.cacheQuery q u) (k + 1) := by
  obtain ⟨S, hs, hc⟩ := h
  refine ⟨Insert.insert q S, (Finset.card_insert_le q S).trans (by omega), ?_⟩
  intro t ht
  by_cases he : t = q
  · exact he ▸ Finset.mem_insert_self _ _
  · rw [QueryCache.cacheQuery_of_ne cache u he] at ht
    exact Finset.mem_insert_of_mem (hc t ht)

lemma splitHash_insert_collision (cache : HashCache C) (q : Query C) (u : HashOutput)
    (hno : ¬ CacheHasCollision cache) (hbad : CacheHasCollision (cache.cacheQuery q u)) :
    ∃ t, cache t = some u := by
  obtain ⟨a, b, v, w, hab, ha, hb, hvw⟩ := hbad
  have hvw' : v = w := eq_of_heq hvw
  subst w
  by_cases haq : a = q
  · subst a
    have hbq : b ≠ q := Ne.symm hab
    simp only [QueryCache.cacheQuery_self, Option.some.injEq] at ha
    rw [QueryCache.cacheQuery_of_ne cache u hbq] at hb
    exact ⟨b, by simpa only [← ha] using hb⟩
  · rw [QueryCache.cacheQuery_of_ne cache u haq] at ha
    by_cases hbq : b = q
    · subst b
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hb
      exact ⟨a, by simpa only [← hb] using ha⟩
    · rw [QueryCache.cacheQuery_of_ne cache u hbq] at hb
      exact False.elim (hno ⟨a, b, v, v, hab, ha, hb, HEq.rfl⟩)

lemma splitHash_insert_birthday (cache : HashCache C) (q : Query C) (k : ℕ)
    (hno : ¬ CacheHasCollision cache) (hk : SplitCacheBound cache k) :
    Pr[fun u => CacheHasCollision (cache.cacheQuery q u) | $ᵗ HashOutput] ≤
      (k : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨S, hs, hc⟩ := hk
  let V := S.image (fun t => (cache t).getD 0)
  have hcard : Fintype.card HashOutput = 2 ^ 256 := by
    unfold HashOutput hashOutputBits
    exact card_bitVec 256
  calc
    _ ≤ Pr[fun u : HashOutput => u ∈ V | $ᵗ HashOutput] := by
      apply probEvent_mono
      intro u _ hu
      obtain ⟨t, ht⟩ := splitHash_insert_collision cache q u hno hu
      exact Finset.mem_image.mpr ⟨t, hc t (by rw [ht]; exact Option.some_ne_none u),
        by simp only [ht, Option.getD_some]⟩
    _ ≤ (V.card : ℝ≥0∞) / Fintype.card HashOutput :=
      probEvent_uniform_injective_mem id Function.injective_id V
    _ ≤ (k : ℝ≥0∞) / 2 ^ 256 := by
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      gcongr
      exact_mod_cast (Finset.card_image_le.trans hs)

lemma SplitCacheBound.mono {cache : HashCache C} {k l : ℕ}
    (h : SplitCacheBound cache k) (hkl : k ≤ l) : SplitCacheBound cache l := by
  obtain ⟨S, hs, hc⟩ := h
  exact ⟨S, hs.trans hkl, hc⟩

lemma splitHash_random_bind {α : Type} (q : Query C)
    (f : HashOutput → StateT (HashCache C) ProbComp α) (cache : HashCache C) (k : ℕ)
    (hno : ¬ CacheHasCollision cache) (hk : SplitCacheBound cache k) (ε : ℝ≥0∞)
    (hf : ∀ u s, ¬ CacheHasCollision s → SplitCacheBound s (k + 1) →
      Pr[fun z => CacheHasCollision z.2 | (f u).run s] ≤ ε) :
    Pr[fun z => CacheHasCollision z.2 |
      (((Query C →ₒ HashOutput).randomOracle q) >>= f).run cache] ≤
      (k : ℝ≥0∞) / 2 ^ 256 + ε := by
  rw [StateT.run_bind]
  cases he : cache q with
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ he, pure_bind]
    exact (hf u cache hno (hk.mono (by omega))).trans le_add_self
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ he, bind_map_left]
    have h := probEvent_bind_le_add
      (mx := ($ᵗ HashOutput)) (my := fun u => (f u).run (cache.cacheQuery q u))
      (p := fun u => ¬ CacheHasCollision (cache.cacheQuery q u))
      (q := fun z => ¬ CacheHasCollision z.2)
      (ε₁ := (k : ℝ≥0∞) / 2 ^ 256) (ε₂ := ε)
      (by simpa only [not_not] using splitHash_insert_birthday cache q k hno hk)
      (by intro u _ hu; simpa only [not_not] using hf u _ hu (hk.insert q u))
    simpa only [not_not, uniformSampleImpl] using h

lemma splitLocal_uncounted (prims : Primitives) (t : (LocalSpec C).Domain)
    (h : ¬ Counted t) : ∃ p, localAnswer prims t = StateT.lift p := by
  rcases t with n | q | x
  · exact ⟨_, rfl⟩
  · cases q with
    | hash input =>
      have hi : MpcInput input := by simpa only [Counted, not_not] using h
      refine ⟨pure (prims.Th input), ?_⟩
      change hashAnswer prims (.hash input) = _
      rw [hashAnswer_of_isFixed prims hi]
      rfl
    | _ => exact (h trivial).elim
  · exact (h trivial).elim

/-- Whole-run birthday bound with private sampling and the fixed `Th` domain excluded from the count. -/
theorem splitLocal_birthday_aux (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) : ∀ (n k : ℕ), IsQueryBoundP oa Counted n →
    ∀ cache : HashCache C, ¬ CacheHasCollision cache → SplitCacheBound cache k →
    Pr[fun z => CacheHasCollision z.2 | (simulateQ (localAnswer prims) oa).run cache] ≤
      ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n k _ cache hno hk
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hno, if_false]
    exact zero_le
  | query_bind t f ih =>
    intro n k hn cache hno hk
    rw [isQueryBoundP_query_bind_iff] at hn
    have hlift : ∀ p, localAnswer prims t = StateT.lift p →
        Pr[fun z => CacheHasCollision z.2 |
          (simulateQ (localAnswer prims) (liftM ((LocalSpec C).query t) >>= f)).run cache] ≤
          ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
      intro p hp
      change Pr[fun z => CacheHasCollision z.2 |
        (localAnswer prims t >>= fun u => simulateQ (localAnswer prims) (f u)).run cache] ≤ _
      rw [hp]
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      apply probEvent_bind_le_of_forall_le
      intro u _
      exact (ih u _ k (hn.2 u) cache hno hk).trans
        (Finset.sum_le_sum_of_subset (Finset.range_mono (by split_ifs <;> omega)))
    by_cases ht : Counted t
    swap
    · obtain ⟨p, hp⟩ := splitLocal_uncounted prims t ht
      exact hlift p hp
    rcases isAtom_localAnswer prims t with ⟨p, hp⟩ | ⟨q, g, hq⟩
    · exact hlift p hp
    have hnpos : 0 < n := by have := hn.1.resolve_left (not_not.mpr ht); omega
    have he : (k : ℝ≥0∞) / 2 ^ 256 +
        ∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 =
        ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
      conv_rhs => rw [show n = (n - 1) + 1 from by omega]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [show k + 1 + j = k + (j + 1) by omega]
    rw [← he]
    change Pr[fun z => CacheHasCollision z.2 |
      (localAnswer prims t >>= fun u => simulateQ (localAnswer prims) (f u)).run cache] ≤ _
    rw [hq, bind_map_left]
    apply splitHash_random_bind q _ cache k hno hk
    intro u s hs hsk
    apply ih (g u) (n - 1) (k + 1) _ s hs hsk
    simpa only [if_pos ht] using hn.2 (g u)

/-- The full local oracle, including private sampling and PRG calls, satisfies the tight birthday bound. -/
theorem splitLocal_birthday (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n : ℕ) (hn : IsQueryBoundP oa Counted n) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ (localAnswer prims) oa).run ∅] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * 2 ^ 256) := by
  have h := splitLocal_birthday_aux prims oa n 0 hn ∅
    (by rintro ⟨a, b, u, v, _, ha, _, _⟩; simp at ha)
    ⟨∅, by simp, fun t ht => (ht rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at h
  exact h.trans_eq (ENNReal.gauss_sum_inv_eq n (2 ^ 256))

lemma splitInit_dummy_histories (K : Constants C E) (counts : List ℕ)
    (D : C.Coalition) (x : C.Party → List (Tuple C)) (hx : TupleInputs K counts D x)
    (hsplit : ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    SplitHistories D (fun i => filledHistory K i (dummyOf D x i)) := by
  exact (splitInit_histories K counts D x hx hsplit).transfer D (initHist K counts D x hx).2.2.1

lemma splitHalv_hist {σ : Type} (K : Constants C E) (D : C.Coalition) (len tg L : ℕ)
    (AR BR AD BD : C.Party → ℕ → E) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD)
    (pa : σ × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2) :
    HistRel D tg (L + 1 + 1)
      (fun i => ⟨recordHistory K i (hsR i).history (halvOut K D len AR BR pa fresh i) 2,
        (hsR i).label + 1 + 1, (hsR i).tag⟩)
      (fun i => ⟨recordHistory K i (hsD i).history (halvOut K D len AD BD pa fresh i) 2,
        (hsD i).label + 1 + 1, (hsD i).tag⟩) := by
  obtain ⟨htagR, htagD, hknown, hcommonR, hcommonD⟩ := hh
  refine ⟨fun i hi => by simp [htagR i hi], fun i hi => by simp [htagD i hi], ?_, ?_, ?_⟩
  · intro T hT i hi hiT
    simp only [recordHistory, if_pos hiT, hknown T hT i hi hiT]
    unfold halvOut
    rw [multFinish_known D 2 _ _ _ _ _ _ fresh i hi (hrec i hi) T hT]
  · intro T hT i j hi hj hiT hjT
    simp only [recordHistory, if_pos hiT, if_pos hjT, hcommonR T hT i j hi hj hiT hjT]
    unfold halvOut
    rw [multFinish_unknown K D 2 _ _ _ _ fresh T hT i j hi hj (hrec i hi) (hrec j hj) hiT hjT]
  · intro T hT i j hi hj hiT hjT
    simp only [recordHistory, if_pos hiT, if_pos hjT, hcommonD T hT i j hi hj hiT hjT]
    unfold halvOut
    rw [multFinish_unknown K D 2 _ _ _ _ fresh T hT i j hi hj (hrec i hi) (hrec j hj) hiT hjT]

/-- The final masked multiplication also needs only the polynomial differences. -/
lemma splitMaskedView (K : Constants C E) (D : C.Coalition) (known : Shares C E)
    {A B A' B' : C.Party → E} (hA : ShamirDifference K D A A')
    (hB : ShamirDifference K D B B') :
    maskedView K D known 0 A B = maskedView K D known 0 A' B' := by
  unfold maskedView
  apply extendView_eq_of_relation
  apply shamirPair_viewRelation
  · intro k; exact ShamirDifference.refl K D _
  · intro k; exact ShamirDifference.refl K D _
  · intro k
    exact (ShamirDifference.refl K D _).add_split K D hA
  · intro k
    exact (ShamirDifference.refl K D _).add_split K D hB

/-- Keep only the oracle domain whose output collisions are being charged. -/
def splitRegionCache (P : Query C → Prop) (cache : HashCache C) : HashCache C :=
  fun q => if P q then cache q else none

lemma splitRegionCache_insert (P : Query C → Prop) (cache : HashCache C)
    (q : Query C) (u : HashOutput) (hq : P q) :
    splitRegionCache P (cache.cacheQuery q u) = (splitRegionCache P cache).cacheQuery q u := by
  funext t
  by_cases ht : t = q
  · subst t
    simp [splitRegionCache, hq]
  · simp only [splitRegionCache, QueryCache.cacheQuery_of_ne _ _ ht]

lemma splitRegionCache_insert_irrelevant (P : Query C → Prop) (cache : HashCache C)
    (q : Query C) (u : HashOutput) (hq : ¬ P q) :
    splitRegionCache P (cache.cacheQuery q u) = splitRegionCache P cache := by
  funext t
  by_cases ht : t = q
  · subst t
    simp [splitRegionCache, hq]
  · simp only [splitRegionCache, QueryCache.cacheQuery_of_ne _ _ ht]

def splitLocalHashInput : (LocalSpec C).Domain → Option (Query C)
  | .inl _ => none
  | .inr (.inl q) => if IsFixed q then none else some q
  | .inr (.inr x) => some (.streamKey x.2.1)

def SplitRegionCounted (P : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q, splitLocalHashInput t = some q ∧ P q

lemma splitLocalHashInput_none (prims : Primitives) (t : (LocalSpec C).Domain)
    (h : splitLocalHashInput t = none) : ∃ p, localAnswer prims t = StateT.lift p := by
  rcases t with n | q | x
  · exact ⟨_, rfl⟩
  · simp only [splitLocalHashInput, ite_eq_left_iff, reduceCtorEq, imp_false, not_not] at h
    obtain ⟨input, rfl, hi⟩ := h
    refine ⟨pure (prims.Th input), ?_⟩
    change hashAnswer prims (.hash input) = _
    rw [hashAnswer_of_isFixed prims hi]
    rfl
  · simp [splitLocalHashInput] at h

lemma splitLocalHashInput_some (prims : Primitives) (t : (LocalSpec C).Domain)
    (q : Query C) (h : splitLocalHashInput t = some q) :
    ∃ f : HashOutput → (LocalSpec C).Range t,
      localAnswer prims t = f <$> (Query C →ₒ HashOutput).randomOracle q := by
  rcases t with n | r | x
  · simp [splitLocalHashInput] at h
  · by_cases hr : IsFixed r
    · simp [splitLocalHashInput, hr] at h
    · simp only [splitLocalHashInput, if_neg hr, Option.some.injEq] at h
      subst q
      refine ⟨id, ?_⟩
      change hashAnswer prims r = _
      rw [hashAnswer_of_not_isFixed prims hr]
      exact (id_map _).symm
  · simp only [splitLocalHashInput, Option.some.injEq] at h
    subst q
    refine ⟨fun d => prims.aes.eval (truncateHash d) x.2.2, ?_⟩
    change prgAnswer prims x = _
    simp only [prgAnswer, hashAnswer, map_eq_bind_pure_comp]
    rfl

lemma splitRegion_random_bind {α : Type} (P : Query C → Prop) (q : Query C)
    (f : HashOutput → StateT (HashCache C) ProbComp α) (cache : HashCache C) (k : ℕ)
    (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (hk : SplitCacheBound (splitRegionCache P cache) k) (ε : ℝ≥0∞)
    (hf : ∀ u s, ¬ CacheHasCollision (splitRegionCache P s) →
      SplitCacheBound (splitRegionCache P s) (k + if P q then 1 else 0) →
      Pr[fun z => CacheHasCollision (splitRegionCache P z.2) | (f u).run s] ≤ ε) :
    Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (((Query C →ₒ HashOutput).randomOracle q) >>= f).run cache] ≤
      (if P q then (k : ℝ≥0∞) / 2 ^ 256 else 0) + ε := by
  rw [StateT.run_bind]
  cases he : cache q with
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ he, pure_bind]
    exact (hf u cache hno (hk.mono (Nat.le_add_right _ _))).trans le_add_self
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ he, bind_map_left]
    by_cases hq : P q
    · simp only [if_pos hq] at hf ⊢
      have h := probEvent_bind_le_add
        (mx := ($ᵗ HashOutput)) (my := fun u => (f u).run (cache.cacheQuery q u))
        (p := fun u => ¬ CacheHasCollision (splitRegionCache P (cache.cacheQuery q u)))
        (q := fun z => ¬ CacheHasCollision (splitRegionCache P z.2))
        (ε₁ := (k : ℝ≥0∞) / 2 ^ 256) (ε₂ := ε)
        (by simpa only [not_not, splitRegionCache_insert P cache q _ hq]
            using splitHash_insert_birthday (splitRegionCache P cache) q k hno hk)
        (by
          intro u _ hu
          simp only [not_not]
          apply hf u _ hu
          rw [splitRegionCache_insert P cache q u hq]
          exact hk.insert q u)
      simpa only [not_not, uniformSampleImpl] using h
    · simp only [if_neg hq, Nat.add_zero] at hf ⊢
      rw [zero_add]
      apply probEvent_bind_le_of_forall_le
      intro u _
      apply hf u _
      · simpa only [splitRegionCache_insert_irrelevant P cache q u hq] using hno
      · simpa only [splitRegionCache_insert_irrelevant P cache q u hq] using hk

theorem splitRegion_birthday_aux (prims : Primitives) (P : Query C → Prop) {α : Type}
    (oa : OracleComp (LocalSpec C) α) : ∀ (n k : ℕ), IsQueryBoundP oa (SplitRegionCounted P) n →
    ∀ cache : HashCache C, ¬ CacheHasCollision (splitRegionCache P cache) →
    SplitCacheBound (splitRegionCache P cache) k →
    Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (simulateQ (localAnswer prims) oa).run cache] ≤
      ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n k _ cache hno hk
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hno, if_false]
    exact zero_le
  | query_bind t f ih =>
    intro n k hn cache hno hk
    rw [isQueryBoundP_query_bind_iff] at hn
    change Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (localAnswer prims t >>= fun u => simulateQ (localAnswer prims) (f u)).run cache] ≤ _
    cases he : splitLocalHashInput t with
    | none =>
      obtain ⟨p, hp⟩ := splitLocalHashInput_none prims t he
      have ht : ¬ SplitRegionCounted P t := by simp [SplitRegionCounted, he]
      rw [hp]
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      apply probEvent_bind_le_of_forall_le
      intro u _
      apply ih u n k _ cache hno hk
      simpa only [if_neg ht] using hn.2 u
    | some q =>
      obtain ⟨g, hg⟩ := splitLocalHashInput_some prims t q he
      have ht : SplitRegionCounted P t ↔ P q := by simp [SplitRegionCounted, he]
      rw [hg, bind_map_left]
      by_cases hq : P q
      · have hcount := ht.mpr hq
        have hnpos : 0 < n := by have := hn.1.resolve_left (not_not.mpr hcount); omega
        have hsum : (k : ℝ≥0∞) / 2 ^ 256 +
            ∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 =
            ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          conv_rhs => rw [show n = (n - 1) + 1 from by omega]
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [show k + 1 + j = k + (j + 1) by omega]
        rw [← hsum]
        have h := splitRegion_random_bind P q (fun u => simulateQ (localAnswer prims) (f (g u)))
          cache k hno hk (∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256) (by
            intro u s hs hsk
            exact ih (g u) (n - 1) (k + 1)
              (by simpa only [if_pos hcount] using hn.2 (g u)) s hs
              (by simpa only [if_pos hq] using hsk))
        simpa only [if_pos hq] using h
      · have hcount : ¬ SplitRegionCounted P t := fun h => hq (ht.mp h)
        have h := splitRegion_random_bind P q (fun u => simulateQ (localAnswer prims) (f (g u)))
          cache k hno hk (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256) (by
            intro u s hs hsk
            exact ih (g u) n k (by simpa only [if_neg hcount] using hn.2 (g u)) s hs
              (by simpa only [if_neg hq, Nat.add_zero] using hsk))
        simpa only [if_neg hq, zero_add] using h

/-- Queries outside the selected hash domains need no charge in their collision bound. -/
theorem splitRegion_birthday (prims : Primitives) (P : Query C → Prop) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n : ℕ) (hn : IsQueryBoundP oa (SplitRegionCounted P) n) :
    Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (simulateQ (localAnswer prims) oa).run ∅] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * 2 ^ 256) := by
  have hempty : splitRegionCache P (∅ : HashCache C) = ∅ := by
    funext q
    simp [splitRegionCache]
  have h := splitRegion_birthday_aux prims P oa n 0 hn ∅
    (by rw [hempty]; rintro ⟨a, b, u, v, _, ha, _, _⟩; simp at ha)
    (by rw [hempty]; exact ⟨∅, by simp, fun t ht => (ht rfl).elim⟩)
  simp only [Nat.zero_add, div_eq_mul_inv] at h
  exact h.trans_eq (ENNReal.gauss_sum_inv_eq n (2 ^ 256))

lemma splitRegionCounted_counted (P : Query C → Prop) (t : (LocalSpec C).Domain)
    (h : SplitRegionCounted P t) : Counted t := by
  obtain ⟨q, hq, _⟩ := h
  rcases t with n | r | x
  · simp [splitLocalHashInput] at hq
  · cases r <;> simp_all [splitLocalHashInput, Counted, IsFixed]
  · trivial

lemma counted_splitRegionBound (P : Query C → Prop) {α : Type}
    {oa : OracleComp (LocalSpec C) α} {n : ℕ} (h : IsQueryBoundP oa Counted n) :
    IsQueryBoundP oa (SplitRegionCounted P) n :=
  IsQueryBoundP.of_imp (splitRegionCounted_counted P) h

def SplitHashDomain : Query C → Prop
  | .history _ => True
  | .digest _ _ => True
  | _ => False

lemma splitHistories_abort_region (D : C.Coalition) (h : C.Party → C.Term → List Bit)
    (hsplit : SplitHistories D h) (cache : HashCache C)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache))
    (ds : C.Party → List HashOutput)
    (hds : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → ∃ salt hist d,
      cache (.history (h i T)) = some hist ∧ cache (.digest salt hist) = some d ∧
      (ds i)[C.terms.idxOf T]? = some d)
    (sent : C.Party → Mail C E) (i : C.Party) : ¬ digestLive D ds sent i := by
  apply splitHistories_abort D h hsplit (splitRegionCache SplitHashDomain cache) hno ds _ sent i
  intro j hj T hT hjT
  simpa only [splitRegionCache, SplitHashDomain, if_true] using hds j hj T hT hjT

/-- A selected-domain call budget fits half of the hash-error allowance. -/
theorem splitRegion_birthday_le_checkHashError (prims : Primitives) (P : Query C → Prop)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (count q n : ℕ)
    (hn : IsQueryBoundP oa (SplitRegionCounted P) n)
    (hbudget : n ≤ q + termHashes C + halvings count + 2) :
    (Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (simulateQ (localAnswer prims) oa).run ∅]).toReal ≤ checkHashError C count q / 2 := by
  have h := ENNReal.toReal_mono (by finiteness) (splitRegion_birthday prims P oa n hn)
  have hnum : n * (n - 1) ≤ (q + termHashes C + halvings count + 2) ^ 2 := by
    calc
      n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul hbudget hbudget
  have hnumR : ((n * (n - 1) : ℕ) : ℝ) ≤ ((q + termHashes C + halvings count + 2) ^ 2 : ℕ) :=
    by exact_mod_cast hnum
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h
  unfold checkHashError
  calc
    _ ≤ ((n * (n - 1) : ℕ) : ℝ) / (2 * 2 ^ 256) := h
    _ ≤ ((q + termHashes C + halvings count + 2) ^ 2 : ℕ) / (2 * (2 : ℝ) ^ 256) := by
      exact div_le_div_of_nonneg_right hnumR (by positivity)
    _ = _ := by ring

lemma splitRegion_step_bound (prims : Primitives) (P : Query C → Prop)
    (t : (LocalSpec C).Domain) (cache : HashCache C) (k : ℕ)
    (hk : SplitCacheBound (splitRegionCache P cache) k)
    (z : (LocalSpec C).Range t × HashCache C)
    (hz : z ∈ support ((localAnswer prims t).run cache)) :
    SplitCacheBound (splitRegionCache P z.2) (k + if SplitRegionCounted P t then 1 else 0) := by
  cases he : splitLocalHashInput t with
  | none =>
    obtain ⟨p, hp⟩ := splitLocalHashInput_none prims t he
    rw [hp] at hz
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, _, rfl⟩ := hz
    simpa only [SplitRegionCounted, he, reduceCtorEq, false_and, exists_false, if_false, Nat.add_zero] using hk
  | some q =>
    obtain ⟨f, hf⟩ := splitLocalHashInput_some prims t q he
    rw [hf, StateT.run_map] at hz
    rw [support_map, Set.mem_image] at hz
    obtain ⟨⟨u, cache'⟩, hu, rfl⟩ := hz
    have hu' := randomOracle_support q cache (u, cache') hu
    dsimp only at hu'
    have ht : SplitRegionCounted P t ↔ P q := by simp [SplitRegionCounted, he]
    simp only [ht]
    by_cases hq : P q
    · rw [if_pos hq]
      obtain ⟨S, hs, hc⟩ := hk
      refine ⟨insert q S, (Finset.card_insert_le q S).trans (by omega), ?_⟩
      intro r hr
      by_cases hrq : r = q
      · exact hrq ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply hc r
        simpa only [splitRegionCache, hu'.2.2 r hrq] using hr
    · rw [if_neg hq, Nat.add_zero]
      have hcache : splitRegionCache P cache' = splitRegionCache P cache := by
        funext r
        by_cases hrq : r = q
        · subst r; simp [splitRegionCache, hq]
        · simp only [splitRegionCache, hu'.2.2 r hrq]
      rwa [hcache]

lemma splitRegion_support_bound (prims : Primitives) (P : Query C → Prop) {α : Type}
    (oa : OracleComp (LocalSpec C) α) : ∀ n, IsQueryBoundP oa (SplitRegionCounted P) n →
    ∀ cache k, SplitCacheBound (splitRegionCache P cache) k →
    ∀ z ∈ support ((simulateQ (localAnswer prims) oa).run cache),
      SplitCacheBound (splitRegionCache P z.2) (k + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ cache k hk z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hk.mono (Nat.le_add_right _ _)
  | query_bind t f ih =>
    intro n hn cache k hk z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    change z ∈ support ((localAnswer prims t >>= fun u => simulateQ (localAnswer prims) (f u)).run cache) at hz
    rw [StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, s⟩, hu, hz⟩ := hz
    have hs := splitRegion_step_bound prims P t cache k hk (u, s) hu
    have h := ih u _ (hn.2 u) s _ hs z hz
    apply h.mono
    by_cases ht : SplitRegionCounted P t
    · have hnpos := hn.1.resolve_left (not_not.mpr ht)
      simp only [if_pos ht]; omega
    · simp only [if_neg ht]; omega

/-- The actual digest queries leave both answers in the monotone cache. -/
lemma split_oneDigest_support (prims : Primitives) (salt hist : List Bit)
    (cache : HashCache C) (z : HashOutput × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims)
      (liftComp (oneDigestQuery (C := C) salt hist) (LocalSpec C))).run cache)) :
    cache ≤ z.2 ∧ ∃ h, z.2 (.history hist) = some h ∧ z.2 (.digest salt h) = some z.1 := by
  rw [simulateQ_localAnswer_liftComp] at hz
  simp only [oneDigestQuery, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨h, s⟩, hh, hz⟩ := hz
  obtain ⟨hle, hc, _⟩ := support_hashQuery prims (q := .history hist)
    (by rintro ⟨_, he, _⟩; cases he) cache _ hh
  obtain ⟨hle', hc', _⟩ := support_hashQuery prims (q := .digest salt h)
    (by rintro ⟨_, he, _⟩; cases he) s _ hz
  exact ⟨hle.trans hle', h, hle' hc, hc'⟩

def SplitDigestEvidence (D : C.Coalition) (hist : C.Party → C.Term → List Bit)
    (salts : C.Party → Shares C Bit) (T : C.Term) (col : DigestColumn C) (cache : HashCache C) : Prop :=
  ∀ i, i ∉ D.1 → i ∈ C.holders T → ∃ h,
    cache (.history (hist i T)) = some h ∧ cache (.digest (vector 256 (salts i T)) h) = some (col i)

lemma SplitDigestEvidence.mono {D : C.Coalition} {hist : C.Party → C.Term → List Bit}
    {salts : C.Party → Shares C Bit} {T : C.Term} {col : DigestColumn C} {cache cache' : HashCache C}
    (h : SplitDigestEvidence D hist salts T col cache) (hle : cache ≤ cache') :
    SplitDigestEvidence D hist salts T col cache' := by
  intro i hi hiT
  obtain ⟨a, ha, hb⟩ := h i hi hiT
  exact ⟨a, hle ha, hle hb⟩

lemma split_column_support (prims : Primitives) (D : C.Coalition) (T : C.Term)
    (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (cache : HashCache C) (z : DigestColumn C × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims)
      (Concrete.sequenceFin (honestDigestColumn D T salts hist))).run cache)) :
    cache ≤ z.2 ∧ SplitDigestEvidence D hist salts T z.1 z.2 := by
  rw [simulateQ_sequenceFin] at hz
  have hh := support_sequenceFin_inv (fun _ : HashCache C => True)
    (fun i => simulateQ (localAnswer prims) (honestDigestColumn D T salts hist i))
    (fun i a s => i ∉ D.1 → i ∈ C.holders T → ∃ h,
      s (.history (hist i T)) = some h ∧ s (.digest (vector 256 (salts i T)) h) = some a)
    (by
      intro i s _ u hu
      unfold honestDigestColumn at hu
      by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
      · rw [if_pos hi] at hu
        obtain ⟨hle, he⟩ := split_oneDigest_support prims _ _ s u hu
        exact ⟨hle, trivial, fun _ _ => he⟩
      · rw [if_neg hi] at hu
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
        subst u
        exact ⟨le_rfl, trivial, fun h₁ h₂ => (hi ⟨h₁, h₂⟩).elim⟩)
    (by
      intro i a s s' h hle hi hiT
      obtain ⟨v, hv, hd⟩ := h hi hiT
      exact ⟨v, hle hv, hle hd⟩) cache trivial z hz
  exact ⟨hh.1, hh.2.2⟩

lemma split_ghost_support (prims : Primitives) (D : C.Coalition)
    (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit) :
    ∀ (Ts : List C.Term) (cache : HashCache C) z,
    z ∈ support ((simulateQ (localAnswer prims) (mixedGhostDigests D
      (fun T => Concrete.sequenceFin (honestDigestColumn D T salts hist)) Ts pure)).run cache) →
    cache ≤ z.2 ∧ List.Forall₂ (fun T col => KnownTo D.1 T →
      SplitDigestEvidence D hist salts T col z.2) Ts z.1 := by
  intro Ts
  induction Ts with
  | nil =>
    intro cache z hz
    simp only [mixedGhostDigests, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨le_rfl, .nil⟩
  | cons T Ts ih =>
    intro cache z hz
    simp only [mixedGhostDigests] at hz
    by_cases hT : KnownTo D.1 T
    · rw [if_pos hT, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨col, s⟩, hc, hz⟩ := hz
      rw [mixedGhostDigests_bind_pure, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨cols, s'⟩, hcs, hz⟩ := hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      obtain ⟨hle, he⟩ := split_column_support prims D T salts hist cache (col, s) hc
      obtain ⟨hle', he'⟩ := ih s (cols, s') hcs
      exact ⟨hle.trans hle', .cons (fun _ => he.mono hle') he'⟩
    · rw [if_neg hT, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨d, s⟩, hd, hz⟩ := hz
      rw [mixedGhostDigests_bind_pure, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨cols, s'⟩, hcs, hz⟩ := hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      have hle := Grows.simulateQ (grows_localAnswer prims)
        (liftComp ($ᵗ HashOutput) (LocalSpec C)) cache (d, s) hd
      obtain ⟨hle', he'⟩ := ih s (cols, s') hcs
      exact ⟨hle.trans hle', .cons (fun h => (hT h).elim) he'⟩

lemma split_ghost_abort (prims : Primitives) (D : C.Coalition)
    (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (hsplit : SplitHistories D hist) (cache : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (mixedGhostDigests D
      (fun T => Concrete.sequenceFin (honestDigestColumn D T salts hist)) C.terms pure)).run cache))
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain z.2))
    (sent : C.Party → Mail C E) (i : C.Party) :
    ¬ digestLive D (digestRows z.1) sent i := by
  have he := (split_ghost_support prims D salts hist C.terms cache z hz).2
  apply splitHistories_abort_region D hist hsplit z.2 hno (digestRows z.1) _ sent i
  intro j hj T hT hjT
  have hlen : C.terms.idxOf T < z.1.length := he.length_eq ▸ idxOf_terms_lt T
  have hentry := he.get (idxOf_terms_lt T) hlen
  simp only [List.get_eq_getElem, List.getElem_idxOf] at hentry
  obtain ⟨a, ha, hd⟩ := hentry hT j hj hjT
  refine ⟨vector 256 (salts j T), a, z.1[C.terms.idxOf T] j, ha, hd, ?_⟩
  simp only [digestRows, List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some]

def splitRisk (k n : ℕ) : ℝ :=
  (((k + n : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) / (2 * 2 ^ 256)

lemma splitRisk_nonneg (k n : ℕ) : 0 ≤ splitRisk k n := by
  unfold splitRisk
  have : (k : ℝ) ≤ ((k + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right k n
  apply div_nonneg _ (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma splitRisk_add (k n m : ℕ) : splitRisk k n + splitRisk (k + n) m = splitRisk k (n + m) := by
  simp only [splitRisk, Nat.cast_add]
  ring

lemma splitRisk_mono {k k' n n' : ℕ} (hk : k ≤ k') (hn : n ≤ n') :
    splitRisk k n ≤ splitRisk k' n' := by
  unfold splitRisk
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [Nat.cast_add]
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have hn' : (n : ℝ) ≤ n' := by exact_mod_cast hn
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n,
    Nat.cast_nonneg (α := ℝ) k', Nat.cast_nonneg (α := ℝ) n']

lemma splitRegion_birthday_real (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n k : ℕ)
    (hn : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) n)
    (cache : HashCache C) (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache))
    (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k) :
    (Pr[fun z => CacheHasCollision (splitRegionCache SplitHashDomain z.2) |
      (simulateQ (localAnswer prims) oa).run cache]).toReal ≤ splitRisk k n := by
  have hfin : ∀ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 ≠ ⊤ := by
    intros; finiteness
  have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin)
    (splitRegion_birthday_aux prims SplitHashDomain oa n k hn cache hno hk)
  have hs : (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256).toReal =
      (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ)) / 2 ^ 256 := by
    rw [ENNReal.toReal_sum hfin]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, Finset.sum_div]
  rw [hs] at h
  refine h.trans ?_
  have hsum : ∀ n : ℕ, 2 * (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ)) ≤
      ((k + n : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one] at *
      nlinarith
  have hden : (0 : ℝ) < 2 ^ 256 := by positivity
  unfold splitRisk
  apply (div_le_div_iff₀ hden (by positivity)).2
  nlinarith [hsum n]

lemma split_digestQuery_region (t : (LocalSpec C).Domain) (h : DigestQuery t) :
    SplitRegionCounted SplitHashDomain t := by
  rcases t with n | q | x
  · simp [DigestQuery, digestSaltProjection] at h
  · cases q <;> simp_all [DigestQuery, digestSaltProjection, SplitRegionCounted,
      splitLocalHashInput, SplitHashDomain, IsFixed]
  · simp [DigestQuery, digestSaltProjection] at h

/-- Convexity with a support-sensitive bad event. -/
lemma split_tvDist_bind {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (bad : α → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ a, a ∈ support oa → ¬ bad a → tvDist (f a) (g a) ≤ c) :
    tvDist (oa >>= f) (oa >>= g) ≤ (Pr[bad | oa]).toReal + c := by
  let f' : α → ProbComp β := fun a => if bad a then g a else f a
  apply (tvDist_triangle _ (oa >>= f') _).trans
  apply add_le_add
  · exact tvDist_bind_left_event_le oa f f' bad (by intro a ha; simp [f', ha])
  · apply tvDist_bind_left_le_const
    intro a ha
    by_cases hb : bad a
    · simpa [f', hb] using hc
    · simpa [f', hb] using h a ha hb

/-- A shared prefix spends its birthday budget once, then continues on collision-free caches. -/
lemma split_tvDist_prefix (prims : Primitives) {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) β) (n k : ℕ)
    (hq : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) n)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache))
    (c : ℝ) (hc0 : 0 ≤ c)
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ k + n → SplitCacheBound (splitRegionCache SplitHashDomain cache') (k + n) →
      ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache') →
      tvDist ((simulateQ (localAnswer prims) (f a)).run' cache')
        ((simulateQ (localAnswer prims) (g a)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) (oa >>= f)).run' cache)
      ((simulateQ (localAnswer prims) (oa >>= g)).run' cache) ≤ splitRisk k n + c := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine (split_tvDist_bind _ _ _ (fun z : α × HashCache C => CacheHasCollision (splitRegionCache SplitHashDomain z.2))
    c hc0 ?_).trans (add_le_add (splitRegion_birthday_real prims oa n k hq cache hno hk) le_rfl)
  intro z hz hzno
  obtain ⟨seen', hcov, hs⟩ := localProgram_digest_covered prims oa
    (SplitRegionCounted SplitHashDomain) split_digestQuery_region n hq cache seen hc z hz
  have hb := splitRegion_support_bound prims SplitHashDomain oa n hq cache k hk z hz
  simpa only [StateT.run'_eq] using h z.1 z.2 seen' hcov (by omega) hb hzno

def splitBound (C : Committee) (step final k fuel : ℕ) : ℝ :=
  coupleBound C step final k fuel + splitRisk k (fuel * step + termHashes C)

lemma splitBound_nonneg (step final k fuel : ℕ) : 0 ≤ splitBound C step final k fuel :=
  add_nonneg (coupleBound_nonneg _ _ _ _) (splitRisk_nonneg _ _)

lemma splitBound_prefix (step final k fuel rounds : ℕ) :
    splitRisk k (rounds * step) + splitBound C step final (k + rounds * step) fuel =
      splitBound C step final k (fuel + rounds) := by
  unfold splitBound coupleBound
  have hr := splitRisk_add k (rounds * step) (fuel * step + termHashes C)
  simp only [Nat.cast_add, Nat.cast_mul] at *
  rw [← add_assoc, add_comm (splitRisk _ _) _, add_assoc, hr]
  congr 2 <;> ring

variable {Ia α : Type}

lemma split_prob_lift_no_digest (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) (SplitRegionCounted SplitHashDomain) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind,liftComp_query]
    simp only [OracleQuery.input_query,OracleQuery.cont_query,id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) (SplitRegionCounted SplitHashDomain) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [SplitRegionCounted,splitLocalHashInput, SplitRegionCounted, SplitHashDomain, IsFixed]),fun u => by
      simpa [SplitRegionCounted,splitLocalHashInput, SplitRegionCounted, SplitHashDomain, IsFixed] using ih u⟩



lemma split_hashQuery_no_digest (q : Query C) (hq : ¬ (SplitRegionCounted SplitHashDomain) (.inr (.inl q))) :
    IsQueryBoundP (liftComp (hashQuery q) (LocalSpec C)) (SplitRegionCounted SplitHashDomain) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inr (.inl q)))) (SplitRegionCounted SplitHashDomain) 0
  exact (isQueryBoundP_query_iff ..).2 (fun h => False.elim (hq h))


lemma split_findChallenge_no_digest (K : Constants C E) (key : HashOutput) : ∀ tries index,
    IsQueryBoundP (liftComp (findChallenge K key tries index) (LocalSpec C)) (SplitRegionCounted SplitHashDomain) 0
  | 0,index => by simp [findChallenge]
  | tries+1,index => by
    simp only [findChallenge,liftComp_bind]
    apply isQueryBoundP_bind (n := 0) (m := 0) (split_hashQuery_no_digest _ (by simp [SplitRegionCounted,splitLocalHashInput, SplitRegionCounted, SplitHashDomain, IsFixed]))
    intro h _
    split
    · simp
    · exact split_findChallenge_no_digest K key tries (index+1)


lemma split_challengeQuery_no_digest (K : Constants C E) (tg L : ℕ) (v : List E) :
    IsQueryBoundP (liftComp (challengeQuery K tg L v) (LocalSpec C)) (SplitRegionCounted SplitHashDomain) 0 := by
  simp only [challengeQuery, liftComp_bind]
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (split_hashQuery_no_digest _ (by simp [SplitRegionCounted, splitLocalHashInput, SplitRegionCounted, SplitHashDomain, IsFixed])) fun key _ =>
      split_findChallenge_no_digest K key challengeTries 0

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma split_bind_sample_digestBound {σ' α β : Type} [SampleableType α] (oa : OracleComp (LocalSpec C) σ')
    (k : σ' → α → β) (n : ℕ) (h : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) n) :
    IsQueryBoundP (oa >>= fun p => liftComp ($ᵗ α) (LocalSpec C) >>= fun f => pure (k p f)) (SplitRegionCounted SplitHashDomain) n :=
  (isQueryBoundP_bind (m := 0) h fun p _ =>
    isQueryBoundP_bind (n := 0) (m := 0) (split_prob_lift_no_digest _) fun _ _ => isQueryBoundP_pure _ _ 0).mono
    (by omega)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma split_sample_bind_digestBound {σ' α : Type} [SampleableType α] (ans : α → OracleComp (LocalSpec C) σ')
    (n : ℕ) (h : ∀ a, IsQueryBoundP (ans a) (SplitRegionCounted SplitHashDomain) n) :
    IsQueryBoundP (liftComp ($ᵗ α) (LocalSpec C) >>= fun v => ans v >>= fun pa => pure (v, pa)) (SplitRegionCounted SplitHashDomain) n :=
  (isQueryBoundP_bind (n := 0) (m := n) (split_prob_lift_no_digest _) fun v _ =>
    (isQueryBoundP_bind (n := n) (m := 0) (h v) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)).mono (by omega)

lemma split_coinDraw_digestBound (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State) :
    IsQueryBoundP (coinDraw D Ad st) (SplitRegionCounted SplitHashDomain) step := by
  unfold coinDraw
  refine split_sample_bind_digestBound _ step fun v => ?_
  apply (counted_splitRegionBound SplitHashDomain)
  dsimp only [leftAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

lemma split_extend_digestBound (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State)
    (inputs : C.Party → Option (List (Product C E))) (h : ∀ i, i ∉ D.1 → (inputs i).isSome) :
    IsQueryBoundP (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st inputs)
      (SplitRegionCounted SplitHashDomain) step := by
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st inputs h]
  refine split_bind_sample_digestBound _ _ step ?_
  apply (counted_splitRegionBound SplitHashDomain)
  dsimp only [leftAdversary, rightAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)


lemma split_finalReplies_digestBound (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State)
    (view : Ad.State × Shares C E × (C.Party → C.Party → ℕ → E) → C.Party → List (Product C E)) :
    IsQueryBoundP (do
      let p ← (leftAdversary (rightAdversary Ad)).answer st ()
      let p' ← (rightAdversary (leftAdversary Ad)).answer p.1 (view p)
      pure (p, p')) (SplitRegionCounted SplitHashDomain) (step + step) := by
  have h1 : IsQueryBoundP ((leftAdversary (rightAdversary Ad)).answer st ()) (SplitRegionCounted SplitHashDomain) step := by
    apply (counted_splitRegionBound SplitHashDomain)
    dsimp only [leftAdversary, rightAdversary]
    simp only [bind_assoc, pure_bind]
    exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  have h2 : ∀ (s : Ad.State) (l : C.Party → List (Product C E)),
      IsQueryBoundP ((rightAdversary (leftAdversary Ad)).answer s l) (SplitRegionCounted SplitHashDomain) step := by
    intro s l
    apply (counted_splitRegionBound SplitHashDomain)
    dsimp only [leftAdversary, rightAdversary]
    simp only [bind_assoc, pure_bind]
    exact (isQueryBoundP_bind (m := 0) (ha s _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  exact isQueryBoundP_bind h1 fun p _ =>
    (isQueryBoundP_bind (m := 0) (h2 p.1 (view p)) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)


lemma split_rl_answer_bound (Ad : CheckAdversary C E Ia) (step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State) (v : C.Party → List (Product C E)) :
    IsQueryBoundP ((rightAdversary (leftAdversary Ad)).answer st v) (SplitRegionCounted SplitHashDomain) step := by
  apply (counted_splitRegionBound SplitHashDomain)
  dsimp only [leftAdversary, rightAdversary]
  simp only [bind_assoc, pure_bind]
  exact (isQueryBoundP_bind (m := 0) (ha st _) (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)




lemma split_sequenceFin_digestBound : ∀ {n : ℕ} (oa : Fin n → OracleComp (LocalSpec C) α) (p : ℕ),
    (∀ i,IsQueryBoundP (oa i) (SplitRegionCounted SplitHashDomain) p) →
      IsQueryBoundP (Concrete.sequenceFin oa) (SplitRegionCounted SplitHashDomain) (n*p)
  | 0,oa,p,h => isQueryBoundP_pure _ _ _
  | n+1,oa,p,h => by
    simp only [Concrete.sequenceFin]
    have hb := isQueryBoundP_bind (h 0) (fun a _ =>
      isQueryBoundP_bind (split_sequenceFin_digestBound (fun i : Fin n => oa i.succ) p (fun i => h i.succ))
        (fun b _ => isQueryBoundP_pure (SplitRegionCounted SplitHashDomain) (Fin.cases (motive := fun _ => α) a b) 0))
    simpa [Nat.succ_mul,Nat.add_comm] using hb

lemma split_oneDigest_bound (salt hist : List Bit) :
    IsQueryBoundP (liftComp (oneDigestQuery (C := C) salt hist) (LocalSpec C))
      (SplitRegionCounted SplitHashDomain) 2 := by
  unfold oneDigestQuery
  rw [liftComp_bind]
  apply isQueryBoundP_bind (n := 1) (m := 1)
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl (.history hist))))) _ 1
    rw [isQueryBoundP_query_iff]
    simp
  · intro h _
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl (.digest salt h))))) _ 1
    rw [isQueryBoundP_query_iff]
    simp

lemma split_column_bound (D : C.Coalition) (T : C.Term)
    (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit) :
    IsQueryBoundP (Concrete.sequenceFin (honestDigestColumn D T salts hist))
      (SplitRegionCounted SplitHashDomain) (C.n * 2) := by
  apply split_sequenceFin_digestBound
  intro i
  unfold honestDigestColumn
  split_ifs
  · exact split_oneDigest_bound _ _
  · exact isQueryBoundP_pure _ _ _

lemma split_ghost_bound (D : C.Coalition) (salts : C.Party → Shares C Bit)
    (hist : C.Party → C.Term → List Bit) (Ts : List C.Term) :
    IsQueryBoundP (mixedGhostDigests D
      (fun T => Concrete.sequenceFin (honestDigestColumn D T salts hist)) Ts pure)
      (SplitRegionCounted SplitHashDomain) (Ts.length * (C.n * 2)) := by
  induction Ts with
  | nil => simp [mixedGhostDigests]
  | cons T Ts ih =>
    simp only [mixedGhostDigests]
    split_ifs
    · refine (isQueryBoundP_bind (m := Ts.length * (C.n * 2)) (split_column_bound D T salts hist) (fun col _ => ?_)).mono ?_
      · rw [mixedGhostDigests_bind_pure]
        exact (isQueryBoundP_bind ih (fun cols _ => isQueryBoundP_pure _ (col :: cols) 0)).mono (by omega)
      · simp [Nat.add_mul] <;> omega
    · refine (isQueryBoundP_bind (m := Ts.length * (C.n * 2)) (split_prob_lift_no_digest ($ᵗ HashOutput)) (fun d _ => ?_)).mono ?_
      · rw [mixedGhostDigests_bind_pure]
        exact (isQueryBoundP_bind ih (fun cols _ => isQueryBoundP_pure _ (digestColumnValues D T d :: cols) 0)).mono (by omega)
      · simp [Nat.add_mul] <;> omega

lemma split_ghost_terms_bound (D : C.Coalition) (salts : C.Party → Shares C Bit)
    (hist : C.Party → C.Term → List Bit) :
    IsQueryBoundP (mixedGhostDigests D
      (fun T => Concrete.sequenceFin (honestDigestColumn D T salts hist)) C.terms pure)
      (SplitRegionCounted SplitHashDomain) (termHashes C) := by
  convert split_ghost_bound D salts hist C.terms using 1
  rw [check_terms_length]
  unfold termHashes termCount
  ring

theorem splitGhostSalt_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel : ℕ) (p0 : Ad.State) (known knownQ : Shares C E) (attack : ℕ → E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (hrecv : ∀ i, i ∉ D.1 → i ∈ receivers)
    (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (htagR : ∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L)
    (htagD : ∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L)
    (hknownHist : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T)
    (AR BR VR AD BD VD : C.Party → E)
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (step k : ℕ) (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    (cache : HashCache C) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        saltGhostPhase K D Ad (fuel + 2) p0
          (finalHs K hsR (finalOut K D AR BR known attack knownQ offset receivers w q))
          (fun i _ => finalTail K D known knownQ attack offset receivers AR BR VR w q i) tailR)).run' cache)
      ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        saltGhostPhase K D Ad (fuel + 2) p0
          (finalHs K hsD (finalOut K D AD BD known attack knownQ offset receivers w q))
          (fun i _ => finalTail K D known knownQ attack offset receivers AD BD VD w q i) tailD)).run' cache) ≤ splitRisk k (step + termHashes C) := by
  -- the known digest columns do not depend on the side or on the tables
  let hist0 : C.Party → C.Term → List Bit := fun j =>
    (finalHs K hsR (finalOut K D AR BR known attack knownQ offset receivers 0 0) j).history
  let known0 : SaltReply Ad → C.Term → OracleComp (LocalSpec C) (DigestColumn C) := fun p T =>
    Concrete.sequenceFin (honestDigestColumn D T (randShares D 256 p.2.1 0) hist0)
  have hcol : ∀ (A B : C.Party → E) (hs : C.Party → RunState C)
      (hh : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hs i).history T = (hsR i).history T)
      (w q : MaskTable C E) (p : SaltReply Ad) (T : C.Term), KnownTo D.1 T →
      Concrete.sequenceFin (honestDigestColumn D T (randShares D 256 p.2.1 0)
        (fun j => (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) j).history)) =
        known0 p T := by
    intro A B hs hh w q p T hT
    congr 1
    funext i
    unfold honestDigestColumn
    by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
    · have he : (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i).history T =
          hist0 i T := by
        simp only [hist0, finalHs, finalState, recordHistory, if_pos hi.2, hh T hT i hi.1 hi.2]
        rw [finalOut_known K D A B AR BR known attack knownQ offset receivers w q 0 0 i T hT]
      simp only [if_pos hi, he]
    · simp only [if_neg hi]
  let OB : OracleComp (LocalSpec C) (SaltReply Ad × List (DigestColumn C)) :=
    (rightAdversary (rightAdversary Ad)).answer p0 () >>= fun p =>
      mixedGhostDigests D (known0 p) C.terms pure >>= fun cols => pure (p, cols)
  have side : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C)
      (hh : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hs i).history T = (hsR i).history T)
      (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β),
      SameRun prims
        (do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          saltGhostPhase K D Ad (fuel + 2) p0
            (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q))
            (fun i _ => finalTail K D known knownQ attack offset receivers A B V w q i) tail)
        (OB >>= fun x => do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) x.1.1
            (fun i => afterDigests i (digestRows x.2 i)
              ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
                (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) >>=
            tail) := by
    intro A B V hs hh tail
    refine SameRun.trans (SameRun.of_eq ?_) (sameRun_samples_swap prims OB (fun w q x =>
      executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) x.1.1
        (fun i => afterDigests i (digestRows x.2 i)
          ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
            (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) >>= tail))
    refine bind_congr fun w => bind_congr fun q => ?_
    unfold saltGhostPhase
    have hfun : saltGhostContinuation K D Ad (fuel + 2)
        (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q))
        (fun i _ => finalTail K D known knownQ attack offset receivers A B V w q i) tail =
        fun p => mixedGhostDigests D (known0 p) C.terms pure >>= fun cols =>
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) p.1
            (fun i => afterDigests i (digestRows cols i)
              ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
                (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) >>=
            tail := by
      funext p
      unfold saltGhostContinuation
      rw [mixedGhostDigests_congr D _ (known0 p) (hcol A B hs hh w q p), mixedGhostDigests_bind_pure]
    rw [hfun]
    exact ghost_reassoc _ _ _

  rw [tvDist_sameRun_congr prims
    (side AR BR VR hsR (fun _ _ _ _ _ => rfl) tailR)
    (side AD BD VD hsD (fun T hT i hi hh => (hknownHist T hT i hi hh).symm) tailD)]
  have hOB : IsQueryBoundP OB (SplitRegionCounted SplitHashDomain) (step + termHashes C) := by
    unfold OB
    apply isQueryBoundP_bind (counted_splitRegionBound SplitHashDomain (saltReply_queryBound Ad p0 step ha))
    intro p _
    exact (isQueryBoundP_bind (split_ghost_terms_bound D (randShares D 256 p.2.1 0) hist0)
      (fun cols _ => isQueryBoundP_pure _ (p, cols) 0)).mono (by omega)
  have hsplit' : SplitHistories D hist0 := hsplit.record K D
    (finalOut K D AR BR known attack knownQ offset receivers 0 0) 2
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine (split_tvDist_bind _ _ _
    (fun z : (SaltReply Ad × List (DigestColumn C)) × HashCache C =>
      CacheHasCollision (splitRegionCache SplitHashDomain z.2)) 0 le_rfl ?_).trans ?_
  · intro z hz hzn
    have hghost : ∃ s, (z.1.2, z.2) ∈ support ((simulateQ (localAnswer prims)
        (mixedGhostDigests D (known0 z.1.1) C.terms pure)).run s) := by
      change z ∈ support ((simulateQ (localAnswer prims) OB).run cache) at hz
      simp only [OB, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨p, s⟩, _, ⟨cols, s'⟩, hg, hz⟩ := hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨s, hg⟩
    obtain ⟨s, hg⟩ := hghost
    have hstop : ∀ sent i, i ∉ D.1 → ¬ digestLive (E := E) D (digestRows z.1.2) sent i := by
      intro sent i _
      exact split_ghost_abort prims D (randShares D 256 z.1.1.2.1 0) hist0 hsplit' s
        (z.1.2, z.2) hg hzn sent i
    have heq : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C) (w q : MaskTable C E),
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2) z.1.1.1
          (fun i => afterDigests i (digestRows z.1.2 i)
            ((finalTail K D known knownQ attack offset receivers A B V w q i).run'
              (afterSalt (finalHs K hs (finalOut K D A B known attack knownQ offset receivers w q) i)))) =
        (do
          let p ← Ad.round z.1.1.1 (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then digestOutbox i (digestRows z.1.2 i) c else none)
          pure (p.1, fun _ => none)) := by
      intro A B V hs w q
      exact split_afterDigests_abort K D Ad (fuel + 1) _ _ _ hstop
    simp only [← StateT.run'_eq, ← map_bind, ← StateT.run_bind, ← simulateQ_bind]
    simp only [heq]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      pure_bind, bind_assoc, StateT.run'_eq, map_bind, map_pure, htail, tvDist_self, le_refl]
  · simpa only [add_zero] using splitRegion_birthday_real prims OB (step + termHashes C) k hOB cache hno hk

theorem splitFinalMasked_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st1 : Ad.State)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (htagR : ∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L)
    (htagD : ∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L)
    (hknownHist : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T)
    (hcommonR : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsR i).history T = (hsR j).history T)
    (hcommonD : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsD i).history T = (hsD j).history T)
    (AR BR VR AD BD VD : C.Party → E)
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : ℕ) (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
          (finalMaskedProgram K D AR BR VR hsR known attack knownQ offset receivers w q) >>= tailR)).run' cache)
      ((simulateQ (localAnswer prims) (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
          (finalMaskedProgram K D AD BD VD hsD known attack knownQ offset receivers w q) >>= tailD)).run' cache) ≤
      splitBound C step final k (fuel + 3) := by
  have hB : (0 : ℝ) ≤ ((C.terms.length * (seen.card + (fuel + 2 + 1) * step + final +
      (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256 := by positivity
  by_cases hall : ∀ i, i ∉ D.1 → i ∈ receivers
  · have h1 := finalSalt_hide prims K D Ad fuel step final hr ha st1 known knownQ attack offset receivers hall
      hsR hcommonR AR BR VR tailR hqR cache seen hc
    have h3 := finalSalt_hide prims K D Ad fuel step final hr ha st1 known knownQ attack offset receivers hall
      hsD hcommonD AD BD VD tailD hqD cache seen hc
    have h2 := splitGhostSalt_tv prims K D Ad fuel st1 known knownQ attack offset receivers hall
      tg L hsR hsD htagR htagD hknownHist AR BR VR AD BD VD hsplit tailR tailD htail step k ha cache hk hno
    have hhide : ((C.terms.length * (seen.card + (fuel + 2 + 1) * step + final +
        (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256 ≤
        coupleBound C step final k (fuel + 3) / 2 := by
      unfold coupleBound
      have he : (2 : ℝ) * (↑(C.terms.length * (k + (fuel + 3) * step + final +
          (C.n + 1) * C.terms.length)) / 2 ^ 256) / 2 =
          ↑(C.terms.length * (k + (fuel + 3) * step + final +
          (C.n + 1) * C.terms.length)) / 2 ^ 256 := by ring
      rw [he]
      gcongr
    have hrisk := splitRisk_mono (k := k) le_rfl
      (n := step + termHashes C) (n' := (fuel + 3) * step + termHashes C)
      (by nlinarith)
    have h3' : tvDist _ _ ≤ _ := (tvDist_comm _ _).le.trans h3
    have ht := (tvDist_triangle _ _ _).trans (add_le_add h1
      ((tvDist_triangle _ _ _).trans (add_le_add h2 h3')))
    unfold splitBound
    linarith
  · push Not at hall
    have hmiss : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C)
        (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β),
        (do
          let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) st1
            (finalMaskedProgram K D A B V hs known attack knownQ offset receivers w q) >>= tail) =
        (do
          let _w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          let _q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
          tail (st1, fun _ => none)) := by
      intro A B V hs tail
      refine bind_congr fun w => bind_congr fun q => ?_
      rw [finalMasked_missing K D Ad (fuel + 2) st1 A B V hs known attack knownQ offset receivers w q hall, pure_bind]
    simp only [hmiss, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _

lemma split_tvDist_rounds (prims : Primitives) {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) β) (step final fuel rounds k : ℕ)
    (hq : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) (rounds * step))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache))
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ k + rounds * step → SplitCacheBound (splitRegionCache SplitHashDomain cache') (k + rounds * step) →
      ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache') →
      tvDist ((simulateQ (localAnswer prims) (f a)).run' cache')
        ((simulateQ (localAnswer prims) (g a)).run' cache') ≤ splitBound C step final (k + rounds * step) fuel) :
    tvDist ((simulateQ (localAnswer prims) (oa >>= f)).run' cache)
      ((simulateQ (localAnswer prims) (oa >>= g)).run' cache) ≤ splitBound C step final k (fuel + rounds) := by
  rw [← splitBound_prefix]
  exact split_tvDist_prefix prims oa f g _ k hq cache seen hc hcard hk hno _ (splitBound_nonneg ..) h

lemma split_tvDist_zero (prims : Primitives) {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) β) (k : ℕ)
    (hq : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) 0)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) (c : ℝ) (hc0 : 0 ≤ c)
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ k → SplitCacheBound (splitRegionCache SplitHashDomain cache') k →
      ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache') →
      tvDist ((simulateQ (localAnswer prims) (f a)).run' cache')
        ((simulateQ (localAnswer prims) (g a)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) (oa >>= f)).run' cache)
      ((simulateQ (localAnswer prims) (oa >>= g)).run' cache) ≤ c := by
  simpa only [splitRisk, Nat.add_zero, sub_self, zero_div, zero_add] using
    split_tvDist_prefix prims oa f g 0 k hq cache seen hc hcard hk hno c hc0 h

theorem splitFinalStep_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State)
    (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (htagR : ∀ i, i ∉ D.1 → (hsR i).tag = tg ∧ (hsR i).label = L)
    (htagD : ∀ i, i ∉ D.1 → (hsD i).tag = tg ∧ (hsD i).label = L)
    (hknownHist : ∀ T, KnownTo D.1 T → ∀ i, i ∉ D.1 → i ∈ C.holders T → (hsR i).history T = (hsD i).history T)
    (hcommonR : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsR i).history T = (hsR j).history T)
    (hcommonD : ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hsD i).history T = (hsD j).history T)
    (AvR BvR AvD BvD : C.Party → ℕ → E) (VR VD : C.Party → E)
    (hrel : SplitHalvRel K D AvR BvR AvD BvD VR VD)
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : ℕ) (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3 + 2) st
          (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (AvR i, BvR i, VR i)).run' (hsR i)) >>=
          tailR)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3 + 2) st
          (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (AvD i, BvD i, VD i)).run' (hsD i)) >>=
          tailD)).run' cache) ≤
      splitBound C step final k (fuel + 3 + 2) := by
  have hview : ∀ known : Shares C E, maskedView K D known 0 (fun j => AvD j 0) (fun j => BvD j 0) =
      maskedView K D known 0 (fun j => AvR j 0) (fun j => BvR j 0) := by
    intro known
    exact (splitMaskedView K D known (hrel.1 0) (hrel.2.1 0)).symm
  rw [tvDist_sameRun_congr prims
    ((finalStep_masks prims K D Ad (fuel + 3) st AvR BvR VR hsR).bind fun out => SameRun.refl prims (tailR out))
    ((finalStep_masks prims K D Ad (fuel + 3) st AvD BvD VD hsD).bind fun out => SameRun.refl prims (tailD out))]
  simp only [hview]
  let OB := (do
    let p ← (leftAdversary (rightAdversary Ad)).answer st ()
    let p' ← (rightAdversary (leftAdversary Ad)).answer p.1
      (maskedView K D p.2.1 0 (fun j => AvR j 0) (fun j => BvR j 0))
    pure (p, p'))
  have hform : ∀ (A B V : C.Party → E) (hs : C.Party → RunState C)
      (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β),
      (do
        let p ← (leftAdversary (rightAdversary Ad)).answer st ()
        let p' ← (rightAdversary (leftAdversary Ad)).answer p.1
          (maskedView K D p.2.1 0 (fun j => AvR j 0) (fun j => BvR j 0))
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) p'.1
          (finalMaskedProgram K D A B V hs p.2.1 p'.2.1 p'.2.2.1 p'.2.2.2.1 p'.2.2.2.2 w q)) >>= tail =
      OB >>= fun x => (do
        let w ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        let q ← liftComp ($ᵗ (MaskTable C E)) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) (fuel + 3) x.2.1
          (finalMaskedProgram K D A B V hs x.1.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 w q) >>= tail) := by
    intro A B V hs tail
    simp only [OB, bind_assoc, pure_bind]
  rw [hform, hform]
  refine split_tvDist_rounds prims OB _ _ step final (fuel + 3) 2 k
    (by simpa only [two_mul] using (split_finalReplies_digestBound Ad step ha st
      (fun p => maskedView K D p.2.1 0 (fun j => AvR j 0) (fun j => BvR j 0))))
    cache seen hc hcard hk hno ?_
  intro x cache' seen' hc' hcard' hk' hno'
  exact splitFinalMasked_tv prims K D Ad fuel step final hr ha x.2.1 x.1.2.1 x.2.2.2.1 x.2.2.1 x.2.2.2.2.1
    x.2.2.2.2.2 tg L hsR hsD htagR htagD hknownHist hcommonR hcommonD _ _ VR _ _ VD hsplit tailR tailD htail hqR hqD
    cache' seen' hc' (k + 2 * step) hcard' hk' hno'

theorem splitFinalStep_live_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (fuel step final : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live]
    (tg L : ℕ) (hsR hsD : C.Party → RunState C) (hh : HistRel D tg L hsR hsD)
    (AvR BvR AvD BvD : C.Party → ℕ → E) (VR VD : C.Party → E)
    (hrel : SplitHalvRel K D AvR BvR AvD BvD VR VD)
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : ℕ) (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 5) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (AvR i, BvR i, VR i)).run' (hsR i)
            else failure) >>= tailR)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 5) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (AvD i, BvD i, VD i)).run' (hsD i)
            else failure) >>= tailD)).run' cache) ≤
      splitBound C step final k (fuel + 5) := by
  obtain ⟨htagR, htagD, hknownHist, hcommonR, hcommonD⟩ := hh
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · rw [executePhase_congr_honest D Ad _ _ st _ _ (fun i hi => if_pos (hall i hi)),
      executePhase_congr_honest D Ad _ _ st (fun i => if live i then _ else failure) _ (fun i hi => if_pos (hall i hi))]
    exact splitFinalStep_tv prims K D Ad fuel step final hr ha st tg L hsR hsD htagR htagD hknownHist hcommonR hcommonD
      AvR BvR AvD BvD VR VD hrel hsplit tailR tailD htail hqR hqD cache seen hc k hcard hk hno
  · push Not at hall
    rw [finalStep_missing K D Ad (fuel + 4) st live hsR AvR BvR VR hall,
      finalStep_missing K D Ad (fuel + 4) st live hsD AvD BvD VD hall]
    simp only [pure_bind, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _

def SplitHalvRest (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width n j F : ℕ) {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    Prop :=
  ∀ (st : Ad.State) (live : Finset C.Party) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E) (cache : HashCache C) (seen : Finset (List Bit)) (k : ℕ),
    SplitHalvRel K D AR BR AD BD DR DD → HistRel D tg L hsR hsD →
    SplitHistories D (fun i => (hsR i).history) →
    DigestSaltsCovered cache seen → seen.card ≤ k →
    SplitCacheBound (splitRegionCache SplitHashDomain cache) k →
    ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache) →
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (halvProg K width n j (AR i) (BR i) (DR i) i).run' (hsR i) else failure) >>=
          tailR)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (halvProg K width n j (AD i) (BD i) (DD i) i).run' (hsD i) else failure) >>=
          tailD)).run' cache) ≤
      splitBound C step final k F

/-- The last halving state leads into the final segment. -/
theorem splitHalvRest_zero (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width fuel : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final) :
    SplitHalvRest prims K D Ad step final width 0 (halvingSteps width) (fuel + 5) tailR tailD := by
  intro st live tg L hsR hsD AR BR AD BD DR DD cache seen k hrel hh hsplit hc hcard hk hno
  simp only [halvProg_zero]
  exact splitFinalStep_live_tv prims K D Ad fuel step final hr ha st (· ∈ live) tg L hsR hsD hh AR BR AD BD DR DD
    hrel hsplit tailR tailD htail hqR hqD cache seen hc k hcard hk hno


theorem splitHalvCoin_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width n j F : ℕ) {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hIH : SplitHalvRest prims K D Ad step final width n (j + 1) F tailR tailD) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD) (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E)
    (hrel : SplitHalvRel K D AR BR AD BD DR DD)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2)
    (y : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    (k : ℕ) (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsR i).history (halvOut K D (halvedLength^[j] width) AR BR pa fresh i) 2,
          (hsR i).label + 1, (hsR i).tag⟩)
        (halvCont K width n j AR BR DR (halvOut K D (halvedLength^[j] width) AR BR pa fresh)) tailR y)).run' cache)
      ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsD i).history (halvOut K D (halvedLength^[j] width) AD BD pa fresh i) 2,
          (hsD i).label + 1, (hsD i).tag⟩)
        (halvCont K width n j AD BD DD (halvOut K D (halvedLength^[j] width) AD BD pa fresh)) tailD y)).run' cache) ≤
      splitBound C step final k F := by
  have hrel' := splitHalv_after K D (halvedLength^[j] width) hrel pa fresh hrec
  have hh' := splitHalv_hist K D (halvedLength^[j] width) tg L AR BR AD BD hsR hsD hh pa fresh hrec
  have hsplit' := hsplit.record K D (halvOut K D (halvedLength^[j] width) AR BR pa fresh) 2
  have htagR := hh.1
  have htagD := hh.2.1
  by_cases hy : ∃ i, i ∉ D.1 ∧ i ∈ y.2.2
  · unfold halvCoinNext
    rw [tvDist_sameRun_congr prims
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagR i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tailR out))
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagD i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tailD out)),
      bind_assoc, bind_assoc]
    refine split_tvDist_zero prims _ _ _ k (split_challengeQuery_no_digest K tg (L + 1) (List.ofFn y.1))
      cache seen hc hcard hk hno _ (splitBound_nonneg ..) ?_
    intro r cache' seen' hc' hcard' hk' hno'
    rcases r with _ | r
    · simp only [executePhase_failure, pure_bind, htail, tvDist_self]
      exact splitBound_nonneg _ _ _ _
    · exact hIH y.2.1 y.2.2 tg (L + 1 + 1) _ _ _ _ _ _ _ _ cache' seen' k
        (hrel' r) hh' hsplit' hc' hcard' hk' hno'
  · push Not at hy
    have hfail : ∀ (hs : C.Party → RunState C) (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
        (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β),
        halvCoinNext K D Ad F hs g tail y = tail (y.2.1, fun _ => none) := by
      intro hs g tail
      unfold halvCoinNext
      rw [executePhase_congr_honest D Ad _ F y.2.1 _ (fun _ => failure), executePhase_failure, pure_bind]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ y.2.2) := fun h => hy i h.1 h.2
      simp only [hn, if_false, afterChallenge]
    rw [hfail, hfail, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _

lemma split_tvDist_rounds_tail (prims : Primitives) {α γ β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) γ) (tailR tailD : γ → OracleComp (LocalSpec C) β) (step final fuel rounds k : ℕ)
    (hq : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) (rounds * step))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache))
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ k + rounds * step → SplitCacheBound (splitRegionCache SplitHashDomain cache') (k + rounds * step) →
      ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache') →
      tvDist ((simulateQ (localAnswer prims) (f a >>= tailR)).run' cache')
        ((simulateQ (localAnswer prims) (g a >>= tailD)).run' cache') ≤ splitBound C step final (k + rounds * step) fuel) :
    tvDist ((simulateQ (localAnswer prims) ((oa >>= f) >>= tailR)).run' cache)
      ((simulateQ (localAnswer prims) ((oa >>= g) >>= tailD)).run' cache) ≤ splitBound C step final k (fuel + rounds) := by
  rw [bind_assoc, bind_assoc]
  exact split_tvDist_rounds prims oa _ _ step final fuel rounds k hq cache seen hc hcard hk hno h

lemma split_tvDist_zero_tail (prims : Primitives) {α γ β : Type} (oa : OracleComp (LocalSpec C) α)
    (f g : α → OracleComp (LocalSpec C) γ) (tailR tailD : γ → OracleComp (LocalSpec C) β) (k : ℕ)
    (hq : IsQueryBoundP oa (SplitRegionCounted SplitHashDomain) 0)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) (c : ℝ) (hc0 : 0 ≤ c)
    (h : ∀ a (cache' : HashCache C) (seen' : Finset (List Bit)), DigestSaltsCovered cache' seen' →
      seen'.card ≤ k → SplitCacheBound (splitRegionCache SplitHashDomain cache') k →
      ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache') →
      tvDist ((simulateQ (localAnswer prims) (f a >>= tailR)).run' cache')
        ((simulateQ (localAnswer prims) (g a >>= tailD)).run' cache') ≤ c) :
    tvDist ((simulateQ (localAnswer prims) ((oa >>= f) >>= tailR)).run' cache)
      ((simulateQ (localAnswer prims) ((oa >>= g) >>= tailD)).run' cache) ≤ c := by
  rw [bind_assoc, bind_assoc]
  exact split_tvDist_zero prims oa _ _ k hq cache seen hc hcard hk hno c hc0 h

theorem splitHalvRest_succ (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width n j F : ℕ) (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hIH : SplitHalvRest prims K D Ad step final width n (j + 1) F tailR tailD) :
    SplitHalvRest prims K D Ad step final width (n + 1) j (F + 1 + 1) tailR tailD := by
  intro st live tg L hsR hsD AR BR AD BD DR DD cache seen k hrel hh hsplit hc hcard hk hno
  by_cases hall : ∀ i, i ∉ D.1 → i ∈ live
  swap
  · rw [halvExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsR width n j AR BR DR,
      halvExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsD width n j AD BD DD]
    simp only [pure_bind, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _
  rw [halvExtend_local K D Ad (F + 1) st (· ∈ live) hall hsR width n j AR BR DR,
    halvExtend_local K D Ad (F + 1) st (· ∈ live) hall hsD width n j AD BD DD,
    ← splitHalvRel_inputs_view K D _ hrel]
  have hq1 := split_rl_answer_bound Ad step ha st (extendView K D.1 (halvInputs D (halvedLength^[j] width) AR BR))
  refine split_tvDist_rounds_tail prims _ _ _ tailR tailD step final (F + 1) 1 k
    (by simpa only [one_mul] using hq1) cache seen hc hcard hk hno ?_
  intro pa cache1 seen1 hc1 hcard1 hk1 hno1
  simp only [one_mul] at hcard1 hk1 ⊢
  refine split_tvDist_zero_tail prims _ _ _ tailR tailD (k + step) (split_prob_lift_no_digest _)
    cache1 seen1 hc1 hcard1 hk1 hno1 _ (splitBound_nonneg ..) ?_
  intro fresh cache2 seen2 hc2 hcard2 hk2 hno2
  rw [halvAfter_form K D Ad (F + 1) pa.1 hsR width n j AR BR DR pa fresh,
    halvAfter_form K D Ad (F + 1) pa.1 hsD width n j AD BD DD pa fresh]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  · rw [halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tailR, halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tailD]
    refine split_tvDist_rounds prims (coinDraw D Ad pa.1) _ _ step final F 1 (k + step)
      (by simpa only [one_mul] using split_coinDraw_digestBound D Ad step ha pa.1)
      cache2 seen2 hc2 hcard2 hk2 hno2 ?_
    intro y cache3 seen3 hc3 hcard3 hk3 hno3
    exact splitHalvCoin_tv prims K D Ad step final width n j F tailR tailD htail hIH tg L hsR hsD hh AR BR AD BD DR DD
      hrel pa fresh hrec y cache3 seen3 hc3 hsplit (k + step + 1 * step) hcard3 hk3 hno3
  · rw [executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec,
      executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec]
    simp only [pure_bind, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _

theorem splitHalvRest_all (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (step final width : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final) :
    ∀ n j fuel, j + n = halvingSteps width →
      SplitHalvRest prims K D Ad step final width n j (fuel + 2 * n + 5) tailR tailD
  | 0, j, fuel, h => by
    simp only [Nat.add_zero] at h
    subst h
    simpa using splitHalvRest_zero prims K D Ad step final width fuel hr ha hw tailR tailD htail hqR hqD
  | n + 1, j, fuel, h => by
    have he : fuel + 2 * (n + 1) + 5 = fuel + 2 * n + 5 + 1 + 1 := by ring
    rw [he]
    exact splitHalvRest_succ prims K D Ad step final width n j (fuel + 2 * n + 5) ha tailR tailD htail
      (splitHalvRest_all prims K D Ad step final width hr ha hw tailR tailD htail hqR hqD n (j + 1) fuel (by omega))


def SplitSliceRest (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E)
    (count step final n j F : ℕ) {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    Prop :=
  ∀ (st : Ad.State) (live : Finset C.Party) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E) (cache : HashCache C) (seen : Finset (List Bit)) (k : ℕ),
    SplitSliceRel D xsR ysR xsD ysD → ShamirDifference K D DR DD → HistRel D tg L hsR hsD →
    SplitHistories D (fun i => (hsR i).history) →
    DigestSaltsCovered cache seen → seen.card ≤ k →
    SplitCacheBound (splitRegionCache SplitHashDomain cache) k →
    ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache) →
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (sliceProg K τ count n j (xsR i) (ysR i) (DR i) i).run' (hsR i) else failure) >>=
          tailR)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (sliceProg K τ count n j (xsD i) (ysD i) (DD i) i).run' (hsD i) else failure) >>=
          tailD)).run' cache) ≤
      splitBound C step final k F

theorem splitSliceCoin_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final n j F : ℕ) (hj : j < sliceBits) (hw : 0 < sliceWidth count)
    (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hIH : SplitSliceRest prims K D Ad τ count step final n (j + 1) F tailR tailD) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD) (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E)
    (hrel : SplitSliceRel D xsR ysR xsD ysD) (hdiff : ShamirDifference K D DR DD)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2)
    (y : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party))
    (cache : HashCache C) (seen : Finset (List Bit)) (hcov : DigestSaltsCovered cache seen)
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    (k : ℕ) (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsR i).history (sliceOut K D τ count j xsR ysR pa fresh i) 2,
          (hsR i).label + 1, (hsR i).tag⟩)
        (sliceCont K τ count n j xsR ysR DR (sliceOut K D τ count j xsR ysR pa fresh)) tailR y)).run' cache)
      ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsD i).history (sliceOut K D τ count j xsD ysD pa fresh i) 2,
          (hsD i).label + 1, (hsD i).tag⟩)
        (sliceCont K τ count n j xsD ysD DD (sliceOut K D τ count j xsD ysD pa fresh)) tailD y)).run' cache) ≤
      splitBound C step final k F := by
  have hrel' := fun r => splitSliceRel_fold D count j r xsR ysR xsD ysD hrel
  have hdiff' := splitSlice_claim K D τ count j xsR ysR xsD ysD hdiff pa fresh hrec
  have hh' := splitSlice_hist K D τ count j xsR ysR xsD ysD tg L hsR hsD hh pa fresh hrec
  have hsplit' := hsplit.record K D (sliceOut K D τ count j xsR ysR pa fresh) 2
  have htagR := hh.1
  have htagD := hh.2.1
  by_cases hy : ∃ i, i ∉ D.1 ∧ i ∈ y.2.2
  · unfold halvCoinNext
    rw [tvDist_sameRun_congr prims
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagR i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tailR out))
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagD i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tailD out)),
      bind_assoc, bind_assoc]
    refine split_tvDist_zero prims _ _ _ k (split_challengeQuery_no_digest K tg (L + 1) (List.ofFn y.1))
      cache seen hcov hcard hk hno _ (splitBound_nonneg ..) ?_
    intro r cache' seen' hc' hcard' hk' hno'
    rcases r with _ | r
    · simp only [executePhase_failure, pure_bind, htail, tvDist_self]
      exact splitBound_nonneg _ _ _ _
    · exact hIH y.2.1 y.2.2 tg (L + 1 + 1) _ _ _ _ _ _ _ _ cache' seen' k
        (hrel' r) (hdiff' r) hh' hsplit' hc' hcard' hk' hno'
  · push Not at hy
    have hfail : ∀ (hs : C.Party → RunState C) (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
        (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β),
        halvCoinNext K D Ad F hs g tail y = tail (y.2.1, fun _ => none) := by
      intro hs g tail
      unfold halvCoinNext
      rw [executePhase_congr_honest D Ad _ F y.2.1 _ (fun _ => failure), executePhase_failure, pure_bind]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ y.2.2) := fun h => hy i h.1 h.2
      simp only [hn, if_false, afterChallenge]
    rw [hfail, hfail, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _


theorem splitSliceRest_succ (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final n j F : ℕ) (hj : j < sliceBits) (hw : 0 < sliceWidth count)
    (hcoef : τ.getD (sliceBits - 1 - j) 0 ≠ 0) (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hIH : SplitSliceRest prims K D Ad τ count step final n (j + 1) F tailR tailD) :
    SplitSliceRest prims K D Ad τ count step final (n + 1) j (F + 1 + 1) tailR tailD := by
  intro st live tg L hsR hsD xsR ysR xsD ysD DR DD cache seen k hrel hdiff hh hsplit hc hcard hk hno
  by_cases hall : ∀ i, i ∉ D.1 → i ∈ live
  swap
  · rw [sliceExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsR τ count n j xsR ysR DR,
      sliceExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsD τ count n j xsD ysD DD]
    simp only [pure_bind, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _
  rw [sliceExtend_local K D Ad (F + 1) st (· ∈ live) hall hsR τ count n j xsR ysR DR,
    sliceExtend_local K D Ad (F + 1) st (· ∈ live) hall hsD τ count n j xsD ysD DD,
    ← splitSliceInputs_view K D τ count j xsR ysR xsD ysD hrel]
  have hq1 := split_rl_answer_bound Ad step ha st (extendView K D.1 (sliceInputs D τ count j xsR ysR))
  refine split_tvDist_rounds_tail prims _ _ _ tailR tailD step final (F + 1) 1 k
    (by simpa only [one_mul] using hq1) cache seen hc hcard hk hno ?_
  intro pa cache1 seen1 hc1 hcard1 hk1 hno1
  simp only [one_mul] at hcard1 hk1 ⊢
  refine split_tvDist_zero_tail prims _ _ _ tailR tailD (k + step) (split_prob_lift_no_digest _)
    cache1 seen1 hc1 hcard1 hk1 hno1 _ (splitBound_nonneg ..) ?_
  intro fresh cache2 seen2 hc2 hcard2 hk2 hno2
  rw [sliceAfter_form K D Ad (F + 1) pa.1 hsR τ count n j xsR ysR DR pa fresh,
    sliceAfter_form K D Ad (F + 1) pa.1 hsD τ count n j xsD ysD DD pa fresh]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  · rw [halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tailR, halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tailD]
    refine split_tvDist_rounds prims (coinDraw D Ad pa.1) _ _ step final F 1 (k + step)
      (by simpa only [one_mul] using split_coinDraw_digestBound D Ad step ha pa.1)
      cache2 seen2 hc2 hcard2 hk2 hno2 ?_
    intro y cache3 seen3 hc3 hcard3 hk3 hno3
    exact splitSliceCoin_tv prims K D Ad τ count step final n j F hj hw hcoef tailR tailD htail hIH tg L hsR hsD hh xsR ysR xsD ysD DR DD
      hrel hdiff pa fresh hrec y cache3 seen3 hc3 hsplit (k + step + 1 * step) hcard3 hk3 hno3
  · rw [executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec,
      executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec]
    simp only [pure_bind, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _

theorem splitSliceRest_zero (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final fuel : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final) :
    SplitSliceRest prims K D Ad τ count step final 0 sliceBits
      (fuel + 2 * halvingSteps (sliceWidth count) + 5) tailR tailD := by
  intro st live tg L hsR hsD xsR ysR xsD ysD DR DD cache seen k hrel hdiff hh hsplit hc hcard hk hno
  simp only [sliceProg_zero]
  exact splitHalvRest_all prims K D Ad step final (sliceWidth count) hr ha hw tailR tailD htail hqR hqD
    (halvingSteps (sliceWidth count)) 0 fuel (by simp) st live tg L hsR hsD _ _ _ _ DR DD cache seen k
    (splitSliceRel_halvRel K D hrel hdiff) hh hsplit hc hcard hk hno

theorem splitSliceRest_all (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final : ℕ) (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final) :
    ∀ n j fuel, j + n = sliceBits →
      SplitSliceRest prims K D Ad τ count step final n j (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5) tailR tailD
  | 0, j, fuel, h => by
    simp only [Nat.add_zero] at h
    subst h
    simpa using splitSliceRest_zero prims K D Ad τ count step final fuel hr ha hw tailR tailD htail hqR hqD
  | n + 1, j, fuel, h => by
    have he : fuel + 2 * (n + 1) + 2 * halvingSteps (sliceWidth count) + 5 =
        fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5 + 1 + 1 := by ring
    rw [he]
    exact splitSliceRest_succ prims K D Ad τ count step final n j _ (by omega) hw (hτ _ (by omega)) ha tailR tailD htail
      (splitSliceRest_all prims K D Ad τ count step final hτ hr ha hw tailR tailD htail hqR hqD n (j + 1) fuel (by omega))


lemma split_startQuery_no_digest (K : Constants C E) (tg L : ℕ) (v : List E) (d : ℕ) :
    IsQueryBoundP (liftComp (startQuery K tg L v d) (LocalSpec C)) (SplitRegionCounted SplitHashDomain) 0 := by
  simp only [startQuery, liftComp_bind]
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (split_hashQuery_no_digest _ (by simp [SplitRegionCounted, splitLocalHashInput, SplitHashDomain, IsFixed])) fun key _ => ?_
  generalize List.range d = l
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_map]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => ?_
    · rw [map_eq_bind_pure_comp]
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (split_hashQuery_no_digest _ (by simp [SplitRegionCounted, splitLocalHashInput, SplitHashDomain, IsFixed])) fun _ _ => by simp
    · exact isQueryBoundP_bind (n := 0) (m := 0) ih fun _ _ => by simp

theorem splitStart_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (count step final fuel : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    {β : Type} (tailR tailD : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (htail : ∀ st, tailR (st, fun _ => none) = tailD (st, fun _ => none))
    (hqR : ∀ out, IsQueryBoundP (tailR out) Counted final)
    (hqD : ∀ out, IsQueryBoundP (tailD out) Counted final) (st : Ad.State) (tg L : ℕ)
    (hsR hsD : C.Party → RunState C) (hh : HistRel D tg L hsR hsD) (XR YR ZR XD YD ZD : C.Party → Shares C E)
    (hrel : ∀ τ : List E, SplitSliceRel D
      (fun i T k => wordWeightOf K τ count k * XR i T k) YR
      (fun i T k => wordWeightOf K τ count k * XD i T k) YD)
    (hdiff : ∀ τ : List E, ShamirDifference K D
      (fun i => conv K (localContext i) (claimOf K τ count (ZR i)) 0)
      (fun i => conv K (localContext i) (claimOf K τ count (ZD i)) 0))
    (hsplit : SplitHistories D (fun i => (hsR i).history))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (k : ℕ) (hcard : seen.card ≤ k) (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)) :
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K)
          (fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 + 1) st
          (fun i => (startProg K count (XR i) (YR i) (ZR i) i).run' (hsR i)) >>= tailR)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K)
          (fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 + 1) st
          (fun i => (startProg K count (XD i) (YD i) (ZD i) i).run' (hsD i)) >>= tailD)).run' cache) ≤
      splitBound C step final k (fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 + 1) := by
  set F := fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 with hFdef
  unfold startProg
  rw [start_eq K D Ad F (coins count) st hsR _ tailR, start_eq K D Ad F (coins count) st hsD _ tailD]
  refine split_tvDist_rounds prims (coinDraw D Ad st) _ _ step final F 1 k
    (by simpa only [one_mul] using split_coinDraw_digestBound D Ad step ha st) cache seen hc hcard hk hno ?_
  intro y cache1 seen1 hc1 hcard1 hk1 hno1
  simp only [one_mul] at hcard1 hk1 ⊢
  have htagR := hh.1
  have htagD := hh.2.1
  by_cases hy : ∃ i, i ∉ D.1 ∧ i ∈ y.2.2
  · unfold startCoinNext
    rw [tvDist_sameRun_congr prims
      ((executePhase_afterStart_common prims K D Ad F (coins count) y.2.1 hsR tg L htagR (List.ofFn y.1) y.2.2 hy
        _).bind fun out => SameRun.refl prims (tailR out))
      ((executePhase_afterStart_common prims K D Ad F (coins count) y.2.1 hsD tg L htagD (List.ofFn y.1) y.2.2 hy
        _).bind fun out => SameRun.refl prims (tailD out)),
      bind_assoc, bind_assoc]
    refine split_tvDist_zero prims _ _ _ (k + step) (split_startQuery_no_digest K tg L (List.ofFn y.1) (coins count))
      cache1 seen1 hc1 hcard1 hk1 hno1 _ (splitBound_nonneg ..) ?_
    intro τ cache2 seen2 hc2 hcard2 hk2 hno2
    simp only [require_bind_run']
    by_cases hP : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [eq_true hP, if_true]
      exact splitSliceRest_all prims K D Ad τ count step final hP hr ha hw tailR tailD htail hqR hqD
        sliceBits 0 fuel (by simp) y.2.1 y.2.2 tg (L + 1) _ _ _ _ _ _ _ _ cache2 seen2 (k + step)
        (hrel τ) (hdiff τ) (histRel_label D tg L hsR hsD hh) hsplit hc2 hcard2 hk2 hno2
    · simp only [eq_false hP, if_false, ite_self, executePhase_failure, pure_bind, htail, tvDist_self]
      exact splitBound_nonneg _ _ _ _
  · push Not at hy
    have hfail : ∀ (hs : C.Party → RunState C) (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
        (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β),
        startCoinNext K D Ad F (coins count) hs g tail y = tail (y.2.1, fun _ => none) := by
      intro hs g tail
      unfold startCoinNext
      rw [executePhase_congr_honest D Ad _ F y.2.1 _ (fun _ => failure), executePhase_failure, pure_bind]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ y.2.2) := fun h => hy i h.1 h.2
      simp only [hn, if_false, afterStart]
    rw [hfail, hfail, htail, tvDist_self]
    exact splitBound_nonneg _ _ _ _


lemma SplitHistories.two_le_n {D : C.Coalition} {hist : C.Party → C.Term → List Bit}
    (h : SplitHistories D hist) : 2 ≤ C.n := by
  obtain ⟨T, _, i, j, _, _, _, _, _, hne⟩ := h
  have hij : i ≠ j := by rintro rfl; exact hne rfl
  have hi := i.isLt
  have hj := j.isLt
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  omega

lemma splitBudget_le (start step final fuel count q : ℕ) (hn : 2 ≤ C.n)
    (hq : start + fuel * step + final ≤ q) :
    splitRisk 0 start + splitBound C step final start fuel ≤ checkHashError C count q := by
  have hm : (0 : ℝ) ≤ C.terms.length := Nat.cast_nonneg _
  have hn' : (2 : ℝ) ≤ C.n := by exact_mod_cast hn
  have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ (C.n : ℝ) ^ 2 - C.n - 1 := by nlinarith
  have hnum : 4 * (C.terms.length : ℝ) * (q + ((C.n : ℝ) + 1) * C.terms.length) ≤
      ((q : ℝ) + 2 * C.n * C.terms.length) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ C.n by linarith)) hm) hq',
      mul_nonneg hnn (sq_nonneg (C.terms.length : ℝ)), sq_nonneg (q : ℝ)]
  have hH : (termHashes C : ℝ) = 2 * C.n * C.terms.length := by
    simp only [termHashes, Nat.cast_mul, Nat.cast_ofNat, check_terms_length, termCount]
  have hB : coupleBound C step final start fuel ≤
      ((q + termHashes C : ℕ) : ℝ) ^ 2 / (2 * 2 ^ 256) := by
    have hq'' : (start : ℝ) + fuel * step + final ≤ q := by exact_mod_cast hq
    unfold coupleBound
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hden : (0 : ℝ) < 2 ^ 256 := by positivity
    rw [hH]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ 256)).2
    have he : (2 * ((C.terms.length : ℝ) * (start + fuel * step + final +
        ((C.n : ℝ) + 1) * C.terms.length) / 2 ^ 256)) * (2 * 2 ^ 256) =
        4 * C.terms.length * (start + fuel * step + final + ((C.n : ℝ) + 1) * C.terms.length) := by
      field_simp
      <;> ring
    rw [he]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hq'')]
  have hR : splitRisk 0 start + splitRisk start (fuel * step + termHashes C) ≤
      ((q + termHashes C : ℕ) : ℝ) ^ 2 / (2 * 2 ^ 256) := by
    rw [show splitRisk 0 start + splitRisk start (fuel * step + termHashes C) =
      splitRisk 0 (start + (fuel * step + termHashes C)) by
        simpa only [zero_add] using splitRisk_add 0 start (fuel * step + termHashes C)]
    have h := splitRisk_mono (k := 0) le_rfl
      (n := start + (fuel * step + termHashes C)) (n' := q + termHashes C) (by omega)
    simpa only [splitRisk, zero_add, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using h
  unfold splitBound
  have hsum := add_le_add hB hR
  unfold checkHashError
  have hden : (0 : ℝ) < 2 ^ 256 := by positivity
  have he : ((q + termHashes C : ℕ) : ℝ) ^ 2 / (2 * 2 ^ 256) +
      ((q + termHashes C : ℕ) : ℝ) ^ 2 / (2 * 2 ^ 256) =
      ((q + termHashes C : ℕ) : ℝ) ^ 2 / 2 ^ 256 := by ring
  rw [he] at hsum
  have hh : splitRisk 0 start + (coupleBound C step final start fuel +
      splitRisk start (fuel * step + termHashes C)) ≤
      ((q + termHashes C : ℕ) : ℝ) ^ 2 / 2 ^ 256 := by linarith
  refine hh.trans ?_
  simp only [Nat.cast_pow]
  apply div_le_div_of_nonneg_right _ (le_of_lt hden)
  exact_mod_cast Nat.pow_le_pow_left (show q + termHashes C ≤ q + termHashes C + halvings count + 2 by omega) 2

theorem checkSplitDistance (prims : Primitives) (K : Constants C E) :
    CheckSplitDistance prims K := by
  intro counts D A x z Z q hx hq hpos _ hsplit
  obtain ⟨start, step, final, hbudget, hstart, hr, ha, hZ⟩ := hq
  have hh := initHist K counts D x hx
  have hsplitH := splitInit_histories K counts D x hx hsplit
  set l := multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))
  set tailD : A.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) Bool :=
    fun r => Z (r.1, fun i => if i ∉ D.1 ∧ l.2.2 ∧ r.2 i = some () then some () else none)
  have hfuel : checkRounds counts.sum =
      2 + 2 * sliceBits + 2 * halvingSteps (sliceWidth counts.sum) + 5 + 1 := by
    unfold checkRounds halvings; ring
  have hreal : checkRealLocal K (checkRounds counts.sum) D A x z Z =
      A.start (corruptInputs D x) z >>= fun st =>
        executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), 0, 0⟩) >>= Z := by
    unfold checkRealLocal
    refine bind_congr fun st => ?_
    rw [executePhase_congr_honest D A _ _ st _ _ fun i hi =>
      checkProtocol_startProg K i (x i) counts (hx.1 i hi) hpos]
  have hideal : checkIdealLocal K (checkRounds counts.sum) D A x z Z =
      A.start (corruptInputs D x) z >>= fun st =>
        executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (dummyOf D x i) (·.x)) (liftedPart (dummyOf D x i) (·.y))
            (liftedPart (dummyOf D x i) (·.z)) i).run' ⟨filledHistory K i (dummyOf D x i), 0, 0⟩) >>= tailD := by
    unfold checkIdealLocal
    refine bind_congr fun st => ?_
    change (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
      (fun i => checkProtocol K i (dummyOf D x i)) >>= tailD) = _
    rw [executePhase_congr_honest D A _ _ st _ _ fun i hi =>
      checkProtocol_startProg K i (dummyOf D x i) counts
        (canonicalDummyTuples_leak_counts K counts D x hx i hi) hpos]
  rw [hreal, hideal]
  unfold localAccepts
  simp only [probEvent_eq_eq_probOutput]
  refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
  have hc0 : DigestSaltsCovered (C := C) ∅ ∅ := fun _ _ hd => absurd rfl hd
  have hk0 : SplitCacheBound (splitRegionCache SplitHashDomain (∅ : HashCache C)) 0 :=
    ⟨∅, by simp, by intro t ht; exact (ht (by simp [splitRegionCache])).elim⟩
  have hno0 : ¬ CacheHasCollision (splitRegionCache SplitHashDomain (∅ : HashCache C)) := by
    rintro ⟨a, b, u, v, _, ha, _, _⟩
    simp [splitRegionCache] at ha
  refine (split_tvDist_prefix prims _ _ _ start 0
    (counted_splitRegionBound SplitHashDomain (hstart _ _)) ∅ ∅ hc0 (by simp) hk0 hno0
    (splitBound C step final start (checkRounds counts.sum)) (splitBound_nonneg ..) ?_).trans
    (splitBudget_le start step final (checkRounds counts.sum) counts.sum q hsplitH.two_le_n hbudget)
  intro st cache seen hc hcard hk hno
  simp only [zero_add] at hcard hk
  rw [hfuel]
  exact splitStart_tv prims K D A counts.sum step final 2 hr ha (sliceWidth_pos hpos) Z tailD
    (by intro st; simp [tailD]) (fun r => hZ _) (fun r => hZ _) st 0 0 _ _ hh
    _ _ _ _ _ _ (splitInit_sliceRel K counts D x hx) (splitInit_claim K counts D x hx)
    hsplitH cache seen hc start hcard hk hno

/-- The last split-case gap closes the complete multiplication-check security theorem. -/
theorem multVerifyClosed (prims : Primitives) (K : Constants C E) : MultVerifyStatement prims K :=
  multVerifyOfSplitRoute prims K (checkSoundStage prims K) (checkSplitDistance prims K)

/-- info: 'ThresholdLeanXmssSecurity.checkSplitDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkSplitDistance

/-- info: 'ThresholdLeanXmssSecurity.multVerifyClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multVerifyClosed

end ThresholdLeanXmssSecurity
