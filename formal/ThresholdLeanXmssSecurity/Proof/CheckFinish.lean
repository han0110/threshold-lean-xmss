import ThresholdLeanXmssSecurity.Proof.CheckStages
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The end of the check proof

The target is `CheckCoreDistance` of `Proof/CheckSecurity.lean`, and from it `MultVerifyStatement`.

* `checkCoupleStage` proves `CheckCoupleStage` (step 4). The slice loop (`sliceRest_all`) keeps
  `SliceRel` with Gruen's step on replicated products (`sliceRel_step`, which needs the slice coin
  non-zero) and hands over to `halvRest_all` (`sliceRel_halvRel`). The start (first coin, `expand`,
  `require`) is common to the two runs (`start_tv`). The initial relation (`initHist`, `checkInitSlice`)
  uses that `F_multVerify` leaks `z - x y` of the agreeing copies, so the real and the
  `canonicalDummyTuples` claims differ by the difference of the inner products. The budget is
  `coupleBound_le_coupleHashError`.
* `checkCoreDistanceFull` proves `CheckCoreDistance` from the two stages that are still open,
  `CheckSoundStage` and `CheckSplitStage`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ## The budget of the coupling -/

section Budget

variable {C : Committee}

/-- The coupling bound of a run fits in `coupleHashError`: `2 · terms · (q + (n + 1) · terms)` is at
most `(q + termHashes)^2`. -/
theorem coupleBound_le_coupleHashError (step final s F count q : ℕ) (hq : s + F * step + final ≤ q) :
    coupleBound C step final s F ≤ coupleHashError C count q := by
  unfold coupleBound coupleHashError
  have hl : C.terms.length = termCount C := check_terms_length
  have hn : 1 ≤ C.n := by unfold Committee.n; have := C.one_le_t; omega
  rw [hl, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have key : 2 * (termCount C * (s + F * step + final + (C.n + 1) * termCount C)) ≤
      (q + termHashes C) ^ 2 + (halvings count + 2) * (q + 2 * termHashes C) := by
    unfold termHashes
    have h1 : termCount C * (s + F * step + final) ≤ termCount C * q := Nat.mul_le_mul_left _ hq
    have h2 : 2 * (termCount C * q) ≤ 2 * C.n * termCount C * q * 2 := by
      have : 2 * (termCount C * q) = 2 * 1 * termCount C * q := by ring
      rw [this]
      have : 2 * 1 * termCount C * q ≤ 2 * C.n * termCount C * q := by gcongr
      omega
    have h3 : 2 * ((C.n + 1) * termCount C * termCount C) ≤ (2 * C.n * termCount C) ^ 2 := by
      have : (C.n + 1) ≤ 2 * C.n := by omega
      have h4 : 2 * ((C.n + 1) * termCount C * termCount C) ≤ 2 * (2 * C.n * termCount C * termCount C) := by
        gcongr
      have h5 : 2 * (2 * C.n * termCount C * termCount C) ≤ (2 * C.n * termCount C) ^ 2 := by
        have : (2 * C.n * termCount C) ^ 2 = 2 * (2 * C.n * termCount C * termCount C) * C.n := by ring
        rw [this]; exact Nat.le_mul_of_pos_right _ hn
      omega
    have hsq : (q + 2 * C.n * termCount C) ^ 2 = q ^ 2 + 2 * C.n * termCount C * q * 2 +
        (2 * C.n * termCount C) ^ 2 := by ring
    have hl2 : 2 * (termCount C * (s + F * step + final + (C.n + 1) * termCount C)) =
        2 * (termCount C * (s + F * step + final)) + 2 * ((C.n + 1) * termCount C * termCount C) := by ring
    rw [hl2, hsq]
    have : 0 ≤ (halvings count + 2) * (q + 2 * (2 * C.n * termCount C)) := Nat.zero_le _
    omega
  exact_mod_cast key

end Budget

/-! ## The slice loop -/

section Slice

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField
variable {Ia : Type}

/-- The half length of slice step `j`. -/
def sliceHalf (count j : ℕ) : ℕ := sliceWidth count * 2 ^ (sliceBits - 1 - j)

/-- The slice coins below the folded bit, the weight of position `k` in slice step `j`. -/
def sliceRest (τ : List E) (count j k : ℕ) : E := coinProduct τ 0 (sliceBits - 1 - j) (k / sliceWidth count)

/-- The two inner products of slice step `j`. -/
def sliceProducts (τ : List E) (count j : ℕ) (xs ys : Shares C E) : List (Product C E) :=
  [.replicated (fun T k => sliceRest τ count j k * xs T k) ys (sliceHalf count j),
   .replicated (fun T k => sliceRest τ count j k * (xs T k + xs T (k + sliceHalf count j)))
    (fun T k => ys T k + ys T (k + sliceHalf count j)) (sliceHalf count j)]

/-- The vectors after slice step `j` with challenge `r`. -/
def sliceFold (count j : ℕ) (r : E) (v : Shares C E) : Shares C E := fun T k =>
  v T k + r * (v T k + v T (k + sliceHalf count j))

/-- The claim after slice step `j`. -/
def sliceClaim (τ : List E) (j : ℕ) (r V t0 tInf : E) : E :=
  (1 + r) * t0 + r * ((V + t0) / τ.getD (sliceBits - 1 - j) 0) + r * (1 + r) * tInf

/-- The rest of the check from slice step `j`, with `n` slice steps left. -/
def sliceProg (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party) :
    RunM C E (CheckSpec C E) Unit :=
  (List.range' j n).foldlM (sliceStep K (localContext i) (hybridCheckGadgets K i) τ count) (xs, ys, V) >>=
    fun p => halvProg K (sliceWidth count) (halvingSteps (sliceWidth count)) 0 (conv K (localContext i) p.1)
      (conv K (localContext i) p.2.1) p.2.2 i

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma sliceProg_zero (K : Constants C E) (τ : List E) (count j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party) :
    sliceProg K τ count 0 j xs ys V i = halvProg K (sliceWidth count) (halvingSteps (sliceWidth count)) 0
      (conv K (localContext i) xs) (conv K (localContext i) ys) V i := by
  simp [sliceProg]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma sliceProg_succ (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party) :
    sliceProg K τ count (n + 1) j xs ys V i = (do
      let t ← (hybridCheckGadgets K i).extendMult (sliceProducts τ count j xs ys)
      let r ← challenge K (hybridCheckGadgets K i)
      sliceProg K τ count n (j + 1) (sliceFold count j r xs) (sliceFold count j r ys)
        (sliceClaim τ j r V (conv K (localContext i) t 0) (conv K (localContext i) t 1)) i) := by
  simp only [sliceProg, List.range'_succ, List.foldlM_cons, sliceStep, bind_assoc, pure_bind]
  rfl

/-- The length of the vectors before slice step `j`. -/
def sliceLen (count j : ℕ) : ℕ := sliceWidth count * 2 ^ (sliceBits - j)

/-- The weight of position `k` before slice step `j`. -/
def sliceWeight (τ : List E) (count j k : ℕ) : E := coinProduct τ 0 (sliceBits - j) (k / sliceWidth count)

/-- The relation of the two slice states before slice step `j`: the honest views are one replicated
sharing on each side, equal on the known terms, and the claims differ by a hidden-term sharing of the
difference of the weighted inner products. -/
def SliceRel (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ) (xsR ysR xsD ysD : C.Party → Shares C E)
    (DR DD : C.Party → E) : Prop :=
  ∃ (xR yR xD yD : Shares C E) (dD : C.Term → E),
    (∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → xsR i T = xR T ∧ ysR i T = yR T ∧ xsD i T = xD T ∧ ysD i T = yD T) ∧
    (∀ T, KnownTo D.1 T → xR T = xD T ∧ yR T = yD T ∧ dD T = 0) ∧
    (∀ i, i ∉ D.1 → DR i - DD i = conv K (localContext i) (fun T _ => dD T) 0) ∧
    ∑ T, dD T = ∑ k ∈ range (sliceLen count j), sliceWeight τ count j k *
      (shareValue xR k * shareValue yR k - shareValue xD k * shareValue yD k)

/-- The inputs of the multiplication of slice step `j`. -/
def sliceInputs (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E) :
    C.Party → Option (List (Product C E)) :=
  fun i => if i ∈ D.1 then none else some (sliceProducts τ count j (xs i) (ys i))

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma productShare_replicated_congr (K : Constants C E) (i : C.Party) (xv yv X Y : Shares C E) (n : ℕ)
    (hx : ∀ T, i ∈ C.holders T → xv T = X T) (hy : ∀ T, i ∈ C.holders T → yv T = Y T) :
    productShare K (localContext i) (.replicated xv yv n) = productShare K (localContext i) (.replicated X Y n) := by
  simp only [productShare, mulRep]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun AB hAB => ?_
  obtain ⟨h1, h2⟩ := K.pairs_held i AB hAB
  rw [hx AB.1 h1, hy AB.2 h2]

omit [SampleableType E] in
/-- The honest shares of two replicated inner products with one sharing on each side and equal known
terms differ by the difference of the inner products. -/
lemma replicated_total_diff (K : Constants C E) (D : C.Coalition) (xv yv xv' yv' : C.Party → Shares C E)
    (X Y X' Y' : Shares C E) (n : ℕ)
    (hv : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → xv i T = X T ∧ yv i T = Y T ∧ xv' i T = X' T ∧ yv' i T = Y' T)
    (hk : ∀ T, KnownTo D.1 T → X T = X' T ∧ Y T = Y' T) :
    ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i) (.replicated (xv i) (yv i) n) -
      ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i) (.replicated (xv' i) (yv' i) n) =
      ∑ g ∈ range n, (shareValue X g * shareValue Y g - shareValue X' g * shareValue Y' g) := by
  have e1 : ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i) (.replicated (xv i) (yv i) n) =
      ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i) (.replicated X Y n) :=
    Finset.sum_congr rfl fun i hi => productShare_replicated_congr K i _ _ _ _ n
      (fun T hT => (hv i (Finset.mem_filter.mp hi).2 T hT).1) (fun T hT => (hv i (Finset.mem_filter.mp hi).2 T hT).2.1)
  have e2 : ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i) (.replicated (xv' i) (yv' i) n) =
      ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i) (.replicated X' Y' n) :=
    Finset.sum_congr rfl fun i hi => productShare_replicated_congr K i _ _ _ _ n
      (fun T hT => (hv i (Finset.mem_filter.mp hi).2 T hT).2.2.1)
      (fun T hT => (hv i (Finset.mem_filter.mp hi).2 T hT).2.2.2)
  rw [e1, e2, honest_sum_sub D _ _ (fun i hi => productShare_replicated_congr K i _ _ _ _ n
      (fun T hT => (hk T ⟨i, hi, hT⟩).1) (fun T hT => (hk T ⟨i, hi, hT⟩).2)),
    sum_productShare_replicated K (fun _ => X) (fun _ => Y) X Y n (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    sum_productShare_replicated K (fun _ => X') (fun _ => Y') X' Y' n (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    ← Finset.sum_sub_distrib]
  rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- Gruen's slice step on the difference of two weighted inner products: the claim of the step is the
weighted inner product of the folded vectors, for every challenge, when the slice coin is not zero. -/
lemma slice_claim_identity [CharP E 2] (τ : List E) (width w : ℕ) (hw : 0 < width) (hc : τ.getD w 0 ≠ 0)
    (a b p q : ℕ → E) (r : E) :
    (1 + r) * ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) * (a k * b k - p k * q k) +
      r * ((∑ k ∈ range (width * 2 ^ (w + 1)), coinProduct τ 0 (w + 1) (k / width) * (a k * b k - p k * q k) +
        ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) * (a k * b k - p k * q k)) / τ.getD w 0) +
      r * (1 + r) * ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) *
        ((a k + a (k + width * 2 ^ w)) * (b k + b (k + width * 2 ^ w)) -
          (p k + p (k + width * 2 ^ w)) * (q k + q (k + width * 2 ^ w))) =
    ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) *
      ((a k + r * (a k + a (k + width * 2 ^ w))) * (b k + r * (b k + b (k + width * 2 ^ w))) -
        (p k + r * (p k + p (k + width * 2 ^ w))) * (q k + r * (q k + q (k + width * 2 ^ w)))) := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  set H := width * 2 ^ w
  set c := τ.getD w 0
  have hfull : ∑ k ∈ range (width * 2 ^ (w + 1)), coinProduct τ 0 (w + 1) (k / width) * (a k * b k - p k * q k) =
      ∑ k ∈ range H, coinProduct τ 0 w (k / width) * (a k * b k - p k * q k) +
        c * ∑ k ∈ range H, coinProduct τ 0 w (k / width) * (a (k + H) * b (k + H) - p (k + H) * q (k + H)) := by
    have h1 := slice_sum_split τ width w hw a b
    have h2 := slice_sum_split τ width w hw p q
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    rw [h1, h2]
    ring
  rw [hfull]
  set S1 := ∑ k ∈ range H, coinProduct τ 0 w (k / width) * (a k * b k - p k * q k)
  set S2 := ∑ k ∈ range H, coinProduct τ 0 w (k / width) * (a (k + H) * b (k + H) - p (k + H) * q (k + H))
  have hdiv : (S1 + c * S2 + S1) / c = S2 := by
    rw [show S1 + c * S2 + S1 = c * S2 + 2 * S1 by ring, two, zero_mul, add_zero]
    field_simp
  rw [hdiv]
  have hk : ∀ k ∈ range H, coinProduct τ 0 w (k / width) *
      ((a k + r * (a k + a (k + H))) * (b k + r * (b k + b (k + H))) -
        (p k + r * (p k + p (k + H))) * (q k + r * (q k + q (k + H)))) =
      (1 + r) * (coinProduct τ 0 w (k / width) * (a k * b k - p k * q k)) +
      r * (coinProduct τ 0 w (k / width) * (a (k + H) * b (k + H) - p (k + H) * q (k + H))) +
      r * (1 + r) * (coinProduct τ 0 w (k / width) *
        ((a k + a (k + H)) * (b k + b (k + H)) - (p k + p (k + H)) * (q k + q (k + H)))) := by
    intro k _
    linear_combination (norm := ring_nf) (coinProduct τ 0 w (k / width) *
      (r * p (k + H) * q (k + H) - r * a (k + H) * b (k + H))) * two
  rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

omit [SampleableType E] in
lemma sliceInputs_total (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E)
    (g : ℕ) :
    extendTotal K D (sliceInputs D τ count j xs ys) g =
      ∑ i ∈ univ.filter (· ∉ D.1), productShare K (localContext i)
        (((sliceProducts τ count j (xs i) (ys i))[g]?).getD (.replicated 0 0 0)) := by
  unfold extendTotal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ∉ D.1 := (Finset.mem_filter.mp hi).2
  simp only [sliceInputs, hi', if_false, Option.map_some, Option.getD_some]
  cases (sliceProducts τ count j (xs i) (ys i))[g]? with
  | none => simp [productShare, mulRep]
  | some p => rfl

omit [SampleableType E] in
/-- One slice step keeps the slice relation, for any challenge, when the slice coin is not zero and the
hidden output difference of the two inner products goes to the lacked term. -/
lemma sliceRel_step [CharP E 2] (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ)
    (hj : j < sliceBits) (hw : 0 < sliceWidth count) (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E)
    (h : SliceRel K D τ count j xsR ysR xsD ysD DR DD) (r : E) (zR zD : C.Party → Shares C E) (δ0 δ1 : E)
    (hz : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < 2,
      zR i T g - zD i T g = if lackedTerm D.1 = some T then (if g = 0 then δ0 else δ1) else 0)
    (h0 : δ0 = extendTotal K D (sliceInputs D τ count j xsR ysR) 0 -
      extendTotal K D (sliceInputs D τ count j xsD ysD) 0)
    (h1 : δ1 = extendTotal K D (sliceInputs D τ count j xsR ysR) 1 -
      extendTotal K D (sliceInputs D τ count j xsD ysD) 1) :
    SliceRel K D τ count (j + 1) (fun i => sliceFold count j r (xsR i)) (fun i => sliceFold count j r (ysR i))
      (fun i => sliceFold count j r (xsD i)) (fun i => sliceFold count j r (ysD i))
      (fun i => sliceClaim τ j r (DR i) (conv K (localContext i) (zR i) 0) (conv K (localContext i) (zR i) 1))
      (fun i => sliceClaim τ j r (DD i) (conv K (localContext i) (zD i) 0) (conv K (localContext i) (zD i) 1)) := by
  obtain ⟨xR, yR, xD, yD, dD, hv, hk, hl, hsum⟩ := h
  set c := τ.getD (sliceBits - 1 - j) 0 with hcdef
  let lack : C.Term → E → E := fun T x => if lackedTerm D.1 = some T then x else 0
  have hlack : ∀ x : E, ∑ T, lack T x = x := by
    intro x
    obtain ⟨T₀, hT₀, -⟩ := lackedTerm_spec D
    simp only [lack, hT₀, Option.some.injEq]
    rw [Finset.sum_ite_eq univ T₀ (fun _ => x)]
    simp
  refine ⟨sliceFold count j r xR, sliceFold count j r yR, sliceFold count j r xD, sliceFold count j r yD,
    fun T => (1 + r) * lack T δ0 + r * ((dD T + lack T δ0) / c) + r * (1 + r) * lack T δ1, ?_, ?_, ?_, ?_⟩
  · intro i hi T hT
    obtain ⟨e1, e2, e3, e4⟩ := hv i hi T hT
    unfold sliceFold
    dsimp only
    rw [e1, e2, e3, e4]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro T hT
    obtain ⟨e1, e2, e3⟩ := hk T hT
    have hn : lackedTerm D.1 ≠ some T := fun h => lackedTerm_unknown D T h hT
    unfold sliceFold
    dsimp only
    rw [e1, e2, e3]
    simp [lack, hn]
  · intro i hi
    have e0 := conv_sub_eq K i (zR i) (zD i) 0 (fun T => lack T δ0)
      (fun T hT => by simpa [lack] using hz i hi T hT 0 (by norm_num))
    have e1 := conv_sub_eq K i (zR i) (zD i) 1 (fun T => lack T δ1)
      (fun T hT => by simpa [lack] using hz i hi T hT 1 (by norm_num))
    have eD := hl i hi
    rw [conv_const_eq] at eD ⊢
    unfold sliceClaim
    rw [← hcdef]
    rw [show (1 + r) * conv K (localContext i) (zR i) 0 + r * ((DR i + conv K (localContext i) (zR i) 0) / c) +
        r * (1 + r) * conv K (localContext i) (zR i) 1 -
        ((1 + r) * conv K (localContext i) (zD i) 0 + r * ((DD i + conv K (localContext i) (zD i) 0) / c) +
          r * (1 + r) * conv K (localContext i) (zD i) 1) =
        (1 + r) * (conv K (localContext i) (zR i) 0 - conv K (localContext i) (zD i) 0) +
          r / c * ((DR i - DD i) + (conv K (localContext i) (zR i) 0 - conv K (localContext i) (zD i) 0)) +
          r * (1 + r) * (conv K (localContext i) (zR i) 1 - conv K (localContext i) (zD i) 1) by ring,
      e0, e1, eD, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun T _ => by ring
  · set w := sliceBits - 1 - j with hwdef
    set width := sliceWidth count
    have hH : sliceHalf count j = width * 2 ^ w := rfl
    have e1 : sliceBits - j = w + 1 := by omega
    have e2 : sliceBits - (j + 1) = w := by omega
    have hlen : sliceLen count j = width * 2 ^ (w + 1) := by unfold sliceLen; rw [e1]
    have hlen' : sliceLen count (j + 1) = width * 2 ^ w := by unfold sliceLen; rw [e2]
    have hwt : ∀ k, sliceWeight τ count j k = coinProduct τ 0 (w + 1) (k / width) := fun k => by
      unfold sliceWeight; rw [e1]
    have hwt' : ∀ k, sliceWeight τ count (j + 1) k = coinProduct τ 0 w (k / width) := fun k => by
      unfold sliceWeight; rw [e2]
    have hv' : ∀ (rest : ℕ → E), ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
        (fun k => rest k * xsR i T k) = (fun k => rest k * xR T k) ∧ ysR i T = yR T ∧
        (fun k => rest k * xsD i T k) = (fun k => rest k * xD T k) ∧ ysD i T = yD T := by
      intro rest i hi T hT
      obtain ⟨e1, e2, e3, e4⟩ := hv i hi T hT
      rw [e1, e3]; exact ⟨rfl, e2, rfl, e4⟩
    have hv'' : ∀ (rest : ℕ → E), ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
        (fun k => rest k * (xsR i T k + xsR i T (k + width * 2 ^ w))) =
          (fun k => rest k * (xR T k + xR T (k + width * 2 ^ w))) ∧
        (fun k => ysR i T k + ysR i T (k + width * 2 ^ w)) = (fun k => yR T k + yR T (k + width * 2 ^ w)) ∧
        (fun k => rest k * (xsD i T k + xsD i T (k + width * 2 ^ w))) =
          (fun k => rest k * (xD T k + xD T (k + width * 2 ^ w))) ∧
        (fun k => ysD i T k + ysD i T (k + width * 2 ^ w)) = (fun k => yD T k + yD T (k + width * 2 ^ w)) := by
      intro rest i hi T hT
      obtain ⟨e1, e2, e3, e4⟩ := hv i hi T hT
      rw [e1, e2, e3, e4]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hk' : ∀ (rest : ℕ → E), ∀ T, KnownTo D.1 T →
        (fun k => rest k * xR T k) = (fun k => rest k * xD T k) ∧ yR T = yD T := by
      intro rest T hT; rw [(hk T hT).1, (hk T hT).2.1]; exact ⟨rfl, rfl⟩
    have hk'' : ∀ (rest : ℕ → E), ∀ T, KnownTo D.1 T →
        (fun k => rest k * (xR T k + xR T (k + width * 2 ^ w))) =
          (fun k => rest k * (xD T k + xD T (k + width * 2 ^ w))) ∧
        (fun k => yR T k + yR T (k + width * 2 ^ w)) = (fun k => yD T k + yD T (k + width * 2 ^ w)) := by
      intro rest T hT; rw [(hk T hT).1, (hk T hT).2.1]; exact ⟨rfl, rfl⟩
    have hd0 := replicated_total_diff K D _ _ _ _ _ _ _ _ (width * 2 ^ w) (hv' (sliceRest τ count j))
      (hk' (sliceRest τ count j))
    have hd1 := replicated_total_diff K D _ _ _ _ _ _ _ _ (width * 2 ^ w) (hv'' (sliceRest τ count j))
      (hk'' (sliceRest τ count j))
    have t0 : δ0 = ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) *
        (shareValue xR k * shareValue yR k - shareValue xD k * shareValue yD k) := by
      rw [h0, sliceInputs_total, sliceInputs_total]
      refine hd0.trans (Finset.sum_congr rfl fun k _ => ?_)
      simp only [shareValue, ← Finset.mul_sum]
      unfold sliceRest
      ring
    have t1 : δ1 = ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) *
        ((shareValue xR k + shareValue xR (k + width * 2 ^ w)) * (shareValue yR k + shareValue yR (k + width * 2 ^ w)) -
          (shareValue xD k + shareValue xD (k + width * 2 ^ w)) *
            (shareValue yD k + shareValue yD (k + width * 2 ^ w))) := by
      rw [h1, sliceInputs_total, sliceInputs_total]
      refine hd1.trans (Finset.sum_congr rfl fun k _ => ?_)
      simp only [shareValue, ← Finset.mul_sum, Finset.sum_add_distrib]
      unfold sliceRest
      ring
    have hL : ∑ T, (fun T => (1 + r) * lack T δ0 + r * ((dD T + lack T δ0) / c) + r * (1 + r) * lack T δ1) T =
        (1 + r) * δ0 + r * ((∑ T, dD T + δ0) / c) + r * (1 + r) * δ1 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hlack]
    have hF : ∀ (v : Shares C E) k, shareValue (sliceFold count j r v) k =
        shareValue v k + r * (shareValue v k + shareValue v (k + width * 2 ^ w)) := by
      intro v k
      simp only [shareValue, sliceFold, hH, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hS : ∑ T, dD T = ∑ k ∈ range (width * 2 ^ (w + 1)), coinProduct τ 0 (w + 1) (k / width) *
        (shareValue xR k * shareValue yR k - shareValue xD k * shareValue yD k) := by
      rw [hsum, hlen]; exact Finset.sum_congr rfl fun k _ => by rw [hwt]
    have hR : ∑ k ∈ range (sliceLen count (j + 1)), sliceWeight τ count (j + 1) k *
        (shareValue (sliceFold count j r xR) k * shareValue (sliceFold count j r yR) k -
          shareValue (sliceFold count j r xD) k * shareValue (sliceFold count j r yD) k) =
        ∑ k ∈ range (width * 2 ^ w), coinProduct τ 0 w (k / width) *
          ((shareValue xR k + r * (shareValue xR k + shareValue xR (k + width * 2 ^ w))) *
            (shareValue yR k + r * (shareValue yR k + shareValue yR (k + width * 2 ^ w))) -
          (shareValue xD k + r * (shareValue xD k + shareValue xD (k + width * 2 ^ w))) *
            (shareValue yD k + r * (shareValue yD k + shareValue yD (k + width * 2 ^ w)))) := by
      rw [hlen']; exact Finset.sum_congr rfl fun k _ => by rw [hwt' k, hF, hF, hF, hF]
    rw [hL, hR, hS, t0, t1, hcdef]
    exact slice_claim_identity τ width w hw (hcdef ▸ hc) _ _ _ _ r

/-! ### The slice steps in the network -/

/-- The rest of a slice step after its multiplication. -/
def sliceNext (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : Shares C E) (V : E) (i : C.Party)
    (t : Shares C E) : RunM C E (CheckSpec C E) Unit := do
  let r ← challenge K (hybridCheckGadgets K i)
  sliceProg K τ count n (j + 1) (sliceFold count j r xs) (sliceFold count j r ys)
    (sliceClaim τ j r V (conv K (localContext i) t 0) (conv K (localContext i) t 1)) i

lemma sliceInputs_width (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E) :
    (firstInput (sliceInputs D τ count j xs ys)).length = 2 := by
  obtain ⟨j', _, hj⟩ := firstInput_honest D (fun i => sliceProducts (C := C) τ count j (xs i) (ys i))
  change (firstInput (fun i => if i ∈ D.1 then none else some (sliceProducts τ count j (xs i) (ys i)))).length = 2
  rw [hj]
  rfl

lemma sliceInputs_some (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E) :
    ∀ i, i ∉ D.1 → (sliceInputs D τ count j xs ys i).isSome := by
  intro i hi; simp [sliceInputs, hi]

/-- The multiplication of a slice step, with every honest operator live. -/
theorem sliceExtend_local (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i) else failure) =
    (do
      let pa ← (rightAdversary (leftAdversary Ad)).answer st (extendView K D.1 (sliceInputs D τ count j xs ys))
      let fresh ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
      executePhase localRoles D Ad (checkFunctionalities K) F pa.1
        (fun i => afterExtend K i 2 (hs i) (sliceNext K τ count n j (xs i) (ys i) (V i) i)
          (multFinish D 2 (filler K .peer)
            (fun g => extendTotal K D (sliceInputs D τ count j xs ys) g + pa.2.1 g)
            pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i))) := by
  have hp : (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i)
      else failure) =
      (fun i => if live i then ((hybridCheckGadgets K i).extendMult (sliceProducts τ count j (xs i) (ys i))
        >>= sliceNext K τ count n j (xs i) (ys i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [sliceProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs
    (fun i => sliceProducts τ count j (xs i) (ys i)) (fun i => sliceNext K τ count n j (xs i) (ys i) (V i) i),
    if_pos hall]
  change (runFunctionality localRoles D (rightAdversary (leftAdversary Ad)) (FextendMult K) st
    (sliceInputs D τ count j xs ys) >>= _) = _
  rw [runFunctionality_extend_local K D (rightAdversary (leftAdversary Ad)) st _ (sliceInputs_some D τ count j xs ys)]
  have hw := sliceInputs_width D τ count j xs ys
  generalize (firstInput (sliceInputs D τ count j xs ys)).length = w at hw ⊢
  subst hw
  simp only [bind_assoc, pure_bind]
  rfl

/-- A missing honest operator at the multiplication of a slice step stops everyone. -/
theorem sliceExtend_missing (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F : ℕ)
    (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hmiss : ¬ ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i) else failure) =
      pure (st, fun _ => none) := by
  have hp : (fun i => if live i then (sliceProg K τ count (n + 1) j (xs i) (ys i) (V i) i).run' (hs i)
      else failure) =
      (fun i => if live i then ((hybridCheckGadgets K i).extendMult (sliceProducts τ count j (xs i) (ys i))
        >>= sliceNext K τ count n j (xs i) (ys i) (V i) i).run' (hs i) else failure) := by
    funext i; rw [sliceProg_succ]; rfl
  rw [hp, executePhase_extend_live K D Ad F st live hs _ _, if_neg hmiss]

/-- The leak of the multiplication of a slice step is the same on the two sides. -/
lemma sliceInputs_view (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ)
    (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E)
    (h : SliceRel K D τ count j xsR ysR xsD ysD DR DD) :
    extendView K D.1 (sliceInputs D τ count j xsR ysR) = extendView K D.1 (sliceInputs D τ count j xsD ysD) := by
  obtain ⟨xR, yR, xD, yD, dD, hv, hk, -, -⟩ := h
  apply extendView_eq_of_relation
  have hsame : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → xsR i T = xsD i T ∧ ysR i T = ysD i T := by
    intro i hi T hT hiT
    obtain ⟨e1, e2, e3, e4⟩ := hv i hi T hiT
    rw [e1, e2, e3, e4, (hk T hT).1, (hk T hT).2.1]
    exact ⟨rfl, rfl⟩
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

/-- The output share of the multiplication of a slice step at an honest receiver. -/
def sliceOut {σ' : Type} (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ) (xs ys : C.Party → Shares C E)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (i : C.Party) : Shares C E :=
  (multFinish D 2 (filler K .peer) (fun g => extendTotal K D (sliceInputs D τ count j xs ys) g + pa.2.1 g)
    pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i).getD 0

/-- The slice relation and the history relation after a slice step. -/
lemma slice_after {σ' : Type} (K : Constants C E) (D : C.Coalition) (τ : List E) (count j : ℕ)
    (hj : j < sliceBits) (hw : 0 < sliceWidth count) (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E)
    (hrel : SliceRel K D τ count j xsR ysR xsD ysD DR DD) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD)
    (pa : σ' × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2) (r : E) :
    SliceRel K D τ count (j + 1) (fun i => sliceFold count j r (xsR i)) (fun i => sliceFold count j r (ysR i))
      (fun i => sliceFold count j r (xsD i)) (fun i => sliceFold count j r (ysD i))
      (fun i => sliceClaim τ j r (DR i) (conv K (localContext i) (sliceOut K D τ count j xsR ysR pa fresh i) 0)
        (conv K (localContext i) (sliceOut K D τ count j xsR ysR pa fresh i) 1))
      (fun i => sliceClaim τ j r (DD i) (conv K (localContext i) (sliceOut K D τ count j xsD ysD pa fresh i) 0)
        (conv K (localContext i) (sliceOut K D τ count j xsD ysD pa fresh i) 1)) ∧
    HistRel D tg (L + 1 + 1)
      (fun i => ⟨recordHistory K i (hsR i).history (sliceOut K D τ count j xsR ysR pa fresh i) 2,
        (hsR i).label + 1 + 1, (hsR i).tag⟩)
      (fun i => ⟨recordHistory K i (hsD i).history (sliceOut K D τ count j xsD ysD pa fresh i) 2,
        (hsD i).label + 1 + 1, (hsD i).tag⟩) := by
  letI : CharP E 2 := charP_two
  obtain ⟨htagR, htagD, hknownHist, hcommonR, hcommonD⟩ := hh
  constructor
  · refine sliceRel_step K D τ count j hj hw hc xsR ysR xsD ysD DR DD hrel r _ _
      (extendTotal K D (sliceInputs D τ count j xsR ysR) 0 - extendTotal K D (sliceInputs D τ count j xsD ysD) 0)
      (extendTotal K D (sliceInputs D τ count j xsR ysR) 1 - extendTotal K D (sliceInputs D τ count j xsD ysD) 1)
      ?_ rfl rfl
    intro i hi T hT g hg
    unfold sliceOut
    rw [multFinish_diff D 2 _ _ _ _ _ _ fresh i hi (hrec i hi) T hT g hg]
    split_ifs with h1 h2
    · subst h2; ring
    · have : g = 1 := by omega
      subst this; ring
    · rfl
  · refine ⟨fun i hi => by simp [htagR i hi], fun i hi => by simp [htagD i hi], ?_, ?_, ?_⟩
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

/-- The programs after the multiplication of a slice step. -/
lemma sliceAfter_form (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F' : ℕ) (st : Ad.State)
    (hs : C.Party → RunState C) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)
    (fresh : C.Term → Fin 2 → E) :
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => afterExtend K i 2 (hs i) (sliceNext K τ count n j (xs i) (ys i) (V i) i)
        (multFinish D 2 (filler K .peer)
          (fun g => extendTotal K D (sliceInputs D τ count j xs ys) g + pa.2.1 g)
          pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2 fresh i)) =
    executePhase localRoles D Ad (checkFunctionalities K) F' st
      (fun i => if i ∈ pa.2.2.2.2 then
        (challenge K (hybridCheckGadgets K i) >>= fun r =>
          sliceProg K τ count n (j + 1) (sliceFold count j r (xs i)) (sliceFold count j r (ys i))
            (sliceClaim τ j r (V i) (conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 0)
              (conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 1)) i).run'
          ⟨recordHistory K i (hs i).history (sliceOut K D τ count j xs ys pa fresh i) 2,
            (hs i).label + 1, (hs i).tag⟩
        else failure) := by
  apply executePhase_congr_honest
  intro i hi
  rw [multFinish_honest D 2 _ _ _ _ _ _ i hi]
  by_cases hr : i ∈ pa.2.2.2.2
  · simp only [hr, if_true, afterExtend, sliceOut, sliceNext]
  · simp only [hr, if_false, afterExtend]

/-- The coupling of the rest of the check from slice step `j` with `n` slice steps left and `F` steps
of fuel. -/
def SliceRest (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E)
    (count step final n j F : ℕ) {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    Prop :=
  ∀ (st : Ad.State) (live : Finset C.Party) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E) (cache : HashCache C) (seen : Finset (List Bit)),
    SliceRel K D τ count j xsR ysR xsD ysD DR DD → HistRel D tg L hsR hsD →
    DigestSaltsCovered cache seen →
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (sliceProg K τ count n j (xsR i) (ysR i) (DR i) i).run' (hsR i) else failure) >>=
          tail)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if i ∈ live then (sliceProg K τ count n j (xsD i) (ysD i) (DD i) i).run' (hsD i) else failure) >>=
          tail)).run' cache) ≤
      coupleBound C step final seen.card F

/-- The challenge continuation of a slice step. -/
def sliceCont (K : Constants C E) (τ : List E) (count n j : ℕ) (xs ys : C.Party → Shares C E) (V : C.Party → E)
    (z : C.Party → Shares C E) (i : C.Party) (r : E) : RunM C E (CheckSpec C E) Unit :=
  sliceProg K τ count n (j + 1) (sliceFold count j r (xs i)) (sliceFold count j r (ys i))
    (sliceClaim τ j r (V i) (conv K (localContext i) (z i) 0) (conv K (localContext i) (z i) 1)) i

/-- One coin of a slice step: the common challenge and then the rest of the check. -/
theorem sliceCoin_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final n j F : ℕ) (hj : j < sliceBits) (hw : 0 < sliceWidth count)
    (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hIH : SliceRest prims K D Ad τ count step final n (j + 1) F tail) (tg L : ℕ) (hsR hsD : C.Party → RunState C)
    (hh : HistRel D tg L hsR hsD) (xsR ysR xsD ysD : C.Party → Shares C E) (DR DD : C.Party → E)
    (hrel : SliceRel K D τ count j xsR ysR xsD ysD DR DD)
    (pa : Ad.State × (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) (fresh : C.Term → Fin 2 → E)
    (hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2)
    (y : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party))
    (cache : HashCache C) (seen : Finset (List Bit)) (hcov : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsR i).history (sliceOut K D τ count j xsR ysR pa fresh i) 2,
          (hsR i).label + 1, (hsR i).tag⟩)
        (sliceCont K τ count n j xsR ysR DR (sliceOut K D τ count j xsR ysR pa fresh)) tail y)).run' cache)
      ((simulateQ (localAnswer prims) (halvCoinNext K D Ad F
        (fun i => ⟨recordHistory K i (hsD i).history (sliceOut K D τ count j xsD ysD pa fresh i) 2,
          (hsD i).label + 1, (hsD i).tag⟩)
        (sliceCont K τ count n j xsD ysD DD (sliceOut K D τ count j xsD ysD pa fresh)) tail y)).run' cache) ≤
      coupleBound C step final seen.card F := by
  have hafter := slice_after K D τ count j hj hw hc xsR ysR xsD ysD DR DD hrel tg L hsR hsD hh pa fresh hrec
  have hrel' := fun r => (hafter r).1
  have hh' := (hafter 0).2
  have htagR := hh.1
  have htagD := hh.2.1
  by_cases hy : ∃ i, i ∉ D.1 ∧ i ∈ y.2.2
  · unfold halvCoinNext
    rw [tvDist_sameRun_congr prims
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagR i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tail out))
      ((executePhase_afterChallenge_common' prims K D Ad F y.2.1 _ tg (L + 1)
        (fun i hi => by simp [htagD i hi]) (List.ofFn y.1) y.2.2 hy _).bind fun out => SameRun.refl prims (tail out)),
      bind_assoc, bind_assoc]
    refine tvDist_prefix prims _ _ _ 0 (challengeQuery_no_digest K tg (L + 1) (List.ofFn y.1)) cache seen hcov _ ?_
    intro r cache' seen' hc' hcard
    rcases r with _ | r
    · simp only [executePhase_failure, tvDist_self]
      exact coupleBound_nonneg _ _ _ _
    · refine le_trans ?_ (coupleBound_mono (s := seen'.card) (f := F) (by omega))
      exact hIH y.2.1 y.2.2 tg (L + 1 + 1) _ _ _ _ _ _ _ _ cache' seen' (hrel' r) hh' hc'
  · push Not at hy
    have hfail : ∀ (hs : C.Party → RunState C) (g : C.Party → E → RunM C E (CheckSpec C E) Unit),
        halvCoinNext K D Ad F hs g tail y = tail (y.2.1, fun _ => none) := by
      intro hs g
      unfold halvCoinNext
      rw [executePhase_congr_honest D Ad _ F y.2.1 _ (fun _ => failure), executePhase_failure, pure_bind]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ y.2.2) := fun h => hy i h.1 h.2
      simp only [hn, if_false, afterChallenge]
    rw [hfail, hfail, tvDist_self]
    exact coupleBound_nonneg _ _ _ _

/-- One slice step keeps the coupling of the rest of the check. -/
theorem sliceRest_succ (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final n j F : ℕ) (hj : j < sliceBits) (hw : 0 < sliceWidth count)
    (hc : τ.getD (sliceBits - 1 - j) 0 ≠ 0) (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hIH : SliceRest prims K D Ad τ count step final n (j + 1) F tail) :
    SliceRest prims K D Ad τ count step final (n + 1) j (F + 1 + 1) tail := by
  intro st live tg L hsR hsD xsR ysR xsD ysD DR DD cache seen hrel hh hcov
  by_cases hall : ∀ i, i ∉ D.1 → i ∈ live
  swap
  · rw [sliceExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsR τ count n j xsR ysR DR,
      sliceExtend_missing K D Ad (F + 1) st (· ∈ live) hall hsD τ count n j xsD ysD DD, tvDist_self]
    exact coupleBound_nonneg _ _ _ _
  rw [sliceExtend_local K D Ad (F + 1) st (· ∈ live) hall hsR τ count n j xsR ysR DR,
    sliceExtend_local K D Ad (F + 1) st (· ∈ live) hall hsD τ count n j xsD ysD DD,
    ← sliceInputs_view K D τ count j xsR ysR xsD ysD DR DD hrel]
  have hq1 := rl_answer_bound Ad step ha st (extendView K D.1 (sliceInputs D τ count j xsR ysR))
  refine tvDist_prefix_tail prims _ _ _ tail step hq1 cache seen hcov _ ?_
  intro pa cache1 seen1 hc1 hcard1
  refine tvDist_sample1_tail prims _ _ tail cache1 seen1 hc1 _ ?_
  intro fresh cache2 seen2 hc2 hcard2
  rw [sliceAfter_form K D Ad (F + 1) pa.1 hsR τ count n j xsR ysR DR pa fresh,
    sliceAfter_form K D Ad (F + 1) pa.1 hsD τ count n j xsD ysD DD pa fresh]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  · rw [halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tail,
      halvChallenge_eq K D Ad F pa.1 pa.2.2.2.2 hrec _ _ tail]
    refine tvDist_prefix prims (coinDraw D Ad pa.1) _ _ step (coinDraw_digestBound D Ad step ha pa.1) cache2 seen2
      hc2 _ ?_
    intro y cache3 seen3 hc3 hcard3
    have hF : (F + 1 + 1) * step = F * step + step + step := by ring
    exact le_trans (sliceCoin_tv prims K D Ad τ count step final n j F hj hw hc tail hIH tg L hsR hsD hh
      xsR ysR xsD ysD DR DD hrel pa fresh hrec y cache3 seen3 hc3) (coupleBound_mono (by omega))
  · rw [executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec,
      executePhase_challenge_live K D Ad F pa.1 (fun i => i ∈ pa.2.2.2.2) _ _, if_neg hrec, tvDist_self]
    exact coupleBound_nonneg _ _ _ _

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma conv_sub_const (K : Constants C E) (i : C.Party) (X Y : Shares C E) (k : ℕ) :
    conv K (localContext i) X k - conv K (localContext i) Y k =
      conv K (localContext i) (fun T _ => X T k - Y T k) 0 := by
  simp only [conv, ← Finset.sum_sub_distrib, mul_sub]

/-- After the slice steps the slice relation is the halving relation of the Shamir vectors `Conv`. -/
lemma sliceRel_halvRel (K : Constants C E) (D : C.Coalition) (τ : List E) (count : ℕ)
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

/-- The last slice state leads into the halving loop. -/
theorem sliceRest_zero (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final fuel : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final) :
    SliceRest prims K D Ad τ count step final 0 sliceBits
      (fuel + 2 * halvingSteps (sliceWidth count) + 5) tail := by
  intro st live tg L hsR hsD xsR ysR xsD ysD DR DD cache seen hrel hh hc
  obtain ⟨AR, BR, AD, BD, hconv, hhalv⟩ := sliceRel_halvRel K D τ count xsR ysR xsD ysD DR DD hrel
  have hR := executePhase_congr_honest D Ad (checkFunctionalities K) (fuel + 2 * halvingSteps (sliceWidth count) + 5)
    st (fun i => if i ∈ live then (sliceProg K τ count 0 sliceBits (xsR i) (ysR i) (DR i) i).run' (hsR i)
      else failure)
    (fun i => if i ∈ live then (halvProg K (sliceWidth count) (halvingSteps (sliceWidth count)) 0 (AR i) (BR i)
      (DR i) i).run' (hsR i) else failure)
    (fun i hi => by
      simp only [sliceProg_zero, (hconv i hi).1, (hconv i hi).2.1])
  have hD := executePhase_congr_honest D Ad (checkFunctionalities K) (fuel + 2 * halvingSteps (sliceWidth count) + 5)
    st (fun i => if i ∈ live then (sliceProg K τ count 0 sliceBits (xsD i) (ysD i) (DD i) i).run' (hsD i)
      else failure)
    (fun i => if i ∈ live then (halvProg K (sliceWidth count) (halvingSteps (sliceWidth count)) 0 (AD i) (BD i)
      (DD i) i).run' (hsD i) else failure)
    (fun i hi => by
      simp only [sliceProg_zero, (hconv i hi).2.2.1, (hconv i hi).2.2.2])
  rw [hR, hD]
  exact halvRest_all prims K D Ad step final (sliceWidth count) hr ha hw tail hq (halvingSteps (sliceWidth count)) 0
    fuel (by simp) st live tg L hsR hsD AR BR AD BD DR DD cache seen hhalv hh hc

/-- The slice steps, the halving loop and the final segment keep the coupling (GS20, Protocols 13 to 15). -/
theorem sliceRest_all (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (τ : List E) (count step final : ℕ) (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final) :
    ∀ n j fuel, j + n = sliceBits →
      SliceRest prims K D Ad τ count step final n j (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5) tail
  | 0, j, fuel, h => by
    simp only [Nat.add_zero] at h
    subst h
    simpa using sliceRest_zero prims K D Ad τ count step final fuel hr ha hw tail hq
  | n + 1, j, fuel, h => by
    have he : fuel + 2 * (n + 1) + 2 * halvingSteps (sliceWidth count) + 5 =
        fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5 + 1 + 1 := by ring
    rw [he]
    exact sliceRest_succ prims K D Ad τ count step final n j _ (by omega) hw (hτ _ (by omega)) ha tail
      (sliceRest_all prims K D Ad τ count step final hτ hr ha hw tail hq n (j + 1) fuel (by omega))

end Slice

/-! ## The start of the check -/

section Start

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField
variable {Ia : Type}

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The coin key of the first coin with the label `ρ` and its `d` expanded values. -/
def startQuery (K : Constants C E) (tag ρ : ℕ) (values : List E) (d : ℕ) : OracleComp (RoSpec C) (List E) :=
  hashQuery (.coinKey tag ρ (values.flatMap fun v => List.ofFn (K.encode v))) >>= fun key =>
    (List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand key k)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem start_run' {α : Type} (K : Constants C E) (i : C.Party) (d : ℕ) (f : List E → RunM C E (CheckSpec C E) α)
    (st : RunState C) :
    ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= f).run' st =
      call (Sum.inl (Sum.inl 1)) >>= fun o => match o with
        | some (.inl (.inl v)) => oracleStep (startQuery K st.tag st.label v d) >>= fun τ =>
            (f τ).run' ⟨st.history, st.label + 1, st.tag⟩
        | _ => failure := by
  simp only [coinKey, expand, bind_assoc, hybridCheckGadgets, freshLabel, startQuery, oracleStep_bind]
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, StateT.run_get]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> simp [StateT.run_lift]

/-- The program of an operator after the first coin. -/
def afterStart {α : Type} (K : Constants C E) (hs : RunState C) (d : ℕ) (f : List E → RunM C E (CheckSpec C E) α)
    (out : Option (List E)) : PartyM C E (CheckSpec C E) α :=
  match out with
  | some v => oracleStep (startQuery K hs.tag hs.label v d) >>= fun τ => (f τ).run' ⟨hs.history, hs.label + 1, hs.tag⟩
  | none => failure

theorem executePhase_start {α : Type} (K : Constants C E) (D : C.Coalition) (A : CheckAdversary C E Ia)
    (fuel : ℕ) (st : A.State) (hs : C.Party → RunState C) (d : ℕ) (f : C.Party → List E → RunM C E (CheckSpec C E) α) :
    executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
      (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= f i).run' (hs i)) = (do
      let p ← runFunctionality localRoles D (leftAdversary (leftAdversary A)) (Fcoin (E := E)) st
        (fun i => if i ∈ D.1 then none else some 1)
      executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterStart K (hs i) d (f i) (p.2 i))) := by
  simp_rw [start_run']
  rw [executePhase_call, runCheck_coin, bind_map_left]
  apply bind_congr
  intro p
  dsimp only
  congr 1
  funext i
  cases he : p.2 i <;> rfl

/-- The rest of the start after its coin. -/
def startCoinNext {β : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F d : ℕ)
    (hs : C.Party → RunState C) (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (y : (Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 1) → E) ×
      (Ad.State × Finset C.Party)) : OracleComp (LocalSpec C) β :=
  executePhase localRoles D Ad (checkFunctionalities K) F y.2.1
    (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ y.2.2 then some (List.ofFn y.1) else none)) >>= tail

/-- The start of the check, from its coin. -/
lemma start_eq {β : Type} (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia) (F d : ℕ)
    (st : Ad.State) (hs : C.Party → RunState C) (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β) :
    executePhase localRoles D Ad (checkFunctionalities K) (F + 1) st
      (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= g i).run' (hs i)) >>= tail =
    coinDraw D Ad st >>= startCoinNext K D Ad F d hs g tail := by
  rw [executePhase_start K D Ad F st hs d g]
  have hin : ∀ i, i ∉ D.1 → ((if i ∈ D.1 then none else some 1 : Option ℕ)).isSome := by
    intro i hi; simp [hi]
  rw [runFunctionality_coin_local D (leftAdversary (leftAdversary Ad)) st _ hin]
  simp only [coinDraw, startCoinNext, bind_assoc, pure_bind]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma startQuery_no_digest (K : Constants C E) (tg L : ℕ) (v : List E) (d : ℕ) :
    IsQueryBoundP (liftComp (startQuery K tg L v d) (LocalSpec C)) DigestQuery 0 := by
  simp only [startQuery, liftComp_bind]
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection])) fun key _ => ?_
  generalize List.range d = l
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_map]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => ?_
    · rw [map_eq_bind_pure_comp]
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection])) fun _ _ => by simp
    · exact isQueryBoundP_bind (n := 0) (m := 0) ih fun _ _ => by simp

/-- After a common coin, the honest operators read common expanded coins. -/
theorem executePhase_afterStart_common {α : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (Ad : CheckAdversary C E Ia) (fuel d : ℕ) (st : Ad.State) (hs : C.Party → RunState C) (tg L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tg ∧ (hs i).label = L) (v : List E) (rec : Finset C.Party)
    (hrec : ∃ i, i ∉ D.1 ∧ i ∈ rec) (g : C.Party → List E → RunM C E (CheckSpec C E) α) :
    SameRun prims
      (executePhase localRoles D Ad (checkFunctionalities K) fuel st
        (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ rec then some v else none)))
      (do
        let τ ← liftComp (startQuery K tg L v d) (LocalSpec C)
        executePhase localRoles D Ad (checkFunctionalities K) fuel st
          (fun i => if i ∈ rec then (g i τ).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure)) := by
  let f : C.Party → List E → PartyM C E (CheckSpec C E) α := fun i τ =>
    if i ∉ D.1 ∧ i ∈ rec then (g i τ).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩ else failure
  let oa : C.Party → OracleComp (LocalSpec C) (List E) := fun i =>
    if i ∉ D.1 ∧ i ∈ rec then liftComp (startQuery K tg L v d) (LocalSpec C) else pure []
  have hp : (fun i => afterStart K (hs i) d (g i)
      (if i ∉ D.1 ∧ i ∈ rec then some v else none)) = (fun i => localStep (oa i) >>= f i) := by
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ rec
    · simp only [hi, afterStart, oa, f, oracleStep, (htag i hi.1).1, (htag i hi.1).2]
      rfl
    · simp only [hi, if_false, afterStart, oa, f, localStep_pure', pure_bind]
  rw [hp]
  refine (executePhase_local_fallback prims D Ad _ fuel st oa (fun _ => []) f).trans ?_
  have hsel : SameRun prims (Concrete.sequenceFin (fun i => if i ∈ D.1 then pure [] else oa i))
      (do let r ← liftComp (startQuery K tg L v d) (LocalSpec C)
          pure (fun i => if i ∉ D.1 ∧ i ∈ rec then r else [])) := by
    convert sameRun_sequenceFin_selected prims (startQuery K tg L v d) []
      (fun i => i ∉ D.1 ∧ i ∈ rec) hrec using 2
    · funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr, oa]
    · funext r
      congr 1
      funext i
      by_cases hi : i ∈ D.1 <;> by_cases hr : i ∈ rec <;> simp [hi, hr]
  refine (hsel.bind fun vs => SameRun.refl prims _).trans ?_
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro r
  apply SameRun.of_eq
  apply executePhase_congr_honest
  intro i hi
  by_cases hr : i ∈ rec <;> simp [f, hi, hr]

/-- The check from its first coin, on the lifted vectors `X`, `Y`, `Z`. -/
def startProg (K : Constants C E) (count : ℕ) (X Y Z : Shares C E) (i : C.Party) : RunM C E (CheckSpec C E) Unit :=
  (coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key (coins count)) >>= fun τ =>
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0)) >>= fun _ =>
      sliceProg K τ count sliceBits 0 (fun T k => wordWeightOf K τ count k * X T k) Y
        (conv K (localContext i) (claimOf K τ count Z) 0) i

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem check_startProg (K : Constants C E) (i : C.Party) (tuples : List (Tuple C))
    (h : (tuples.map (·.count)).sum ≠ 0) :
    check K (localContext i) (hybridCheckGadgets K i) tuples =
      startProg K (tuples.map (·.count)).sum (liftedPart tuples (·.x)) (liftedPart tuples (·.y))
        (liftedPart tuples (·.z)) i := by
  rw [check_eq K (localContext i) (hybridCheckGadgets K i) tuples h]
  unfold startProg sliceProg halvProg
  simp only [bind_assoc]
  refine bind_congr fun key => bind_congr fun τ => bind_congr fun _ => ?_
  have hh : halvings (tuples.map (·.count)).sum - sliceBits = halvingSteps (sliceWidth (tuples.map (·.count)).sum) := by
    unfold halvings; omega
  rw [hh, List.range_eq_range', List.range_eq_range']

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma require_bind_run' {α : Type} (P : Prop) (f : Unit → RunM C E (CheckSpec C E) α) (s : RunState C) :
    (StateT.lift (require P) >>= f).run' s = if P then (f ()).run' s else failure := by
  unfold require
  split_ifs <;> simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift]

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma histRel_label (D : C.Coalition) (tg L : ℕ) (hsR hsD : C.Party → RunState C) (hh : HistRel D tg L hsR hsD) :
    HistRel D tg (L + 1) (fun i => ⟨(hsR i).history, (hsR i).label + 1, (hsR i).tag⟩)
      (fun i => ⟨(hsD i).history, (hsD i).label + 1, (hsD i).tag⟩) := by
  obtain ⟨htagR, htagD, hknown, hcommonR, hcommonD⟩ := hh
  exact ⟨fun i hi => by simp [htagR i hi], fun i hi => by simp [htagD i hi], hknown, hcommonR, hcommonD⟩

/-- The start of the check (first coin, expansion, `require`) followed by the slice steps, the halving
loop and the final segment keeps the coupling. -/
theorem start_tv (prims : Primitives) (K : Constants C E) (D : C.Coalition) (Ad : CheckAdversary C E Ia)
    (count step final fuel : ℕ) (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    {β : Type} (tail : Ad.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) β)
    (hq : ∀ out, IsQueryBoundP (tail out) Counted final) (st : Ad.State) (tg L : ℕ)
    (hsR hsD : C.Party → RunState C) (hh : HistRel D tg L hsR hsD) (XR YR ZR XD YD ZD : C.Party → Shares C E)
    (hrel : ∀ τ : List E, (∀ b < sliceBits, τ.getD b 0 ≠ 0) → SliceRel K D τ count 0
      (fun i T k => wordWeightOf K τ count k * XR i T k) YR (fun i T k => wordWeightOf K τ count k * XD i T k) YD
      (fun i => conv K (localContext i) (claimOf K τ count (ZR i)) 0)
      (fun i => conv K (localContext i) (claimOf K τ count (ZD i)) 0))
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    tvDist ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K)
          (fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 + 1) st
          (fun i => (startProg K count (XR i) (YR i) (ZR i) i).run' (hsR i)) >>= tail)).run' cache)
      ((simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K)
          (fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 + 1) st
          (fun i => (startProg K count (XD i) (YD i) (ZD i) i).run' (hsD i)) >>= tail)).run' cache) ≤
      coupleBound C step final seen.card (fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 + 1) := by
  set F := fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth count) + 5 with hFdef
  unfold startProg
  rw [start_eq K D Ad F (coins count) st hsR _ tail, start_eq K D Ad F (coins count) st hsD _ tail]
  refine tvDist_prefix prims (coinDraw D Ad st) _ _ step (coinDraw_digestBound D Ad step ha st) cache seen hc _ ?_
  intro y cache1 seen1 hc1 hcard1
  have htagR := hh.1
  have htagD := hh.2.1
  by_cases hy : ∃ i, i ∉ D.1 ∧ i ∈ y.2.2
  · unfold startCoinNext
    rw [tvDist_sameRun_congr prims
      ((executePhase_afterStart_common prims K D Ad F (coins count) y.2.1 hsR tg L htagR (List.ofFn y.1) y.2.2 hy
        _).bind fun out => SameRun.refl prims (tail out))
      ((executePhase_afterStart_common prims K D Ad F (coins count) y.2.1 hsD tg L htagD (List.ofFn y.1) y.2.2 hy
        _).bind fun out => SameRun.refl prims (tail out)),
      bind_assoc, bind_assoc]
    refine tvDist_prefix prims _ _ _ 0 (startQuery_no_digest K tg L (List.ofFn y.1) (coins count)) cache1 seen1 hc1
      _ ?_
    intro τ cache2 seen2 hc2 hcard2
    simp only [require_bind_run']
    by_cases hP : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [eq_true hP, if_true]
      refine le_trans (sliceRest_all prims K D Ad τ count step final hP hr ha hw tail hq sliceBits 0 fuel (by simp)
        y.2.1 y.2.2 tg (L + 1) _ _ _ _ _ _ _ _ cache2 seen2 (hrel τ hP) (histRel_label D tg L hsR hsD hh) hc2)
        (coupleBound_mono (by
          have e : (F + 1) * step = F * step + step := by ring
          rw [e, hFdef]; omega))
    · simp only [eq_false hP, if_false, ite_self, tvDist_self]
      exact coupleBound_nonneg _ _ _ _
  · push Not at hy
    have hfail : ∀ (hs : C.Party → RunState C) (g : C.Party → List E → RunM C E (CheckSpec C E) Unit),
        startCoinNext K D Ad F (coins count) hs g tail y = tail (y.2.1, fun _ => none) := by
      intro hs g
      unfold startCoinNext
      rw [executePhase_congr_honest D Ad _ F y.2.1 _ (fun _ => failure), executePhase_failure, pure_bind]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ y.2.2) := fun h => hy i h.1 h.2
      simp only [hn, if_false, afterStart]
    rw [hfail, hfail, tvDist_self]
    exact coupleBound_nonneg _ _ _ _

end Start

/-! ## The coupling stage -/

section Couple

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The tuples of the ideal run, from the leak of `F_multVerify`. -/
def dummyOf (D : C.Coalition) (x : C.Party → List (Tuple C)) (i : C.Party) : List (Tuple C) :=
  canonicalDummyTuples D (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).1
    (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1 i

/-- The initial relation of the real and the ideal check: the histories of the filled values, and for
every coin `τ` with non-zero slice coins the slice relation of the weighted lifted tuples and the claims
(the differences `z - x y` agree position by position). -/
def CheckInitRel (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (x : C.Party → List (Tuple C)),
    TupleInputs K counts D x → counts.sum ≠ 0 →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    HistRel D 0 0 (fun i => ⟨filledHistory K i (x i), 0, 0⟩) (fun i => ⟨filledHistory K i (dummyOf D x i), 0, 0⟩) ∧
    ∀ τ : List E, (∀ b < sliceBits, τ.getD b 0 ≠ 0) → SliceRel K D τ counts.sum 0
      (fun i T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k) (fun i => liftedPart (x i) (·.y))
      (fun i T k => wordWeightOf K τ counts.sum k * liftedPart (dummyOf D x i) (·.x) T k)
      (fun i => liftedPart (dummyOf D x i) (·.y))
      (fun i => conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0)
      (fun i => conv K (localContext i) (claimOf K τ counts.sum (liftedPart (dummyOf D x i) (·.z))) 0)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma checkProtocol_startProg (K : Constants C E) (i : C.Party) (tuples : List (Tuple C)) (counts : List ℕ)
    (hc : tuples.map (·.count) = counts) (h : counts.sum ≠ 0) :
    checkProtocol K i tuples = (startProg K counts.sum (liftedPart tuples (·.x)) (liftedPart tuples (·.y))
      (liftedPart tuples (·.z)) i).run' ⟨filledHistory K i tuples, 0, 0⟩ := by
  unfold checkProtocol
  rw [check_startProg K i tuples (by rw [hc]; exact h), hc]

/-- `CheckCoupleStage` from the initial relation. -/
theorem checkCoupleStage_of_init (prims : Primitives) (K : Constants C E) (hinit : CheckInitRel K) :
    CheckCoupleStage prims K := by
  intro counts D A x z Z q hx hq hpos _ hagree
  obtain ⟨start, step, final, hbudget, hstart, hr, ha, hZ⟩ := hq
  obtain ⟨hh, hrel⟩ := hinit counts D x hx hpos hagree
  set l := multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))
  set tail : A.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) Bool :=
    fun r => Z (r.1, fun i => if i ∉ D.1 ∧ l.2.2 ∧ r.2 i = some () then some () else none)
  have hfuel : checkRounds counts.sum =
      2 + 2 * sliceBits + 2 * halvingSteps (sliceWidth counts.sum) + 5 + 1 := by
    unfold checkRounds halvings; ring
  have hmasked : checkMaskedLocal K (checkRounds counts.sum) D A x z Z =
      A.start (corruptInputs D x) z >>= fun st =>
        executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), 0, 0⟩) >>= tail := by
    rw [checkMaskedLocal_eq]
    unfold checkRealRun
    simp only [bind_assoc]
    refine bind_congr fun st => ?_
    rw [executePhase_congr_honest D A _ _ st _ _ fun i hi =>
      checkProtocol_startProg K i (x i) counts (hx.1 i hi) hpos]
  have hideal : checkIdealLocal K (checkRounds counts.sum) D A x z Z =
      A.start (corruptInputs D x) z >>= fun st =>
        executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (dummyOf D x i) (·.x)) (liftedPart (dummyOf D x i) (·.y))
            (liftedPart (dummyOf D x i) (·.z)) i).run' ⟨filledHistory K i (dummyOf D x i), 0, 0⟩) >>= tail := by
    unfold checkIdealLocal
    refine bind_congr fun st => ?_
    change (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
      (fun i => checkProtocol K i (dummyOf D x i)) >>= tail) = _
    rw [executePhase_congr_honest D A _ _ st _ _ fun i hi =>
      checkProtocol_startProg K i (dummyOf D x i) counts
        (canonicalDummyTuples_leak_counts K counts D x hx i hi) hpos]
  rw [hmasked, hideal]
  unfold localAccepts
  simp only [probEvent_eq_eq_probOutput]
  refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
  have hc0 : DigestSaltsCovered (C := C) ∅ ∅ := fun _ _ hd => absurd rfl hd
  refine tvDist_prefix prims _ _ _ start (counted_digestBound (hstart _ _)) ∅ ∅ hc0 _ ?_
  intro st cache seen hc hcard
  rw [hfuel]
  refine (start_tv prims K D A counts.sum step final 2 hr ha (sliceWidth_pos hpos) tail (fun r => hZ _) st 0 0 _ _ hh
    _ _ _ _ _ _ hrel cache seen hc).trans ?_
  rw [← hfuel]
  refine coupleBound_le_coupleHashError step final seen.card (checkRounds counts.sum) counts.sum q ?_
  simp only [Finset.card_empty, zero_add] at hcard
  omega

end Couple

/-! ## The initial histories -/

section InitHist

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The filled values of a term depend only on the modes and the vectors of `z` at the term. -/
lemma filledHistory_congr (K : Constants C E) (i : C.Party) (a b : List (Tuple C)) (T : C.Term)
    (h : a.map (fun τ => (τ.mode, vector τ.count (τ.z T))) = b.map (fun τ => (τ.mode, vector τ.count (τ.z T)))) :
    filledHistory K i a T = filledHistory K i b T := by
  unfold filledHistory
  split_ifs
  · let G : ReshareMode × List Bit → List Bit := fun p =>
      ((List.range p.2.length).filter fun g => (filler K p.1 T g).isSome).map fun g => p.2.getD g 0
    have hG : ∀ τ : Tuple C, ((List.range τ.count).filter fun g => (filler K τ.mode T g).isSome).map (τ.z T) =
        G (τ.mode, vector τ.count (τ.z T)) := by
      intro τ
      simp only [G, vector, List.length_map, List.length_range]
      refine List.map_congr_left fun g hg => ?_
      have hg' : g < τ.count := List.mem_range.mp (List.mem_filter.mp hg).1
      simp [hg']
    rw [List.flatMap_congr (fun τ _ => hG τ), List.flatMap_congr (fun τ _ => hG τ)]
    rw [← List.flatMap_map (f := fun τ : Tuple C => (τ.mode, vector τ.count (τ.z T))) (g := G),
      ← List.flatMap_map (f := fun τ : Tuple C => (τ.mode, vector τ.count (τ.z T))) (g := G), h]
  · rfl

/-- The modes and the known `z` vectors of the ideal tuples are those of the real tuples. -/
lemma dummyOf_known_modes (D : C.Coalition) (x : C.Party → List (Tuple C)) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (hT : KnownTo D.1 T) :
    (dummyOf D x i).map (fun τ => (τ.mode, vector τ.count (τ.z T))) =
      (x i).map (fun τ => (τ.mode, vector τ.count (τ.z T))) := by
  unfold dummyOf canonicalDummyTuples
  change (((checkKnownTuples D x i).getD []).zipIdx.map _).map _ = _
  rw [checkKnownTuples_honest D x i hi]
  simp only [Option.getD_some, List.zipIdx_map, List.map_map]
  cases ht : lackedTerm D.1 with
  | none =>
    simp only [Function.comp_def, Prod.map, id_eq, knownView_vector D.1 _ _ T hT]
    change List.map ((fun τ : Tuple C => (τ.mode, vector τ.count (τ.z T))) ∘ Prod.fst) _ = _
    rw [← List.map_map]
    simp
  | some T₀ =>
    have hne : T ≠ T₀ := by intro he; subst T₀; exact lackedTerm_unknown D T ht hT
    simp only [Function.comp_def, Prod.map, id_eq, if_neg hne, knownView_vector D.1 _ _ T hT]
    change List.map ((fun τ : Tuple C => (τ.mode, vector τ.count (τ.z T))) ∘ Prod.fst) _ = _
    rw [← List.map_map]
    simp

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
lemma map_pair_eq {α β γ : Type} : ∀ (a b : List α) (f : α → β) (g : α → γ), a.map f = b.map f → a.map g = b.map g →
    a.map (fun t => (f t, g t)) = b.map (fun t => (f t, g t))
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | s :: a, t :: b, f, g, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
    exact ⟨Prod.ext h1.1 h2.1, map_pair_eq a b f g h1.2 h2.2⟩

/-- The modes of the ideal tuples are those of the real tuples. -/
lemma dummyOf_modes (D : C.Coalition) (x : C.Party → List (Tuple C)) (i : C.Party) (hi : i ∉ D.1) :
    (dummyOf D x i).map (·.mode) = (x i).map (·.mode) := by
  unfold dummyOf canonicalDummyTuples
  change (((checkKnownTuples D x i).getD []).zipIdx.map _).map _ = _
  rw [checkKnownTuples_honest D x i hi]
  simp only [Option.getD_some, List.zipIdx_map, List.map_map]
  cases lackedTerm D.1 with
  | none =>
    change List.map ((fun τ : Tuple C => τ.mode) ∘ Prod.fst) _ = _
    rw [← List.map_map]
    simp
  | some T₀ =>
    change List.map ((fun τ : Tuple C => τ.mode) ∘ Prod.fst) _ = _
    rw [← List.map_map]
    simp

/-- The initial histories of the real and the ideal check are related. -/
theorem initHist (K : Constants C E) (counts : List ℕ) (D : C.Coalition) (x : C.Party → List (Tuple C))
    (hx : TupleInputs K counts D x) :
    HistRel D 0 0 (fun i => ⟨filledHistory K i (x i), 0, 0⟩) (fun i => ⟨filledHistory K i (dummyOf D x i), 0, 0⟩) := by
  have hz : ∀ (a b : List (Tuple C)) (T : C.Term),
      a.map (fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) =
        b.map (fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) →
      a.map (·.mode) = b.map (·.mode) →
      a.map (fun τ => (τ.mode, vector τ.count (τ.z T))) = b.map (fun τ => (τ.mode, vector τ.count (τ.z T))) := by
    intro a b T h1 h2
    have h3 := congrArg (List.map fun p => p.2.2) h1
    simp only [List.map_map, Function.comp_def] at h3
    exact map_pair_eq a b (·.mode) (fun τ => vector τ.count (τ.z T)) h2 h3
  refine ⟨fun i _ => ⟨rfl, rfl⟩, fun i _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro T hT i hi _
    exact filledHistory_congr K i _ _ T (dummyOf_known_modes D x i hi T hT).symm
  · intro T hT i j hi hj hiT hjT
    have e : ∀ l, filledHistory K i l T = filledHistory K j l T := fun l => by
      unfold filledHistory; simp [hiT, hjT]
    show filledHistory K i (x i) T = filledHistory K j (x j) T
    rw [e]
    exact filledHistory_congr K j _ _ T
      (hz _ _ T (tupleInputs_unknown_vectors K hx T hT i hiT j hjT hi hj) (hx.2.1 i j hi hj))
  · intro T hT i j hi hj hiT hjT
    have e : ∀ l, filledHistory K i l T = filledHistory K j l T := fun l => by
      unfold filledHistory; simp [hiT, hjT]
    show filledHistory K i (dummyOf D x i) T = filledHistory K j (dummyOf D x j) T
    rw [e]
    exact filledHistory_congr K j _ _ T
      (hz _ _ T (canonicalDummyTuples_unknown_vectors K counts D x hx _ T hT i hiT j hjT hi hj)
        ((dummyOf_modes D x i hi).trans ((hx.2.1 i j hi hj).trans (dummyOf_modes D x j hj).symm)))

/-- The initial slice relation of the real and the ideal check: for every coin `τ` with non-zero
slice coins, the weighted lifted tuples and the claims are related (the differences `z - x y` agree
position by position). -/
def CheckInitSlice (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (x : C.Party → List (Tuple C)),
    TupleInputs K counts D x → counts.sum ≠ 0 →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    ∀ τ : List E, (∀ b < sliceBits, τ.getD b 0 ≠ 0) → SliceRel K D τ counts.sum 0
      (fun i T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k) (fun i => liftedPart (x i) (·.y))
      (fun i T k => wordWeightOf K τ counts.sum k * liftedPart (dummyOf D x i) (·.x) T k)
      (fun i => liftedPart (dummyOf D x i) (·.y))
      (fun i => conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0)
      (fun i => conv K (localContext i) (claimOf K τ counts.sum (liftedPart (dummyOf D x i) (·.z))) 0)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A reconstruction from views that exist exactly at the honest operators reads an honest holder. -/
lemma reconstruct_honest {α : Type} [Inhabited α] (D : C.Coalition) (views : C.Party → Option (C.Term → α))
    (T : C.Term) (hc : ∀ i, i ∈ D.1 → views i = none) (hh : ∀ i, i ∉ D.1 → (views i).isSome) :
    ∃ j ∈ C.holders T, j ∉ D.1 ∧ ∃ f, views j = some f ∧ reconstruct views T = f T := by
  obtain ⟨i₀, hi₀T, hi₀D⟩ := exists_honest_holder D T
  unfold reconstruct
  rcases hl : (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) with _ | ⟨f, rest⟩
  · exfalso
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hh i₀ hi₀D)
    have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) :=
      List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [hi₀T, hf]⟩
    rw [hl] at this
    simp at this
  · have hmem : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hmem
    split_ifs at hi with hiT
    have hiD : i ∉ D.1 := fun h => by rw [hc i h] at hi; cases hi
    exact ⟨i, hiT, hiD, f, hi, by simp⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma tupleInputs_count_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (i : C.Party) (hi : i ∉ D.1) (m : ℕ) :
    (x i)[m]?.map (·.count) = counts[m]? := by
  rw [← List.getElem?_map, hx.1 i hi]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The count of a reconstructed tuple is the count of the honest inputs. -/
lemma tupleAt_count (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (m : ℕ) :
    (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count = counts.getD m 0 := by
  obtain ⟨j0, hj0, hf⟩ := firstInput_honest D x
  simp only [tupleAt, hf, tupleInputs_count_at K hx j0 hj0 m, List.getD_eq_getElem?_getD]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma firstInput_length (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) :
    (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length = counts.length := by
  obtain ⟨j0, hj0, hf⟩ := firstInput_honest D x
  rw [hf, ← List.length_map (f := (·.count)), hx.1 j0 hj0]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- Agreeing honest copies, tuple by tuple. -/
lemma agree_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (T : C.Term) (i j : C.Party) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (m g : ℕ) (hm : m < counts.length) (hg : g < counts.getD m 0) :
    (x i)[m]?.map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) = (x j)[m]?.map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) := by
  have hlen := firstInput_length K hx
  have h1 := hagree m (by rw [hlen]; exact hm) T i hiT j hjT hi hj g (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by rw [hlen]; exact hm)]
    simpa [tupleAt_count K hx m] using hg)
  simpa [hi, hj] using h1

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma liftedPart_flat (tuples : List (Tuple C)) (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart (E := E) tuples part T k = match flatPos (tuples.map (·.count)) k with
      | some (m, g) => (tuples[m]?.map fun τ => algebraMap Bit E (part τ T g)).getD 0
      | none => 0 :=
  getD_flatMap_vector_pos (fun τ g => algebraMap Bit E (part τ T g)) tuples k

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- Two lists of tuples with the counts `counts` and equal parts at every position have equal lifted
parts. -/
lemma liftedPart_congr_flat (counts : List ℕ) (a b : List (Tuple C)) (part : Tuple C → Shares C Bit) (T : C.Term)
    (ha : a.map (·.count) = counts) (hb : b.map (·.count) = counts)
    (h : ∀ m g, m < counts.length → g < counts.getD m 0 →
      a[m]?.map (fun τ => part τ T g) = b[m]?.map (fun τ => part τ T g)) :
    liftedPart (E := E) a part T = liftedPart b part T := by
  funext k
  rw [liftedPart_flat, liftedPart_flat, ha, hb]
  rcases hp : flatPos counts k with _ | ⟨m, g⟩
  · rfl
  · obtain ⟨hm, hg⟩ := flatPos_spec counts k m g hp
    have e := h m g hm hg
    simp only
    rw [show a[m]?.map (fun τ => algebraMap Bit E (part τ T g)) =
        (a[m]?.map fun τ => part τ T g).map (algebraMap Bit E) by rw [Option.map_map]; rfl, e,
      Option.map_map]
    rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- With agreeing copies the real lifted parts are one sharing. -/
lemma real_lifted_consistent (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i j : C.Party) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) (hi : i ∉ D.1) (hj : j ∉ D.1) :
    liftedPart (E := E) (x i) part T = liftedPart (x j) part T := by
  refine liftedPart_congr_flat counts _ _ part T (hx.1 i hi) (hx.1 j hj) fun m g hm hg => ?_
  have e := agree_at K hx hagree T i j hiT hjT hi hj m g hm hg
  rcases hpart with rfl | rfl | rfl
  · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map Prod.fst) e
  · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map fun p => p.2.1) e
  · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map fun p => p.2.2) e

/-- Tuple `m` of the ideal input of an honest operator. -/
lemma dummyOf_get (D : C.Coalition) (x : C.Party → List (Tuple C)) (i : C.Party) (hi : i ∉ D.1) (T₀ : C.Term)
    (hT₀ : lackedTerm D.1 = some T₀) (m : ℕ) :
    (dummyOf D x i)[m]? = (x i)[m]?.map fun τ => (⟨knownView D.1 τ.count τ.x, knownView D.1 τ.count τ.y,
      fun T g => if T = T₀ then
        ((multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1.getD m fun _ => 0) g +
          shareValue (tupleAt (checkKnownTuples D x) m).x g * shareValue (tupleAt (checkKnownTuples D x) m).y g -
          ∑ T' ∈ univ.erase T₀, (tupleAt (checkKnownTuples D x) m).z T' g
        else knownView D.1 τ.count τ.z T g, τ.count, τ.mode⟩ : Tuple C) := by
  unfold dummyOf canonicalDummyTuples
  change (((checkKnownTuples D x i).getD []).zipIdx.map _)[m]? = _
  rw [checkKnownTuples_honest D x i hi]
  simp only [Option.getD_some, List.getElem?_map, List.getElem?_zipIdx, hT₀, Option.map_map, zero_add,
    Function.comp_def, checkKnownTuples]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma getElem?_some_of_lt {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)} (K : Constants C E)
    (hx : TupleInputs K counts D x) (i : C.Party) (hi : i ∉ D.1) (m : ℕ) (hm : m < counts.length) :
    ∃ τ, (x i)[m]? = some τ ∧ τ.count = counts.getD m 0 := by
  have h := tupleInputs_count_at K hx i hi m
  rw [List.getElem?_eq_getElem hm] at h
  rcases hτ : (x i)[m]? with _ | τ
  · rw [hτ] at h; cases h
  · rw [hτ] at h
    refine ⟨τ, rfl, ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A part of a reconstructed real tuple is the part of any honest holder. -/
lemma tupleAt_part (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (m g : ℕ) (hm : m < counts.length)
    (hg : g < counts.getD m 0) :
    (x i)[m]?.map (fun τ => part τ T g) = some (part (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m) T g) := by
  have key : ∀ j, j ∈ C.holders T → j ∉ D.1 →
      (x i)[m]?.map (fun τ => part τ T g) = (x j)[m]?.map (fun τ => part τ T g) := by
    intro j hjT hj
    have e := agree_at K hx hagree T i j hiT hjT hi hj m g hm hg
    rcases hpart with rfl | rfl | rfl
    · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map Prod.fst) e
    · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map fun p => p.2.1) e
    · simpa [Option.map_map, Function.comp_def] using congrArg (Option.map fun p => p.2.2) e
  have hviews : ∀ (sel : Tuple C → Shares C Bit),
      ∃ j ∈ C.holders T, j ∉ D.1 ∧ ∃ f, Option.map sel ((if j ∈ D.1 then none else some (x j)).bind (·[m]?))
        = some f ∧ reconstruct (fun i => Option.map sel ((if i ∈ D.1 then none else some (x i)).bind (·[m]?))) T
        = f T := fun sel =>
    reconstruct_honest D _ T (fun i hi => by simp [hi]) (fun i hi => by
      obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx i hi m hm
      simp [hi, hτ])
  rcases hpart with rfl | rfl | rfl
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := hviews (·.x)
    rw [key j hjT (by exact hj)]
    simp only [hj, if_false, Option.bind_some] at hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτ] at hf ⊢
    simp only [Option.map_some, Option.some.injEq] at hf ⊢
    have e : (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x T = f T := hr
    rw [e, ← hf]
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := hviews (·.y)
    rw [key j hjT (by exact hj)]
    simp only [hj, if_false, Option.bind_some] at hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτ] at hf ⊢
    simp only [Option.map_some, Option.some.injEq] at hf ⊢
    have e : (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y T = f T := hr
    rw [e, ← hf]
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := hviews (·.z)
    rw [key j hjT (by exact hj)]
    simp only [hj, if_false, Option.bind_some] at hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτ] at hf ⊢
    simp only [Option.map_some, Option.some.injEq] at hf ⊢
    have e : (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z T = f T := hr
    rw [e, ← hf]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A part of a reconstructed known tuple is the known part of any honest holder. -/
lemma tupleAtKnown_part (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (m g : ℕ) (hm : m < counts.length)
    (hg : g < counts.getD m 0) :
    (x i)[m]?.map (fun τ => knownView D.1 τ.count (part τ) T g) =
      some (part (tupleAt (checkKnownTuples D x) m) T g) := by
  have key : ∀ j, j ∈ C.holders T → j ∉ D.1 →
      (x i)[m]?.map (fun τ => knownView D.1 τ.count (part τ) T g) =
        (x j)[m]?.map (fun τ => knownView D.1 τ.count (part τ) T g) := by
    intro j hjT hj
    have e := agree_at K hx hagree T i j hiT hjT hi hj m g hm hg
    obtain ⟨τi, hτi, hci⟩ := getElem?_some_of_lt K hx i hi m hm
    obtain ⟨τj, hτj, hcj⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [hτi, hτj] at e ⊢
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e ⊢
    simp only [knownView, hci, hcj]
    rcases hpart with rfl | rfl | rfl
    · dsimp only; rw [e.1]
    · dsimp only; rw [e.2.1]
    · dsimp only; rw [e.2.2]
  have hc : ∀ (sel : Tuple C → Shares C Bit), ∀ i, i ∈ D.1 →
      Option.map sel ((checkKnownTuples D x i).bind (·[m]?)) = none := by
    intro sel i hi; simp [checkKnownTuples, multVerifyLeak, hi]
  have hh : ∀ (sel : Tuple C → Shares C Bit), ∀ i, i ∉ D.1 →
      (Option.map sel ((checkKnownTuples D x i).bind (·[m]?))).isSome := by
    intro sel i hi
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx i hi m hm
    rw [checkKnownTuples_honest D x i hi]
    simp [List.getElem?_map, hτ]
  have hfin : ∀ (sel : Tuple C → Shares C Bit) (j : C.Party) (hj : j ∉ D.1) (f : Shares C Bit),
      Option.map sel ((checkKnownTuples D x j).bind (·[m]?)) = some f →
      ∃ τ, (x j)[m]? = some τ ∧ sel ⟨knownView D.1 τ.count τ.x, knownView D.1 τ.count τ.y,
        knownView D.1 τ.count τ.z, τ.count, τ.mode⟩ = f := by
    intro sel j hj f hf
    obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx j hj m hm
    rw [checkKnownTuples_honest D x j hj] at hf
    simp only [Option.bind_some, List.getElem?_map, hτ, Option.map_some, Option.some.injEq] at hf
    exact ⟨τ, hτ, hf⟩
  rcases hpart with rfl | rfl | rfl
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := reconstruct_honest D _ T (hc (·.x)) (hh (·.x))
    obtain ⟨τ, hτ, hτf⟩ := hfin (·.x) j hj f hf
    rw [key j hjT hj, hτ, Option.map_some]; dsimp only
    have e : (tupleAt (checkKnownTuples D x) m).x T = f T := hr
    rw [e, ← hτf]
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := reconstruct_honest D _ T (hc (·.y)) (hh (·.y))
    obtain ⟨τ, hτ, hτf⟩ := hfin (·.y) j hj f hf
    rw [key j hjT hj, hτ, Option.map_some]; dsimp only
    have e : (tupleAt (checkKnownTuples D x) m).y T = f T := hr
    rw [e, ← hτf]
  · obtain ⟨j, hjT, hj, f, hf, hr⟩ := reconstruct_honest D _ T (hc (·.z)) (hh (·.z))
    obtain ⟨τ, hτ, hτf⟩ := hfin (·.z) j hj f hf
    rw [key j hjT hj, hτ, Option.map_some]; dsimp only
    have e : (tupleAt (checkKnownTuples D x) m).z T = f T := hr
    rw [e, ← hτf]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A lifted real part at an honest holder, position by position. -/
lemma lifted_real_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (part : Tuple C → Shares C Bit) (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (k : ℕ) :
    liftedPart (E := E) (x i) part T k = match flatPos counts k with
      | some (m, g) => algebraMap Bit E (part (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m) T g)
      | none => 0 := by
  rw [liftedPart_flat, hx.1 i hi]
  rcases hp : flatPos counts k with _ | ⟨m, g⟩
  · rfl
  · obtain ⟨hm, hg⟩ := flatPos_spec counts k m g hp
    have e := tupleAt_part K hx hagree part hpart T i hiT hi m g hm hg
    simp only
    rw [show (x i)[m]?.map (fun τ => algebraMap Bit E (part τ T g)) =
        ((x i)[m]?.map fun τ => part τ T g).map (algebraMap Bit E) by rw [Option.map_map]; rfl, e]
    rfl

/-- The value of a part of the ideal tuples at a term and a position. -/
def dummyValue (D : C.Coalition) (x : C.Party → List (Tuple C)) (T₀ : C.Term) (which : Fin 3) (T : C.Term)
    (m g : ℕ) : Bit :=
  let σ := tupleAt (checkKnownTuples D x) m
  match which with
  | 0 => σ.x T g
  | 1 => σ.y T g
  | 2 => if T = T₀ then
      ((multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1.getD m fun _ => 0) g +
        shareValue σ.x g * shareValue σ.y g - ∑ T' ∈ univ.erase T₀, σ.z T' g
      else σ.z T g

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma dummy_part_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀) (which : Fin 3)
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (m g : ℕ) (hm : m < counts.length)
    (hg : g < counts.getD m 0) :
    (dummyOf D x i)[m]?.map (fun τ => ([τ.x, τ.y, τ.z].getD which.1 0) T g) =
      some (dummyValue D x T₀ which T m g) := by
  rw [dummyOf_get D x i hi T₀ hT₀ m, Option.map_map]
  fin_cases which
  · have e := tupleAtKnown_part K hx hagree (·.x) (Or.inl rfl) T i hiT hi m g hm hg
    simpa [Function.comp_def, dummyValue] using e
  · have e := tupleAtKnown_part K hx hagree (·.y) (Or.inr (Or.inl rfl)) T i hiT hi m g hm hg
    simpa [Function.comp_def, dummyValue] using e
  · by_cases hT : T = T₀
    · obtain ⟨τ, hτ, -⟩ := getElem?_some_of_lt K hx i hi m hm
      subst hT
      simp [Function.comp_def, dummyValue, hτ]
    · have e := tupleAtKnown_part K hx hagree (·.z) (Or.inr (Or.inr rfl)) T i hiT hi m g hm hg
      simpa [Function.comp_def, dummyValue, hT] using e

/-- A lifted ideal part at an honest holder, position by position. -/
lemma lifted_dummy_at (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀) (which : Fin 3) (part : Tuple C → Shares C Bit)
    (hw : ∀ τ, part τ = [τ.x, τ.y, τ.z].getD which.1 0)
    (T : C.Term) (i : C.Party) (hiT : i ∈ C.holders T) (hi : i ∉ D.1) (k : ℕ) :
    liftedPart (E := E) (dummyOf D x i) part T k = match flatPos counts k with
      | some (m, g) => algebraMap Bit E (dummyValue D x T₀ which T m g)
      | none => 0 := by
  rw [liftedPart_flat, show (dummyOf D x i).map (·.count) = counts from
    canonicalDummyTuples_leak_counts K counts D x hx i hi]
  rcases hp : flatPos counts k with _ | ⟨m, g⟩
  · rfl
  · obtain ⟨hm, hg⟩ := flatPos_spec counts k m g hp
    have e := dummy_part_at K hx hagree T₀ hT₀ which T i hiT hi m g hm hg
    simp only [← hw] at e
    simp only
    rw [show (dummyOf D x i)[m]?.map (fun τ => algebraMap Bit E (part τ T g)) =
        ((dummyOf D x i)[m]?.map fun τ => part τ T g).map (algebraMap Bit E) by rw [Option.map_map]; rfl, e]
    rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- With agreeing copies `F_multVerify` leaks the differences `z - x y` of the reconstructed tuples. -/
lemma leak_difference (K : Constants C E) {counts : List ℕ} {D : C.Coalition} {x : C.Party → List (Tuple C)}
    (hx : TupleInputs K counts D x) (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (m g : ℕ) (hm : m < counts.length) (hg : g < counts.getD m 0) :
    ((multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1.getD m fun _ => 0) g =
      shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z g -
        shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x g *
        shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y g := by
  have hlen := firstInput_length K hx
  have e : (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1 =
      ((List.range (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length).map
        (tupleAt (fun i => if i ∈ D.1 then none else some (x i)))).map fun τ g =>
          if g < τ.count then shareValue τ.z g - shareValue τ.x g * shareValue τ.y g else 0 := by
    simp only [multVerifyLeak]
    exact if_pos hagree
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_range (by rw [hlen]; exact hm)]
  simp only [Option.map_some, Option.getD_some, tupleAt_count K hx m, if_pos hg]

/-- The known lifted parts of the ideal input are those of the real input. -/
lemma dummy_known_lifted (D : C.Coalition) (x : C.Party → List (Tuple C)) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (hT : KnownTo D.1 T) (part : Tuple C → Shares C Bit)
    (hpart : part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) :
    liftedPart (E := E) (dummyOf D x i) part T = liftedPart (x i) part T := by
  have hv := canonicalDummyTuples_known_vectors D x
    (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1 i hi T hT
  have hp : (dummyOf D x i).map (fun τ => vector τ.count (part τ T)) = (x i).map (fun τ => vector τ.count (part τ T)) := by
    rcases hpart with rfl | rfl | rfl
    · have h := congrArg (List.map Prod.fst) hv; simp only [List.map_map, Function.comp_def] at h; exact h
    · have h := congrArg (List.map fun p => p.2.1) hv; simp only [List.map_map, Function.comp_def] at h; exact h
    · have h := congrArg (List.map fun p => p.2.2) hv; simp only [List.map_map, Function.comp_def] at h; exact h
  funext k
  rw [liftedPart_eq, liftedPart_eq, hp]

/-- The initial slice relation holds. -/
theorem checkInitSlice (K : Constants C E) : CheckInitSlice K := by
  intro counts D x hx hpos hagree τ hτ
  letI : CharP E 2 := charP_two
  obtain ⟨T₀, hT₀, -⟩ := lackedTerm_spec D
  choose hd hdT hdD using exists_honest_holder D
  let σR := fun m => tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m
  let gR : (Tuple C → Shares C Bit) → Shares C E := fun part T k => match flatPos counts k with
    | some (m, g) => algebraMap Bit E (part (σR m) T g)
    | none => 0
  let gD : Fin 3 → Shares C E := fun w T k => match flatPos counts k with
    | some (m, g) => algebraMap Bit E (dummyValue D x T₀ w T m g)
    | none => 0
  have hR : ∀ part : Tuple C → Shares C Bit, (part = (·.x) ∨ part = (·.y) ∨ part = (·.z)) →
      ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → liftedPart (x i) part T = gR part T :=
    fun part hpart i hi T hT => funext fun k => lifted_real_at K hx hagree part hpart T i hT hi k
  have hDm : ∀ (w : Fin 3) (part : Tuple C → Shares C Bit), (∀ τ, part τ = [τ.x, τ.y, τ.z].getD w.1 0) →
      ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → liftedPart (dummyOf D x i) part T = gD w T :=
    fun w part hw i hi T hT => funext fun k => lifted_dummy_at K hx hagree T₀ hT₀ w part hw T i hT hi k
  have hX := hR (·.x) (Or.inl rfl)
  have hY := hR (·.y) (Or.inr (Or.inl rfl))
  have hZ := hR (·.z) (Or.inr (Or.inr rfl))
  have hX' := hDm 0 (·.x) (fun _ => rfl)
  have hY' := hDm 1 (·.y) (fun _ => rfl)
  have hZ' := hDm 2 (·.z) (fun _ => rfl)
  have hknown : ∀ T, KnownTo D.1 T → gR (·.x) T = gD 0 T ∧ gR (·.y) T = gD 1 T ∧ gR (·.z) T = gD 2 T := by
    intro T hT
    have h := hdD T
    have hh := hdT T
    refine ⟨?_, ?_, ?_⟩
    · rw [← hX _ h T hh, ← hX' _ h T hh, dummy_known_lifted D x _ h T hT _ (Or.inl rfl)]
    · rw [← hY _ h T hh, ← hY' _ h T hh, dummy_known_lifted D x _ h T hT _ (Or.inr (Or.inl rfl))]
    · rw [← hZ _ h T hh, ← hZ' _ h T hh, dummy_known_lifted D x _ h T hT _ (Or.inr (Or.inr rfl))]
  refine ⟨fun T k => wordWeightOf K τ counts.sum k * gR (·.x) T k, gR (·.y),
    fun T k => wordWeightOf K τ counts.sum k * gD 0 T k, gD 1,
    fun T => claimOf K τ counts.sum (gR (·.z)) T 0 - claimOf K τ counts.sum (gD 2) T 0, ?_, ?_, ?_, ?_⟩
  · intro i hi T hT
    refine ⟨?_, hY i hi T hT, ?_, hY' i hi T hT⟩
    · show (fun k => _) = _; rw [hX i hi T hT]
    · show (fun k => _) = _; rw [hX' i hi T hT]
  · intro T hT
    obtain ⟨e1, e2, e3⟩ := hknown T hT
    refine ⟨by dsimp only; rw [e1], e2, by simp only [claimOf, e3, sub_self]⟩
  · intro i hi
    have e1 : conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0 =
        conv K (localContext i) (claimOf K τ counts.sum (gR (·.z))) 0 :=
      conv_congr i _ _ 0 fun T hT => by simp only [claimOf, hZ i hi T hT]
    have e2 : conv K (localContext i) (claimOf K τ counts.sum (liftedPart (dummyOf D x i) (·.z))) 0 =
        conv K (localContext i) (claimOf K τ counts.sum (gD 2)) 0 :=
      conv_congr i _ _ 0 fun T hT => by simp only [claimOf, hZ' i hi T hT]
    dsimp only
    rw [e1, e2, conv_sub_const]
  · have hC5 : ∀ k, shareValue (gR (·.z)) k - shareValue (gR (·.x)) k * shareValue (gR (·.y)) k =
        shareValue (gD 2) k - shareValue (gD 0) k * shareValue (gD 1) k := by
      intro k
      simp only [shareValue, gR, gD]
      rcases hp : flatPos counts k with _ | ⟨m, g⟩
      · simp
      · obtain ⟨hm, hg⟩ := flatPos_spec counts k m g hp
        simp only [← map_sum, ← map_mul, ← map_sub]
        apply congrArg (algebraMap Bit E)
        have e1 := leak_difference K hx hagree m g hm hg
        have e2 := replace_hidden_difference (tupleAt (checkKnownTuples D x) m) T₀
          ((multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1.getD m fun _ => 0) g
        have e3 : ∀ w : Fin 3, ∀ T, dummyValue D x T₀ w T m g = match w with
            | 0 => (tupleAt (checkKnownTuples D x) m).x T g
            | 1 => (tupleAt (checkKnownTuples D x) m).y T g
            | 2 => if T = T₀ then
                ((multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.1.getD m fun _ => 0) g +
                  shareValue (tupleAt (checkKnownTuples D x) m).x g *
                    shareValue (tupleAt (checkKnownTuples D x) m).y g -
                  ∑ T' ∈ univ.erase T₀, (tupleAt (checkKnownTuples D x) m).z T' g
                else (tupleAt (checkKnownTuples D x) m).z T g := fun w T => rfl
        simp only [e3]
        exact e1.symm.trans e2.symm
    have hlen : sliceLen counts.sum 0 = 2 ^ sliceBits * sliceWidth counts.sum := by
      simp [sliceLen, mul_comm]
    have hL : ∑ T, (claimOf K τ counts.sum (gR (·.z)) T 0 - claimOf K τ counts.sum (gD 2) T 0) =
        ∑ k ∈ range (2 ^ sliceBits * sliceWidth counts.sum),
          coinProduct τ 0 sliceBits (sliceOf counts.sum k) * wordWeightOf K τ counts.sum k *
            (shareValue (gR (·.z)) k - shareValue (gD 2) k) := by
      simp only [claimOf, shareValue, ← Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
      rw [Finset.sum_comm]
    show ∑ T, (claimOf K τ counts.sum (gR (·.z)) T 0 - claimOf K τ counts.sum (gD 2) T 0) = _
    rw [hL, hlen]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw1 : shareValue (fun T k => wordWeightOf K τ counts.sum k * gR (·.x) T k) k =
        wordWeightOf K τ counts.sum k * shareValue (gR (·.x)) k := by
      simp only [shareValue, Finset.mul_sum]
    have hw2 : shareValue (fun T k => wordWeightOf K τ counts.sum k * gD 0 T k) k =
        wordWeightOf K τ counts.sum k * shareValue (gD 0) k := by
      simp only [shareValue, Finset.mul_sum]
    rw [hw1, hw2]
    have h5 := hC5 k
    simp only [sliceWeight, Nat.sub_zero, sliceOf]
    linear_combination (coinProduct τ 0 sliceBits (k / sliceWidth counts.sum) * wordWeightOf K τ counts.sum k) * h5

theorem checkInitRel_of_slice (K : Constants C E) (h : CheckInitSlice K) : CheckInitRel K :=
  fun counts D x hx hpos hagree => ⟨initHist K counts D x hx, h counts D x hx hpos hagree⟩

end InitHist

/-! ## The core distance -/

section Final

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- Step 4 of the plan: `CheckCoupleStage` holds. -/
theorem checkCoupleStage (prims : Primitives) (K : Constants C E) : CheckCoupleStage prims K :=
  checkCoupleStage_of_init prims K (checkInitRel_of_slice K (checkInitSlice K))

/-- `CheckCoreDistance` from the two stages that are still open: the soundness stage and the
disagreement stage. -/
theorem checkCoreDistanceFull (prims : Primitives) (K : Constants C E)
    (hsound : CheckSoundStage prims K) (hsplit : CheckSplitStage prims K) : CheckCoreDistance prims K :=
  checkCoreDistanceProof prims K hsound (checkCoupleStage prims K) hsplit

theorem multVerifyStatementFull (prims : Primitives) (K : Constants C E)
    (hsound : CheckSoundStage prims K) (hsplit : CheckSplitStage prims K) : MultVerifyStatement prims K :=
  multVerifyStatementProof prims K (checkCoreDistanceFull prims K hsound hsplit)

end Final

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.checkCoupleStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.checkCoupleStage

/-- info: 'ThresholdLeanXmssSecurity.checkCoreDistanceFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.checkCoreDistanceFull

/-- info: 'ThresholdLeanXmssSecurity.multVerifyStatementFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.multVerifyStatementFull
