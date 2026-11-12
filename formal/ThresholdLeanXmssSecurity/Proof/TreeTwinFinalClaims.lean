import ThresholdLeanXmssSecurity.Proof.TreeTwinLinked2
import ThresholdLeanXmssSecurity.Proof.TreeCheckMaskExtraction
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkOpenings
import ThresholdLeanXmssSecurity.Proof.TreeSaltGuardedPairBound
import ThresholdLeanXmssSecurity.Proof.SeedHit
import XmssSecurity.Proof.ConsistentQueryBound

/-!
# Final claims under the actual Shamir reduction

The first two coordinates of `treeStagesHalvingUpdate` do not read the
reshared products. A difference confined to coordinate zero is multiplied
by `1 + r` at each accepted challenge. Consequently, translating the later
field masks cannot remove such a difference before final randomization.

A finite cache with two distinct PRF answers supplies such a source input
for `Circuit.identity 1`. The halving instrumentation erases to the exact
source program and extracts accepted challenges from successful runs.
For fixed final masks, two supported public challenges prevent a coupling
of unequal claims that preserves the corrupt recipient's opening view.

A prescribed-table interpretation is realized in the actual logged stream
world, preserving both caches. Actual honest-batch completeness supplies
a successful 40-round prefix, including setup, through the final Coin.
A fixed cooperative recorder replays that prefix with every honest result
present, preserving its scheduled abort at the final opening. That abort
rules out the original semantic wrong-output event for every log.

An exact timed split retains the original continuation programs, including
early aborts. The successful honest execution also supplies live final
opening entries under the same table. Together these give an actual
`TreeStagesReach` witness at fuel 37, after setup, with the recorder ready
to save the opening and abort.

The witness starts from an actually supported, good common prefix. Its
coherent table can retain the two distinct first-job PRF answers; the
auxiliary cache used to select that table is absent from the actual replay. One
fixed recorder and its live final-opening programs survive every finite
public padding program on a supported cache coherent with the same table.
The local opening shape supplies an accepted challenge different from 0
and 1. For this fixed recorder, the original reached-good condition is
equivalent to excluding the budget-domain hash collision and salt reuse;
salt guesses and wrong outputs are excluded. The fixed-setup variant also
retains prescribed private contributions, derived keys and term stream keys
in the contexts at the live opening. Hash coherence and this source support
do not by themselves imply exclusion of collisions or salt reuse.

A concrete AES fixture encodes a term key and the low 128 bits of the round
label in its salt output. Log/cache coherence identifies every actual
logged stream bit with that fixture. For an injective term encoding, actual
source coverage by those keys and bounded labels therefore excludes salt
reuse; the coverage is an explicit hypothesis of that last implication.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinFinalClaims

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

abbrev Claim (E : Type) := (ℕ → E) × (ℕ → E) × E

def atZero (d : E) : ℕ → E := fun k => if k = 0 then d else 0

/-- Both operand folds are fixed before the product reshare is read. -/
theorem halving_operands_ignore_output (ctx : Context C) (width j : ℕ) (p : Claim E)
    (out out' : Shares C E) (r : E) :
    (treeStagesHalvingUpdate K ctx width j p out r).1 =
        (treeStagesHalvingUpdate K ctx width j p out' r).1 ∧
      (treeStagesHalvingUpdate K ctx width j p out r).2.1 =
        (treeStagesHalvingUpdate K ctx width j p out' r).2.1 := ⟨rfl, rfl⟩

theorem atZero_high (length k : ℕ) (d : E) :
    (if k + halvedLength length < length then atZero d (k + halvedLength length) else 0) = 0 := by
  unfold atZero halvedLength
  split_ifs <;> first | rfl | omega

/-- A point difference in an operand survives the exact source halving,
regardless of either product table, context, or previous scalar claim. -/
theorem halving_first_difference (ctx₁ ctx₂ : Context C) (width j : ℕ)
    (p₁ p₂ : Claim E) (out₁ out₂ : Shares C E) (r d : E)
    (difference : p₁.1 - p₂.1 = atZero d) :
    (treeStagesHalvingUpdate K ctx₁ width j p₁ out₁ r).1 -
      (treeStagesHalvingUpdate K ctx₂ width j p₂ out₂ r).1 = atZero ((1 + r) * d) := by
  funext k
  have low := congrFun difference k
  have high := congrFun difference (k + halvedLength (halvedLength^[j] width))
  change p₁.1 k - p₂.1 k = atZero d k at low
  change p₁.1 (k + halvedLength (halvedLength^[j] width)) -
    p₂.1 (k + halvedLength (halvedLength^[j] width)) =
      atZero d (k + halvedLength (halvedLength^[j] width)) at high
  have padded :
      (if k + halvedLength (halvedLength^[j] width) < halvedLength^[j] width
        then p₁.1 (k + halvedLength (halvedLength^[j] width)) else 0) -
      (if k + halvedLength (halvedLength^[j] width) < halvedLength^[j] width
        then p₂.1 (k + halvedLength (halvedLength^[j] width)) else 0) = 0 := by
    by_cases h : k + halvedLength (halvedLength^[j] width) < halvedLength^[j] width
    · rw [if_pos h, if_pos h, high]
      simpa only [if_pos h] using atZero_high (halvedLength^[j] width) k d
    · simp only [if_neg h, sub_self]
  change p₁.1 k + r * (p₁.1 k + _) - (p₂.1 k + r * (p₂.1 k + _)) = _
  calc _ = (1 + r) * (p₁.1 k - p₂.1 k) + r *
        ((if k + halvedLength (halvedLength^[j] width) < halvedLength^[j] width
          then p₁.1 (k + halvedLength (halvedLength^[j] width)) else 0) -
        (if k + halvedLength (halvedLength^[j] width) < halvedLength^[j] width
          then p₂.1 (k + halvedLength (halvedLength^[j] width)) else 0)) := by ring
    _ = atZero ((1 + r) * d) k := by
      rw [padded, low]
      simp only [atZero]
      split_ifs <;> ring

/-- The same calculation applies to the second operand, independently of
the product reshare and of the first operand. -/
theorem halving_second_difference (ctx₁ ctx₂ : Context C) (width j : ℕ)
    (p₁ p₂ : Claim E) (out₁ out₂ : Shares C E) (r d : E)
    (difference : p₁.2.1 - p₂.2.1 = atZero d) :
    (treeStagesHalvingUpdate K ctx₁ width j p₁ out₁ r).2.1 -
      (treeStagesHalvingUpdate K ctx₂ width j p₂ out₂ r).2.1 = atZero ((1 + r) * d) := by
  exact halving_first_difference K ctx₁ ctx₂ width j
    (p₁.2.1, p₁.1, p₁.2.2) (p₂.2.1, p₂.1, p₂.2.2) out₁ out₂ r d difference

theorem one_add_challenge_ne_zero (r : E) (hr : r ≠ 1) : 1 + r ≠ 0 := by
  intro h
  apply hr
  have two : (1 : E) + 1 = 0 := by
    haveI : CharP E 2 := charP_two
    exact CharTwo.add_self_eq_zero 1
  linear_combination h - two

/-- Both scalar claims are kept; each side has its own actual reshare
output. The transcript records only the common challenge and its index. -/
def reduceTranscript (ctx₁ ctx₂ : Context C) (width : ℕ)
    (transcript : List (ℕ × Shares C E × Shares C E × E)) (p : Claim E × Claim E) :
    Claim E × Claim E :=
  transcript.foldl (fun p row =>
    (treeStagesHalvingUpdate K ctx₁ width row.1 p.1 row.2.1 row.2.2.2,
      treeStagesHalvingUpdate K ctx₂ width row.1 p.2 row.2.2.1 row.2.2.2)) p

def challengeFactor (transcript : List (ℕ × Shares C E × Shares C E × E)) : E :=
  (transcript.map fun row => 1 + row.2.2.2).prod

theorem reduceTranscript_first_difference (ctx₁ ctx₂ : Context C) (width : ℕ)
    (transcript : List (ℕ × Shares C E × Shares C E × E)) (p₁ p₂ : Claim E) (d : E)
    (difference : p₁.1 - p₂.1 = atZero d) :
    (reduceTranscript K ctx₁ ctx₂ width transcript (p₁, p₂)).1.1 -
      (reduceTranscript K ctx₁ ctx₂ width transcript (p₁, p₂)).2.1 =
        atZero (challengeFactor transcript * d) := by
  induction transcript generalizing p₁ p₂ d with
  | nil => simpa only [reduceTranscript, List.foldl_nil, challengeFactor, List.map_nil, List.prod_nil, one_mul] using difference
  | cons row transcript ih =>
    have step := halving_first_difference K ctx₁ ctx₂ width row.1 p₁ p₂ row.2.1 row.2.2.1 row.2.2.2 d difference
    have rest := ih _ _ _ step
    simpa only [reduceTranscript, List.foldl_cons, challengeFactor, List.map_cons, List.prod_cons,
      mul_assoc, mul_left_comm, mul_comm] using rest

theorem challengeFactor_ne_zero (transcript : List (ℕ × Shares C E × Shares C E × E))
    (valid : ∀ row ∈ transcript, row.2.2.2 ≠ 1) : challengeFactor transcript ≠ 0 := by
  induction transcript with
  | nil => simp [challengeFactor]
  | cons row rows ih =>
    simp only [challengeFactor, List.map_cons, List.prod_cons]
    exact mul_ne_zero (one_add_challenge_ne_zero row.2.2.2 (valid row (by simp)))
      (ih (fun q hq => valid q (List.mem_cons_of_mem _ hq)))

/-- No choices of the two reshare-output transcripts can make these final
operand shares equal when the starting point difference is nonzero. -/
theorem reduceTranscript_first_ne (ctx₁ ctx₂ : Context C) (width : ℕ)
    (transcript : List (ℕ × Shares C E × Shares C E × E)) (p₁ p₂ : Claim E) (d : E)
    (different : d ≠ 0) (difference : p₁.1 - p₂.1 = atZero d)
    (valid : ∀ row ∈ transcript, row.2.2.2 ≠ 1) :
    (reduceTranscript K ctx₁ ctx₂ width transcript (p₁, p₂)).1.1 0 ≠
      (reduceTranscript K ctx₁ ctx₂ width transcript (p₁, p₂)).2.1 0 := by
  intro equal
  have diff := congrFun (reduceTranscript_first_difference K ctx₁ ctx₂ width transcript p₁ p₂ d difference) 0
  simp only [Pi.sub_apply, atZero, equal, sub_self] at diff
  exact mul_ne_zero (challengeFactor_ne_zero transcript valid) different diff.symm

/-- The source slice also preserves a point difference. Its slice width
is positive for every nonempty check, so no high coordinate reaches zero. -/
theorem slice_first_difference (ctx₁ ctx₂ : Context C) (τ₁ τ₂ : List E) (count j : ℕ)
    (nonempty : count ≠ 0) (p₁ p₂ : Shares C E × Shares C E × E)
    (out₁ out₂ : Shares C E) (r : E) (d : C.Term → E)
    (difference : ∀ T, p₁.1 T - p₂.1 T = atZero (d T)) :
    ∀ T, (treeStagesSliceUpdate K ctx₁ τ₁ count j p₁ out₁ r).1 T -
      (treeStagesSliceUpdate K ctx₂ τ₂ count j p₂ out₂ r).1 T = atZero ((1 + r) * d T) := by
  have half : 0 < sliceWidth count * 2 ^ (sliceBits - 1 - j) :=
    Nat.mul_pos (sliceWidth_pos nonempty) (by positivity)
  intro T
  funext k
  have low := congrFun (difference T) k
  have high := congrFun (difference T) (k + sliceWidth count * 2 ^ (sliceBits - 1 - j))
  change p₁.1 T k - p₂.1 T k = atZero (d T) k at low
  have highZero : p₁.1 T (k + sliceWidth count * 2 ^ (sliceBits - 1 - j)) -
      p₂.1 T (k + sliceWidth count * 2 ^ (sliceBits - 1 - j)) = 0 := by
    simpa only [Pi.sub_apply, atZero, if_neg (show k + sliceWidth count * 2 ^ (sliceBits - 1 - j) ≠ 0 by omega)] using high
  change p₁.1 T k + r * (p₁.1 T k + _) - (p₂.1 T k + r * (p₂.1 T k + _)) = _
  calc _ = (1 + r) * (p₁.1 T k - p₂.1 T k) + r *
        (p₁.1 T (k + sliceWidth count * 2 ^ (sliceBits - 1 - j)) -
          p₂.1 T (k + sliceWidth count * 2 ^ (sliceBits - 1 - j))) := by ring
    _ = atZero ((1 + r) * d T) k := by
      rw [highZero, low]
      simp only [atZero]
      split_ifs <;> ring

/-- `Conv` takes the same point difference to its actual Shamir share.
This keeps the complete term coefficient vector, rather than only a bound. -/
theorem conv_point_difference (ctx : Context C) (x₁ x₂ : Shares C E) (d : C.Term → E)
    (difference : ∀ T, x₁ T - x₂ T = atZero (d T)) :
    conv K ctx x₁ - conv K ctx x₂ = atZero (conv K ctx (fun T _ => d T) 0) := by
  funext k
  change (∑ T ∈ Finset.univ.filter (ctx.self ∈ C.holders ·), psi K T ctx.self * x₁ T k) -
      (∑ T ∈ Finset.univ.filter (ctx.self ∈ C.holders ·), psi K T ctx.self * x₂ T k) = _
  rw [← Finset.sum_sub_distrib]
  have term : ∀ T, psi K T ctx.self * x₁ T k - psi K T ctx.self * x₂ T k =
      psi K T ctx.self * atZero (d T) k := by
    intro T
    rw [← mul_sub]
    exact congrArg (psi K T ctx.self * ·) (congrFun (difference T) k)
  simp_rw [term]
  by_cases hk : k = 0
  · simp only [atZero, if_pos hk]
    rfl
  · simp only [atZero, if_neg hk, mul_zero, Finset.sum_const_zero]

/-- A nonzero aggregate coefficient cannot disappear at every honest
Shamir evaluation. The honest quorum determines the polynomial. -/
theorem exists_honest_nonzero_conv (D : C.Coalition) (d : C.Term → E)
    (nonzero : ∑ T, d T ≠ 0) :
    ∃ i, i ∉ D.1 ∧ conv K (localContext i) (fun T _ => d T) 0 ≠ 0 := by
  by_contra h
  push Not at h
  haveI : CharP E 2 := charP_two
  obtain ⟨P, degree, value, points⟩ := cdi05_conv_correct K d
  have zero : P = 0 := poly_eq_of_honest K D P 0 (degree_lt_of_natDegree P degree)
    (by simp) (fun i hi => by
      rw [← points i]
      simpa only [Polynomial.eval_zero] using h i hi)
  apply nonzero
  rw [← value, zero]
  simp

/-- An actual nonzero Shamir operand difference cannot be repaired by
any later halving field outputs at all live honest senders. -/
theorem exists_honest_final_difference (D : C.Coalition) (d : C.Term → E)
    (nonzero : ∑ T, d T ≠ 0) (width : ℕ)
    (p₁ p₂ : C.Party → Claim E)
    (difference : ∀ i, i ∉ D.1 → (p₁ i).1 - (p₂ i).1 =
      atZero (conv K (localContext i) (fun T _ => d T) 0))
    (transcript : C.Party → List (ℕ × Shares C E × Shares C E × E))
    (valid : ∀ i, i ∉ D.1 → ∀ row ∈ transcript i, row.2.2.2 ≠ 1) :
    ∃ i, i ∉ D.1 ∧
      (reduceTranscript K (localContext i) (localContext i) width (transcript i) (p₁ i, p₂ i)).1.1 0 ≠
      (reduceTranscript K (localContext i) (localContext i) width (transcript i) (p₁ i, p₂ i)).2.1 0 := by
  obtain ⟨i, hi, hn⟩ := exists_honest_nonzero_conv K D d nonzero
  exact ⟨i, hi, reduceTranscript_first_ne K _ _ width (transcript i) (p₁ i) (p₂ i) _ hn
    (difference i hi) (valid i hi)⟩

/-- Record precisely the products and challenges consumed by the source
halving fold. No extra oracle query or random draw is inserted. -/
def halvingRecorded {ι : Type} {G : OracleSpec ι} (ctx : Context C)
    (gadgets : CheckGadgets C E G) (width : ℕ) :
    List ℕ → Claim E → RunM C E G (Claim E × List (ℕ × Shares C E × E))
  | [], p => pure (p, [])
  | j :: rest, p => do
      let out ← gadgets.extendMult (treeStagesHalvingProducts width j p)
      let r ← challenge K gadgets
      let result ← halvingRecorded ctx gadgets width rest
        (treeStagesHalvingUpdate K ctx width j p out r)
      pure (result.1, (j, out, r) :: result.2)

/-- Erasure is the exact source program, for arbitrary gadgets and hence
also for the real PRSS network gadgets. -/
theorem halvingRecorded_erase {ι : Type} {G : OracleSpec ι} (ctx : Context C)
    (gadgets : CheckGadgets C E G) (width : ℕ) (remaining : List ℕ) (p : Claim E) :
    Prod.fst <$> halvingRecorded K ctx gadgets width remaining p =
      remaining.foldlM (halvingStep K ctx gadgets width) p := by
  induction remaining generalizing p with
  | nil => simp only [halvingRecorded, List.foldlM_nil, map_pure]
  | cons j rest ih =>
    have step : halvingStep K ctx gadgets width p j = (do
        let out ← gadgets.extendMult (treeStagesHalvingProducts width j p)
        let r ← challenge K gadgets
        pure (treeStagesHalvingUpdate K ctx width j p out r)) := by
      rcases p with ⟨a, b, d⟩
      rfl
    simp only [halvingRecorded, List.foldlM_cons, map_bind]
    rw [step]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro out
    apply bind_congr
    intro r
    simpa only [map_bind, map_pure, bind_pure_comp, pure_bind,
      treeStagesHalvingUpdate] using ih (treeStagesHalvingUpdate K ctx width j p out r)

/-- The smallest source run with a nonempty check: an identity circuit
with one output has exactly its output-rerandomization tuple. -/
theorem identity_one_run {ι : Type} {G : OracleSpec ι}
    (gadgets : RunGadgets C E G) (input : C.Term → List Bit) :
    runJobs K gadgets [Circuit.identity 1] [input] = (do
      let z ← gadgets.rerand (outputShares K [Circuit.identity 1] [input]) 1
      gadgets.verify [⟨outputShares K [Circuit.identity 1] [input], one K, z, 1, .peer⟩]
      let opened ← gadgets.output z 1
      pure [[opened 0]]) := by
  rw [runJobs_eq]
  simp only [depth, Circuit.identity, List.map_cons, List.map_nil,
    List.length_nil, List.foldl_cons, List.foldl_nil, Nat.max_self,
    List.range_zero, List.foldlM_nil, pure_bind, tailBody, outputsOf,
    List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
  congr 1

theorem identity_one_output (input : C.Term → List Bit) :
    outputShares K [Circuit.identity 1] [input] =
      fun T k => if k = 0 then (input T).getD 0 0 else 0 := by
  funext T k
  cases k <;> simp [outputShares, outputsOf, Circuit.identity, Affine.share]

/-- The exact weighted first operand at entry to the identity run's
check. Neither rerandomized output nor product correction occurs in it. -/
theorem identity_one_initial (τ : List E) (input : C.Term → List Bit) (z : Shares C Bit) :
    (fun T k => wordWeightOf K τ 1 k *
      liftedPart [⟨outputShares K [Circuit.identity 1] [input], one K, z, 1, .peer⟩]
        Tuple.x T k) =
      fun T => atZero (K.weight (bitOf 0) * algebraMap Bit E ((input T).getD 0 0)) := by
  funext T k
  rw [identity_one_output]
  cases k <;> simp [liftedPart, vector, atZero, wordWeightOf, wordOf, coinProduct]

theorem identity_one_initial_difference (τ : List E) (input₁ input₂ : C.Term → List Bit)
    (z₁ z₂ : Shares C Bit) :
    ∀ T,
      (fun k => wordWeightOf K τ 1 k *
        liftedPart [⟨outputShares K [Circuit.identity 1] [input₁], one K, z₁, 1, .peer⟩]
          Tuple.x T k) -
      (fun k => wordWeightOf K τ 1 k *
        liftedPart [⟨outputShares K [Circuit.identity 1] [input₂], one K, z₂, 1, .peer⟩]
          Tuple.x T k) =
      atZero (K.weight (bitOf 0) *
        (algebraMap Bit E ((input₁ T).getD 0 0) - algebraMap Bit E ((input₂ T).getD 0 0))) := by
  intro T
  have left := congrFun (identity_one_initial K τ input₁ z₁) T
  have right := congrFun (identity_one_initial K τ input₂ z₂) T
  rw [left, right]
  funext k
  simp only [Pi.sub_apply, atZero]
  split_ifs <;> ring

/-- Two distinct PRF queries with distinct answers. This is a finite
cache, rather than a constant hash oracle. -/
def inputCache (x : Point) : HashCache C :=
  ((∅ : HashCache C).cacheQuery (.prf 0 x) 0).cacheQuery (.prf 1 x) 1

theorem inputCache_zero (x : Point) : inputCache (C := C) x (.prf 0 x) = some 0 := by
  have different : (Query.prf (C := C) 0 x) ≠ .prf 1 x := by
    intro equal
    exact (by decide : (0 : HashOutput) ≠ 1) (Query.prf.inj equal).1
  unfold inputCache
  rw [QueryCache.cacheQuery_of_ne _ _ different]
  simp

theorem inputCache_one (x : Point) : inputCache (C := C) x (.prf 1 x) = some 1 := by
  simp [inputCache]

/-- Each first PRF query can return the selected hash value under the
actual random-oracle handler. -/
theorem prf_answer_support (prims : Primitives) (cache : HashCache C)
    (seed value : HashOutput) (x : Point) (missing : cache (.prf seed x) = none) :
    (value, cache.cacheQuery (.prf seed x) value) ∈ support
      ((hashAnswer prims (.prf seed x)).run cache) := by
  change (value, cache.cacheQuery (.prf seed x) value) ∈ support
    (((Query C →ₒ HashOutput).randomOracle (.prf seed x)).run cache)
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ missing, support_map]
  exact ⟨value, by simp [uniformSampleImpl], rfl⟩

/-- The concrete input cache is produced by two actual distinct PRF
hash queries, starting from the empty cache. -/
theorem inputCache_reachable (prims : Primitives) (x : Point) :
    ((), inputCache (C := C) x) ∈ support ((do
      let _ ← hashAnswer prims (.prf (C := C) 0 x)
      let _ ← hashAnswer prims (.prf (C := C) 1 x)
      pure ()).run ∅) := by
  have different : (Query.prf (C := C) 1 x) ≠ .prf 0 x := by
    intro equal
    exact (by decide : (1 : HashOutput) ≠ 0) (Query.prf.inj equal).1
  have missing : ((∅ : HashCache C).cacheQuery (.prf 0 x) 0) (.prf 1 x) = none := by
    rw [QueryCache.cacheQuery_of_ne _ _ different]
    rfl
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff]
  refine ⟨(0, (∅ : HashCache C).cacheQuery (.prf 0 x) 0),
    prf_answer_support prims ∅ 0 0 x rfl, (1, inputCache x),
    prf_answer_support prims _ 1 1 x missing, ?_⟩
  simp

/-- With seed 1 at one held term and seed 0 elsewhere, the actual cached
input reader returns first bit 1 exactly at that term. -/
theorem cached_input_first (ctx : Context C) (x : Point) (T₀ : C.Term)
    (seeds : ∀ T, ctx.keys.seed T = if T = T₀ then 1 else 0) (T : C.Term) :
    (treeStagesCachedInputs (inputCache x) ctx ⟨.randomizer, [x]⟩ T).getD 0 0 =
      if ctx.self ∈ C.holders T ∧ T = T₀ then 1 else 0 := by
  unfold treeStagesCachedInputs
  by_cases held : ctx.self ∈ C.holders T
  · simp only [if_pos held, inputBits, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [seeds]
    by_cases same : T = T₀
    · rw [if_pos same, inputCache_one]
      simp only [Option.getD_some, if_pos (show ctx.self ∈ C.holders T ∧ T = T₀ from ⟨held, same⟩)]
      rw [getD_bitsOfDigest _ _ (by decide)]
      norm_num [truncateHash, digestBits, hashOutputBits]
      exact BitVec.getElem_one (by decide)
    · rw [if_neg same, inputCache_zero]
      simp only [Option.getD_some, if_neg (by tauto : ¬ (ctx.self ∈ C.holders T ∧ T = T₀))]
      rw [getD_bitsOfDigest _ _ (by decide)]
      norm_num [truncateHash, digestBits, hashOutputBits]
      exact BitVec.getElem_zero (by decide)
  · simp [held]

theorem cached_dummy_input_first (ctx : Context C) (x : Point)
    (seeds : ∀ T, ctx.keys.seed T = 0) (T : C.Term) :
    (treeStagesCachedInputs (inputCache x) ctx ⟨.randomizer, [x]⟩ T).getD 0 0 = 0 := by
  unfold treeStagesCachedInputs
  split_ifs
  · simp only [inputBits, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [seeds, inputCache_zero]
    simp only [Option.getD_some]
    rw [getD_bitsOfDigest _ _ (by decide)]
    norm_num [truncateHash, digestBits, hashOutputBits]
    exact BitVec.getElem_zero (by decide)
  · rfl

/-- The finite cache covers every PRF read of this one-point job under
the real seed family, so the input replay theorem applies to it. -/
theorem inputCache_covers (ctx : Context C) (x : Point) (T₀ : C.Term)
    (seeds : ∀ T, ctx.keys.seed T = if T = T₀ then 1 else 0) :
    TreeStagesPrfCovered (inputCache x) ctx.keys.seed [⟨.randomizer, [x]⟩] := by
  intro job hj y hy T
  simp only [List.mem_singleton] at hj
  subst job
  simp only [List.mem_singleton] at hy
  subst y
  rw [seeds]
  by_cases same : T = T₀
  · rw [if_pos same]
    exact ⟨1, inputCache_one x⟩
  · rw [if_neg same]
    exact ⟨0, inputCache_zero x⟩

/-- Replacing all unknown seeds by 0 sends this real seed family to the
all-zero family, exactly as in `treeSimIdealCont`. -/
theorem hidden_single_seed_dummy (D : C.Coalition) (T₀ : C.Term)
    (hidden : ¬ KnownTo D.1 T₀) (T : C.Term) :
    (if KnownTo D.1 T then (if T = T₀ then (1 : HashOutput) else 0) else 0) = 0 := by
  by_cases same : T = T₀
  · subst T
    simp only [if_neg hidden]
  · simp only [if_neg same, ite_self]

/-- The actual cached PRF inputs produce a nonzero, single-coordinate
first operand in the identity check at every holder of the hidden term. -/
theorem cached_identity_initial_difference (ctx₁ ctx₂ : Context C) (τ : List E)
    (x : Point) (T₀ : C.Term) (held : ctx₁.self ∈ C.holders T₀)
    (seeds₁ : ∀ T, ctx₁.keys.seed T = if T = T₀ then 1 else 0)
    (seeds₂ : ∀ T, ctx₂.keys.seed T = 0) (z₁ z₂ : Shares C Bit) :
    let input₁ := treeStagesCachedInputs (inputCache x) ctx₁ ⟨.randomizer, [x]⟩
    let input₂ := treeStagesCachedInputs (inputCache x) ctx₂ ⟨.randomizer, [x]⟩
    ∀ T,
      (fun k => wordWeightOf K τ 1 k *
        liftedPart [⟨outputShares K [Circuit.identity 1] [input₁], one K, z₁, 1, .peer⟩]
          Tuple.x T k) -
      (fun k => wordWeightOf K τ 1 k *
        liftedPart [⟨outputShares K [Circuit.identity 1] [input₂], one K, z₂, 1, .peer⟩]
          Tuple.x T k) = atZero (if T = T₀ then K.weight (bitOf 0) else 0) := by
  intro input₁ input₂ T
  rw [identity_one_initial_difference K τ input₁ input₂ z₁ z₂]
  change atZero (K.weight (bitOf 0) *
    (algebraMap Bit E ((treeStagesCachedInputs (inputCache x) ctx₁ ⟨.randomizer, [x]⟩ T).getD 0 0) -
      algebraMap Bit E ((treeStagesCachedInputs (inputCache x) ctx₂ ⟨.randomizer, [x]⟩ T).getD 0 0))) = _
  rw [cached_input_first ctx₁ x T₀ seeds₁, cached_dummy_input_first ctx₂ x seeds₂]
  by_cases same : T = T₀
  · subst T
    simp only [held, and_self, if_true, map_one, map_zero, sub_zero, mul_one]
  · simp only [same, and_false, if_false, map_zero, sub_self, mul_zero]

theorem identity_coefficient_sum_ne_zero (T₀ : C.Term) :
    (∑ T, if T = T₀ then K.weight (bitOf 0) else 0) ≠ 0 := by
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using
    K.weight_independent.ne_zero (bitOf 0)

/-- Every successful actual halving fold has a recorded execution with
the same final claim and complete run state. -/
theorem halvingRecorded_exists {ι : Type} {G : OracleSpec ι} (ctx : Context C)
    (gadgets : CheckGadgets C E G) (width : ℕ) (remaining : List ℕ) (p final : Claim E)
    (st st' : RunState C)
    (reached : some (final, st') ∈ support
      (((remaining.foldlM (halvingStep K ctx gadgets width) p).run st).run)) :
    ∃ transcript, some ((final, transcript), st') ∈ support
      (((halvingRecorded K ctx gadgets width remaining p).run st).run) := by
  rw [← halvingRecorded_erase K ctx gadgets width remaining p] at reached
  simp only [StateT.run_map, OptionT.run_map, support_map, Set.mem_image] at reached
  obtain ⟨out, hout, he⟩ := reached
  cases out with
  | none => cases he
  | some out =>
    cases he
    exact ⟨out.1.2, hout⟩

/-- Successful source challenges always avoid 0 and 1, even before
interpreting network or hash oracles. -/
theorem challenge_support {ι : Type} {G : OracleSpec ι}
    (gadgets : CheckGadgets C E G) (st st' : RunState C) (r : E)
    (reached : some (r, st') ∈ support (((challenge K gadgets).run st).run)) :
    r ≠ 0 ∧ r ≠ 1 := by
  simp only [challenge, StateT.run_bind, StateT.run_lift] at reached
  obtain ⟨key, _, reached⟩ := treeSimCheck_some_bind _ _ _ reached
  obtain ⟨result, hresult, reached⟩ := treeSimCheck_some_bind _ _ _ reached
  obtain ⟨value, hvalue, equal⟩ := treeSimCheck_some_bind _ _ _ hresult
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff,
    Option.some.injEq] at equal
  subst result
  simp only [oracleStep, localStep, OptionT.run_lift, bind_pure_comp,
    support_map, Set.mem_image] at hvalue
  obtain ⟨value', hvalue, equal⟩ := hvalue
  cases equal
  cases value with
  | none => simp [StateT.run_lift, OptionT.run_failure] at reached
  | some value =>
    simp only [StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at reached
    obtain ⟨rfl, _⟩ := reached
    have inner := mem_support_of_mem_support_liftComp _ _ _ hvalue
    have original := mem_support_of_mem_support_liftComp _ _ _ inner
    exact findChallenge_support K key.1 challengeTries 0 (some r) original r rfl

def recordedReduce (ctx : Context C) (width : ℕ)
    (transcript : List (ℕ × Shares C E × E)) (p : Claim E) : Claim E :=
  transcript.foldl (fun p row => treeStagesHalvingUpdate K ctx width row.1 p row.2.1 row.2.2) p

/-- A successful instrumented execution records exactly its halving
schedule, accepted challenges and resulting source claim. -/
theorem halvingRecorded_support {ι : Type} {G : OracleSpec ι} (ctx : Context C)
    (gadgets : CheckGadgets C E G) (width : ℕ) (remaining : List ℕ) (p final : Claim E)
    (st st' : RunState C) (transcript : List (ℕ × Shares C E × E))
    (reached : some ((final, transcript), st') ∈ support
      (((halvingRecorded K ctx gadgets width remaining p).run st).run)) :
    final = recordedReduce K ctx width transcript p ∧ transcript.map Prod.fst = remaining ∧
      ∀ row ∈ transcript, row.2.2 ≠ 0 ∧ row.2.2 ≠ 1 := by
  induction remaining generalizing p final st st' transcript with
  | nil =>
    simp only [halvingRecorded, StateT.run_pure, OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at reached
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := reached
    simp [recordedReduce]
  | cons j rest ih =>
    simp only [halvingRecorded, StateT.run_bind, StateT.run_pure] at reached
    obtain ⟨out, _, reached⟩ := treeSimCheck_some_bind _ _ _ reached
    obtain ⟨challenge, valid, reached⟩ := treeSimCheck_some_bind _ _ _ reached
    obtain ⟨result, tail, reached⟩ := treeSimCheck_some_bind _ _ _ reached
    simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at reached
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := reached
    have tailFacts := ih _ _ _ _ _ tail
    refine ⟨tailFacts.1, by simp only [List.map_cons, tailFacts.2.1], ?_⟩
    intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · exact challenge_support K gadgets out.2 challenge.2 challenge.1 valid
    · exact tailFacts.2.2 row hrow

/-- Two recorded source folds that see the same indexed challenges retain
a nonzero point difference, independently of both product transcripts. -/
theorem recordedReduce_point_difference (ctx₁ ctx₂ : Context C) (width : ℕ)
    (left right : List (ℕ × Shares C E × E))
    (same : left.map (fun row => (row.1, row.2.2)) = right.map (fun row => (row.1, row.2.2)))
    (p₁ p₂ : Claim E) (d : E) (nonzero : d ≠ 0)
    (difference : p₁.1 - p₂.1 = atZero d)
    (valid : ∀ row ∈ left, row.2.2 ≠ 1) :
    ∃ e, e ≠ 0 ∧
      (recordedReduce K ctx₁ width left p₁).1 - (recordedReduce K ctx₂ width right p₂).1 = atZero e := by
  induction left generalizing right p₁ p₂ d with
  | nil =>
    cases right with
    | nil => exact ⟨d, nonzero, difference⟩
    | cons _ _ => simp only [List.map_nil, List.map_cons] at same; cases same
  | cons row rows ih =>
    cases right with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at same
    | cons other others =>
      obtain ⟨⟨indices, challenges⟩, rest⟩ :
          (row.1 = other.1 ∧ row.2.2 = other.2.2) ∧
          rows.map (fun row => (row.1, row.2.2)) = others.map (fun row => (row.1, row.2.2)) := by
        simpa only [List.map_cons, List.cons.injEq, Prod.mk.injEq] using same
      have step := halving_first_difference K ctx₁ ctx₂ width row.1 p₁ p₂
        row.2.1 other.2.1 row.2.2 d difference
      rw [indices, challenges] at step
      exact ih others rest _ _ ((1 + other.2.2) * d)
        (mul_ne_zero (one_add_challenge_ne_zero _ (by
          rw [← challenges]
          exact valid row (by simp))) nonzero) (by simpa only [indices, challenges] using step)
        (fun x hx => valid x (List.mem_cons_of_mem _ hx))

/-- This obstruction uses successful executions of the actual source
folds. The only synchronization premise is equality of their recorded
indexed challenges; no premise relates either field-output transcript. -/
theorem halving_sources_no_repair {ι : Type} {G : OracleSpec ι}
    (ctx₁ ctx₂ : Context C) (gadgets₁ gadgets₂ : CheckGadgets C E G) (width : ℕ)
    (remaining : List ℕ) (p₁ p₂ final₁ final₂ : Claim E) (d : E)
    (nonzero : d ≠ 0) (difference : p₁.1 - p₂.1 = atZero d)
    (st₁ st₂ st₁' st₂' : RunState C) (left right : List (ℕ × Shares C E × E))
    (run₁ : some ((final₁, left), st₁') ∈ support
      (((halvingRecorded K ctx₁ gadgets₁ width remaining p₁).run st₁).run))
    (run₂ : some ((final₂, right), st₂') ∈ support
      (((halvingRecorded K ctx₂ gadgets₂ width remaining p₂).run st₂).run))
    (same : left.map (fun row => (row.1, row.2.2)) = right.map (fun row => (row.1, row.2.2))) :
    final₁.1 0 ≠ final₂.1 0 := by
  have leftFacts := halvingRecorded_support K ctx₁ gadgets₁ width remaining p₁ final₁ st₁ st₁' left run₁
  have rightFacts := halvingRecorded_support K ctx₂ gadgets₂ width remaining p₂ final₂ st₂ st₂' right run₂
  obtain ⟨e, he, hd⟩ := recordedReduce_point_difference K ctx₁ ctx₂ width left right same p₁ p₂ d
    nonzero difference (fun row hrow => (leftFacts.2.2 row hrow).2)
  rw [← leftFacts.1, ← rightFacts.1] at hd
  intro equal
  have at0 := congrFun hd 0
  simp only [Pi.sub_apply, equal, sub_self, atZero] at at0
  exact he at0.symm

/-- A coupling supplies a related right result for every supported left
result, with its actual right marginal support. -/
theorem coupling_support_right {α β : Type} {left : ProbComp α} {right : ProbComp β}
    {R : α → β → Prop} (coupled : RelTriple left right R)
    (a : α) (ha : a ∈ support left) : ∃ b ∈ support right, R a b := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at coupled
  obtain ⟨joint, related⟩ := coupled
  have had : a ∈ support 𝒟[left] := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at ha ⊢
    exact ha
  rw [← joint.2.map_fst, support_map] at had
  obtain ⟨pair, hp, he⟩ := had
  have hbd : pair.2 ∈ support 𝒟[right] := by
    rw [← joint.2.map_snd, support_map]
    exact ⟨pair, hp, rfl⟩
  have hb : pair.2 ∈ support right := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hbd ⊢
    exact hbd
  exact ⟨pair.2, hb, he ▸ related pair hp⟩

/-- If a public challenge and its final opening are coupled exactly, the
actual opening functions agree at every supported left challenge. The two
challenge samplers need not have been coupled by the identity. -/
theorem final_kernel_pointwise (ctx₁ ctx₂ : Context C) (p₁ p₂ : Claim E)
    (w₁ w₂ q₁ q₂ : Shares C E) (left right : ProbComp E)
    (coupled : RelTriple
      ((fun r => (r, TreeTwinLinked2.finalVector K ctx₁ p₁ w₁ q₁ r)) <$> left)
      ((fun r => (r, TreeTwinLinked2.finalVector K ctx₂ p₂ w₂ q₂ r)) <$> right)
      Eq) :
    ∀ r ∈ support left,
      TreeTwinLinked2.finalVector K ctx₁ p₁ w₁ q₁ r =
        TreeTwinLinked2.finalVector K ctx₂ p₂ w₂ q₂ r := by
  intro r hr
  obtain ⟨out, hout, equal⟩ := coupling_support_right coupled
    (r, TreeTwinLinked2.finalVector K ctx₁ p₁ w₁ q₁ r) (by
      rw [support_map]
      exact ⟨r, hr, rfl⟩)
  rw [support_map] at hout
  obtain ⟨s, _, rfl⟩ := hout
  have same : r = s := congrArg Prod.fst equal
  subst s
  exact congrArg Prod.snd equal

/-- Fixed masks at a boundary with two supported public challenges cannot
hide an unequal first claim in a coupling of the challenge and opening. -/
theorem final_kernel_no_coupling (ctx₁ ctx₂ : Context C) (p₁ p₂ : Claim E)
    (different : p₁.1 0 ≠ p₂.1 0) (w₁ w₂ q₁ q₂ : Shares C E)
    (left right : ProbComp E) (r s : E)
    (hr : r ∈ support left) (hs : s ∈ support left) (distinct : r ≠ s) :
    ¬ RelTriple
      ((fun t => (t, TreeTwinLinked2.finalVector K ctx₁ p₁ w₁ q₁ t)) <$> left)
      ((fun t => (t, TreeTwinLinked2.finalVector K ctx₂ p₂ w₂ q₂ t)) <$> right)
      Eq := by
  intro coupled
  have equal := final_kernel_pointwise K ctx₁ ctx₂ p₁ p₂ w₁ w₂ q₁ q₂ left right coupled
  exact different (TreeTwinLinked2.finalVector_two_challenges K ctx₁ ctx₂ p₁ p₂ w₁ w₂ q₁ q₂
    r s distinct (congrFun (equal r hr) 0) (congrFun (equal s hs) 0))

/-- The same obstruction holds for the actual corrupt-recipient opening
view, not just for equality of the entire private vector. -/
theorem final_view_kernel_no_coupling (D : C.Coalition) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C) (p₁ p₂ : C.Party → Claim E)
    (w₁ w₂ q₁ q₂ : C.Party → Shares C E) (i j : C.Party)
    (honest : i ∉ D.1) (active : live i = true) (corrupt : j ∈ D.1)
    (different : (p₁ i).1 0 ≠ (p₂ i).1 0)
    (left right : ProbComp E) (r s : E)
    (hr : r ∈ support left) (hs : s ∈ support left) (distinct : r ≠ s) :
    ¬ RelTriple
      ((fun t => (t, treeSimCheckView D live (.opening (fun k =>
        TreeTwinLinked2.finalVector K (ctx₁ k) (p₁ k) (w₁ k) (q₁ k) t)))) <$> left)
      ((fun t => (t, treeSimCheckView D live (.opening (fun k =>
        TreeTwinLinked2.finalVector K (ctx₂ k) (p₂ k) (w₂ k) (q₂ k) t)))) <$> right)
      Eq := by
  intro coupled
  have pointwise : ∀ t ∈ support left,
      TreeTwinLinked2.finalVector K (ctx₁ i) (p₁ i) (w₁ i) (q₁ i) t 0 =
        TreeTwinLinked2.finalVector K (ctx₂ i) (p₂ i) (w₂ i) (q₂ i) t 0 := by
    intro t ht
    obtain ⟨out, hout, equal⟩ := coupling_support_right coupled
      (t, treeSimCheckView D live (.opening (fun k =>
        TreeTwinLinked2.finalVector K (ctx₁ k) (p₁ k) (w₁ k) (q₁ k) t))) (by
        rw [support_map]
        exact ⟨t, ht, rfl⟩)
    rw [support_map] at hout
    obtain ⟨u, _, rfl⟩ := hout
    have same : t = u := congrArg Prod.fst equal
    subst u
    by_contra ne
    exact TreeTwinLinked2.openingView_ne_of_first D live _ _ i j honest active corrupt ne
      (congrArg Prod.snd equal)
  exact different (TreeTwinLinked2.finalVector_two_challenges K (ctx₁ i) (ctx₂ i)
    (p₁ i) (p₂ i) (w₁ i) (w₂ i) (q₁ i) (q₂ i) r s distinct (pointwise r hr) (pointwise s hs))

/-- A fixed corrupt-mail script, retaining every actual received view.
The script may stop with aborts after the selected final opening. -/
def recordingReplay (sent : ℕ → C.Party → C.Party → Option (Msg E)) :
    Adversary C E (Keys C) PEmpty PEmpty where
  State := ℕ × List (C.Party → C.Party → Option (Msg E))
  start _ _ := pure (0, [])
  round state view := pure ((state.1 + 1, state.2 ++ [view]), sent state.1)
  answer _ impossible := PEmpty.elim impossible

theorem recordingReplay_queryBound {O : Type}
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (fuel : ℕ) :
    IsQueryBounded (recordingReplay sent) (O := O) (fun _ => pure false) fuel 0 := by
  refine ⟨0, 0, 0, by simp, ?_, ?_, ?_, ?_⟩
  · intro x z
    exact isQueryBoundP_pure _ _ _
  · intro state view
    exact isQueryBoundP_pure _ _ _
  · intro state impossible
    exact PEmpty.elim impossible
  · intro result
    exact isQueryBoundP_pure _ _ _

theorem real_steps_no_calls {α : Type} (steps : C.Party → Step C E RealSpec α) :
    ∀ i, ¬ (steps i).callInput.isSome := by
  intro i
  cases steps i with
  | done _ => simp [Step.callInput]
  | wait _ _ => simp [Step.callInput]
  | call impossible _ => exact PEmpty.elim impossible

/-- Exact source round of the recorder: it appends the current corrupt
view, returns the fixed script row, and resumes every honest program. -/
theorem recordingReplay_round {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E))
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D (recordingReplay sent) noFunctionality state steps = (do
      let next ← Concrete.sequenceFin fun j => match steps j with
        | .done out => pure (Step.done out)
        | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
            free (advance (resume fun k => if k ∈ D.1 then sent state.1 k j else (steps k).delivered j))
        | .call _ _ => pure (Step.done none)
      pure ((state.1 + 1, state.2 ++ [fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none]), next, sent state.1)) := by
  have noCalls : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, _, hi⟩, _⟩
    exact real_steps_no_calls steps i hi
  simp only [stepRound, if_neg noCalls, recordingReplay, worldRoles,
    liftComp_pure, counted_pure, pure_bind]
  congr 1
  apply congrArg Concrete.sequenceFin
  funext j
  cases steps j with
  | done out => rfl
  | wait outbox resume => split_ifs <;> rfl
  | call impossible _ => exact PEmpty.elim impossible

theorem recordingReplay_round_counter {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (steps : C.Party → Step C E RealSpec α)
    (out : (recordingReplay sent).State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E))
    (run : out ∈ support (stepRound worldRoles D (recordingReplay sent) noFunctionality state steps)) :
    out.1.1 = state.1 + 1 := by
  rw [recordingReplay_round] at run
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at run
  obtain ⟨next, _, rfl⟩ := run
  rfl

/-- A successful timed prefix cannot stop its scheduler early. The recorder's
counter therefore identifies its exact synchronous boundary. -/
theorem recordingReplay_timed_rounds_counter {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (n : ℕ)
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec α)
    (timed : ∀ i, TreeSimCheckTimedStep n (steps i))
    (out : (recordingReplay sent).State × (C.Party → Option α))
    (run : out ∈ support (executeRounds worldRoles D (recordingReplay sent) noFunctionality n state steps))
    (accepted : ∃ i value, out.2 i = some value) : out.1.1 = state.1 + n := by
  induction n generalizing state steps out with
  | zero =>
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at run
    subst out
    exact (Nat.add_zero _).symm
  | succ n ih =>
    rw [executeRounds] at run
    split_ifs at run with stopped
    · simp only [support_pure, Set.mem_singleton_iff] at run
      subst out
      obtain ⟨i, value, present⟩ := accepted
      change (steps i).output = some value at present
      rw [(timed i).pending] at present
      cases present
    · rw [mem_support_bind_iff] at run
      obtain ⟨next, round, tail⟩ := run
      have after := ih next.1 next.2.1
        (treeSimCheckTimed_round D (recordingReplay sent) n state steps timed next round) out tail accepted
      have counter := recordingReplay_round_counter D sent state steps next round
      rw [after, counter]
      omega

theorem recordingReplay_timed_phase_counter {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (n : ℕ) (state : (recordingReplay sent).State)
    (p : C.Party → PartyM C E RealSpec α) (timed : ∀ i, TreeSimCheckTimed n (p i).run)
    (out : (recordingReplay sent).State × (C.Party → Option α))
    (run : out ∈ support (executePhase worldRoles D (recordingReplay sent) noFunctionality n state p))
    (accepted : ∃ i value, out.2 i = some value) : out.1.1 = state.1 + n := by
  rw [executePhase, mem_support_bind_iff] at run
  obtain ⟨steps, start, run⟩ := run
  exact recordingReplay_timed_rounds_counter D sent n state steps
    (treeSimCheckTimed_start_mem D n p timed steps start) out run accepted

/-- A scheduled corrupt abort leaves every pending honest exchange aborted,
while the recorder still saves the complete pre-abort opening view. -/
theorem recordingReplay_abort_round {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (stop : sent state.1 = fun _ _ => some .abort) (j : C.Party) (corrupt : j ∈ D.1)
    (steps : C.Party → Step C E RealSpec α) (exchange : ∀ i, TreeSimCheckExchangeStep (steps i)) :
    stepRound worldRoles D (recordingReplay sent) noFunctionality state steps =
      pure ((state.1 + 1, state.2 ++ [fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none]),
        (fun _ => Step.done none), (fun _ _ => some .abort)) := by
  rw [recordingReplay_round, stop]
  have each (i : C.Party) : (match steps i with
      | .done out => pure (Step.done out)
      | .wait _ resume => if i ∈ D.1 then pure (Step.done none) else
          free (advance (resume fun k => if k ∈ D.1 then some .abort else (steps k).delivered i))
      | .call _ _ => pure (Step.done none)) =
      (pure (.done none) : OracleComp (WorldSpec C) (Step C E RealSpec α)) := by
    cases he : steps i with
    | done out =>
      have none : out = none := by simpa only [he, TreeSimCheckExchangeStep] using exchange i
      rw [none]
    | wait out resume =>
      dsimp only
      by_cases honest : i ∈ D.1
      · rw [if_pos honest]
      · rw [if_neg honest]
        have abort := (show TreeSimCheckExchangeStep (.wait out resume) from he ▸ exchange i)
          (fun k => if k ∈ D.1 then some .abort else (steps k).delivered i) j
          (by simp only [if_pos corrupt, Msg.isAbort])
        rw [abort, free_pure]
    | call input resume => exact input.elim
  simp only [each, sequenceFin_pure, pure_bind]
  rfl

theorem recordingReplay_abort_rounds {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (fuel : ℕ) (state : (recordingReplay sent).State)
    (stop : sent state.1 = fun _ _ => some .abort) (j : C.Party) (corrupt : j ∈ D.1)
    (steps : C.Party → Step C E RealSpec α) (exchange : ∀ i, TreeSimCheckExchangeStep (steps i))
    (out : (recordingReplay sent).State × (C.Party → Option α))
    (run : out ∈ support (executeRounds worldRoles D (recordingReplay sent) noFunctionality fuel state steps)) :
    out.2 = fun _ => none := by
  have pending : (fun i => (steps i).output) = fun _ => none := funext fun i => (exchange i).pending
  cases fuel with
  | zero =>
    simp only [executeRounds, pending, support_pure, Set.mem_singleton_iff] at run
    exact congrArg Prod.snd run
  | succ fuel =>
    rw [executeRounds] at run
    split_ifs at run
    · simp only [pending, support_pure, Set.mem_singleton_iff] at run
      exact congrArg Prod.snd run
    · rw [recordingReplay_abort_round D sent state stop j corrupt steps exchange] at run
      erw [pure_bind] at run
      dsimp only at run
      rw [executeRounds_all_none] at run
      simp only [support_pure, Set.mem_singleton_iff] at run
      exact congrArg Prod.snd run

/-- A fixed abort immediately after a timed prefix prevents every later
honest output, for every oracle answer and every remaining fuel. -/
theorem recordingReplay_timed_abort {α β : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (n fuel : ℕ) (state : (recordingReplay sent).State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (exchange : ∀ i a, TreeSimCheckExchange (k i a))
    (stop : sent (state.1 + (n + 1)) = fun _ _ => some .abort)
    (j : C.Party) (corrupt : j ∈ D.1)
    (out : (recordingReplay sent).State × (C.Party → Option β))
    (run : out ∈ support (executePhase worldRoles D (recordingReplay sent) noFunctionality
      (n + 1 + fuel) state (fun i => p i >>= k i))) : out.2 = fun _ => none := by
  by_contra failed
  have accepted : ∃ i value, out.2 i = some value := by
    by_contra none
    apply failed
    funext i
    cases he : out.2 i with
    | none => rfl
    | some value => exact (none ⟨i, value, he⟩).elim
  obtain ⟨pref, prefixRun, live, next, restarted, rest⟩ :=
    treeSimCheckTimed_phase_live D (recordingReplay sent) n fuel state p k timed exchange out run accepted
  have prefixAccepted : ∃ i value, pref.2 i = some value := by
    obtain ⟨i, honest⟩ := prss_exists_honest D
    obtain ⟨value, he⟩ := Option.isSome_iff_exists.mp (live i honest)
    exact ⟨i, value, he⟩
  have counter := recordingReplay_timed_phase_counter D sent (n + 1) state p timed pref prefixRun prefixAccepted
  have nextExchange : ∀ i, TreeSimCheckExchangeStep (next i) := by
    have each := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ restarted)
    intro i
    have hi := each i
    cases he : pref.2 i with
    | none =>
      have equal : next i = .done none := by
        simpa only [he, continueStep, support_pure, Set.mem_singleton_iff] using hi
      simp only [equal, TreeSimCheckExchangeStep]
    | some value =>
      exact exchange i value _ (by simpa only [he, continueStep] using hi)
  exact failed (recordingReplay_abort_rounds D sent fuel pref.1
    (by rw [counter]; exact stop) j corrupt next nextExchange out rest)

theorem recordingReplay_timed_abort_all_fuel {α β : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (n fuel : ℕ) (state : (recordingReplay sent).State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (exchange : ∀ i a, TreeSimCheckExchange (k i a))
    (stop : sent (state.1 + (n + 1)) = fun _ _ => some .abort)
    (j : C.Party) (corrupt : j ∈ D.1)
    (out : (recordingReplay sent).State × (C.Party → Option β))
    (run : out ∈ support (executePhase worldRoles D (recordingReplay sent) noFunctionality
      fuel state (fun i => p i >>= k i))) : out.2 = fun _ => none := by
  by_contra failed
  have accepted : ∃ i value, out.2 i = some value := by
    by_contra none
    apply failed
    funext i
    cases he : out.2 i with
    | none => rfl
    | some value => exact (none ⟨i, value, he⟩).elim
  have enough := TreeCheckWalkRecipe.timed_phase_fuel D (recordingReplay sent)
    fuel (n + 1) state p k timed out run accepted
  obtain ⟨remaining, rfl⟩ : ∃ remaining, fuel = n + 1 + remaining := ⟨fuel - (n + 1), by omega⟩
  exact failed (recordingReplay_timed_abort D sent n remaining state p k timed exchange stop j corrupt out run)

/-- The recorder's update is injective in the complete current view. -/
theorem recordingReplay_view_injective
    (sent : ℕ → C.Party → C.Party → Option (Msg E))
    (state : (recordingReplay sent).State) :
    Function.Injective (fun view : C.Party → C.Party → Option (Msg E) =>
      (state.1 + 1, state.2 ++ [view])) := by
  intro left right same
  have lists := congrArg Prod.snd same
  exact List.singleton_inj.mp (List.append_cancel_left lists)

def singleCoin (T₀ : C.Term) (v : E) : C.Term → Fin 1 → E :=
  fun T _ => if T = T₀ then v else 0

/-- Corrupt Coin shares depend only on known contributions; setting
those to zero makes their complete outboxes independent of the fresh table. -/
theorem corrupt_coin_zero (D : C.Coalition) (fresh : C.Term → Fin 1 → E)
    (pairs : C.Pair → Fin 1 → E) (j : C.Party) (corrupt : j ∈ D.1) :
    coinOut K j 1 (frandShare D 1 0 0 fresh pairs j) = openOut j 0 1 := by
  have zero : conv K (localContext j) (frandShare D 1 0 0 fresh pairs j).1 = 0 := by
    funext g
    rw [conv_frandShare]
    apply Finset.sum_eq_zero
    intro T hT
    have known : KnownTo D.1 T := ⟨j, corrupt, (Finset.mem_filter.mp hT).2⟩
    rw [if_pos known]
    simp only [Pi.zero_apply, mul_zero]
  unfold coinOut
  rw [zero]
  rfl

theorem singleCoin_noCoalition (D : C.Coalition) (T₀ : C.Term)
    (hidden : ¬ KnownTo D.1 T₀) (v : E) (i : C.Party) :
    frandShare D 1 0 0 (singleCoin T₀ v) 0 i =
      frandShare noCoalition 1 0 0 (singleCoin T₀ v) 0 i := by
  apply Prod.ext
  · funext T g
    have unknown : ¬ KnownTo (noCoalition : C.Coalition).1 T := by simp [KnownTo, noCoalition]
    simp only [frandShare, if_neg unknown]
    by_cases held : i ∈ C.holders T
    · simp only [if_pos held]
      by_cases known : KnownTo D.1 T
      · have different : T ≠ T₀ := fun h => hidden (h ▸ known)
        simp only [if_pos known, Pi.zero_apply, singleCoin, if_neg different]
        split_ifs <;> rfl
      · simp only [if_neg known]
    · simp only [if_neg held]
  · funext j g
    simp only [frandShare, Pi.zero_apply]
    split_ifs <;> simp

/-- One fixed correct corrupt-mail row accepts every value contributed
by a single hidden term in the actual Coin reconstruction. -/
theorem singleCoin_output (D : C.Coalition) (T₀ : C.Term)
    (hidden : ¬ KnownTo D.1 T₀) (v : E) (i : C.Party) (honest : i ∉ D.1) :
    treeSimCoinOutput K D 1 (fun k => frandShare D 1 0 0 (singleCoin T₀ v) 0 k)
      (fun j => openOut j 0 1) i = some [v] := by
  unfold treeSimCoinOutput
  rw [if_neg honest]
  have inbox : (fun j => if j ∈ D.1 then openOut j 0 1 i else
      coinOut K j 1 (frandShare D 1 0 0 (singleCoin T₀ v) 0 j) i) =
      fun j => coinOut K j 1 (frandShare D 1 0 0 (singleCoin T₀ v) 0 j) i := by
    funext j
    by_cases corrupt : j ∈ D.1
    · rw [if_pos corrupt, corrupt_coin_zero K D _ _ j corrupt]
    · rw [if_neg corrupt]
  rw [inbox]
  simp_rw [singleCoin_noCoalition D T₀ hidden v]
  rw [coinRes_honest']
  simp [singleCoin, List.ofFn_succ]

/-- The fresh-term/fresh-pair Coin kernel contains every output under
that same fixed corrupt-mail row. This is a support statement for the
finite tables used by the real Coin-source coupling. -/
theorem singleCoin_kernel_support [SampleableType E] (D : C.Coalition)
    (T₀ : C.Term) (hidden : ¬ KnownTo D.1 T₀) (v : E)
    (i : C.Party) (honest : i ∉ D.1) :
    some [v] ∈ support (do
      let fresh ← $ᵗ (C.Term → Fin 1 → E)
      let pairs ← $ᵗ (C.Pair → Fin 1 → E)
      pure (treeSimCoinOutput K D 1 (frandShare D 1 0 0 fresh pairs)
        (fun j => openOut j 0 1) i)) := by
  simp only [mem_support_bind_iff]
  refine ⟨singleCoin T₀ v, by simp, 0, by simp, ?_⟩
  rw [singleCoin_output K D T₀ hidden v i honest]
  simp

/-- Reverse realization of one coherent prescribed random-oracle reply.
The cache extension remains coherent with the same total answer function. -/
theorem randomOracle_realize {Q R : Type} [DecidableEq Q] [SampleableType R]
    (f : Q → R) (cache : (Q →ₒ R).QueryCache) (agrees : cache.AgreesWithFn f) (q : Q) :
    ∃ next, (f q, next) ∈ support (((Q →ₒ R).randomOracle q).run cache) ∧
      next.AgreesWithFn f := by
  cases found : cache q with
  | none =>
    refine ⟨cache.cacheQuery q (f q), ?_, ?_⟩
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ found, support_map]
      exact ⟨f q, by simp [uniformSampleImpl], rfl⟩
    · exact (cache.agreesWithFn_cacheQuery_iff q (f q) f found).mpr ⟨agrees, rfl⟩
  | some value =>
    have same : f q = value := agrees found
    refine ⟨cache, ?_, agrees⟩
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ found, same]
    simp

theorem hashAnswer_realize (prims : Primitives) (h : Query C → HashOutput)
    (good : Good prims h) (cache : HashCache C) (agrees : Agrees h cache) (q : Query C) :
    ∃ next, (h q, next) ∈ support ((hashAnswer prims q).run cache) ∧ Agrees h next := by
  by_cases fixed : IsFixed q
  · obtain ⟨input, rfl, mpc⟩ := fixed
    refine ⟨cache, ?_, agrees⟩
    rw [hashAnswer_of_isFixed prims mpc, good input mpc, StateT.run_pure]
    simp
  · rw [hashAnswer_of_not_isFixed prims fixed]
    obtain ⟨next, supported, coherent⟩ := randomOracle_realize h cache
      (fun {q} {v} hq => agrees q v hq) q
    exact ⟨next, supported, fun q v hq => coherent hq⟩

/-- A supported run of a prescribed handler is realized by the actual
stateful handler when each prescribed query has a coherent supported
realization. This direction constructs actual support, not source support. -/
theorem realize_simulateQ {ι σ α : Type} {spec : OracleSpec ι}
    (fixed : QueryImpl spec ProbComp) (actual : QueryImpl spec (StateT σ ProbComp))
    (coherent : σ → Prop)
    (step : ∀ s, coherent s → ∀ q value, value ∈ support (fixed q) →
      ∃ next, (value, next) ∈ support ((actual q).run s) ∧ coherent next)
    (program : OracleComp spec α) (value : α) (s : σ) (initial : coherent s)
    (supported : value ∈ support (simulateQ fixed program)) :
    ∃ next, (value, next) ∈ support ((simulateQ actual program).run s) ∧ coherent next := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure result =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
    subst value
    exact ⟨s, by simp, initial⟩
  | query_bind q continuation ih =>
    simp only [simulateQ_query_bind, mem_support_bind_iff] at supported
    obtain ⟨answer, ha, rest⟩ := supported
    obtain ⟨middle, query, invariant⟩ := step s initial q answer ha
    obtain ⟨next, tail, final⟩ := ih answer middle invariant rest
    refine ⟨next, ?_, final⟩
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨(answer, middle), query, tail⟩

/-- Ordinary local padding can be realized under any coherent good public
table, including padding that prefetches every challenge lookup. -/
theorem fixedLocal_realize (prims : Primitives) (hash : Query C → HashOutput)
    (good : Good prims hash) {α : Type} (program : OracleComp (LocalSpec C) α)
    (value : α) (s : HashCache C) (initial : Agrees hash s)
    (run : value ∈ support (simulateQ (fixedLocal prims hash) program)) :
    ∃ next, (value, next) ∈ support ((simulateQ (localAnswer prims) program).run s) ∧
      Agrees hash next := by
  apply realize_simulateQ (fixedLocal prims hash) (localAnswer prims) (Agrees hash) _
    program value s initial run
  intro cache coherent q value supported
  rcases q with q | q | x
  · refine ⟨cache, ?_, coherent⟩
    change value ∈ support (liftM (unifSpec.query q) : ProbComp _) at supported
    change (value, cache) ∈ support ((fun value => (value, cache)) <$>
      (liftM (unifSpec.query q) : ProbComp _))
    rw [support_map]
    exact Set.mem_image_of_mem _ supported
  · change value ∈ support (pure (hash q) : ProbComp _) at supported
    have same : value = hash q := by simpa using supported
    subst value
    exact hashAnswer_realize prims hash good cache coherent q
  · change value ∈ support
      (pure (prims.aes.eval (truncateHash (hash (.streamKey x.2.1))) x.2.2) : ProbComp _) at supported
    have same : value = prims.aes.eval (truncateHash (hash (.streamKey x.2.1))) x.2.2 := by
      simpa using supported
    subst value
    obtain ⟨next, actual, final⟩ := hashAnswer_realize prims hash good cache coherent (.streamKey x.2.1)
    refine ⟨next, ?_, final⟩
    change (_, next) ∈ support ((prgAnswer prims x).run cache)
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, mem_support_bind_iff]
    exact ⟨(hash (.streamKey x.2.1), next), actual, by simp⟩

theorem padding_coherent_supported (prims : Primitives) (hash : Query C → HashOutput)
    (good : Good prims hash) (padding : OracleComp (LocalSpec C) Unit)
    (s : HashCache C) (initial : Agrees hash s) :
    ∃ next, ((), next) ∈ support ((simulateQ (localAnswer prims) padding).run s) ∧
      Agrees hash next := by
  obtain ⟨value, run⟩ := XmssSecurity.probComp_support_nonempty (simulateQ (fixedLocal prims hash) padding)
  cases value
  exact fixedLocal_realize prims hash good padding () s initial run

/-- Prescribed public-hash and hidden-stream tables, retaining ordinary
private sampling. This handler is used only to construct supported runs. -/
def prescribedLocal (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) :
    QueryImpl (LocalSpec C) ProbComp
  | .inl q => liftM (unifSpec.query q)
  | .inr (.inl q) => pure (hash q)
  | .inr (.inr x) => pure (if Hidden D x.1 then hidden ((x.1, x.2.1), x.2.2)
      else prims.aes.eval (truncateHash (hash (.streamKey x.2.1))) x.2.2)

/-- The ordinary AES answer table is one possible complete hidden table.
It is used only for transferring supported honest executions. -/
def aesHidden (prims : Primitives) (hash : Query C → HashOutput) : HiddenAddress C → Bit :=
  fun x => prims.aes.eval (truncateHash (hash (.streamKey x.1.2))) x.2

theorem prescribedLocal_aes (prims : Primitives) (D : C.Coalition) (hash : Query C → HashOutput) :
    prescribedLocal prims D hash (aesHidden prims hash) = fixedLocal prims hash := by
  funext query
  rcases query with sampled | hashQuery | stream
  · rfl
  · rfl
  · simp only [prescribedLocal, aesHidden, ite_self]
    rfl

/-- A supported ordinary honest computation fixes one coherent public hash;
its AES streams give a supported instance of the prescribed stream semantics. -/
theorem localRun_prescribed (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C) α) (s : HashCache C) (noMpc : NoMpc s)
    (out : α × HashCache C) (run : out ∈ support ((simulateQ (localAnswer prims) p).run s)) :
    ∃ hash, Good prims hash ∧ Agrees hash s ∧ Agrees hash out.2 ∧
      out.1 ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash)) p) := by
  obtain ⟨grows, preserved, supported⟩ := localRun_support (prims := prims) p s out run
  have finalNoMpc := preserved noMpc
  refine ⟨hashOf prims out.2, good_hashOf prims out.2,
    (agrees_hashOf prims finalNoMpc).mono grows, agrees_hashOf prims finalNoMpc, ?_⟩
  rw [prescribedLocal_aes]
  exact supported _ (good_hashOf prims out.2) (agrees_hashOf prims finalNoMpc)

/-- The deterministic part of the prescribed handler, including hidden PRSS reads. -/
def prescribedRo (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) : QueryImpl (RoSpec C) Id
  | .inl q => pure (hash q)
  | .inr x => pure (if Hidden D x.1 then hidden ((x.1, x.2.1), x.2.2)
      else prims.aes.eval (truncateHash (hash (.streamKey x.2.1))) x.2.2)

def prescribedValue (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    {α : Type} (program : OracleComp (RoSpec C) α) : α :=
  Id.run (simulateQ (prescribedRo prims D hash hidden) program)

theorem prescribedValue_pure (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) {α : Type} (a : α) :
    prescribedValue prims D hash hidden (pure a) = a := rfl

theorem prescribedValue_bind (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) {α β : Type}
    (program : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β) :
    prescribedValue prims D hash hidden (program >>= f) =
      prescribedValue prims D hash hidden (f (prescribedValue prims D hash hidden program)) := by
  simp only [prescribedValue, simulateQ_bind, Id.run_bind]

theorem prescribedValue_mapM (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) {α β : Type}
    (f : α → OracleComp (RoSpec C) β) : ∀ xs : List α,
    prescribedValue prims D hash hidden (xs.mapM f) =
      xs.map (fun x => prescribedValue prims D hash hidden (f x))
  | [] => rfl
  | x :: xs => by
    rw [List.mapM_cons, prescribedValue_bind, prescribedValue_bind,
      prescribedValue_mapM prims D hash hidden f xs, prescribedValue_pure, List.map_cons]

theorem prescribedLocal_ro (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    {α : Type} (program : OracleComp (RoSpec C) α) :
    simulateQ (prescribedLocal prims D hash hidden) (liftComp program (LocalSpec C)) =
      pure (prescribedValue prims D hash hidden program) := by
  induction program using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure, prescribedValue_pure]
  | query_bind q continuation ih =>
    rw [liftComp_bind, simulateQ_bind, prescribedValue_bind]
    simp only [ih]
    cases q <;> rfl

/-- A single prescribed stream table gives identical term values to all
holders and symmetric pair values to both endpoints. -/
theorem prescribedValue_prssDraw (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (keys : C.Party → Keys C) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput)
    (i : C.Party) {R : Type} [Field R] (codec : Codec C E R) (label idx count : ℕ) :
    prescribedValue prims D hash hidden (prssDraw (prssCtx keys kT kP i) codec label idx count) =
      (honestR (fun T => prescribedValue prims D hash hidden
          (codec.draw (.term T) (kT T) label idx count)) i,
        honestZ (fun p => prescribedValue prims D hash hidden
          (codec.draw (.pair p) (kP p) label idx count)) i) := by
  unfold prssDraw
  simp only [prescribedValue_bind, prescribedValue_pure]
  refine Prod.ext (funext fun T => ?_) (funext fun j => ?_)
  · change (prescribedValue prims D hash hidden (termDraws _ codec label idx count)).getD
      (C.terms.idxOf T) (fun _ => 0) = _
    unfold termDraws
    rw [prescribedValue_mapM, getD_terms_idxOf]
    by_cases held : i ∈ C.holders T
    · simp [honestR, prssCtx, held]
    · simp [honestR, prssCtx, held, prescribedValue_pure]
  · change (prescribedValue prims D hash hidden (pairDraws _ codec label idx count)).getD
      j.val (fun _ => 0) = _
    unfold pairDraws
    rw [prescribedValue_mapM, getD_parties]
    by_cases self : j = i
    · simp [honestZ, prssCtx, self, prescribedValue_pure]
    · simp [honestZ, prssCtx, self]

def StreamCoherent (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (s : HashCache C × HiddenCache C) : Prop :=
  Agrees hash s.1 ∧ s.2.AgreesWithFn hidden

/-- Every prescribed local reply can be realized in the actual stream
world while preserving both cache invariants. -/
theorem prescribedLocal_step (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (s : HashCache C × HiddenCache C) (initial : StreamCoherent hash hidden s)
    (q : (LocalSpec C).Domain) (value : (LocalSpec C).Range q)
    (supported : value ∈ support (prescribedLocal prims D hash hidden q)) :
    ∃ next, (value, next) ∈ support ((streamWorld prims D (.inr q)).run s) ∧
      StreamCoherent hash hidden next := by
  rcases q with q | q | x
  · refine ⟨s, ?_, initial⟩
    change value ∈ support (liftM (unifSpec.query q) : ProbComp _) at supported
    change (value, s) ∈ support
      ((fun p => (p.1, (p.2, s.2))) <$>
        ((fun u => (u, s.1)) <$> (liftM (unifSpec.query q) : ProbComp _)))
    simp only [support_map, Set.mem_image]
    exact ⟨(value, s.1), ⟨value, supported, rfl⟩, rfl⟩
  · change value ∈ support (pure (hash q) : ProbComp _) at supported
    simp only [support_pure] at supported
    subst value
    obtain ⟨cache, run, agrees⟩ := hashAnswer_realize prims hash good s.1 initial.1 q
    refine ⟨(cache, s.2), ?_, agrees, initial.2⟩
    change (hash q, cache, s.2) ∈ support
      ((fun p => (p.1, (p.2, s.2))) <$> ((hashAnswer prims q).run s.1))
    rw [support_map]
    exact ⟨(hash q, cache), run, rfl⟩
  · change value ∈ support (pure (if Hidden D x.1 then hidden ((x.1, x.2.1), x.2.2)
      else prims.aes.eval (truncateHash (hash (.streamKey x.2.1))) x.2.2) : ProbComp _) at supported
    simp only [support_pure] at supported
    subst value
    by_cases fresh : Hidden D x.1
    · obtain ⟨cache, run, agrees⟩ := randomOracle_realize hidden s.2 initial.2 ((x.1, x.2.1), x.2.2)
      refine ⟨(s.1, cache), ?_, initial.1, agrees⟩
      simp only [if_pos fresh, streamWorld, StateT.run_mk]
      rw [support_map]
      exact ⟨(hidden ((x.1, x.2.1), x.2.2), cache), run, rfl⟩
    · obtain ⟨cache, run, agrees⟩ := hashAnswer_realize prims hash good s.1 initial.1 (.streamKey x.2.1)
      refine ⟨(cache, s.2), ?_, agrees, initial.2⟩
      simp only [if_neg fresh, streamWorld, onHash, StateT.run_mk]
      change (prims.aes.eval (truncateHash (hash (.streamKey x.2.1))) x.2.2, cache, s.2) ∈ support
        ((fun p => (p.1, (p.2, s.2))) <$> ((prgAnswer prims x).run s.1))
      rw [support_map]
      refine ⟨(_, cache), ?_, rfl⟩
      simp only [prgAnswer, StateT.run_bind, StateT.run_pure, mem_support_bind_iff]
      exact ⟨(hash (.streamKey x.2.1), cache), run, by simp⟩

/-- A prescribed finite local execution lifts to support of the actual
stream world. Hidden table replies remain consistent across all holders. -/
theorem prescribedLocal_realize (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    {α : Type} (program : OracleComp (LocalSpec C) α) (value : α)
    (s : HashCache C × HiddenCache C) (initial : StreamCoherent hash hidden s)
    (supported : value ∈ support (simulateQ (prescribedLocal prims D hash hidden) program)) :
    ∃ next, (value, next) ∈ support
      ((simulateQ (streamWorld prims D) (free program)).run s) ∧ StreamCoherent hash hidden next := by
  have result := realize_simulateQ (prescribedLocal prims D hash hidden)
    (fun q => streamWorld prims D (.inr q)) (StreamCoherent hash hidden)
    (prescribedLocal_step prims D hash hidden good) program value s initial supported
  have programEq : simulateQ (streamWorld prims D) (free program) =
      simulateQ (fun q => streamWorld prims D (.inr q)) program := by
    rw [free, ← QueryImpl.simulateQ_compose]
    congr 1
    funext t
    exact (simulateQ_query _ _).trans (id_map _)
  rw [programEq]
  exact result

/-- The same reverse realization retains an actual classified query log;
the result is in the support of `treeSimLoggedWorld` itself. -/
theorem prescribedLocal_logged_realize (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    {α : Type} (program : OracleComp (LocalSpec C) α) (value : α)
    (s : TreeSimState C) (initial : StreamCoherent hash hidden s.1)
    (supported : value ∈ support (simulateQ (prescribedLocal prims D hash hidden) program)) :
    ∃ next, (value, next) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D) (free program)).run s) ∧
      StreamCoherent hash hidden next.1 := by
  obtain ⟨cache, run, coherent⟩ := prescribedLocal_realize prims D hash hidden good program value s.1 initial supported
  rw [← treeSimLoggedWorld_erase prims D (free program) s.1 s.2, support_map] at run
  obtain ⟨out, actual, same⟩ := run
  have valueEq : out.1 = value := congrArg Prod.fst same
  have cacheEq : out.2.1 = cache := congrArg Prod.snd same
  refine ⟨out.2, ?_, ?_⟩
  · cases out with
    | mk answer state =>
      dsimp only at valueEq
      subst answer
      exact actual
  · rw [cacheEq]
    exact coherent

def recordingLocalRound {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E))
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec α) :
    OracleComp (LocalSpec C)
      ((recordingReplay sent).State × (C.Party → Step C E RealSpec α) ×
        (C.Party → C.Party → Option (Msg E))) := do
  let next ← Concrete.sequenceFin (roundLocal D steps (sent state.1))
  pure ((state.1 + 1, state.2 ++ [fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none]), next, sent state.1)

theorem recordingReplay_round_local {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E))
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D (recordingReplay sent) noFunctionality state steps =
      free (recordingLocalRound D sent state steps) := by
  rw [stepRound_real]
  simp only [recordingReplay, worldRoles, liftComp_pure, counted_pure, pure_bind,
    recordingLocalRound, free_bind, free_pure]

def recordingLocalSteps {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) :
    ℕ → (recordingReplay sent).State → (C.Party → Step C E RealSpec α) →
      OracleComp (LocalSpec C) ((recordingReplay sent).State × (C.Party → Step C E RealSpec α))
  | 0, state, steps => pure (state, steps)
  | fuel + 1, state, steps =>
      if ∀ i, i ∉ D.1 → (steps i).isDone then pure (state, steps) else do
        let (state, steps, _) ← recordingLocalRound D sent state steps
        recordingLocalSteps D sent fuel state steps

/-- The complete recorder-driven prefix is a concrete local-oracle
program, retaining all suspended honest programs and the full recorder. -/
theorem recordingReplay_steps_local {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (fuel : ℕ)
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec α) :
    executeSteps worldRoles D (recordingReplay sent) noFunctionality fuel state steps =
      free (recordingLocalSteps D sent fuel state steps) := by
  induction fuel generalizing state steps with
  | zero => simp only [executeSteps, recordingLocalSteps, free_pure]
  | succ fuel ih =>
    simp only [executeSteps, recordingLocalSteps]
    split_ifs
    · exact (free_pure _).symm
    · rw [recordingReplay_round_local, free_bind]
      exact bind_congr (fun result => ih result.1 result.2.1)

theorem recordingReplay_steps_interpret (prims : Primitives) {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (fuel : ℕ)
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec α) :
    simulateQ (treeSimLoggedWorld prims D)
      (executeSteps worldRoles D (recordingReplay sent) noFunctionality fuel state steps) =
      executeSteps (treeSimRealRoles prims D) D (recordingReplay sent) noFunctionality fuel state steps := by
  induction fuel generalizing state steps with
  | zero => simp only [executeSteps, simulateQ_pure]
  | succ fuel ih =>
    simp only [executeSteps]
    split_ifs
    · exact simulateQ_pure _ _
    · rw [simulateQ_bind, simulateQ_stepRound]
      exact bind_congr (fun result => ih result.1 result.2.1)

/-- A coherent prescribed recorder prefix gives support in the actual
scheduler with its actual classified log and both actual final caches. -/
theorem recordingReplay_steps_realize (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (fuel : ℕ)
    (state : (recordingReplay sent).State) (steps : C.Party → Step C E RealSpec TreeOutput)
    (value : (recordingReplay sent).State × (C.Party → Step C E RealSpec TreeOutput))
    (s : TreeSimState C) (initial : StreamCoherent hash hidden s.1)
    (supported : value ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalSteps D sent fuel state steps))) :
    ∃ next, (value, next) ∈ support
      ((executeSteps (treeSimRealRoles prims D) D (recordingReplay sent) noFunctionality
        fuel state steps).run s) ∧ StreamCoherent hash hidden next.1 := by
  have result := prescribedLocal_logged_realize prims D hash hidden good
    (recordingLocalSteps D sent fuel state steps) value s initial supported
  rw [← recordingReplay_steps_local D sent fuel state steps] at result
  simpa only [recordingReplay_steps_interpret] using result

def recordingLocalPhase {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (fuel : ℕ)
    (state : (recordingReplay sent).State) (program : C.Party → PartyM C E RealSpec α) :
    OracleComp (LocalSpec C) ((recordingReplay sent).State × (C.Party → Option α)) := do
  let steps ← Concrete.sequenceFin fun i =>
    if i ∈ D.1 then pure (Step.done none) else advance (program i).run
  let result ← recordingLocalSteps D sent fuel state steps
  pure (result.1, fun i => (result.2 i).output)

theorem recordingReplay_phase_local {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (fuel : ℕ)
    (state : (recordingReplay sent).State) (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D (recordingReplay sent) noFunctionality fuel state program =
      free (recordingLocalPhase D sent fuel state program) := by
  simp only [executePhase, startSteps, recordingLocalPhase, free_bind, free_sequenceFin]
  have start : (Concrete.sequenceFin fun i =>
      if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) =
      Concrete.sequenceFin (fun i => free
        (if i ∈ D.1 then pure (Step.done none) else advance (program i).run)) := by
    congr 1
    funext i
    split_ifs <;> simp only [free_pure, worldRoles]
  rw [start]
  apply bind_congr
  intro steps
  rw [executeRounds_eq_executeSteps, recordingReplay_steps_local]
  simp only [free_pure, bind_pure_comp]

/-- This local program includes the real setup, the real ceremony continuation,
and exactly the scheduler prefix retained by `TreeStagesReach`. -/
def recordingLocalTrace (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (sent : ℕ → C.Party → C.Party → Option (Msg E)) (x : C.Party → Keys C)
    (state : (recordingReplay sent).State) (fuel : ℕ) :
    OracleComp (LocalSpec C)
      ((recordingReplay sent).State × (C.Party → Step C E RealSpec TreeOutput)) := do
  let p ← recordingLocalPhase D sent 3 state
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
  let next ← Concrete.sequenceFin fun i =>
    continueStep (treeSimRealCont K circuits settings top tree x i) (.done (p.2 i))
  recordingLocalSteps D sent fuel p.1 next

theorem recordingReplay_trace_interpret (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (sent : ℕ → C.Party → C.Party → Option (Msg E))
    (x : C.Party → Keys C) (state : (recordingReplay sent).State) (fuel : ℕ) :
    simulateQ (treeSimLoggedWorld prims D)
      (free (recordingLocalTrace K circuits settings top tree D sent x state fuel)) =
      treeStagesTrace prims K circuits settings top tree D (recordingReplay sent) x state fuel := by
  simp only [recordingLocalTrace, free_bind, ← recordingReplay_phase_local,
    ← recordingReplay_steps_local, simulateQ_bind, simulateQ_executePhase,
    recordingReplay_steps_interpret, treeStagesTrace, treeSimContinue, treeSimRealRoles]

/-- Prescribing a coherent complete local prefix realizes the original reached
configuration, including the three setup rounds and the classified query log. -/
theorem recordingReplay_reach_realize (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (good : Good prims hash) (sent : ℕ → C.Party → C.Party → Option (Msg E))
    (x : C.Party → Keys C) (state : (recordingReplay sent).State) (fuel : ℕ)
    (value : (recordingReplay sent).State × (C.Party → Step C E RealSpec TreeOutput))
    (s : TreeSimState C) (initial : StreamCoherent hash hidden s.1)
    (supported : value ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalTrace K circuits settings top tree D sent x state fuel))) :
    ∃ next, TreeStagesReach prims K circuits settings top tree D (recordingReplay sent)
      x state s fuel (value, next) ∧ StreamCoherent hash hidden next.1 := by
  have result := prescribedLocal_logged_realize prims D hash hidden good
    (recordingLocalTrace K circuits settings top tree D sent x state fuel) value s initial supported
  simpa only [recordingReplay_trace_interpret, TreeStagesReach] using result

/-- Honest local programs cannot add a counted digest query to the actual
classified log. Private samples and stream queries retain their free role. -/
theorem free_logged_no_counted_digest (prims : Primitives) (D : C.Coalition) {α : Type}
    (program : OracleComp (LocalSpec C) α) (s : TreeSimState C)
    (initial : ∀ salt hist value,
      (⟨.inl (.inl (.inr (.inl (.digest salt hist)))), value⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∉ s.2)
    (out : α × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free program)).run s)) :
    ∀ salt hist value,
      (⟨.inl (.inl (.inr (.inl (.digest salt hist)))), value⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∉ out.2.2 := by
  have interpretation : simulateQ (treeSimLoggedWorld prims D) (free program) =
      simulateQ (fun q => treeSimLoggedWorld prims D (.inr q)) program := by
    rw [free, ← QueryImpl.simulateQ_compose]
    congr 1
    funext t
    exact (simulateQ_query _ _).trans (id_map _)
  rw [interpretation] at run
  clear interpretation
  induction program using OracleComp.inductionOn generalizing s out with
  | pure value =>
    erw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst out
    exact initial
  | query_bind q k ih =>
    erw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨middle, query, rest⟩ := run
    apply ih middle.1 middle.2 _ out rest
    change middle ∈ support ((treeSimLoggedWorld prims D (.inr q)).run s) at query
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map] at query
    obtain ⟨answer, _, rfl⟩ := query
    intro salt hist value present
    rw [List.mem_append, List.mem_singleton] at present
    rcases present with old | added
    · exact initial salt hist value old
    · have impossible := congrArg Sigma.fst added
      cases impossible

/-- The fixed recorder makes no oracle queries, so every actual reached
ceremony log from an empty transcript excludes the original salt-guess event. -/
theorem recordingReplay_reached_not_saltGuess (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (sent : ℕ → C.Party → Mail C E) (x : C.Party → Keys C)
    (state : (recordingReplay sent).State) (cache : HashCache C × HiddenCache C) (fuel : ℕ)
    (a : TreeSimConfig (recordingReplay sent) (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D (recordingReplay sent)
      x state (cache, []) fuel a) : ¬ TreeSimSaltGuess D a.2.2 := by
  unfold TreeStagesReach at reach
  rw [← recordingReplay_trace_interpret] at reach
  have noCounted := free_logged_no_counted_digest prims D
    (recordingLocalTrace K circuits settings top tree D sent x state fuel) (cache, [])
    (by intros; simp) a reach
  rintro ⟨salt, hist, value, _, queried⟩
  exact noCounted salt hist value queried

theorem prescribedLocal_private (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    {α : Type} (program : ProbComp α) :
    simulateQ (prescribedLocal prims D hash hidden) (liftComp program (LocalSpec C)) = program := by
  induction program using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure]
  | query_bind q continuation ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    rfl

/-- Setup hash queries are independent of the hidden stream table. -/
theorem prescribedLocal_hashOnly (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    {α : Type} (program : OracleComp (RoSpec C) α)
    (noPrg : IsQueryBoundP program TreeCheckPrgQuery 0) :
    simulateQ (prescribedLocal prims D hash hidden) (liftComp program (LocalSpec C)) =
      pure (ThresholdLeanXmssSecurity.D prims hash program) := by
  induction program using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure, D_pure]
  | query_bind q continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at noPrg
    cases q with
    | inr q => simpa [TreeCheckPrgQuery] using noPrg.1
    | inl q =>
      rw [liftComp_bind, simulateQ_bind, D_bind]
      change (pure (hash q) >>= _) = _
      rw [pure_bind]
      exact ih (hash q) (by simpa [TreeCheckPrgQuery] using noPrg.2 (hash q))

theorem sequenceFin_support_of_each {α : Type} :
    ∀ {n : ℕ} (program : Fin n → ProbComp α) (value : Fin n → α),
      (∀ i, value i ∈ support (program i)) → value ∈ support (Concrete.sequenceFin program)
  | 0, program, value, each => by
    simp only [Concrete.sequenceFin, support_pure, Set.mem_singleton_iff]
    funext i
    exact i.elim0
  | n + 1, program, value, each => by
    simp only [Concrete.sequenceFin, mem_support_bind_iff]
    refine ⟨value 0, each 0, (fun i => value i.succ),
      sequenceFin_support_of_each (fun i => program i.succ) (fun i => value i.succ)
        (fun i => each i.succ), ?_⟩
    simp only [support_pure, Set.mem_singleton_iff]
    funext i
    cases i using Fin.cases <;> rfl

theorem sampleParts_support (own : Parts C) : own ∈ support sampleParts := by
  cases own with
  | mk parameter term pair =>
    simp only [sampleParts, mem_support_bind_iff]
    exact ⟨parameter, by simp, term, by simp, pair, by simp, by simp⟩

def maskedSteps {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i => if i ∈ D.1 then .done none else steps i

def recorderView (D : C.Coalition) (outbox : C.Party → Mail C E) :
    C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then outbox i c else none

/-- A fixed cooperative script delivers the same inbox as the complete
honest network, while recording exactly the corrupt recipients' view. -/
theorem recordingLocalRound_wait {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (outbox : C.Party → Mail C E)
    (resume : C.Party → Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
    (script : sent state.1 = outbox) :
    recordingLocalRound D sent state (maskedSteps D (fun i => .wait (outbox i) (resume i))) = (do
      let next ← Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else
        advance (resume i (fun j => outbox j i))
      pure ((state.1 + 1, state.2 ++ [recorderView D outbox]), next, outbox)) := by
  unfold recordingLocalRound
  rw [script]
  have localEq : (roundLocal D (maskedSteps D (fun i => Step.wait (outbox i) (resume i))) outbox) =
      (fun i => if i ∈ D.1 then pure (.done none) else
        advance (resume i (fun j => outbox j i))) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp only [roundLocal, maskedSteps, if_pos hi]
    · simp only [roundLocal, maskedSteps, if_neg hi]
      congr 2
      funext j
      by_cases hj : j ∈ D.1 <;> simp only [hj, ↓reduceIte, Step.delivered]
  rw [localEq]
  congr 1
  funext next
  congr 3
  congr 1
  congr 1
  funext c i
  by_cases hi : i ∈ D.1 <;> simp [maskedSteps, recorderView, hi, Step.outbox]

/-- Every supported honest-network round can be replayed by the fixed
corrupt row it delivered, with the same honest suspended programs. -/
theorem recordingLocalRound_honest_support {α : Type}
    (impl : QueryImpl (LocalSpec C) ProbComp) (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (steps next : C.Party → Step C E RealSpec α)
    (script : sent state.1 = fun j i => (steps j).delivered i)
    (run : next ∈ support (simulateQ impl (honestStep noFunctionality PEmpty.elim steps))) :
    ((state.1 + 1, state.2 ++ [recorderView D (fun i => (steps i).outbox)]),
      maskedSteps D next, (fun j i => (steps j).delivered i)) ∈ support
      (simulateQ impl (recordingLocalRound D sent state (maskedSteps D steps))) := by
  have noCalls : ¬ ((∃ i, (steps i).callInput.isSome) ∧
      ∀ i, (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, hi⟩, _⟩
    exact real_steps_no_calls steps i hi
  rw [honestStep, if_neg noCalls, simulateQ_sequenceFin] at run
  have each := mem_support_sequenceFin _ _ run
  unfold recordingLocalRound
  rw [script]
  simp only [simulateQ_bind, simulateQ_sequenceFin, simulateQ_pure]
  erw [mem_support_bind_iff]
  refine ⟨maskedSteps D next, sequenceFin_support_of_each _ _ (fun i => ?_), ?_⟩
  · by_cases corrupt : i ∈ D.1
    · simp only [maskedSteps, if_pos corrupt, roundLocal, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
    · have hi := each i
      simp only [maskedSteps, if_neg corrupt, roundLocal]
      cases he : steps i with
      | done out => simpa only [he, simulateQ_pure, support_pure, Set.mem_singleton_iff] using hi
      | wait out resume =>
        have inbox : (fun j => if j ∈ D.1 then (steps j).delivered i else
            (if j ∈ D.1 then Step.done none else steps j).delivered i) =
            (fun j => (steps j).delivered i) := by
          funext j
          split_ifs <;> rfl
        rw [inbox]
        simpa only [he] using hi
      | call impossible _ => exact impossible.elim
  · erw [mem_support_pure_iff]
    have view : recorderView D (fun i => (steps i).outbox) =
        (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (maskedSteps D steps i).outbox c else none) := by
      funext c i
      by_cases corrupt : i ∈ D.1 <;> simp [maskedSteps, recorderView, corrupt]
    rw [view]
    rfl

theorem simulated_source_support {ι α : Type} {S : OracleSpec.{0, 0} ι}
    (impl : QueryImpl S ProbComp) (p : OracleComp S α) :
    support (simulateQ impl p) ⊆ support p := by
  have h := support_simulateQ_run'_subset (impl.liftTarget (StateT Unit ProbComp)) p ()
  simpa [StateT.run'_eq] using h

theorem honestStep_real {α : Type} (steps : C.Party → Step C E RealSpec α) :
    honestStep noFunctionality PEmpty.elim steps = Concrete.sequenceFin (fun i => match steps i with
      | .done out => pure (.done out)
      | .wait _ resume => advance (resume fun j => (steps j).delivered i)
      | .call input _ => input.elim) := by
  have noCalls : ¬ ((∃ i, (steps i).callInput.isSome) ∧
      ∀ i, (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, hi⟩, _⟩
    exact real_steps_no_calls steps i hi
  rw [honestStep, if_neg noCalls]
  congr 1
  funext i
  cases steps i with
  | done _ => rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

theorem honestStep_done {α : Type} (steps next : C.Party → Step C E RealSpec α)
    (run : next ∈ support (honestStep noFunctionality PEmpty.elim steps))
    (i : C.Party) (value : Option α) (done : steps i = .done value) : next i = .done value := by
  rw [honestStep_real] at run
  have each := mem_support_sequenceFin_oc _ _ run i
  simpa only [done, support_pure, Set.mem_singleton_iff] using each

theorem honestRounds_done_output {α : Type} (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec α) (out : C.Party → Option α)
    (run : out ∈ support (honestRounds noFunctionality PEmpty.elim fuel steps))
    (i : C.Party) (value : Option α) (done : steps i = .done value) : out i = value := by
  induction fuel generalizing steps out with
  | zero =>
    simp only [honestRounds, support_pure, Set.mem_singleton_iff] at run
    simp only [run, done, Step.output]
  | succ fuel ih =>
    rw [honestRounds] at run
    split_ifs at run
    · simp only [support_pure, Set.mem_singleton_iff] at run
      simp only [run, done, Step.output]
    · rw [mem_support_bind_iff] at run
      obtain ⟨next, round, rest⟩ := run
      exact ih next out rest (honestStep_done steps next round i value done)

theorem honestRounds_timed_pending {α : Type} (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (out : C.Party → Option α)
    (timed : ∀ i, TreeSimCheckTimedStep (n + 1) (steps i))
    (run : out ∈ support (honestRounds noFunctionality PEmpty.elim (n + 1) steps))
    (success : ∀ i, (out i).isSome) : ∀ i, ¬ (steps i).isDone := by
  intro i
  cases he : steps i with
  | done value =>
    have none : value = none := by simpa only [he, TreeSimCheckTimedStep] using timed i
    have absent := honestRounds_done_output (n + 1) steps out run i value he
    rw [none] at absent
    have present := success i
    rw [absent] at present
    cases present
  | wait _ _ => simp only [Step.isDone, not_false_eq_true]
  | call input _ => exact input.elim

theorem honestStep_timed {α : Type} (n : ℕ) (steps next : C.Party → Step C E RealSpec α)
    (timed : ∀ i, TreeSimCheckTimedStep (n + 1) (steps i))
    (run : next ∈ support (honestStep noFunctionality PEmpty.elim steps)) :
    ∀ i, TreeSimCheckTimedStep n (next i) := by
  have each := run
  rw [honestStep_real] at each
  have localRun := mem_support_sequenceFin_oc _ _ each
  intro i
  cases he : steps i with
  | done value =>
    have none : value = none := by simpa only [he, TreeSimCheckTimedStep] using timed i
    rw [honestStep_done steps next run i value he, none]
    cases n <;> simp only [TreeSimCheckTimedStep]
  | wait out resume =>
    have h : ∀ inbox, TreeSimCheckTimed n (resume inbox) := by
      simpa only [he, TreeSimCheckTimedStep] using timed i
    exact (h _).advance_mem _ (by simpa only [he] using localRun i)
  | call input _ => exact input.elim

/-- A successful timed honest prefix determines a fixed corrupt script for
exactly those rounds. Every row outside the prefix is preserved, so a later
scheduled abort can be retained. The original suspended source programs and
all honest local answers are replayed. -/
theorem recordingLocalSteps_of_honest_timed {α : Type}
    (impl : QueryImpl (LocalSpec C) ProbComp) (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (out : C.Party → Option α)
    (timed : ∀ i, TreeSimCheckTimedStep n (steps i))
    (run : out ∈ support (simulateQ impl (honestRounds noFunctionality PEmpty.elim n steps)))
    (success : ∀ i, (out i).isSome)
    (state : ℕ × List (C.Party → Mail C E)) (tail : ℕ → C.Party → Mail C E) :
    ∃ (sent : ℕ → C.Party → Mail C E) (views : List (C.Party → Mail C E)),
      (∀ m, m < state.1 ∨ state.1 + n ≤ m → sent m = tail m) ∧
      ((state.1 + n, views), maskedSteps D (fun i => Step.done (out i))) ∈ support
        (simulateQ impl (recordingLocalSteps D sent n state (maskedSteps D steps))) := by
  induction n generalizing steps state tail with
  | zero =>
    simp only [honestRounds, simulateQ_pure, support_pure, Set.mem_singleton_iff] at run
    have done : steps = fun i => .done (out i) := by
      funext i
      obtain ⟨value, he⟩ := (timed i).final
      rw [run]
      simp only [he, Step.output]
    refine ⟨tail, state.2, fun _ _ => rfl, ?_⟩
    rw [recordingLocalSteps, simulateQ_pure, done]
    exact Set.mem_singleton _
  | succ n ih =>
    have pending := honestRounds_timed_pending n steps out timed
      (simulated_source_support impl _ run) success
    obtain ⟨i, honest⟩ := prss_exists_honest D
    have notDone : ¬ ∀ j, (steps j).isDone := fun h => pending i (h i)
    rw [honestRounds, if_neg notDone, simulateQ_bind, mem_support_bind_iff] at run
    obtain ⟨next, round, rest⟩ := run
    let row : C.Party → Mail C E := fun j i => (steps j).delivered i
    let nextState := (state.1 + 1, state.2 ++ [recorderView D (fun i => (steps i).outbox)])
    let first : ℕ → C.Party → Mail C E := fun m => if m = state.1 then row else tail m
    obtain ⟨sent, views, outside, replay⟩ := ih next
      (honestStep_timed n steps next timed (simulated_source_support impl _ round)) rest nextState first
    have script : sent state.1 = row := by
      rw [outside state.1 (Or.inl (by dsimp only [nextState]; omega))]
      simp only [first, ite_true]
    refine ⟨sent, views, ?_, ?_⟩
    · intro m hm
      rw [outside m (by dsimp only [nextState]; omega)]
      simp only [first, if_neg (by omega : m ≠ state.1)]
    · have notDoneMasked : ¬ ∀ j, j ∉ D.1 → (maskedSteps D steps j).isDone := by
        intro h
        exact pending i (by simpa only [maskedSteps, if_neg honest] using h i honest)
      rw [recordingLocalSteps, if_neg notDoneMasked, simulateQ_bind]
      erw [mem_support_bind_iff]
      refine ⟨(nextState, maskedSteps D next, row),
        recordingLocalRound_honest_support impl D sent state steps next script round, ?_⟩
      have counter : state.1 + (n + 1) = (state.1 + 1) + n := by omega
      rw [counter]
      exact replay

/-- The fixed-script replay includes the actual local entry work of every
honest party, before the first network exchange. -/
theorem recordingLocalPhase_of_honest_timed {α : Type}
    (impl : QueryImpl (LocalSpec C) ProbComp) (D : C.Coalition) (n : ℕ)
    (p : C.Party → PartyM C E RealSpec α) (out : C.Party → Option α)
    (timed : ∀ i, TreeSimCheckTimed n (p i).run)
    (run : out ∈ support (simulateQ impl
      (honestStart p >>= honestRounds noFunctionality PEmpty.elim n)))
    (success : ∀ i, (out i).isSome)
    (state : ℕ × List (C.Party → Mail C E)) (tail : ℕ → C.Party → Mail C E) :
    ∃ (sent : ℕ → C.Party → Mail C E) (views : List (C.Party → Mail C E)),
      (∀ m, m < state.1 ∨ state.1 + n ≤ m → sent m = tail m) ∧
      ((state.1 + n, views), (fun i => if i ∈ D.1 then none else out i)) ∈ support
        (simulateQ impl (recordingLocalPhase D sent n state p)) := by
  rw [simulateQ_bind, mem_support_bind_iff] at run
  obtain ⟨steps, start, rounds⟩ := run
  rw [honestStart, simulateQ_sequenceFin] at start
  have each := mem_support_sequenceFin _ _ start
  have timedSteps : ∀ i, TreeSimCheckTimedStep n (steps i) := fun i =>
    (timed i).advance_mem _ (simulated_source_support impl _ (each i))
  obtain ⟨sent, views, outside, replay⟩ := recordingLocalSteps_of_honest_timed impl D n
    steps out timedSteps rounds success state tail
  refine ⟨sent, views, outside, ?_⟩
  have entries : maskedSteps D steps ∈ support (simulateQ impl
      (Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else advance (p i).run)) := by
    rw [simulateQ_sequenceFin]
    apply sequenceFin_support_of_each
    intro i
    by_cases corrupt : i ∈ D.1
    · simp only [if_pos corrupt, maskedSteps, simulateQ_pure, support_pure, Set.mem_singleton_iff]
    · simpa only [if_neg corrupt, maskedSteps] using each i
  unfold recordingLocalPhase
  rw [simulateQ_bind]
  erw [mem_support_bind_iff]
  refine ⟨maskedSteps D steps, entries, ?_⟩
  rw [simulateQ_bind]
  erw [mem_support_bind_iff]
  refine ⟨((state.1 + n, views), maskedSteps D (fun i => Step.done (out i))), replay, ?_⟩
  rw [simulateQ_pure]
  erw [mem_support_pure_iff]
  congr 1
  funext i
  simp only [maskedSteps]
  split_ifs <;> rfl

/-- Reverse honest-prefix replay lands in the actual logged execution,
with its actual final hash and hidden caches. -/
theorem recordingReplay_honest_timed_phase_realize {α : Type}
    (prims : Primitives) (D : C.Coalition) (hash : Query C → HashOutput)
    (hidden : HiddenAddress C → Bit) (good : Good prims hash) (n : ℕ)
    (p : C.Party → PartyM C E RealSpec α) (out : C.Party → Option α)
    (timed : ∀ i, TreeSimCheckTimed n (p i).run)
    (run : out ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (honestStart p >>= honestRounds noFunctionality PEmpty.elim n)))
    (success : ∀ i, (out i).isSome)
    (state : ℕ × List (C.Party → Mail C E)) (tail : ℕ → C.Party → Mail C E)
    (s : TreeSimState C) (initial : StreamCoherent hash hidden s.1) :
    ∃ (sent : ℕ → C.Party → Mail C E) (views : List (C.Party → Mail C E)) (next : TreeSimState C),
      (∀ m, m < state.1 ∨ state.1 + n ≤ m → sent m = tail m) ∧
      (((state.1 + n, views), (fun i => if i ∈ D.1 then none else out i)), next) ∈ support
        ((executePhase (treeSimRealRoles prims D) D (recordingReplay sent) noFunctionality n state p).run s) ∧
      StreamCoherent hash hidden next.1 := by
  obtain ⟨sent, views, outside, replay⟩ := recordingLocalPhase_of_honest_timed
    (prescribedLocal prims D hash hidden) D n p out timed run success state tail
  obtain ⟨next, actual, coherent⟩ := prescribedLocal_logged_realize prims D hash hidden good
    (recordingLocalPhase D sent n state p) _ s initial replay
  rw [← recordingReplay_phase_local] at actual
  refine ⟨sent, views, next, outside, ?_, coherent⟩
  rw [simulateQ_executePhase] at actual
  unfold recordingReplay at actual ⊢
  exact actual

theorem honest_phase_eq {α : Type} (fuel : ℕ) (p : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles noCoalition (honestAdversary (I := Keys C) PEmpty.elim)
      noFunctionality fuel () p =
      (fun out => ((), out)) <$> free (honestStart p >>= honestRounds noFunctionality PEmpty.elim fuel) := by
  unfold executePhase
  rw [startSteps_honest]
  simp only [executeRounds_honest, free_bind, map_bind]
  rfl

/-- A successful interpreted honest run supplies a supported, successful
prefix at its exact timed cut. The prefix answers are retained from that run. -/
theorem honest_timed_prefix_supported {α β : Type}
    (impl : QueryImpl (LocalSpec C) ProbComp) (n fuel : ℕ)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (exchange : ∀ i a, TreeSimCheckExchange (k i a))
    (out : C.Party → Option β)
    (run : out ∈ support (simulateQ impl
      (honestStart (fun i => p i >>= k i) >>= honestRounds noFunctionality PEmpty.elim (n + 1 + fuel))))
    (success : ∀ i, (out i).isSome) :
    ∃ pref, pref ∈ support (simulateQ impl
      (honestStart p >>= honestRounds noFunctionality PEmpty.elim (n + 1))) ∧
      ∀ i, (pref i).isSome := by
  let program : QueryImpl (ProgramSpec C) ProbComp := fun _ => pure false
  let world : QueryImpl (WorldSpec C) ProbComp := (impl + program) + impl
  let A := honestAdversary (C := C) (E := E) (I := Keys C) (PEmpty.elim : PEmpty → PEmpty)
  have actual : ((), out) ∈ support (simulateQ world
      (executePhase worldRoles noCoalition A noFunctionality (n + 1 + fuel) () (fun i => p i >>= k i))) := by
    rw [honest_phase_eq]
    erw [simulateQ_map, simulateQ_free, support_map]
    exact Set.mem_image_of_mem _ run
  rw [treeSimCheckTimed_phase_split noCoalition A n fuel () p k timed, simulateQ_bind] at actual
  erw [mem_support_bind_iff] at actual
  obtain ⟨pref, hpref, rest⟩ := actual
  rw [simulateQ_bind] at rest
  erw [mem_support_bind_iff] at rest
  obtain ⟨next, resumed, suffix⟩ := rest
  have accepted : ∃ i value, out i = some value := by
    obtain ⟨i, _⟩ := prss_exists_honest (noCoalition : C.Coalition)
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp (success i)
    exact ⟨i, value, present⟩
  have live := treeSimCheck_exchange_continuations_live noCoalition A fuel pref.1 pref.2 k exchange next
    (simulated_source_support world _ resumed) ((), out) (simulated_source_support world _ suffix) accepted
  have prefixSupported : pref.2 ∈ support (simulateQ impl
      (honestStart p >>= honestRounds noFunctionality PEmpty.elim (n + 1))) := by
    rw [honest_phase_eq] at hpref
    erw [simulateQ_map, simulateQ_free, support_map] at hpref
    obtain ⟨value, supported, equal⟩ := hpref
    have same : value = pref.2 := congrArg Prod.snd equal
    exact same ▸ supported
  exact ⟨pref.2, prefixSupported, fun i => live i (by simp)⟩

/-- The same successful honest execution supplies both its timed prefix
and its actual live continuation entries under the same oracle table. -/
theorem honest_timed_prefix_live_supported {α β : Type}
    (impl : QueryImpl (LocalSpec C) ProbComp) (n fuel : ℕ)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (exchange : ∀ i a, TreeSimCheckExchange (k i a))
    (out : C.Party → Option β)
    (run : out ∈ support (simulateQ impl
      (honestStart (fun i => p i >>= k i) >>= honestRounds noFunctionality PEmpty.elim (n + 1 + fuel))))
    (success : ∀ i, (out i).isSome) :
    ∃ pref next,
      pref ∈ support (simulateQ impl
        (honestStart p >>= honestRounds noFunctionality PEmpty.elim (n + 1))) ∧
      (∀ i, (pref i).isSome) ∧
      next ∈ support (simulateQ impl
        (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i)))) ∧
      ∀ i, ¬ (next i).isDone := by
  let program : QueryImpl (ProgramSpec C) ProbComp := fun _ => pure false
  let world : QueryImpl (WorldSpec C) ProbComp := (impl + program) + impl
  let A := honestAdversary (C := C) (E := E) (I := Keys C) (PEmpty.elim : PEmpty → PEmpty)
  have actual : ((), out) ∈ support (simulateQ world
      (executePhase worldRoles noCoalition A noFunctionality (n + 1 + fuel) () (fun i => p i >>= k i))) := by
    rw [honest_phase_eq]
    erw [simulateQ_map, simulateQ_free, support_map]
    exact Set.mem_image_of_mem _ run
  rw [treeSimCheckTimed_phase_split noCoalition A n fuel () p k timed, simulateQ_bind] at actual
  erw [mem_support_bind_iff] at actual
  obtain ⟨pref, hpref, rest⟩ := actual
  rw [simulateQ_bind] at rest
  erw [mem_support_bind_iff] at rest
  obtain ⟨next, resumed, suffix⟩ := rest
  have accepted : ∃ i value, out i = some value := by
    obtain ⟨i, _⟩ := prss_exists_honest (noCoalition : C.Coalition)
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp (success i)
    exact ⟨i, value, present⟩
  have rawNext := simulated_source_support world _ resumed
  have rawSuffix := simulated_source_support world _ suffix
  have live := treeSimCheck_exchange_continuations_live noCoalition A fuel pref.1 pref.2 k exchange
    next rawNext ((), out) rawSuffix accepted
  have prefixSupported : pref.2 ∈ support (simulateQ impl
      (honestStart p >>= honestRounds noFunctionality PEmpty.elim (n + 1))) := by
    rw [honest_phase_eq] at hpref
    erw [simulateQ_map, simulateQ_free, support_map] at hpref
    obtain ⟨value, supported, equal⟩ := hpref
    exact (congrArg Prod.snd equal) ▸ supported
  have each := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ rawNext)
  have nextExchange : ∀ i, TreeSimCheckExchangeStep (next i) := by
    intro i
    have localRun := each i
    cases he : pref.2 i with
    | none =>
      have absent : next i = .done none := by simpa [he, continueStep] using localRun
      simp [absent, TreeSimCheckExchangeStep]
    | some a => exact exchange i a _ (by simpa only [he, continueStep] using localRun)
  refine ⟨pref.2, next, prefixSupported, (fun i => live i (by simp)), ?_, ?_⟩
  · simpa only [world, simulateQ_free] using resumed
  · intro i done
    have absent : next i = .done none := by
      have pending := (nextExchange i).pending
      cases he : next i <;> simp_all [Step.isDone, Step.output]
    have allNone := treeSimCheck_exchange_rounds_abort noCoalition A fuel pref.1 next nextExchange
      ⟨i, by simp, absent⟩ ((), out) rawSuffix
    change out = fun _ => none at allNone
    obtain ⟨j, value, present⟩ := accepted
    simp only [allNone] at present
    cases present

/-- Appending a suffix to live continuation entries retains their network
boundary and reuses the same supported local answers. -/
theorem live_continuations_attach {α β γ : Type}
    (impl : QueryImpl (LocalSpec C) ProbComp)
    (pref : C.Party → Option α) (present : ∀ i, (pref i).isSome)
    (k : C.Party → α → PartyM C E RealSpec β)
    (finish : C.Party → α → β → PartyM C E RealSpec γ)
    (next : C.Party → Step C E RealSpec β)
    (run : next ∈ support (simulateQ impl
      (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i)))))
    (live : ∀ i, ¬ (next i).isDone) :
    ∃ next', next' ∈ support (simulateQ impl
      (Concrete.sequenceFin fun i => continueStep
        (fun a => k i a >>= finish i a) (.done (pref i)))) ∧
      ∀ i, ¬ (next' i).isDone := by
  choose data hdata using fun i => Option.isSome_iff_exists.mp (present i)
  let next' := fun i => suspendStep (finish i (data i)) (next i)
  refine ⟨next', ?_, fun i => ?_⟩
  · rw [simulateQ_sequenceFin] at run ⊢
    have each := mem_support_sequenceFin _ _ run
    apply sequenceFin_support_of_each
    intro i
    have localRun := each i
    simp only [hdata i, continueStep] at localRun ⊢
    rw [advance_bind, simulateQ_bind, mem_support_bind_iff]
    refine ⟨next i, localRun, ?_⟩
    have pending : (next i).output = none := by
      have active := live i
      cases he : next i <;> simp_all [Step.isDone, Step.output]
    rw [continueStep_pending _ _ pending, simulateQ_pure]
    exact Set.mem_singleton _
  · exact fun done => live i ((suspendStep_isDone _ _).mp done)

/-- Empty corrupt slots stay empty in the source scheduler itself. -/
theorem source_round_corrupt {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (empty : ∀ i, i ∈ D.1 → steps i = .done none)
    (r : A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E))
    (run : r ∈ support (stepRound worldRoles D A noFunctionality state steps)) :
    ∀ i, i ∈ D.1 → r.2.1 i = .done none := by
  rw [stepRound_real] at run
  obtain ⟨⟨state', sent⟩, _, run⟩ := (mem_support_bind_iff _ _ _).mp run
  obtain ⟨next, hn, equal⟩ := (mem_support_bind_iff _ _ _).mp run
  have same : r = (state', next, sent) := by simpa using equal
  subst r
  intro i hi
  have localRun := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
  simpa only [roundLocal, empty i hi, support_pure, Set.mem_singleton_iff] using localRun

theorem pending_stopped_none {α : Type} (D : C.Coalition)
    (steps : C.Party → Step C E RealSpec α)
    (pending : ∀ i, (steps i).output = none)
    (empty : ∀ i, i ∈ D.1 → steps i = .done none)
    (stopped : ∀ i, i ∉ D.1 → (steps i).isDone) :
    steps = fun _ => .done none := by
  funext i
  by_cases hi : i ∈ D.1
  · exact empty i hi
  · have done := stopped i hi
    have absent := pending i
    cases he : steps i <;> simp_all [Step.isDone, Step.output]

/-- A timed split retaining the exact source continuations, including
early aborts and the scheduler's empty corrupt slots. -/
theorem timed_steps_split {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimedStep (n + 1) (steps i))
    (empty : ∀ i, i ∈ D.1 → steps i = .done none) :
    executeSteps worldRoles D A noFunctionality (n + 1 + fuel) state
      (fun i => suspendStep (k i) (steps i)) = (do
      let p ← executeRounds worldRoles D A noFunctionality (n + 1) state steps
      let next ← free (Concrete.sequenceFin fun i => continueStep (k i) (.done (p.2 i)))
      executeSteps worldRoles D A noFunctionality fuel p.1 next) := by
  induction n generalizing state steps with
  | zero =>
    have pending := fun i => (timed i).pending
    have finish : ∀ i out resume, steps i = .wait out resume → i ∉ D.1 → ∀ inbox,
        ∃ result, advance (resume inbox) = pure (.done result) := by
      intro i out resume he hi inbox
      have h : TreeSimCheckTimed 0 (resume inbox) := (he ▸ timed i) inbox
      obtain ⟨result, hr⟩ := h.zero
      exact ⟨result, by rw [hr]; rfl⟩
    rw [Nat.zero_add, Nat.add_comm 1 fuel, executeSteps, executeRounds]
    simp only [suspendStep_isDone]
    split_ifs with stopped
    · have allNone := pending_stopped_none D steps pending empty stopped
      subst steps
      simp only [suspendStep, Step.output, pure_bind, continueStep, sequenceFin_pure, free_pure]
      exact (executeSteps_done worldRoles D A noFunctionality fuel state _ (by intros; trivial)).symm
    · rw [stepRound_suspend_finish D A state steps k pending finish]
      simp only [bind_assoc, pure_bind, executeRounds]
      rw [stepRound_real]
      simp only [bind_assoc]
      apply bind_congr
      rintro ⟨state', sent⟩
      have localFinish := roundLocal_suspend_finish D steps k pending finish sent
      choose result hresult hnext using localFinish
      have pureNext : roundLocal D steps sent = fun i => pure (.done (result i)) := funext hresult
      rw [pureNext, sequenceFin_pure, free_pure, pure_bind]
      rfl
  | succ n ih =>
    rw [Nat.succ_add, executeSteps, executeRounds]
    simp only [suspendStep_isDone]
    split_ifs with stopped
    · have allNone := pending_stopped_none D steps (fun i => (timed i).pending) empty stopped
      subst steps
      simp only [suspendStep, Step.output, pure_bind, continueStep, sequenceFin_pure, free_pure]
      exact (executeSteps_done worldRoles D A noFunctionality fuel state _ (by intros; trivial)).symm
    · rw [stepRound_suspend D A state steps k (fun i => (timed i).pending)
        (fun i out resume he hi inbox => ((he ▸ timed i) inbox).suspend (k i))]
      simp only [bind_assoc, pure_bind]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro r hr
      exact ih r.1 r.2.1 (treeSimCheckTimed_round D A (n + 1) state steps timed r hr)
        (source_round_corrupt D A state steps empty r hr)

/-- Splitting a party program preserves its actual pending programs, not
only their optional output projection. -/
theorem timed_phase_steps_split {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run) :
    (startSteps worldRoles D (fun i => p i >>= k i) >>= fun steps =>
      executeSteps worldRoles D A noFunctionality (n + 1 + fuel) state steps) = (do
      let out ← executePhase worldRoles D A noFunctionality (n + 1) state p
      let next ← free (Concrete.sequenceFin fun i => continueStep (k i) (.done (out.2 i)))
      executeSteps worldRoles D A noFunctionality fuel out.1 next) := by
  simp only [executePhase, treeSimCheckTimed_start D n p k timed, bind_map_left, bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro steps hs
  apply timed_steps_split D A n fuel state steps k (treeSimCheckTimed_start_mem D (n + 1) p timed steps hs)
  intro i hi
  have entry := mem_support_sequenceFin_oc _ _ hs i
  simpa only [if_pos hi, support_pure, Set.mem_singleton_iff] using entry

/-- One fixed recorder replays a supported timed prefix and its retained
continuation entries from every cache coherent with the same two tables. -/
theorem recordingReplay_timed_resume_replay {α β : Type} (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (n : ℕ) (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run) (pref : C.Party → Option α)
    (run : pref ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (honestStart p >>= honestRounds noFunctionality PEmpty.elim (n + 1))))
    (present : ∀ i, (pref i).isSome) (entries : C.Party → Step C E RealSpec β)
    (entryRun : entries ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i)))))
    (state : ℕ × List (C.Party → Mail C E)) (tail : ℕ → C.Party → Mail C E) :
    ∃ (sent : ℕ → C.Party → Mail C E) (views : List (C.Party → Mail C E)),
      (∀ m, m < state.1 ∨ state.1 + (n + 1) ≤ m → sent m = tail m) ∧
      ∀ s : TreeSimState C, StreamCoherent hash hidden s.1 → ∃ next : TreeSimState C,
        (((state.1 + (n + 1), views), maskedSteps D entries), next) ∈ support
          ((simulateQ (treeSimLoggedWorld prims D)
            (startSteps worldRoles D (fun i => p i >>= k i) >>= fun steps =>
              executeSteps worldRoles D (recordingReplay sent) noFunctionality (n + 1) state steps)).run s) ∧
        StreamCoherent hash hidden next.1 := by
  obtain ⟨sent, views, outside, prefixRun⟩ := recordingLocalPhase_of_honest_timed
    (prescribedLocal prims D hash hidden) D (n + 1) p pref timed run present state tail
  refine ⟨sent, views, outside, ?_⟩
  intro s coherent
  obtain ⟨boundary, prefixActual, boundaryCoherent⟩ := prescribedLocal_logged_realize prims D hash hidden good
    (recordingLocalPhase D sent (n + 1) state p)
    ((state.1 + (n + 1), views), fun i => if i ∈ D.1 then none else pref i) s coherent prefixRun
  rw [← recordingReplay_phase_local] at prefixActual
  let outputs := fun i => if i ∈ D.1 then none else pref i
  let continuation := Concrete.sequenceFin fun i => continueStep (k i) (.done (outputs i))
  have maskedRun : maskedSteps D entries ∈ support
      (simulateQ (prescribedLocal prims D hash hidden) continuation) := by
    rw [simulateQ_sequenceFin] at entryRun
    have each := mem_support_sequenceFin _ _ entryRun
    simp only [continuation, simulateQ_sequenceFin]
    apply sequenceFin_support_of_each
    intro i
    by_cases corrupt : i ∈ D.1
    · simp only [outputs, maskedSteps, if_pos corrupt, continueStep, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
    · simpa only [outputs, maskedSteps, if_neg corrupt] using each i
  obtain ⟨next, actualEntries, finalCoherent⟩ := prescribedLocal_logged_realize prims D hash hidden good
    continuation (maskedSteps D entries) boundary boundaryCoherent maskedRun
  refine ⟨next, ?_, finalCoherent⟩
  rw [show n + 1 = n + 1 + 0 by omega,
    timed_phase_steps_split D (recordingReplay sent) n 0 state p k timed]
  unfold recordingReplay at prefixActual ⊢
  simp only [simulateQ_bind, executeSteps, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  exact ⟨(((state.1 + (n + 1), views), outputs), boundary), prefixActual,
    (maskedSteps D entries, next), actualEntries, rfl⟩

theorem recordingLocalSteps_wait {α : Type} (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State) (fuel : ℕ)
    (outbox : C.Party → Mail C E)
    (resume : C.Party → Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
    (script : sent state.1 = outbox) :
    recordingLocalSteps D sent (fuel + 1) state
      (maskedSteps D (fun i => .wait (outbox i) (resume i))) = (do
      let next ← Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else
        advance (resume i (fun j => outbox j i))
      recordingLocalSteps D sent fuel
        (state.1 + 1, state.2 ++ [recorderView D outbox]) next) := by
  have pending : ¬ ∀ i, i ∉ D.1 →
      (maskedSteps D (fun i => Step.wait (outbox i) (resume i)) i).isDone := by
    intro allDone
    obtain ⟨i, hi⟩ := prss_exists_honest D
    simpa [maskedSteps, hi, Step.isDone] using allDone i hi
  rw [recordingLocalSteps, if_neg pending, recordingLocalRound_wait D sent state outbox resume script]
  simp only [bind_assoc, pure_bind]

def prssReplayScript (prims : Primitives) (hash : Query C → HashOutput)
    (parts : C.Party → Parts C) : ℕ → C.Party → Mail C E
  | 0 => fun i => commitOutbox i (ThresholdLeanXmssSecurity.D prims hash (commitQueries .prss i (parts i)))
  | 1 => fun i => revealOutbox .prss i (parts i)
  | 2 => fun i =>
      let keys := ThresholdLeanXmssSecurity.D prims hash (deriveKeys .prss i (honestView (E := E) .prss parts i))
      echoOutbox .prss i keys (ThresholdLeanXmssSecurity.D prims hash (sharedQueries .prss i keys))
  | _ => fun _ _ => none

def prssRecorderState (prims : Primitives) (D : C.Coalition) (hash : Query C → HashOutput)
    (parts : C.Party → Parts C) (sent : ℕ → C.Party → Mail C E) : (recordingReplay sent).State :=
  (3, [recorderView D (prssReplayScript prims hash parts 0),
    recorderView D (prssReplayScript prims hash parts 1),
    recorderView D (prssReplayScript prims hash parts 2)])

set_option backward.isDefEq.respectTransparency false in
/-- The concrete recorder can complete all three actual setup rounds using
the honest commit, reveal and echo rows for any prescribed contribution table. -/
theorem recordingReplay_prssLocalRounds (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (parts : C.Party → Parts C) (sent : ℕ → C.Party → Mail C E)
    (script : ∀ n, n < 3 → sent n = prssReplayScript prims hash parts n) :
    simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalSteps D sent 3 (0, [])
        (maskedSteps D (fun i => prssStart i (parts i)
          (ThresholdLeanXmssSecurity.D prims hash (commitQueries .prss i (parts i))) pure))) =
      pure (prssRecorderState prims D hash parts sent,
        maskedSteps D (fun i => Step.done (some (honestPrssKeys hash parts i)))) := by
  let keys := fun i => ThresholdLeanXmssSecurity.D prims hash
    (deriveKeys .prss i (honestView (E := E) .prss parts i))
  let shared := fun i => ThresholdLeanXmssSecurity.D prims hash (sharedQueries .prss i (keys i))
  let commit := fun i => commitOutbox (E := E) i
    (ThresholdLeanXmssSecurity.D prims hash (commitQueries .prss i (parts i)))
  let reveal := fun i => revealOutbox (E := E) .prss i (parts i)
  let echo := fun i => echoOutbox (E := E) .prss i (keys i) (shared i)
  have hkeys i : (⟨(keys i).2.1, (keys i).2.2⟩ : PrssKeys C) = honestPrssKeys hash parts i := by
    simp only [keys, D_deriveKeys_honest]
    rfl
  have first i : advance (exchangeResume (fun committed =>
        exchange (revealOutbox .prss i (parts i)) >>= fun revealed =>
        setupRest .prss i (parts i) committed revealed >>= fun ks => pure ⟨ks.2.1, ks.2.2⟩)
      (fun j => commit j i) : OracleComp (PartySpec C E RealSpec) (Option (PrssKeys C))) =
      pure (.wait (reveal i) (exchangeResume fun revealed =>
        setupRest .prss i (parts i) (fun j => commit j i) revealed >>= fun ks => pure ⟨ks.2.1, ks.2.2⟩)) := by
    simp only [commit, reveal]
    rw [exchangeResume_of_no_abort _ _ (fun j => isAbort_commitOutbox j _ i)]
    exact advance_setup_reveal _ _ _ _
  have second i : simulateQ (prescribedLocal prims D hash hidden)
      (advance (exchangeResume (fun revealed =>
        setupRest .prss i (parts i) (fun j => commit j i) revealed >>= fun ks => pure ⟨ks.2.1, ks.2.2⟩)
        (fun j => reveal j i) : OracleComp (PartySpec C E RealSpec) (Option (PrssKeys C)))) =
      pure (.wait (echo i) (exchangeResume fun received =>
        require (echoCheck .prss i (keys i) (shared i) received) >>= fun _ =>
          pure ⟨(keys i).2.1, (keys i).2.2⟩)) := by
    simp only [commit, reveal, echo]
    rw [exchangeResume_of_no_abort _ _ (fun j => isAbort_revealOutbox _ j _ i),
      advance_setupRest, simulateQ_bind,
      prescribedLocal_hashOnly prims D hash hidden
        (openQueries .prss i (fun j => revealOutbox .prss j (parts j) i))
        (by exact TreeCheckMaskExtraction.hash_mapM_noPrg _ _), pure_bind]
    split_ifs with accepted
    · rw [simulateQ_bind, prescribedLocal_hashOnly prims D hash hidden _
        (TreeCheckMaskExtraction.deriveKeys_noPrg _ _ _), pure_bind,
        simulateQ_bind, prescribedLocal_hashOnly prims D hash hidden (sharedQueries .prss i _)
        (by exact TreeCheckMaskExtraction.hash_mapM_noPrg _ _), pure_bind, simulateQ_pure]
      rfl
    · exact absurd (openCheck_honest prims hash .prss parts i) accepted
  have third i : advance (exchangeResume (fun received =>
        require (echoCheck .prss i (keys i) (shared i) received) >>= fun _ =>
          pure ⟨(keys i).2.1, (keys i).2.2⟩)
      (fun j => echo j i) : OracleComp (PartySpec C E RealSpec) (Option (PrssKeys C))) =
      pure (.done (some (honestPrssKeys hash parts i))) := by
    simp only [echo]
    rw [exchangeResume_of_no_abort _ _ (fun j => isAbort_echoOutbox _ j _ _ i),
      advance_require_bind, if_pos (echoCheck_honest prims hash .prss parts i), hkeys]
    rfl
  unfold prssStart
  rw [recordingLocalSteps_wait D sent (0, []) 2
    (fun i => commitOutbox i (ThresholdLeanXmssSecurity.D prims hash (commitQueries .prss i (parts i)))) _
    (by simpa only [prssReplayScript] using script 0 (by decide))]
  simp only [commit] at first
  simp only [first]
  have maskPure {α : Type} (steps : C.Party → Step C E RealSpec α) :
      (Concrete.sequenceFin fun i => if i ∈ D.1 then
        (pure (.done none) : OracleComp (LocalSpec C) _) else pure (steps i)) =
        pure (maskedSteps D steps) := by
    simpa only [maskedSteps, apply_ite (pure : Step C E RealSpec α → OracleComp (LocalSpec C) _)]
      using sequenceFin_pure (m := OracleComp (LocalSpec C)) (maskedSteps D steps)
  rw [maskPure, pure_bind]
  simp only [Nat.zero_add, List.nil_append]
  rw [recordingLocalSteps_wait D sent
    (1, [recorderView D commit]) 1 reveal _
    (by simpa only [prssReplayScript] using script 1 (by decide)),
    simulateQ_bind, simulateQ_sequenceFin]
  have secondAll : (Concrete.sequenceFin fun i => simulateQ (prescribedLocal prims D hash hidden)
      (if i ∈ D.1 then pure (.done none) else advance (exchangeResume (fun revealed =>
        setupRest .prss i (parts i) (fun j => commit j i) revealed >>= fun ks => pure ⟨ks.2.1, ks.2.2⟩)
        (fun j => reveal j i) : OracleComp (PartySpec C E RealSpec) (Option (PrssKeys C))))) =
      pure (maskedSteps D (fun i => .wait (echo i) (exchangeResume fun received =>
        require (echoCheck .prss i (keys i) (shared i) received) >>= fun _ =>
          pure ⟨(keys i).2.1, (keys i).2.2⟩))) := by
    trans Concrete.sequenceFin (fun i => pure (maskedSteps D (fun i => Step.wait (echo i)
      (exchangeResume fun received => require (echoCheck .prss i (keys i) (shared i) received) >>= fun _ =>
        pure (⟨(keys i).2.1, (keys i).2.2⟩ : PrssKeys C))) i))
    · congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp only [maskedSteps, if_pos hi, simulateQ_pure]
      · simpa only [maskedSteps, if_neg hi] using second i
    · exact sequenceFin_pure _
  rw [secondAll, pure_bind]
  simp only [List.singleton_append]
  rw [recordingLocalSteps_wait D sent
    (2, [recorderView D commit, recorderView D reveal]) 0 echo _
    (by simpa only [prssReplayScript] using script 2 (by decide))]
  simp only [third, maskPure, pure_bind, recordingLocalSteps, simulateQ_pure]
  rfl

/-- Every prescribed contribution table is supported by the actual private
setup draws. The remaining script rows can be chosen for the ceremony. -/
theorem recordingReplay_prssLocalPhase (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (parts : C.Party → Parts C) (sent : ℕ → C.Party → Mail C E)
    (script : ∀ n, n < 3 → sent n = prssReplayScript prims hash parts n) :
    (prssRecorderState prims D hash parts sent,
      fun i => if i ∈ D.1 then none else some (honestPrssKeys hash parts i)) ∈ support
      (simulateQ (prescribedLocal prims D hash hidden)
        (recordingLocalPhase D sent 3 (0, [])
          (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))) := by
  rw [recordingLocalPhase, simulateQ_bind, simulateQ_sequenceFin, mem_support_bind_iff]
  refine ⟨maskedSteps D (fun i => prssStart i (parts i)
    (ThresholdLeanXmssSecurity.D prims hash (commitQueries .prss i (parts i))) pure), ?_, ?_⟩
  · apply sequenceFin_support_of_each
    intro i
    by_cases hi : i ∈ D.1
    · simp only [maskedSteps, if_pos hi, simulateQ_pure, support_pure, Set.mem_singleton_iff]
    · simp only [maskedSteps, if_neg hi]
      have start := advance_prssSetup i (pure : PrssKeys C → PartyM C E RealSpec (PrssKeys C))
      simp only [bind_pure] at start
      rw [start, simulateQ_bind, prescribedLocal_private, mem_support_bind_iff]
      refine ⟨parts i, sampleParts_support _, ?_⟩
      rw [simulateQ_bind, prescribedLocal_hashOnly prims D hash hidden
        (commitQueries .prss i (parts i)) (by exact TreeCheckMaskExtraction.hash_mapM_noPrg _ _),
        pure_bind, simulateQ_pure]
      simp only [support_pure, Set.mem_singleton_iff]
  · rw [simulateQ_bind, recordingReplay_prssLocalRounds prims D hash hidden parts sent script,
      pure_bind, simulateQ_pure]
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, true_and]
    funext i
    by_cases hi : i ∈ D.1 <;> simp only [maskedSteps, hi, ↓reduceIte, Step.output]

/-- The full cooperative setup is supported by the actual logged world,
with coherent hash and hidden caches retained for the next ceremony round. -/
theorem recordingReplay_prssPhase_realize (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (parts : C.Party → Parts C) (sent : ℕ → C.Party → Mail C E)
    (script : ∀ n, n < 3 → sent n = prssReplayScript prims hash parts n)
    (s : TreeSimState C) (initial : StreamCoherent hash hidden s.1) :
    ∃ next, ((prssRecorderState prims D hash parts sent,
      fun i => if i ∈ D.1 then none else some (honestPrssKeys hash parts i)), next) ∈ support
      ((executePhase (treeSimRealRoles prims D) D (recordingReplay sent) noFunctionality 3 (0, [])
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s) ∧
      StreamCoherent hash hidden next.1 := by
  have result := prescribedLocal_logged_realize prims D hash hidden good
    (recordingLocalPhase D sent 3 (0, [])
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))) _ s initial
    (recordingReplay_prssLocalPhase prims D hash hidden parts sent script)
  rw [← recordingReplay_phase_local, simulateQ_executePhase] at result
  exact result

theorem chunks_one_cons {α : Type} (item : α) (items : List α) :
    ∃ rest, chunks 1 (item :: items) = [item] :: rest := by
  simp only [chunks, List.length_cons, Nat.add_sub_cancel, Nat.div_one,
    List.range_succ_eq_map, List.map_cons, Nat.mul_zero, List.drop_zero,
    List.take_succ_cons, List.take_zero]
  exact ⟨_, rfl⟩

/-- Exposes a specified first top-tree job without evaluating the remaining jobs. -/
theorem top_firstBatch_factor_head (ctx : Context C) (circuits : Circuits) (top : TopTree)
    (job : Job) (jobs : List Job) (head : topJobs = job :: jobs) :
    ∃ finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput,
      ceremonyAfterSetup K circuits ⟨.peer, 1⟩ ctx top .top = (do
        let input ← inputShares ctx job
        let out ← (runJobs K (realRunGadgets K ctx .peer)
          [circuits ctx.keys.parameter job.kind] [input]).run ⟨fun _ => [], 0, 0⟩
        finish out) := by
  obtain ⟨rest, chunkEq⟩ := chunks_one_cons job jobs
  refine ⟨?_, ?_⟩
  swap
  simp only [ceremonyAfterSetup, ceremonyOutput, batched, head, chunkEq, List.mapM_cons,
    StateT.run'_eq, StateT.run_bind, StateT.run_lift,
    ceremonyBatch, StateT.run_get, StateT.run_set, List.mapM_nil, List.map_cons, List.map_nil,
    pure_bind, bind_assoc, map_bind, bind_map_left]
  rfl

/-- The first top-tree batch is an actual singleton job with one PRF point.
The continuation retains every remaining batch and the public tree assembly. -/
theorem top_firstBatch_factor (ctx : Context C) (circuits : Circuits) (top : TopTree) :
    ∃ (job : Job) (point : Point)
      (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput),
      job.points = [point] ∧
      ceremonyAfterSetup K circuits ⟨.peer, 1⟩ ctx top .top = (do
        let input ← inputShares ctx job
        let out ← (runJobs K (realRunGadgets K ctx .peer)
          [circuits ctx.keys.parameter job.kind] [input]).run ⟨fun _ => [], 0, 0⟩
        finish out) := by
  obtain ⟨job, jobs, point, topEq, points⟩ := SeedHitProof.topJobs_head
  obtain ⟨finish, source⟩ := top_firstBatch_factor_head K ctx circuits top job jobs topEq
  exact ⟨job, point, finish, points, source⟩

def identityCheckFinish (ctx : Context C) (input : C.Term → List Bit)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (z : Shares C Bit × RunState C) : PartyM C E RealSpec TreeOutput := do
  let out ← (do
    check K ctx (realCheckGadgets K ctx)
      [⟨outputShares K [Circuit.identity 1] [input], one K, z.1, 1, .peer⟩]
    let opened ← StateT.lift (openRep K ctx z.1 1)
    pure [[opened 0]]).run z.2
  finish out

/-- The actual first singleton identity batch begins with its output
rerandomization and continues into the real check of that same tuple. -/
theorem top_identity_peer_factor (ctx : Context C) (top : TopTree) :
    ∃ (job : Job) (point : Point)
      (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput),
      job.points = [point] ∧
      ceremonyAfterSetup K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ ctx top .top = (do
        let input ← inputShares ctx job
        treeSimPeerProgram K ctx 0 1
          (ownerSum K ctx (outputShares K [Circuit.identity 1] [input])) ⟨fun _ => [], 0, 0⟩
          (identityCheckFinish K ctx input finish)) := by
  obtain ⟨job, point, finish, points, source⟩ :=
    top_firstBatch_factor K ctx (fun _ _ => Circuit.identity 1) top
  refine ⟨job, point, finish, points, ?_⟩
  rw [source]
  apply bind_congr
  intro input
  rw [identity_one_run]
  simp only [StateT.run_bind, bind_assoc, realRunGadgets, treeSimPeerProgram]
  apply bind_congr
  intro rnd
  apply bind_congr
  intro z
  simp only [identityCheckFinish, StateT.run_bind, bind_assoc]

/-- All parties enter the same first job; only their contexts and their
remaining ceremony continuations differ. -/
theorem top_identity_peer_factor_all (ctx : C.Party → Context C) (top : TopTree) :
    ∃ (job : Job) (point : Point)
      (finish : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput),
      job.points = [point] ∧ ∀ i,
      ceremonyAfterSetup K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ (ctx i) top .top = (do
        let input ← inputShares (ctx i) job
        treeSimPeerProgram K (ctx i) 0 1
          (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input])) ⟨fun _ => [], 0, 0⟩
          (identityCheckFinish K (ctx i) input (finish i))) := by
  obtain ⟨job, jobs, point, head, points⟩ := SeedHitProof.topJobs_head
  choose finish source using fun i =>
    top_firstBatch_factor_head K (ctx i) (fun _ _ => Circuit.identity 1) top job jobs head
  refine ⟨job, point, finish, points, ?_⟩
  intro i
  rw [source i]
  apply bind_congr
  intro input
  rw [identity_one_run]
  simp only [StateT.run_bind, bind_assoc, realRunGadgets, treeSimPeerProgram]
  apply bind_congr
  intro rnd
  apply bind_congr
  intro z
  simp only [identityCheckFinish, StateT.run_bind, bind_assoc]

/-- Every bit vector is supported by the actual fresh hidden-stream
block, with its exact populated cache and classified query log. -/
theorem fresh_hidden_block_support (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → HiddenAddress C) (injective : Function.Injective addr)
    (hidden : ∀ i, Hidden D (addr i).1.1) (s : TreeSimState C)
    (fresh : ∀ i, s.1.2 (addr i) = none) (values : Fin n → Bit) :
    (values, (s.1.1, cacheFin addr values s.1.2), s.2 ++ treeSimHiddenLog addr values) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run s) := by
  rw [treeSim_hiddenDraws_log, support_map]
  refine ⟨(values, s.1.1, cacheFin addr values s.1.2), ?_, rfl⟩
  apply (mem_support_evalDist_iff _ _).1
  rw [show 𝒟[(simulateQ (streamWorld prims D) (hiddenDraws addr)).run s.1] =
      𝒟[(fun vals => (vals, (s.1.1, cacheFin addr vals s.1.2))) <$> ($ᵗ (Fin n → Bit))] from
    streamWorld_sequenceFin_fresh prims D addr injective hidden s.1.1 s.1.2 fresh]
  apply (mem_support_evalDist_iff _ _).2
  simp only [support_map, support_uniformSample]
  exact ⟨values, Set.mem_univ _, rfl⟩

/-- A fresh hidden field draw in the actual protocol supports every field
value at coordinate zero, with its exact encoded bits in the cache and log. -/
theorem fresh_hidden_element_support (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (hidden : Hidden D name) (key : HashOutput) (label idx : ℕ)
    (s : TreeSimState C)
    (fresh : ∀ g : Fin elementBits, s.1.2 ((name, key), label, idx, g.val) = none)
    (value : E) :
    let addr := fun g : Fin elementBits => ((name, key), label, idx, g.val)
    ∃ out : ℕ → E, out 0 = value ∧
      (out, (s.1.1, cacheFin addr (K.encode value) s.1.2),
        s.2 ++ treeSimHiddenLog addr (K.encode value)) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx 1) (LocalSpec C)))).run s) := by
  let addr := fun g : Fin elementBits => ((name, key), label, idx, g.val)
  have injective : Function.Injective addr := by
    intro a b equal
    exact Fin.ext (congrArg (fun x : HiddenAddress C => x.2.2.2) equal)
  let finalState : TreeSimState C :=
    ((s.1.1, cacheFin addr (K.encode value) s.1.2), s.2 ++ treeSimHiddenLog addr (K.encode value))
  let bits := fun g => (List.ofFn (K.encode value)).getD g 0
  have bitRun : (bits, finalState) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prgBits name key label idx elementBits) (LocalSpec C)))).run s) := by
    rw [treeSim_prgBits_table, simulateQ_map, StateT.run_map, support_map]
    exact ⟨(K.encode value, finalState),
      fresh_hidden_block_support prims D addr injective (fun _ => hidden) s fresh (K.encode value), rfl⟩
  refine ⟨(fun g => K.encode.symm (fun b => bits (elementBits * g + b.val))), ?_, ?_⟩
  · change K.encode.symm (fun b => bits (elementBits * 0 + b.val)) = value
    have encoded : (fun b : Fin elementBits => bits (elementBits * 0 + b.val)) = K.encode value := by
      funext b
      simp [bits, List.getD_eq_getElem?_getD, b.isLt]
    rw [encoded]
    exact K.encode.symm_apply_apply value
  · change ((fun g => K.encode.symm (fun b => bits (elementBits * g + b.val))), finalState) ∈ _
    simp only [elementCodec, Nat.mul_one, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff]
    exact ⟨(bits, finalState), bitRun, by simp⟩

/-- Replaces exactly one labelled hidden block and leaves all other
addresses unchanged. Freshness is checked against the starting cache. -/
def replaceHiddenBlock {n : ℕ} (name : KeyName C) (key : HashOutput) (label idx : ℕ)
    (values : Fin n → Bit) (old : HiddenAddress C → Bit) (x : HiddenAddress C) : Bit :=
  if h : x.1 = (name, key) ∧ x.2.1 = label ∧ x.2.2.1 = idx ∧ x.2.2.2 < n then
    values ⟨x.2.2.2, h.2.2.2⟩ else old x

theorem replaceHiddenBlock_at {n : ℕ} (name : KeyName C) (key : HashOutput) (label idx : ℕ)
    (values : Fin n → Bit) (old : HiddenAddress C → Bit) (b : Fin n) :
    replaceHiddenBlock name key label idx values old ((name, key), label, idx, b.val) = values b := by
  simp only [replaceHiddenBlock, b.isLt, and_self, dite_true]

theorem replaceHiddenBlock_agrees {n : ℕ} (name : KeyName C) (key : HashOutput) (label idx : ℕ)
    (values : Fin n → Bit) (old : HiddenAddress C → Bit) (cache : HiddenCache C)
    (initial : cache.AgreesWithFn old)
    (fresh : ∀ b : Fin n, cache ((name, key), label, idx, b.val) = none) :
    cache.AgreesWithFn (replaceHiddenBlock name key label idx values old) := by
  intro x value found
  unfold replaceHiddenBlock
  split_ifs with block
  · have address : x = ((name, key), label, idx, x.2.2.2) := by
      rcases x with ⟨⟨xn, xk⟩, xl, xi, xp⟩
      simp only [Prod.mk.injEq] at block
      rcases block with ⟨⟨rfl, rfl⟩, rfl, rfl, _⟩
      rfl
    have empty := fresh ⟨x.2.2.2, block.2.2.2⟩
    rw [← address, found] at empty
    cases empty
  · exact initial found

theorem prescribedValue_prgBits (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    prescribedValue prims D hash hidden (prgBits name key label idx count) =
      fun g => ((List.range count).map (fun position =>
        if Hidden D name then hidden ((name, key), label, idx, position)
        else prims.aes.eval (truncateHash (hash (.streamKey key))) (label, idx, position))).getD g 0 := by
  unfold prgBits
  rw [prescribedValue_bind, prescribedValue_mapM, prescribedValue_pure]
  congr 1

/-- Prescribing encoded bits controls the actual field draw's first value,
without imposing a zero-preserving or linear encoding. -/
theorem prescribedValue_element_zero (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (name : KeyName C) (secret : Hidden D name) (key : HashOutput) (label idx : ℕ) (value : E)
    (encoded : ∀ b : Fin elementBits, hidden ((name, key), label, idx, b.val) = K.encode value b) :
    prescribedValue prims D hash hidden ((elementCodec K).draw name key label idx 1) 0 = value := by
  simp only [elementCodec, Nat.mul_one, prescribedValue_bind, prescribedValue_pure,
    prescribedValue_prgBits, if_pos secret, Nat.mul_zero, Nat.zero_add]
  have bits : (fun b : Fin elementBits =>
      ((List.range elementBits).map (fun position => hidden ((name, key), label, idx, position))).getD b.val 0) =
      K.encode value := by
    funext b
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using b.isLt)]
    simpa only [List.getElem_map, List.getElem_range] using encoded b
  rw [bits]
  exact K.encode.symm_apply_apply value

/-- A replacement block cannot change a draw under another key name. -/
theorem prescribedValue_element_other (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    {n : ℕ} (name : KeyName C) (key : HashOutput) (label idx : ℕ) (values : Fin n → Bit)
    (other : KeyName C) (different : other ≠ name) (otherKey : HashOutput)
    (otherLabel otherIdx count : ℕ) :
    prescribedValue prims D hash (replaceHiddenBlock name key label idx values hidden)
      ((elementCodec K).draw other otherKey otherLabel otherIdx count) =
      prescribedValue prims D hash hidden ((elementCodec K).draw other otherKey otherLabel otherIdx count) := by
  have bits : prescribedValue prims D hash (replaceHiddenBlock name key label idx values hidden)
      (prgBits other otherKey otherLabel otherIdx (elementBits * count)) =
      prescribedValue prims D hash hidden (prgBits other otherKey otherLabel otherIdx (elementBits * count)) := by
    simp only [prescribedValue_prgBits]
    funext g
    congr 2
    funext position
    simp only [replaceHiddenBlock, Prod.mk.injEq, different, false_and, dite_false]
  simp only [elementCodec, prescribedValue_bind, prescribedValue_pure, bits]

/-- Common term streams make the actual checked Coin opening accept;
pair streams have no influence on that opening. -/
theorem coinRes_common (rr : Shares C E) (zz : C.Party → C.Party → ℕ → E) (count : ℕ)
    (i : C.Party) :
    coinRes K i count (honestR rr i, zz i)
      (fun j => coinOut K j count (honestR rr j, zz j) i) =
      some (vector count (fun g => ∑ T, rr T g)) := by
  haveI : CharP E 2 := charP_two
  let shares := fun j => conv K (localContext j) (honestR rr j)
  have opening := openShN_honest K shares (fun g => ∑ T, rr T g) count
    (fun g _ => isShamir_honestR K rr g) i
  unfold coinRes
  rw [if_neg (by simp [anyAbort, coinOut, openOut, Msg.isAbort])]
  change (if OpenAgreesN K i (shares i) count (fun j => openOut j (shares j) count i)
    then some (openValueN K i (shares i) (fun j => openOut j (shares j) count i)) else none).map
      (vector count) = _
  rw [if_pos opening.1, Option.map_some]
  congr 1
  exact vector_congr' count _ _ opening.2

/-- A cooperative actual Coin exchange accepts the common PRSS sum and
continues the original suspended programs, retaining the recorder view. -/
theorem recordingLocalRound_coin (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (rr : Shares C E) (zz : C.Party → C.Party → ℕ → E) (count : ℕ)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (script : sent state.1 = fun i => coinOut K i count (honestR rr i, zz i)) :
    simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalRound D sent state (maskedSteps D (fun i =>
        treeSimCoinStep K (ctx i) (honestR rr i, zz i) count (st i) (k i)))) = (do
      let steps ← Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else
        simulateQ (prescribedLocal prims D hash hidden)
          (advance (k i (vector count (fun g => ∑ T, rr T g), nextLabel (st i))).run)
      pure ((state.1 + 1, state.2 ++ [recorderView D (fun i => coinOut K i count (honestR rr i, zz i))]),
        steps, (fun i => coinOut K i count (honestR rr i, zz i)))) := by
  have converted (i : C.Party) : conv K (ctx i) (honestR rr i) =
      conv K (localContext i) (honestR rr i) := by
    funext g
    simp only [ThresholdLeanXmss.conv, self, localContext]
  unfold treeSimCoinStep
  simp only [converted, self]
  change sent state.1 = (fun i => openOut i (conv K (localContext i) (honestR rr i)) count) at script
  erw [recordingLocalRound_wait D sent state _ _ script]
  rw [simulateQ_bind, simulateQ_sequenceFin]
  apply OracleComp.bind_congr'
  · congr 1
    funext i
    by_cases corrupt : i ∈ D.1
    · simp only [if_pos corrupt, simulateQ_pure]
    · simp only [if_neg corrupt]
      rw [exchangeResume_of_no_abort _ _ (by intro j; simp [openOut, Msg.isAbort])]
      haveI : CharP E 2 := charP_two
      have opening := openShN_honest K
        (fun j => conv K (localContext j) (honestR rr j))
        (fun g => ∑ T, rr T g) count (fun g _ => isShamir_honestR K rr g) i
      simp only [require, if_pos opening.1, pure_bind]
      have values := vector_congr' count _ _ opening.2
      rw [values]
  · intro steps
    exact simulateQ_pure _ _

theorem peer_program_interpret (impl : QueryImpl (LocalSpec C) ProbComp)
    (ctx : Context C) (idx count : ℕ) (value : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) :
    simulateQ impl (advance (treeSimPeerProgram K ctx idx count value st k).run) =
      (fun rnd => treeSimPeerStep K ctx bitCodec rnd value count st k) <$>
        simulateQ impl (liftComp (prssDraw ctx (bitCodec (E := E)) st.label idx count) (LocalSpec C)) := by
  let program : QueryImpl (ProgramSpec C) ProbComp := fun _ => pure false
  let world : QueryImpl (WorldSpec C) ProbComp := (impl + program) + impl
  have source := treeSim_peer_entry K ctx (bitCodec (E := E)) idx count value st k
  have interpreted := congrArg (simulateQ world) source
  simpa only [world, worldRoles, simulateQ_free, simulateQ_map, treeSimPeerProgram] using interpreted

theorem peer_program_prescribed (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (ctx : Context C) (idx count : ℕ) (value : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) :
    simulateQ (prescribedLocal prims D hash hidden)
      (advance (treeSimPeerProgram K ctx idx count value st k).run) =
      pure (treeSimPeerStep K ctx bitCodec
        (prescribedValue prims D hash hidden (prssDraw ctx (bitCodec (E := E)) st.label idx count))
        value count st k) := by
  rw [peer_program_interpret, prescribedLocal_ro, map_pure]

theorem coin_program_prescribed (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (ctx : Context C) (count : ℕ) (st : RunState C)
    (k : List E × RunState C → PartyM C E RealSpec TreeOutput) :
    simulateQ (prescribedLocal prims D hash hidden)
      (advance ((((realCheckGadgets K ctx).coin count).run st >>= k).run)) =
      pure (treeSimCoinStep K ctx
        (prescribedValue prims D hash hidden (prssDraw ctx (elementCodec K) st.label 1 count))
        count st k) := by
  let impl := prescribedLocal prims D hash hidden
  let program : QueryImpl (ProgramSpec C) ProbComp := fun _ => pure false
  let world : QueryImpl (WorldSpec C) ProbComp := (impl + program) + impl
  have interpreted := congrArg (simulateQ world) (treeSim_coin_entry K ctx count st k)
  simp only [world, worldRoles, simulateQ_free, simulateQ_map] at interpreted
  rw [interpreted, prescribedLocal_ro, map_pure]

theorem coin_entries_prescribed (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (ctx : C.Party → Context C) (count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput) :
    simulateQ (prescribedLocal prims D hash hidden)
      (Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else
        advance ((((realCheckGadgets K (ctx i)).coin count).run (st i) >>= k i).run)) =
      pure (maskedSteps D (fun i => treeSimCoinStep K (ctx i)
        (prescribedValue prims D hash hidden (prssDraw (ctx i) (elementCodec K) (st i).label 1 count))
        count (st i) (k i))) := by
  rw [simulateQ_sequenceFin]
  trans Concrete.sequenceFin (fun i => pure (maskedSteps D (fun i => treeSimCoinStep K (ctx i)
    (prescribedValue prims D hash hidden (prssDraw (ctx i) (elementCodec K) (st i).label 1 count))
    count (st i) (k i)) i))
  · congr 1
    funext i
    by_cases corrupt : i ∈ D.1
    · simp only [maskedSteps, if_pos corrupt, simulateQ_pure]
    · simp only [maskedSteps, if_neg corrupt, coin_program_prescribed]
  · exact sequenceFin_pure _

/-- All entries of the actual Coin are supported from the given shared
cache; no preliminary stream draw or unlogged table installation is inserted. -/
theorem coin_entries_realize (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (ctx : C.Party → Context C) (count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (s : TreeSimState C) (initial : StreamCoherent hash hidden s.1) :
    ∃ next,
      (maskedSteps D (fun i => treeSimCoinStep K (ctx i)
        (prescribedValue prims D hash hidden (prssDraw (ctx i) (elementCodec K) (st i).label 1 count))
        count (st i) (k i)), next) ∈ support
        ((simulateQ (treeSimLoggedWorld prims D) (free (Concrete.sequenceFin fun i =>
          if i ∈ D.1 then pure (.done none) else
            advance ((((realCheckGadgets K (ctx i)).coin count).run (st i) >>= k i).run)))).run s) ∧
      StreamCoherent hash hidden next.1 := by
  apply prescribedLocal_logged_realize prims D hash hidden good _ _ s initial
  rw [coin_entries_prescribed]
  exact Set.mem_singleton _

/-- At one fixed cache boundary, a fresh hidden term supports every actual
Coin value. One fixed corrupt reply row accepts all these values. The source
kernel includes every honest party's real PRSS draw and retains the full log. -/
theorem fresh_coin_entries_all_values (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (keys : C.Party → Keys C) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput)
    (label : ℕ) (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (T₀ : C.Term) (unknown : ¬ KnownTo D.1 T₀) (s : TreeSimState C)
    (initial : StreamCoherent hash hidden s.1)
    (fresh : ∀ b : Fin elementBits, s.1.2 ((.term T₀, kT T₀), label, 1, b.val) = none) :
    let base := fun T => prescribedValue prims D hash hidden
      ((elementCodec K).draw (.term T) (kT T) label 1 1)
    let sent := fun j => coinOut K j 1 (honestR base j, 0)
    ∀ value : E, ∃ (rnd : C.Party → PrssOutput C E) (next : TreeSimState C),
      (maskedSteps D (fun i => treeSimCoinStep K (prssCtx keys kT kP i) (rnd i) 1 (st i) (k i)), next) ∈
        support ((simulateQ (treeSimLoggedWorld prims D) (free (Concrete.sequenceFin fun i =>
          if i ∈ D.1 then pure (.done none) else advance
            ((((realCheckGadgets K (prssCtx keys kT kP i)).coin 1).run (st i) >>= k i).run)))).run s) ∧
      (∀ j, j ∈ D.1 → coinOut K j 1 (rnd j) = sent j) ∧
      ∀ i, i ∉ D.1 → treeSimCoinOutput K D 1 rnd sent i = some [value] := by
  let rr := fun h T => prescribedValue prims D hash h
    ((elementCodec K).draw (.term T) (kT T) label 1 1)
  let zz := fun h p => prescribedValue prims D hash h
    ((elementCodec K).draw (.pair p) (kP p) label 1 1)
  dsimp only
  intro value
  let chosen := value - ∑ T ∈ Finset.univ.erase T₀, rr hidden T 0
  let patch := replaceHiddenBlock (.term T₀) (kT T₀) label 1 (K.encode chosen) hidden
  let rnd := fun i => (honestR (rr patch) i, honestZ (zz patch) i)
  have other T (different : T ≠ T₀) : rr patch T = rr hidden T := by
    apply prescribedValue_element_other K prims D hash hidden
      (.term T₀) (kT T₀) label 1 (K.encode chosen) (.term T)
    exact fun eq => different (KeyName.term.inj eq)
  have selected : rr patch T₀ 0 = chosen := by
    apply prescribedValue_element_zero K prims D hash patch (.term T₀) unknown (kT T₀) label 1 chosen
    exact replaceHiddenBlock_at (.term T₀) (kT T₀) label 1 (K.encode chosen) hidden
  have sum : ∑ T, rr patch T 0 = value := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T₀), selected]
    have rest : (∑ T ∈ Finset.univ.erase T₀, rr patch T 0) =
        ∑ T ∈ Finset.univ.erase T₀, rr hidden T 0 :=
      Finset.sum_congr rfl fun T hT => congrFun (other T (Finset.mem_erase.mp hT).1) 0
    rw [rest]
    exact sub_add_cancel _ _
  have coherent : StreamCoherent hash patch s.1 :=
    ⟨initial.1, replaceHiddenBlock_agrees (.term T₀) (kT T₀) label 1 (K.encode chosen)
      hidden s.1.2 initial.2 fresh⟩
  obtain ⟨next, actual, _⟩ := coin_entries_realize K prims D hash patch good
    (prssCtx keys kT kP) 1 st k s coherent
  have drawn i : prescribedValue prims D hash patch
      (prssDraw (prssCtx keys kT kP i) (elementCodec K) (st i).label 1 1) = rnd i := by
    rw [labels i]
    exact prescribedValue_prssDraw prims D hash patch keys kT kP i (elementCodec K) label 1 1
  simp_rw [drawn] at actual
  have corrupt j (corrupt : j ∈ D.1) : coinOut K j 1 (rnd j) =
      coinOut K j 1 (honestR (rr hidden) j, 0) := by
    have common : honestR (rr patch) j = honestR (rr hidden) j := by
      funext T g
      by_cases held : j ∈ C.holders T
      · have different : T ≠ T₀ := fun eq => unknown ⟨j, corrupt, eq ▸ held⟩
        simp only [honestR, if_pos held, other T different]
      · simp only [honestR, if_neg held]
    change openOut j (conv K (localContext j) (honestR (rr patch) j)) 1 = _
    rw [common]
    rfl
  refine ⟨rnd, next, actual, corrupt, ?_⟩
  intro i honest
  unfold treeSimCoinOutput
  rw [if_neg honest]
  have inbox : (fun j => if j ∈ D.1 then coinOut K j 1 (honestR (rr hidden) j, 0) i else
      coinOut K j 1 (rnd j) i) = fun j => coinOut K j 1 (rnd j) i := by
    funext j
    by_cases hj : j ∈ D.1
    · rw [if_pos hj, corrupt j hj]
    · rw [if_neg hj]
  rw [inbox]
  change coinRes K i 1 (honestR (rr patch) i, honestZ (zz patch) i)
    (fun j => coinOut K j 1 (honestR (rr patch) j, honestZ (zz patch) j) i) = _
  rw [coinRes_common]
  simp only [vector, List.range_one, List.map_cons, List.map_nil, sum]

abbrev OpeningData (C : Committee) (E : Type) := (E → ℕ → E) × (ℕ × ℕ) × (List E × RunState C)

/-- The source prefix ends after the final Coin draw and opening, before
its public hash expansion and the final three-coordinate opening. -/
def checkOpeningPrefix (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    PartyM C E RealSpec (OpeningData C E) := do
  let p ← (treeLockstepCheckPrefix K ctx tuples).run st
  let coin ← ((realCheckGadgets K ctx).coin 1).run p.2
  pure (p.1, (p.2.tag, p.2.label), coin)

def checkOpeningResume (ctx : Context C) (data : OpeningData C E) :
    PartyM C E RealSpec (Unit × RunState C) :=
  treeStagesChallengeTail K data.2.1.1 data.2.1.2 (fun r => do
    let opened ← openSh K ctx (data.1 r.1) 3
    require (opened 0 * opened 1 = opened 2)
    pure ((), r.2)) data.2.2

theorem check_opening_factor (ctx : Context C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) (st : RunState C) :
    (check K ctx (realCheckGadgets K ctx) tuples).run st =
      checkOpeningPrefix K ctx tuples st >>= checkOpeningResume K ctx := by
  rw [treeLockstep_check_eq K ctx tuples nonzero, StateT.run_bind]
  simp only [checkOpeningPrefix, bind_assoc, pure_bind]
  apply bind_congr
  intro p
  simp only [treeLockstepCheckSuffix, StateT.run_bind, StateT.run_lift]
  rw [treeStages_challenge_prefix]
  apply bind_congr
  intro coin
  unfold checkOpeningResume
  congr 1
  funext result
  simp only [pure_bind, bind_assoc]

theorem checkOpeningPrefix_timed (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    TreeSimCheckTimed (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 4)
      (checkOpeningPrefix K ctx tuples st).run := by
  unfold checkOpeningPrefix
  convert (treeLockstep_checkPrefix_timed K ctx tuples st).bind (fun p =>
    (treeLockstep_timed_coin K ctx 1 p.2).bind (fun coin => TreeSimCheckTimed.done (p.1, (p.2.tag, p.2.label), coin))) using 1
  first | omega | rfl

theorem checkOpeningResume_exchange (ctx : Context C) (data : OpeningData C E) :
    TreeSimCheckExchange (checkOpeningResume K ctx data) := by
  unfold checkOpeningResume treeStagesChallengeTail
  apply TreeSimCheckExchange.oracle_bind
  intro key
  apply TreeSimCheckExchange.oracle_bind
  intro result
  cases result with
  | none =>
    intro step run
    change step ∈ support (pure (.done none) : OracleComp (LocalSpec C) (Step C E RealSpec _)) at run
    simp only [support_pure, Set.mem_singleton_iff] at run
    subst step
    rfl
  | some value =>
    unfold openSh
    simp only [bind_assoc]
    exact TreeSimCheckExchange.exchange_bind _ _

theorem timed_require {α : Type} (n : ℕ) (p : Prop)
    (k : Unit → PartyM C E RealSpec α) (timed : ∀ u, TreeSimCheckTimed n (k u).run) :
    TreeSimCheckTimed n (require p >>= k).run := by
  unfold require
  split_ifs
  · simpa only [pure_bind] using timed ()
  · exact .abort n

theorem prssSetup_timed (i : C.Party) :
    TreeSimCheckTimed 3 (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run := by
  rw [prssSetup_eq]
  apply TreeSimCheckTimed.local_bind 2
  intro own
  rw [commitRevealEcho_eq]
  simp only [bind_assoc, pure_bind]
  apply TreeSimCheckTimed.oracle_bind 2
  intro commitments
  apply TreeSimCheckTimed.exchange_bind 2
  intro committed
  apply TreeSimCheckTimed.exchange_bind 1
  intro revealed
  apply TreeSimCheckTimed.oracle_bind 0
  intro opened
  apply timed_require 1
  intro _
  apply TreeSimCheckTimed.oracle_bind 0
  intro keys
  apply TreeSimCheckTimed.oracle_bind 0
  intro shared
  apply TreeSimCheckTimed.exchange_bind 0
  intro received
  apply timed_require 0
  intro _
  exact .done _

/-- The ceremony's retained source execution is exactly the original
post-setup trace. No output projection discards its pending programs. -/
theorem ceremony_retained_trace (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (state : A.State) (fuel : ℕ) :
    simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => ceremony K circuits settings i (x i) top tree) >>= fun steps =>
        executeSteps worldRoles D A noFunctionality (fuel + 3) state steps) =
      treeStagesTrace prims K circuits settings top tree D A x state fuel := by
  change simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree x i) >>=
        fun steps => executeSteps worldRoles D A noFunctionality (fuel + 3) state steps) = _
  rw [Nat.add_comm fuel 3]
  rw [timed_phase_steps_split D A 2 fuel state _ _ (fun i => prssSetup_timed i)]
  simp only [simulateQ_bind, simulateQ_executePhase, treeStagesTrace, treeSimContinue]
  simp only [treeLate_executeSteps_real]
  rfl

def identityAfterVerify (ctx : Context C) (z : Shares C Bit)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Unit × RunState C) : PartyM C E RealSpec TreeOutput := do
  let result ← (do
    let opened ← StateT.lift (openRep K ctx z 1)
    pure [[opened 0]] : RunM C E RealSpec (List (List Bit))).run out.2
  finish result

abbrev IdentityOpeningData (C : Committee) (E : Type) :=
  (C.Term → List Bit) × Shares C Bit × OpeningData C E

def identityBeforeOpening (ctx : Context C) (job : Job) :
    PartyM C E RealSpec (IdentityOpeningData C E) := do
  let input ← inputShares ctx job
  let z ← ((realRunGadgets K ctx .peer).rerand
    (outputShares K [Circuit.identity 1] [input]) 1).run ⟨fun _ => [], 0, 0⟩
  let data ← checkOpeningPrefix K ctx
    [⟨outputShares K [Circuit.identity 1] [input], one K, z.1, 1, .peer⟩] z.2
  pure (input, z.1, data)

set_option maxRecDepth 100000 in
theorem identity_halvings : halvings 1 = 16 := by
  have steps : halvingSteps 512 = 9 := by
    repeat' (rw [halvingSteps]; norm_num [halvedLength])
  norm_num [halvings, sliceBits, sliceWidth, sliceLength, wordBits, steps]

include K in
theorem identity_batch_cost_lt_one : checkCost E 0 1 0 < 1 := by
  have small : (2 : ℝ≥0∞) / Fintype.card E ≤ 1 := by
    rw [card_field K]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by simp)).mp
    norm_num [ENNReal.toReal_div, elementBits]
  have power : ((2 : ℝ≥0∞) / Fintype.card E) ^ challengeTries ≤ 2 / Fintype.card E :=
    pow_le_of_le_one (by positivity) small (by norm_num [challengeTries])
  calc checkCost E 0 1 0 ≤ (18 ^ 2 : ℝ≥0∞) / 2 ^ 257 +
      (7 / Fintype.card E + 17 * (2 / Fintype.card E) ^ challengeTries) := by
        convert (checkCost_le (E := E) 0 1 16 (by rw [identity_halvings])) using 1
        norm_num [checkKeys, identity_halvings, freshCost, sliceBits]
    _ ≤ (18 ^ 2 : ℝ≥0∞) / 2 ^ 257 + (7 / Fintype.card E + 17 * (2 / Fintype.card E)) :=
      add_le_add le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left power (by positivity)))
    _ < 1 := by
      rw [card_field K]
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, elementBits]
      have denominator : (512 : ℝ) ≤ 2 ^ 257 := by
        calc (512 : ℝ) = 2 ^ 9 := by norm_num
          _ ≤ 2 ^ 257 := by gcongr <;> norm_num
      have first := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 324)
        (by norm_num : (0 : ℝ) < 512) denominator
      exact lt_of_le_of_lt (add_le_add first le_rfl) (by norm_num)

def identityBatch (ctx : Context C) (job : Job) :
    PartyM C E RealSpec (List (List Bit) × RunState C) := do
  let input ← inputShares ctx job
  (runJobs K (realRunGadgets K ctx .peer) [Circuit.identity 1] [input]).run ⟨fun _ => [], 0, 0⟩

/-- The actual honest first identity batch, including its real PRSS
rerandomization, check and output opening, has abort probability below one. -/
theorem identityBatch_failure_le (prims : Primitives)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s) :
    Pr[fun out => ¬ ∀ i, (out i).isSome |
      (simulateQ (localAnswer prims)
        (honestStart (fun i => identityBatch K (prssCtx (dealtKeys parameter seeds pairs) kT kP i) job) >>=
          honestRounds noFunctionality PEmpty.elim 39)).run' s] ≤ checkCost E 0 1 0 := by
  haveI : Nonempty C.Party := ⟨(prss_exists_honest (noCoalition : C.Coalition)).choose⟩
  have bound := batch_step prims K noFunctionality PEmpty.elim .peer
    (fun _ _ => Circuit.identity 1) parameter seeds pairs kT kP [job]
    0 0 0 0 ∅ le_rfl (by simp) s noMpc coinsFresh 0
    (fun _ result => pure result) (fun out => ¬ ∀ i, (out i).isSome) 0
    (by intro outs hist keys cache _ _ _ _ _; simp [honestRounds_pure])
  have hd : depth [Circuit.identity 1] = 0 := rfl
  have ht : tupleCount [Circuit.identity 1] = 1 := rfl
  simpa only [identityBatch, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    pure_bind, bind_assoc, bind_pure, hd, ht, checkLabels, show (1 : ℕ) ≠ 0 by omega,
    ite_false, identity_halvings, Finset.card_empty, zero_mul, zero_add, add_zero] using bound

/-- There is a genuinely supported successful honest identity batch;
this is an existence result for the original real source program. -/
theorem identityBatch_success_supported (prims : Primitives)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s) :
    ∃ out, out ∈ support ((simulateQ (localAnswer prims)
      (honestStart (fun i => identityBatch K (prssCtx (dealtKeys parameter seeds pairs) kT kP i) job) >>=
        honestRounds noFunctionality PEmpty.elim 39)).run' s) ∧ ∀ i, (out i).isSome := by
  have bound := identityBatch_failure_le K prims parameter seeds pairs kT kP job s noMpc coinsFresh
  by_contra absent
  push Not at absent
  have full : Pr[fun out => ¬ ∀ i, (out i).isSome |
      (simulateQ (localAnswer prims)
        (honestStart (fun i => identityBatch K (prssCtx (dealtKeys parameter seeds pairs) kT kP i) job) >>=
          honestRounds noFunctionality PEmpty.elim 39)).run' s] = 1 :=
    probEvent_eq_one_iff.mpr ⟨by simp, fun out supported => by simpa using absent out supported⟩
  rw [full] at bound
  exact (not_le_of_gt (identity_batch_cost_lt_one K)) bound

set_option maxRecDepth 100000 in
theorem identity_check_opening_rounds :
    2 * sliceBits + 2 * (halvings 1 - sliceBits) + 4 = 36 := by
  have steps : halvingSteps 512 = 9 := by
    repeat' (rw [halvingSteps]; norm_num [halvedLength])
  norm_num [halvings, sliceBits, sliceWidth, sliceLength, wordBits, steps]

theorem identityBeforeOpening_timed (ctx : Context C) (job : Job) :
    TreeSimCheckTimed 37 (identityBeforeOpening K ctx job).run := by
  unfold identityBeforeOpening
  rw [inputShares_fun]
  apply TreeSimCheckTimed.oracle_bind 36
  intro input
  have after (z : Shares C Bit × RunState C) : TreeSimCheckTimed 36 ((do
      let data ← checkOpeningPrefix K ctx
        [⟨outputShares K [Circuit.identity 1] [input], one K, z.1, 1, .peer⟩] z.2
      pure (input, z.1, data) : PartyM C E RealSpec (IdentityOpeningData C E)).run) := by
    have timed := (checkOpeningPrefix_timed K ctx
      [⟨outputShares K [Circuit.identity 1] [input], one K, z.1, 1, .peer⟩] z.2).bind
      (n := 0) (k := fun data => (pure (input, z.1, data) : PartyM C E RealSpec (IdentityOpeningData C E)))
      (fun _ => .done _)
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, identity_check_opening_rounds] using timed
  exact (treeSimCheckTimed_rerand K ctx .peer
    (outputShares K [Circuit.identity 1] [input]) 1 ⟨fun _ => [], 0, 0⟩).bind after

def identityBatchOpeningResume (ctx : Context C) (data : IdentityOpeningData C E) :
    PartyM C E RealSpec (List (List Bit) × RunState C) := do
  let checked ← checkOpeningResume K ctx data.2.2
  let opened ← openRep K ctx data.2.1 1
  pure ([[opened 0]], checked.2)

theorem identityBatch_opening_factor (ctx : Context C) (job : Job) :
    identityBatch K ctx job = identityBeforeOpening K ctx job >>= identityBatchOpeningResume K ctx := by
  simp only [identityBatch, identityBeforeOpening, bind_assoc, pure_bind]
  apply bind_congr
  intro input
  rw [identity_one_run]
  simp only [StateT.run_bind]
  apply bind_congr
  intro z
  simp only [realRunGadgets]
  rw [check_opening_factor K ctx _ (by simp)]
  simp only [bind_assoc]
  apply bind_congr
  intro data
  unfold identityBatchOpeningResume
  apply bind_congr
  intro checked
  simp only [StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]

theorem identityBatchOpeningResume_exchange (ctx : Context C) (data : IdentityOpeningData C E) :
    TreeSimCheckExchange (identityBatchOpeningResume K ctx data) :=
  (checkOpeningResume_exchange K ctx data.2.2).bind _

/-- The actual honest identity batch reaches its pre-final-opening cut
successfully under one coherent prescribed public hash and hidden table. -/
theorem identityBeforeOpening_success_prescribed (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s) :
    ∃ (hash : Query C → HashOutput) (pref : C.Party → Option (IdentityOpeningData C E)),
      Good prims hash ∧ Agrees hash s ∧
      pref ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (honestStart (fun i => identityBeforeOpening K
          (prssCtx (dealtKeys parameter seeds pairs) kT kP i) job) >>=
            honestRounds noFunctionality PEmpty.elim 37)) ∧ ∀ i, (pref i).isSome := by
  obtain ⟨out, supported, success⟩ := identityBatch_success_supported K prims
    parameter seeds pairs kT kP job s noMpc coinsFresh
  rw [StateT.run'_eq, support_map] at supported
  obtain ⟨result, actual, same⟩ := supported
  obtain ⟨hash, good, initial, _, prescribed⟩ := localRun_prescribed prims D _ s noMpc result actual
  change result.1 = out at same
  have allSome : ∀ i, (result.1 i).isSome := by rw [same]; exact success
  simp only [identityBatch_opening_factor] at prescribed
  obtain ⟨pref, prefixRun, live⟩ := honest_timed_prefix_supported
    (prescribedLocal prims D hash (aesHidden prims hash)) 36 2
    (fun i => identityBeforeOpening K (prssCtx (dealtKeys parameter seeds pairs) kT kP i) job)
    (fun i => identityBatchOpeningResume K (prssCtx (dealtKeys parameter seeds pairs) kT kP i))
    (fun i => identityBeforeOpening_timed K _ job)
    (fun i data => identityBatchOpeningResume_exchange K _ data) result.1 prescribed allSome
  exact ⟨hash, pref, good, initial, prefixRun, live⟩

def ceremonyBeforeOpening (job : Job) (i : C.Party) (keys : Keys C) :
    PartyM C E RealSpec (Context C × IdentityOpeningData C E) := do
  let prss ← prssSetup i
  let ctx : Context C := ⟨i, keys, prss⟩
  let data ← identityBeforeOpening K ctx job
  pure (ctx, data)

def ceremonyOpeningResume
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (data : Context C × IdentityOpeningData C E) : PartyM C E RealSpec TreeOutput :=
  checkOpeningResume K data.1 data.2.2.2 >>=
    identityAfterVerify K data.1 data.2.2.1 (finish data.1)

theorem ceremonyBeforeOpening_timed (job : Job) (i : C.Party) (keys : Keys C) :
    TreeSimCheckTimed 40 (ceremonyBeforeOpening K job i keys).run := by
  unfold ceremonyBeforeOpening
  apply (prssSetup_timed i).bind (n := 37)
  intro prss
  apply (identityBeforeOpening_timed K ⟨i, keys, prss⟩ job).bind (n := 0)
  intro data
  exact .done _

theorem ceremonyOpeningResume_exchange
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (data : Context C × IdentityOpeningData C E) : TreeSimCheckExchange (ceremonyOpeningResume K finish data) :=
  (checkOpeningResume_exchange K data.1 data.2.2.2).bind _

theorem challengeTail_bind {α β : Type} (tag label : ℕ)
    (body : E × RunState C → PartyM C E RealSpec α)
    (data : List E × RunState C) (k : α → PartyM C E RealSpec β) :
    treeStagesChallengeTail K tag label body data >>= k =
      treeStagesChallengeTail K tag label (fun r => body r >>= k) data := by
  unfold treeStagesChallengeTail
  simp only [bind_assoc]
  apply bind_congr
  intro key
  apply bind_congr
  intro value
  cases value <;> rfl

/-- A live entry after the source challenge tail has an accepted nonzero
challenge, with the actual continuation selected by that challenge. -/
theorem challengeTail_live_entry {α : Type} (impl : QueryImpl (LocalSpec C) ProbComp)
    (tag label : ℕ) (data : List E × RunState C)
    (body : E × RunState C → PartyM C E RealSpec α)
    (entries : E → Step C E RealSpec α)
    (entry : ∀ r, advance (body (r, data.2)).run = pure (entries r))
    (step : Step C E RealSpec α)
    (run : step ∈ support (simulateQ impl
      (advance (treeStagesChallengeTail K tag label body data).run)))
    (live : ¬ step.isDone) :
    ∃ r, r ≠ 0 ∧ r ≠ 1 ∧ step = entries r := by
  let program : QueryImpl (ProgramSpec C) ProbComp := fun _ => pure false
  let world : QueryImpl (WorldSpec C) ProbComp := (impl + program) + impl
  have factor := congrArg (simulateQ world)
    (treeStages_challenge_tail_factor K tag label data.1 data.2 body)
  simp only [world, simulateQ_bind, simulateQ_free] at factor
  rw [factor, mem_support_bind_iff] at run
  obtain ⟨value, challenge, resumed⟩ := run
  cases value with
  | none =>
    have absent : step = .done none := by
      simpa only [treeSimResume, simulateQ_pure, support_pure, Set.mem_singleton_iff] using resumed
    exact (live (absent ▸ trivial)).elim
  | some r =>
    have accepted := challengeQuery_support K tag label data.1 (some r)
      (simulated_source_support impl _ challenge) r rfl
    have equal : step = entries r := by
      simpa only [treeSimResume, entry, simulateQ_pure, support_pure, Set.mem_singleton_iff] using resumed
    exact ⟨r, accepted.1, accepted.2, equal⟩

theorem ceremonyOpeningResume_live_entry (impl : QueryImpl (LocalSpec C) ProbComp)
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (data : Context C × IdentityOpeningData C E) (step : Step C E RealSpec TreeOutput)
    (run : step ∈ support (simulateQ impl (advance (ceremonyOpeningResume K finish data).run)))
    (live : ¬ step.isDone) :
    ∃ r, r ≠ 0 ∧ r ≠ 1 ∧ step =
      treeSimCheckStep K (.opening (fun _ => data.2.2.2.1 r)) data.1.self
        (identityAfterVerify K data.1 data.2.2.1 (finish data.1) ((), data.2.2.2.2.2.2)) := by
  unfold ceremonyOpeningResume checkOpeningResume at run
  rw [challengeTail_bind] at run
  apply challengeTail_live_entry K impl data.2.2.2.2.1.1 data.2.2.2.2.1.2 data.2.2.2.2.2
    _ _ (fun r => ?_) step run live
  simp only [bind_assoc, pure_bind]
  exact treeSim_check_open_entry K data.1 (data.2.2.2.1 r) _

theorem ceremonyOpeningResume_factor
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (data : Context C × IdentityOpeningData C E) :
    ceremonyOpeningResume K finish data =
      identityBatchOpeningResume K data.1 data.2 >>= finish data.1 := by
  simp only [ceremonyOpeningResume, identityBatchOpeningResume, bind_assoc, pure_bind]
  apply bind_congr
  intro checked
  simp only [identityAfterVerify, StateT.run_bind, StateT.run_lift, StateT.run_pure,
    bind_assoc, pure_bind]

def ceremonyIdentityBatch (job : Job) (i : C.Party) (keys : Keys C) :
    PartyM C E RealSpec (List (List Bit) × RunState C) := do
  let prss ← prssSetup i
  identityBatch K ⟨i, keys, prss⟩ job

theorem ceremonyIdentityBatch_factor (job : Job) (i : C.Party) (keys : Keys C) :
    ceremonyIdentityBatch K job i keys = ceremonyBeforeOpening K job i keys >>=
      (fun data => identityBatchOpeningResume K data.1 data.2) := by
  simp only [ceremonyIdentityBatch, ceremonyBeforeOpening, identityBatch_opening_factor,
    bind_assoc, pure_bind]

theorem ceremonyIdentityBatch_failure_le (prims : Primitives)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s) :
    Pr[fun out => ¬ ∀ i, (out i).isSome |
      (simulateQ (localAnswer prims)
        (honestStart (fun i => ceremonyIdentityBatch K job i (dealtKeys parameter seeds pairs i)) >>=
          honestRounds noFunctionality PEmpty.elim 42)).run' s] ≤ checkCost E 0 1 0 := by
  haveI : Nonempty C.Party := ⟨(prss_exists_honest (noCoalition : C.Coalition)).choose⟩
  unfold ceremonyIdentityBatch
  apply setup_step prims noFunctionality PEmpty.elim 39 _ _ s noMpc
  intro kT kP next nextNoMpc _ frame
  exact identityBatch_failure_le K prims parameter seeds pairs kT kP job next nextNoMpc
    (cacheOK_of_frame coinsFresh frame)

/-- Actual setup and the first complete identity batch have a supported
successful run, with the public hash still agreeing with the initial cache. -/
theorem ceremonyBeforeOpening_success_prescribed (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s) :
    ∃ (hash : Query C → HashOutput)
      (pref : C.Party → Option (Context C × IdentityOpeningData C E)),
      Good prims hash ∧ Agrees hash s ∧
      pref ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (honestStart (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) >>=
          honestRounds noFunctionality PEmpty.elim 40)) ∧ ∀ i, (pref i).isSome := by
  have bound := ceremonyIdentityBatch_failure_le K prims parameter seeds pairs job s noMpc coinsFresh
  have success : ∃ out, out ∈ support ((simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyIdentityBatch K job i (dealtKeys parameter seeds pairs i)) >>=
        honestRounds noFunctionality PEmpty.elim 42)).run' s) ∧ ∀ i, (out i).isSome := by
    by_contra absent
    push Not at absent
    have full : Pr[fun out => ¬ ∀ i, (out i).isSome |
        (simulateQ (localAnswer prims)
          (honestStart (fun i => ceremonyIdentityBatch K job i (dealtKeys parameter seeds pairs i)) >>=
            honestRounds noFunctionality PEmpty.elim 42)).run' s] = 1 :=
      probEvent_eq_one_iff.mpr ⟨by simp, fun out supported => by simpa using absent out supported⟩
    rw [full] at bound
    exact (not_le_of_gt (identity_batch_cost_lt_one K)) bound
  obtain ⟨out, supported, allSome⟩ := success
  rw [StateT.run'_eq, support_map] at supported
  obtain ⟨result, actual, same⟩ := supported
  change result.1 = out at same
  obtain ⟨hash, good, initial, _, prescribed⟩ := localRun_prescribed prims D _ s noMpc result actual
  have resultSome : ∀ i, (result.1 i).isSome := by rw [same]; exact allSome
  simp only [ceremonyIdentityBatch_factor] at prescribed
  obtain ⟨pref, prefixRun, live⟩ := honest_timed_prefix_supported
    (prescribedLocal prims D hash (aesHidden prims hash)) 39 2
    (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i))
    (fun _ data => identityBatchOpeningResume K data.1 data.2)
    (fun i => ceremonyBeforeOpening_timed K job i _)
    (fun _ data => identityBatchOpeningResume_exchange K data.1 data.2) result.1 prescribed resultSome
  exact ⟨hash, pref, good, initial, prefixRun, live⟩

/-- The successful prefix and its live final-opening entries use one
prescribed table, obtained from an actual complete honest batch. -/
theorem ceremonyBeforeOpening_live_prescribed (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s)
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    ∃ (hash : Query C → HashOutput)
      (pref : C.Party → Option (Context C × IdentityOpeningData C E))
      (next : C.Party → Step C E RealSpec TreeOutput),
      Good prims hash ∧ Agrees hash s ∧
      pref ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (honestStart (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) >>=
          honestRounds noFunctionality PEmpty.elim 40)) ∧ (∀ i, (pref i).isSome) ∧
      next ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (Concrete.sequenceFin fun i => continueStep (ceremonyOpeningResume K finish) (.done (pref i)))) ∧
      ∀ i, ¬ (next i).isDone := by
  have bound := ceremonyIdentityBatch_failure_le K prims parameter seeds pairs job s noMpc coinsFresh
  have success : ∃ out, out ∈ support ((simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyIdentityBatch K job i (dealtKeys parameter seeds pairs i)) >>=
        honestRounds noFunctionality PEmpty.elim 42)).run' s) ∧ ∀ i, (out i).isSome := by
    by_contra absent
    push Not at absent
    have full : Pr[fun out => ¬ ∀ i, (out i).isSome |
        (simulateQ (localAnswer prims)
          (honestStart (fun i => ceremonyIdentityBatch K job i (dealtKeys parameter seeds pairs i)) >>=
            honestRounds noFunctionality PEmpty.elim 42)).run' s] = 1 :=
      probEvent_eq_one_iff.mpr ⟨by simp, fun out supported => by simpa using absent out supported⟩
    rw [full] at bound
    exact (not_le_of_gt (identity_batch_cost_lt_one K)) bound
  obtain ⟨out, supported, allSome⟩ := success
  rw [StateT.run'_eq, support_map] at supported
  obtain ⟨result, actual, same⟩ := supported
  change result.1 = out at same
  obtain ⟨hash, good, initial, _, prescribed⟩ := localRun_prescribed prims D _ s noMpc result actual
  have resultSome : ∀ i, (result.1 i).isSome := by rw [same]; exact allSome
  simp only [ceremonyIdentityBatch_factor] at prescribed
  obtain ⟨pref, next, prefixRun, live, entries, active⟩ := honest_timed_prefix_live_supported
    (prescribedLocal prims D hash (aesHidden prims hash)) 39 2
    (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i))
    (fun _ data => identityBatchOpeningResume K data.1 data.2)
    (fun i => ceremonyBeforeOpening_timed K job i _)
    (fun _ data => identityBatchOpeningResume_exchange K data.1 data.2) result.1 prescribed resultSome
  obtain ⟨next', actualEntries, active'⟩ := live_continuations_attach
    (prescribedLocal prims D hash (aesHidden prims hash)) pref live
    (fun _ data => identityBatchOpeningResume K data.1 data.2)
    (fun _ data => finish data.1) next entries active
  refine ⟨hash, pref, next', good, initial, prefixRun, live, ?_, active'⟩
  have factor : ceremonyOpeningResume K finish = fun data =>
      identityBatchOpeningResume K data.1 data.2 >>= finish data.1 :=
    funext (ceremonyOpeningResume_factor K finish)
  rw [factor]
  exact actualEntries

/-- The corrupt recorder actually completes setup and the identity prefix,
from an empty hidden cache, while keeping its first final-opening abort row.
Every honest prefix result is present in this logged run. -/
theorem ceremonyBeforeOpening_success_logged (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (job : Job)
    (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s) (log : TreeSimLog C) :
    ∃ (hash : Query C → HashOutput)
      (pref : C.Party → Option (Context C × IdentityOpeningData C E))
      (sent : ℕ → C.Party → Mail C E) (views : List (C.Party → Mail C E)) (next : TreeSimState C),
      Good prims hash ∧ Agrees hash s ∧ (∀ i, (pref i).isSome) ∧
      sent 40 = (fun _ _ => some .abort) ∧
      (((40, views), (fun i => if i ∈ D.1 then none else pref i)), next) ∈ support
        ((executePhase (treeSimRealRoles prims D) D (recordingReplay sent) noFunctionality 40 (0, [])
          (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i))).run ((s, ∅), log)) ∧
      StreamCoherent hash (aesHidden prims hash) next.1 := by
  obtain ⟨hash, pref, good, initial, run, live⟩ := ceremonyBeforeOpening_success_prescribed K prims D
    parameter seeds pairs job s noMpc coinsFresh
  have coherent : StreamCoherent hash (aesHidden prims hash) (s, ∅) := by
    refine ⟨initial, ?_⟩
    intro x value found
    simp at found
  obtain ⟨sent, views, next, outside, actual, finalCoherent⟩ := recordingReplay_honest_timed_phase_realize
    prims D hash (aesHidden prims hash) good 40
    (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) pref
    (fun i => ceremonyBeforeOpening_timed K job i _) run live (0, []) (fun _ _ _ => some .abort)
    ((s, ∅), log) coherent
  exact ⟨hash, pref, sent, views, next, good, initial, live,
    outside 40 (Or.inr le_rfl), actual, finalCoherent⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The actual identity ceremony has exactly 40 exchanges before its first
final opening. The saved continuation contains the final test, OpenRep and
all remaining top-tree jobs. -/
theorem ceremony_identity_opening_factor (top : TopTree) :
    ∃ (job : Job) (point : Point)
      (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput),
      job.points = [point] ∧ ∀ i keys,
      (ceremony K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ i keys top .top : PartyM C E RealSpec TreeOutput) =
        ceremonyBeforeOpening K job i keys >>= ceremonyOpeningResume K finish := by
  obtain ⟨job, jobs, point, head, points⟩ := SeedHitProof.topJobs_head
  choose finish source using fun ctx =>
    top_firstBatch_factor_head K ctx (fun _ _ => Circuit.identity 1) top job jobs head
  refine ⟨job, point, finish, points, ?_⟩
  intro i keys
  rw [ceremony_eq_prssSetup_bind]
  simp only [ceremonyBeforeOpening, bind_assoc, pure_bind]
  apply bind_congr
  intro prss
  rw [source]
  simp only [identityBeforeOpening, bind_assoc, pure_bind]
  apply bind_congr
  intro input
  rw [identity_one_run]
  simp only [StateT.run_bind, bind_assoc]
  apply bind_congr
  intro z
  simp only [realRunGadgets]
  rw [check_opening_factor K _ _ (by simp)]
  simp only [bind_assoc]
  apply bind_congr
  intro data
  simp only [ceremonyOpeningResume]
  apply bind_congr
  intro checked
  simp only [identityAfterVerify, StateT.run_bind, bind_assoc]

/-- A supported 40-round identity prefix and its actual continuation
entries form the original retained trace at post-setup fuel 37. -/
theorem identity_opening_reach (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (top : TopTree) (x : C.Party → Keys C)
    (job : Job)
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (factor : ∀ i keys,
      (ceremony K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ i keys top .top : PartyM C E RealSpec TreeOutput) =
        ceremonyBeforeOpening K job i keys >>= ceremonyOpeningResume K finish)
    (state : A.State) (s : TreeSimState C)
    (p : (A.State × (C.Party → Option (Context C × IdentityOpeningData C E))) × TreeSimState C)
    (hp : p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 40 state
      (fun i => ceremonyBeforeOpening K job i (x i))).run s))
    (q : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (hq : q ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (Concrete.sequenceFin fun i => continueStep (ceremonyOpeningResume K finish)
        (.done (p.1.2 i))))).run p.2)) :
    TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D A x state s 37
      ((p.1.1, q.1), q.2) := by
  unfold TreeStagesReach
  rw [← ceremony_retained_trace]
  simp only [factor]
  rw [timed_phase_steps_split D A 39 0 state _ _ (fun i => ceremonyBeforeOpening_timed K job i (x i))]
  simp only [simulateQ_bind, simulateQ_executePhase, executeSteps, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  exact ⟨p, hp, q, hq, rfl⟩

/-- An actual logged identity ceremony reaches live final-opening
programs with a fixed corrupt recorder, whose very next row aborts.
The retained witness includes setup, both caches and the complete log. -/
theorem recordingReplay_identity_finalOpening_shaped (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (top : TopTree) (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s)
    (log : TreeSimLog C) :
    ∃ (hash : Query C → HashOutput) (sent : ℕ → C.Party → Mail C E)
      (views : List (C.Party → Mail C E)) (steps : C.Party → Step C E RealSpec TreeOutput)
      (next : TreeSimState C)
      (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput),
      Good prims hash ∧ Agrees hash s ∧ sent 40 = (fun _ _ => some .abort) ∧
      TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
        (dealtKeys parameter seeds pairs) (0, []) ((s, ∅), log) 37 (((40, views), steps), next) ∧
      StreamCoherent hash (aesHidden prims hash) next.1 ∧
      (∀ i, i ∈ D.1 → steps i = .done none) ∧ (∀ i, i ∉ D.1 → ¬ (steps i).isDone) ∧
      ∀ i, i ∉ D.1 → ∃ (data : Context C × IdentityOpeningData C E) (r : E),
        r ≠ 0 ∧ r ≠ 1 ∧ steps i =
          treeSimCheckStep K (.opening (fun _ => data.2.2.2.1 r)) data.1.self
            (identityAfterVerify K data.1 data.2.2.1 (finish data.1) ((), data.2.2.2.2.2.2)) := by
  obtain ⟨job, point, finish, _, factor⟩ := ceremony_identity_opening_factor K top
  obtain ⟨hash, pref, entries, good, initial, run, live, entryRun, active⟩ :=
    ceremonyBeforeOpening_live_prescribed K prims D parameter seeds pairs job s noMpc coinsFresh finish
  have coherent : StreamCoherent hash (aesHidden prims hash) (s, ∅) := by
    refine ⟨initial, ?_⟩
    intro x value found
    simp at found
  obtain ⟨sent, views, boundary, outside, prefixRun, boundaryCoherent⟩ :=
    recordingReplay_honest_timed_phase_realize prims D hash (aesHidden prims hash) good 40
      (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) pref
      (fun i => ceremonyBeforeOpening_timed K job i _) run live (0, []) (fun _ _ _ => some .abort)
      ((s, ∅), log) coherent
  let outputs := fun i => if i ∈ D.1 then none else pref i
  let continuation := Concrete.sequenceFin fun i =>
    continueStep (ceremonyOpeningResume K finish) (.done (outputs i))
  have maskedRun : maskedSteps D entries ∈ support
      (simulateQ (prescribedLocal prims D hash (aesHidden prims hash)) continuation) := by
    rw [simulateQ_sequenceFin] at entryRun
    have each := mem_support_sequenceFin _ _ entryRun
    simp only [continuation, simulateQ_sequenceFin]
    apply sequenceFin_support_of_each
    intro i
    by_cases corrupt : i ∈ D.1
    · simp only [outputs, maskedSteps, if_pos corrupt, continueStep, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
    · simpa only [outputs, maskedSteps, if_neg corrupt] using each i
  obtain ⟨next, actualEntries, finalCoherent⟩ := prescribedLocal_logged_realize prims D hash
    (aesHidden prims hash) good continuation (maskedSteps D entries) boundary boundaryCoherent maskedRun
  refine ⟨hash, sent, views, maskedSteps D entries, next, finish, good, initial,
    outside 40 (Or.inr le_rfl), ?_, finalCoherent, ?_, ?_, ?_⟩
  · exact identity_opening_reach K prims D (recordingReplay sent) top (dealtKeys parameter seeds pairs)
      job finish factor (0, []) ((s, ∅), log) (((40, views), outputs), boundary) prefixRun
      (maskedSteps D entries, next) actualEntries
  · intro i corrupt
    simp only [maskedSteps, if_pos corrupt]
  · intro i honest
    simpa only [maskedSteps, if_neg honest] using active i
  · intro i honest
    obtain ⟨data, present⟩ := Option.isSome_iff_exists.mp (live i)
    rw [simulateQ_sequenceFin] at entryRun
    have each := mem_support_sequenceFin _ _ entryRun i
    simp only [present, continueStep] at each
    obtain ⟨r, nonzero, notOne, shape⟩ := ceremonyOpeningResume_live_entry K
      (prescribedLocal prims D hash (aesHidden prims hash)) finish data (entries i) each (active i)
    exact ⟨data, r, nonzero, notOne, by simpa only [maskedSteps, if_neg honest] using shape⟩

/-- The shaped source witness in particular supplies live retained
reachability with a fixed abort at the next round. -/
theorem recordingReplay_identity_finalOpening_reached (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (top : TopTree) (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s)
    (log : TreeSimLog C) :
    ∃ (hash : Query C → HashOutput) (sent : ℕ → C.Party → Mail C E)
      (views : List (C.Party → Mail C E)) (steps : C.Party → Step C E RealSpec TreeOutput)
      (next : TreeSimState C),
      Good prims hash ∧ Agrees hash s ∧ sent 40 = (fun _ _ => some .abort) ∧
      TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
        (dealtKeys parameter seeds pairs) (0, []) ((s, ∅), log) 37 (((40, views), steps), next) ∧
      StreamCoherent hash (aesHidden prims hash) next.1 ∧
      (∀ i, i ∈ D.1 → steps i = .done none) ∧ ∀ i, i ∉ D.1 → ¬ (steps i).isDone := by
  obtain ⟨hash, sent, views, steps, next, _, good, initial, stop, reach, coherent, empty, live, _⟩ :=
    recordingReplay_identity_finalOpening_shaped K prims D parameter seeds pairs top s noMpc coinsFresh log
  exact ⟨hash, sent, views, steps, next, good, initial, stop, reach, coherent, empty, live⟩

/-- One fixed supported trace survives every finite public padding
program on a supported padded cache. The padding and the replay use the
same table, so prefetched final challenge lookups are retained. -/
theorem recordingReplay_identity_padding_reached (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (top : TopTree) (s : HashCache C) (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s)
    (log : TreeSimLog C) :
    ∃ (hash : Query C → HashOutput) (sent : ℕ → C.Party → Mail C E)
      (views : List (C.Party → Mail C E)) (steps : C.Party → Step C E RealSpec TreeOutput),
      Good prims hash ∧ Agrees hash s ∧ sent 40 = (fun _ _ => some .abort) ∧
      (∀ i, i ∈ D.1 → steps i = .done none) ∧ (∀ i, i ∉ D.1 → ¬ (steps i).isDone) ∧
      ∀ padding : OracleComp (LocalSpec C) Unit, ∃ (pad : HashCache C) (next : TreeSimState C),
        ((), pad) ∈ support ((simulateQ (localAnswer prims) padding).run s) ∧
        TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
          (dealtKeys parameter seeds pairs) (0, []) ((pad, ∅), log) 37 (((40, views), steps), next) ∧
        StreamCoherent hash (aesHidden prims hash) next.1 := by
  obtain ⟨job, point, finish, _, factor⟩ := ceremony_identity_opening_factor K top
  obtain ⟨hash, pref, entries, good, initial, run, live, entryRun, active⟩ :=
    ceremonyBeforeOpening_live_prescribed K prims D parameter seeds pairs job s noMpc coinsFresh finish
  obtain ⟨sent, views, outside, replay⟩ := recordingReplay_timed_resume_replay prims D hash
    (aesHidden prims hash) good 39
    (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i))
    (fun _ => ceremonyOpeningResume K finish) (fun i => ceremonyBeforeOpening_timed K job i _)
    pref run live entries entryRun (0, []) (fun _ _ _ => some .abort)
  refine ⟨hash, sent, views, maskedSteps D entries, good, initial, outside 40 (Or.inr le_rfl),
    ?_, ?_, ?_⟩
  · intro i corrupt
    simp only [maskedSteps, if_pos corrupt]
  · intro i honest
    simpa only [maskedSteps, if_neg honest] using active i
  · intro padding
    obtain ⟨pad, padded, agrees⟩ := padding_coherent_supported prims hash good padding s initial
    have coherent : StreamCoherent hash (aesHidden prims hash) (pad, ∅) := by
      refine ⟨agrees, ?_⟩
      intro x value found
      simp at found
    obtain ⟨next, actual, final⟩ := replay ((pad, ∅), log) coherent
    refine ⟨pad, next, padded, ?_, final⟩
    unfold TreeStagesReach
    rw [← ceremony_retained_trace]
    simp only [factor]
    unfold recordingReplay at actual ⊢
    exact actual

/-- Aborting on the first final-opening exchange prevents all ceremony
outputs, for every input and oracle answer, including earlier abort paths. -/
theorem recordingReplay_identity_no_outputs (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (stop : sent 40 = fun _ _ => some .abort)
    (j : C.Party) (corrupt : j ∈ D.1) (top : TopTree) (x : C.Party → Keys C)
    (z : Aux) (fuel : ℕ)
    (out : (recordingReplay sent).State × (C.Party → Option TreeOutput))
    (run : out ∈ support (realExecution D (recordingReplay sent) noFunctionality fuel
      (fun i keys => (ceremony K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ i keys top .top :
        PartyM C E RealSpec TreeOutput)) x z)) : out.2 = fun _ => none := by
  obtain ⟨job, point, finish, _, factor⟩ := ceremony_identity_opening_factor K top
  have start : worldRoles.adversary ((recordingReplay sent).start (corruptInputs D x) z) =
      (pure (0, []) : OracleComp (WorldSpec C) (recordingReplay sent).State) := by
    simp only [recordingReplay, worldRoles, liftComp_pure, counted_pure]
  unfold realExecution at run
  rw [start, pure_bind] at run
  have phase : out ∈ support (executePhase worldRoles D (recordingReplay sent) noFunctionality
      fuel (0, []) (fun i => ceremonyBeforeOpening K job i (x i) >>= ceremonyOpeningResume K finish)) := by
    simpa only [factor] using run
  exact recordingReplay_timed_abort_all_fuel D sent 39 fuel (0, [])
    (fun i => ceremonyBeforeOpening K job i (x i)) (fun _ => ceremonyOpeningResume K finish)
    (fun i => ceremonyBeforeOpening_timed K job i (x i))
    (fun _ data => ceremonyOpeningResume_exchange K finish data) stop j corrupt out phase

/-- With that fixed scheduled abort, the semantic wrong-output event is
false for every log. No reachability or hash assumption is needed. -/
theorem recordingReplay_identity_not_wrong (prims : Primitives) (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (stop : sent 40 = fun _ _ => some .abort)
    (j : C.Party) (corrupt : j ∈ D.1) (top : TopTree) (x : C.Party → Keys C)
    (z : Aux) (log : TreeSimLog C) :
    ¬ TreeSimWrongOutput prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
      (recordingReplay sent) x z log := by
  rintro ⟨parameter, seeds, pairs, dealt, out, _, witness, i, _, accepted, _⟩
  obtain ⟨fuel, pref, _, _, replay⟩ := treeSimOutputWitness_replay prims K
    (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
    parameter seeds pairs z dealt out log witness
  have none := recordingReplay_identity_no_outputs K D sent stop j corrupt top
    (dealtKeys parameter seeds pairs) z fuel out replay.mem_support
  rw [none] at accepted
  cases accepted

/-- For this fixed abort recorder the original reached-good condition has
exactly two remaining events: a budget-domain hash collision or salt reuse.
Neither wrong outputs nor salt guesses require a further premise. -/
theorem recordingReplay_identity_good_iff (prims : Primitives) (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (stop : sent 40 = fun _ _ => some .abort)
    (j : C.Party) (corrupt : j ∈ D.1) (top : TopTree) (x : C.Party → Keys C) (z : Aux)
    (state : (recordingReplay sent).State) (cache : HashCache C × HiddenCache C) (fuel : ℕ)
    (a : TreeSimConfig (recordingReplay sent) (TreeSimState C))
    (reach : TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
      (recordingReplay sent) x state (cache, []) fuel a) :
    (¬ TreeSimBad3 prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
      (recordingReplay sent) x z a.2.2) ↔
      ¬ TreeSimHashBudgetCollision a.2.2 ∧ ¬ TreeSimSaltReuse D a.2.2 := by
  have wrong := recordingReplay_identity_not_wrong K prims D sent stop j corrupt top x z a.2.2
  have guess := recordingReplay_reached_not_saltGuess K prims (fun _ _ => Circuit.identity 1)
    ⟨.peer, 1⟩ top .top D sent x state cache fuel a reach
  simp only [TreeSimBad3, treeSimHashBad3_iff, wrong, guess, or_false, false_or, not_or]

/-- The actual dealer has a supported output whose public cache retains
fresh Coin domains. This uses its source frame, not an empty-cache reset. -/
theorem dealer_fresh_supported (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    ∃ (dealt : Option TreeOutput × List (List (List Bit))) (s : HashCache C),
      (dealt, s) ∈ support ((simulateQ (localAnswer prims)
        (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run ∅) ∧
      NoMpc s ∧ CacheOK ∅ 0 s := by
  obtain ⟨result, run⟩ := XmssSecurity.probComp_support_nonempty
    ((simulateQ (localAnswer prims)
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run ∅)
  have noMpc := (localRun_support (prims := prims) _ ∅ result run).2.1 noMpc_empty
  have frame := FrameL.liftComp (FrameR.dealerCeremony prims circuits settings parameter seeds top tree)
  exact ⟨result.1, result.2, run, noMpc, cacheOK_of_frame cacheOK_empty (frame ∅ result run)⟩

/-- The recorder starts without queries, so its original common prefix
is precisely the supported dealer output and cache, with an empty log. -/
theorem recordingReplay_commonPrefix_of_dealer (prims : Primitives) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (sent : ℕ → C.Party → Mail C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit))) (s : HashCache C)
    (run : (dealt, s) ∈ support ((simulateQ (localAnswer prims)
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run ∅)) :
    (dealt, ((0, []), ((s, ∅), []))) ∈ support
      (treeSimCommonPrefix prims circuits settings top tree D (recordingReplay sent) parameter seeds pairs z) := by
  unfold treeSimCommonPrefix recordingReplay
  rw [mem_support_bind_iff]
  refine ⟨(dealt, s), run, ?_⟩
  simp only [worldRoles, liftComp_pure, counted_pure, simulateQ_pure, StateT.run_pure,
    pure_bind, support_pure, Set.mem_singleton_iff]

theorem hashBad3_nil (D : C.Coalition) : ¬ TreeSimHashBad3 D [] := by
  rw [treeSimHashBad3_iff]
  simp [TreeSimHashBudgetCollision, TreeSimHashAnswer, TreeSimSaltGuess, TreeSimSaltReuse]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8000 in
/-- The fixed recorder and a genuinely supported common prefix precede
every padding. Every padding has a supported cache on which the same live
original final-opening programs are reached. The later log's hash-and-salt
goodness is not asserted by this theorem. -/
theorem recordingReplay_identity_commonPrefix_padding (prims : Primitives) (D : C.Coalition)
    (j : C.Party) (corrupt : j ∈ D.1) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (top : TopTree) (z : Aux) :
    ∃ (sent : ℕ → C.Party → Mail C E)
      (p : (Option TreeOutput × List (List (List Bit))) × ((recordingReplay sent).State × TreeSimState C))
      (views : List (C.Party → Mail C E)) (steps : C.Party → Step C E RealSpec TreeOutput),
      p ∈ support (treeSimCommonPrefix prims (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) parameter seeds pairs z) ∧
      ¬ TreeSimBad3 prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) (dealtKeys parameter seeds pairs) z p.2.2.2 ∧
      sent 40 = (fun _ _ => some .abort) ∧
      (∀ i, i ∈ D.1 → steps i = .done none) ∧ (∀ i, i ∉ D.1 → ¬ (steps i).isDone) ∧
      ∀ padding : OracleComp (LocalSpec C) Unit, ∃ (pad : Unit × HashCache C) (next : TreeSimState C),
        pad ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1) ∧
        TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
          (dealtKeys parameter seeds pairs) p.2.1 ((pad.2, p.2.2.1.2), p.2.2.2) 37
            (((40, views), steps), next) := by
  obtain ⟨dealt, s, dealer, noMpc, fresh⟩ := dealer_fresh_supported prims
    (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ parameter seeds top .top
  obtain ⟨hash, sent, views, steps, _, _, stop, empty, live, replay⟩ :=
    recordingReplay_identity_padding_reached K prims D parameter seeds pairs top s noMpc fresh []
  refine ⟨sent, (dealt, ((0, []), ((s, ∅), []))), views, steps, ?_, ?_, stop, empty, live, ?_⟩
  · unfold treeSimCommonPrefix recordingReplay
    rw [mem_support_bind_iff]
    refine ⟨(dealt, s), ?_, ?_⟩
    · with_reducible exact dealer
    · simp only [worldRoles, liftComp_pure, counted_pure, simulateQ_pure, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff]
  · exact fun bad => bad.elim (hashBad3_nil D)
      (recordingReplay_identity_not_wrong K prims D sent stop j corrupt top (dealtKeys parameter seeds pairs) z [])
  · intro padding
    obtain ⟨pad, next, padded, reached, _⟩ := replay padding
    exact ⟨((), pad), next, padded, reached⟩

/-- The first rerandomization resumes the real check Coin with the
recorded tuple and the actual output continuation. -/
theorem identityCheckFinish_coin (ctx : Context C) (input : C.Term → List Bit)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (z : Shares C Bit × RunState C) :
    identityCheckFinish K ctx input finish z =
      ((realCheckGadgets K ctx).coin 1).run z.2 >>=
        treeStagesCheckAfterCoin K ctx
          [⟨outputShares K [Circuit.identity 1] [input], one K, z.1, 1, .peer⟩]
          z.2.tag z.2.label (identityAfterVerify K ctx z.1 finish) := by
  rw [← treeStages_check_coin_entry K ctx _ (by simp) z.2]
  simp only [identityCheckFinish, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro checked
  simp only [identityAfterVerify, StateT.run_bind, bind_assoc]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The first source entries are deterministic once the common hash and
stream tables are prescribed, with one shared first job. -/
theorem recordingReplay_identity_entries (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (parts : C.Party → Parts C) (top : TopTree) (x : C.Party → Keys C) :
    ∃ (job : Job) (point : Point)
      (finish : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput),
      job.points = [point] ∧
      let ctx := fun i => (⟨i, x i, honestPrssKeys hash parts i⟩ : Context C)
      let input := fun i => ThresholdLeanXmssSecurity.D prims hash (inputQuery (ctx i) job)
      let rnd := fun i => prescribedValue prims D hash hidden
        (prssDraw (ctx i) (bitCodec (E := E)) 0 0 1)
      simulateQ (prescribedLocal prims D hash hidden)
        (Concrete.sequenceFin fun i => continueStep
          (treeSimRealCont K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top x i)
          (.done (if i ∈ D.1 then none else some (honestPrssKeys hash parts i)))) =
        pure (maskedSteps D (fun i => treeSimPeerStep K (ctx i) bitCodec (rnd i)
          (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1 ⟨fun _ => [], 0, 0⟩
          (identityCheckFinish K (ctx i) (input i) (finish i)))) := by
  let ctx := fun i => (⟨i, x i, honestPrssKeys hash parts i⟩ : Context C)
  obtain ⟨job, point, finish, points, source⟩ := top_identity_peer_factor_all K ctx top
  refine ⟨job, point, finish, points, ?_⟩
  dsimp only
  rw [simulateQ_sequenceFin]
  trans Concrete.sequenceFin (fun i => pure (maskedSteps D (fun i =>
    treeSimPeerStep K (ctx i) bitCodec
      (prescribedValue prims D hash hidden (prssDraw (ctx i) (bitCodec (E := E)) 0 0 1))
      (ownerSum K (ctx i) (outputShares K [Circuit.identity 1]
        [ThresholdLeanXmssSecurity.D prims hash (inputQuery (ctx i) job)])) 1 ⟨fun _ => [], 0, 0⟩
      (identityCheckFinish K (ctx i)
        (ThresholdLeanXmssSecurity.D prims hash (inputQuery (ctx i) job)) (finish i))) i))
  · congr 1
    funext i
    by_cases honest : i ∈ D.1
    · simp only [maskedSteps, if_pos honest, continueStep, simulateQ_pure]
    · simp only [maskedSteps, if_neg honest, continueStep, treeSimRealCont]
      change simulateQ (prescribedLocal prims D hash hidden)
        (advance (ceremonyAfterSetup K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ (ctx i) top .top).run) = _
      rw [source, inputShares_fun, advance_oracleStep_bind, simulateQ_bind,
        prescribedLocal_hashOnly prims D hash hidden _ (treeCheck_inputQuery_hashOnly _ _), pure_bind,
        peer_program_prescribed]
  · exact sequenceFin_pure _

/-- A cooperative peer row resumes each exact saved continuation with the
actual reshared values and recorded history. -/
theorem recordingLocalRound_peer (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (ctx : C.Party → Context C) (rnd : C.Party → PrssOutput C Bit)
    (value : C.Party → ℕ → Bit) (count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (script : sent state.1 = fun i => reshareOut K (ctx i) bitCodec (rnd i).1 (rnd i).2 (value i) count) :
    let outbox := fun i => reshareOut K (ctx i) bitCodec (rnd i).1 (rnd i).2 (value i) count
    let z := fun i => reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2 (value i) count (fun j => outbox j i)
    let recorded := fun i => (⟨recordPeer K bitCodec (ctx i).self (st i).history (z i) count,
      (st i).label + 1, (st i).tag⟩ : RunState C)
    simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalRound D sent state (maskedSteps D
        (fun i => treeSimPeerStep K (ctx i) bitCodec (rnd i) (value i) count (st i) (k i)))) = (do
      let steps ← Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else
        simulateQ (prescribedLocal prims D hash hidden) (advance (k i (z i, recorded i)).run)
      pure ((state.1 + 1, state.2 ++ [recorderView D outbox]), steps, outbox)) := by
  dsimp only
  unfold treeSimPeerStep
  rw [recordingLocalRound_wait D sent state _ _ script,
    simulateQ_bind, simulateQ_sequenceFin]
  apply OracleComp.bind_congr'
  · congr 1
    funext i
    by_cases corrupt : i ∈ D.1
    · simp only [if_pos corrupt, simulateQ_pure]
    · simp only [if_neg corrupt]
      rw [exchangeResume_of_no_abort _ _ (fun j =>
        isAbort_reshareOut K bitCodec bitCodec_roundTrip (ctx j) (rnd j).1 (rnd j).2 (value j) count i)]
  · intro steps
    exact simulateQ_pure _ _

def identityPeerOutbox (ctx : C.Party → Context C) (input : C.Party → C.Term → List Bit)
    (rnd : C.Party → PrssOutput C Bit) : C.Party → Mail C E := fun i =>
  reshareOut K (ctx i) bitCodec (rnd i).1 (rnd i).2
    (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1

/-- The exact first Coin step after the complete peer rerandomization row. -/
def identityCoinEntry (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (ctx : C.Party → Context C) (input : C.Party → C.Term → List Bit)
    (rnd : C.Party → PrssOutput C Bit)
    (finish : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (i : C.Party) : Step C E RealSpec TreeOutput :=
  let outbox := identityPeerOutbox K ctx input rnd
  let z := reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2
    (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1 (fun j => outbox j i)
  let st : RunState C := ⟨recordPeer K bitCodec (ctx i).self (fun _ => []) z 1, 1, 0⟩
  treeSimCoinStep K (ctx i)
    (prescribedValue prims D hash hidden (prssDraw (ctx i) (elementCodec K) 1 1 1)) 1 st
    (treeStagesCheckAfterCoin K (ctx i)
      [⟨outputShares K [Circuit.identity 1] [input i], one K, z, 1, .peer⟩]
      0 1 (identityAfterVerify K (ctx i) z (finish i)))

/-- Sending the actual peer outboxes reaches the first checked Coin
without dropping the source history, input tuple or ceremony continuation. -/
theorem recordingLocalRound_identity_peer (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit)
    (sent : ℕ → C.Party → Mail C E) (state : (recordingReplay sent).State)
    (ctx : C.Party → Context C) (input : C.Party → C.Term → List Bit)
    (rnd : C.Party → PrssOutput C Bit)
    (finish : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (script : sent state.1 = identityPeerOutbox K ctx input rnd) :
    simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalRound D sent state (maskedSteps D (fun i =>
        treeSimPeerStep K (ctx i) bitCodec (rnd i)
          (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1 ⟨fun _ => [], 0, 0⟩
          (identityCheckFinish K (ctx i) (input i) (finish i))))) =
      pure ((state.1 + 1, state.2 ++ [recorderView D (identityPeerOutbox K ctx input rnd)]),
        maskedSteps D (identityCoinEntry K prims D hash hidden ctx input rnd finish),
        identityPeerOutbox K ctx input rnd) := by
  rw [recordingLocalRound_peer K prims D hash hidden sent state ctx rnd _ 1 _ _ script]
  have each i : (if i ∈ D.1 then pure (.done none) else
      simulateQ (prescribedLocal prims D hash hidden)
        (advance (identityCheckFinish K (ctx i) (input i) (finish i)
          (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2
            (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1
              (fun j => identityPeerOutbox K ctx input rnd j i),
            ⟨recordPeer K bitCodec (ctx i).self (fun _ => [])
              (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2
                (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1
                  (fun j => identityPeerOutbox K ctx input rnd j i)) 1, 1, 0⟩)).run)) =
      pure (maskedSteps D (identityCoinEntry K prims D hash hidden ctx input rnd finish) i) := by
    by_cases corrupt : i ∈ D.1
    · simp only [maskedSteps, if_pos corrupt]
    · simp only [maskedSteps, if_neg corrupt]
      rw [identityCheckFinish_coin, coin_program_prescribed]
      rfl
  have entries : (Concrete.sequenceFin fun i => if i ∈ D.1 then pure (.done none) else
      simulateQ (prescribedLocal prims D hash hidden)
        (advance (identityCheckFinish K (ctx i) (input i) (finish i)
          (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2
            (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1
              (fun j => identityPeerOutbox K ctx input rnd j i),
            ⟨recordPeer K bitCodec (ctx i).self (fun _ => [])
              (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2
                (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1
                  (fun j => identityPeerOutbox K ctx input rnd j i)) 1, 1, 0⟩)).run)) =
      pure (maskedSteps D (identityCoinEntry K prims D hash hidden ctx input rnd finish)) := by
    simp only [each, sequenceFin_pure]
  simp only [identityPeerOutbox] at entries
  dsimp only
  rw [entries, pure_bind]
  rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- Every actual first identity-batch entry waits at its real peer
rerandomization. Its input is the answer of the source PRF query program. -/
theorem top_identity_entry_shape (impl : QueryImpl (LocalSpec C) ProbComp)
    (ctx : Context C) (top : TopTree) (out : Step C E RealSpec TreeOutput)
    (run : out ∈ support (simulateQ impl (advance
      (ceremonyAfterSetup K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ ctx top .top).run))) :
    ∃ (job : Job) (point : Point)
      (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
      (input : C.Term → List Bit) (rnd : PrssOutput C Bit),
      job.points = [point] ∧
      input ∈ support (simulateQ impl (liftComp (inputQuery ctx job) (LocalSpec C))) ∧
      out = treeSimPeerStep K ctx bitCodec rnd
        (ownerSum K ctx (outputShares K [Circuit.identity 1] [input])) 1 ⟨fun _ => [], 0, 0⟩
        (identityCheckFinish K ctx input finish) := by
  obtain ⟨job, point, finish, points, source⟩ := top_identity_peer_factor K ctx top
  rw [source, inputShares_fun, advance_oracleStep_bind, simulateQ_bind, mem_support_bind_iff] at run
  obtain ⟨input, inputRun, run⟩ := run
  rw [peer_program_interpret, support_map] at run
  obtain ⟨rnd, _, equal⟩ := run
  exact ⟨job, point, finish, input, rnd, points, inputRun, equal.symm⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- A fixed cooperative recorder reaches the actual first identity-batch
exchange after fresh setup. Every honest party is live and retains the
original ceremony continuation. -/
theorem recordingReplay_identity_entry_reached (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (parts : C.Party → Parts C) (sent : ℕ → C.Party → Mail C E)
    (script : ∀ n, n < 3 → sent n = prssReplayScript prims hash parts n)
    (top : TopTree) (x : C.Party → Keys C) (s : TreeSimState C)
    (initial : StreamCoherent hash hidden s.1) :
    ∃ steps next,
      TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) x (0, []) s 0
        ((prssRecorderState prims D hash parts sent, steps), next) ∧
      StreamCoherent hash hidden next.1 ∧
      ∀ i, i ∉ D.1 →
        let ctx : Context C := ⟨i, x i, honestPrssKeys hash parts i⟩
        ∃ (job : Job) (point : Point)
          (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
          (rnd : PrssOutput C Bit), job.points = [point] ∧
          let input := ThresholdLeanXmssSecurity.D prims hash (inputQuery ctx job)
          steps i = treeSimPeerStep K ctx bitCodec rnd
            (ownerSum K ctx (outputShares K [Circuit.identity 1] [input])) 1 ⟨fun _ => [], 0, 0⟩
            (identityCheckFinish K ctx input finish) := by
  let keys := fun i => if i ∈ D.1 then none else some (honestPrssKeys hash parts i)
  let continuation := Concrete.sequenceFin fun i => continueStep
    (treeSimRealCont K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top x i) (.done (keys i))
  obtain ⟨steps, supported⟩ := XmssSecurity.probComp_support_nonempty
    (simulateQ (prescribedLocal prims D hash hidden) continuation)
  have start : (prssRecorderState prims D hash parts sent, steps) ∈ support
      (simulateQ (prescribedLocal prims D hash hidden)
        (recordingLocalTrace K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D sent x (0, []) 0)) := by
    simp only [recordingLocalTrace, simulateQ_bind, mem_support_bind_iff]
    refine ⟨(prssRecorderState prims D hash parts sent, keys),
      recordingReplay_prssLocalPhase prims D hash hidden parts sent script, steps, supported, ?_⟩
    simp only [recordingLocalSteps, simulateQ_pure, support_pure, Set.mem_singleton_iff]
  obtain ⟨next, reached, coherent⟩ := recordingReplay_reach_realize K prims
    (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D hash hidden good sent x (0, []) 0
    (prssRecorderState prims D hash parts sent, steps) s initial start
  refine ⟨steps, next, reached, coherent, ?_⟩
  intro i honest
  have each := supported
  simp only [continuation, simulateQ_sequenceFin] at each
  have localRun := mem_support_sequenceFin _ _ each i
  simp only [keys, if_neg honest, continueStep, treeSimRealCont] at localRun
  have actualRun : steps i ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (advance (ceremonyAfterSetup K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩
        ⟨i, x i, honestPrssKeys hash parts i⟩ top .top).run)) := by
    with_reducible exact localRun
  with_reducible obtain ⟨job, point, finish, input, rnd, points, inputRun, equal⟩ :=
    (top_identity_entry_shape K (prescribedLocal prims D hash hidden)
      ⟨i, x i, honestPrssKeys hash parts i⟩ top (steps i) actualRun)
  rw [prescribedLocal_hashOnly prims D hash hidden _
    (treeCheck_inputQuery_hashOnly _ _), support_pure, Set.mem_singleton_iff] at inputRun
  rw [inputRun] at equal
  exact ⟨job, point, finish, rnd, points, equal⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The actual recorder reaches the first check Coin after setup and a
successful real peer rerandomization. The same hash and hidden tables govern
the whole prefix, including every repeated read. -/
theorem recordingReplay_identity_firstCoin_abort_reached (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (parts : C.Party → Parts C) (top : TopTree) (x : C.Party → Keys C) (s : TreeSimState C)
    (initial : StreamCoherent hash hidden s.1) :
    ∃ (job : Job) (point : Point)
      (finish : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
      (sent : ℕ → C.Party → Mail C E) (next : TreeSimState C), job.points = [point] ∧
      (∀ n, n < 3 → sent n = prssReplayScript prims hash parts n) ∧
      sent 40 = (fun _ _ => some .abort) ∧
      let ctx := fun i => (⟨i, x i, honestPrssKeys hash parts i⟩ : Context C)
      let input := fun i => ThresholdLeanXmssSecurity.D prims hash (inputQuery (ctx i) job)
      let rnd := fun i => prescribedValue prims D hash hidden (prssDraw (ctx i) (bitCodec (E := E)) 0 0 1)
      let outbox := identityPeerOutbox K ctx input rnd
      sent 3 = outbox ∧
      TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) x (0, []) s 1
        (((4, (prssRecorderState prims D hash parts sent).2 ++ [recorderView D outbox]),
          maskedSteps D (identityCoinEntry K prims D hash hidden ctx input rnd finish)), next) ∧
      StreamCoherent hash hidden next.1 := by
  obtain ⟨job, point, finish, points, entries⟩ :=
    recordingReplay_identity_entries K prims D hash hidden parts top x
  let ctx := fun i => (⟨i, x i, honestPrssKeys hash parts i⟩ : Context C)
  let input := fun i => ThresholdLeanXmssSecurity.D prims hash (inputQuery (ctx i) job)
  let rnd := fun i => prescribedValue prims D hash hidden (prssDraw (ctx i) (bitCodec (E := E)) 0 0 1)
  let outbox := identityPeerOutbox K ctx input rnd
  let sent : ℕ → C.Party → Mail C E := fun n =>
    if n < 3 then prssReplayScript prims hash parts n else if n = 40 then fun _ _ => some .abort else outbox
  have script : ∀ n, n < 3 → sent n = prssReplayScript prims hash parts n := by
    intro n hn
    simp only [sent, if_pos hn]
  let peer := maskedSteps D (fun i => treeSimPeerStep K (ctx i) bitCodec (rnd i)
    (ownerSum K (ctx i) (outputShares K [Circuit.identity 1] [input i])) 1 ⟨fun _ => [], 0, 0⟩
    (identityCheckFinish K (ctx i) (input i) (finish i)))
  let coins := maskedSteps D (identityCoinEntry K prims D hash hidden ctx input rnd finish)
  let state : (recordingReplay sent).State := prssRecorderState prims D hash parts sent
  let nextState : (recordingReplay sent).State := (4, state.2 ++ [recorderView D outbox])
  have pending : ¬ ∀ i, i ∉ D.1 → (peer i).isDone := by
    intro allDone
    obtain ⟨i, hi⟩ := prss_exists_honest D
    simpa only [peer, maskedSteps, if_neg hi, treeSimPeerStep, Step.isDone] using allDone i hi
  have once : simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalSteps D sent 1 state peer) = pure (nextState, coins) := by
    rw [recordingLocalSteps, if_neg pending, simulateQ_bind]
    have round := recordingLocalRound_identity_peer K prims D hash hidden sent state ctx input rnd finish
      (by simp only [state, prssRecorderState, sent, show ¬ (3 : ℕ) < 3 by omega, show (3 : ℕ) ≠ 40 by omega, ite_false, outbox])
    change simulateQ (prescribedLocal prims D hash hidden) (recordingLocalRound D sent state peer) = _ at round
    rw [round]
    erw [pure_bind]
    simp only [recordingLocalSteps, simulateQ_pure]
    rfl
  have supported : (nextState, coins) ∈ support (simulateQ (prescribedLocal prims D hash hidden)
      (recordingLocalTrace K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D sent x (0, []) 1)) := by
    simp only [recordingLocalTrace, simulateQ_bind, mem_support_bind_iff]
    refine ⟨(state, fun i => if i ∈ D.1 then none else some (honestPrssKeys hash parts i)),
      recordingReplay_prssLocalPhase prims D hash hidden parts sent script, peer, ?_, ?_⟩
    · rw [entries]
      exact Set.mem_singleton _
    · rw [once]
      exact Set.mem_singleton _
  obtain ⟨next, reached, coherent⟩ := recordingReplay_reach_realize K prims
    (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D hash hidden good sent x (0, []) 1
    (nextState, coins) s initial supported
  refine ⟨job, point, finish, sent, next, points, script, by simp only [sent, show ¬ (40 : ℕ) < 3 by omega, ite_false, ite_true], ?_⟩
  exact ⟨by simp only [sent, show ¬ (3 : ℕ) < 3 by omega, show (3 : ℕ) ≠ 40 by omega, ite_false, outbox, ctx, input, rnd], reached, coherent⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem recordingReplay_identity_firstCoin_reached (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (hidden : HiddenAddress C → Bit) (good : Good prims hash)
    (parts : C.Party → Parts C) (top : TopTree) (x : C.Party → Keys C) (s : TreeSimState C)
    (initial : StreamCoherent hash hidden s.1) :
    ∃ (job : Job) (point : Point)
      (finish : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
      (sent : ℕ → C.Party → Mail C E) (next : TreeSimState C), job.points = [point] ∧
      (∀ n, n < 3 → sent n = prssReplayScript prims hash parts n) ∧
      let ctx := fun i => (⟨i, x i, honestPrssKeys hash parts i⟩ : Context C)
      let input := fun i => ThresholdLeanXmssSecurity.D prims hash (inputQuery (ctx i) job)
      let rnd := fun i => prescribedValue prims D hash hidden (prssDraw (ctx i) (bitCodec (E := E)) 0 0 1)
      let outbox := identityPeerOutbox K ctx input rnd
      sent 3 = outbox ∧
      TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) x (0, []) s 1
        (((4, (prssRecorderState prims D hash parts sent).2 ++ [recorderView D outbox]),
          maskedSteps D (identityCoinEntry K prims D hash hidden ctx input rnd finish)), next) ∧
      StreamCoherent hash hidden next.1 := by
  obtain ⟨job, point, finish, sent, next, points, script, _, reached⟩ :=
    recordingReplay_identity_firstCoin_abort_reached K prims D hash hidden good parts top x s initial
  exact ⟨job, point, finish, sent, next, points, script, reached⟩

/-- Only the PRF-input domain is prescribed here. Setup, transcript and
challenge hash answers remain those of `base`. -/
def identityInputHash (base : Query C → HashOutput) : Query C → HashOutput
  | .prf seed _ => if seed = 1 then 1 else 0
  | query => base query

theorem identityInputHash_good (prims : Primitives) (base : Query C → HashOutput)
    (good : Good prims base) : Good prims (identityInputHash base) := good

/-- A finite auxiliary extension fixes two input answers while preserving
the dealer cache and fresh Coin domains. It is used to choose a table;
the actual replay still starts from the original dealer cache. -/
theorem input_answers_extend (prims : Primitives) (hash : Query C → HashOutput)
    (good : Good prims hash) (s : HashCache C) (agrees : Agrees hash s)
    (noMpc : NoMpc s) (fresh : CacheOK ∅ 0 s) (point : Point)
    (zero : hash (.prf 0 point) = 0) (one : hash (.prf 1 point) = 1) :
    ∃ next : HashCache C, s ≤ next ∧ NoMpc next ∧ CacheOK ∅ 0 next ∧
      next (.prf 0 point) = some 0 ∧ next (.prf 1 point) = some 1 := by
  obtain ⟨middle, first, coherent⟩ := hashAnswer_realize prims hash good s agrees (.prf 0 point)
  obtain ⟨next, second, _⟩ := hashAnswer_realize prims hash good middle coherent (.prf 1 point)
  have firstFrame := hashAnswer_support (prims := prims) (.prf 0 point) s (hash (.prf 0 point), middle) first
  have secondFrame := hashAnswer_support (prims := prims) (.prf 1 point) middle (hash (.prf 1 point), next) second
  have firstCached := hashAnswer_cached prims (q := .prf 0 point)
    (by rintro ⟨_, impossible, _⟩; cases impossible) s _ first
  have secondCached := hashAnswer_cached prims (q := .prf 1 point)
    (by rintro ⟨_, impossible, _⟩; cases impossible) middle _ second
  rw [zero] at firstCached
  rw [one] at secondCached
  refine ⟨next, firstFrame.1.trans secondFrame.1,
    secondFrame.2.1 (firstFrame.2.1 noMpc), ?_, secondFrame.1 firstCached, secondCached⟩
  apply cacheOK_of_frame fresh
  intro q coin
  have different (seed : HashOutput) : (Query.prf (C := C) seed point) ≠ q := by
    rcases coin with ⟨key, index, rfl⟩ | ⟨tag, label, values, rfl⟩ <;> intro impossible <;> cases impossible
  exact (hashAnswer_frame prims _ q (different 1) middle _ second).trans
    (hashAnswer_frame prims _ q (different 0) s _ first)

set_option linter.constructorNameAsVariable false in
/-- The live first-batch source can be chosen with the two distinct input
answers after an actual dealer run. The table extension is only a witness
selection device; its extra entries are absent from the returned dealer cache. -/
theorem identity_pinned_prefix_supported (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (top : TopTree) (job : Job) (point : Point)
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    ∃ (dealt : Option TreeOutput × List (List (List Bit))) (s : HashCache C)
      (hash : Query C → HashOutput) (pref : C.Party → Option (Context C × IdentityOpeningData C E))
      (entries : C.Party → Step C E RealSpec TreeOutput),
      (dealt, s) ∈ support ((simulateQ (localAnswer prims)
        (liftComp (dealerCeremony (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ parameter seeds top .top)
          (LocalSpec C))).run ∅) ∧
      Good prims hash ∧ Agrees hash s ∧ hash (.prf 0 point) = 0 ∧ hash (.prf 1 point) = 1 ∧
      pref ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (honestStart (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) >>=
          honestRounds noFunctionality PEmpty.elim 40)) ∧ (∀ i, (pref i).isSome) ∧
      entries ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (Concrete.sequenceFin fun i => continueStep (ceremonyOpeningResume K finish) (.done (pref i)))) ∧
      ∀ i, ¬ (entries i).isDone := by
  let initialHash := identityInputHash (hashOf prims (∅ : HashCache C))
  have goodInitial : Good prims initialHash := identityInputHash_good prims _ (good_hashOf prims ∅)
  let dealer := liftComp
    (dealerCeremony (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ parameter seeds top .top) (LocalSpec C)
  obtain ⟨dealt, selected⟩ := XmssSecurity.probComp_support_nonempty (simulateQ (fixedLocal prims initialHash) dealer)
  obtain ⟨s, actual, initialCoherent⟩ := fixedLocal_realize prims initialHash goodInitial dealer dealt ∅
    (by intro q value found; simp at found) (by with_reducible exact selected)
  have noMpc := (localRun_support (prims := prims) dealer ∅ (dealt, s)
    (by with_reducible exact actual)).2.1 noMpc_empty
  have frame : FrameL prims dealer := by
    with_reducible exact (FrameL.liftComp
      (FrameR.dealerCeremony prims (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ parameter seeds top .top))
  have fresh := cacheOK_of_frame cacheOK_empty (frame ∅ (dealt, s) (by with_reducible exact actual))
  obtain ⟨auxiliary, larger, auxiliaryNoMpc, auxiliaryFresh, zero, one⟩ := input_answers_extend prims initialHash
    goodInitial s initialCoherent noMpc fresh point
    (by simp [initialHash, identityInputHash]) (by simp [initialHash, identityInputHash])
  obtain ⟨hash, pref, entries, good, coherent, run, present, entryRun, live⟩ :=
    ceremonyBeforeOpening_live_prescribed K prims D parameter seeds pairs job auxiliary auxiliaryNoMpc auxiliaryFresh finish
  have zeroAnswer := coherent _ _ zero
  have oneAnswer := coherent _ _ one
  with_reducible exact ⟨dealt, s, hash, pref, entries, actual, good, coherent.mono larger,
    zeroAnswer, oneAnswer, run, present, entryRun, live⟩

set_option linter.constructorNameAsVariable false in
/-- The actual common-prefix and arbitrary-padding witness can also keep
the real seed-1 answer distinct from the dummy seed-0 answer at the first
job's point. The same table remains coherent at the live reached boundary. -/
theorem recordingReplay_identity_commonPrefix_padding_pinned (prims : Primitives) (D : C.Coalition)
    (j : C.Party) (corrupt : j ∈ D.1) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (top : TopTree) (z : Aux) :
    ∃ (job : Job) (point : Point)
      (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
      (hash : Query C → HashOutput) (sent : ℕ → C.Party → Mail C E)
      (p : (Option TreeOutput × List (List (List Bit))) × ((recordingReplay sent).State × TreeSimState C))
      (views : List (C.Party → Mail C E)) (steps : C.Party → Step C E RealSpec TreeOutput),
      job.points = [point] ∧
      (∀ i keys, (ceremony K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ i keys top .top :
        PartyM C E RealSpec TreeOutput) = ceremonyBeforeOpening K job i keys >>= ceremonyOpeningResume K finish) ∧
      Good prims hash ∧ Agrees hash p.2.2.1.1 ∧ hash (.prf 0 point) = 0 ∧ hash (.prf 1 point) = 1 ∧
      p ∈ support (treeSimCommonPrefix prims (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) parameter seeds pairs z) ∧
      ¬ TreeSimBad3 prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) (dealtKeys parameter seeds pairs) z p.2.2.2 ∧
      sent 40 = (fun _ _ => some .abort) ∧
      (∀ i, i ∈ D.1 → steps i = .done none) ∧ (∀ i, i ∉ D.1 → ¬ (steps i).isDone) ∧
      ∀ padding : OracleComp (LocalSpec C) Unit, ∃ (pad : Unit × HashCache C) (next : TreeSimState C),
        pad ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1) ∧
        TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
          (dealtKeys parameter seeds pairs) p.2.1 ((pad.2, p.2.2.1.2), p.2.2.2) 37
            (((40, views), steps), next) ∧ StreamCoherent hash (aesHidden prims hash) next.1 := by
  obtain ⟨job, point, finish, points, factor⟩ := ceremony_identity_opening_factor K top
  obtain ⟨dealt, s, hash, pref, entries, dealer, good, agrees, zero, one, run, present, entryRun, active⟩ :=
    identity_pinned_prefix_supported K prims D parameter seeds pairs top job point finish
  obtain ⟨sent, views, outside, replay⟩ := recordingReplay_timed_resume_replay prims D hash
    (aesHidden prims hash) good 39
    (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i))
    (fun _ => ceremonyOpeningResume K finish) (fun i => ceremonyBeforeOpening_timed K job i _)
    pref run present entries entryRun (0, []) (fun _ _ _ => some .abort)
  have stop := outside 40 (Or.inr le_rfl)
  refine ⟨job, point, finish, hash, sent, (dealt, ((0, []), ((s, ∅), []))), views,
    maskedSteps D entries, points, factor, good, agrees, zero, one, ?_, ?_, stop, ?_, ?_, ?_⟩
  · unfold treeSimCommonPrefix recordingReplay
    rw [mem_support_bind_iff]
    refine ⟨(dealt, s), ?_, ?_⟩
    · with_reducible exact dealer
    · simp only [worldRoles, liftComp_pure, counted_pure, simulateQ_pure, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff]
  · exact fun bad => bad.elim (hashBad3_nil D)
      (recordingReplay_identity_not_wrong K prims D sent stop j corrupt top (dealtKeys parameter seeds pairs) z [])
  · intro i hi
    simp only [maskedSteps, if_pos hi]
  · intro i hi
    simpa only [maskedSteps, if_neg hi] using active i
  · intro padding
    obtain ⟨pad, padded, compatible⟩ := padding_coherent_supported prims hash good padding s agrees
    have coherent : StreamCoherent hash (aesHidden prims hash) (pad, ∅) := by
      refine ⟨compatible, ?_⟩
      intro x value found
      simp at found
    obtain ⟨next, actual, final⟩ := replay ((pad, ∅), []) coherent
    refine ⟨((), pad), next, padded, ?_, final⟩
    unfold TreeStagesReach
    rw [← ceremony_retained_trace]
    simp only [factor]
    unfold recordingReplay at actual ⊢
    exact actual

/-- The actual first-job query reads the same private inputs as the
two-entry cache used by the identity-claim calculation. -/
theorem inputQuery_cached_of_answers (prims : Primitives) (hash : Query C → HashOutput)
    (ctx : Context C) (job : Job) (point : Point) (points : job.points = [point])
    (seeds : ∀ T, ctx.keys.seed T = 0 ∨ ctx.keys.seed T = 1)
    (answer0 : hash (.prf 0 point) = 0) (answer1 : hash (.prf 1 point) = 1) :
    ThresholdLeanXmssSecurity.D prims hash (inputQuery ctx job) =
      treeStagesCachedInputs (inputCache point) ctx ⟨.randomizer, [point]⟩ := by
  funext T
  rw [treeCheck_D_inputQuery]
  unfold treeStagesCachedInputs
  split_ifs with held
  · simp only [inputBits, points, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have queried : hash (.prf (ctx.keys.seed T) point) =
        ((inputCache (C := C) point) (.prf (ctx.keys.seed T) point)).getD 0 := by
      rcases seeds T with zero | one
      · rw [zero, answer0, inputCache_zero]
        rfl
      · rw [one, answer1, inputCache_one]
        rfl
    rw [queried]
  · rfl

theorem identity_inputQuery_cached (prims : Primitives) (base : Query C → HashOutput)
    (ctx : Context C) (job : Job) (point : Point) (points : job.points = [point])
    (seeds : ∀ T, ctx.keys.seed T = 0 ∨ ctx.keys.seed T = 1) :
    ThresholdLeanXmssSecurity.D prims (identityInputHash base) (inputQuery ctx job) =
      treeStagesCachedInputs (inputCache point) ctx ⟨.randomizer, [point]⟩ := by
  exact inputQuery_cached_of_answers prims (identityInputHash base) ctx job point points seeds
    (by simp [identityInputHash]) (by simp [identityInputHash])

/-- Pin finitely many non-Coin hash answers in an auxiliary cache while
keeping the freshness hypotheses of the actual batch completeness theorem. -/
theorem hash_queries_extend (prims : Primitives) (hash : Query C → HashOutput)
    (good : Good prims hash) (queries : List (Query C))
    (notFixed : ∀ q ∈ queries, ¬ IsFixed q) (notCoin : ∀ q ∈ queries, ¬ IsCoin q)
    (s : HashCache C) (agrees : Agrees hash s) (noMpc : NoMpc s) (fresh : CacheOK ∅ 0 s) :
    ∃ next : HashCache C, s ≤ next ∧ Agrees hash next ∧ NoMpc next ∧ CacheOK ∅ 0 next ∧
      ∀ q ∈ queries, next q = some (hash q) := by
  induction queries generalizing s with
  | nil => exact ⟨s, le_rfl, agrees, noMpc, fresh, by simp⟩
  | cons q queries ih =>
    obtain ⟨middle, selected, coherent⟩ := hashAnswer_realize prims hash good s agrees q
    have frame := hashAnswer_support (prims := prims) q s (hash q, middle) selected
    have cached := hashAnswer_cached prims (q := q) (notFixed q (by simp)) s _ selected
    have freshMiddle : CacheOK ∅ 0 middle := by
      apply cacheOK_of_frame fresh
      intro query coin
      exact hashAnswer_frame prims q query (fun equal => notCoin q (by simp) (equal ▸ coin))
        s _ selected
    obtain ⟨next, larger, compatible, valid, nextFresh, pinned⟩ := ih
      (fun query mem => notFixed query (by simp [mem]))
      (fun query mem => notCoin query (by simp [mem])) middle coherent (frame.2.1 noMpc) freshMiddle
    refine ⟨next, frame.1.trans larger, compatible, valid, nextFresh, ?_⟩
    intro query mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact larger cached
    · exact pinned query mem

/-- The three setup exchanges support any fixed private contribution table,
followed by the actual caller under the derived keys from that same hash. -/
theorem honest_setup_prefix_supported {α : Type} (prims : Primitives)
    (hash : Query C → HashOutput) (parts : C.Party → Parts C) (fuel : ℕ)
    (f : C.Party → PrssKeys C → PartyM C E RealSpec α)
    (out : C.Party → Option α)
    (suffix : out ∈ support (simulateQ (fixedLocal prims hash)
      (honestStart (fun i => f i (honestPrssKeys hash parts i)) >>=
        honestRounds noFunctionality PEmpty.elim fuel))) :
    out ∈ support (simulateQ (fixedLocal prims hash)
      (honestStart (fun i => prssSetup i >>= f i) >>=
        honestRounds noFunctionality PEmpty.elim (fuel + 3))) := by
  rw [simulateQ_bind, mem_support_bind_iff]
  refine ⟨fun i => prssStart i (parts i)
    (ThresholdLeanXmssSecurity.D prims hash (commitQueries .prss i (parts i))) (f i), ?_, ?_⟩
  · rw [honestStart, simulateQ_sequenceFin]
    apply sequenceFin_support_of_each
    intro i
    rw [advance_prssSetup, simulateQ_bind]
    have samples : simulateQ (fixedLocal prims hash) (liftComp (sampleParts (C := C)) (LocalSpec C)) = sampleParts := by
      rw [← prescribedLocal_aes prims (noCoalition : C.Coalition) hash]
      exact prescribedLocal_private prims noCoalition hash (aesHidden prims hash) _
    rw [samples, mem_support_bind_iff]
    refine ⟨parts i, sampleParts_support _, ?_⟩
    rw [simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind, simulateQ_pure]
    exact Set.mem_singleton _
  · rw [simulateQ_fixedLocal_prssRounds]
    exact suffix

/-- Indexed output maps keep every network message and its source continuation. -/
theorem honestStep_map {α β : Type} (f : C.Party → α → β)
    (steps : C.Party → Step C E RealSpec α) :
    honestStep noFunctionality PEmpty.elim (fun i => treeSimCheckMapStep (f i) (steps i)) =
      (fun next i => treeSimCheckMapStep (f i) (next i)) <$>
        honestStep noFunctionality PEmpty.elim steps := by
  rw [honestStep_real, honestStep_real]
  trans Concrete.sequenceFin (fun i => treeSimCheckMapStep (f i) <$>
    (match steps i with
      | .done out => pure (.done out)
      | .wait _ resume => advance (resume fun j => (steps j).delivered i)
      | .call input _ => input.elim))
  · congr 1
    funext i
    cases hs : steps i with
    | done out => rfl
    | call input _ => exact input.elim
    | wait out resume =>
      change advance (Option.map (f i) <$> resume
          (fun j => (treeSimCheckMapStep (f j) (steps j)).delivered i)) =
        treeSimCheckMapStep (f i) <$> advance (resume fun j => (steps j).delivered i)
      simp only [treeSimCheckMapStep_delivered]
      exact treeSimCheck_advance_map (f i) _
  · simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]

theorem honestRounds_map {α β : Type} (f : C.Party → α → β) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec α) :
    honestRounds noFunctionality PEmpty.elim fuel (fun i => treeSimCheckMapStep (f i) (steps i)) =
      (fun out i => (out i).map (f i)) <$> honestRounds noFunctionality PEmpty.elim fuel steps := by
  induction fuel generalizing steps with
  | zero => simp only [honestRounds, treeSimCheckMapStep_output, map_pure]
  | succ fuel ih =>
    simp only [honestRounds, treeSimCheckMapStep_isDone]
    split_ifs
    · simp only [treeSimCheckMapStep_output, map_pure]
    · rw [honestStep_map, map_bind]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      exact bind_congr fun next => ih next

theorem honest_run_map {α β : Type} (f : C.Party → α → β) (fuel : ℕ)
    (p : C.Party → PartyM C E RealSpec α) :
    (honestStart (fun i => f i <$> p i) >>= honestRounds noFunctionality PEmpty.elim fuel) =
      (fun out i => (out i).map (f i)) <$>
        (honestStart p >>= honestRounds noFunctionality PEmpty.elim fuel) := by
  have start : honestStart (fun i => f i <$> p i) =
      (fun steps i => treeSimCheckMapStep (f i) (steps i)) <$> honestStart p := by
    have each (i : C.Party) : advance (f i <$> p i).run =
        treeSimCheckMapStep (f i) <$> advance (p i).run := by
      rw [OptionT.run_map]
      exact treeSimCheck_advance_map (f i) _
    simp only [honestStart, each]
    simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]
  rw [start, map_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  exact bind_congr fun steps => honestRounds_map f fuel steps

/-- The finite setup key queries and term-stream keys of prescribed private
contributions. These queries lie outside the Coin freshness domains. -/
def setupKeyQueries (hash : Query C → HashOutput) (parts : C.Party → Parts C) : List (Query C) :=
  C.terms.map (termInput .prss parts) ++
    (Finset.univ.toList.map (pairInput .prss parts)) ++
    C.terms.map (fun T => .streamKey (hash (termInput .prss parts T)))

theorem setupKeyQueries_notFixed (hash : Query C → HashOutput) (parts : C.Party → Parts C)
    (q : Query C) (mem : q ∈ setupKeyQueries hash parts) : ¬ IsFixed q := by
  simp only [setupKeyQueries, List.mem_append, List.mem_map] at mem
  rcases mem with (⟨T, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨T, _, rfl⟩ <;>
    rintro ⟨input, impossible, _⟩ <;> cases impossible

theorem setupKeyQueries_notCoin (hash : Query C → HashOutput) (parts : C.Party → Parts C)
    (q : Query C) (mem : q ∈ setupKeyQueries hash parts) : ¬ IsCoin q := by
  simp only [setupKeyQueries, List.mem_append, List.mem_map] at mem
  rcases mem with (⟨T, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨T, _, rfl⟩ <;>
    rintro (⟨key, index, impossible⟩ | ⟨tag, label, values, impossible⟩) <;> cases impossible

set_option linter.constructorNameAsVariable false in
/-- Actual setup can retain prescribed private contributions and their term,
pair and stream-key answers while the first identity batch reaches its live
final opening. Only an auxiliary selection cache contains the pinned queries. -/
theorem identity_fixed_setup_live_prescribed (prims : Primitives) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (job : Job) (parts : C.Party → Parts C) (base : Query C → HashOutput)
    (baseGood : Good prims base) (s : HashCache C) (baseAgrees : Agrees base s)
    (noMpc : NoMpc s) (coinsFresh : CacheOK ∅ 0 s)
    (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    ∃ (hash : Query C → HashOutput)
      (pref : C.Party → Option (Context C × IdentityOpeningData C E))
      (next : C.Party → Step C E RealSpec TreeOutput),
      Good prims hash ∧ Agrees hash s ∧
      (∀ T, hash (termInput .prss parts T) = base (termInput .prss parts T)) ∧
      (∀ p, hash (pairInput .prss parts p) = base (pairInput .prss parts p)) ∧
      (∀ T, hash (.streamKey (base (termInput .prss parts T))) =
        base (.streamKey (base (termInput .prss parts T)))) ∧
      (∀ i data, pref i = some data →
        data.1 = (⟨i, dealtKeys parameter seeds pairs i, honestPrssKeys hash parts i⟩ : Context C)) ∧
      pref ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (honestStart (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) >>=
          honestRounds noFunctionality PEmpty.elim 40)) ∧ (∀ i, (pref i).isSome) ∧
      next ∈ support (simulateQ (prescribedLocal prims D hash (aesHidden prims hash))
        (Concrete.sequenceFin fun i => continueStep (ceremonyOpeningResume K finish) (.done (pref i)))) ∧
      ∀ i, ¬ (next i).isDone := by
  obtain ⟨auxiliary, larger, _, auxiliaryNoMpc, auxiliaryFresh, pinned⟩ :=
    hash_queries_extend prims base baseGood (setupKeyQueries base parts)
      (setupKeyQueries_notFixed base parts) (setupKeyQueries_notCoin base parts)
      s baseAgrees noMpc coinsFresh
  let kT := fun T => base (termInput .prss parts T)
  let kP := fun p => base (pairInput .prss parts p)
  obtain ⟨out, supported, allSome⟩ := identityBatch_success_supported K prims
    parameter seeds pairs kT kP job auxiliary auxiliaryNoMpc auxiliaryFresh
  rw [StateT.run'_eq, support_map] at supported
  obtain ⟨result, actual, same⟩ := supported
  change result.1 = out at same
  obtain ⟨hash, good, coherent, _, prescribed⟩ := localRun_prescribed prims D _ auxiliary
    auxiliaryNoMpc result actual
  have termEqual (T : C.Term) : hash (termInput .prss parts T) = kT T :=
    coherent _ _ (pinned _ (by simp [setupKeyQueries, Committee.terms]))
  have pairEqual (p : C.Pair) : hash (pairInput .prss parts p) = kP p :=
    coherent _ _ (pinned _ (by simp [setupKeyQueries]))
  have streamEqual (T : C.Term) : hash (.streamKey (kT T)) = base (.streamKey (kT T)) :=
    coherent _ _ (pinned _ (by simp [setupKeyQueries, kT, Committee.terms]))
  have keysEqual (i : C.Party) : honestPrssKeys hash parts i = prssKeysOf kT kP i := by
    simp only [honestPrssKeys, prssKeysOf, termEqual, pairEqual]
  let ctx := fun i => prssCtx (dealtKeys parameter seeds pairs) kT kP i
  have contextEqual (i : C.Party) :
      (⟨i, dealtKeys parameter seeds pairs i, honestPrssKeys hash parts i⟩ : Context C) = ctx i := by
    rw [keysEqual]
    rfl
  have resultSome : ∀ i, (result.1 i).isSome := by rw [same]; exact allSome
  simp only [identityBatch_opening_factor] at prescribed
  obtain ⟨pref, next, prefixRun, live, entries, active⟩ := honest_timed_prefix_live_supported
    (prescribedLocal prims D hash (aesHidden prims hash)) 36 2
    (fun i => identityBeforeOpening K (ctx i) job)
    (fun i data => identityBatchOpeningResume K (ctx i) data)
    (fun i => identityBeforeOpening_timed K (ctx i) job)
    (fun i data => identityBatchOpeningResume_exchange K (ctx i) data) result.1 prescribed resultSome
  let tagged := fun i => (pref i).map (fun data => (ctx i, data))
  have taggedRun : tagged ∈ support (simulateQ (fixedLocal prims hash)
      (honestStart (fun i => (fun data => (ctx i, data)) <$> identityBeforeOpening K (ctx i) job) >>=
        honestRounds noFunctionality PEmpty.elim 37)) := by
    rw [honest_run_map, simulateQ_map, support_map]
    rw [prescribedLocal_aes] at prefixRun
    exact Set.mem_image_of_mem _ prefixRun
  have suffix : tagged ∈ support (simulateQ (fixedLocal prims hash)
      (honestStart (fun i => do
        let data ← identityBeforeOpening K
          ⟨i, dealtKeys parameter seeds pairs i, honestPrssKeys hash parts i⟩ job
        pure ((⟨i, dealtKeys parameter seeds pairs i, honestPrssKeys hash parts i⟩ : Context C), data)) >>=
        honestRounds noFunctionality PEmpty.elim 37)) := by
    simp only [contextEqual]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using taggedRun
  have whole := honest_setup_prefix_supported prims hash parts 37
    (fun i prss => do
      let data ← identityBeforeOpening K ⟨i, dealtKeys parameter seeds pairs i, prss⟩ job
      pure ((⟨i, dealtKeys parameter seeds pairs i, prss⟩ : Context C), data)) tagged suffix
  change tagged ∈ support (simulateQ (fixedLocal prims hash)
    (honestStart (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i)) >>=
      honestRounds noFunctionality PEmpty.elim 40)) at whole
  rw [← prescribedLocal_aes prims D hash] at whole
  obtain ⟨next', actualEntries, active'⟩ := live_continuations_attach
    (prescribedLocal prims D hash (aesHidden prims hash)) pref live
    (fun i data => identityBatchOpeningResume K (ctx i) data)
    (fun i _ => finish (ctx i)) next entries active
  refine ⟨hash, tagged, next', good, coherent.mono larger, termEqual, pairEqual,
    streamEqual, ?_, whole, ?_, ?_, active'⟩
  · intro i data equal
    cases hp : pref i with
    | none => simp [tagged, hp] at equal
    | some value =>
      have hd : (ctx i, value) = data := by simpa only [tagged, hp, Option.map_some, Option.some.injEq] using equal
      rw [← hd, contextEqual]
  · intro i
    simpa only [tagged, Option.isSome_map] using live i
  · have programs : (fun i => continueStep (ceremonyOpeningResume K finish) (.done (tagged i))) =
        (fun i => continueStep (fun data => identityBatchOpeningResume K (ctx i) data >>= finish (ctx i))
          (.done (pref i))) := by
      funext i
      cases hp : pref i with
      | none => simp only [tagged, hp, Option.map_none, continueStep]
      | some data =>
        simp only [tagged, hp, Option.map_some, continueStep, ceremonyOpeningResume_factor]
    rw [programs]
    exact actualEntries

set_option linter.constructorNameAsVariable false in
/-- The actual common-prefix replay can keep prescribed setup keys and
stream keys, the two distinct source input answers, and the exact context
at each live final opening, uniformly over every later public padding. -/
theorem recordingReplay_identity_fixed_setup_padding (prims : Primitives) (D : C.Coalition)
    (j : C.Party) (corrupt : j ∈ D.1) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (top : TopTree) (z : Aux)
    (parts : C.Party → Parts C) (base : Query C → HashOutput) (baseGood : Good prims base)
    (input0 : ∀ point, base (.prf 0 point) = 0) (input1 : ∀ point, base (.prf 1 point) = 1) :
    ∃ (job : Job) (point : Point)
      (finish : Context C → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
      (hash : Query C → HashOutput) (sent : ℕ → C.Party → Mail C E)
      (p : (Option TreeOutput × List (List (List Bit))) × ((recordingReplay sent).State × TreeSimState C))
      (views : List (C.Party → Mail C E)) (steps : C.Party → Step C E RealSpec TreeOutput),
      job.points = [point] ∧
      (∀ i keys, (ceremony K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ i keys top .top :
        PartyM C E RealSpec TreeOutput) = ceremonyBeforeOpening K job i keys >>= ceremonyOpeningResume K finish) ∧
      Good prims hash ∧ Agrees hash p.2.2.1.1 ∧ hash (.prf 0 point) = 0 ∧ hash (.prf 1 point) = 1 ∧
      (∀ T, hash (termInput .prss parts T) = base (termInput .prss parts T)) ∧
      (∀ pair, hash (pairInput .prss parts pair) = base (pairInput .prss parts pair)) ∧
      (∀ T, hash (.streamKey (base (termInput .prss parts T))) =
        base (.streamKey (base (termInput .prss parts T)))) ∧
      p ∈ support (treeSimCommonPrefix prims (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) parameter seeds pairs z) ∧
      ¬ TreeSimBad3 prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D
        (recordingReplay sent) (dealtKeys parameter seeds pairs) z p.2.2.2 ∧
      sent 40 = (fun _ _ => some .abort) ∧
      (∀ i, i ∈ D.1 → steps i = .done none) ∧ (∀ i, i ∉ D.1 → ¬ (steps i).isDone) ∧
      (∀ i, i ∉ D.1 → ∃ (data : IdentityOpeningData C E) (r : E), r ≠ 0 ∧ r ≠ 1 ∧
        let ctx : Context C := ⟨i, dealtKeys parameter seeds pairs i, honestPrssKeys hash parts i⟩
        steps i = treeSimCheckStep K (.opening (fun _ => data.2.2.1 r)) i
          (identityAfterVerify K ctx data.2.1 (finish ctx) ((), data.2.2.2.2.2))) ∧
      ∀ padding : OracleComp (LocalSpec C) Unit, ∃ (pad : Unit × HashCache C) (next : TreeSimState C),
        pad ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1) ∧
        TreeStagesReach prims K (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ top .top D (recordingReplay sent)
          (dealtKeys parameter seeds pairs) p.2.1 ((pad.2, p.2.2.1.2), p.2.2.2) 37
            (((40, views), steps), next) ∧ StreamCoherent hash (aesHidden prims hash) next.1 := by
  obtain ⟨job, point, finish, points, factor⟩ := ceremony_identity_opening_factor K top
  let dealer := liftComp
    (dealerCeremony (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ parameter seeds top .top) (LocalSpec C)
  obtain ⟨dealt, selected⟩ := XmssSecurity.probComp_support_nonempty (simulateQ (fixedLocal prims base) dealer)
  obtain ⟨s, actualDealer, baseAgrees⟩ := fixedLocal_realize prims base baseGood dealer dealt ∅
    (by intro q value found; simp at found) (by with_reducible exact selected)
  have noMpc := (localRun_support (prims := prims) dealer ∅ (dealt, s)
    (by with_reducible exact actualDealer)).2.1 noMpc_empty
  have frame : FrameL prims dealer := by
    with_reducible exact (FrameL.liftComp
      (FrameR.dealerCeremony prims (fun _ _ => Circuit.identity 1) ⟨.peer, 1⟩ parameter seeds top .top))
  have fresh := cacheOK_of_frame cacheOK_empty (frame ∅ (dealt, s) (by with_reducible exact actualDealer))
  obtain ⟨auxiliary, larger, compatible, auxiliaryNoMpc, auxiliaryFresh, pinned⟩ :=
    hash_queries_extend prims base baseGood [.prf 0 point, .prf 1 point]
      (by intro q h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> rintro ⟨_, impossible, _⟩ <;> cases impossible)
      (by intro q h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;>
            rintro (⟨_, _, impossible⟩ | ⟨_, _, _, impossible⟩) <;> cases impossible)
      s baseAgrees noMpc fresh
  obtain ⟨hash, pref, entries, good, agreesAux, termEqual, pairEqual, streamEqual,
    contexts, run, present, entryRun, active⟩ := identity_fixed_setup_live_prescribed K prims D
      parameter seeds pairs job parts base baseGood auxiliary compatible auxiliaryNoMpc auxiliaryFresh finish
  have agrees := agreesAux.mono larger
  have zero : hash (.prf 0 point) = 0 :=
    (agreesAux _ _ (pinned _ (by simp))).trans (input0 point)
  have one : hash (.prf 1 point) = 1 :=
    (agreesAux _ _ (pinned _ (by simp))).trans (input1 point)
  obtain ⟨sent, views, outside, replay⟩ := recordingReplay_timed_resume_replay prims D hash
    (aesHidden prims hash) good 39
    (fun i => ceremonyBeforeOpening K job i (dealtKeys parameter seeds pairs i))
    (fun _ => ceremonyOpeningResume K finish) (fun i => ceremonyBeforeOpening_timed K job i _)
    pref run present entries entryRun (0, []) (fun _ _ _ => some .abort)
  have stop := outside 40 (Or.inr le_rfl)
  refine ⟨job, point, finish, hash, sent, (dealt, ((0, []), ((s, ∅), []))), views,
    maskedSteps D entries, points, factor, good, agrees, zero, one, termEqual, pairEqual, streamEqual,
    ?_, ?_, stop, ?_, ?_, ?_, ?_⟩
  · unfold treeSimCommonPrefix recordingReplay
    rw [mem_support_bind_iff]
    refine ⟨(dealt, s), ?_, ?_⟩
    · with_reducible exact actualDealer
    · simp only [worldRoles, liftComp_pure, counted_pure, simulateQ_pure, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff]
  · exact fun bad => bad.elim (hashBad3_nil D)
      (recordingReplay_identity_not_wrong K prims D sent stop j corrupt top (dealtKeys parameter seeds pairs) z [])
  · intro i hi
    simp only [maskedSteps, if_pos hi]
  · intro i hi
    simpa only [maskedSteps, if_neg hi] using active i
  · intro i hi
    obtain ⟨data, value⟩ := Option.isSome_iff_exists.mp (present i)
    have each := entryRun
    rw [simulateQ_sequenceFin] at each
    have localEntry := mem_support_sequenceFin _ _ each i
    simp only [value, continueStep] at localEntry
    obtain ⟨r, nonzero, nonone, shape⟩ := ceremonyOpeningResume_live_entry K
      (prescribedLocal prims D hash (aesHidden prims hash)) finish data (entries i) localEntry (active i)
    have context := contexts i data value
    refine ⟨data.2, r, nonzero, nonone, ?_⟩
    simp only [maskedSteps, if_neg hi, shape, context]
  · intro padding
    obtain ⟨pad, padded, compatible⟩ := padding_coherent_supported prims hash good padding s agrees
    have coherent : StreamCoherent hash (aesHidden prims hash) (pad, ∅) := by
      refine ⟨compatible, ?_⟩
      intro x value found
      simp at found
    obtain ⟨next, actual, final⟩ := replay ((pad, ∅), []) coherent
    refine ⟨((), pad), next, padded, ?_, final⟩
    unfold TreeStagesReach
    rw [← ceremony_retained_trace]
    simp only [factor]
    unfold recordingReplay at actual ⊢
    exact actual

/-- Embed a chosen AES key in the actual 256-bit derived-key space. -/
def setupCode (key : Digest) : HashOutput := key.setWidth hashOutputBits

theorem truncate_setupCode (key : Digest) : truncateHash (setupCode key) = key := by
  unfold setupCode truncateHash
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hi, show i < hashOutputBits by unfold hashOutputBits; unfold digestBits at hi; omega]

/-- Every holder contributes the chosen code of its term. Such contributions
are supported by the private setup samples. -/
def codedSetupParts (codes : C.Term → Digest) : C.Party → Parts C :=
  fun _ => ⟨0, fun T => setupCode (codes T), fun _ => 0⟩

/-- Only setup derivations, stream-key conversion and the two input seeds
are prescribed. The later table selection leaves Coin answers fresh. -/
def codedSetupHash (prims : Primitives) : Query C → HashOutput
  | .hash input => prims.Th input
  | .derive .prss .term values => values.headD 0
  | .streamKey key => key
  | .prf seed _ => if seed = 1 then 1 else 0
  | _ => 0

theorem codedSetupHash_good (prims : Primitives) : Good prims (codedSetupHash (C := C) prims) := by
  intro input _
  rfl

theorem codedSetupHash_term (prims : Primitives) (codes : C.Term → Digest) (T : C.Term) :
    codedSetupHash prims (termInput .prss (codedSetupParts codes) T) = setupCode (codes T) := by
  have nonempty : C.parties.filter (· ∈ C.holders T) ≠ [] := by
    obtain ⟨i, held⟩ := exists_holder T
    have mem : i ∈ C.parties.filter (· ∈ C.holders T) := by simp [Committee.parties, held]
    intro empty
    rw [empty] at mem
    cases mem
  unfold termInput codedSetupHash
  cases list : C.parties.filter (· ∈ C.holders T) with
  | nil => exact (nonempty list).elim
  | cons i rest => rfl

/-- The prescribed setup and stream-key inputs decode to the chosen AES
keys in any later table that extends the finite setup pinning. -/
theorem codedSetupHash_stream (prims : Primitives) (codes : C.Term → Digest)
    (hash : Query C → HashOutput)
    (termEqual : ∀ T, hash (termInput .prss (codedSetupParts codes) T) =
      codedSetupHash prims (termInput .prss (codedSetupParts codes) T))
    (streamEqual : ∀ T, hash (.streamKey
        (codedSetupHash prims (termInput .prss (codedSetupParts codes) T))) =
      codedSetupHash (C := C) prims (.streamKey
        (codedSetupHash prims (termInput .prss (codedSetupParts codes) T)))) (T : C.Term) :
    hash (termInput .prss (codedSetupParts codes) T) = setupCode (codes T) ∧
      truncateHash (hash (.streamKey (setupCode (codes T)))) = codes T := by
  refine ⟨(termEqual T).trans (codedSetupHash_term prims codes T), ?_⟩
  have stream := streamEqual T
  rw [codedSetupHash_term] at stream
  rw [stream]
  exact truncate_setupCode (codes T)

/-- A concrete permitted PRF fixture encodes its key and the low 128 bits
of the round label in the 256 salt bits. Other stream coordinates return 0. -/
def codedSaltBit (key : Digest) (label position : ℕ) : Bit :=
  if position < digestBits then (if key.getLsbD position then 1 else 0)
  else if (BitVec.ofNat digestBits label).getLsbD (position - digestBits) then 1 else 0

def codedSaltAes : Aes :=
  ⟨$ᵗ Digest, fun key point => if point.2.1 = 2 then codedSaltBit key point.1 point.2.2 else 0⟩

theorem codedSaltBit_key (key key' : Digest) (label label' : ℕ)
    (equal : ∀ g : Fin 256, codedSaltBit key label g.val = codedSaltBit key' label' g.val) :
    key = key' := by
  apply BitVec.eq_of_getLsbD_eq
  intro g bound
  have value := equal ⟨g, by unfold digestBits at bound; omega⟩
  simp only [codedSaltBit, if_pos bound] at value
  cases left : key.getLsbD g <;> cases right : key'.getLsbD g <;> simp_all

theorem codedSaltBit_label (key key' : Digest) (label label' : ℕ)
    (bound : label < 2 ^ digestBits) (bound' : label' < 2 ^ digestBits)
    (equal : ∀ g : Fin 256, codedSaltBit key label g.val = codedSaltBit key' label' g.val) :
    label = label' := by
  have words : BitVec.ofNat digestBits label = BitVec.ofNat digestBits label' := by
    apply BitVec.eq_of_getLsbD_eq
    intro g hg
    have value := equal ⟨digestBits + g, by unfold digestBits at hg ⊢; omega⟩
    simp only [codedSaltBit, show ¬ digestBits + g < digestBits by omega,
      ite_false, Nat.add_sub_cancel_left] at value
    cases left : (BitVec.ofNat digestBits label).getLsbD g <;>
      cases right : (BitVec.ofNat digestBits label').getLsbD g <;> simp_all
  have values := congrArg BitVec.toNat words
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt bound'] using values

/-- A reached log coherent with the prescribed AES table records exactly
that table's stream bits, for both hidden and publicly evaluated streams. -/
theorem logged_aes_answer (prims : Primitives) (D : C.Coalition) (hash : Query C → HashOutput)
    {α : Type} (program : OracleComp (WorldSpec C) α) (cache : HashCache C)
    (out : α × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D) program).run ((cache, ∅), [])))
    (coherent : StreamCoherent hash (aesHidden prims hash) out.2.1)
    (y : PrgInput C) (bit : Bit)
    (read : (⟨.inr (.inr (.inr y)), bit⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ out.2.2) :
    bit = prims.aes.eval (truncateHash (hash (.streamKey y.2.1))) y.2.2 := by
  by_cases secret : Hidden D y.1
  · have consistent := TreeSaltGuardedPairBound.hiddenCoherent_run prims D program
      ((cache, ∅), []) (by intro y bit _; simp) out run
    have cached := (consistent y bit secret).mp read
    exact (coherent.2 cached).symm
  · have consistent := TreeSaltGuardedPairBound.publicCoherent_run prims D program
      ((cache, ∅), []) (by intro y bit _ h; simp at h) out run
    obtain ⟨key, cached, value⟩ := consistent y bit secret read
    rw [← coherent.1 _ _ cached] at value
    exact value

/-- For the concrete key-and-label AES fixture, actual recorded salt reuse
is excluded by the source's key/label positions. The bit equalities come
from the actual logged run, not an abstract salt process. -/
theorem recordingReplay_coded_not_saltReuse_of_positions (Th : HashInput → HashOutput)
    (D : C.Coalition) (codes : C.Term → Digest) (injective : Function.Injective codes)
    (hash : Query C → HashOutput)
    (decoded : ∀ T, truncateHash (hash (.streamKey (setupCode (codes T)))) = codes T)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (sent : ℕ → C.Party → Mail C E) (x : C.Party → Keys C)
    (state : (recordingReplay sent).State) (cache : HashCache C) (fuel : ℕ)
    (a : TreeSimConfig (recordingReplay sent) (TreeSimState C))
    (reach : TreeStagesReach ⟨Th, codedSaltAes⟩ K circuits settings top tree D (recordingReplay sent)
      x state ((cache, ∅), []) fuel a)
    (coherent : StreamCoherent hash (aesHidden ⟨Th, codedSaltAes⟩ hash) a.2.1)
    (positions : ∀ T key label g bit,
      (⟨.inr (.inr (.inr (.term T, key, label, 2, g))), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ a.2.2 →
      key = setupCode (codes T) ∧ label < 2 ^ digestBits) :
    ¬ TreeSimSaltReuse D a.2.2 := by
  have actual := reach
  unfold TreeStagesReach at actual
  rw [← recordingReplay_trace_interpret] at actual
  rintro ⟨salt, T, key, label, T', key', label', _, _, different, reads⟩
  obtain ⟨keyEq, labelBound⟩ := positions T key label 0 _ (reads ⟨0, by decide⟩).1
  obtain ⟨keyEq', labelBound'⟩ := positions T' key' label' 0 _ (reads ⟨0, by decide⟩).2
  have equal : ∀ g : Fin 256, codedSaltBit (codes T) label g.val =
      codedSaltBit (codes T') label' g.val := by
    intro g
    have first := logged_aes_answer ⟨Th, codedSaltAes⟩ D hash _ cache a actual coherent
      (.term T, key, label, 2, g.val) _ (reads g).1
    have second := logged_aes_answer ⟨Th, codedSaltAes⟩ D hash _ cache a actual coherent
      (.term T', key', label', 2, g.val) _ (reads g).2
    simp only [keyEq, keyEq', decoded, codedSaltAes, ite_true] at first second
    exact first.symm.trans second
  have terms : T = T' := injective (codedSaltBit_key _ _ _ _ equal)
  have labels : label = label' := codedSaltBit_label _ _ _ _ labelBound labelBound' equal
  apply different
  simp only [keyEq, keyEq', terms, labels]

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.exists_honest_final_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_honest_final_difference

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.identity_one_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity_one_run

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.inputCache_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inputCache_reachable

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.cached_identity_initial_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cached_identity_initial_difference

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.halvingRecorded_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halvingRecorded_erase

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.halvingRecorded_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halvingRecorded_exists

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.halving_sources_no_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halving_sources_no_repair

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.final_view_kernel_no_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_view_kernel_no_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.prescribedLocal_logged_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prescribedLocal_logged_realize

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_reach_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_reach_realize

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_prssPhase_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_prssPhase_realize

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.fresh_hidden_element_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fresh_hidden_element_support

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.prescribedValue_prssDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prescribedValue_prssDraw

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_entries

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingLocalRound_identity_peer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingLocalRound_identity_peer

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_firstCoin_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_firstCoin_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.identity_inputQuery_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity_inputQuery_cached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.replaceHiddenBlock_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replaceHiddenBlock_agrees

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.coin_entries_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coin_entries_realize

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.fresh_coin_entries_all_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fresh_coin_entries_all_values

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_timed_abort_all_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_timed_abort_all_fuel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.ceremony_identity_opening_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_identity_opening_factor

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_no_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_no_outputs

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_not_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_not_wrong

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingLocalRound_coin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingLocalRound_coin

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingLocalSteps_of_honest_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingLocalSteps_of_honest_timed

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_honest_timed_phase_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_honest_timed_phase_realize

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.honest_timed_prefix_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_timed_prefix_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.identity_batch_cost_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity_batch_cost_lt_one

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.identityBatch_success_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identityBatch_success_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.ceremonyBeforeOpening_success_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyBeforeOpening_success_logged

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_firstCoin_abort_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_firstCoin_abort_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.timed_phase_steps_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms timed_phase_steps_split

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.honest_timed_prefix_live_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_timed_prefix_live_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.ceremony_retained_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_retained_trace

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_finalOpening_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_finalOpening_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.fixedLocal_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedLocal_realize

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_timed_resume_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_timed_resume_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_finalOpening_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_finalOpening_shaped

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_padding_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_padding_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_commonPrefix_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_commonPrefix_padding

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_reached_not_saltGuess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_reached_not_saltGuess

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_good_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_good_iff

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.identity_pinned_prefix_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity_pinned_prefix_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_commonPrefix_padding_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_commonPrefix_padding_pinned

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.inputQuery_cached_of_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inputQuery_cached_of_answers

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.hash_queries_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hash_queries_extend

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.honest_setup_prefix_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_setup_prefix_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.honest_run_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_run_map

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.identity_fixed_setup_live_prescribed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity_fixed_setup_live_prescribed

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_identity_fixed_setup_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_identity_fixed_setup_padding

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.codedSetupHash_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codedSetupHash_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.logged_aes_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logged_aes_answer

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinalClaims.recordingReplay_coded_not_saltReuse_of_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingReplay_coded_not_saltReuse_of_positions

end ThresholdLeanXmssSecurity.TreeTwinFinalClaims
