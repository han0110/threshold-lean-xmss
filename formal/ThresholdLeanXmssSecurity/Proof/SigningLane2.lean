import ThresholdLeanXmssSecurity.Proof.SigningCappedExpect
import ThresholdLeanXmssSecurity.Proof.SigningEagerGrind
import XmssSecurity.Scan.PerKey

/-!
# The lane 2 potential of leanVM as one capped potential

`probEvent_capped_expect_le` (`SigningCappedExpect`) takes one potential with an upper step bound
of `1 / N` at each counted output-side call. The lane 2 proof of leanVM (`Ghost.collision_le`) is
not of that form. This module gives it that form.

## The leanVM terms

Let `N = 2 ^ 128`, `l = landing = |validDigests| / N`, and `A = momentA l Q`. The terms are on
`Ghost.State`, which holds the cache, the signing trace and the count `k` (`Scan/Phase.lean`).

| term | pays for | step bound |
| --- | --- | --- |
| `f1 = N² 1{PreBad} + N openΦ` | a sign step that selects a partnered cached input | rises by `aCost = V W + H` at a fresh encoding call at an unsigned key, and not at a sign step (`sign_collision_le` spends `N Φ_e`) |
| `f2 = hvSum` | the compensator of `aCost` | rises by at least `l aCost` (`f2_step`) |
| `f3 = F3 (nCount, vCount, k)` | the moment of the landed count | rises by at most `A openInd`, and is `⊤` past the budget (`f3_step`) |
| `f4 = N² 1{PostBad}` | a later call that repeats a selected digest | rises by at most `N signedInd` (`f4_step`) |

The terms are in units of `1 / N²`, so the allowed rise at one call is `N`. leanVM has no bound
`aCost ≤ N` at one call. It bounds the sum of `aCost` over the run only, through `f2`, `f3` and
`landing_mul_hvSum_le` (`preBad_le`).

## The compensated potential

`lane2Sum = f1 + (f3 - f2 / l) + f4`.

* `f2 / l ≤ f3` at every state (`f2_le_landing_mul_f3`), so the subtraction does not truncate.
* At one call `f1` rises by `aCost`, `f2 / l` rises by at least `aCost`, and `f3` rises by at most
  `A openInd`. So `lane2Sum` rises by at most `A openInd + N signedInd ≤ N` (`lane2Sum_step`),
  with `momentA_le_N` (`Q < 2 ^ 127`) and `openCost_add_signedCost_le`.
* `lane2Potential` is `lane2Sum / N²` up to the count `q`, and zero above. It meets `hstep` at
  `1 / N` (`lane2Potential_step`).
* `probEvent_lane2_le` gives `q / N` for the flag or an event with `N² ≤ f1 + f4`, and
  `probEvent_ghost_lane2_le` is its form for the leanVM terms.

## The sign step that returns the base

The threshold adversary sees the base (round 1 releases `ρ_e`, and the base is the answer of the
base call). `Ghost.impl` returns only the signature.

* Each step lemma reads the state after one call, and holds for each call and each state. So the
  information of the adversary does not enter it. A step with the same state law keeps it
  (`tsum_view_eq`, `f1_step_of_law` to `f4_step_of_law`).
* `signWithBase` returns the base and the signature. Its trace entry holds the signature only, so its
  state law is that of `Concrete.scheme.sign` (`evalDist_signWithBaseStep`). All four step lemmas
  hold at it (`f1_step_signWithBase` to `f4_step_signWithBase`). No step bound fails.
* The base must be uniform and independent of the cache at the sign step, as in
  `selection_uniform_eq`. In the threshold run the base is a fresh oracle answer at the first base
  call. A call before the release that meets `ρ_e` is an input-side hit of the capped flag.

## The remaining goals

`probEvent_ghost_lane2_le` is the bound on the leanVM event `ghostEvent`. The flat run
(`SigningFlat`) must give a view to the leanVM cache and trace, and these facts for each call.

* A world call has the view law of a leanVM world step (`f1_step_of_viewLaw`, `f2_step_of_viewLaw`,
  `f4_step_of_viewLaw`), and its count matches the leanVM tick for `f3_step_of_law`. This needs the
  map from the threshold encoding input (`.message lay key`) to `Partner.input`.
* The base call has the view law of `signWithBaseStep`. This needs the bridge from `Scheme.grind`
  to `precomputedSignBoundedAttempts`, a base that is a truncated fresh oracle answer in place of
  `$ᵗ Randomness`, and `topSignedAt` at the key. The base call is counted here, and leanVM does not
  tick at a sign step, so `f3` uses `f3_step_of_counts` with `counts_signWithBaseStep`.
* Another counted call keeps the view, and `f3_step_of_counts` applies.
* `hinv` (`Ghost.Inv`, the count of cached inputs is at most the count), and `hcost` from
  `openCost_add_signedCost_le` (an encoding call is counted and output side).
* The start view is `(cache0, [])` with no encoding input in `cache0`, and each key has one base
  call (`leafIndices.Nodup` in `ghostEvent`, change R3).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLane2Proof

open SigningOpeningProof SigningCappedExpectProof

section Combine

attribute [local instance] Classical.propDecidable

variable {κ σ : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (StateT σ ProbComp))
  (p inputSide : κ → Prop)

theorem countImpl_support_count (t : κ) (st : σ × ℕ) (x : spec t × (σ × ℕ))
    (hx : x ∈ support ((countImpl impl p t).run st)) : x.2.2 = st.2 + if p t then 1 else 0 := by
  simp only [countImpl, StateT.run_mk, support_map, Set.mem_image] at hx
  obtain ⟨y, -, rfl⟩ := hx
  rfl

/-- Two functions that agree on the support have the same expectation. -/
theorem tsum_congr_support {β : Type} (mx : ProbComp β) (F G : β → ℝ≥0∞)
    (h : ∀ x ∈ support mx, F x = G x) :
    ∑' x, Pr[= x | mx] * F x = ∑' x, Pr[= x | mx] * G x := by
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- The expectation of a sum of three functions. -/
theorem tsum_add3 {β : Type} (mx : ProbComp β) (F G H : β → ℝ≥0∞) :
    ∑' x, Pr[= x | mx] * (F x + G x + H x) =
      ∑' x, Pr[= x | mx] * F x + ∑' x, Pr[= x | mx] * G x + ∑' x, Pr[= x | mx] * H x := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add]

/-- The uncapped lane 2 sum `f1 + (f3 - f2 / l) + f4`. It is `N ^ 2` times a probability. -/
def lane2Sum (l : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞) (st : σ × ℕ) : ℝ≥0∞ :=
  f1 st + (f3 st - f2 st * l⁻¹) + f4 st

/-- The compensated step. `f1` rises by `cost1`, `f2` rises by at least `l * cost1`, and `f3`
rises by at most `A * openC`. So `f3 - f2 / l` falls by `cost1` and rises by `A * openC`, and the
sum rises by at most `A * openC + N * signedC`. -/
theorem lane2Sum_step (N l A : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞)
    (cost1 openC signedC : κ → σ × ℕ → ℝ≥0∞) (mx : ProbComp (β × (σ × ℕ))) (st : σ × ℕ) (t : κ)
    (h1 : ∑' x, Pr[= x | mx] * f1 x.2 ≤ f1 st + cost1 t st)
    (h2 : f2 st + l * cost1 t st ≤ ∑' x, Pr[= x | mx] * f2 x.2)
    (h3 : ∑' x, Pr[= x | mx] * f3 x.2 ≤ f3 st + A * openC t st)
    (h4 : ∑' x, Pr[= x | mx] * f4 x.2 ≤ f4 st + N * signedC t st)
    (hcomp : ∀ st, f2 st ≤ l * f3 st) (hf2 : ∀ st, f2 st ≠ ⊤) (hA : A ≤ N)
    (hl0 : l ≠ 0) (hlt : l ≠ ⊤) :
    ∑' x, Pr[= x | mx] * lane2Sum l f1 f2 f3 f4 x.2 ≤
      lane2Sum l f1 f2 f3 f4 st + N * (openC t st + signedC t st) := by
  have hle : ∀ s, f2 s * l⁻¹ ≤ f3 s := fun s => by
    calc f2 s * l⁻¹ ≤ l * f3 s * l⁻¹ := mul_le_mul' (hcomp s) le_rfl
      _ = f3 s := by rw [mul_comm l, mul_assoc, ENNReal.mul_inv_cancel hl0 hlt, mul_one]
  have hb : ∀ s, f2 s * l⁻¹ ≠ ⊤ := fun s => ENNReal.mul_ne_top (hf2 s) (ENNReal.inv_ne_top.2 hl0)
  have hd : ∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) + cost1 t st ≤
      (f3 st - f2 st * l⁻¹) + A * openC t st := by
    rcases eq_or_ne (f3 st) ⊤ with htop | htop
    · rw [htop, ENNReal.top_sub (hb st), top_add]; exact le_top
    have hsplit : ∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) +
        (∑' x, Pr[= x | mx] * f2 x.2) * l⁻¹ = ∑' x, Pr[= x | mx] * f3 x.2 := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [mul_assoc, ← mul_add, tsub_add_cancel_of_le (hle x.2)]
    have hlow : f2 st * l⁻¹ + cost1 t st ≤ (∑' x, Pr[= x | mx] * f2 x.2) * l⁻¹ := by
      calc f2 st * l⁻¹ + cost1 t st = (f2 st + l * cost1 t st) * l⁻¹ := by
            rw [add_mul, mul_comm l, mul_assoc, ENNReal.mul_inv_cancel hl0 hlt, mul_one]
        _ ≤ _ := mul_le_mul' h2 le_rfl
    rw [← ENNReal.add_le_add_iff_right (hb st)]
    calc ∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) + cost1 t st + f2 st * l⁻¹ =
          ∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) + (f2 st * l⁻¹ + cost1 t st) := by ring
      _ ≤ ∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) + (∑' x, Pr[= x | mx] * f2 x.2) * l⁻¹ :=
          add_le_add le_rfl hlow
      _ ≤ f3 st + A * openC t st := hsplit.le.trans h3
      _ = (f3 st - f2 st * l⁻¹) + A * openC t st + f2 st * l⁻¹ := by
          rw [add_right_comm, tsub_add_cancel_of_le (hle st)]
  unfold lane2Sum
  rw [tsum_add3]
  calc _ ≤ f1 st + cost1 t st + ∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) +
        (f4 st + N * signedC t st) := add_le_add (add_le_add h1 le_rfl) h4
    _ = f1 st + (∑' x, Pr[= x | mx] * (f3 x.2 - f2 x.2 * l⁻¹) + cost1 t st) +
        (f4 st + N * signedC t st) := by ring
    _ ≤ f1 st + ((f3 st - f2 st * l⁻¹) + A * openC t st) + (f4 st + N * signedC t st) :=
        add_le_add (add_le_add le_rfl hd) le_rfl
    _ ≤ f1 st + ((f3 st - f2 st * l⁻¹) + N * openC t st) + (f4 st + N * signedC t st) := by
        gcongr
    _ = _ := by ring

/-- The capped lane 2 potential. It is `lane2Sum / N ^ 2` up to the count `q`, and zero above. -/
def lane2Potential (q : ℕ) (N l : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞) (st : σ × ℕ) : ℝ≥0∞ :=
  if st.2 ≤ q then lane2Sum l f1 f2 f3 f4 st * (N * N)⁻¹ else 0

/-- **The lane 2 potential meets `hstep` of `probEvent_capped_expect_le`.** The hypotheses are the
step lemmas `f1_step` to `f4_step`, `landing_mul_hvSum_le`, `momentA_le_N` and
`openCost_add_signedCost_le` of leanVM, at the counted run. -/
theorem lane2Potential_step (q : ℕ) (N l A : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞)
    (cost1 openC signedC : κ → σ × ℕ → ℝ≥0∞) (Inv : σ × ℕ → Prop)
    (h1 : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f1 x.2 ≤ f1 st + cost1 t st)
    (h2 : ∀ t st, Inv st →
      f2 st + l * cost1 t st ≤ ∑' x, Pr[= x | (countImpl impl p t).run st] * f2 x.2)
    (h3 : ∀ t st, Inv st → (p t → st.2 < q) →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f3 x.2 ≤ f3 st + A * openC t st)
    (h4 : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f4 x.2 ≤ f4 st + N * signedC t st)
    (hcomp : ∀ st, f2 st ≤ l * f3 st) (hf2 : ∀ st, f2 st ≠ ⊤)
    (hcost : ∀ t st, openC t st + signedC t st ≤ if p t ∧ ¬inputSide t then 1 else 0)
    (hA : A ≤ N) (hl0 : l ≠ 0) (hlt : l ≠ ⊤) (hN0 : N ≠ 0) (hNt : N ≠ ⊤) :
    ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * lane2Potential q N l f1 f2 f3 f4 x.2 ≤
        lane2Potential q N l f1 f2 f3 f4 st +
          if cappedCall p q t st ∧ ¬inputSide t then N⁻¹ else 0 := by
  intro t st hst
  set mx := (countImpl impl p t).run st
  by_cases hq : st.2 + (if p t then 1 else 0) ≤ q
  · have hcap : p t → st.2 < q := fun hp => by rw [if_pos hp] at hq; omega
    have hst2 : st.2 ≤ q := le_trans (Nat.le_add_right _ _) hq
    rw [tsum_congr_support mx _ (fun x => lane2Sum l f1 f2 f3 f4 x.2 * (N * N)⁻¹) fun x hx => by
      rw [lane2Potential, if_pos (by rw [countImpl_support_count impl p t st x hx]; exact hq)]]
    have hmul : ∀ x : spec t × (σ × ℕ), Pr[= x | mx] * (lane2Sum l f1 f2 f3 f4 x.2 * (N * N)⁻¹) =
        Pr[= x | mx] * lane2Sum l f1 f2 f3 f4 x.2 * (N * N)⁻¹ := fun x => (mul_assoc _ _ _).symm
    simp_rw [hmul]
    rw [ENNReal.tsum_mul_right, lane2Potential, if_pos hst2]
    have hs := lane2Sum_step N l A f1 f2 f3 f4 cost1 openC signedC mx st t (h1 t st hst) (h2 t st hst)
      (h3 t st hst hcap) (h4 t st hst) hcomp hf2 hA hl0 hlt
    refine (mul_le_mul' hs le_rfl).trans ?_
    rw [add_mul]
    refine add_le_add le_rfl ?_
    have hNN : N * (N * N)⁻¹ = N⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt), ← mul_assoc, ENNReal.mul_inv_cancel hN0 hNt,
        one_mul]
    by_cases hout : p t ∧ ¬inputSide t
    · rw [if_pos ⟨⟨hout.1, hcap hout.1⟩, hout.2⟩, mul_comm N, mul_assoc, hNN]
      calc (openC t st + signedC t st) * N⁻¹ ≤ 1 * N⁻¹ :=
            mul_le_mul' ((hcost t st).trans (by rw [if_pos hout])) le_rfl
        _ = N⁻¹ := one_mul _
    · have h0 : openC t st + signedC t st = 0 :=
        le_antisymm ((hcost t st).trans (by rw [if_neg hout])) zero_le
      rw [h0, mul_zero, zero_mul]
      exact zero_le
  · refine le_trans (le_of_eq ?_) zero_le
    refine (tsum_congr_support mx _ (fun _ => 0) fun x hx => ?_).trans (by simp)
    rw [lane2Potential, if_neg (by rw [countImpl_support_count impl p t st x hx]; exact hq)]

/-- **The lane 2 bound in the capped hybrid.** An event `E` with `N ^ 2 ≤ f1 + f4` (`PreBad` in
`f1` and `PostBad` in `f4`) within the count `q`, or the input-side flag, has probability at most
`q / N`, with `N = |T|`. -/
theorem probEvent_lane2_le {β K T : Type} [Fintype K] [DecidableEq K] [Fintype T] [Nonempty T]
    [DecidableEq T] [SampleableType (K → T)] (keyOf : κ → K) (point : κ → T) (q : ℕ) (l A : ℝ≥0∞)
    (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞) (cost1 openC signedC : κ → σ × ℕ → ℝ≥0∞) (Inv : σ × ℕ → Prop)
    (hinv : ∀ t st, Inv st → ∀ x ∈ support ((countImpl impl p t).run st), Inv x.2)
    (h1 : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f1 x.2 ≤ f1 st + cost1 t st)
    (h2 : ∀ t st, Inv st →
      f2 st + l * cost1 t st ≤ ∑' x, Pr[= x | (countImpl impl p t).run st] * f2 x.2)
    (h3 : ∀ t st, Inv st → (p t → st.2 < q) →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f3 x.2 ≤ f3 st + A * openC t st)
    (h4 : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f4 x.2 ≤
        f4 st + (Fintype.card T : ℝ≥0∞) * signedC t st)
    (hcomp : ∀ st, f2 st ≤ l * f3 st) (hf2 : ∀ st, f2 st ≠ ⊤)
    (hcost : ∀ t st, openC t st + signedC t st ≤ if p t ∧ ¬inputSide t then 1 else 0)
    (hA : A ≤ Fintype.card T) (hl0 : l ≠ 0) (hlt : l ≠ ⊤)
    (E : σ × ℕ → Prop)
    (hE : ∀ st, E st → (Fintype.card T : ℝ≥0∞) * Fintype.card T ≤ f1 st + f4 st)
    (oa : OracleComp (spec + RevealSpec K T) β) (σ₀ : σ) (hσ₀ : Inv (σ₀, 0))
    (hf1₀ : f1 (σ₀, 0) = 0) (hf3₀ : f3 (σ₀, 0) = 0) (hf4₀ : f4 (σ₀, 0) = 0) :
    Pr[fun r => r.2.2.2 = true ∨ (E r.2.1 ∧ r.2.1.2 ≤ q) | $ᵗ (K → T) >>= fun s =>
      (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
        ((σ₀, 0), fun _ => none, false)] ≤ q * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hN0 : (Fintype.card T : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card T : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine probEvent_capped_expect_le impl inputSide p keyOf point q Inv
    (lane2Potential q (Fintype.card T) l f1 f2 f3 f4) hinv
    (lane2Potential_step impl p inputSide q _ l A f1 f2 f3 f4 cost1 openC signedC Inv h1 h2 h3 h4
      hcomp hf2 hcost hA hl0 hlt hN0 hNt)
    (fun st => E st ∧ st.2 ≤ q) (fun st hst => ?_) oa σ₀ hσ₀ ?_
  · rw [lane2Potential, if_pos hst.2, lane2Sum]
    calc (1 : ℝ≥0∞) = (Fintype.card T : ℝ≥0∞) * Fintype.card T *
          ((Fintype.card T : ℝ≥0∞) * Fintype.card T)⁻¹ :=
          (ENNReal.mul_inv_cancel (mul_ne_zero hN0 hN0) (ENNReal.mul_ne_top hNt hNt)).symm
      _ ≤ _ := by
          refine mul_le_mul' ((hE st hst.1).trans ?_) le_rfl
          rw [add_right_comm]
          exact le_self_add
  · rw [lane2Potential, if_pos (Nat.zero_le q), lane2Sum, hf1₀, hf3₀, hf4₀, zero_tsub, add_zero,
      add_zero, zero_mul]

end Combine

section Transfer

/-- Two computations whose maps have the same law have the same expectation of a function of the
map. -/
theorem tsum_map_eq {β β' T : Type} (mx : ProbComp β) (my : ProbComp β') (f : β → T) (g : β' → T)
    (hlaw : 𝒟[f <$> mx] = 𝒟[g <$> my]) (F : T → ℝ≥0∞) :
    ∑' x, Pr[= x | mx] * F (f x) = ∑' y, Pr[= y | my] * F (g y) := by
  rw [← tsum_probOutput_map_mul mx f F, ← tsum_probOutput_map_mul my g F]
  refine tsum_congr fun z => ?_
  rw [probOutput_def, probOutput_def, hlaw]

/-- A step whose state law, read through `view`, equals the state law of another step has the same
expectation of every function of the read state. -/
theorem tsum_view_eq {α α' S S' : Type} (mx : ProbComp (α × S)) (my : ProbComp (α' × S'))
    (view : S → S') (hlaw : 𝒟[(fun x => view x.2) <$> mx] = 𝒟[(fun y => y.2) <$> my])
    (F : S' → ℝ≥0∞) :
    ∑' x, Pr[= x | mx] * F (view x.2) = ∑' y, Pr[= y | my] * F y.2 := by
  rw [← tsum_probOutput_map_mul mx (fun x => view x.2) F,
    ← tsum_probOutput_map_mul my (fun y => y.2) F]
  refine tsum_congr fun z => ?_
  rw [probOutput_def, probOutput_def, hlaw]

variable (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
  {α S : Type} (mx : ProbComp (α × S)) (view : S → XmssSecurity.Ghost.State) (st : S)
  (input : (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).Domain)

/-- `f1_step` of leanVM for any step with the state law of a leanVM step. -/
theorem f1_step_of_law
    (hlaw : 𝒟[(fun x => view x.2) <$> mx] =
      𝒟[(fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st)]) :
    ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f1 secretKey (view x.2) ≤
      XmssSecurity.Ghost.f1 secretKey (view st) +
        XmssSecurity.Ghost.cost1 secretKey input (view st) := by
  rw [tsum_view_eq mx _ view hlaw]
  exact XmssSecurity.Ghost.f1_step publicKey secretKey input (view st)

/-- `f2_step` of leanVM for any step with the state law of a leanVM step. -/
theorem f2_step_of_law
    (hlaw : 𝒟[(fun x => view x.2) <$> mx] =
      𝒟[(fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st)]) :
    XmssSecurity.Ghost.f2 secretKey (view st) +
        XmssSecurity.Partner.landing * XmssSecurity.Ghost.cost1 secretKey input (view st) ≤
      ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f2 secretKey (view x.2) := by
  rw [tsum_view_eq mx _ view hlaw]
  exact XmssSecurity.Ghost.f2_step publicKey secretKey input (view st)

/-- `f3_step` of leanVM for any step with the state law of a leanVM step. -/
theorem f3_step_of_law (Q : ℕ) (hQ : Q ≤ 2 ^ 127) (hinv : XmssSecurity.Ghost.Inv secretKey (view st))
    (hlaw : 𝒟[(fun x => view x.2) <$> mx] =
      𝒟[(fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st)]) :
    ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f3 secretKey Q (view x.2) ≤
      XmssSecurity.Ghost.f3 secretKey Q (view st) +
        XmssSecurity.Ghost.cost3 secretKey Q input (view st) := by
  rw [tsum_view_eq mx _ view hlaw]
  exact XmssSecurity.Ghost.f3_step publicKey secretKey Q hQ input (view st) hinv

/-- `f4_step` of leanVM for any step with the state law of a leanVM step. -/
theorem f4_step_of_law
    (hlaw : 𝒟[(fun x => view x.2) <$> mx] =
      𝒟[(fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st)]) :
    ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f4 secretKey (view x.2) ≤
      XmssSecurity.Ghost.f4 secretKey (view st) +
        XmssSecurity.Ghost.cost4 secretKey input (view st) := by
  rw [tsum_view_eq mx _ view hlaw]
  exact XmssSecurity.Ghost.f4_step publicKey secretKey input (view st)

end Transfer

section SignWithBase

variable (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)

/-- The leanVM sign step that also returns the base of its scan. -/
def signWithBase (leafIndex : XmssSecurity.LeafIndex) (message : XmssSecurity.Message) :
    OracleComp XmssSecurity.OracleWorld (XmssSecurity.Randomness × Option XmssSecurity.Signature) := do
  let base ← liftM XmssSecurity.Concrete.signingRandomness
  let result ← XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base
    XmssSecurity.signingAttemptLimit 0
  return (base, if XmssSecurity.Concrete.topSignedAt secretKey leafIndex then result else none)

/-- Without the base, `signWithBase` is the leanVM sign step. -/
theorem snd_signWithBase (leafIndex : XmssSecurity.LeafIndex) (message : XmssSecurity.Message) :
    Prod.snd <$> signWithBase secretKey leafIndex message =
      XmssSecurity.Concrete.scheme.sign secretKey leafIndex message := by
  change _ = XmssSecurity.Concrete.precomputedCappedSign secretKey leafIndex message
  rw [XmssSecurity.Concrete.precomputedCappedSign, signWithBase]
  simp

/-- The ghost step of a sign request that returns the base to the adversary. The trace entry
stores the signature only, as in `XmssSecurity.Ghost.impl`. -/
def signWithBaseStep (request : XmssSecurity.SignRequest) :
    StateT XmssSecurity.Ghost.State ProbComp
      (XmssSecurity.Randomness × Option XmssSecurity.Signature) :=
  StateT.mk fun s => (fun r => (r.1, ((r.2, s.1.2 ++ [⟨request, r.1.2, s.1.1, r.2⟩]), s.2))) <$>
    (simulateQ XmssSecurity.romImpl
      (signWithBase secretKey request.leafIndex request.message)).run s.1.1

/-- The state law of the base-returning sign step is the state law of the leanVM sign step. -/
theorem evalDist_signWithBaseStep (request : XmssSecurity.SignRequest)
    (s : XmssSecurity.Ghost.State) :
    𝒟[(fun x => x.2) <$> (signWithBaseStep secretKey request).run s] =
      𝒟[(fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey secretKey (.inr request)).run s] := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  have hsign : (simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign secretKey request.leafIndex request.message)).run cache =
      (fun r => (r.1.2, r.2)) <$> (simulateQ XmssSecurity.romImpl
        (signWithBase secretKey request.leafIndex request.message)).run cache := by
    rw [← snd_signWithBase, simulateQ_map, StateT.run_map]
  congr 1
  rw [XmssSecurity.Ghost.impl_run, XmssSecurity.Ghost.source_sign, signWithBaseStep, StateT.run_mk]
  simp only [Functor.map_map]
  erw [hsign]
  show _ = (fun a : Option XmssSecurity.Signature × XmssSecurity.HashSpec.QueryCache =>
      ((a.2, XmssSecurity.signingCacheTraceUpdate (Sum.inr request) cache a.1 a.2 trace),
        XmssSecurity.Ghost.tick (Sum.inr request) k)) <$> (fun r => (r.1.2, r.2)) <$>
      (simulateQ XmssSecurity.romImpl (signWithBase secretKey request.leafIndex request.message)).run cache
  rw [Functor.map_map]
  simp [XmssSecurity.Ghost.tick, XmssSecurity.Ghost.IsAdvHash, XmssSecurity.signingCacheTraceUpdate]

include publicKey in
/-- `f1_step` of leanVM holds at the base-returning sign step. -/
theorem f1_step_signWithBase (request : XmssSecurity.SignRequest) (s : XmssSecurity.Ghost.State) :
    ∑' x, Pr[= x | (signWithBaseStep secretKey request).run s] * XmssSecurity.Ghost.f1 secretKey x.2 ≤
      XmssSecurity.Ghost.f1 secretKey s + XmssSecurity.Ghost.cost1 secretKey (.inr request) s :=
  f1_step_of_law publicKey secretKey _ id s (.inr request)
    (by simpa using evalDist_signWithBaseStep publicKey secretKey request s)

include publicKey in
/-- `f2_step` of leanVM holds at the base-returning sign step. -/
theorem f2_step_signWithBase (request : XmssSecurity.SignRequest) (s : XmssSecurity.Ghost.State) :
    XmssSecurity.Ghost.f2 secretKey s +
        XmssSecurity.Partner.landing * XmssSecurity.Ghost.cost1 secretKey (.inr request) s ≤
      ∑' x, Pr[= x | (signWithBaseStep secretKey request).run s] * XmssSecurity.Ghost.f2 secretKey x.2 :=
  f2_step_of_law publicKey secretKey _ id s (.inr request)
    (by simpa using evalDist_signWithBaseStep publicKey secretKey request s)

include publicKey in
/-- `f3_step` of leanVM holds at the base-returning sign step. -/
theorem f3_step_signWithBase (Q : ℕ) (hQ : Q ≤ 2 ^ 127) (request : XmssSecurity.SignRequest)
    (s : XmssSecurity.Ghost.State) (hs : XmssSecurity.Ghost.Inv secretKey s) :
    ∑' x, Pr[= x | (signWithBaseStep secretKey request).run s] * XmssSecurity.Ghost.f3 secretKey Q x.2 ≤
      XmssSecurity.Ghost.f3 secretKey Q s + XmssSecurity.Ghost.cost3 secretKey Q (.inr request) s :=
  f3_step_of_law publicKey secretKey _ id s (.inr request) Q hQ hs
    (by simpa using evalDist_signWithBaseStep publicKey secretKey request s)

include publicKey in
/-- `f4_step` of leanVM holds at the base-returning sign step. -/
theorem f4_step_signWithBase (request : XmssSecurity.SignRequest) (s : XmssSecurity.Ghost.State) :
    ∑' x, Pr[= x | (signWithBaseStep secretKey request).run s] * XmssSecurity.Ghost.f4 secretKey x.2 ≤
      XmssSecurity.Ghost.f4 secretKey s + XmssSecurity.Ghost.cost4 secretKey (.inr request) s :=
  f4_step_of_law publicKey secretKey _ id s (.inr request)
    (by simpa using evalDist_signWithBaseStep publicKey secretKey request s)

end SignWithBase


section Split

/-! The count of the threshold run is the second component, and `view` reads the leanVM cache and
trace from the rest. `f1`, `f2` and `f4` do not read the count, so their transfer needs the law of
the view only. -/

variable (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
  {α S : Type} (mx : ProbComp (α × (S × ℕ)))
  (view : S → XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace) (st : S × ℕ)
  (input : (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).Domain) (k : ℕ)

/-- The leanVM state of a threshold state. -/
abbrev ghostView (st : S × ℕ) : XmssSecurity.Ghost.State := (view st.1, st.2)

/-- `f1_step` of leanVM for a step whose view has the law of a leanVM step at any count. -/
theorem f1_step_of_viewLaw
    (hlaw : 𝒟[(fun x => view x.2.1) <$> mx] =
      𝒟[(fun y => y.2.1) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st.1, k)]) :
    ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f1 secretKey (ghostView view x.2) ≤
      XmssSecurity.Ghost.f1 secretKey (ghostView view st) +
        XmssSecurity.Ghost.cost1 secretKey input (ghostView view st) := by
  have h := tsum_map_eq mx ((XmssSecurity.Ghost.impl publicKey secretKey input).run (view st.1, k))
    (fun x => view x.2.1) (fun y => y.2.1) hlaw
    (fun c => XmssSecurity.Ghost.f1 secretKey (c, 0))
  exact h.le.trans (XmssSecurity.Ghost.f1_step publicKey secretKey input (view st.1, k))

/-- `f2_step` of leanVM for a step whose view has the law of a leanVM step at any count. -/
theorem f2_step_of_viewLaw
    (hlaw : 𝒟[(fun x => view x.2.1) <$> mx] =
      𝒟[(fun y => y.2.1) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st.1, k)]) :
    XmssSecurity.Ghost.f2 secretKey (ghostView view st) +
        XmssSecurity.Partner.landing * XmssSecurity.Ghost.cost1 secretKey input (ghostView view st) ≤
      ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f2 secretKey (ghostView view x.2) := by
  have h := tsum_map_eq mx ((XmssSecurity.Ghost.impl publicKey secretKey input).run (view st.1, k))
    (fun x => view x.2.1) (fun y => y.2.1) hlaw
    (fun c => XmssSecurity.Ghost.f2 secretKey (c, 0))
  exact (XmssSecurity.Ghost.f2_step publicKey secretKey input (view st.1, k)).trans h.ge

/-- `f4_step` of leanVM for a step whose view has the law of a leanVM step at any count. -/
theorem f4_step_of_viewLaw
    (hlaw : 𝒟[(fun x => view x.2.1) <$> mx] =
      𝒟[(fun y => y.2.1) <$> (XmssSecurity.Ghost.impl publicKey secretKey input).run (view st.1, k)]) :
    ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f4 secretKey (ghostView view x.2) ≤
      XmssSecurity.Ghost.f4 secretKey (ghostView view st) +
        XmssSecurity.Ghost.cost4 secretKey input (ghostView view st) := by
  have h := tsum_map_eq mx ((XmssSecurity.Ghost.impl publicKey secretKey input).run (view st.1, k))
    (fun x => view x.2.1) (fun y => y.2.1) hlaw
    (fun c => XmssSecurity.Ghost.f4 secretKey (c, 0))
  exact h.le.trans (XmssSecurity.Ghost.f4_step publicKey secretKey input (view st.1, k))

/-- The `f3` step of a call that keeps the counts of the view and adds at most one to the count
within the budget, such as the base call or a counted call that is not an encoding call. It uses
`F3_budget`. -/
theorem f3_step_of_counts (Q : ℕ)
    (hsupp : ∀ x ∈ support mx,
      XmssSecurity.Ghost.nCount secretKey.parameter (view x.2.1).1 (view x.2.1).2 =
          XmssSecurity.Ghost.nCount secretKey.parameter (view st.1).1 (view st.1).2 ∧
        XmssSecurity.Ghost.vCount secretKey.parameter (view x.2.1).1 (view x.2.1).2 =
          XmssSecurity.Ghost.vCount secretKey.parameter (view st.1).1 (view st.1).2 ∧
        (x.2.2 = st.2 ∨ (x.2.2 = st.2 + 1 ∧ st.2 < Q))) :
    ∑' x, Pr[= x | mx] * XmssSecurity.Ghost.f3 secretKey Q (ghostView view x.2) ≤
      XmssSecurity.Ghost.f3 secretKey Q (ghostView view st) := by
  refine XmssSecurity.Ghost.tsum_le_of_support _ _ _ fun x hx => ?_
  obtain ⟨hn, hv, hk⟩ := hsupp x hx
  unfold XmssSecurity.Ghost.f3
  rw [hn, hv]
  rcases hk with hk | ⟨hk, hlt⟩
  · rw [hk]
  · rw [hk]; exact XmssSecurity.Partner.F3_budget hlt

/-- The view and count of the base-returning sign step keep the counts. -/
theorem counts_signWithBaseStep (request : XmssSecurity.SignRequest) (s : XmssSecurity.Ghost.State)
    (x) (hx : x ∈ support ((signWithBaseStep secretKey request).run s)) :
    XmssSecurity.Ghost.nCount secretKey.parameter x.2.1.1 x.2.1.2 =
        XmssSecurity.Ghost.nCount secretKey.parameter s.1.1 s.1.2 ∧
      XmssSecurity.Ghost.vCount secretKey.parameter x.2.1.1 x.2.1.2 =
        XmssSecurity.Ghost.vCount secretKey.parameter s.1.1 s.1.2 ∧ x.2.2 = s.2 := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  rw [signWithBaseStep, StateT.run_mk, support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have hr' : (r.1.2, r.2) ∈ support ((simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign secretKey request.leafIndex request.message)).run cache) := by
    rw [← snd_signWithBase, simulateQ_map, StateT.run_map, support_map]
    exact ⟨r, hr, rfl⟩
  have h := XmssSecurity.Ghost.counts_sign secretKey (trace := trace) hr'
  exact ⟨h.1, h.2.1, rfl⟩

end Split

/-- `f2` is finite. -/
theorem f2_ne_top (secretKey : XmssSecurity.SecretKey) (s : XmssSecurity.Ghost.State) :
    XmssSecurity.Ghost.f2 secretKey s ≠ ⊤ := by
  unfold XmssSecurity.Ghost.f2 XmssSecurity.Ghost.hvSum XmssSecurity.Partner.H
  refine ENNReal.sum_ne_top.2 fun e _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
  refine ENNReal.sum_ne_top.2 fun y _ => ?_
  split_ifs
  exacts [XmssSecurity.Ghost.W_ne_top _ _ _ y, ENNReal.zero_ne_top]

/-- The comparison `hcomp` of `lane2Potential_step` for the leanVM potentials. It is
`landing_mul_hvSum_le` divided by `landing`. -/
theorem f2_le_landing_mul_f3 (secretKey : XmssSecurity.SecretKey) (Q : ℕ)
    (s : XmssSecurity.Ghost.State) :
    XmssSecurity.Ghost.f2 secretKey s ≤
      XmssSecurity.Partner.landing * XmssSecurity.Ghost.f3 secretKey Q s := by
  have h := XmssSecurity.Ghost.landing_mul_hvSum_le Q (k := s.2) secretKey.parameter s.1.1 s.1.2
  rw [pow_two, mul_assoc] at h
  exact (ENNReal.mul_le_mul_iff_right XmssSecurity.Ghost.landing_ne_zero
    XmssSecurity.Partner.landing_ne_top).1 h

section Ghost

attribute [local instance] Classical.propDecidable

variable {κ σ : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (StateT σ ProbComp))
  (p inputSide : κ → Prop)

/-- The lane 2 event of leanVM on the view. A sign step selected a partnered cached input
(`PreBad`), or a later call repeated a selected digest (`PostBad`). -/
def ghostEvent (secretKey : XmssSecurity.SecretKey)
    (view : σ → XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace) (st : σ × ℕ) :
    Prop :=
  XmssSecurity.Ghost.PreBad secretKey (view st.1).2 ∨
    ((view st.1).2.leafIndices.Nodup ∧
      XmssSecurity.Ghost.PostBad secretKey.parameter (view st.1).2 (view st.1).1)

/-- **The lane 2 bound of leanVM in the capped hybrid.** The step hypotheses are the leanVM step
lemmas on the view, which `f1_step_of_viewLaw` to `f4_step_of_viewLaw`, `f3_step_of_law` and
`f3_step_of_counts` give for each kind of call. -/
theorem probEvent_ghost_lane2_le {β K T : Type} [Fintype K] [DecidableEq K] [Fintype T]
    [Nonempty T] [DecidableEq T] [SampleableType (K → T)]
    (hcard : Fintype.card T = 2 ^ XmssSecurity.digestBits) (keyOf : κ → K) (point : κ → T) (q : ℕ)
    (hq : q < 2 ^ 127) (secretKey : XmssSecurity.SecretKey)
    (view : σ → XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace)
    (cost1 openC signedC : κ → σ × ℕ → ℝ≥0∞)
    (hinv : ∀ t st, XmssSecurity.Ghost.Inv secretKey (ghostView view st) →
      ∀ x ∈ support ((countImpl impl p t).run st), XmssSecurity.Ghost.Inv secretKey (ghostView view x.2))
    (h1 : ∀ t st, XmssSecurity.Ghost.Inv secretKey (ghostView view st) →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * XmssSecurity.Ghost.f1 secretKey (ghostView view x.2) ≤
        XmssSecurity.Ghost.f1 secretKey (ghostView view st) + cost1 t st)
    (h2 : ∀ t st, XmssSecurity.Ghost.Inv secretKey (ghostView view st) →
      XmssSecurity.Ghost.f2 secretKey (ghostView view st) + XmssSecurity.Partner.landing * cost1 t st ≤
        ∑' x, Pr[= x | (countImpl impl p t).run st] *
          XmssSecurity.Ghost.f2 secretKey (ghostView view x.2))
    (h3 : ∀ t st, XmssSecurity.Ghost.Inv secretKey (ghostView view st) → (p t → st.2 < q) →
      ∑' x, Pr[= x | (countImpl impl p t).run st] *
          XmssSecurity.Ghost.f3 secretKey q (ghostView view x.2) ≤
        XmssSecurity.Ghost.f3 secretKey q (ghostView view st) +
          ENNReal.ofReal (XmssSecurity.Partner.momentA XmssSecurity.Ghost.pReal q) * openC t st)
    (h4 : ∀ t st, XmssSecurity.Ghost.Inv secretKey (ghostView view st) →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * XmssSecurity.Ghost.f4 secretKey (ghostView view x.2) ≤
        XmssSecurity.Ghost.f4 secretKey (ghostView view st) +
          ((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞) * signedC t st)
    (hcost : ∀ t st, openC t st + signedC t st ≤ if p t ∧ ¬inputSide t then 1 else 0)
    (oa : OracleComp (spec + RevealSpec K T) β) (σ₀ : σ)
    (cache0 : XmssSecurity.HashSpec.QueryCache) (hview₀ : view σ₀ = (cache0, []))
    (hc0 : ∀ e y, cache0 (XmssSecurity.Partner.input secretKey.parameter e y) = none) :
    Pr[fun r => r.2.2.2 = true ∨ (ghostEvent secretKey view r.2.1 ∧ r.2.1.2 ≤ q) |
      $ᵗ (K → T) >>= fun s =>
        (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
          ((σ₀, 0), fun _ => none, false)] ≤ q * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hN : (Fintype.card T : ℝ≥0∞) = ((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞) := by
    rw [hcard]
  have hst₀ : ghostView view (σ₀, 0) = ((cache0, []), 0) := by simp [ghostView, hview₀]
  refine probEvent_lane2_le impl p inputSide keyOf point q XmssSecurity.Partner.landing
    (ENNReal.ofReal (XmssSecurity.Partner.momentA XmssSecurity.Ghost.pReal q))
    (fun st => XmssSecurity.Ghost.f1 secretKey (ghostView view st))
    (fun st => XmssSecurity.Ghost.f2 secretKey (ghostView view st))
    (fun st => XmssSecurity.Ghost.f3 secretKey q (ghostView view st))
    (fun st => XmssSecurity.Ghost.f4 secretKey (ghostView view st)) cost1 openC signedC
    (fun st => XmssSecurity.Ghost.Inv secretKey (ghostView view st)) hinv h1 h2 h3
    (fun t st hst => by rw [hN]; exact h4 t st hst)
    (fun st => f2_le_landing_mul_f3 secretKey q _) (fun st => f2_ne_top secretKey _) hcost
    (by rw [hN]; exact XmssSecurity.Ghost.momentA_le_N hq) XmssSecurity.Ghost.landing_ne_zero
    XmssSecurity.Partner.landing_ne_top (ghostEvent secretKey view) (fun st hst => ?_) oa σ₀
    (by simp only [hst₀]; exact XmssSecurity.Ghost.inv_initial secretKey hc0)
    (by simp only [hst₀]; exact XmssSecurity.Ghost.f1_initial secretKey hc0)
    (by simp only [hst₀]; exact XmssSecurity.Ghost.f3_initial secretKey hc0 q)
    (by simp only [hst₀]; rw [XmssSecurity.Ghost.f4, XmssSecurity.Ghost.postPot_nil, mul_zero])
  rw [hN]
  rcases hst with h | h
  · refine le_trans ?_ le_self_add
    unfold XmssSecurity.Ghost.f1
    rw [if_pos h, mul_one]
    exact le_self_add
  · refine le_trans ?_ le_add_self
    unfold XmssSecurity.Ghost.f4 XmssSecurity.Ghost.postPot
    rw [if_pos h, mul_one]

end Ghost

end SigningLane2Proof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.probEvent_lane2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.probEvent_lane2_le

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.lane2Potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.lane2Potential_step

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.evalDist_signWithBaseStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.evalDist_signWithBaseStep

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.f2_le_landing_mul_f3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.f2_le_landing_mul_f3

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.probEvent_ghost_lane2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.probEvent_ghost_lane2_le
