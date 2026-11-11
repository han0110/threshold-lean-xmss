import ThresholdLeanXmssSecurity.Proof.SigningOpening

/-!
# The expectation form of the capped hit bound

This module holds the tool of change R2 (`SigningEagerGrind`). The uncharged lane is one expectation
over a capped hybrid, and not a flag that one call decides.

## The hybrid

* `cappedHybrid` is `revealImpl` over `countImpl` with no output-side flag. The secrets `s : K → T`
  are uniform and the handler never reads them. So each secret is in effect sampled at its reveal
  (`sum_uniform_reveal_le`, `revealImpl_run_congr`).
* The flag pays for the input side. A counted call among the first `q` raises it when it carries an
  unrevealed secret.
* A potential `f` on the state `σ × ℕ` pays for the output side. It starts at zero, and it is at
  least one on the event `E`.
* `hstep` asks that `f` rise in expectation by at most `1 / |T|` at each of the first `q` counted
  output-side calls, and not rise at any other call. A potential `g` that rises at every counted
  output-side call gives such an `f` as `fun st => if st.2 ≤ q then g st else 0`, with the event
  `fun st => E st ∧ st.2 ≤ q`. The support-wise budget then gives `st.2 ≤ q` in the coupling. An
  invariant `Inv` restricts `hstep` as in `XmssSecurity.expectedFinal_le`.

## The results

* `expectedFinal_flag_le` shows that a raised flag adds at most one to the expected potential.
* `expectedFinal_capped_le_aux` bounds the averaged expected potential by `f + (q - n) / |T|`.
* `probEvent_capped_expect_le` bounds the flag or `E` by `q / |T|`.
* `probEvent_le_of_capped_expect` is the 128-bit form for an event that the flag or `E` dominates.

At a counted call the flag rises with probability `1 / |T|` over `s` on the input side, and `f`
rises by at most `1 / |T|` in expectation on the output side. The count rises by one in both cases.
So the sum of the two parts is at most `1 / |T|` for each of the first `q` counted calls, also when
a run mixes the two sides.

`XmssSecurity.expectedFinal_le` fixes one handler, and for a fixed `s` the input-side hit is not a
random step. So the induction here averages over `s` at each step. It reuses
`XmssSecurity.expectedFinal`, `XmssSecurity.expectedFinal_pure` and
`XmssSecurity.probEvent_le_expectedFinal`.

## The check on the two traces

Let `N = |T| = 2 ^ 128`.

* In the stopped scan of `SigningUncharged.trueOpening_charge_gap`, the adversary calls
  `commitmentInput` with trials `ρ'` until a match, and then makes encoding calls. In the hybrid the
  commitment `c_e` is a fresh pending answer, so the scan does not see `ρ_e` and its length `T_h`
  does not depend on `s e`. Each scan call is input side with the unrevealed key `e`, and it costs
  `1 / N` through the flag. Each of the `U_h` encoding calls is output side, and the lane 2
  potential of leanVM in `f` rises by `1 / N`. The cap counts both, so the bound is
  `E[T_h + U_h] / N ≤ q / N`.
* In the coin-flip trace of `SigningEagerGrind`, the coin is an uncounted call, and `f` does not
  rise at it. On heads the `q` commitment calls before round 1 are input side, and the flag costs at
  most `q / N`. On tails the `q` encoding calls at `e` are output side, and `f` rises by at most
  `q / N`. The induction takes the mean of the two branches, so the bound is `q / N`, and not the
  `1.5 · q / N` of the flag cap plus `Ghost.collision_le`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningCappedExpectProof

open SigningOpeningProof

section CappedExpect

attribute [local instance] Classical.propDecidable

variable {κ σ β K T : Type} {spec : OracleSpec κ}
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T] [SampleableType (K → T)]

/-- The potential of the capped hybrid. It is one when the input-side flag is up, plus `f` of the
hybrid state. -/
def cappedPotential (f : σ × ℕ → ℝ≥0∞) (st : (σ × ℕ) × (K → Option T) × Bool) : ℝ≥0∞ :=
  (if st.2.2 = true then 1 else 0) + f st.1

variable (impl : QueryImpl spec (StateT σ ProbComp)) (inputSide : κ → Prop) (p : κ → Prop)
  (keyOf : κ → K) (point : κ → T)

/-- The capped hybrid. Only input-side calls raise the flag. The output side is in the potential. -/
abbrev cappedHybrid (q : ℕ) (s : K → T) :=
  revealImpl (countImpl impl p) (cappedCall p q) inputSide (fun _ _ _ => False) keyOf point s

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A counted call of the capped hybrid at any flag. It raises the flag exactly on an input-side
hit. -/
theorem cappedHybrid_inl_run (q : ℕ) (s : K → T) (t : κ)
    (k : spec t → OracleComp (spec + RevealSpec K T) β) (st : σ × ℕ) (stored : K → Option T)
    (b : Bool) :
    (simulateQ (cappedHybrid impl inputSide p keyOf point q s)
        (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k)).run (st, stored, b) =
      (countImpl impl p t).run st >>= fun x =>
        (simulateQ (cappedHybrid impl inputSide p keyOf point q s) (k x.1)).run
          (x.2, stored, b || decide (cappedCall p q t st ∧ inputSide t ∧
            stored (keyOf t) = none ∧ s (keyOf t) = point t)) := by
  rw [revealImpl_query_bind_run]
  simp only [revealImpl, StateT.run_mk, bind_map_left]
  refine bind_congr fun x => ?_
  congr 3
  congr 1
  exact decide_eq_decide.mpr (by simp)

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A raised flag adds at most one to the expected potential. The handler never reads the flag. -/
theorem expectedFinal_flag_le (q : ℕ) (s : K → T) (f : σ × ℕ → ℝ≥0∞)
    (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (st : σ × ℕ) (stored : K → Option T) (b : Bool),
      XmssSecurity.expectedFinal (cappedHybrid impl inputSide p keyOf point q s) (cappedPotential f) oa
          (st, stored, true) ≤
        1 + XmssSecurity.expectedFinal (cappedHybrid impl inputSide p keyOf point q s)
          (cappedPotential f) oa (st, stored, b) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st stored b
    simp only [XmssSecurity.expectedFinal_pure, cappedPotential, if_true]
    gcongr
    exact le_add_self
  | query_bind t k ih =>
    intro st stored b
    simp only [XmssSecurity.expectedFinal] at ih ⊢
    rcases t with t | key
    · rw [cappedHybrid_inl_run, cappedHybrid_inl_run, tsum_probOutput_bind_mul,
        tsum_probOutput_bind_mul]
      simp only [Bool.true_or]
      generalize (b || decide (cappedCall p q t st ∧ inputSide t ∧
        stored (keyOf t) = none ∧ s (keyOf t) = point t)) = b'
      have hle := fun x : spec.Range t × σ × ℕ => ih x.1 x.2 stored b'
      refine (ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hle x) _).trans ?_
      simp only [mul_add, mul_one, ENNReal.tsum_add]
      gcongr
      exact tsum_probOutput_le_one
    · rw [revealImpl_inr_run, revealImpl_inr_run]
      exact ih _ _ _ _

/-- The expectation form of `probEvent_capped_le_aux`, from the count `st.2`. The flag pays for the
input-side calls, and `f` pays for the output-side calls. Each of the first `q` counted calls costs
at most `1 / |T|`. -/
theorem expectedFinal_capped_le_aux (q : ℕ) (Inv : σ × ℕ → Prop) (f : σ × ℕ → ℝ≥0∞)
    (hinv : ∀ t st, Inv st → ∀ x ∈ support ((countImpl impl p t).run st), Inv x.2)
    (hstep : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f x.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then (Fintype.card T : ℝ≥0∞)⁻¹ else 0)
    (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (st : σ × ℕ) (stored : K → Option T), Inv st →
      ∑' s, Pr[= s | $ᵗ (K → T)] * XmssSecurity.expectedFinal
          (cappedHybrid impl inputSide p keyOf point q s) (cappedPotential f) oa (st, stored, false) ≤
        f st + (q - st.2 : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st stored _
    simp only [XmssSecurity.expectedFinal_pure, cappedPotential, Bool.false_eq_true, if_false,
      zero_add]
    rw [ENNReal.tsum_mul_right]
    exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans le_self_add
  | query_bind t k ih =>
    intro st stored hst
    set ε : ℝ≥0∞ := (Fintype.card T : ℝ≥0∞)⁻¹
    rcases t with t | key
    · set I := fun s => cappedHybrid impl inputSide p keyOf point q s
      set mx := (countImpl impl p t).run st
      set P : (K → T) → Prop := fun s => cappedCall p q t st ∧ inputSide t ∧
        stored (keyOf t) = none ∧ s (keyOf t) = point t with hPdef
      set G : (K → T) → spec t × σ × ℕ → Bool → ℝ≥0∞ := fun s x b =>
        XmssSecurity.expectedFinal (I s) (cappedPotential f) (k x.1) (x.2, stored, b) with hGdef
      have hrun : ∀ s, XmssSecurity.expectedFinal (I s) (cappedPotential f)
          (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k) (st, stored, false) =
          ∑' x, Pr[= x | mx] * G s x (decide (P s)) := by
        intro s
        simp only [XmssSecurity.expectedFinal, I, hGdef]
        rw [cappedHybrid_inl_run, tsum_probOutput_bind_mul]
        simp only [Bool.false_or, hPdef]
        rfl
      have hflag : ∀ s x, G s x (decide (P s)) ≤ (if P s then 1 else 0) + G s x false := by
        intro s x
        by_cases h : P s
        · simp only [h, decide_true, if_true, hGdef]
          exact expectedFinal_flag_le impl inputSide p keyOf point q s f (k x.1) x.2 stored false
        · simp [h]
      have hsupp : ∀ x ∈ support mx, x.2.2 = st.2 + if p t then 1 else 0 := by
        intro x hx
        simp only [mx, countImpl, StateT.run_mk, support_map, Set.mem_image] at hx
        obtain ⟨y, -, rfl⟩ := hx
        rfl
      have hhit : ∑' s, Pr[= s | $ᵗ (K → T)] * (if P s then 1 else 0) ≤
          if cappedCall p q t st ∧ inputSide t then ε else 0 := by
        by_cases hc : cappedCall p q t st ∧ inputSide t
        · rw [if_pos hc]
          simp only [mul_ite, mul_one, mul_zero]
          rw [← probEvent_eq_tsum_ite]
          exact (probEvent_mono fun s _ h => h.2.2.2).trans
            (le_of_eq (probEvent_uniform_key_eq (keyOf t) (point t)))
        · rw [if_neg hc]
          have : ∀ s, ¬P s := fun s h => hc ⟨h.1, h.2.1⟩
          simp [this]
      have hcont : ∑' x, Pr[= x | mx] * ∑' s, Pr[= s | $ᵗ (K → T)] * G s x false ≤
          f st + (if cappedCall p q t st ∧ ¬inputSide t then ε else 0) +
            (q - (st.2 + if p t then 1 else 0) : ℕ) * ε := by
        calc _ ≤ ∑' x, Pr[= x | mx] * (f x.2 + (q - (st.2 + if p t then 1 else 0) : ℕ) * ε) := by
              refine ENNReal.tsum_le_tsum fun x => ?_
              by_cases hx : x ∈ support mx
              · gcongr
                have := ih x.1 x.2 stored (hinv t st hst x hx)
                rw [hsupp x hx] at this
                exact this
              · simp [probOutput_eq_zero_of_not_mem_support hx]
          _ = ∑' x, Pr[= x | mx] * f x.2 +
              ∑' x, Pr[= x | mx] * ((q - (st.2 + if p t then 1 else 0) : ℕ) * ε) := by
              simp only [mul_add, ENNReal.tsum_add]
          _ ≤ _ := by
              refine add_le_add (hstep t st hst) ?_
              rw [ENNReal.tsum_mul_right]
              exact mul_le_of_le_one_left' tsum_probOutput_le_one
      calc _ = ∑' s, Pr[= s | $ᵗ (K → T)] * ∑' x, Pr[= x | mx] * G s x (decide (P s)) := by
            exact tsum_congr fun s => congrArg _ (hrun s)
        _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] * ∑' x, Pr[= x | mx] *
            ((if P s then 1 else 0) + G s x false) := by
            gcongr with s x
            exact hflag s x
        _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] * (if P s then 1 else 0) +
            ∑' x, Pr[= x | mx] * ∑' s, Pr[= s | $ᵗ (K → T)] * G s x false := by
            simp only [mul_add, ENNReal.tsum_add]
            refine add_le_add ?_ (le_of_eq ?_)
            · gcongr with s
              rw [ENNReal.tsum_mul_right]
              exact mul_le_of_le_one_left' tsum_probOutput_le_one
            · simp only [← ENNReal.tsum_mul_left]
              rw [ENNReal.tsum_comm]
              simp only [mul_left_comm]
        _ ≤ (if cappedCall p q t st ∧ inputSide t then ε else 0) +
            (f st + (if cappedCall p q t st ∧ ¬inputSide t then ε else 0) +
              (q - (st.2 + if p t then 1 else 0) : ℕ) * ε) := add_le_add hhit hcont
        _ ≤ f st + (q - st.2 : ℕ) * ε := by
            calc _ = f st + (((if cappedCall p q t st ∧ inputSide t then ε else 0) +
                  (if cappedCall p q t st ∧ ¬inputSide t then ε else 0)) +
                  (q - (st.2 + if p t then 1 else 0) : ℕ) * ε) := by ring
              _ = f st + ((if cappedCall p q t st then ε else 0) +
                  (q - (st.2 + if p t then 1 else 0) : ℕ) * ε) := by
                  congr 2
                  by_cases hc : cappedCall p q t st <;> by_cases hin : inputSide t <;> simp [hc, hin]
              _ ≤ f st + (q - st.2 : ℕ) * ε := by
                  gcongr f st + ?_
                  by_cases hpt : p t
                  · by_cases hn : st.2 < q
                    · rw [if_pos ⟨hpt, hn⟩, if_pos hpt, ← one_add_mul]
                      gcongr
                      exact_mod_cast (by omega : 1 + (q - (st.2 + 1)) ≤ q - st.2)
                    · rw [if_neg (fun h => hn h.2), if_pos hpt, zero_add]
                      gcongr
                      omega
                  · rw [if_neg (fun h => hpt h.1), if_neg hpt, zero_add, add_zero]
    · simp only [XmssSecurity.expectedFinal] at ih ⊢
      cases hstored : stored key with
      | some v =>
        simp only [revealImpl_inr_run, hstored, Option.getD_some]
        exact ih v st _ hst
      | none =>
        simp only [revealImpl_inr_run, hstored, Option.getD_none]
        set H : T → (K → T) → ℝ≥0∞ := fun v s => ∑' r, Pr[= r |
          (simulateQ (cappedHybrid impl inputSide p keyOf point q s) (k v)).run
            (st, Function.update stored key (some v), false)] * cappedPotential f r.2 with hHdef
        have hH : ∀ v s w, H v (Function.update s key w) = H v s := by
          intro v s w
          simp only [hHdef]
          rw [revealImpl_run_congr (countImpl impl p) (cappedCall p q) inputSide (fun _ _ _ => False)
            keyOf point (Function.update s key w) s (k v) st _ false]
          intro k' hk'
          have hne : k' ≠ key := by
            rintro rfl
            simp at hk'
          exact Function.update_of_ne hne _ _
        have hih : ∀ v, ∑ s, Pr[= s | $ᵗ (K → T)] * H v s ≤ f st + (q - st.2 : ℕ) * ε := by
          intro v
          have := ih v st (Function.update stored key (some v)) hst
          rwa [tsum_fintype] at this
        rw [tsum_fintype]
        exact sum_uniform_reveal_le key H _ hH hih

/-- The expectation form of `probEvent_hit_capped_le`. A potential `f` that starts at zero, rises in
expectation by at most `1 / |T|` at each of the first `q` counted output-side calls, and is at
least one on `E`, bounds the flag or `E` by `q / |T|`. No query bound is needed. -/
theorem probEvent_capped_expect_le (q : ℕ) (Inv : σ × ℕ → Prop) (f : σ × ℕ → ℝ≥0∞)
    (hinv : ∀ t st, Inv st → ∀ x ∈ support ((countImpl impl p t).run st), Inv x.2)
    (hstep : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f x.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then (Fintype.card T : ℝ≥0∞)⁻¹ else 0)
    (E : σ × ℕ → Prop) (hE : ∀ st, E st → 1 ≤ f st)
    (oa : OracleComp (spec + RevealSpec K T) β) (σ₀ : σ) (hσ₀ : Inv (σ₀, 0)) (hf₀ : f (σ₀, 0) = 0) :
    Pr[fun r => r.2.2.2 = true ∨ E r.2.1 | $ᵗ (K → T) >>= fun s =>
      (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
        ((σ₀, 0), fun _ => none, false)] ≤ q * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hΦ : ∀ st : (σ × ℕ) × (K → Option T) × Bool, (st.2.2 = true ∨ E st.1) →
      1 ≤ cappedPotential f st := by
    rintro st (h | h)
    · simp [cappedPotential, h]
    · exact (hE _ h).trans le_add_self
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] * XmssSecurity.expectedFinal
        (cappedHybrid impl inputSide p keyOf point q s) (cappedPotential f) oa
        ((σ₀, 0), fun _ => none, false) := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        gcongr
        exact XmssSecurity.probEvent_le_expectedFinal _ (cappedPotential f)
          (fun st => st.2.2 = true ∨ E st.1) hΦ oa _
    _ ≤ f (σ₀, 0) + (q - (σ₀, 0).2 : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ :=
        expectedFinal_capped_le_aux impl inputSide p keyOf point q Inv f hinv hstep oa _ _ hσ₀
    _ = _ := by simp [hf₀]

/-- The 128-bit case of `probEvent_capped_expect_le`, as a bound on any event that the flag or `E`
dominates. The bound is `q / 2 ^ 128`. -/
theorem probEvent_le_of_capped_expect {γ : Type} [SampleableType (K → LeanXmss.Digest)]
    (run : ProbComp γ) (event : γ → Prop) (keyOf : κ → K) (point : κ → LeanXmss.Digest) (q : ℕ)
    (Inv : σ × ℕ → Prop) (f : σ × ℕ → ℝ≥0∞)
    (hinv : ∀ t st, Inv st → ∀ x ∈ support ((countImpl impl p t).run st), Inv x.2)
    (hstep : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f x.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0)
    (E : σ × ℕ → Prop) (hE : ∀ st, E st → 1 ≤ f st)
    (oa : OracleComp (spec + RevealSpec K LeanXmss.Digest) β) (σ₀ : σ) (hσ₀ : Inv (σ₀, 0))
    (hf₀ : f (σ₀, 0) = 0)
    (hcouple : Pr[event | run] ≤ Pr[fun r => r.2.2.2 = true ∨ E r.2.1 |
      $ᵗ (K → LeanXmss.Digest) >>= fun s =>
        (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
          ((σ₀, 0), fun _ => none, false)]) :
    Pr[event | run] ≤ q / 2 ^ 128 := by
  have hcard : Fintype.card LeanXmss.Digest = 2 ^ 128 := by
    unfold LeanXmss.Digest LeanXmss.digestBits; exact card_bitVec 128
  have hstep' : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f x.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then
          (Fintype.card LeanXmss.Digest : ℝ≥0∞)⁻¹ else 0 := by
    intro t st hst
    rw [hcard]
    exact_mod_cast hstep t st hst
  refine hcouple.trans ((probEvent_capped_expect_le impl inputSide p keyOf point q Inv f hinv hstep'
    E hE oa σ₀ hσ₀ hf₀).trans (le_of_eq ?_))
  rw [hcard, div_eq_mul_inv]
  norm_num

end CappedExpect

end SigningCappedExpectProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningCappedExpectProof.probEvent_capped_expect_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCappedExpectProof.probEvent_capped_expect_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCappedExpectProof.probEvent_le_of_capped_expect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCappedExpectProof.probEvent_le_of_capped_expect
