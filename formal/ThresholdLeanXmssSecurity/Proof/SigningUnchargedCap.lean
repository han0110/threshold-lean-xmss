import ThresholdLeanXmssSecurity.Proof.SigningAssembly

/-!
# A shared cap for the input and cached-partner rows

The capped potential is the input-hit indicator plus the output potential.
Its expectation therefore bounds the sum of the two event probabilities,
including executions on which both events occur. No disjointness or second
query budget is needed. This strengthens the union bound in `SigningLane2`.

The pinned and current leanVM expectation and capped-lane modules were searched.
We reuse their `expectedFinal` and the threshold `expectedFinal_capped_le_aux`;
the new step is retaining both summands when applying the potential bound.

`input_cached_le_of_capped` transports the two original signing rows into that
single hybrid. Its concrete transports and step invariant remain to be proved;
`InputCachedLaneCap` states the exact unresolved cap. `uncharged_le_with_rows`
retains the top and absent-start probabilities separately, and the original
`UnchargedLaneCap` follows when both have zero mass. No D17 model change is made.
The concurrent A3 audit also found that `CachedPartnerRow` uses a global cached-selection
flag rather than the forged key's flag (A40). No transport from that row to the
leanVM event is asserted here.
-/

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningUnchargedCapProof

open SigningOpeningProof SigningCappedExpectProof SigningLane2Proof

attribute [local instance] Classical.propDecidable

/-- The two probabilities are charged to the two summands of the potential. -/
theorem flag_add_event_le_expectedFinal {κ σ β K T : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT ((σ × ℕ) × (K → Option T) × Bool) ProbComp))
    (f : σ × ℕ → ℝ≥0∞) (E : σ × ℕ → Prop) (hE : ∀ st, E st → 1 ≤ f st)
    (oa : OracleComp spec β) (initial : (σ × ℕ) × (K → Option T) × Bool) :
    Pr[fun r => r.2.2.2 = true | (simulateQ impl oa).run initial] +
      Pr[fun r => E r.2.1 | (simulateQ impl oa).run initial] ≤
      XmssSecurity.expectedFinal impl (cappedPotential f) oa initial := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add,
    XmssSecurity.expectedFinal]
  apply ENNReal.tsum_le_tsum
  intro r
  unfold cappedPotential
  rw [mul_add]
  apply add_le_add
  · split_ifs <;> simp
  · split_ifs with he
    · exact le_mul_of_one_le_right' (hE _ he)
    · exact zero_le

section Capped

variable {κ σ β K T : Type} {spec : OracleSpec κ}
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T] [SampleableType (K → T)]
  (impl : QueryImpl spec (StateT σ ProbComp)) (inputSide p : κ → Prop)
  (keyOf : κ → K) (point : κ → T)

/-- One cap bounds the sum of the input-side hit and the output-side event. -/
theorem probEvent_flag_add_event_le (q : ℕ) (Inv : σ × ℕ → Prop) (f : σ × ℕ → ℝ≥0∞)
    (hinv : ∀ t st, Inv st → ∀ x ∈ support ((countImpl impl p t).run st), Inv x.2)
    (hstep : ∀ t st, Inv st →
      ∑' x, Pr[= x | (countImpl impl p t).run st] * f x.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then (Fintype.card T : ℝ≥0∞)⁻¹ else 0)
    (E : σ × ℕ → Prop) (hE : ∀ st, E st → 1 ≤ f st)
    (oa : OracleComp (spec + RevealSpec K T) β) (initial : σ)
    (hinit : Inv (initial, 0)) (hf : f (initial, 0) = 0) :
    let run := $ᵗ (K → T) >>= fun s =>
      (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
        ((initial, 0), fun _ => none, false)
    Pr[fun r => r.2.2.2 = true | run] + Pr[fun r => E r.2.1 | run] ≤
      q * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  dsimp only
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] * XmssSecurity.expectedFinal
        (cappedHybrid impl inputSide p keyOf point q s) (cappedPotential f) oa
        ((initial, 0), fun _ => none, false) := by
      apply ENNReal.tsum_le_tsum
      intro s
      rw [← mul_add]
      exact mul_le_mul_right (flag_add_event_le_expectedFinal _ f E hE oa _) _
    _ ≤ f (initial, 0) + (q - (initial, 0).2 : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ :=
      expectedFinal_capped_le_aux impl inputSide p keyOf point q Inv f hinv hstep oa _ _ hinit
    _ = _ := by simp [hf]

end Capped

section Lane2

variable {κ σ : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (StateT σ ProbComp))
  (p inputSide : κ → Prop)

/-- The compensated leanVM potential pays both event probabilities under one cap.
The potential calculation is the one in `SigningLane2Proof.probEvent_lane2_le`;
only the final use of the averaged expectation retains the sum instead of the union. -/
theorem probEvent_lane2_sum_le {β K T : Type} [Fintype K] [DecidableEq K] [Fintype T] [Nonempty T]
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
    let run := $ᵗ (K → T) >>= fun s =>
      (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
        ((σ₀, 0), fun _ => none, false)
    Pr[fun r => r.2.2.2 = true | run] +
      Pr[fun r => E r.2.1 ∧ r.2.1.2 ≤ q | run] ≤ q * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hN0 : (Fintype.card T : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card T : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine probEvent_flag_add_event_le impl inputSide p keyOf point q Inv
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

end Lane2

section Signing

open LeanXmss ThresholdLeanXmss SigningAssemblyProof SigningUnchargedLoggedProof

variable {C : Committee} (prims : Primitives)

/-- The exact remaining A6 cap, with only the two D17 rows removed. -/
def InputCachedLaneCap (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[InputHitRow prims x | jointRun prims A x] +
      Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x] ≤ (q : ℝ≥0∞) / 2 ^ 128

section Transport

variable {κ σ β K : Type} {spec : OracleSpec κ}
  [Fintype K] [DecidableEq K] [SampleableType (K → Digest)]
  (impl : QueryImpl spec (StateT σ ProbComp)) (inputSide p : κ → Prop)
  (keyOf : κ → K) (point : κ → Digest)

/-- One hybrid for both signing rows. -/
def cappedRun (q : ℕ) (oa : OracleComp (spec + RevealSpec K Digest) β) (initial : σ) :=
  $ᵗ (K → Digest) >>= fun s =>
    (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
      ((initial, 0), fun _ => none, false)

/-- Separate marginal transports into the same hybrid suffice for the sum.
The two events need not be disjoint, and receive no separate query budgets. -/
theorem input_cached_le_of_capped
    (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (q : ℕ) (Inv : σ × ℕ → Prop) (f : σ × ℕ → ℝ≥0∞)
    (hinv : ∀ t st, Inv st → ∀ r ∈ support ((countImpl impl p t).run st), Inv r.2)
    (hstep : ∀ t st, Inv st →
      ∑' r, Pr[= r | (countImpl impl p t).run st] * f r.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0)
    (E : σ × ℕ → Prop) (hE : ∀ st, E st → 1 ≤ f st)
    (oa : OracleComp (spec + RevealSpec K Digest) β) (initial : σ)
    (hinit : Inv (initial, 0)) (hf : f (initial, 0) = 0)
    (hinput : Pr[InputHitRow prims x | jointRun prims A x] ≤
      Pr[fun r => r.2.2.2 = true | cappedRun impl inputSide p keyOf point q oa initial])
    (hpartner : Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x] ≤
      Pr[fun r => E r.2.1 | cappedRun impl inputSide p keyOf point q oa initial]) :
    Pr[InputHitRow prims x | jointRun prims A x] +
      Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by
    unfold Digest digestBits
    exact card_bitVec 128
  have hstep' : ∀ t st, Inv st →
      ∑' r, Pr[= r | (countImpl impl p t).run st] * f r.2 ≤
        f st + if cappedCall p q t st ∧ ¬inputSide t then
          (Fintype.card Digest : ℝ≥0∞)⁻¹ else 0 := by
    simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using hstep
  have hcap := probEvent_flag_add_event_le impl inputSide p keyOf point q Inv f
    hinv hstep' E hE oa initial hinit hf
  refine (add_le_add hinput hpartner).trans ?_
  simpa only [cappedRun, hcard, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hcap

end Transport

/-- The two D17 rows appear separately, without hiding their mass in the lane cap. -/
theorem uncharged_le_with_rows
    (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (hcap : InputCachedLaneCap prims ρ) (A : TsigAdversary C) (q : ℕ)
    (x : SigningSecurityProof.Keys3 C) (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr[UnchargedRow prims x | jointRun prims A x] +
      Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128 + Pr[TopRow prims x | jointRun prims A x] +
        Pr[AbsentRow prims x | jointRun prims A x] := by
  have hrows := (probEvent_or_le (jointRun prims A x) (InputHitRow prims x)
    (fun r => TopRow prims x r ∨ AbsentRow prims x r)).trans
      (add_le_add le_rfl (probEvent_or_le (jointRun prims A x) (TopRow prims x) (AbsentRow prims x)))
  change Pr[UnchargedRow prims x | jointRun prims A x] ≤ _ at hrows
  refine (add_le_add hrows le_rfl).trans ?_
  calc
    _ = (Pr[InputHitRow prims x | jointRun prims A x] +
        Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x]) +
        Pr[TopRow prims x | jointRun prims A x] + Pr[AbsentRow prims x | jointRun prims A x] := by ac_rfl
    _ ≤ _ := add_le_add (add_le_add (hcap A q x hx hkeys hq hsmall) le_rfl) le_rfl

/-- Restoring the original cap requires both D17 rows to have zero mass. -/
theorem unchargedLaneCap_of_inputCached
    (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (hcap : InputCachedLaneCap prims ρ)
    (htop : ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
      x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
      ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
      (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
      q < 2 ^ 127 → Pr[TopRow prims x | jointRun prims A x] = 0)
    (habsent : ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
      x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
      ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
      (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
      q < 2 ^ 127 → Pr[AbsentRow prims x | jointRun prims A x] = 0) :
    UnchargedLaneCap prims ρ := by
  intro A q x hx hkeys hq hsmall
  have h := uncharged_le_with_rows prims ρ hcap A q x hx hkeys hq hsmall
  simpa only [htop A q x hx hkeys hq hsmall, habsent A q x hx hkeys hq hsmall, add_zero] using h

end Signing

/-- info: 'ThresholdLeanXmssSecurity.SigningUnchargedCapProof.flag_add_event_le_expectedFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flag_add_event_le_expectedFinal

/-- info: 'ThresholdLeanXmssSecurity.SigningUnchargedCapProof.probEvent_flag_add_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_flag_add_event_le

/-- info: 'ThresholdLeanXmssSecurity.SigningUnchargedCapProof.probEvent_lane2_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_lane2_sum_le

/-- info: 'ThresholdLeanXmssSecurity.SigningUnchargedCapProof.input_cached_le_of_capped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms input_cached_le_of_capped

/-- info: 'ThresholdLeanXmssSecurity.SigningUnchargedCapProof.uncharged_le_with_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uncharged_le_with_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningUnchargedCapProof.unchargedLaneCap_of_inputCached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unchargedLaneCap_of_inputCached

end ThresholdLeanXmssSecurity.SigningUnchargedCapProof
