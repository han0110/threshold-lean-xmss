import ThresholdLeanXmssSecurity.Proof.SigningCappedExpect
import ThresholdLeanXmssSecurity.Proof.SigningEagerGrind
import XmssSecurity.Scan.PerKey

/-!
# The lane 2 potential of leanVM as one capped potential

`probEvent_capped_expect_le` (`SigningCappedExpect`) takes one potential with an upper step bound
of `1 / N` at each counted output-side call. The lane 2 proof of leanVM (`Ghost.collision_le_core`)
is not of that form. This module gives it that form.

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
* `lane2Potential` is `lane2Sum / N²` up to the count `q`, and zero above.
  `compilerPotential` in `SigningLaneHybridCap` uses it, and `viewSum_step` in
  `SigningCompilerPotential` uses `lane2Sum_step`.

## The sign step that returns the base

The threshold adversary sees the base (round 1 releases `ρ_e`, and the base is the answer of the
base call). `Ghost.impl` returns only the signature.

* A step with the same state law has the same expectation of each function of the state
  (`tsum_view_eq`).
* `signWithBase` returns the base and the signature. Its trace entry holds the signature only, so its
  state law is that of `Concrete.scheme.sign` (`evalDist_signWithBaseStep`). The base call keeps the
  leanVM counts (`counts_signWithBaseStep`).
* `ghostEvent` is the lane 2 event of leanVM on a view of the threshold state.
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
    ∑' x, Pr{let z ← mx}[z = x] * F x = ∑' x, Pr{let z ← mx}[z = x] * G x := by
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [prEvent_eq_zero_of_not_mem_support _ hx]

/-- The expectation of a sum of three functions. -/
theorem tsum_add3 {β : Type} (mx : ProbComp β) (F G H : β → ℝ≥0∞) :
    ∑' x, Pr{let z ← mx}[z = x] * (F x + G x + H x) =
      ∑' x, Pr{let z ← mx}[z = x] * F x + ∑' x, Pr{let z ← mx}[z = x] * G x + ∑' x, Pr{let z ← mx}[z = x] * H x := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add]

/-- The uncapped lane 2 sum `f1 + (f3 - f2 / l) + f4`. It is `N ^ 2` times a probability. -/
def lane2Sum (l : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞) (st : σ × ℕ) : ℝ≥0∞ :=
  f1 st + (f3 st - f2 st * l⁻¹) + f4 st

/-- The compensated step. `f1` rises by `cost1`, `f2` rises by at least `l * cost1`, and `f3`
rises by at most `A * openC`. So `f3 - f2 / l` falls by `cost1` and rises by `A * openC`, and the
sum rises by at most `A * openC + N * signedC`. -/
theorem lane2Sum_step {β : Type} (N l A : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞)
    (cost1 openC signedC : κ → σ × ℕ → ℝ≥0∞) (mx : ProbComp (β × (σ × ℕ))) (st : σ × ℕ) (t : κ)
    (h1 : ∑' x, Pr{let z ← mx}[z = x] * f1 x.2 ≤ f1 st + cost1 t st)
    (h2 : f2 st + l * cost1 t st ≤ ∑' x, Pr{let z ← mx}[z = x] * f2 x.2)
    (h3 : ∑' x, Pr{let z ← mx}[z = x] * f3 x.2 ≤ f3 st + A * openC t st)
    (h4 : ∑' x, Pr{let z ← mx}[z = x] * f4 x.2 ≤ f4 st + N * signedC t st)
    (hcomp : ∀ st, f2 st ≤ l * f3 st) (hf2 : ∀ st, f2 st ≠ ⊤) (hA : A ≤ N)
    (hl0 : l ≠ 0) (hlt : l ≠ ⊤) :
    ∑' x, Pr{let z ← mx}[z = x] * lane2Sum l f1 f2 f3 f4 x.2 ≤
      lane2Sum l f1 f2 f3 f4 st + N * (openC t st + signedC t st) := by
  have hle : ∀ s, f2 s * l⁻¹ ≤ f3 s := fun s => by
    calc f2 s * l⁻¹ ≤ l * f3 s * l⁻¹ := mul_le_mul' (hcomp s) le_rfl
      _ = f3 s := by rw [mul_comm l, mul_assoc, ENNReal.mul_inv_cancel hl0 hlt, mul_one]
  have hb : ∀ s, f2 s * l⁻¹ ≠ ⊤ := fun s => ENNReal.mul_ne_top (hf2 s) (ENNReal.inv_ne_top.2 hl0)
  have hd : ∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) + cost1 t st ≤
      (f3 st - f2 st * l⁻¹) + A * openC t st := by
    rcases eq_or_ne (f3 st) ⊤ with htop | htop
    · rw [htop, ENNReal.top_sub (hb st), top_add]; exact le_top
    have hsplit : ∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) +
        (∑' x, Pr{let z ← mx}[z = x] * f2 x.2) * l⁻¹ = ∑' x, Pr{let z ← mx}[z = x] * f3 x.2 := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [mul_assoc, ← mul_add, tsub_add_cancel_of_le (hle x.2)]
    have hlow : f2 st * l⁻¹ + cost1 t st ≤ (∑' x, Pr{let z ← mx}[z = x] * f2 x.2) * l⁻¹ := by
      calc f2 st * l⁻¹ + cost1 t st = (f2 st + l * cost1 t st) * l⁻¹ := by
            rw [add_mul, mul_comm l, mul_assoc, ENNReal.mul_inv_cancel hl0 hlt, mul_one]
        _ ≤ _ := mul_le_mul' h2 le_rfl
    rw [← ENNReal.add_le_add_iff_right (hb st)]
    calc ∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) + cost1 t st + f2 st * l⁻¹ =
          ∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) + (f2 st * l⁻¹ + cost1 t st) := by ring
      _ ≤ ∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) + (∑' x, Pr{let z ← mx}[z = x] * f2 x.2) * l⁻¹ :=
          add_le_add le_rfl hlow
      _ ≤ f3 st + A * openC t st := hsplit.le.trans h3
      _ = (f3 st - f2 st * l⁻¹) + A * openC t st + f2 st * l⁻¹ := by
          rw [add_right_comm, tsub_add_cancel_of_le (hle st)]
  unfold lane2Sum
  rw [tsum_add3]
  calc _ ≤ f1 st + cost1 t st + ∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) +
        (f4 st + N * signedC t st) := add_le_add (add_le_add h1 le_rfl) h4
    _ = f1 st + (∑' x, Pr{let z ← mx}[z = x] * (f3 x.2 - f2 x.2 * l⁻¹) + cost1 t st) +
        (f4 st + N * signedC t st) := by ring
    _ ≤ f1 st + ((f3 st - f2 st * l⁻¹) + A * openC t st) + (f4 st + N * signedC t st) :=
        add_le_add (add_le_add le_rfl hd) le_rfl
    _ ≤ f1 st + ((f3 st - f2 st * l⁻¹) + N * openC t st) + (f4 st + N * signedC t st) := by
        gcongr
    _ = _ := by ring

/-- The capped lane 2 potential. It is `lane2Sum / N ^ 2` up to the count `q`, and zero above. -/
def lane2Potential (q : ℕ) (N l : ℝ≥0∞) (f1 f2 f3 f4 : σ × ℕ → ℝ≥0∞) (st : σ × ℕ) : ℝ≥0∞ :=
  if st.2 ≤ q then lane2Sum l f1 f2 f3 f4 st * (N * N)⁻¹ else 0

end Combine

section Transfer

/-- Two computations whose maps have the same law have the same expectation of a function of the
map. -/
theorem tsum_map_eq {β β' T : Type} (mx : ProbComp β) (my : ProbComp β') (f : β → T) (g : β' → T)
    (hlaw : (f <$> mx) =ᵈ (g <$> my)) (F : T → ℝ≥0∞) :
    ∑' x, Pr{let z ← mx}[z = x] * F (f x) = ∑' y, Pr{let z ← my}[z = y] * F (g y) := by
  rw [← OracleComp.tsum_prEvent_map_mul mx f F, ← OracleComp.tsum_prEvent_map_mul my g F]
  refine tsum_congr fun z => ?_
  rw [hlaw.prEvent_eq (· = z)]

/-- A step whose state law, read through `view`, equals the state law of another step has the same
expectation of every function of the read state. -/
theorem tsum_view_eq {α α' S S' : Type} (mx : ProbComp (α × S)) (my : ProbComp (α' × S'))
    (view : S → S') (hlaw : ((fun x => view x.2) <$> mx) =ᵈ ((fun y => y.2) <$> my))
    (F : S' → ℝ≥0∞) :
    ∑' x, Pr{let z ← mx}[z = x] * F (view x.2) = ∑' y, Pr{let z ← my}[z = y] * F y.2 := by
  rw [← OracleComp.tsum_prEvent_map_mul mx (fun x => view x.2) F,
    ← OracleComp.tsum_prEvent_map_mul my (fun y => y.2) F]
  refine tsum_congr fun z => ?_
  rw [hlaw.prEvent_eq (· = z)]

variable (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
  {α S : Type} (mx : ProbComp (α × S)) (view : S → XmssSecurity.Ghost.State) (st : S)
  (input : (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).Domain)

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
    ((fun x => x.2) <$> (signWithBaseStep secretKey request).run s) =ᵈ
      ((fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey secretKey (.inr request)).run s) := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  have hsign : (simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.scheme.sign secretKey request.leafIndex request.message)).run cache =
      (fun r => (r.1.2, r.2)) <$> (simulateQ XmssSecurity.romImpl
        (signWithBase secretKey request.leafIndex request.message)).run cache := by
    rw [← snd_signWithBase, simulateQ_map, StateT.run_map]
  refine EvalDistEq.of_eq ?_
  rw [XmssSecurity.Ghost.impl_run, XmssSecurity.Ghost.source_sign, signWithBaseStep, StateT.run_mk]
  simp only [Functor.map_map]
  erw [hsign]
  show _ = (fun a : Option XmssSecurity.Signature × XmssSecurity.HashSpec.QueryCache =>
      ((a.2, XmssSecurity.signingCacheTraceUpdate (Sum.inr request) cache a.1 a.2 trace),
        XmssSecurity.Ghost.tick (Sum.inr request) k)) <$> (fun r => (r.1.2, r.2)) <$>
      (simulateQ XmssSecurity.romImpl (signWithBase secretKey request.leafIndex request.message)).run cache
  rw [Functor.map_map]
  simp [XmssSecurity.Ghost.tick, XmssSecurity.Ghost.IsAdvHash, XmssSecurity.signingCacheTraceUpdate]

end SignWithBase


section Split

/-! The count of the threshold run is the second component, and `view` reads the leanVM cache and
trace from the rest. `f1`, `f2` and `f4` do not read the count, so their transfer needs the law of
the view only. -/

variable (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
  {α S : Type} (mx : ProbComp (α × (S × ℕ)))
  (view : S → XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace) (st : S × ℕ)
  (input : (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).Domain) (k : ℕ)

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

/-- The comparison `hcomp` of `lane2Sum_step` for the leanVM potentials. It is
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

end Ghost

end SigningLane2Proof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.evalDist_signWithBaseStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.evalDist_signWithBaseStep

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2Proof.f2_le_landing_mul_f3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2Proof.f2_le_landing_mul_f3
