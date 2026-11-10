import ThresholdLeanXmssSecurity.Proof.SigningCost

/-!
# The guess and partner lane

`GuessPartnerLaneBound` of `Proof/SigningCost.lean` from two lanes on the logged run.

Proved stages:

* The count of the logged run is the sum of the costs of the calls in its log
  (`loggedRun_count_eq`).
* A call costs one unit as a digest call or as a guess call, and never both (`digestCost_add_guessCost`).
* The two lanes share the budget `q` of the run (`guessPartnerLaneBound`).

Open stages, the hypotheses of `guessPartnerLaneBound`:

* `GuessLaneBound`: a win with a guess costs `2^-128` for each guess call of the log, in expectation.
* `PartnerLaneBound`: a win with a partner costs `2^-128` for each digest call of the log, in
  expectation.

The proof plan of the lanes is in the notes of `Proof/SigningCost.lean` and `Proof/HiddenCore.lean`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningGuessLaneProof

open SigningDescentProof SigningCacheProof SigningCostProof

variable {C : Committee} (prims : Primitives)

/-- A digest input of `Th` at the bottom layer or at the top layer. -/
def DigestInput (input : XmssSecurity.HashInput) : Prop :=
  (∃ P e s, input = XmssSecurity.Concrete.CacheView.encodingInput P e s) ∨
    ∃ P key s, input = XmssSecurity.Concrete.CacheView.topEncodingInput P key s

/-- A call of `H` on a digest input, on the counted copy or on the free copy. -/
def DigestCall : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inr (.inl (.hash input)))) => DigestInput input
  | .inr (.inr (.inl (.hash input))) => DigestInput input
  | _ => False

open Classical in
/-- The cost of a digest call. -/
def digestCost (t : (WorldSpec C).Domain) : ℕ := if DigestCall t then 1 else 0

/-- The cost of a guess call, namely every other counted call. -/
def guessCost (t : (WorldSpec C).Domain) : ℕ := SeedHitProof.signCost t - digestCost t

/-- The sum of a cost over the calls of a log. -/
def logCost (cost : (WorldSpec C).Domain → ℕ) (log : QueryLog (WorldSpec C)) : ℕ :=
  (log.map fun entry => cost entry.1).sum

theorem digestCost_add_guessCost (t : (WorldSpec C).Domain) :
    digestCost t + guessCost t = SeedHitProof.signCost t := by
  have h : digestCost t ≤ SeedHitProof.signCost t := by
    unfold digestCost
    split_ifs with hd
    · rcases t with ((n | (q | y)) | u) | (n | (q | y)) <;>
        simp_all [DigestCall, SeedHitProof.signCost]
    · exact Nat.zero_le _
  unfold guessCost
  omega

theorem logCost_add (log : QueryLog (WorldSpec C)) :
    logCost digestCost log + logCost guessCost log = logCost SeedHitProof.signCost log := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
    simp only [logCost, List.map_cons, List.sum_cons] at ih ⊢
    rw [← digestCost_add_guessCost entry.1]
    omega

/-- The count of the logged run is the sum of the costs of the calls in its log. -/
theorem loggedRun_count_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∀ r ∈ support (loggedRun prims A x), r.2.1.2 = logCost SeedHitProof.signCost r.2.2 := by
  refine SeedHitProof.support_simulateQ_inv (loggedImpl prims)
    (fun s => s.1.2 = logCost SeedHitProof.signCost s.2) ?_ _ _ rfl
  intro t s hs z hz
  simp only [loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp only [countImpl, SeedHitProof.withCount, StateT.run_mk, support_map, Set.mem_image] at hw
  obtain ⟨v, -, rfl⟩ := hw
  simp [hs, logCost, QueryLog.logQuery, QueryLog.singleton]

set_option maxRecDepth 100000 in
/-- The count of the logged run is within the budget. -/
theorem loggedRun_count_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    ∀ r ∈ support (loggedRun prims A x), r.2.1.2 ≤ q := by
  intro r hr
  refine exposedRun_count_le prims A x q hq (r.1, r.2.1) ?_
  rw [← loggedRun_forget, support_map]
  exact ⟨r, hr, rfl⟩

/-- A win without the flag that ends in a guess on the final cache. -/
def WinGuess (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  r.1.1 = (true, false) ∧ ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := finalOf x r top state forgery
    Guess z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
      (XmssSecurity.Bridge.toModelSig z.forgery.signature)

/-- A win without the flag that ends in a partner on the final cache. -/
def WinPartner (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  r.1.1 = (true, false) ∧ ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := finalOf x r top state forgery
    Partner z.cache z.keys.1 z.key (z.honestKey prims) z.forgery.message
      (XmssSecurity.Bridge.toModelSig z.forgery.signature)

/-- The outcome of `exposedRun` in an outcome of the logged run. -/
abbrev forget (r : ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × (HashCache C × ℕ) ×
    QueryLog (WorldSpec C)) : Outcome C :=
  (r.1, r.2.1)

/-! ## The open lanes -/

/-- The guess lane. A win with a guess costs `2^-128` for each guess call of the log, in
expectation. -/
def GuessLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C), x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr[fun r => WinGuess prims x (forget r) | loggedRun prims A x] ≤
      ∑' r, Pr[= r | loggedRun prims A x] * ((logCost guessCost r.2.2 : ℝ≥0∞) / 2 ^ 128)

/-- The partner lane. A win with a partner costs `2^-128` for each digest call of the log, in
expectation. -/
def PartnerLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C), x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr[fun r => WinPartner prims x (forget r) | loggedRun prims A x] ≤
      ∑' r, Pr[= r | loggedRun prims A x] * ((logCost digestCost r.2.2 : ℝ≥0∞) / 2 ^ 128)

end SigningGuessLaneProof

set_option maxRecDepth 100000 in
open SigningCostProof SigningGuessLaneProof in
/-- `GuessPartnerLaneBound` from the two lanes, which share the budget `q`. -/
theorem guessPartnerLaneBound (prims : Primitives) (C : Committee) (guessLane : GuessLaneBound prims C)
    (partnerLane : PartnerLaneBound prims C) : GuessPartnerLaneBound prims C := by
  intro A q x hx hc hq hsmall
  rw [← loggedRun_forget, probEvent_map]
  calc Pr[WinGuessPartner prims x ∘ fun z => (z.1, z.2.1) | loggedRun prims A x]
      ≤ Pr[fun r => WinGuess prims x (forget r) | loggedRun prims A x] +
          Pr[fun r => WinPartner prims x (forget r) | loggedRun prims A x] := by
        refine le_trans (probEvent_mono fun r _ hr => ?_) (probEvent_or_le _ _ _)
        obtain ⟨hwin, top, state, forgery, hsome, h | h⟩ := hr
        · exact Or.inl ⟨hwin, top, state, forgery, hsome, h⟩
        · exact Or.inr ⟨hwin, top, state, forgery, hsome, h⟩
    _ ≤ ∑' r, Pr[= r | loggedRun prims A x] * ((logCost guessCost r.2.2 : ℝ≥0∞) / 2 ^ 128) +
          ∑' r, Pr[= r | loggedRun prims A x] * ((logCost digestCost r.2.2 : ℝ≥0∞) / 2 ^ 128) :=
        add_le_add (guessLane A q x hx hc hq hsmall) (partnerLane A q x hx hc hq hsmall)
    _ ≤ ∑' r, Pr[= r | loggedRun prims A x] * ((q : ℝ≥0∞) / 2 ^ 128) := by
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun r => ?_
        rw [← mul_add, ← ENNReal.add_div]
        by_cases hr : r ∈ support (loggedRun prims A x)
        · refine mul_le_mul_right (ENNReal.div_le_div_right ?_ _) _
          rw [← Nat.cast_add, add_comm, logCost_add, ← loggedRun_count_eq prims A x r hr]
          exact_mod_cast loggedRun_count_le prims A x q hq r hr
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ = (∑' r, Pr[= r | loggedRun prims A x]) * ((q : ℝ≥0∞) / 2 ^ 128) := ENNReal.tsum_mul_right
    _ ≤ (q : ℝ≥0∞) / 2 ^ 128 := mul_le_of_le_one_left bot_le tsum_probOutput_le_one

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.guessPartnerLaneBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.guessPartnerLaneBound
