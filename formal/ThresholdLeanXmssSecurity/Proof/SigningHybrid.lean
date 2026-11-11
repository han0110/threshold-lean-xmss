import ThresholdLeanXmssSecurity.Proof.SigningUnchargedLogged

/-!
# The budget check of the uncharged flag

This module checks the budget of `SigningUnchargedLoggedProof.UnchargedFlag` before any hybrid of
`SeedHitProof.signImpl` is built. The check fails. So the module holds the traces and the one fix
that the check proves, and it does not build the hybrid.

## The rule of the lane

* `SigningOpeningProof.probEvent_le_of_capped` gives `q / 2^128` for the uncharged lane.
* The flag of that tool is decided at one call from the state before the call and the answer.
* Each counted call has one unit of `2^-128`, for every state (`hout`).
* The charged lane has the other unit of each call (`SigningPartnerLinkProof`).

## Trace 1. The commitment counterexample raises the flag on the charged branch

The counterexample is the comment `COUNTEREXAMPLE TO THE EARLIER ONE-UNIT ROUTE ONLY` of
`SigningGuessProof`. It uses `N = 2^128`, `M = 2^120` and `q = M + 2^113`.

* The adversary makes `M` commitment calls and finds `ρ'` with commitment `c_e`.
* With `ρ' = ρ_e`, the call is an input-side hit on `ρ_e`. This has probability `M / N`.
* With `ρ' ≠ ρ_e`, the event is `AlternativeCommitment`. This also has probability about `M / N`.
* Both branches end in `Guess` or `Partner` with probability at least `(7/8)^2`.
* The canonical selection uses `ρ_e`, so it is absent on the second branch. Then `bottomOpened` is
  `chainLength - 1`, the forgery is a `Guess`, and `guess_hiddenInputHit` gives `HiddenInputHit`.
* So `Pr[UnchargedFlag] ≥ (147/128) · M / N`, but the capped tool gives `q / N = (129/128) · M / N`.

`UnchargedFlagCoupling` thus fails for this adversary. The second branch belongs to the charged lane
(`commitmentCost`), and `UnchargedWinLogged` already excludes it. `UnchargedFlagSound` adds the
exclusion to the flag. Then each commitment call has one target in this lane, `ρ_e` on the input
side, and its output target `c_e` stays in the charged lane.

## Trace 2. The window after round 1 needs more than one unit at one call

The valid digests are `K` with `2^107 ≤ K ≤ 2^108`, so a trial is valid with probability `v = K / N`
and `2^-21 ≤ v ≤ 2^-20`.

1. Before round 1 at `e`, the adversary makes `2^30` encoding calls at `e` on messages other than
   `m0`. The valid digests form a set `P` with `|P| ≥ 2^9` in expectation.
2. Round 1 at `e` binds `m0` and releases `ρ_e`. The adversary calls
   `randomizerInput P bottomLayer e ρ_e m0` and gets the base `b`.
3. The adversary calls the scan line from `b` in order. The first valid trial `S` is the selection,
   after about `1 / v ≤ 2^21` calls.
4. The grind of round 2 selects `S`, which the adversary called first. So `FreshSelection` is false.
5. If the digest of `S` is in `P`, the adversary forges with the partner input. This is
   `BottomPartnerCase` with a selection that is not fresh.

The call on `S` is the first call that fixes the selected digest. In that state its hazard is
`|P| / N ≥ 2^9 · 2^-128`, so it needs `2^9` units. The win has probability about `2^30 / N`, inside
`q / N`. So the lane bound is not refuted. Only a flag that is decided at one call fails.

* The hit cannot move to the earlier calls. Before round 1 the target is the selected digest of a
  message that the adversary binds later, so no state fixes one target.
* A presampled selected digest for each message gives one target for each message. An earlier call
  then meets `2^30` targets or more.

leanVM pays this order with the pending risk of lane 1 (`uniformDigest_sign_bonus_sum_le`). That is
an expectation over the calls of `P`, not a cap at one call.

## Trace 3. The cached selection before round 1 needs more than one unit at one call

1. Before round 1 at `e`, the cache holds `S' = encodingInput P e (m0, R0)` with a valid digest, and
   a second input `F` at `e` with the same digest. This state has positive probability.
2. Round 1 binds `m0` and releases `ρ_e`.
3. The first call of `randomizerInput P bottomLayer e ρ_e m0` fixes `b`. The adversary can make it
   in the window, or the grind of round 2 makes it. Either way it is a counted call after round 1.
4. `S'` is the selection if `b = R0 - k` and the `k` trials between are invalid. So its hazard is
   `Σ_k 2^-128 · (1 - v)^k ≈ 2^-128 / v ≥ 2^20 · 2^-128`.

The other order fails too. A flag at the call that makes the collision of `F` and `S'` meets every
cached valid digest at `e`, so it needs two units once two such digests are cached.

leanVM pays this case with the potential `f1` of lane 2 (`capped_cachedSelection_probability_le_expectedDigest`),
which weighs each cached digest by the reach mass of a hidden base. Its base is sampled inside the
signing oracle. Here the base is a counted call after round 1 (FIX.md, Track B, item 4), so that lemma
does not apply as it is.

## Two potentials on one call

An encoding call at `e` before round 1 can meet a selection that is cached before round 1 (Trace 3)
or a selection that the adversary calls in the window (Trace 2). At the time of the call both are
possible. The potential `f1` charges it one unit, and the pending risk charges it one more unit. Both
charges fall in this lane, because the charged lane spends the unit of the call on the fresh
partner. So the available accounting needs two units for this call. One unit can still hold for a
single argument that covers both orders, but no lemma of leanVM or of this repository gives it.

## The form of the coupling

`UnchargedFlagCoupling` lets the prover choose the hybrid. A hybrid that makes `q` calls, each with
one output target, raises its flag with probability `1 - (1 - 2^-128)^q`. So the coupling is the bound
`Pr[flag] ≤ 1 - (1 - 2^-128)^q` itself. A planting coupling of `signImpl` is one way to prove it, but
Traces 2 and 3 show that such a coupling with a flag decided at one call cannot hold.

## What this module proves

* `unchargedFlagSound_of_win` shows that every uncharged win on the log raises `UnchargedFlagSound`.
* `unchargedLaneBoundLogged_of_soundCoupling` and `hiddenCoreAt_of_soundCoupling` are the routes of
  `SigningUnchargedLoggedProof` with the sound flag.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningHybridProof

open LeanXmss ThresholdLeanXmss SigningCostProof SigningPartnerBoundProof SigningUnchargedLoggedProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- `UnchargedFlag` without a commitment collision. A commitment collision is in the charged lane. -/
def UnchargedFlagSound (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  UnchargedFlag prims x w ∧ ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 w.2.1.1

set_option maxRecDepth 100000 in
/-- An uncharged win on the log raises the sound flag. -/
theorem unchargedFlagSound_of_win (hlink : FreshPartnerLink (C := C) prims) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) (hw : w ∈ support (jointRun prims A x))
    (hu : UnchargedWinLogged prims x (w.1.1, w.2)) : UnchargedFlagSound prims x w :=
  ⟨unchargedFlag_of_win prims hlink A x w hw hu, fun h => hu.2 (Or.inl (Or.inr (Or.inl h)))⟩

/-- `UnchargedFlagCoupling` for the sound flag. -/
def UnchargedFlagSoundCoupling : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    ∃ (κ σ β K : Type) (spec : OracleSpec κ) (_ : Fintype K) (_ : DecidableEq K)
      (_ : SampleableType (K → Digest)) (impl : QueryImpl spec (StateT σ ProbComp))
      (inputSide p : κ → Prop) (keyOf : κ → K) (point : κ → Digest)
      (outHit : (t : κ) → σ × ℕ → spec t × (σ × ℕ) → Prop)
      (oa : OracleComp (spec + SigningOpeningProof.RevealSpec K Digest) β) (σ₀ : σ),
      (∀ t σ₁ n, p t → ¬inputSide t →
        Pr[outHit t (σ₁, n) | (SigningOpeningProof.countImpl impl p t).run (σ₁, n)] ≤
          (2 ^ 128 : ℝ≥0∞)⁻¹) ∧
      Pr[UnchargedFlagSound prims x | jointRun prims A x] ≤
        Pr[fun r => r.2.2.2 = true | $ᵗ (K → Digest) >>= fun s =>
          (simulateQ (SigningOpeningProof.revealImpl (SigningOpeningProof.countImpl impl p)
            (SigningOpeningProof.cappedCall p q) inputSide outHit keyOf point s) oa).run
              ((σ₀, 0), fun _ => none, false)]

set_option maxRecDepth 100000 in
/-- The uncharged lane on the log from the fresh partner link and the sound coupling. -/
theorem unchargedLaneBoundLogged_of_soundCoupling (hlink : FreshPartnerLink (C := C) prims)
    (hcouple : UnchargedFlagSoundCoupling (C := C) prims) : UnchargedLaneBoundLogged (C := C) prims := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨κ, σ, β, K, spec, _, _, _, impl, inputSide, p, keyOf, point, outHit, oa, σ₀, hout, hflag⟩ :=
    hcouple A q x hx hkeys hq hsmall
  have hle : Pr[UnchargedWinLogged prims x | loggedRun prims A x] ≤
      Pr[UnchargedFlagSound prims x | jointRun prims A x] := by
    rw [← jointRun_logged, probEvent_map]
    exact probEvent_mono fun w hw hu => unchargedFlagSound_of_win prims hlink A x w hw hu
  exact hle.trans (SigningOpeningProof.probEvent_le_of_capped impl inputSide p
    (jointRun prims A x) (UnchargedFlagSound prims x) keyOf point q outHit hout oa σ₀ hflag)

/-- The signing core from the classification of the honest calls and the sound coupling. -/
theorem hiddenCoreAt_of_soundCoupling (hclass : SelectionClassification (C := C) prims)
    (hcouple : UnchargedFlagSoundCoupling (C := C) prims) : SigningCoreProof.HiddenCoreAt prims C :=
  hiddenCoreAt_of_logged prims
    (unchargedLaneBoundLogged_of_soundCoupling prims (freshPartnerLink_of_classification prims hclass) hcouple)

end SigningHybridProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningHybridProof.unchargedLaneBoundLogged_of_soundCoupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningHybridProof.unchargedLaneBoundLogged_of_soundCoupling

/--
info: 'ThresholdLeanXmssSecurity.SigningHybridProof.hiddenCoreAt_of_soundCoupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningHybridProof.hiddenCoreAt_of_soundCoupling
