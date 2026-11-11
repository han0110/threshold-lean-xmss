import ThresholdLeanXmssSecurity.Proof.SigningGuessLink

/-!
# The bottom partner half of the uncharged lane

A bottom partner is the second case of `SigningGuessProof.winResidual_guess_or_bottomPartner`. The
forged digest input at the key `e` of the forgery differs from the selected input `hk.selected`, and
both give the same digest. `BottomPartnerCase` names this case on an outcome of `exposedRun`, in the
style of `SigningGuessLinkProof.GuessCase`.

The leanVM proof of the partner charges two units of `2^-128` for each encoding call, one in each of
its two lanes. The uncharged lane here has one unit. So this module moves the leanVM lane 1 part of
the bottom partner into the charged lane, where the unit of each bottom digest call is free. The
accounting trace below gives the numbers. It traces the charges of the proof. It is not an attack.

## The new split

* `bottomDigestCost` is `digestCost` minus the top digest calls. On a digest call,
  `structuralHitCost` is zero (`structuralHitCost_zero_digest`) and `commitmentCost` is zero
  (`commitment_not_digest`). The top partner charges only top digest calls
  (`topDigest_rawCost_le`, `resolvedTopPartner_bound_topDigest`). So the charged lane does not use
  the unit of a bottom digest call.
* `ChargedOutput2` is `ChargedOutput` or a bottom partner event `partner`. `UnchargedWin2` is the
  rest of the win.
* `chargedOutput2_bound` bounds `ChargedOutput2` by `q / 2^128`, if `partner` costs one unit for
  each bottom digest call (`BottomPartnerBound`). The sum of the costs is the sum of
  `source_output_costs_le`.
* `hiddenCoreAt_of_split` gives `HiddenCoreAt` from `BottomPartnerBound` and `UnchargedLaneBound2`.

The event `partner` is a parameter. It must be the leanVM lane 1 partner, namely the selection at
`e` reads a digest input that is not in the cache when the grind starts, and a call before or after it
meets the selected digest. An outcome of `exposedRun` holds only the final cache, so it cannot tell a
fresh selection from a cached one. The event needs a run that records the cache at the start of each
grind, as `SigningCacheEntry.initialCache` of leanVM does.

## What stays in `UnchargedWin2`

* The Guess. It is input side, a hidden chain value below the opened position.
  `SigningGuessLinkProof.probEvent_guess_le` links it to `HiddenInputHit`.
* The true opening probes. They are input side, `ρ_e` before its release.
* The cached selection of leanVM lane 2. The selected input is in the cache when the grind starts.
  Before round 1 at `e`, that call guesses the hidden base, which is input side. The partner match
  is output side, two cached digests meet. leanVM charges it with the potential `f1`, which
  weighs each cached digest by the reach mass `W` of a hidden base.
* The window after round 1 at `e`. The adversary can learn the base and query the scan line before
  the grind. Then the selection is cached without a guess. The digest is fixed by the first call at
  the first valid trial, so the risk is output side. leanVM has no such window.

## The leanVM argument (pinned package, the local checkout agrees)

The signer of leanVM samples a uniform `base` in the signing oracle and scans `base + k`
(`precomputedCappedSign`, `IdealStatement.lean`). `cappedWinning_encoding_event_trace_postSigning_decomposition`
splits an encoding win into three cases of one signing entry.

* `FreshSigningEncodingCollision`. The selected input is not in the cache when the signing starts.
  An earlier query at another input has the same digest.
* `PostSigningFreshForgedEncodingCollision`. The selected input is fresh. A later query at the
  forged input has the same digest.
* `CachedSelectionCollision`. The selected input is in the cache when the signing starts. Another
  cached input has the same digest. This is the open case of `SigningGuessLink`.

Lane 1 holds the two fresh cases. The encoding monitor `CappedEncodingMonitor.runObserved` fires on
both orders (`runObserved_empty_eq_true_of_query_before_sign_of_valid`,
`runObserved_empty_eq_true_of_sign_before_query_of_valid`). The charge is as follows.

* `applyUniformQueryMonitor_true_probability_le` charges each query one unit (`fuel.succ`).
* At an unsigned leaf index, a query with a valid digest adds `1 / |validDigests|` to
  `pendingRisk`. A uniform output is valid with probability `|validDigests| / 2^128`, so the
  expected charge is `2^-128` (`uniformDigest_valid_bonus_sum_eq`).
* A sign attempt charges no unit (`applyUniformSignAttemptMonitor_true_probability_le` keeps `fuel`).
  Its first valid digest is uniform on `validDigests`, so it meets a pending digest with probability
  `|pending e| / |validDigests|`. The pending risk pays this (`uniformDigest_sign_bonus_sum_le`).
* At a signed leaf index, a query meets the fixed signed digest with probability `2^-128`.

Lane 2 holds the cached case (`capped_cachedSelection_probability_le_expectedDigest`).

* `PreBad` says that a first entry selects a cached input that already has a partner. `PostBad`
  says that a first entry selects a cached input and a later query repeats its digest.
* `Ghost.collision_le` bounds both by `E[encoding queries] / 2^128` for a count below `2^127`. So
  lane 2 charges one unit for each encoding call on average. The potential `f1` rises by `aCost` on
  each fresh encoding query at an unsigned leaf index, and `f4` rises by `2^128` on each encoding
  query at a signed leaf index, both on the scale `2^256`.

`capped_two_lane_loss_budget` adds the lanes to `(2q + 2^20) / 2^128`. Lane 1 shares its `q` with the
chain and top hits, and lane 2 shares its `q` with the structural collisions.

## The accounting trace of the leanVM proof

Take one encoding call at key `e` before the selection at `e`.

* Lane 1 charges it `2^-128` for the fresh selection (pending risk).
* Lane 2 charges it `2^-128` on average for the cached selection (`f1`, through
  `Ghost.collision_le`).
* At the time of the call, the selection at `e` can still be fresh or cached. So the leanVM proof
  charges both, and the partner costs `2 · 2^-128` for this call in that proof.

In this repository the two lanes have these budgets.

* `ChargedOutput` costs `hitCost + commitmentCost + digestCost ≤ q` (`chargedOutput_bound_of_cost`). So each
  bottom encoding call already pays one unit there.
* `UnchargedLaneBound` gives `q / 2^128` to all of `UnchargedWin`. So each bottom encoding call has
  one unit there, and the Guess and the true opening probes share it.

The leanVM proof thus charges the bottom partner in `UnchargedWin` `2 · 2^-128` for each call before
the selection, and that lane has `2^-128`. A flag that asks for a call at `e` with an input other than
the selected input and an output equal to the selected digest is the union of the two lane 1 orders
and the lane 2 cases. leanVM bounds it only with both lanes. No adversary in leanVM shows that one
unit is too few.

`signingHashError` is `q / 2^127`, two units for each call. So the gap is in the split of
`ChargedOutput` and `UnchargedWin` in `SigningGuessProof`, not in `Statement.lean`.

There is one more gap. The capped tool `SigningOpeningProof.revealImpl` makes each call input side
or output side, never both. A call of `encodingInput` before the selection carries the selected
digest as an output target and, before the first `round1` at `e`, the hidden base as an input
target.

## A difference to leanVM

Round 1 at `e` binds `e` to its message and releases `ρ_e`. The adversary can then learn the base
`H(randomizerInput ρ_e m)` before the grind of round 2. It can query the scan line itself, so the
selected input can be cached at the selection without a guess. leanVM samples the base inside the
signing oracle, so its lane 2 potential (the reach mass `W`) assumes a hidden base. It does not
cover this window directly.

-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningPartnerLinkProof

open LeanXmss ThresholdLeanXmss

variable {C : Committee} (prims : Primitives)

/-- The bottom partner case of `SigningGuessProof.winResidual_guess_or_bottomPartner` on an outcome
of `exposedRun`. -/
def BottomPartnerCase (x : SigningSecurityProof.Keys3 C) (r : SigningCostProof.Outcome C) : Prop :=
  ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := SigningCostProof.finalOf x r top state forgery
    let hk := z.honestKey prims
    let signature := XmssSecurity.Bridge.toModelSig forgery.signature
    ∃ selected, hk.selected = some selected ∧ selected ≠ (forgery.message, signature.randomness) ∧
      XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
          x.1 z.key selected =
        XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
          x.1 z.key (forgery.message, signature.randomness)

/-- A residual win is a Guess or a bottom partner. -/
theorem winResidual_guessCase_or_bottomPartnerCase (x : SigningSecurityProof.Keys3 C)
    (r : SigningCostProof.Outcome C) (hr : SigningGuessProof.WinResidual prims x r) :
    SigningGuessLinkProof.GuessCase prims x r ∨ BottomPartnerCase prims x r := by
  obtain ⟨top, state, forgery, hm, hguess | hpartner⟩ :=
    SigningGuessProof.winResidual_guess_or_bottomPartner prims x r hr
  · exact Or.inl ⟨top, state, forgery, hm, hguess⟩
  · exact Or.inr ⟨top, state, forgery, hm, hpartner⟩


section Split

attribute [local instance] Classical.propDecidable

/-- The cost of a digest call that is not a top digest call. The top partner of `ChargedOutput`
charges only top digest calls (`topDigest_rawCost_le`), so this part of `digestCost` is free in
the charged lane. -/
def bottomDigestCost (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) : ℕ :=
  SigningGuessLaneProof.digestCost t -
    SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t

theorem topDigest_add_bottomDigestCost (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) :
    SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t + bottomDigestCost x t =
      SigningGuessLaneProof.digestCost t := by
  have h : SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t ≤
      SigningGuessLaneProof.digestCost t := by
    convert SigningGuessProof.topDigest_rawCost_le (C := C) x.1 t
  unfold bottomDigestCost
  omega

/-- The top partner charged to the top digest calls alone. -/
theorem resolvedTopPartner_bound_topDigest (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1 |
        SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1)) := by
  convert SigningGuessProof.cachePotential_bound_source prims A x (SigningGuessProof.anyTopDigestInput x.1)
    (SigningGuessProof.topPartnerPotential x) (fun cache => ∃ key, SigningGuessProof.ResolvedTopPartner x key cache)
    (SigningGuessProof.topPartnerPotential_zero x)
    (fun cache he => SigningGuessProof.topPartnerPotential_terminal x cache he)
    (fun input cache => by convert SigningGuessProof.topPartnerPotential_step x input cache using 3)


variable (partner : SigningSecurityProof.Keys3 C → SigningCostProof.Outcome C → Prop)

/-- The charged lane with a bottom partner event added. -/
def ChargedOutput2 (x : SigningSecurityProof.Keys3 C) (r : SigningCostProof.Outcome C) : Prop :=
  SigningGuessProof.ChargedOutput prims x r ∨ partner x r

/-- The win that the new charged lane leaves. -/
def UnchargedWin2 (x : SigningSecurityProof.Keys3 C) (r : SigningCostProof.Outcome C) : Prop :=
  r.1.1 = (true, false) ∧ ¬ChargedOutput2 prims partner x r

/-- The bottom partner event costs one unit for each bottom digest call. -/
def BottomPartnerBound : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C),
    Pr[partner x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x (bottomDigestCost x)

/-- The fixed-cap bound of the new uncharged lane. -/
def UnchargedLaneBound2 : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[UnchargedWin2 prims partner x | SigningDescentProof.exposedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128

set_option maxRecDepth 100000 in
theorem chargedOutput2_bound (hpartner : BottomPartnerBound prims partner) (A : TsigAdversary C)
    (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr[ChargedOutput2 prims partner x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  obtain ⟨T, hhit⟩ := SigningGuessProof.hit_bound_structural_cost prims A q x hx hkeys hq hsmall
  replace hhit : Pr[SigningCostProof.WinHit prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningGuessProof.structuralHitCost x T) := hhit
  have hcost := SigningGuessProof.source_output_costs_le prims A x T q hq
  have hdigest : SigningGuessProof.sourceExpectedCost prims A x SigningGuessLaneProof.digestCost =
      SigningGuessProof.sourceExpectedCost prims A x
          (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1)) +
        SigningGuessProof.sourceExpectedCost prims A x (bottomDigestCost x) := by
    rw [← SigningGuessProof.sourceExpectedCost_add]
    congr 1
    funext t
    exact (topDigest_add_bottomDigestCost x t).symm
  let run := SigningDescentProof.exposedRun prims A x
  have h1 := probEvent_or_le run (SigningGuessProof.ChargedOutput prims x) (partner x)
  have h2 := probEvent_or_le run (SigningCostProof.WinHit prims x)
    (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1 ∨
      ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have h3 := probEvent_or_le run (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (fun r => ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have hsum := h1.trans (add_le_add (h2.trans (add_le_add hhit (h3.trans (add_le_add
    (SigningGuessProof.alternativeCommitment_bound_source prims A x)
    (resolvedTopPartner_bound_topDigest prims A x))))) (hpartner A x))
  change Pr[ChargedOutput2 prims partner x | run] ≤ _ at hsum
  rw [← mul_add, ← mul_add, ← mul_add] at hsum
  refine hsum.trans ?_
  rw [div_eq_mul_inv, mul_comm (q : ℝ≥0∞)]
  refine mul_le_mul_right (le_trans (le_of_eq ?_) hcost) _
  rw [hdigest]
  ac_rfl

set_option maxRecDepth 100000 in
theorem win_le_charged2_uncharged2 (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true |
      runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] ≤
    Pr[ChargedOutput2 prims partner x | SigningDescentProof.exposedRun prims A x] +
      Pr[UnchargedWin2 prims partner x | SigningDescentProof.exposedRun prims A x] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, probEvent_map]
  refine (probEvent_mono fun r _ hw => ?_).trans (probEvent_or_le _ _ _)
  by_cases hc : ChargedOutput2 prims partner x r
  · exact Or.inl hc
  · exact Or.inr ⟨Prod.ext hw.2 hw.1, hc⟩

/-- The signing core from the bottom partner bound and the new uncharged lane. -/
theorem hiddenCoreAt_of_split (hpartner : BottomPartnerBound prims partner)
    (hresidual : UnchargedLaneBound2 prims partner) : SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hkeys hq hsmall
  rw [SigningCostProof.signingHashError_eq]
  exact (win_le_charged2_uncharged2 prims partner A x).trans
    (add_le_add (chargedOutput2_bound prims partner hpartner A q x hx hkeys hq hsmall)
      (hresidual A q x hx hkeys hq hsmall))

end Split

end SigningPartnerLinkProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningPartnerLinkProof.winResidual_guessCase_or_bottomPartnerCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerLinkProof.winResidual_guessCase_or_bottomPartnerCase

/--
info: 'ThresholdLeanXmssSecurity.SigningPartnerLinkProof.chargedOutput2_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerLinkProof.chargedOutput2_bound

/--
info: 'ThresholdLeanXmssSecurity.SigningPartnerLinkProof.hiddenCoreAt_of_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerLinkProof.hiddenCoreAt_of_split
