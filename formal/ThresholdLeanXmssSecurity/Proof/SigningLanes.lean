import ThresholdLeanXmssSecurity.Proof.SigningHybrid

/-!
# The budget check of a two-lane split of the bottom partner

This module checks one split of the bottom partner between the charged lane and the uncharged
lane. The check fails. So the module holds the traces, and it defines no new event.

## The split under test

* The charged lane widens lane 1 of leanVM. The selection at `e` is fresh when its first call
  happens, by any party. The selection meets a digest of an earlier counted encoding call at `e`
  on another input, or a later call meets its digest. The pending-risk potential of
  `SigningPartnerBoundProof` pays the hit. The selecting call costs no unit, because its digest is
  uniform on the valid digests.
* The uncharged lane takes an encoding call at `e` before round 1 whose input is the selected input
  `(m, b + k*)`. The base `b` is a hidden oracle output before round 1. The lane charges one unit
  for each call. The Guess and the true opening probes stay there, on other call types.

## The rules of the check

* `SigningPartnerBoundProof.probEvent_hit_le` steps a potential over the log. So the monitor must
  decide at each call, from the log before the call and the answer, whether the call is the
  selection (`Monitor.step`).
* `SigningOpeningProof.probEvent_le_of_capped` decides the flag at one call. An input-side call hits
  when `s (keyOf t) = point t`, so it has exactly one target value. An output-side call obeys
  `hout`, at most `2^-128` for every state.
* Each counted call has two units, one in each lane (`signingHashError` is `q / 2^127`).
* `q` counts the calls of every party. So `q ≥ 2^32` once a grind can run to the limit
  `randomizerAttemptLimit = 2^32`.

The numbers use `N = 2^128` and `K = |validDigests|` with `2^107 ≤ K ≤ 2^108`
(`XmssSecurity.TargetSum.two_pow_107_le_validDigests_card`,
`XmssSecurity.TargetSum.validDigests_card_le_two_pow_108`). A trial is valid with probability
`v = K / N`, and `2^-21 ≤ v ≤ 2^-20`.

## Trace 1. The charged lane cannot find the selecting call

1. The adversary makes `Q1 = 2^40` counted encoding calls at `e` on messages other than `m0`. Their
   valid digests form the pending set `P`, with `E|P| = Q1 · v ≥ 2^19`.
2. Round 1 at `e` binds `m0` and releases `ρ_e`. The adversary calls the base `b`.
3. The adversary calls `Q2 = 2^31` scan positions `b + 2i` for `i < 2^31`, in decreasing order of
   `i`. The positions stay inside the attempt limit. The odd positions stay uncalled.
4. At the call on `b + 2i`, the positions below it are not in the log. So the log prefix does not
   tell whether this call is the selection.

The monitor has two choices at such a call.

* It installs every fresh valid scan position. About `Q2 · v ≥ 2^10` calls install, and each meets
  `P` with probability `|P| / K`. The hit has probability about `Q1 · Q2 · v / N ≥ 2^-78`. The lane
  budget is `q / N` with `q ≈ 2^40`, so about `2^-88`. The monitor is `2^10` times over budget,
  although almost no installed call is the selection.
* It installs one call, for example the first valid call or a call whose positions below are all
  cached and invalid. Then the true selection is almost never the installed call. It is the first
  valid position from `b`, and the adversary calls it after a larger valid position, or the grind
  calls it first at an odd offset. The event "the selection meets `P`" has probability about
  `|P| / K ≈ 2^-88`, and the monitor misses it. The other lane cannot take it, because the hit
  depends on the later calls that fill the positions below.

The lane total is not refuted. The true event costs about `2^-88`, inside the budget. Only the
pending-risk monitor with one install per key fails.

The same choice arises in the window after round 1 and before the first call of the base. The
adversary calls `(m0, R)` for many `R`. No call there knows its offset from `b`, so no call there is
an identifiable selecting call.

## Trace 2. The uncharged flag needs more than one unit at one call

1. Before round 1 at `e`, the adversary fixes `m0` and `R`. It calls `(m0, R - L), ..., (m0, R - 1)`
   with `L = 2^23`, in increasing order.
2. All `L` answers are invalid with probability `(1 - v)^L ≥ e^-9`. Take this state.
3. The adversary calls `(m0, R)`. Later it binds `m0` at round 1.

The flag fires if `(m0, R)` is the selection of `m0`. That holds if the answer is valid and
`b = R - j` for some `j ≤ L`, because the positions between are cached and invalid. So the hazard
of this one call is at least `v · (L + 1) / N ≥ 4 / N` (`cachedRun_hazard_units`). The positions
`b < R - L` add about `1 / N` more. With the charged unit of the call, the call needs at least five
units, and it has two.

The flag also does not fit the input-side form. It fires for `L + 1` values of the hidden base, not
for one value `point t`.

The lane total is not refuted. The cached positions below `R` have invalid answers, so the flag
never fires on them. Over the whole run, each call adds about one unit in expectation.

## Trace 3. The commitment counterexample

The split moves only encoding calls. A commitment call keeps its input target `ρ_e` in the uncharged
lane (`SigningHybridProof.UnchargedFlagSound`) and its output target `c_e` in the charged lane
(`commitmentCost`). So the counterexample of `SigningGuessProof` costs at most `2 · M / N ≤ 2q / N`.
This check passes.

## What would close the gap

Both lane totals hold in expectation. Each needs a weighted potential in place of a flag or a single
install. These options need a decision of the owner.

* The uncharged lane can use the reach mass `XmssSecurity.W` of leanVM (`Scan/Potential.lean`).
  The potential is the sum of `W` over the cached valid positions of each message. A fresh call
  raises it by `2^-128` in expectation. The first call of the base consumes it, because `b` is
  uniform at that call. The cost is a potential version of `probEvent_le_of_capped`. The risk is
  FIX.md Track B item 4. The argument needs only a uniform `b` at its own first call, not a hidden
  `b` after round 1, but it is not the leanVM lemma as it is. The boundary of the lane must be the
  first call of the base, not round 1 (Trace 1, the window).
* The charged lane can weigh each candidate `x` on the scan line by `(1 - v)^g`, where `g` counts the
  uncalled positions in `[b, x)`, and zero if a called position there is valid. After the first call
  of the base, this weight is a function of the log. The potential is the pending risk times one
  minus the summed weight, plus the weight of each candidate that met `P`. The cost is a new
  potential in place of `Monitor.risk`. No leanVM lemma gives it.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLanesProof

/-- The hazard of the call in Trace 2, scaled by `N`, is at least four units. -/
theorem cachedRun_hazard_units :
    4 * 2 ^ 128 ≤ XmssSecurity.TargetSum.validDigests.card * 2 ^ 23 := by
  have h := XmssSecurity.TargetSum.two_pow_107_le_validDigests_card
  calc 4 * 2 ^ 128 = 2 ^ 107 * 2 ^ 23 := by norm_num
    _ ≤ XmssSecurity.TargetSum.validDigests.card * 2 ^ 23 := Nat.mul_le_mul_right _ h

end SigningLanesProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningLanesProof.cachedRun_hazard_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningLanesProof.cachedRun_hazard_units
