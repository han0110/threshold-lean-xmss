import ThresholdLeanXmssSecurity.Proof.SigningPartnerLink

/-!
# The bound of the fresh bottom partner

This module defines the lane 1 bottom partner of leanVM and proves that it costs `2^-128` for each
bottom digest call.

## The recording run

* `loggedRun` of `SigningCost` logs each call of the run with its answer, in call order.
  `loggedRun_forget` gives back `exposedRun` exactly. So the log is the recording run. The cache at
  the start of a grind is the set of inputs that the log holds before the first call of the grind.
* `monitorOf` replays the hash calls of a log with the encoding monitor of leanVM
  (`EncodingMonitor.State`). `seen` holds the called inputs, so a call is fresh if its input is not
  in `seen`. `Covered` says that each cached input of `H` is in `seen`.

## The partner

`BottomPartnerLogged` is the hit of the monitor.

* The monitor installs the first fresh free-copy call with a valid digest at an unsigned key `e`.
  Round 2 at `e` runs only for the message in `st.bound e`, and a grind runs only if `ρ` opens `c_e`.
  So this call is the selected call of the first grind at `e`, unless `ρ` comes from a commitment
  collision (`AlternativeCommitment`), or the final verification calls at `e` first.
* A grind makes no other call between its trials, so its selected input is fresh at the start of
  the grind exactly when it is fresh at its own call.
* A fresh call at `e` before the selection puts its valid digest in `pending e`. The selection hits
  if its digest is in `pending e`.
* A fresh call at `e` after the selection hits if its digest is the selected digest.
* A call on a seen input changes nothing. Its answer is the cached answer, so its match was already
  checked.
* `monitorOf_hit_of_query_before_sign` and `monitorOf_hit_of_sign_before_query` show both orders on
  a log of two calls.

## The bound

`probEvent_hit_le` follows the pending-risk argument of `CappedEncodingMonitor`.

* A fresh call at an unsigned key adds `1 / |validDigests|` to the pending risk on a valid digest.
  This is `2^-128` in expectation (`uniformDigest_valid_bonus_sum_eq`).
* A sign attempt costs nothing. Its pending risk pays its hit (`uniformDigest_sign_bonus_sum_le`).
* A fresh call at a signed key meets the fixed digest with probability `2^-128`.
* `fresh_risk_sum_le` is the potential form of `applyUniformQueryMonitor_true_probability_le` and
  `applyUniformSignAttemptMonitor_true_probability_le`. These two lemmas bound a monitor program
  with a continuation, so they do not apply to a potential on `loggedImpl` directly.

`keyedCost_le_bottomDigestCost` shows that the monitor charges only bottom digest calls.
`bottomPartnerLogged_bound` is the bottom partner bound.

## The type of the partner event

`SigningPartnerLinkProof.BottomPartnerBound` takes `partner` on an outcome of `exposedRun`. That
outcome holds only the final cache, the state, the forgery and the count, and `partner` cannot see
the adversary. So no event at that type can tell a fresh selection from a cached one.

* Take an adversary that learns the base after round 1 at `e` and calls the scan line at `e`
  before round 2. Take a second adversary that makes the same calls after round 2.
* Both runs can end with the same outcome. The selection is cached in the first run and fresh in
  the second run.

So this module states the split on `loggedRun`. `chargedOutputLogged_bound` and
`hiddenCoreAt_of_logged` follow `SigningPartnerLinkProof.chargedOutput2_bound` and
`SigningPartnerLinkProof.hiddenCoreAt_of_split`. The open hypothesis is `UnchargedLaneBoundLogged`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningPartnerBoundProof

open LeanXmss ThresholdLeanXmss SigningHitLaneProof SigningCostProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The hash call of a log entry, with its input, the digest of its answer, and `true` on the free
copy, where the honest operators call. -/
def hashEntry : (Σ t : (WorldSpec C).Domain, (WorldSpec C).Range t) →
    Option (XmssSecurity.HashInput × XmssSecurity.Digest × Bool)
  | ⟨.inl (.inl (.inr (.inl (.hash input)))), output⟩ => some (input, XmssSecurity.truncateHash output, false)
  | ⟨.inr (.inr (.inl (.hash input))), output⟩ => some (input, XmssSecurity.truncateHash output, true)
  | _ => none

/-- The pending-risk monitor of leanVM on the hash calls of a run. `seen` holds the inputs that
the run has called. -/
structure Monitor where
  seen : Set XmssSecurity.HashInput
  state : XmssSecurity.EncodingMonitor.State
  hit : Bool

def Monitor.empty : Monitor := ⟨∅, .empty, false⟩

/-- A fresh hash call. At an encoding input of key `e` it acts as
`CappedEncodingMonitor.applyUniformQueryMonitor` on the counted copy and as
`CappedEncodingMonitor.applyUniformSignAttemptMonitor` on the free copy. The monitor installs the
first fresh free-copy call with a valid digest at an unsigned key. -/
def Monitor.fresh (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor) (input : XmssSecurity.HashInput)
    (digest : XmssSecurity.Digest) (honest : Bool) : Monitor :=
  let seen := insert input m.seen
  (keyOf input).elim ⟨seen, m.state, m.hit⟩ fun e =>
    (m.state.signed e).elim
      (if XmssSecurity.TargetSum.ValidDigest digest then
        if honest then ⟨seen, m.state.install e digest, m.hit || decide (digest ∈ m.state.pending e)⟩
        else ⟨seen, m.state.addPending e digest, m.hit⟩
      else ⟨seen, m.state, m.hit⟩)
      fun target => ⟨seen, m.state, m.hit || decide (digest = target)⟩

/-- One hash call. A call on a seen input changes nothing. -/
def Monitor.step (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (entry : XmssSecurity.HashInput × XmssSecurity.Digest × Bool) : Monitor :=
  if entry.1 ∈ m.seen then m else m.fresh keyOf entry.1 entry.2.1 entry.2.2

/-- The monitor after the hash calls of a log. -/
def monitorOf (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (log : QueryLog (WorldSpec C)) : Monitor :=
  (log.filterMap hashEntry).foldl (Monitor.step keyOf) Monitor.empty

theorem monitorOf_logQuery (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (log : QueryLog (WorldSpec C))
    (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) :
    monitorOf keyOf (log.logQuery t u) =
      match hashEntry ⟨t, u⟩ with
      | none => monitorOf keyOf log
      | some entry => (monitorOf keyOf log).step keyOf entry := by
  unfold monitorOf
  rw [QueryLog.logQuery, List.filterMap_append, List.foldl_append]
  cases h : hashEntry ⟨t, u⟩ <;> simp [QueryLog.singleton, h]

theorem Monitor.fresh_none (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) (honest : Bool)
    (hk : keyOf input = none) :
    m.fresh keyOf input digest honest = ⟨insert input m.seen, m.state, m.hit⟩ := by
  simp only [Monitor.fresh, hk, Option.elim]

theorem Monitor.fresh_signed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) (honest : Bool)
    (e : XmssSecurity.LeafIndex) (hk : keyOf input = some e)
    (target : XmssSecurity.Digest) (hs : m.state.signed e = some target) :
    m.fresh keyOf input digest honest =
      ⟨insert input m.seen, m.state, m.hit || decide (digest = target)⟩ := by
  simp only [Monitor.fresh, hk, hs, Option.elim]

theorem Monitor.fresh_unsigned (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) (honest : Bool)
    (e : XmssSecurity.LeafIndex) (hk : keyOf input = some e)
    (hs : m.state.signed e = none) :
    m.fresh keyOf input digest honest =
      if XmssSecurity.TargetSum.ValidDigest digest then
        if honest then ⟨insert input m.seen, m.state.install e digest,
          m.hit || decide (digest ∈ m.state.pending e)⟩
        else ⟨insert input m.seen, m.state.addPending e digest, m.hit⟩
      else ⟨insert input m.seen, m.state, m.hit⟩ := by
  simp only [Monitor.fresh, hk, hs, Option.elim]

theorem Monitor.fresh_hit (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) (honest : Bool) (h : m.hit = true) :
    (m.fresh keyOf input digest honest).hit = true := by
  cases hk : keyOf input with
  | none => rw [m.fresh_none keyOf input digest honest hk]; exact h
  | some e =>
    cases hs : m.state.signed e with
    | none =>
      rw [m.fresh_unsigned keyOf input digest honest e hk hs]
      split_ifs <;> simp [h]
    | some target => rw [m.fresh_signed keyOf input digest honest e hk target hs]; simp [h]

theorem Monitor.fresh_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) (honest : Bool) :
    (m.fresh keyOf input digest honest).seen = insert input m.seen := by
  cases hk : keyOf input with
  | none => rw [m.fresh_none keyOf input digest honest hk]
  | some e =>
    cases hs : m.state.signed e with
    | none =>
      rw [m.fresh_unsigned keyOf input digest honest e hk hs]
      split_ifs <;> rfl
    | some target => rw [m.fresh_signed keyOf input digest honest e hk target hs]

theorem Monitor.step_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (entry : XmssSecurity.HashInput × XmssSecurity.Digest × Bool) :
    insert entry.1 m.seen ⊆ (m.step keyOf entry).seen := by
  unfold Monitor.step
  split_ifs with hs
  · exact Set.insert_subset hs le_rfl
  · rw [Monitor.fresh_seen]

theorem Monitor.step_of_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (entry : XmssSecurity.HashInput × XmssSecurity.Digest × Bool) (h : entry.1 ∈ m.seen) :
    m.step keyOf entry = m := if_pos h

theorem Monitor.step_of_not_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (entry : XmssSecurity.HashInput × XmssSecurity.Digest × Bool) (h : entry.1 ∉ m.seen) :
    m.step keyOf entry = m.fresh keyOf entry.1 entry.2.1 entry.2.2 := if_neg h

/-- The potential of the monitor, `1` after a hit and the pending risk before. -/
def Monitor.risk (m : Monitor) : ℝ≥0∞ :=
  if m.hit = true then 1 else XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state

theorem uniformDigest_sum_const (c : ℝ≥0∞) :
    ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] * c = c := by
  simp only [probOutput_uniformSample, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem pendingRisk_install_eq (state : XmssSecurity.EncodingMonitor.State) (e : XmssSecurity.LeafIndex)
    (left right : XmssSecurity.Digest) :
    XmssSecurity.CappedEncodingMonitor.State.pendingRisk (state.install e left) =
      XmssSecurity.CappedEncodingMonitor.State.pendingRisk (state.install e right) := by
  unfold XmssSecurity.CappedEncodingMonitor.State.pendingRisk
  rw [XmssSecurity.EncodingMonitor.State.pendingCount_install_eq state e left right]

/-- One fresh call with a uniform digest. A call at an encoding input pays `1 / |Digest|`, and every
other call pays nothing. A sign attempt pays nothing, since its pending risk pays its hit. This is
the potential form of `CappedEncodingMonitor.applyUniformQueryMonitor_true_probability_le` and
`CappedEncodingMonitor.applyUniformSignAttemptMonitor_true_probability_le`. -/
theorem fresh_risk_sum_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (hm : m.hit = false) (input : XmssSecurity.HashInput) (honest : Bool) :
    ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
        (m.fresh keyOf input digest honest).risk ≤
      m.risk + if (keyOf input).isSome then (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ else 0 := by
  have hrisk : m.risk = XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state := by
    simp [Monitor.risk, hm]
  rw [hrisk]
  set R := XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state with hR
  cases hk : keyOf input with
  | none =>
    simp only [Monitor.fresh_none keyOf m input _ honest hk, Monitor.risk, hm, Bool.false_eq_true,
      if_false, Option.isSome_none, add_zero]
    rw [uniformDigest_sum_const]
  | some e =>
    simp only [Option.isSome_some, if_true]
    cases hs : m.state.signed e with
    | some target =>
      simp only [Monitor.fresh_signed keyOf m input _ honest e hk target hs, Monitor.risk, hm,
        Bool.false_or, decide_eq_true_eq]
      calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
            ((if digest ∈ ({target} : Finset XmssSecurity.Digest) then 1 else 0) + R) := by
            gcongr with digest
            by_cases hd : digest = target <;> simp [hd, hR]
        _ = R + (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ := by
            simp only [mul_add, Finset.sum_add_distrib, uniformDigest_sum_const,
              XmssSecurity.CappedEncodingMonitor.uniformDigest_mem_bonus_sum_eq, Finset.card_singleton,
              Nat.cast_one, one_mul]
            exact add_comm _ _
    | none =>
      cases honest with
      | false =>
        simp only [Monitor.fresh_unsigned keyOf m input _ false e hk hs, Bool.false_eq_true, if_false]
        calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
              (R + if XmssSecurity.TargetSum.ValidDigest digest then
                (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
              gcongr with digest
              by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
              · simp only [hv, if_true, Monitor.risk, hm, Bool.false_eq_true, if_false]
                exact XmssSecurity.CappedEncodingMonitor.State.pendingRisk_addPending_le _ _ _
              · simp [hv, Monitor.risk, hm, hR]
          _ = R + (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ := by
              simp only [mul_add, Finset.sum_add_distrib, uniformDigest_sum_const,
                XmssSecurity.CappedEncodingMonitor.uniformDigest_valid_bonus_sum_eq]
      | true =>
        simp only [Monitor.fresh_unsigned keyOf m input _ true e hk hs, if_true]
        set R0 := XmssSecurity.CappedEncodingMonitor.State.pendingRisk (m.state.install e 0) with hR0
        have hsplit : R0 + ((m.state.pending e).card : ℝ≥0∞) *
            (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ = R :=
          XmssSecurity.CappedEncodingMonitor.State.pendingRisk_install_add m.state e 0
        calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
              (R0 + if XmssSecurity.TargetSum.ValidDigest digest then
                (if digest ∈ m.state.pending e then 1 else 0)
              else ((m.state.pending e).card : ℝ≥0∞) *
                (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by
              gcongr with digest
              by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
              · by_cases hp : digest ∈ m.state.pending e
                · simp [hv, hp, Monitor.risk]
                · simp only [hv, hp, if_true, if_false, Monitor.risk, hm, Bool.false_or,
                    decide_false, Bool.false_eq_true, add_zero]
                  rw [pendingRisk_install_eq m.state e digest 0]
              · simp only [hv, if_false, Monitor.risk, hm, Bool.false_eq_true]
                rw [hsplit]
          _ ≤ R0 + ((m.state.pending e).card : ℝ≥0∞) *
                (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
              simp only [mul_add, Finset.sum_add_distrib, uniformDigest_sum_const]
              gcongr
              exact XmssSecurity.CappedEncodingMonitor.uniformDigest_sign_bonus_sum_le _
          _ ≤ R + (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ := by
              rw [hsplit]
              exact le_self_add

/-- The unit of a call for the partner, one for each hash call at an encoding input, on either
copy. -/
def keyedCost (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    (WorldSpec C).Domain → ℕ
  | .inl (.inl (.inr (.inl (.hash input)))) => if (keyOf input).isSome then 1 else 0
  | .inr (.inr (.inl (.hash input))) => if (keyOf input).isSome then 1 else 0
  | _ => 0

theorem tsum_probOutput_mul_le_of_const {α : Type} (mx : ProbComp α) (F : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ z ∈ support mx, F z ≤ c) : ∑' z, Pr[= z | mx] * F z ≤ c := by
  calc ∑' z, Pr[= z | mx] * F z ≤ ∑' z, Pr[= z | mx] * c := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support mx
        · gcongr
          exact h z hz
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
    _ ≤ c := by
        rw [ENNReal.tsum_mul_right]
        calc (∑' z, Pr[= z | mx]) * c ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
          _ = c := one_mul c

/-- A uniform answer of `H` truncates to a uniform digest. -/
theorem hashOutput_sum_truncate (g : XmssSecurity.Digest → ℝ≥0∞) :
    ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * g (XmssSecurity.truncateHash output) =
      ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
        g digest := by
  rw [← tsum_probOutput_map_mul, tsum_fintype]
  refine Finset.sum_congr rfl fun digest _ => ?_
  congr 1
  rw [← probEvent_eq_eq_probOutput, probEvent_map, probOutput_uniformSample]
  have h := XmssSecurity.Rom.uniform_truncate_probability digest
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  · rw [card_bitVec]

/-- The monitor entry of a call of `H` on `q`. -/
def queryEntry (q : Query C) (output : HashOutput) (honest : Bool) :
    Option (XmssSecurity.HashInput × XmssSecurity.Digest × Bool) :=
  match q with
  | .hash input => some (input, XmssSecurity.truncateHash output, honest)
  | _ => none

/-- The monitor after an optional entry. -/
def Monitor.after (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor) :
    Option (XmssSecurity.HashInput × XmssSecurity.Digest × Bool) → Monitor
  | none => m
  | some entry => m.step keyOf entry

/-- The unit of a call of `H` on `q`. -/
def queryCost (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) : Query C → ℕ
  | .hash input => if (keyOf input).isSome then 1 else 0
  | _ => 0

theorem card_digest_inv : (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [card_bitVec]
  norm_num [XmssSecurity.digestBits]

/-- A call of the lazy `H` raises the risk by at most `2^-128` at an encoding input, and not at
all elsewhere, if every cached input is seen. -/
theorem randomOracle_risk_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (q : Query C) (honest : Bool) (cache : HashCache C) (m : Monitor)
    (hcov : ∀ input, cache (.hash input) ≠ none → input ∈ m.seen) :
    ∑' w, Pr[= w | ((Query C →ₒ HashOutput).randomOracle q).run cache] *
        (m.after keyOf (queryEntry q w.1 honest)).risk ≤
      m.risk + (2 ^ 128 : ℝ≥0∞)⁻¹ * (queryCost keyOf q : ℝ≥0∞) := by
  cases q with
  | hash input =>
    by_cases hseen : input ∈ m.seen
    · refine (tsum_probOutput_mul_le_of_const _ _ m.risk fun w _ => ?_).trans le_self_add
      simp only [queryEntry, Monitor.after]
      rw [Monitor.step_of_seen keyOf m (input, XmssSecurity.truncateHash w.1, honest) hseen]
    have hnone : cache (.hash input) = none := by
      by_contra h
      exact hseen (hcov input h)
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hnone, tsum_probOutput_map_mul]
    have hfresh : ∀ output : HashOutput,
        (m.after keyOf (queryEntry (C := C) (.hash input) output honest)).risk =
          (m.fresh keyOf input (XmssSecurity.truncateHash output) honest).risk := fun output => by
      simp only [queryEntry, Monitor.after]
      rw [Monitor.step_of_not_seen keyOf m (input, XmssSecurity.truncateHash output, honest) hseen]
    simp only [hfresh]
    by_cases hm : m.hit = true
    · refine (tsum_probOutput_mul_le_of_const _ _ m.risk fun w _ => ?_).trans le_self_add
      simp [Monitor.risk, Monitor.fresh_hit keyOf m _ _ _ hm, hm]
    · rw [Bool.not_eq_true] at hm
      have hsum := hashOutput_sum_truncate (fun digest => (m.fresh keyOf input digest honest).risk)
      refine (le_of_eq hsum).trans ((fresh_risk_sum_le keyOf m hm input honest).trans ?_)
      gcongr
      rw [card_digest_inv]
      cases hk : keyOf input <;> simp [queryCost, hk]
  | _ =>
    exact (tsum_probOutput_mul_le_of_const _ _ m.risk fun w _ => le_rfl).trans le_self_add

/-- Every cached input of `H` is seen by the monitor. -/
def Covered (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (s : LoggedState C) : Prop :=
  ∀ input, s.1.1 (.hash input) ≠ none → input ∈ (monitorOf keyOf s.2).seen

/-- Each call of `loggedImpl` other than a programming query raises the risk by at most `2^-128`
for each hash call at an encoding input. -/
theorem logged_risk_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : Covered keyOf s) (ht : ¬IsProgram t) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] * (monitorOf keyOf r.2.2).risk ≤
      (monitorOf keyOf s.2).risk + (2 ^ 128 : ℝ≥0∞)⁻¹ * (keyedCost keyOf t : ℝ≥0∞) := by
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    tsum_probOutput_map_mul, monitorOf_logQuery]
  have hconst : ∀ {α : Type} (mx : ProbComp α) (F : α → ℝ≥0∞),
      (∀ w, F w = (monitorOf keyOf s.2).risk) →
      ∑' w, Pr[= w | mx] * F w ≤ (monitorOf keyOf s.2).risk + (2 ^ 128 : ℝ≥0∞)⁻¹ * (keyedCost keyOf t : ℝ≥0∞) :=
    fun mx F hF => (tsum_probOutput_mul_le_of_const mx F _ fun w _ => (hF w).le).trans le_self_add
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · exact hconst _ _ fun w => rfl
  · cases q
    all_goals exact randomOracle_risk_le keyOf _ false s.1.1 _ hs
  · exact hconst _ _ fun w => rfl
  · exact (ht trivial).elim
  · exact hconst _ _ fun w => rfl
  · cases q
    all_goals exact randomOracle_risk_le keyOf _ true s.1.1 _ hs
  · exact hconst _ _ fun w => rfl

theorem loggedImpl_support (t : (WorldSpec C).Domain) (s : LoggedState C)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    ∃ w ∈ support ((SeedHitProof.signImpl prims t).run s.1.1),
      r.1 = w.1 ∧ r.2.1.1 = w.2 ∧ r.2.2 = s.2.logQuery t w.1 := by
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map,
    Set.mem_image] at hr
  obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hr
  exact ⟨w, hw, rfl, rfl, rfl⟩

/-- A call of the lazy `H` on `q` changes the cache only at `q`. -/
theorem randomOracle_cache_ne (q : Query C) (cache : HashCache C)
    (w : HashOutput × HashCache C) (hw : w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run cache))
    (other : Query C) (hne : other ≠ q) : w.2 other = cache other := by
  cases hc : cache q with
  | some v =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc] at hw
    rw [(mem_support_pure_iff _ _).1 hw]
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hw
    obtain ⟨v, -, rfl⟩ := hw
    exact QueryCache.cacheQuery_of_ne _ _ hne

theorem covered_step (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : ¬Programmed s.2 → Covered keyOf s)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    ¬Programmed r.2.2 → Covered keyOf r.2 := by
  intro hp
  have hlog := loggedImpl_log prims t s r hr
  rw [hlog, programmed_logQuery, not_or] at hp
  have hcov := hs hp.1
  obtain ⟨w, hw, h1, hcache, hlog'⟩ := loggedImpl_support prims t s r hr
  intro input hin
  rw [hcache] at hin
  rw [hlog', monitorOf_logQuery]
  have hsub : ∀ entry, (monitorOf keyOf s.2).seen ⊆ ((monitorOf keyOf s.2).after keyOf entry).seen := by
    intro entry
    cases entry with
    | none => exact le_rfl
    | some entry => exact (Set.subset_insert _ _).trans (Monitor.step_seen keyOf _ entry)
  have hq : ∀ (q : Query C) (honest : Bool) (v : HashOutput),
      (v, w.2) ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) →
      input ∈ ((monitorOf keyOf s.2).after keyOf (queryEntry q v honest)).seen := by
    intro q honest v hv
    by_cases he : q = .hash input
    · subst he
      exact Monitor.step_seen keyOf (monitorOf keyOf s.2) (input, XmssSecurity.truncateHash v, honest)
        (Set.mem_insert _ _)
    · have hc := randomOracle_cache_ne q s.1.1 (v, w.2) hv (.hash input) (Ne.symm he)
      exact hsub _ (hcov input (hc ▸ hin))
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change w ∈ support ((fun u => (u, s.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hw
    rw [support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact hcov input hin
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) at hw
    cases q
    all_goals exact hq _ false w.1 hw
  · change w ∈ support ((prgAnswer prims p).run s.1.1) at hw
    simp only [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure] at hw
    obtain ⟨x, hx, hw⟩ := Set.mem_iUnion₂.1 hw
    have hw2 : w.2 = x.2 := congrArg Prod.snd (show w = _ from hw)
    have hc := randomOracle_cache_ne _ s.1.1 x hx (.hash input) (by simp)
    rw [hw2, hc] at hin
    exact hcov input hin
  · exact (hp.2 trivial).elim
  · change w ∈ support ((fun u => (u, s.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hw
    rw [support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact hcov input hin
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) at hw
    cases q
    all_goals exact hq _ true w.1 hw
  · change w ∈ support ((prgAnswer prims p).run s.1.1) at hw
    simp only [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure] at hw
    obtain ⟨x, hx, hw⟩ := Set.mem_iUnion₂.1 hw
    have hw2 : w.2 = x.2 := congrArg Prod.snd (show w = _ from hw)
    have hc := randomOracle_cache_ne _ s.1.1 x hx (.hash input) (by simp)
    rw [hw2, hc] at hin
    exact hcov input hin

set_option maxRecDepth 100000 in
/-- A hit of the monitor on `loggedRun` costs `2^-128` for each hash call at an encoding input. -/
theorem probEvent_hit_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun z => (monitorOf keyOf z.2.2).hit = true | loggedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => (keyedCost keyOf t : ℝ≥0∞)) (SigningDescentProof.finalRun A x) loggedInit := by
  let potential : LoggedState C → ℝ≥0∞ := fun s => (monitorOf keyOf s.2).risk
  let Inv : LoggedState C → Prop := fun s => ¬Programmed s.2 → Covered keyOf s
  let bad : LoggedState C → Prop := fun s => (monitorOf keyOf s.2).hit = true ∧ ¬Programmed s.2
  have hbad : ∀ s, bad s → 1 ≤ guarded potential s := by
    intro s hs
    rw [guarded, if_neg hs.2]
    simp [potential, Monitor.risk, hs.1]
  have hstep : ∀ t s, Inv s → ∑' r, Pr[= r | (loggedImpl prims t).run s] * guarded potential r.2 ≤
      guarded potential s + (2 ^ 128 : ℝ≥0∞)⁻¹ * (keyedCost keyOf t : ℝ≥0∞) := by
    intro t s hs
    exact SigningGuessProof.guarded_domain_step prims (Covered keyOf) potential
      (fun t => (2 ^ 128 : ℝ≥0∞)⁻¹ * (keyedCost keyOf t : ℝ≥0∞))
      (fun t s hs _ ht => logged_risk_le prims keyOf t s hs ht) t s hs
  have hinit : Inv loggedInit := fun _ input h => (h rfl).elim
  have hz : guarded potential loggedInit = 0 := by
    rw [guarded, if_neg (show ¬Programmed (loggedInit (C := C)).2 by simp [loggedInit, Programmed])]
    simp [potential, monitorOf, loggedInit, Monitor.risk, Monitor.empty,
      XmssSecurity.CappedEncodingMonitor.State.pendingRisk_empty]
  have hb := SigningGuessProof.probEvent_le_chargedCost (loggedImpl prims) Inv
    (fun t s hs r hr => covered_step prims keyOf t s hs r hr) (guarded potential) bad hbad
    (fun t _ => (keyedCost keyOf t : ℝ≥0∞)) (2 ^ 128 : ℝ≥0∞)⁻¹ hstep
    (SigningDescentProof.finalRun A x) loggedInit hinit hz
  refine le_trans ?_ hb
  apply probEvent_mono
  intro z hz hhit
  exact ⟨hhit, noProgramQuery prims C A x z hz⟩

/-- An encoding input is not a top digest input. -/
theorem encodingInput_not_anyTopDigestInput (x : SigningSecurityProof.Keys3 C) (e : XmssSecurity.LeafIndex)
    (payload : XmssSecurity.Message × XmssSecurity.Randomness) :
    ¬SigningGuessProof.anyTopDigestInput x.1
      (.hash (XmssSecurity.Concrete.CacheView.encodingInput x.1 e payload) : Query C) := by
  rintro ⟨key, top, htop⟩
  have h := XmssSecurity.domain_eq_of_tweakableHashInput_eq x.1 (Query.hash.inj htop)
  cases h

/-- The partner charges only bottom digest calls. -/
theorem keyedCost_le_bottomDigestCost (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) :
    keyedCost (XmssSecurity.encodingInputLeafIndex? x.1) t ≤ SigningPartnerLinkProof.bottomDigestCost x t := by
  have hbottom : ∀ t, SigningGuessLaneProof.DigestCall t →
      SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t = 0 →
      keyedCost (XmssSecurity.encodingInputLeafIndex? x.1) t ≤ 1 →
      keyedCost (XmssSecurity.encodingInputLeafIndex? x.1) t ≤ SigningPartnerLinkProof.bottomDigestCost x t := by
    intro t hd hraw hk
    have h := SigningPartnerLinkProof.topDigest_add_bottomDigestCost x t
    rw [hraw, zero_add, SigningGuessLaneProof.digestCost, if_pos hd] at h
    rw [h]
    exact hk
  have hhash : ∀ (input : XmssSecurity.HashInput) (t : (WorldSpec C).Domain),
      (t = .inl (.inl (.inr (.inl (.hash input)))) ∨ t = .inr (.inr (.inl (.hash input)))) →
      keyedCost (XmssSecurity.encodingInputLeafIndex? x.1) t ≤ SigningPartnerLinkProof.bottomDigestCost x t := by
    intro input t ht
    cases hk : XmssSecurity.encodingInputLeafIndex? x.1 input with
    | none => rcases ht with rfl | rfl <;> simp [keyedCost, hk]
    | some e =>
      obtain ⟨payload, rfl⟩ :=
        XmssSecurity.exists_encodingInput_of_encodingInputLeafIndex?_eq_some x.1 input e hk
      rcases ht with rfl | rfl
      all_goals
        refine hbottom _ (Or.inl ⟨x.1, e, payload, rfl⟩) ?_ ?_
        · simp [SigningGuessProof.rawDomainCost, encodingInput_not_anyTopDigestInput]
        · simp only [keyedCost]
          split_ifs <;> omega
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · exact Nat.zero_le _
  · cases q
    case hash input => exact hhash input _ (Or.inl rfl)
    all_goals exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · cases q
    case hash input => exact hhash input _ (Or.inr rfl)
    all_goals exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The first order of leanVM `runObserved_empty_eq_true_of_query_before_sign_of_valid`. A call on
the counted copy meets a later fresh selection at the same key. -/
theorem monitorOf_hit_of_query_before_sign
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (e : XmssSecurity.LeafIndex)
    (query sign : XmssSecurity.HashInput) (hquery : keyOf query = some e) (hsign : keyOf sign = some e)
    (hne : sign ≠ query) (queryOutput signOutput : HashOutput)
    (heq : XmssSecurity.truncateHash queryOutput = XmssSecurity.truncateHash signOutput)
    (hvalid : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash signOutput)) :
    (monitorOf keyOf ([⟨.inl (.inl (.inr (.inl (.hash query)))), queryOutput⟩,
      ⟨.inr (.inr (.inl (.hash sign))), signOutput⟩] : QueryLog (WorldSpec C))).hit = true := by
  have h1 : Monitor.empty.step keyOf (query, XmssSecurity.truncateHash queryOutput, false) =
      ⟨insert query ∅, XmssSecurity.EncodingMonitor.State.empty.addPending e
        (XmssSecurity.truncateHash signOutput), false⟩ := by
    rw [Monitor.step_of_not_seen keyOf _ _ (Set.notMem_empty _),
      Monitor.fresh_unsigned keyOf _ _ _ _ e hquery rfl, heq, if_pos hvalid]
    rfl
  have hseen : sign ∉ (insert query ∅ : Set XmssSecurity.HashInput) := by simpa using hne
  have hsigned : (XmssSecurity.EncodingMonitor.State.empty.addPending e
      (XmssSecurity.truncateHash signOutput)).signed e = none := rfl
  change ((Monitor.empty.step keyOf (query, XmssSecurity.truncateHash queryOutput, false)).step keyOf
    (sign, XmssSecurity.truncateHash signOutput, true)).hit = true
  rw [h1, Monitor.step_of_not_seen keyOf _ _ hseen, Monitor.fresh_unsigned keyOf _ _ _ _ e hsign hsigned,
    if_pos hvalid, if_pos rfl]
  simp [XmssSecurity.EncodingMonitor.State.addPending]

/-- The second order of leanVM `runObserved_empty_eq_true_of_sign_before_query_of_valid`. A later
fresh call on another input meets the selected digest. -/
theorem monitorOf_hit_of_sign_before_query
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (e : XmssSecurity.LeafIndex)
    (sign query : XmssSecurity.HashInput) (hsign : keyOf sign = some e) (hquery : keyOf query = some e)
    (hne : query ≠ sign) (signOutput queryOutput : HashOutput)
    (heq : XmssSecurity.truncateHash queryOutput = XmssSecurity.truncateHash signOutput)
    (hvalid : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash signOutput)) :
    (monitorOf keyOf ([⟨.inr (.inr (.inl (.hash sign))), signOutput⟩,
      ⟨.inl (.inl (.inr (.inl (.hash query)))), queryOutput⟩] : QueryLog (WorldSpec C))).hit = true := by
  have h1 : Monitor.empty.step keyOf (sign, XmssSecurity.truncateHash signOutput, true) =
      ⟨insert sign ∅, XmssSecurity.EncodingMonitor.State.empty.install e
        (XmssSecurity.truncateHash signOutput), false || decide (XmssSecurity.truncateHash signOutput ∈
          XmssSecurity.EncodingMonitor.State.empty.pending e)⟩ := by
    rw [Monitor.step_of_not_seen keyOf _ _ (Set.notMem_empty _),
      Monitor.fresh_unsigned keyOf _ _ _ _ e hsign rfl, if_pos hvalid, if_pos rfl]
    rfl
  have hseen : query ∉ (insert sign ∅ : Set XmssSecurity.HashInput) := by simpa using hne
  have hsigned : (XmssSecurity.EncodingMonitor.State.empty.install e
      (XmssSecurity.truncateHash signOutput)).signed e = some (XmssSecurity.truncateHash signOutput) := by
    simp [XmssSecurity.EncodingMonitor.State.install]
  change ((Monitor.empty.step keyOf (sign, XmssSecurity.truncateHash signOutput, true)).step keyOf
    (query, XmssSecurity.truncateHash queryOutput, false)).hit = true
  rw [h1, Monitor.step_of_not_seen keyOf _ _ hseen,
    Monitor.fresh_signed keyOf _ _ _ _ e hquery _ hsigned, heq]
  simp

/-- An outcome of `loggedRun`. -/
abbrev LoggedOutcome (C : Committee) :=
  ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C

/-- The lane 1 bottom partner of leanVM on the log of a run. The selection at a key `e` is a fresh
honest call with a valid digest, and some call at `e` on another input meets its digest, before or
after it. -/
def BottomPartnerLogged (x : SigningSecurityProof.Keys3 C) (z : LoggedOutcome C) : Prop :=
  (monitorOf (XmssSecurity.encodingInputLeafIndex? x.1) z.2.2).hit = true

/-- The bottom partner costs `2^-128` for each bottom digest call. -/
theorem bottomPartnerLogged_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[BottomPartnerLogged x | loggedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine (probEvent_hit_le prims _ A x).trans ?_
  gcongr
  apply XmssSecurity.expectedSimulatedCost_mono
  intro t _
  exact_mod_cast keyedCost_le_bottomDigestCost x t

/-- The charged lane with the bottom partner on the log. -/
def ChargedOutputLogged (x : SigningSecurityProof.Keys3 C) (z : LoggedOutcome C) : Prop :=
  SigningGuessProof.ChargedOutput prims x (z.1, z.2.1) ∨ BottomPartnerLogged x z

/-- The win that the charged lane on the log leaves. -/
def UnchargedWinLogged (x : SigningSecurityProof.Keys3 C) (z : LoggedOutcome C) : Prop :=
  z.1.1 = (true, false) ∧ ¬ChargedOutputLogged prims x z

/-- The fixed-cap bound of the uncharged lane on the log. -/
def UnchargedLaneBoundLogged : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[UnchargedWinLogged prims x | loggedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128

set_option maxRecDepth 100000 in
/-- `SigningPartnerLinkProof.chargedOutput2_bound` with the bottom partner on the log. -/
theorem chargedOutputLogged_bound (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr[ChargedOutputLogged prims x | loggedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  obtain ⟨T, hhit⟩ := SigningGuessProof.hit_bound_structural_cost prims A q x hx hkeys hq hsmall
  replace hhit : Pr[SigningCostProof.WinHit prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningGuessProof.structuralHitCost x T) := hhit
  have hcost := SigningGuessProof.source_output_costs_le prims A x T q hq
  have hdigest : SigningGuessProof.sourceExpectedCost prims A x SigningGuessLaneProof.digestCost =
      SigningGuessProof.sourceExpectedCost prims A x
          (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1)) +
        SigningGuessProof.sourceExpectedCost prims A x (SigningPartnerLinkProof.bottomDigestCost x) := by
    rw [← SigningGuessProof.sourceExpectedCost_add]
    congr 1
    funext t
    exact (SigningPartnerLinkProof.topDigest_add_bottomDigestCost x t).symm
  let run := SigningDescentProof.exposedRun prims A x
  have h1 : Pr[ChargedOutputLogged prims x | loggedRun prims A x] ≤
      Pr[SigningGuessProof.ChargedOutput prims x | run] + Pr[BottomPartnerLogged x | loggedRun prims A x] := by
    refine (probEvent_or_le _ _ _).trans (le_of_eq ?_)
    congr 1
    change _ = Pr[SigningGuessProof.ChargedOutput prims x | SigningDescentProof.exposedRun prims A x]
    rw [← loggedRun_forget, probEvent_map]
    rfl
  have h2 := probEvent_or_le run (SigningCostProof.WinHit prims x)
    (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1 ∨
      ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have h3 := probEvent_or_le run (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (fun r => ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have hsum := h1.trans (add_le_add (h2.trans (add_le_add hhit (h3.trans (add_le_add
    (SigningGuessProof.alternativeCommitment_bound_source prims A x)
    (SigningPartnerLinkProof.resolvedTopPartner_bound_topDigest prims A x))))) (bottomPartnerLogged_bound prims A x))
  rw [← mul_add, ← mul_add, ← mul_add] at hsum
  refine hsum.trans ?_
  rw [div_eq_mul_inv, mul_comm (q : ℝ≥0∞)]
  refine mul_le_mul_right (le_trans (le_of_eq ?_) hcost) _
  rw [hdigest]
  ac_rfl

set_option maxRecDepth 100000 in
theorem win_le_chargedLogged_unchargedLogged (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true |
      runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] ≤
    Pr[ChargedOutputLogged prims x | loggedRun prims A x] +
      Pr[UnchargedWinLogged prims x | loggedRun prims A x] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, ← loggedRun_forget, Functor.map_map, probEvent_map]
  refine (probEvent_mono fun r _ hw => ?_).trans (probEvent_or_le _ _ _)
  by_cases hc : ChargedOutputLogged prims x r
  · exact Or.inl hc
  · exact Or.inr ⟨Prod.ext hw.2 hw.1, hc⟩

/-- The signing core from the uncharged lane on the log. The bottom partner bound is proved. -/
theorem hiddenCoreAt_of_logged (hresidual : UnchargedLaneBoundLogged (C := C) prims) :
    SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hkeys hq hsmall
  rw [SigningCostProof.signingHashError_eq]
  exact (win_le_chargedLogged_unchargedLogged prims A x).trans
    (add_le_add (chargedOutputLogged_bound prims A q x hx hkeys hq hsmall)
      (hresidual A q x hx hkeys hq hsmall))

end SigningPartnerBoundProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningPartnerBoundProof.bottomPartnerLogged_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerBoundProof.bottomPartnerLogged_bound

/--
info: 'ThresholdLeanXmssSecurity.SigningPartnerBoundProof.hiddenCoreAt_of_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerBoundProof.hiddenCoreAt_of_logged
