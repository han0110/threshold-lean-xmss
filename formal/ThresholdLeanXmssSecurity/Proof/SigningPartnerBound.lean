import ThresholdLeanXmssSecurity.Proof.SigningPartnerLink

/-!
# The bound of the fresh bottom partner

This module defines the pending-risk monitor of leanVM on a logged run. It bounds the rise of the
monitor risk at each call by `2^-128` for each bottom digest call. `r1Hit_bound` in `SigningOneRun`
and `units_le` in `SigningOwnForger` use it.

## The recording run

* `loggedRun` of `SigningCost` logs each call of the run with its answer, in call order.
  `loggedRun_forget` gives back `exposedRun` exactly. So the log is the recording run. The cache at
  the start of a grind is the set of inputs that the log holds before the first call of the grind.
* An outcome of `exposedRun` holds only the final cache. So it cannot tell a fresh selection from a
  cached one, and the monitor reads the log.
* `monitorOf` replays the hash calls of a log with the encoding monitor of leanVM
  (`EncodingMonitor.State`). `seen` holds the called inputs, so a call is fresh if its input is not
  in `seen`.

## The monitor

* The monitor installs the first fresh free-copy call with a valid digest at an unsigned key `e`.
  Round 2 at `e` runs only for the message in `st.bound e`, and a grind runs only if `ρ` opens `c_e`.
  So this call is the selected call of the first grind at `e`, with two exceptions. Either `ρ`
  comes from a commitment collision (`AlternativeCommitment`), or the final verification calls at
  `e` first.
* A grind makes no other call between its trials. So its selected input is fresh at the start of
  the grind exactly when it is fresh at its own call.
* A fresh call at `e` before the selection puts its valid digest in `pending e`. The selection hits
  if its digest is in `pending e`.
* A fresh call at `e` after the selection hits if its digest is the selected digest.
* A call on a seen input changes nothing. Its answer is the cached answer, so its match was already
  checked.

## The bound

`randomOracle_risk_le` follows the pending-risk argument of `CappedEncodingMonitor` at one call of
the lazy `H`.

* A fresh call at an unsigned key adds `1 / |validDigests|` to the pending risk on a valid digest.
  This is `2^-128` in expectation (`uniformDigest_valid_bonus_sum_eq`).
* A sign attempt costs nothing. Its pending risk pays its hit (`uniformDigest_sign_bonus_sum_le`).
* A fresh call at a signed key meets the fixed digest with probability `2^-128`.
* `fresh_risk_sum_le` is the potential form of `applyUniformQueryMonitor_true_probability_le` and
  `applyUniformSignAttemptMonitor_true_probability_le`. These two lemmas bound a monitor program
  with a continuation, so they do not apply to a potential on `loggedImpl` directly.

`keyedCost_le_bottomDigestCost` shows that the monitor charges only bottom digest calls.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningPartnerBoundProof

open HashSig LeanXmss ThresholdLeanXmss SigningHitLaneProof SigningCostProof

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
    m.step keyOf entry = m := ite_eq_left h

theorem Monitor.step_of_not_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (entry : XmssSecurity.HashInput × XmssSecurity.Digest × Bool) (h : entry.1 ∉ m.seen) :
    m.step keyOf entry = m.fresh keyOf entry.1 entry.2.1 entry.2.2 := ite_eq_right h

/-- The potential of the monitor, `1` after a hit and the pending risk before. -/
def Monitor.risk (m : Monitor) : ℝ≥0∞ :=
  if m.hit = true then 1 else XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state

theorem uniformDigest_sum_const (c : ℝ≥0∞) :
    ∑ digest : XmssSecurity.Digest, Pr{let z ← ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)}[z = digest] * c = c := by
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
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
    ∑ digest : XmssSecurity.Digest, Pr{let z ← ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)}[z = digest] *
        (m.fresh keyOf input digest honest).risk ≤
      m.risk + if (keyOf input).isSome then (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ else 0 := by
  have hrisk : m.risk = XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state := by
    simp [Monitor.risk, hm]
  rw [hrisk]
  set R := XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state with hR
  cases hk : keyOf input with
  | none =>
    simp only [Monitor.fresh_none keyOf m input _ honest hk, Monitor.risk, hm, Bool.false_eq_true,
      ite_false, Option.isSome_none, add_zero]
    rw [uniformDigest_sum_const]
  | some e =>
    simp only [Option.isSome_some, ite_true]
    cases hs : m.state.signed e with
    | some target =>
      simp only [Monitor.fresh_signed keyOf m input _ honest e hk target hs, Monitor.risk, hm,
        Bool.false_or, decide_eq_true_eq]
      calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr{let z ← ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)}[z = digest] *
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
        simp only [Monitor.fresh_unsigned keyOf m input _ false e hk hs, Bool.false_eq_true, ite_false]
        calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr{let z ← ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)}[z = digest] *
              (R + if XmssSecurity.TargetSum.ValidDigest digest then
                (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
              gcongr with digest
              by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
              · simp only [hv, ite_true, Monitor.risk, hm, Bool.false_eq_true, ite_false]
                exact XmssSecurity.CappedEncodingMonitor.State.pendingRisk_addPending_le _ _ _
              · simp [hv, Monitor.risk, hm, hR]
          _ = R + (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ := by
              simp only [mul_add, Finset.sum_add_distrib, uniformDigest_sum_const,
                XmssSecurity.CappedEncodingMonitor.uniformDigest_valid_bonus_sum_eq]
      | true =>
        simp only [Monitor.fresh_unsigned keyOf m input _ true e hk hs, ite_true]
        set R0 := XmssSecurity.CappedEncodingMonitor.State.pendingRisk (m.state.install e 0) with hR0
        have hsplit : R0 + ((m.state.pending e).card : ℝ≥0∞) *
            (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ = R :=
          XmssSecurity.CappedEncodingMonitor.State.pendingRisk_install_add m.state e 0
        calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr{let z ← ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)}[z = digest] *
              (R0 + if XmssSecurity.TargetSum.ValidDigest digest then
                (if digest ∈ m.state.pending e then 1 else 0)
              else ((m.state.pending e).card : ℝ≥0∞) *
                (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by
              gcongr with digest
              by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
              · by_cases hp : digest ∈ m.state.pending e
                · simp [hv, hp, Monitor.risk]
                · simp only [hv, hp, ite_true, ite_false, Monitor.risk, hm, Bool.false_or,
                    decide_false, Bool.false_eq_true, add_zero]
                  rw [pendingRisk_install_eq m.state e digest 0]
              · simp only [hv, ite_false, Monitor.risk, hm, Bool.false_eq_true]
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
    (h : ∀ z ∈ support mx, F z ≤ c) : ∑' z, Pr{let y ← mx}[y = z] * F z ≤ c := by
  calc ∑' z, Pr{let y ← mx}[y = z] * F z ≤ ∑' z, Pr{let y ← mx}[y = z] * c := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support mx
        · gcongr
          exact h z hz
        · rw [prEvent_eq_zero_of_not_mem_support _ hz, zero_mul, zero_mul]
    _ ≤ c := by
        rw [ENNReal.tsum_mul_right]
        calc (∑' z, Pr{let y ← mx}[y = z]) * c ≤ 1 * c := by gcongr; exact (OracleComp.tsum_prEvent_le_one _)
          _ = c := one_mul c

/-- A uniform answer of `H` truncates to a uniform digest. -/
theorem hashOutput_sum_truncate (g : XmssSecurity.Digest → ℝ≥0∞) :
    ∑' output, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = output] * g (XmssSecurity.truncateHash output) =
      ∑ digest : XmssSecurity.Digest, Pr{let z ← ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)}[z = digest] *
        g digest := by
  refine (OracleComp.tsum_prEvent_map_mul _ XmssSecurity.truncateHash g).symm.trans ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun digest _ => ?_
  congr 1
  erw [prEvent_map, SampleableType.prEvent_uniformSample_eq_singleton]
  have h := XmssSecurity.Rom.uniform_truncate_probability digest
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  · rw [Fintype.card_bitVec]

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
  rw [Fintype.card_bitVec]
  norm_num [XmssSecurity.digestBits]

/-- A call of the lazy `H` raises the risk by at most `2^-128` at an encoding input, and not at
all elsewhere, if every cached input is seen. -/
theorem randomOracle_risk_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (q : Query C) (honest : Bool) (cache : HashCache C) (m : Monitor)
    (hcov : ∀ input, cache (.hash input) ≠ none → input ∈ m.seen) :
    ∑' w, Pr{let z ← ((Query C →ₒ HashOutput).randomOracle q).run cache}[z = w] *
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
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hnone, OracleComp.tsum_prEvent_map_mul]
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
    rw [hraw, zero_add, SigningGuessLaneProof.digestCost, ite_eq_left hd] at h
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

end SigningPartnerBoundProof

end ThresholdLeanXmssSecurity
