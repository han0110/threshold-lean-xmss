import ThresholdLeanXmssSecurity.Proof.SigningOwnClaim
import ThresholdLeanXmssSecurity.Proof.SigningOwnHitBound
import ThresholdLeanXmssSecurity.Proof.SigningOwnAlt
import ThresholdLeanXmssSecurity.Proof.SigningOwnTopBound
import ThresholdLeanXmssSecurity.Proof.SigningOwnStopRun
import ThresholdLeanXmssSecurity.Proof.SigningOwnCap
import ThresholdLeanXmssSecurity.Proof.SeedHitOwn

/-! # The signing claim with the budget of the forger alone, from its first stage

- `chargedLaneOwnStop` is the charged lane with the own budget. It joins the hit bound, the bound of
  a second opening of a commitment, the top partner bound and the R1 bound.
- `laneTraceCapOwn` is the capped lane with the own budget.
- `hiddenCoreOwnAt` is the second stage `SigningOwnClaim.HiddenCoreOwnAt` from the two lanes.
- `signingOwnBudget_of_flag` is `SigningOwnBudgetStatement` from the first stage
  `SigningOwnClaim.DistinctFlagOwn`.
- `signingOwnBudget` is `SigningOwnBudgetStatement` with no premise.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnBudget

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningFlatProof SigningFlatEagerProof SigningJointEagerProof
  SigningOneRunProof SigningPartnerBoundProof SigningLane2BridgeProof SigningLane2FlatProof
  SigningOpeningProof SigningUnchargedLoggedProof SigningAssemblyProof SigningTopRowsProof
  SigningCacheLogProof SigningLinkPaidProof SigningLane2Proof SigningLaneUnionProof
open SigningOwnForger SigningOwnGateBlock SigningOwnVerify SigningOwnClaim

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The R1 bound with the own budget, with a stop at the first second opening of a commitment. One
unit pays the bottom digest call of the verification. -/
def R1Own : Prop :=
  ∀ (A : TsigAdversary C) (x : Keys3 C),
    Pr[fun z => SigningOneRunProof.R1HitRow z ∧
        ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 |
        SigningOneRunProof.splitRunAt prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (forgerCost prims A x (ownDomainUnit (BottomDigestInput x)) + (1 : ℕ))

/-- `R1Own` from the bound on the source run. -/
theorem r1Own_of_source (h : SigningOwnStop.R1OwnSource prims (C := C)) : R1Own prims (C := C) := by
  intro A x
  refine (h A x).trans ?_
  gcongr
  exact ownKeyed_source_le_forgerCost prims A x

/-- The charged lane with the own budget, with the R1 row stopped at the first second opening of a
commitment. -/
def ChargedLaneOwnStop : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 → HasSigningOwnBound A q →
    q + signingSlack < 2 ^ 127 →
    Pr[Charged prims x | jointRun prims A x] +
        Pr[fun z => SigningOneRunProof.R1HitRow z ∧
            ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 |
          SigningOneRunProof.splitRunAt prims A x] ≤
      ((q + chargedSlack : ℕ) : ℝ≥0∞) / 2 ^ 128

set_option maxRecDepth 100000 in
/-- The charged lane from the four bounds with the own budget. -/
theorem chargedLaneOwnStop_of_parts (hhit : SigningOwnHitBound.HitOwn prims (C := C))
    (halt : SigningOwnAlt.AltOwn prims (C := C)) (htop : SigningOwnTopBound.TopOwn prims (C := C))
    (hr1 : R1Own prims (C := C)) : ChargedLaneOwnStop prims (C := C) := by
  intro A q x hx hkeys hown hsmall
  have hhit := hhit A q x hx hkeys hown hsmall
  have halt := halt A x
  have htop := htop A x
  have hr1 := hr1 A x
  let run := SigningDescentProof.exposedRun prims A x
  have h1 : Pr[Charged prims x | jointRun prims A x] = Pr[SigningGuessProof.ChargedOutput prims x | run] := by
    change _ = Pr[_ | SigningDescentProof.exposedRun prims A x]
    rw [← SigningGuessLinkProof.verifyRun_forget, ← jointRun_verify, Functor.map_map, probEvent_map]
    rfl
  have h2 := probEvent_or_le run (SigningCostProof.WinHit prims x)
    (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1 ∨
      ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have h3 := probEvent_or_le run (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (fun r => ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have hsum := add_le_add (h2.trans (add_le_add hhit (h3.trans (add_le_add halt htop)))) hr1
  rw [h1]
  refine hsum.trans ?_
  rw [← mul_add, ← mul_add, ← mul_add, div_eq_mul_inv, mul_comm ((q + chargedSlack : ℕ) : ℝ≥0∞)]
  refine mul_le_mul_right ?_ _
  have hcost := forgerCost_le prims A q x _ hown (units_le x)
  rw [forgerCost_add, forgerCost_add, forgerCost_add] at hcost
  have hslack : ((q + chargedSlack : ℕ) : ℝ≥0∞) = (q : ℝ≥0∞) + (((2 ^ 16 + 382 : ℕ) : ℝ≥0∞) + (1 : ℕ) + (1 : ℕ)) := by
    unfold chargedSlack
    push_cast
    ring
  rw [hslack]
  refine le_trans (le_of_eq ?_) (add_le_add hcost le_rfl)
  ring

/-- The charged lane from the bound on the source run of R1. -/
theorem chargedLaneOwnStop_of_r1 (hr1 : SigningOwnStop.R1OwnSource prims (C := C)) :
    ChargedLaneOwnStop prims (C := C) :=
  chargedLaneOwnStop_of_parts prims
    (SigningOwnHitBound.hitOwn_of_gate prims (keyGateBoundOwn_of_block prims))
    (SigningOwnAlt.altOwn prims) (SigningOwnTopBound.topOwn prims) (r1Own_of_source prims hr1)

/-- The charged lane with the own budget. -/
theorem chargedLaneOwnStop : ChargedLaneOwnStop prims (C := C) :=
  chargedLaneOwnStop_of_r1 prims (SigningOwnStop.r1OwnSource prims)

/-- The capped lane with the own budget. -/
theorem laneTraceCapOwn : SigningOwnCap.LaneTraceCapOwn (C := C) prims :=
  SigningOwnCap.laneTraceCapOwn_of_clean prims (SigningCompilerO1Clean.compilerCouplingClean prims)
    (SigningOwnCap.ownCapClean prims)

/-- The bound of the core as the sum of the two lanes. -/
theorem ofReal_signingHashError_own (q : ℕ) :
    ENNReal.ofReal (signingHashError (q + signingSlack)) =
      ((q + chargedSlack : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((q + capSlack : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  rw [SigningCostProof.signingHashError_eq, ← ENNReal.add_div, ← ENNReal.add_div]
  congr 1
  have h : (q + signingSlack) + (q + signingSlack) = (q + chargedSlack) + (q + capSlack) := by
    have := slack_split
    omega
  exact_mod_cast h

set_option maxRecDepth 100000 in
/-- `HiddenCoreOwnAt` from the stopped charged lane and the capped lane. The released partner comes
with no second opening of a commitment (`splitRun_released_partner`), so the stopped R1 row is
enough. -/
theorem hiddenCoreOwnAt_of_lanes_stop (hcharged : ChargedLaneOwnStop prims (C := C))
    (hcap : SigningOwnCap.LaneTraceCapOwn (C := C) prims) : HiddenCoreOwnAt prims C := by
  intro A q x hx hkeys hown hsmall
  have hlink := SigningLaneFinal.releasedLink prims (C := C)
  have hin := SigningLaneInputLoggedProof.laneInputLogged prims (C := C)
  have hl2 := SigningLane2TraceLinkProof.lane2TraceLink prims (C := C)
  rw [ofReal_signingHashError_own, probEvent_core_eq_win]
  have hcharged := hcharged A q x hx hkeys hown hsmall
  let Ev : JointResult C × ℕ × QueryLog (WorldSpec C) → Prop := fun r =>
    NoFlag r ∧ NotChargedLogged prims x r ∧ (SigningReleasedTransferProof.LoggedReleasedRow prims x r ∨ LoggedInputHit prims x r)
  have h1 : Pr[Win | jointRun prims A x] ≤ Pr[Charged prims x | jointRun prims A x] +
      Pr[fun w => ReleasedPartnerRow prims x w ∨ UnchargedRow prims x w | jointRun prims A x] :=
    (probEvent_mono fun w hw hwin => win_cover_released prims A x w hw hwin).trans (probEvent_or_le _ _ _)
  have h2 : Pr[fun w => ReleasedPartnerRow prims x w ∨ UnchargedRow prims x w | jointRun prims A x] ≤
      Pr[fun w => Ev (w.1, w.2.1.2, w.2.2) | jointRun prims A x] := by
    refine probEvent_mono fun w hw h => ?_
    have hl : (w.1.1, w.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
      rw [← jointRun_logged, support_map]
      exact ⟨w, hw, rfl⟩
    have hwin : Win w ∧ ¬Charged prims x w := by
      rcases h with h | h | h | h
      · exact ⟨h.1.1, h.1.2.1⟩
      · exact ⟨h.1, h.2.1⟩
      · exact ⟨h.1, h.2.1⟩
      · exact ⟨h.1, h.2.1⟩
    refine ⟨congrArg Prod.snd hwin.1, ?_, ?_⟩
    · exact (not_congr (SigningPartnerTransferProof.chargedOutput_congr prims x w.1.1 w.2.1.2
        (loggedRun_cacheFromLog prims A x (w.1.1, w.2) hl))).mp hwin.2
    rcases h with h | h
    · left
      exact (and_congr (SigningPartnerTransferProof.lazyPartnerRow_congr prims x w.1.1 w.1.2
        w.2.1.2 w.2.2 (loggedRun_cacheFromLog prims A x (w.1.1, w.2) hl)) Iff.rfl).mp h
    · right
      exact hin A x w hw (laneInputRow_of_unchargedRow prims A x w hw h)
  have h3 : Pr[fun w => Ev (w.1, w.2.1.2, w.2.2) | jointRun prims A x] =
      Pr[fun z => Ev (observed z) | traceRun prims A x] := by
    rw [← probEvent_oneRun prims A x Ev, ← splitRunAt_oneRun, probEvent_map, ← traceRun_forget, probEvent_map]
    rfl
  have h4 : Pr[fun z => Ev (observed z) | traceRun prims A x] ≤
      Pr[fun z => (SigningOneRunProof.R1HitRow (splitOf z) ∧
          ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 (splitOf z).2.1.1.1.1.1) ∨
        (NoFlag (observed z) ∧ NotChargedLogged prims x (observed z) ∧ (LoggedInputHit prims x (observed z) ∨ StaleBaseAt z ∨ GhostAt x z)) |
        traceRun prims A x] := by
    refine probEvent_mono fun z hz h => ?_
    obtain ⟨hnf, hnc, h⟩ := h
    have hs : splitOf z ∈ support (SigningOneRunProof.splitRunAt prims A x) := by
      rw [← traceRun_forget, support_map]
      exact ⟨z, hz, rfl⟩
    rcases h with h | h
    · obtain ⟨hwin, hpartner, hrel, halt⟩ :=
        SigningReleasedTransferProof.splitRun_released_partner prims A x (splitOf z) hs h
      by_cases hcached : SigningOneRunProof.CachedSelectionAt (splitOf z)
      · exact Or.inr ⟨hnf, hnc, Or.inr (hl2 A x z hz ⟨hwin, hpartner, hrel, hcached⟩)⟩
      · rcases hlink A x (splitOf z) hs hwin hpartner hrel hcached with hhit | hcommit
        · exact Or.inl ⟨hhit, halt⟩
        · exact (halt hcommit).elim
    · exact Or.inr ⟨hnf, hnc, Or.inl h⟩
  have h5 : Pr[fun z => (SigningOneRunProof.R1HitRow (splitOf z) ∧
          ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 (splitOf z).2.1.1.1.1.1) ∨
        (NoFlag (observed z) ∧ NotChargedLogged prims x (observed z) ∧ (LoggedInputHit prims x (observed z) ∨ StaleBaseAt z ∨ GhostAt x z)) |
        traceRun prims A x] ≤
      Pr[fun z => SigningOneRunProof.R1HitRow z ∧
            ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 |
          SigningOneRunProof.splitRunAt prims A x] +
        ((q + capSlack : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
    refine (probEvent_or_le _ _ _).trans (add_le_add (le_of_eq ?_) (hcap A q x hx hkeys hown hsmall))
    rw [← traceRun_forget, probEvent_map]
    rfl
  refine h1.trans ((add_le_add le_rfl (h2.trans ((le_of_eq h3).trans (h4.trans h5)))).trans ?_)
  refine le_trans (le_of_eq ?_) (add_le_add hcharged le_rfl)
  ring

/-- `HiddenCoreOwnAt` with the own budget. -/
theorem hiddenCoreOwnAt : HiddenCoreOwnAt prims C :=
  hiddenCoreOwnAt_of_lanes_stop prims (chargedLaneOwnStop prims) (laneTraceCapOwn prims)

/-- The claim from the two stages. The split on the flag keeps `¬KeyCollision` on both sides, so no
call of the dealer pays for a collision. -/
theorem signingOwnBudget_of_core (hflag : DistinctFlagOwn prims C) (hcore : HiddenCoreOwnAt prims C) :
    SigningOwnBudgetStatement prims C := by
  intro A q hown
  have hhit0 : 0 ≤ seedHitError C q := by unfold seedHitError; positivity
  have hcoll0 : 0 ≤ seedCollisionError C := by unfold seedCollisionError; positivity
  by_cases hlarge : 2 ^ 127 ≤ q + signingSlack
  · have h1 : tsigAdvantage prims A ≤ 1 := by
      unfold tsigAdvantage signingAccepts
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact probEvent_le_one)
    have h2 : (1 : ℝ) ≤ signingHashError (q + signingSlack) := by
      unfold signingHashError
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast hlarge
    linarith
  · have hsmall : q + signingSlack < 2 ^ 127 := Nat.lt_of_not_le hlarge
    have hε : 0 ≤ signingHashError (q + signingSlack) := by unfold signingHashError; positivity
    rw [tsigAdvantage_eq]
    have hs := probEvent_win_split prims A
    have hsplit : Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A] ≤
        Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A] +
          Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true |
            flaggedRun prims A] := by
      rw [keyedRun_eq_flaggedRun, probEvent_map]
      refine le_trans (probEvent_mono fun z _ h => ?_) (probEvent_or_le _ _ _)
      by_cases hz : z.2.1.2 = true
      · exact Or.inl ⟨h.1, hz⟩
      · exact Or.inr ⟨h.1, by simpa using hz, h.2⟩
    have hF : (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A]).toReal ≤
        seedHitError C q := by
      refine (toReal_le_div (hflag A q hown)).trans ?_
      unfold seedHitError
      have hcard : Fintype.card (KeySlot C) = C.n.choose (C.t - 1) + C.n.choose 2 := by
        rw [Fintype.card_sum, card_term, card_pair]
      have hle : Fintype.card (KeySlot C) * q ≤ (C.n.choose (C.t - 1) + C.n ^ 2) * q :=
        Nat.mul_le_mul_right q (by rw [hcard]; exact Nat.add_le_add_left (choose_two_le_sq _) _)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)
    have hH : (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true |
        flaggedRun prims A]).toReal ≤ signingHashError (q + signingSlack) := by
      refine ENNReal.toReal_le_of_le_ofReal hε ?_
      unfold flaggedRun
      refine probEvent_bind_le_of_forall_le fun x hx => ?_
      rw [probEvent_map]
      by_cases hc : KeyCollision x.2.1 x.2.2
      · simp [Function.comp_def, hc]
      · simp only [Function.comp_def, hc, not_false_eq_true, true_and]
        exact hcore A q x hx hc hown hsmall
    calc (Pr[fun z => z.2.1 = true | keyedRun prims A]).toReal
        ≤ (Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3] +
            Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A]).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hs
      _ = (Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3]).toReal +
            (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A]).toReal :=
          ENNReal.toReal_add probEvent_ne_top probEvent_ne_top
      _ ≤ seedCollisionError C +
            (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A] +
              Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true |
                flaggedRun prims A]).toReal :=
          add_le_add keyCollision_toReal_le
            (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hsplit)
      _ = seedCollisionError C +
            ((Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = true | flaggedRun prims A]).toReal +
              (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true |
                flaggedRun prims A]).toReal) := by
          rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top]
      _ ≤ seedCollisionError C + (seedHitError C q + signingHashError (q + signingSlack)) :=
          add_le_add le_rfl (add_le_add hF hH)
      _ = _ := by ring

/-- The signing claim with the budget of the forger alone, from its first stage. -/
theorem signingOwnBudget_of_flag (hflag : DistinctFlagOwn prims C) : SigningOwnBudgetStatement prims C :=
  signingOwnBudget_of_core prims hflag (hiddenCoreOwnAt prims)

/-- The signing claim with the budget of the forger alone. -/
theorem signingOwnBudget (C : Committee) : SigningOwnBudgetStatement prims C :=
  signingOwnBudget_of_flag prims (SeedHitOwn.distinctFlagOwn prims)

end ThresholdLeanXmssSecurity.SigningOwnBudget

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.r1Own_of_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.r1Own_of_source

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.chargedLaneOwnStop_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.chargedLaneOwnStop_of_parts

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.chargedLaneOwnStop_of_r1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.chargedLaneOwnStop_of_r1

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.chargedLaneOwnStop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.chargedLaneOwnStop

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.laneTraceCapOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.laneTraceCapOwn

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.ofReal_signingHashError_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.ofReal_signingHashError_own

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.hiddenCoreOwnAt_of_lanes_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.hiddenCoreOwnAt_of_lanes_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.hiddenCoreOwnAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.hiddenCoreOwnAt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget_of_core

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget_of_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget_of_flag

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnBudget.signingOwnBudget
