import ThresholdLeanXmssSecurity.Proof.SigningGuardedFlag
import ThresholdLeanXmssSecurity.Proof.SigningFlatEager
import ThresholdLeanXmssSecurity.Proof.SigningLane2Bridge

/-!
# The assembly of the signing core

This module states `SigningCoreProof.HiddenCoreAt` from plain probability bounds, one row for each
bad event, with one split of the bottom partner.

## The runs

* `jointRun` holds the result, the opening candidates, the final lazy cache and the call log.
  `jointRun_logged` and `jointRun_verify` give `loggedRun`, `verifyRun` and `exposedRun` exactly.
* `splitRunAt ρ` is `SigningFlatEagerProof.splitRun` at `P := x.1` and `ρ x`. It holds the R1
  monitor and the flag `CachedSelection`. Its law of the result, the count and the log is that of
  `loggedRun` (`evalDist_flatEagerRun_logged`). Its final cache is the eager cache.
* No run holds both the candidates and the R1 monitor. So the partner row crosses from `jointRun`
  to `splitRunAt ρ` in one named step, `PartnerCrossing`.

## The split

The split of the bottom partner is the R1 predicate, `CachedSelection`. It replaces
`FreshSelection` of `SigningGuardedFlag`.

* A selection that the log does not hold before the base call is installed by the R1 monitor at
  the base call. A later partner call hits it (`R1Hit`, charged lane).
* A selection that the log holds before the base call is the cached selection of leanVM lane 2
  (uncharged lane).

## The budget table

Let `N = 2^128`. Each counted call (`signCost = 1`) has two units of `1 / N`, one in each lane.
The sum is `2 q / N = signingHashError q` (`SigningCostProof.signingHashError_eq`).

| call | target | lane | step bound |
| --- | --- | --- | --- |
| structural call (`structuralHitCost`) | the hit of the final cache (`WinHit`) | C | `1 / N` for each call in expectation |
| commitment call (`commitmentCost`) | another opening of `c_e` (`AlternativeCommitment`) | C | `1 / N` for each call in expectation |
| top digest call (`anyTopDigestInput`) | the resolved top partner (`ResolvedTopPartner`) | C | `1 / N` for each call in expectation |
| bottom digest call (`bottomDigestCost`) | the selected digest that the base call installs (`R1Hit`) | C | `1 / N` for each call in expectation |
| input-side call (opening or hidden chain value) | the hidden value before its release (`HiddenInputHit` on `partialChainTarget`) | U | `1 / N` for each counted call, under the cap `q` |
| bottom encoding call, cached selection | the selection that the log holds before the base call (leanVM lane 2, `f1` and `f4`) | U | `1 / N` for each counted output-side call, under the cap `q` |
| top encoding call | the top partner that no ceremony resolves | U | no payer (D17) |
| none | a chain start at the forged key with an absent PRF entry (`ForgedStartAbsent`) | U | no payer (D17) |

* Lane C is an expectation. `source_output_costs_le` bounds the four costs by `q` together. The
  bottom digest cost is the cost of `bottomPartnerLogged_bound` and of `r1Hit_bound`, so `R1Hit`
  takes the place of `BottomPartnerLogged` at no extra cost (`chargedLane_bound`).
* Lane U is one cap. `SigningLane2Proof.probEvent_lane2_le` bounds the probability of the
  input-side flag or the lane 2 event in one hybrid by `q / N`, with `q` the count of the run. So
  the rows of lane U have no separate bounds. `UnchargedRow` is the union of the three rows on
  `jointRun`. `UnchargedLaneCap` bounds its probability plus that of the lane 2 row on the split
  run. The lemma does not give this sum over two runs.
* leanVM pays the calls outside its count with `firstLaneSlack = 2^19`. Here `signCost` counts
  each call of `H`, of the PRG and of the programming oracle, and only uniform sampling is free.
  So no slack enters. `lane2_constants` checks the lane 2 constants at `N = 2^128`
  and `q < 2^127`.

## The open steps

* `PartnerCrossing ρ`. `partnerCrossing_of_link` reduces it to `R1Link` of `SigningFlatEager` and
  `PartnerTransfer ρ`, the transfer of the lazy partner row to the eager cache.
* `UnchargedLaneCap ρ`. The rows of the unresolved top partner and of `ForgedStartAbsent` depend
  on D17 (memoized bottom trees). They have their exact events here and no proof. No result
  bounds the mass of `AbsentRow` today, so the truth of the cap also waits on D17.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningAssemblyProof

open LeanXmss ThresholdLeanXmss SigningUnchargedLoggedProof SigningFlatEagerProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The rows on the joint run -/

/-- The win without the flag. -/
def Win (w : JointOutcome C) : Prop :=
  w.1.1.1 = (true, false)

/-- The charged output events on the final lazy cache. -/
def Charged (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  SigningGuessProof.ChargedOutput prims x (w.1.1, w.2.1)

/-- The input-side row. A candidate carried a hidden value before its release, on the partial
chain target. -/
def InputHitRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧
    SigningOpeningProof.HiddenInputHit x (SigningGuardedFlagProof.partialChainTarget prims x (w.1, w.2.1))
      (w.1, w.2.1)

/-- The bottom partner row on the final lazy cache, before the split. -/
def LazyPartnerRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ SigningPartnerLinkProof.BottomPartnerCase prims x (w.1.1, w.2.1)

/-- The row of the top partner that no successful bottom ceremony resolves. -/
def TopRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ SigningGuessProof.TopPartner prims x (w.1.1, w.2.1) ∧
    ¬∃ key, SigningGuessProof.ResolvedTopPartner x key w.2.1.1

/-- The row of a chain start at the forged key with an absent PRF entry. -/
def AbsentRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ SigningGuardedFlagProof.ForgedStartAbsent x (w.1, w.2.1)

/-- The three rows of the uncharged lane on the joint run. -/
def UnchargedRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  InputHitRow prims x w ∨ TopRow prims x w ∨ AbsentRow prims x w

/-! ## The rows on the split run -/

/-- The split run at the public parameter of the keys and the randomizer values `ρ x`. -/
def splitRunAt (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    ProbComp (Result C × ((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) ×
      (TsigState C × Bool)) :=
  splitRun prims (XmssSecurity.encodingInputLeafIndex? x.1) x.1 (ρ x) A x

/-- An outcome of the split run. -/
abbrev SplitOutcome (C : Committee) :=
  Result C × ((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) × (TsigState C × Bool)

/-- The hit of the R1 monitor. -/
def R1HitRow (z : SplitOutcome C) : Prop :=
  z.2.1.1.2.hit = true

/-- The win with a bottom partner on the final eager cache. -/
def EagerPartner (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C) : Prop :=
  z.1.1 = (true, false) ∧ SigningPartnerLinkProof.BottomPartnerCase prims x (z.1, z.2.1.1.1.1)

/-- The lane 2 row. The bottom partner with a selection that the log holds before the base call. -/
def CachedPartnerRow (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C) : Prop :=
  EagerPartner prims x z ∧ CachedSelection z

/-! ## The cover of the win on the joint run -/

set_option maxRecDepth 100000 in
/-- A win is a charged output event or one of the four rows of the lazy cover. -/
theorem win_cover (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hwin : Win w) :
    Charged prims x w ∨ InputHitRow prims x w ∨ LazyPartnerRow prims x w ∨ TopRow prims x w ∨
      AbsentRow prims x w := by
  by_cases hc : Charged prims x w
  · exact Or.inl hc
  have ho := mem_exposedRun_of_joint prims A x w hw
  obtain ⟨top, state, forgery, hm, hbad⟩ :=
    SigningCacheProof.signing_run_badEvent_closed prims A x (w.1.1, w.2.1) ho hwin
  rcases hbad with hhit | hguess | hbottom | htop
  · exact (hc (Or.inl ⟨hwin, top, state, forgery, hm, hhit⟩)).elim
  · by_cases habsent : SigningGuardedFlagProof.ForgedStartAbsent x (w.1, w.2.1)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hc, habsent⟩)))
    · exact Or.inr (Or.inl ⟨hwin, hc, SigningGuardedFlagProof.hiddenInputHit_partial prims x (w.1, w.2.1)
        (SigningGuessLinkProof.guess_hiddenInputHit prims A x (w.1, w.2.1)
          (mem_verifyRun_of_joint prims A x w hw) top state forgery hm hguess) habsent⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hwin, hc, top, state, forgery, hm, hbottom⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hc, ⟨top, state, forgery, hm, htop⟩,
      fun h => hc (Or.inr (Or.inr h))⟩)))

/-- The win without the flag of the signing core is the win of the joint run. -/
theorem probEvent_core_eq_win (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true | runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] =
      Pr[Win | jointRun prims A x] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, ← SigningCostProof.loggedRun_forget,
    ← jointRun_logged, Functor.map_map, Functor.map_map, probEvent_map]
  refine probEvent_ext fun w _ => ?_
  simp only [Function.comp_apply, Win]
  constructor
  · intro h
    exact Prod.ext h.2 h.1
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The win is at most the sum of the charged event, the lazy partner row and the uncharged rows. -/
theorem probEvent_win_le_rows (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[Win | jointRun prims A x] ≤
      Pr[Charged prims x | jointRun prims A x] + Pr[LazyPartnerRow prims x | jointRun prims A x] +
        Pr[UnchargedRow prims x | jointRun prims A x] := by
  have hcover : Pr[Win | jointRun prims A x] ≤ Pr[fun w => Charged prims x w ∨ LazyPartnerRow prims x w ∨
      UnchargedRow prims x w | jointRun prims A x] := by
    refine probEvent_mono fun w hw hwin => ?_
    rcases win_cover prims A x w hw hwin with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have h1 := probEvent_or_le (jointRun prims A x) (Charged prims x)
    (fun w => LazyPartnerRow prims x w ∨ UnchargedRow prims x w)
  have h2 := probEvent_or_le (jointRun prims A x) (LazyPartnerRow prims x) (UnchargedRow prims x)
  refine hcover.trans (h1.trans ?_)
  rw [add_assoc]
  exact add_le_add le_rfl h2

/-! ## The charged lane -/

set_option maxRecDepth 100000 in
/-- The charged lane. `R1HitRow` takes the place of `BottomPartnerLogged` in
`SigningPartnerBoundProof.chargedOutputLogged_bound`, with the same bottom digest cost. -/
theorem chargedLane_bound (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) (A : TsigAdversary C) (q : ℕ)
    (x : SigningSecurityProof.Keys3 C) (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr[Charged prims x | jointRun prims A x] + Pr[R1HitRow | splitRunAt prims ρ A x] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
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
  have h1 : Pr[Charged prims x | jointRun prims A x] = Pr[SigningGuessProof.ChargedOutput prims x | run] := by
    change _ = Pr[_ | SigningDescentProof.exposedRun prims A x]
    rw [← SigningGuessLinkProof.verifyRun_forget, ← jointRun_verify, Functor.map_map, probEvent_map]
    rfl
  have h2 := probEvent_or_le run (SigningCostProof.WinHit prims x)
    (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1 ∨
      ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have h3 := probEvent_or_le run (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (fun r => ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have hsum := add_le_add (h2.trans (add_le_add hhit (h3.trans (add_le_add
    (SigningGuessProof.alternativeCommitment_bound_source prims A x)
    (SigningPartnerLinkProof.resolvedTopPartner_bound_topDigest prims A x)))))
    (split_r1Hit_bound prims x.1 (ρ x) A x)
  rw [← mul_add, ← mul_add, ← mul_add] at hsum
  rw [h1]
  refine hsum.trans ?_
  rw [div_eq_mul_inv, mul_comm (q : ℝ≥0∞)]
  refine mul_le_mul_right (le_trans (le_of_eq ?_) hcost) _
  rw [hdigest]
  ac_rfl

/-! ## The split of the bottom partner -/

/-- The transfer of the lazy partner row to the final eager cache. A lazy partner row has the
law of a partner win on the eager cache without another opening of a commitment. -/
def PartnerTransfer (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[LazyPartnerRow prims x | jointRun prims A x] ≤
      Pr[fun z => EagerPartner prims x z ∧ ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 |
        splitRunAt prims ρ A x]

/-- The crossing of the partner row. The lazy partner row is at most the hit of the R1 monitor
(charged lane) and the lane 2 row (uncharged lane) on the split run. -/
def PartnerCrossing (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[LazyPartnerRow prims x | jointRun prims A x] ≤
      Pr[R1HitRow | splitRunAt prims ρ A x] + Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x]

set_option maxRecDepth 100000 in
/-- The split on the split run. A partner win without another opening of a commitment hits the R1
monitor or has a cached selection, by `R1Link`. -/
theorem partnerCrossing_of_link (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (hlink : R1Link prims ρ) (htransfer : PartnerTransfer prims ρ) : PartnerCrossing prims ρ := by
  intro A q x hx hkeys hq hsmall
  refine (htransfer A q x hx hkeys hq hsmall).trans ((probEvent_mono fun z hz h => ?_).trans (probEvent_or_le _ _ _))
  obtain ⟨⟨hwin, hpartner⟩, halt⟩ := h
  by_cases hcached : CachedSelection z
  · exact Or.inr ⟨⟨hwin, hpartner⟩, hcached⟩
  · rcases hlink A x z hz hwin hpartner hcached with hhit | hcommit
    · exact Or.inl hhit
    · exact (halt hcommit).elim

/-! ## The uncharged lane -/

/-- The cap of the uncharged lane. The rows of lane U share one cap of `q / 2^128`, as the
input-side flag and the lane 2 event share it in `SigningLane2Proof.probEvent_lane2_le`. The rows
`TopRow` and `AbsentRow` have no payer before D17. -/
def UnchargedLaneCap (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[UnchargedRow prims x | jointRun prims A x] + Pr[CachedPartnerRow prims x | splitRunAt prims ρ A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128

/-- The constants of leanVM lane 2 at `N = 2^128`. The moment `A` is at most `N` for `q < 2^127`,
and the cap `q / N` of `probEvent_lane2_le` is `q / 2^128`. No slack enters. -/
theorem lane2_constants {q : ℕ} (hq : q < 2 ^ 127) :
    ENNReal.ofReal (XmssSecurity.Partner.momentA XmssSecurity.Ghost.pReal q) ≤
        (Fintype.card XmssSecurity.Digest : ℝ≥0∞) ∧
      (q : ℝ≥0∞) * (Fintype.card XmssSecurity.Digest : ℝ≥0∞)⁻¹ = (q : ℝ≥0∞) / 2 ^ 128 := by
  refine ⟨?_, ?_⟩
  · have hcard : Fintype.card XmssSecurity.Digest = 2 ^ XmssSecurity.digestBits := by simp
    rw [hcard]
    exact XmssSecurity.Ghost.momentA_le_N hq
  · rw [SigningPartnerBoundProof.card_digest_inv, div_eq_mul_inv]

/-! ## The assembly -/

/-- `HiddenCoreAt` from the crossing of the partner row and the cap of the uncharged lane. The
charged lane is `chargedLane_bound`. -/
theorem hiddenCoreAt_of_rows (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (hcross : PartnerCrossing prims ρ) (hcap : UnchargedLaneCap prims ρ) :
    SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hkeys hq hsmall
  rw [SigningCostProof.signingHashError_eq, probEvent_core_eq_win]
  have hcharged := chargedLane_bound prims ρ A q x hx hkeys hq hsmall
  have huncharged := hcap A q x hx hkeys hq hsmall
  refine (probEvent_win_le_rows prims A x).trans ?_
  refine (add_le_add (add_le_add le_rfl (hcross A q x hx hkeys hq hsmall)) le_rfl).trans ?_
  refine le_trans (le_of_eq ?_) (add_le_add hcharged huncharged)
  ring

/-- `HiddenCoreAt` from `R1Link`, the transfer of the partner row and the cap of the uncharged
lane. -/
theorem hiddenCoreAt_of_link (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (hlink : R1Link prims ρ) (htransfer : PartnerTransfer prims ρ) (hcap : UnchargedLaneCap prims ρ) :
    SigningCoreProof.HiddenCoreAt prims C :=
  hiddenCoreAt_of_rows prims ρ (partnerCrossing_of_link prims ρ hlink htransfer) hcap

end SigningAssemblyProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningAssemblyProof.hiddenCoreAt_of_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningAssemblyProof.hiddenCoreAt_of_link

/-- info: 'ThresholdLeanXmssSecurity.SigningAssemblyProof.chargedLane_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningAssemblyProof.chargedLane_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningAssemblyProof.probEvent_win_le_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningAssemblyProof.probEvent_win_le_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningAssemblyProof.lane2_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningAssemblyProof.lane2_constants
