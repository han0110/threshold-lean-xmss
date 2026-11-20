import ThresholdLeanXmssSecurity.Proof.SigningOneRun
import ThresholdLeanXmssSecurity.Proof.SigningTopRows

/-!
# The partner link with a paid flag

This module splits the bottom partner row by the release at the forged key. An unreleased partner
is paid by the input-side flag, and a released partner keeps the R1 split.

## The unreleased partner

The partner is unreleased when fewer than `t` operators can give the chain parts at the forged key
`e` (`ReleasedAt`, `signersAt`). Then the replayed honest key is unreleased too (`honestKey`).

* `bottomOpened` is then the chain end at every chain (`bottomOpened_of_not_released`). Every
  position below the end is a target of `chainTarget`.
* The descent gives a bottom partner from `same_layer` whether or not the key is released. On the
  honest key without its selection it reads the bottom layer as a fresh key. Then `fresh_layer`
  gives a hit or a guess below the end (`unreleased_badEvent`).
* A guess is a candidate of the verification on a hidden chain value. With all chain starts cached
  it hits `partialChainTarget` (`InputHitRow`). Otherwise `ForgedStartAbsent` holds (`AbsentRow`), and
  `absentRow_hit` gives a hit on `unopenedTopTarget`.

So an unreleased partner needs no grind at `e`. It is a charged hit or a row of the uncharged lane
(`win_cover_released`).

## The released partner

A release needs one honest round 2 at `e` (corruption stops at `t - 1`). Round 2 builds the bottom
tree (`bottomOnce`), which caches all PRF entries at `e`. It then runs `signCodeword` on the
combined parts (`signRound2With`). Their opening either opens `c_e` with the true randomizer or is
an `AlternativeCommitment`. With the true randomizer, the base call is a canonical base call of a
key with cached PRF entries. So the trigger `cachedExtra` of `SigningOneRun` grinds there.

* If the selection is a seen trial, the flag of `e` rises (`cachedTrial`).
* Otherwise the grind installs the digest of the selection as the target of `e`. The partner input
  has the same digest. Before the install it is pending, and the install hits. After the install a
  fresh call on it hits (`Monitor.fresh`). The verification calls it.

No other trigger is needed. `ReleasedLink` states this on the split one run. Its proof needs a run
invariant through the round 2 handler.

## Why the flag is on the joint run

A link on the split one run would read `HiddenInputHit` on the eager final cache. The
descent and the verification links (`runHasFinalState`, `verifyRun_verification`) apply only to
the lazy run, and `SigningOneRunProof.probEvent_oneRun` moves only events that do not read the cache. So
the unreleased partner is paid on `jointRun`, where the input-side row already lives.

## The results

* `unreleased_badEvent` and `win_cover_released` prove the split on the lazy run.
* `laneInputRow_of_unchargedRow` folds the three uncharged rows into one input-side row on the
  partial target or the unopened top target.
* `chargedLane_bound_oneRun` is the charged lane with the R1 bound of the one run.
* `ReleasedLink` is the link at a released key, by the argument above.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLinkPaidProof

open HashSig LeanXmss ThresholdLeanXmss SigningOpeningProof SigningUnchargedLoggedProof SigningAssemblyProof
  SigningTopRowsProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)
attribute [local irreducible] MonadAttach.support

/-! ## The release at the forged key -/

/-- At least `t` operators can give the chain parts at the key of the forgery for its bound
message. It reads only the state of the oracles. -/
def ReleasedAt (o : Option (TopTree × TsigState C × Forgery)) : Prop :=
  ∃ top state forgery, o = some (top, state, forgery) ∧ ∃ message,
    state.bound forgery.signature.leafIndex = some message ∧
      C.t ≤ (signersAt state forgery.signature.leafIndex message).card

/-- Without a release at the forged key, the replayed honest key is unreleased. -/
theorem honestKey_released_false (x : SigningSecurityProof.Keys3 C) (r : SigningCostProof.Outcome C)
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.2 = some (top, state, forgery))
    (hrel : ¬ReleasedAt r.1.2) :
    ((SigningCostProof.finalOf x r top state forgery).honestKey prims).released = false := by
  simp only [SigningDescentProof.FinalState.honestKey, SigningCostProof.finalOf]
  split
  · rename_i message hb
    exact decide_eq_false fun h => hrel ⟨top, state, forgery, hm, message, hb, h⟩
  · rfl

set_option maxRecDepth 100000 in
/-- A win without a release at the forged key is a hit, a guess or a top partner. The bottom layer
has no opened position, so it gives no bottom partner. The proof runs the descent on the honest key
without its selection, which reads the bottom layer as a fresh key. -/
theorem unreleased_badEvent (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningCostProof.Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (hrel : ¬ReleasedAt r.1.2) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      let z := SigningCostProof.finalOf x r top state forgery
      SigningDescentProof.Hit z.cache x.1 z.key (z.honestKey prims) ∨
        SigningDescentProof.Guess z.cache x.1 z.key (z.honestKey prims) forgery.message
          (XmssSecurity.Bridge.toModelSig forgery.signature) ∨
        SigningGuessProof.TopPartner prims x r := by
  obtain ⟨top, state, forgery, hsome, hwins, hcons⟩ := SigningCacheProof.runHasFinalState prims C A x r hr hwin
  refine ⟨top, state, forgery, hsome, ?_⟩
  obtain ⟨htopRoot, hcached, _⟩ := hcons
  have hverify := (SigningDescentProof.D_verify prims _ _ _ _).symm.trans hwins.1
  have hreleased := honestKey_released_false prims x r top state forgery hsome hrel
  let z := SigningCostProof.finalOf x r top state forgery
  let hk := z.honestKey prims
  let hk' : SigningDescentProof.HonestKey := { hk with selected := none }
  have hopened : SigningDescentProof.bottomOpened z.cache x.1 z.key hk' =
      SigningDescentProof.bottomOpened z.cache x.1 z.key hk := by
    exact (SigningDescentProof.bottomOpened_of_none _ _ _ _
      (by simp [hk', SigningDescentProof.selectedEncoding])).trans
      (SigningDescentProof.bottomOpened_of_not_released _ _ _ _ hreleased).symm
  rcases SigningDescentProof.descent z.cache z.key hk' (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩)
      forgery.message _ hverify htopRoot hcached (fun _ h => by simp [hk'] at h) with h | h | h | h
  · exact Or.inl h
  · obtain ⟨encoding, hencoding, hguess⟩ := h
    exact Or.inr (Or.inl ⟨encoding, hencoding, hopened ▸ hguess⟩)
  · obtain ⟨s, hs, -⟩ := h
    simp [hk'] at hs
  · exact Or.inr (Or.inr ⟨top, state, forgery, hsome, h⟩)

/-! ## The cover of the win with the released partner -/

/-- The bottom partner row at a released key. -/
def ReleasedPartnerRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  LazyPartnerRow prims x w ∧ ReleasedAt w.1.1.2

set_option maxRecDepth 100000 in
/-- A win is a charged output event, a released partner, or one of the three uncharged rows. A
partner at an unreleased key is a hit, a guess or a top partner (`unreleased_badEvent`). -/
theorem win_cover_released (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hwin : Win w) :
    Charged prims x w ∨ ReleasedPartnerRow prims x w ∨ UnchargedRow prims x w := by
  by_cases hrel : ReleasedAt w.1.1.2
  · rcases win_cover prims A x w hw hwin with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl ⟨h, hrel⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  by_cases hc : Charged prims x w
  · exact Or.inl hc
  obtain ⟨top, state, forgery, hm, hhit | hguess | htop⟩ :=
    unreleased_badEvent prims A x (w.1.1, w.2.1) (mem_exposedRun_of_joint prims A x w hw) hwin hrel
  · exact (hc (Or.inl ⟨hwin, top, state, forgery, hm, hhit⟩)).elim
  · by_cases habsent : SigningGuardedFlagProof.ForgedStartAbsent x (w.1, w.2.1)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, hc, habsent⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hwin, hc, SigningGuardedFlagProof.hiddenInputHit_partial prims x (w.1, w.2.1)
        (SigningGuessLinkProof.guess_hiddenInputHit prims A x (w.1, w.2.1)
          (mem_verifyRun_of_joint prims A x w hw) top state forgery hm hguess) habsent⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hc, htop, fun h => hc (Or.inr (Or.inr h))⟩)))

/-! ## The input-side row -/

/-- The input-side row of the uncharged lane. A candidate hits the partial chain target or the
unopened top target. -/
def LaneInputRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧
    (HiddenInputHit x (SigningGuardedFlagProof.partialChainTarget prims x (w.1, w.2.1)) (w.1, w.2.1) ∨
      HiddenInputHit x (unopenedTopTarget prims x (w.1, w.2.1)) (w.1, w.2.1))

set_option maxRecDepth 100000 in
/-- Each uncharged row is the input-side row, by `topRow_hit` and `absentRow_hit`. -/
theorem laneInputRow_of_unchargedRow (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (w : JointOutcome C) (hw : w ∈ support (jointRun prims A x)) (hrow : UnchargedRow prims x w) :
    LaneInputRow prims x w := by
  rcases hrow with ⟨hwin, hc, hhit⟩ | htop | habsent
  · exact ⟨hwin, hc, Or.inl hhit⟩
  · exact ⟨htop.1, htop.2.1, Or.inr (topRow_hit prims A x w hw htop)⟩
  · exact ⟨habsent.1, habsent.2.1, Or.inr (absentRow_hit prims A x w hw habsent)⟩

/-! ## The released partner on the one run -/

/-- The lane 2 row on the split one run. A released partner win with a cached selection at the
forged key. -/
def Lane2Row (x : SigningSecurityProof.Keys3 C) (z : SigningOneRunProof.SplitOutcome C) : Prop :=
  z.1.1.1 = (true, false) ∧ SigningPartnerLinkProof.BottomPartnerCase prims x (z.1.1, z.2.1.1.1.1) ∧
    ReleasedAt z.1.1.2 ∧ SigningOneRunProof.CachedSelectionAt z

/-- The link at a released key. A released partner win on the split one run with no cached selection
at the forged key hits the R1 monitor or has another opening of a commitment. -/
def ReleasedLink : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z,
    z ∈ support (SigningOneRunProof.splitRunAt prims A x) →
    z.1.1.1 = (true, false) → SigningPartnerLinkProof.BottomPartnerCase prims x (z.1.1, z.2.1.1.1.1) →
    ReleasedAt z.1.1.2 → ¬SigningOneRunProof.CachedSelectionAt z →
    SigningOneRunProof.R1HitRow z ∨ SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1

/-! ## The assembly -/

set_option maxRecDepth 100000 in
/-- The charged lane on the split one run. The charged output events on `jointRun` and the R1 hit
on the split one run (`SigningOneRunProof.split_r1Hit_bound`) have the sum bound `q / 2 ^ 128`. -/
theorem chargedLane_bound_oneRun (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr{let z ← jointRun prims A x}[Charged prims x z] +
        Pr{let z ← SigningOneRunProof.splitRunAt prims A x}[SigningOneRunProof.R1HitRow z] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  obtain ⟨T, hhit⟩ := SigningGuessProof.hit_bound_structural_cost prims A q x hx hkeys hq hsmall
  replace hhit : Pr{let z ← SigningDescentProof.exposedRun prims A x}[SigningCostProof.WinHit prims x z] ≤
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
  have h1 : Pr{let z ← jointRun prims A x}[Charged prims x z] = Pr{let z ← run}[SigningGuessProof.ChargedOutput prims x z] := by
    change _ = Pr{let z ← SigningDescentProof.exposedRun prims A x}[SigningGuessProof.ChargedOutput prims x z]
    rw [← SigningGuessLinkProof.verifyRun_forget, ← jointRun_verify, Functor.map_map, prEvent_map]
    rfl
  have h2 := prEvent_or_le run (SigningCostProof.WinHit prims x)
    (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1 ∨
      ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have h3 := prEvent_or_le run (fun r => SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1)
    (fun r => ∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1)
  have hsum := add_le_add (h2.trans (add_le_add hhit (h3.trans (add_le_add
    (SigningGuessProof.alternativeCommitment_bound_source prims A x)
    (SigningPartnerLinkProof.resolvedTopPartner_bound_topDigest prims A x)))))
    (SigningOneRunProof.split_r1Hit_bound prims A x)
  rw [← mul_add, ← mul_add, ← mul_add] at hsum
  rw [h1]
  refine hsum.trans ?_
  rw [div_eq_mul_inv, mul_comm (q : ℝ≥0∞)]
  refine mul_le_mul_right (le_trans (le_of_eq ?_) hcost) _
  rw [hdigest]
  ac_rfl

end SigningLinkPaidProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLinkPaidProof.win_cover_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLinkPaidProof.win_cover_released
