import ThresholdLeanXmssSecurity.Proof.SigningJointEager
import ThresholdLeanXmssSecurity.Proof.SigningR1Fixed
import ThresholdLeanXmssSecurity.Proof.SigningUnchargedCap

/-!
# The signing assembly on one run

This module puts the R1 monitor, the per-key cached selection and the verification candidates on
one run, the joint eager run with the cached trigger of `SigningR1Fixed`.

## The results

* `oneRun` is `jointGame` of `SigningJointEager` with `eagerWorld` and the trigger `cachedExtra`.
  `evalDist_oneRun` gives the law of `jointRun` for the result, the candidates, the count and the
  log. The proof is `hashLaw_eagerWorld`, which holds for each extra call.
* `monitoredRun` adds the R1 monitor of `SigningFlatEager`. `potStep_monitoredGame` walks the joint
  game. `r1Hit_bound` bounds the hit by `2^-128` for each bottom digest call in expectation.
* `splitRunAt` adds one write-only flag of a cached trial for each key (`keyedSplitOracle`).
  `CachedSelectionAt` reads the flag at the key of the forgery, so the row is per key.
  `split_r1Hit_bound` is the R1 bound on it, and `splitRunAt_oneRun` forgets it to `oneRun`.

## `R1Link` with the true-opening disjunct is false

`Released` of `SigningOpening` releases the bottom opening of `e` once `bound e` is set. Round 1 of
one honest operator sets `bound e`, but it caches only the PRF entries of the terms of that
operator. So a guess of the opening after round 1 is not a candidate, and it is not yet a base
call of a cached key. The argument is on the support, as in `SigningR1Fixed`.

1. Take `t = 2` with two operators and no corruption. A term is a set of `t - 1` operators, and
   its holders are the other operators, so operator `1` holds no copy of the term `{1}`. The
   forger asks round 1 of operator `1` at `e` on `m` with the quorum of both. `eval` reads only
   the terms of `L J 1`, so this sets `bound e` and leaves the entry of `{1}` at
   `.randomizer bottomLayer e` uncached.
2. The forger asks `H` at the base input of `e` and `m` with a guess `ρ'`. The call is a base call,
   but `RandomizerCached` fails, so `cachedExtra` runs no grind. The opening is released, so
   `unreleasedCandidates` logs nothing. The forger then asks the trials up to the first codeword
   and a partner `(m', r')` with the same digest.
3. The forger asks `.tree (treeOf e)`. The setup caches all PRF entries at `e`. Take a support
   point where their XOR is `ρ'`. No later call is a base call.
4. Steps 4 and 5 of the counterexample of `SigningR1Fixed` follow unchanged. No grind ran, so the
   monitor installs no target and no flag rises. No commitment collides. The candidate log has no
   opening of `e`, so `TrueOpeningHit` is false. The verification suffix logs no opening of `e`,
   because `bound e` is set. `BottomPartnerCase` holds with the selection of step 2.

The guess costs `2^-128` per call, but no row of the current table logs it. Two trigger choices change which event records it.

* The first trigger choice in `SigningR1Fixed`. The trigger runs the grind at each world call after
  which the PRF entries, the bound message and the base answer of a key are all cached. After
  step 3 the grind meets the seen trials of step 2, so the flag of `e` rises. This keeps
  `TrueOpeningHit` and the input-side event of `SigningUnchargedCap`.
* A candidate at each call that carries the opening of a key whose PRF entries are not all cached,
  read from the call log. This changes the input-side event of the uncharged lane, so the cap of
  `SigningUnchargedCap` changes with it.

## The interface hypotheses

* `R1Link` is stated in its exact form and is false. The cap of `SigningUnchargedCap` on this run and the assembly
  of `HiddenCoreAt` from `TopRow` and `AbsentRow` depend on its fix and are not stated here.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningOneRunProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningJointEagerProof

variable {C : Committee} (prims : Primitives)

section Eager

/-- The trigger of `cachedExtra` on the joint state. It reads the flat part of the state. -/
def jointCachedExtra (seeds : C.Term → HashOutput) (P : PublicParameter) (p : FlatJointState C)
    (t : (WorldSpec C).Domain) (p' : FlatJointState C) : OracleComp (Query C →ₒ HashOutput) Unit :=
  SigningR1FixedProof.cachedExtra seeds P (p.1, p.2.1) t (p'.1, p'.2.1)

/-- The joint run with the eager grind of `cachedExtra` at the keys `x`. -/
def oneRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (JointResult C × FlatJointState C) :=
  (jointGame (eagerWorld prims (jointCachedExtra x.2.1 x.1)) A x).run jointInit

/-- The one run preserves the result, the count, both logs and the carried state. -/
theorem evalDist_oneRun_rest (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> oneRun prims A x] =
      𝒟[(fun z => (z.1, restOf z.2)) <$>
        (jointGame (carry (SigningCostProof.loggedImpl prims)) A x).run jointInit] :=
  evalDist_jointGame_eq prims _ _ (hashLaw_eagerWorld prims _) (hashLaw_carry_logged prims) A x

/-- The eager law of the one run. The result, the verification candidates, the count and the call
log have the law of `jointRun`. -/
theorem evalDist_oneRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> oneRun prims A x] =
      𝒟[(fun z => (z.1, z.2.1.2, z.2.2)) <$> SigningUnchargedLoggedProof.jointRun prims A x] := by
  have h := congrArg
    (fun d => (fun z : JointResult C × Rest C (OpeningState C) => (z.1, z.2.1)) <$> d)
    (evalDist_oneRun_rest prims A x)
  simp only [← evalDist_map, Functor.map_map] at h
  rw [← jointGame_eq_jointRun, Functor.map_map]
  exact h

/-- Each event on the observable joint outcome has the same probability on the one run. -/
theorem probEvent_oneRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (event : JointResult C × (ℕ × QueryLog (WorldSpec C)) → Prop) :
    Pr[fun z => event (z.1, z.2.1.1.2, z.2.1.2) | oneRun prims A x] =
      Pr[fun z => event (z.1, z.2.1.2, z.2.2) | SigningUnchargedLoggedProof.jointRun prims A x] := by
  have h := evalDist_oneRun prims A x
  have hp : Pr[event | (fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> oneRun prims A x] =
      Pr[event | (fun z => (z.1, z.2.1.2, z.2.2)) <$>
        SigningUnchargedLoggedProof.jointRun prims A x] := by
    simp only [probEvent_eq_tsum_indicator, probOutput_def, h]
  simpa only [probEvent_map, Function.comp_def] using hp

end Eager

section Monitor

open SigningPartnerBoundProof

/-- The one run with the R1 monitor of `SigningFlatEager`. -/
def monitoredGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT ((SigningHitLaneProof.LoggedState C × Monitor) × OpeningState C) ProbComp (JointResult C) :=
  jointGameWith A x (monitoredWorld prims keyOf extra)
    (fun dealt => flatWith (SigningOpeningProof.openingOracles x dealt) (monitoredWorld prims keyOf extra))
    getCarried

set_option maxRecDepth 100000 in
theorem monitoredGame_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (monitoredGame prims keyOf extra A x) (jointGame (eagerWorld prims extra) A x) := by
  unfold monitoredGame jointGame jointGameWith
  dsimp only
  have hW := monitoredWorld_forgets prims keyOf extra
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

set_option maxRecDepth 100000 in
/-- The monitored one run pays `2^-128` for each keyed call. -/
theorem potStep_monitoredGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    PotStep keyOf (monitoredGame prims keyOf extra A x) := by
  unfold monitoredGame jointGameWith
  dsimp only
  have hW := potStep_monitoredWorld prims (σ := OpeningState C) keyOf extra
  have hsetup : SigningHitProof.ProgramFree (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  refine potStep_bind keyOf (potStep_simulateQ_world keyOf _ hW _ hsetup) fun r => ?_
  rcases r with _ | (top | tree)
  · exact potStep_pure keyOf _
  · refine potStep_bind keyOf (potStep_simulateQ keyOf _
      (fun t => potStep_flatWith keyOf _ (programFree_openingOracles x top) _ hW t) _) fun a => ?_
    refine potStep_bind keyOf (potStep_getCarried keyOf) fun s => ?_
    refine potStep_bind keyOf (potStep_simulateQ_world keyOf _ hW _
      (programFree_tsigFinishLogged x top s.2.1 _)) fun w => ?_
    exact potStep_pure keyOf _
  · exact potStep_pure keyOf _

/-- The initial state of the monitored one run. -/
def monitoredInit : (SigningHitLaneProof.LoggedState C × Monitor) × OpeningState C :=
  ((SigningHitLaneProof.loggedInit, Monitor.empty), ((SigningCoreProof.tsigInit, false), ∅, []))

/-- The one run with the R1 monitor. -/
def monitoredRun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    ProbComp (JointResult C × (SigningHitLaneProof.LoggedState C × Monitor) × OpeningState C) :=
  (monitoredGame prims keyOf (jointCachedExtra x.2.1 x.1) A x).run monitoredInit

theorem monitoredRun_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> monitoredRun prims keyOf A x = oneRun prims A x :=
  monitoredGame_forgets prims keyOf _ A x _ _ _

/-- The hit costs `2^-128` for each keyed call of the log in expectation. -/
theorem probEvent_hit_le_logKeyed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun z => z.2.1.2.hit = true | monitoredRun prims keyOf A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' z, Pr[= z | monitoredRun prims keyOf A x] *
        (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) := by
  classical
  have hinit : CacheSeen (monitoredInit (C := C)).1.1.1.1 (monitoredInit (C := C)).1.2 :=
    fun input h => (h rfl).elim
  have h := (potStep_monitoredGame prims keyOf (jointCachedExtra x.2.1 x.1) A x monitoredInit hinit).2
  have hrisk : (monitoredInit (C := C)).1.2.risk = 0 := by
    simp [monitoredInit, Monitor.risk, Monitor.empty,
      XmssSecurity.CappedEncodingMonitor.State.pendingRisk_empty]
  have hlog : logKeyed keyOf (monitoredInit (C := C)).1.1.2 = 0 := rfl
  rw [hrisk, zero_add, hlog] at h
  simp only [Nat.sub_zero] at h
  refine le_trans ?_ h
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun z => ?_
  split_ifs with hz
  · have hone : z.2.1.2.risk = 1 := by simp [Monitor.risk, hz]
    rw [hone, mul_one]
    exact le_rfl
  · exact bot_le

/-- The keyed calls of the log of the monitored one run have the law of those of `loggedRun`. -/
theorem expected_logKeyed_eq (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr[= z | monitoredRun prims keyOf A x] * (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) =
      ∑' z, Pr[= z | SigningCostProof.loggedRun prims A x] * (logKeyed keyOf z.2.2 : ℝ≥0∞) := by
  have h1 := tsum_probOutput_map_mul (monitoredRun prims keyOf A x) (fun z => (z.1, (z.2.1.1, z.2.2)))
    (fun y => (logKeyed keyOf y.2.1.2 : ℝ≥0∞))
  rw [monitoredRun_forget] at h1
  have h2 := tsum_probOutput_map_mul (oneRun prims A x) (fun z => (z.1, z.2.1.1.2, z.2.1.2))
    (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have h3 := tsum_probOutput_map_mul (SigningUnchargedLoggedProof.jointRun prims A x)
    (fun z => (z.1, z.2.1.2, z.2.2)) (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have h4 := tsum_probOutput_map_mul (SigningUnchargedLoggedProof.jointRun prims A x)
    (fun z => (z.1.1, z.2)) (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  rw [SigningUnchargedLoggedProof.jointRun_logged] at h4
  have hlaw := evalDist_oneRun prims A x
  rw [← h1, h4]
  refine (h2.symm.trans ?_).trans h3
  exact tsum_congr fun y => by rw [probOutput_congr rfl hlaw]

/-- The bound of R1 on the one run. The hit costs `2^-128` for each bottom digest call. -/
theorem r1Hit_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun z => z.2.1.2.hit = true | monitoredRun prims (XmssSecurity.encodingInputLeafIndex? x.1) A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine (probEvent_hit_le_logKeyed prims _ A x).trans ?_
  rw [expected_logKeyed_eq]
  gcongr
  exact (expected_logKeyed_le prims _ A x).trans
    (SigningGuessProof.sourceExpectedCost_mono prims A x _ _ (SigningPartnerBoundProof.keyedCost_le_bottomDigestCost x))

end Monitor

section Split

open SigningPartnerBoundProof

/-- The keys of a cached trial. A trial at an input of key `e` raises the flag of `e` when
`cachedTrial` holds. -/
def cachedTrialAt (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor) (q : Query C)
    (output : HashOutput) (e : XmssSecurity.LeafIndex) : Bool :=
  match q with
  | .hash input => cachedTrial keyOf m (.hash input : Query C) output && decide (keyOf input = some e)
  | _ => false

/-- `monitoredOracle` with a write-only flag of a cached trial for each key. -/
def keyedSplitOracle (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    QueryImpl (Query C →ₒ HashOutput)
      (StateT ((HashCache C × Monitor) × (XmssSecurity.LeafIndex → Bool)) ProbComp) :=
  fun q => StateT.mk fun s => (fun w => (w.1, (w.2, fun e => s.2 e || cachedTrialAt keyOf s.1.2 q w.1 e))) <$>
    (monitoredOracle keyOf q).run s.1

theorem keyedSplitOracle_run_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {β : Type}
    (ob : OracleComp (Query C →ₒ HashOutput) β) (s : HashCache C × Monitor) (b : XmssSecurity.LeafIndex → Bool) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (keyedSplitOracle keyOf) ob).run (s, b) =
      (simulateQ (monitoredOracle keyOf) ob).run s :=
  SigningCoreProof.simulateQ_run_forget _ _ (fun q c b => by
    simp only [keyedSplitOracle, StateT.run_mk, Functor.map_map]
    exact id_map _) ob s b

/-- `monitoredWorld` with the flag of a cached trial for each key. -/
def keyedSplitWorld (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit) :
    QueryImpl (WorldSpec C)
      (StateT (((SigningHitLaneProof.LoggedState C × Monitor) × (XmssSecurity.LeafIndex → Bool)) ×
        OpeningState C) ProbComp) :=
  fun t => StateT.mk fun p => (carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1, p.2) >>= fun z =>
    (fun y => (z.1, ((((ofRest y.2.1.1 (restOf z.2)).1, y.2.1.2), y.2.2), (ofRest y.2.1.1 (restOf z.2)).2))) <$>
      (simulateQ (keyedSplitOracle keyOf) (extra (p.1.1.1, p.2) t z.2)).run
        ((z.2.1.1.1, queryEntryStep keyOf p.1.1.2 (hashEntry ⟨t, z.1⟩)), p.1.2)

theorem keyedSplitWorld_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (t : (WorldSpec C).Domain) :
    Forgets (keyedSplitWorld prims keyOf extra t) (monitoredWorld prims keyOf extra t) := by
  intro a b s
  simp only [keyedSplitWorld, monitoredWorld, StateT.run_mk, map_bind, Functor.map_map]
  refine bind_congr fun z => ?_
  rw [← keyedSplitOracle_run_forget keyOf _ _ b, Functor.map_map]

/-- The monitored one run with the flag of a cached trial for each key. -/
def splitGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (((SigningHitLaneProof.LoggedState C × Monitor) × (XmssSecurity.LeafIndex → Bool)) ×
      OpeningState C) ProbComp (JointResult C) :=
  jointGameWith A x (keyedSplitWorld prims keyOf extra)
    (fun dealt => flatWith (SigningOpeningProof.openingOracles x dealt) (keyedSplitWorld prims keyOf extra))
    getCarried

set_option maxRecDepth 100000 in
theorem splitGame_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatJointState C → (WorldSpec C).Domain → FlatJointState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (splitGame prims keyOf extra A x) (monitoredGame prims keyOf extra A x) := by
  unfold splitGame monitoredGame jointGameWith
  dsimp only
  have hW := keyedSplitWorld_forgets prims keyOf extra
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

/-- An outcome of the split one run. -/
abbrev SplitOutcome (C : Committee) :=
  JointResult C × ((SigningHitLaneProof.LoggedState C × Monitor) × (XmssSecurity.LeafIndex → Bool)) ×
    OpeningState C

/-- The split one run at the public parameter and the seeds of the keys. -/
def splitRunAt (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (SplitOutcome C) :=
  (splitGame prims (XmssSecurity.encodingInputLeafIndex? x.1) (jointCachedExtra x.2.1 x.1) A x).run
    ((monitoredInit.1, fun _ => false), monitoredInit.2)

theorem splitRunAt_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> splitRunAt prims A x =
      monitoredRun prims (XmssSecurity.encodingInputLeafIndex? x.1) A x :=
  splitGame_forgets prims _ _ A x _ _ _

/-- The split one run forgets to the one run. -/
theorem splitRunAt_oneRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1.1, z.2.2))) <$> splitRunAt prims A x = oneRun prims A x := by
  rw [← monitoredRun_forget prims (XmssSecurity.encodingInputLeafIndex? x.1), ← splitRunAt_forget,
    Functor.map_map]

/-- The cached selection at the key of the forgery. A grind at that key met a selection that the
log holds before the call. -/
def CachedSelectionAt (z : SplitOutcome C) : Prop :=
  ∃ top state forgery, z.1.1.2 = some (top, state, forgery) ∧ z.2.1.2 forgery.signature.leafIndex = true

/-- The hit of the R1 monitor on the split one run. -/
def R1HitRow (z : SplitOutcome C) : Prop :=
  z.2.1.1.2.hit = true

/-- The bound of R1 on the split one run. -/
theorem split_r1Hit_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[R1HitRow | splitRunAt prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine le_trans (le_of_eq ?_) (r1Hit_bound prims A x)
  rw [← splitRunAt_forget, probEvent_map]
  rfl

end Split

section Link

/-- `R1Link` on the split one run, with the true-opening disjunct. A bottom partner win with no cached
selection at the forged key hits the R1 monitor, has another opening of a commitment, or has a
candidate that carried the true opening before its release. It is false, by the counterexample in
the module doc. -/
def R1Link : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z, z ∈ support (splitRunAt prims A x) →
    z.1.1.1 = (true, false) → SigningPartnerLinkProof.BottomPartnerCase prims x (z.1.1, z.2.1.1.1.1) →
    ¬CachedSelectionAt z →
    R1HitRow z ∨ SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 ∨
      SigningOpeningProof.TrueOpeningHit x (z.1, z.2.1.1.1.1)

end Link

end SigningOneRunProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOneRunProof.evalDist_oneRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOneRunProof.evalDist_oneRun

/-- info: 'ThresholdLeanXmssSecurity.SigningOneRunProof.probEvent_oneRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOneRunProof.probEvent_oneRun

/-- info: 'ThresholdLeanXmssSecurity.SigningOneRunProof.r1Hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOneRunProof.r1Hit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOneRunProof.split_r1Hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOneRunProof.split_r1Hit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOneRunProof.splitRunAt_oneRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOneRunProof.splitRunAt_oneRun
