import ThresholdLeanXmssSecurity.Proof.SigningJointEager
import ThresholdLeanXmssSecurity.Proof.SigningR1Fixed

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
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningOneRunProof

open HashSig LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningJointEagerProof

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
    ((fun z => (z.1, restOf z.2)) <$> oneRun prims A x) =ᵈ
      ((fun z => (z.1, restOf z.2)) <$>
        (jointGame (carry (SigningCostProof.loggedImpl prims)) A x).run jointInit) :=
  evalDist_jointGame_eq prims _ _ (hashLaw_eagerWorld prims _) (hashLaw_carry_logged prims) A x

/-- The eager law of the one run. The result, the verification candidates, the count and the call
log have the law of `jointRun`. -/
theorem evalDist_oneRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ((fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> oneRun prims A x) =ᵈ
      ((fun z => (z.1, z.2.1.2, z.2.2)) <$> SigningUnchargedLoggedProof.jointRun prims A x) := by
  have h := (evalDist_oneRun_rest prims A x).map
    (fun z : JointResult C × Rest C (OpeningState C) => (z.1, z.2.1))
  simp only [Functor.map_map] at h
  rw [← jointGame_eq_jointRun, Functor.map_map]
  exact h

/-- Each event on the observable joint outcome has the same probability on the one run. -/
theorem probEvent_oneRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (event : JointResult C × (ℕ × QueryLog (WorldSpec C)) → Prop) :
    Pr{let z ← oneRun prims A x}[event (z.1, z.2.1.1.2, z.2.1.2)] =
      Pr{let z ← SigningUnchargedLoggedProof.jointRun prims A x}[event (z.1, z.2.1.2, z.2.2)] := by
  have h := evalDist_oneRun prims A x
  have hp : Pr{let y ← (fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> oneRun prims A x}[event y] =
      Pr{let y ← ((fun z => (z.1, z.2.1.2, z.2.2)) <$>
        SigningUnchargedLoggedProof.jointRun prims A x)}[event y] := by
    exact h.prEvent_eq _
  simpa only [prEvent_map, Function.comp_def] using hp

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
    Pr{let z ← monitoredRun prims keyOf A x}[z.2.1.2.hit = true] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' z, Pr{let y ← monitoredRun prims keyOf A x}[y = z] *
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
  rw [OracleComp.prEvent_eq_tsum_ite]
  refine tsum_le_tsum fun z => ?_
  split_ifs with hz
  · have hone : z.2.1.2.risk = 1 := by simp [Monitor.risk, hz]
    rw [hone, mul_one]
    exact le_rfl
  · exact bot_le

/-- The keyed calls of the log of the monitored one run have the law of those of `loggedRun`. -/
theorem expected_logKeyed_eq (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr{let y ← monitoredRun prims keyOf A x}[y = z] * (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) =
      ∑' z, Pr{let y ← SigningCostProof.loggedRun prims A x}[y = z] * (logKeyed keyOf z.2.2 : ℝ≥0∞) := by
  have h1 := OracleComp.tsum_prEvent_map_mul (monitoredRun prims keyOf A x) (fun z => (z.1, (z.2.1.1, z.2.2)))
    (fun y => (logKeyed keyOf y.2.1.2 : ℝ≥0∞))
  rw [monitoredRun_forget] at h1
  have h2 := OracleComp.tsum_prEvent_map_mul (oneRun prims A x) (fun z => (z.1, z.2.1.1.2, z.2.1.2))
    (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have h3 := OracleComp.tsum_prEvent_map_mul (SigningUnchargedLoggedProof.jointRun prims A x)
    (fun z => (z.1, z.2.1.2, z.2.2)) (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have h4 := OracleComp.tsum_prEvent_map_mul (SigningUnchargedLoggedProof.jointRun prims A x)
    (fun z => (z.1.1, z.2)) (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  rw [SigningUnchargedLoggedProof.jointRun_logged] at h4
  have hlaw := evalDist_oneRun prims A x
  rw [← h1, h4]
  refine (h2.symm.trans ?_).trans h3
  exact tsum_congr fun y => by rw [hlaw.prEvent_eq (· = y)]

/-- The bound of R1 on the one run. The hit costs `2^-128` for each bottom digest call. -/
theorem r1Hit_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr{let z ← monitoredRun prims (XmssSecurity.encodingInputLeafIndex? x.1) A x}[z.2.1.2.hit = true] ≤
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
    Pr{let z ← splitRunAt prims A x}[R1HitRow z] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine le_trans (le_of_eq ?_) (r1Hit_bound prims A x)
  rw [← splitRunAt_forget, prEvent_map]
  rfl

end Split

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
