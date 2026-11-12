import ThresholdLeanXmssSecurity.Proof.SigningReleasedTransfer
import ThresholdLeanXmssSecurity.Proof.SigningLane2Flat
import ThresholdLeanXmssSecurity.Proof.SigningTopRowsCap

/-!
# The uncharged lane as one union on one run

`hiddenCoreAt_of_laneUnion` proves `HiddenCoreAt` from `ReleasedLink`, `LaneInputLogged`,
`Lane2TraceLink` and `LaneTraceCap`. The released partner row and the uncharged row move as one
event to `traceRun`, which is `splitRunAt` with a write-only leanVM trace and a stale bit
(`traceRun_forget`). There, one cap bounds the input-side hit, the stale base and the lane 2 event
together by `q / 2^128`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLaneUnionProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningJointEagerProof
  SigningOneRunProof SigningPartnerBoundProof SigningLane2BridgeProof SigningLane2FlatProof
  SigningOpeningProof SigningUnchargedLoggedProof SigningAssemblyProof SigningTopRowsProof
  SigningCacheLogProof SigningLinkPaidProof SigningLane2Proof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The input-side hit from the log -/

/-- The input-side hit of the uncharged lane, with each target read from the cache of the call log. -/
def LoggedInputHit (x : SigningSecurityProof.Keys3 C) (r : JointResult C × ℕ × QueryLog (WorldSpec C)) : Prop :=
  HiddenInputHit x (SigningGuardedFlagProof.partialChainTarget prims x (r.1, (logCache r.2.2, r.2.1)))
      (r.1, (logCache r.2.2, r.2.1)) ∨
    HiddenInputHit x (unopenedTopTarget prims x (r.1, (logCache r.2.2, r.2.1))) (r.1, (logCache r.2.2, r.2.1))

/-- The input-side row of the joint run is a hit that the log gives. -/
def LaneInputLogged : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C),
    w ∈ support (jointRun prims A x) → LaneInputRow prims x w →
    LoggedInputHit prims x (w.1, w.2.1.2, w.2.2)

/-! ## The split one run with the leanVM trace -/

/-- The state of the trace run. It adds the leanVM trace and the stale bit to the split one run. -/
abbrev TraceState (C : Committee) :=
  (((SigningHitLaneProof.LoggedState C × Monitor) × (XmssSecurity.LeafIndex → Bool)) ×
    (XmssSecurity.SigningCacheTrace × Bool)) × OpeningState C

/-- The trace step of a world call of the split one run. At a base call that runs the grind of
`cachedExtra`, a fresh base input appends the entry of the leanVM sign step. A cached base input at
a key with no entry sets the stale bit. Every other call keeps both. -/
def traceStepAt (seeds : C.Term → HashOutput) (P : PublicParameter) (cache : HashCache C) (st : TsigState C)
    (t : (WorldSpec C).Domain) (cache' : HashCache C) (aux : XmssSecurity.SigningCacheTrace × Bool) :
    XmssSecurity.SigningCacheTrace × Bool :=
  if h : ∃ e, SigningGuessProof.RandomizerCached seeds cache e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e) st t then
    match st.bound h.choose with
    | some message =>
      if cache (.hash (randomizerInput P bottomLayer h.choose
          (SigningGuessProof.cachedRandomizer seeds cache h.choose) (bytesLE 32 message))) = none then
        (aux.1 ++ [⟨⟨h.choose, message⟩,
          signOf (laneKey P) h.choose (cachedFound cache' P h.choose
            (SigningGuessProof.cachedRandomizer seeds cache h.choose) message),
          keptView IsMsg cache, keptView IsMsg cache'⟩], aux.2)
      else (aux.1, aux.2 || decide (h.choose ∉ aux.1.leafIndices))
    | none => aux
  else aux

/-- The world calls of the split one run with the trace and the stale bit. Both are write-only. -/
def traceWorld (x : SigningSecurityProof.Keys3 C) :
    QueryImpl (WorldSpec C) (StateT (TraceState C) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1, ((z.2.1,
      traceStepAt x.2.1 x.1 p.1.1.1.1.1.1 p.2.1.1 t z.2.1.1.1.1.1 p.1.2), z.2.2))) <$>
    (keyedSplitWorld prims (XmssSecurity.encodingInputLeafIndex? x.1) (jointCachedExtra x.2.1 x.1) t).run
      (p.1.1, p.2)

theorem traceWorld_forgets (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) :
    Forgets (traceWorld prims x t)
      (keyedSplitWorld prims (XmssSecurity.encodingInputLeafIndex? x.1) (jointCachedExtra x.2.1 x.1) t) := by
  intro a b s
  simp only [traceWorld, StateT.run_mk, Functor.map_map]
  exact id_map _

/-- The split one run with the trace and the stale bit. -/
def traceGame (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (TraceState C) ProbComp (JointResult C) :=
  jointGameWith A x (traceWorld prims x)
    (fun dealt => flatWith (SigningOpeningProof.openingOracles x dealt) (traceWorld prims x)) getCarried

set_option maxRecDepth 100000 in
theorem traceGame_forgets (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (traceGame prims A x)
      (SigningOneRunProof.splitGame prims (XmssSecurity.encodingInputLeafIndex? x.1) (jointCachedExtra x.2.1 x.1) A x) := by
  unfold traceGame SigningOneRunProof.splitGame jointGameWith
  dsimp only
  have hW := traceWorld_forgets (C := C) prims x
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

/-- An outcome of the trace run. -/
abbrev TraceOutcome (C : Committee) := JointResult C × TraceState C

/-- The trace run, from the empty trace and a false stale bit. -/
def traceRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (TraceOutcome C) :=
  (traceGame prims A x).run (((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)), SigningOneRunProof.monitoredInit.2)

/-- The split outcome of a trace outcome. -/
def splitOf (z : TraceOutcome C) : SigningOneRunProof.SplitOutcome C := (z.1, (z.2.1.1, z.2.2))

/-- Without the trace and the stale bit, the trace run is the split one run. -/
theorem traceRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    splitOf <$> traceRun prims A x = SigningOneRunProof.splitRunAt prims A x :=
  traceGame_forgets prims A x _ _ _

/-- The observable part of a trace outcome, the result, the count and the call log. -/
def observed (z : TraceOutcome C) : JointResult C × ℕ × QueryLog (WorldSpec C) :=
  (z.1, z.2.1.1.1.1.1.2, z.2.1.1.1.1.2)

/-- The leanVM cache and trace of a state of the trace run. -/
def traceView (s : TraceState C) : XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace :=
  (keptView IsMsg s.1.1.1.1.1.1, s.1.2.1)

/-- A base call ran its grind on a cached base input at a key with no trace entry. -/
def StaleBaseAt (z : TraceOutcome C) : Prop := z.2.1.2.2 = true

/-- The lane 2 event of leanVM on the trace run. -/
def GhostAt (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C) : Prop :=
  ghostEvent (laneKey x.1) traceView (z.2, z.2.1.1.1.1.1.2)

/-- The lane 2 row is a stale base or the lane 2 event of leanVM. -/
def Lane2TraceLink : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (z : TraceOutcome C),
    z ∈ support (traceRun prims A x) → Lane2Row prims x (splitOf z) →
    StaleBaseAt z ∨ GhostAt x z

/-- The one cap of the uncharged lane on the trace run. An input-side hit, a stale base or the
lane 2 event of leanVM has probability at most `q / 2^128`. -/
def LaneTraceCap : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[fun z => LoggedInputHit prims x (observed z) ∨ StaleBaseAt z ∨ GhostAt x z |
      traceRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128

/-! ## The assembly -/

set_option maxRecDepth 100000 in
/-- The count of the trace run is within the budget. -/
theorem traceRun_count_le (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (z : TraceOutcome C) (hz : z ∈ support (traceRun prims A x)) : (observed z).2.1 ≤ q := by
  have hs : splitOf z ∈ support (SigningOneRunProof.splitRunAt prims A x) := by
    rw [← traceRun_forget, support_map]
    exact ⟨z, hz, rfl⟩
  obtain ⟨w, hw, -, hcount, -⟩ := SigningReleasedTransferProof.splitRun_source prims A x (splitOf z) hs
  have hl : (w.1.1, w.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
    rw [← jointRun_logged, support_map]
    exact ⟨w, hw, rfl⟩
  exact (le_of_eq hcount.symm).trans (SigningGuessLaneProof.loggedRun_count_le prims A x q hq _ hl)

set_option maxRecDepth 100000 in
/-- `HiddenCoreAt` from the link at a released key and the three parts of the union cap. -/
theorem hiddenCoreAt_of_laneUnion (hlink : ReleasedLink prims (C := C))
    (hin : LaneInputLogged prims (C := C)) (hl2 : Lane2TraceLink prims (C := C))
    (hcap : LaneTraceCap prims (C := C)) : SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hkeys hq hsmall
  rw [SigningCostProof.signingHashError_eq, probEvent_core_eq_win]
  have hcharged := chargedLane_bound_oneRun prims A q x hx hkeys hq hsmall
  let Ev : JointResult C × ℕ × QueryLog (WorldSpec C) → Prop := fun r =>
    SigningReleasedTransferProof.LoggedReleasedRow prims x r ∨ LoggedInputHit prims x r
  have h1 : Pr[Win | jointRun prims A x] ≤ Pr[Charged prims x | jointRun prims A x] +
      Pr[fun w => ReleasedPartnerRow prims x w ∨ UnchargedRow prims x w | jointRun prims A x] :=
    (probEvent_mono fun w hw hwin => win_cover_released prims A x w hw hwin).trans (probEvent_or_le _ _ _)
  have h2 : Pr[fun w => ReleasedPartnerRow prims x w ∨ UnchargedRow prims x w | jointRun prims A x] ≤
      Pr[fun w => Ev (w.1, w.2.1.2, w.2.2) | jointRun prims A x] := by
    refine probEvent_mono fun w hw h => ?_
    rcases h with h | h
    · left
      have hl : (w.1.1, w.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
        rw [← jointRun_logged, support_map]
        exact ⟨w, hw, rfl⟩
      exact (and_congr (SigningPartnerTransferProof.lazyPartnerRow_congr prims x w.1.1 w.1.2
        w.2.1.2 w.2.2 (loggedRun_cacheFromLog prims A x (w.1.1, w.2) hl)) Iff.rfl).mp h
    · right
      exact hin A x w hw (laneInputRow_of_unchargedRow prims A x w hw h)
  have h3 : Pr[fun w => Ev (w.1, w.2.1.2, w.2.2) | jointRun prims A x] =
      Pr[fun z => Ev (observed z) | traceRun prims A x] := by
    rw [← probEvent_oneRun prims A x Ev, ← splitRunAt_oneRun, probEvent_map, ← traceRun_forget, probEvent_map]
    rfl
  have h4 : Pr[fun z => Ev (observed z) | traceRun prims A x] ≤
      Pr[fun z => SigningOneRunProof.R1HitRow (splitOf z) ∨
        (LoggedInputHit prims x (observed z) ∨ StaleBaseAt z ∨ GhostAt x z) | traceRun prims A x] := by
    refine probEvent_mono fun z hz h => ?_
    have hs : splitOf z ∈ support (SigningOneRunProof.splitRunAt prims A x) := by
      rw [← traceRun_forget, support_map]
      exact ⟨z, hz, rfl⟩
    rcases h with h | h
    · obtain ⟨hwin, hpartner, hrel, halt⟩ :=
        SigningReleasedTransferProof.splitRun_released_partner prims A x (splitOf z) hs h
      by_cases hcached : SigningOneRunProof.CachedSelectionAt (splitOf z)
      · exact Or.inr (Or.inr (hl2 A x z hz ⟨hwin, hpartner, hrel, hcached⟩))
      · rcases hlink A x (splitOf z) hs hwin hpartner hrel hcached with hhit | hcommit
        · exact Or.inl hhit
        · exact (halt hcommit).elim
    · exact Or.inr (Or.inl h)
  have h5 : Pr[fun z => SigningOneRunProof.R1HitRow (splitOf z) ∨
        (LoggedInputHit prims x (observed z) ∨ StaleBaseAt z ∨ GhostAt x z) | traceRun prims A x] ≤
      Pr[SigningOneRunProof.R1HitRow | SigningOneRunProof.splitRunAt prims A x] + (q : ℝ≥0∞) / 2 ^ 128 := by
    refine (probEvent_or_le _ _ _).trans (add_le_add (le_of_eq ?_) (hcap A q x hx hkeys hq hsmall))
    rw [← traceRun_forget, probEvent_map]
    rfl
  refine h1.trans ((add_le_add le_rfl (h2.trans ((le_of_eq h3).trans (h4.trans h5)))).trans ?_)
  refine le_trans (le_of_eq ?_) (add_le_add hcharged le_rfl)
  ring

end SigningLaneUnionProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneUnionProof.hiddenCoreAt_of_laneUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneUnionProof.hiddenCoreAt_of_laneUnion

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneUnionProof.traceRun_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneUnionProof.traceRun_forget
