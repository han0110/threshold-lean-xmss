import ThresholdLeanXmssSecurity.Proof.SigningSignedSeparation
import ThresholdLeanXmssSecurity.Proof.SigningOwnForger
import ThresholdLeanXmssSecurity.Proof.SigningOwnR1

/-!
# The split run with a ledger and the stopped R1 potential

`ledgerWorld` is the world of the split run with a write-only ledger. The ledger adds `stopCharge`
at each call. `stopCharge` is one at a fresh bottom digest call before the first second opening of
a commitment, and zero in each other case.

* `ledgerRun_forget` states that the ledger run forgets to the split run.
* `LedgerStep` is `PotStep` of `SigningFlatEager` with the stopped potential
  `SigningOwnR1.stopRisk` and the ledger as the cost.
* `keyedSplitOracle_run_stopRisk_le` states that a trial run of the split world does not raise the
  stopped potential.
* `ledgerStep_world` states that one call of the ledger world pays its rise of the stopped
  potential with its charge.
* `ledgerRun_stopRisk_le` bounds the stopped potential at the end of the ledger run by `2^-128` for
  each unit of the ledger.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningOwnStop

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningJointEagerProof
  SigningPartnerBoundProof SigningReleasedLinkProof SigningReleasedAlignProof SigningOwnForger

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The ledger run -/

theorem logCost_logQuery (c : (WorldSpec C).Domain → ℕ) (log : QueryLog (WorldSpec C))
    (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) :
    SigningGuessLaneProof.logCost c (log.logQuery t u) = SigningGuessLaneProof.logCost c log + c t := by
  simp [SigningGuessLaneProof.logCost, QueryLog.logQuery, QueryLog.singleton]

/-- The charge of one world call for the stopped potential. It is zero after a second opening of a
commitment. Before, it is one at a bottom digest input that is not in the cache. -/
def stopCharge (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (t : (WorldSpec C).Domain) : ℕ :=
  if SigningGuessProof.AlternativeCommitment x.2.1 x.1 cache then 0
  else SigningOwnR1.freshKeyedCost (XmssSecurity.encodingInputLeafIndex? x.1) cache t

/-- The state of the split run with a ledger. -/
abbrev LedgerState (C : Committee) :=
  (((SigningHitLaneProof.LoggedState C × Monitor) × (XmssSecurity.LeafIndex → Bool)) × ℕ) × OpeningState C

/-- The world of the split run with a write-only ledger. The ledger adds `stopCharge` at the cache
before the call. -/
def ledgerWorld (x : SigningSecurityProof.Keys3 C) :
    QueryImpl (WorldSpec C) (StateT (LedgerState C) ProbComp) :=
  fun t => StateT.mk fun p =>
    (fun r => (r.1, ((r.2.1, p.1.2 + stopCharge x p.1.1.1.1.1.1 t), r.2.2))) <$>
      (world prims x t).run (p.1.1, p.2)

theorem ledgerWorld_forgets (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) :
    Forgets (ledgerWorld prims x t) (world prims x t) := by
  intro a b s
  simp only [ledgerWorld, StateT.run_mk, Functor.map_map]
  exact id_map _

/-- The split game with the ledger. -/
def ledgerGame (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (LedgerState C) ProbComp (JointResult C) :=
  jointGameWith A x (ledgerWorld prims x)
    (fun dealt => flatWith (SigningOpeningProof.openingOracles x dealt) (ledgerWorld prims x)) getCarried

theorem ledgerGame_forgets (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (ledgerGame prims A x) (SigningOneRunProof.splitGame prims
      (XmssSecurity.encodingInputLeafIndex? x.1) (SigningOneRunProof.jointCachedExtra x.2.1 x.1) A x) := by
  unfold ledgerGame SigningOneRunProof.splitGame jointGameWith
  dsimp only
  have hW := ledgerWorld_forgets prims x
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

/-- The initial state of the ledger run. -/
def ledgerInit : LedgerState C :=
  (((SigningOneRunProof.monitoredInit.1, fun _ => false), 0), SigningOneRunProof.monitoredInit.2)

/-- The split run with the ledger. -/
def ledgerRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (JointResult C × LedgerState C) :=
  (ledgerGame prims A x).run ledgerInit

/-- The ledger run forgets to the split run. -/
theorem ledgerRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> ledgerRun prims A x =
      SigningOneRunProof.splitRunAt prims A x :=
  ledgerGame_forgets prims A x _ _ _

/-- One call of the ledger world is one call of the split world, and the ledger adds the charge. -/
theorem ledgerWorld_support (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain)
    (p : LedgerState C) (r : (WorldSpec C).Range t × LedgerState C)
    (hr : r ∈ support ((ledgerWorld prims x t).run p)) :
    (r.1, (r.2.1.1, r.2.2)) ∈ support ((world prims x t).run (p.1.1, p.2)) ∧
      r.2.1.2 = p.1.2 + stopCharge x p.1.1.1.1.1.1 t := by
  simp only [ledgerWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact ⟨hw, rfl⟩

/-- A run of the ledger world forgets to a run of the split world. -/
theorem ledger_run_forget {α : Type} (x : SigningSecurityProof.Keys3 C) (oa : OracleComp (WorldSpec C) α)
    (p : LedgerState C) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) :
    (r.1, (r.2.1.1, r.2.2)) ∈ support ((simulateQ (world prims x) oa).run (p.1.1, p.2)) := by
  have h := forgets_simulateQ (ledgerWorld prims x) (world prims x) (ledgerWorld_forgets prims x) oa
    p.1.1 p.1.2 p.2
  rw [← h, support_map]
  exact ⟨r, hr, rfl⟩

/-! ## The potential part -/

/-- The step of the stopped potential in expectation, with the ledger as the cost. It is `PotStep`
of `SigningFlatEager` with `stopRisk` and the ledger. -/
def LedgerStep (x : SigningSecurityProof.Keys3 C) {α : Type}
    (m : StateT (LedgerState C) ProbComp α) : Prop :=
  ∀ p : LedgerState C, CacheSeen p.1.1.1.1.1.1 p.1.1.1.2 →
    (∀ z ∈ support (m.run p), CacheSeen z.2.1.1.1.1.1.1 z.2.1.1.1.2 ∧ p.1.2 ≤ z.2.1.2) ∧
    ∑' z, Pr[= z | m.run p] * SigningOwnR1.stopRisk x z.2.1.1.1.1.1.1 z.2.1.1.1.2 ≤
      SigningOwnR1.stopRisk x p.1.1.1.1.1.1 p.1.1.1.2 + (2 ^ 128 : ℝ≥0∞)⁻¹ *
        ∑' z, Pr[= z | m.run p] * ((z.2.1.2 - p.1.2 : ℕ) : ℝ≥0∞)

theorem ledgerStep_pure (x : SigningSecurityProof.Keys3 C) {α : Type} (a : α) :
    LedgerStep x (pure a : StateT (LedgerState C) ProbComp α) := by
  intro p hp
  refine ⟨fun z hz => ?_, ?_⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hp, le_rfl⟩
  · simp only [StateT.run_pure, tsum_probOutput_pure_mul]
    exact le_self_add

theorem ledgerStep_bind (x : SigningSecurityProof.Keys3 C) {α β : Type}
    {m : StateT (LedgerState C) ProbComp α} {k : α → StateT (LedgerState C) ProbComp β}
    (hm : LedgerStep x m) (hk : ∀ a, LedgerStep x (k a)) : LedgerStep x (m >>= k) := by
  intro p hp
  obtain ⟨hms, hmr⟩ := hm p hp
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨hy1, hy2⟩ := hms y hy
    obtain ⟨hz1, hz2⟩ := (hk y.1 y.2 hy1).1 z hz
    exact ⟨hz1, hy2.trans hz2⟩
  · set c : ℝ≥0∞ := (2 ^ 128 : ℝ≥0∞)⁻¹
    set κ := fun q : LedgerState C => q.1.2
    set f := fun q : LedgerState C => SigningOwnR1.stopRisk x q.1.1.1.1.1.1 q.1.1.1.2
    simp only [StateT.run_bind, tsum_probOutput_bind_mul]
    calc _ ≤ ∑' y, Pr[= y | m.run p] * (f y.2 + c * ∑' z, Pr[= z | (k y.1).run y.2] *
            ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞)) :=
          tsum_le_of_support _ _ _ fun y hy => (hk y.1 y.2 (hms y hy).1).2
      _ = ∑' y, Pr[= y | m.run p] * f y.2 + c * ∑' y, Pr[= y | m.run p] *
            ∑' z, Pr[= z | (k y.1).run y.2] * ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞) := by
          simp only [mul_add, ENNReal.tsum_add]
          congr 1
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun y => by ring
      _ ≤ f p + c * ∑' y, Pr[= y | m.run p] * ((κ y.2 - κ p : ℕ) : ℝ≥0∞) + c * ∑' y, Pr[= y | m.run p] *
            ∑' z, Pr[= z | (k y.1).run y.2] * ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞) := by
          gcongr
      _ = f p + c * ∑' y, Pr[= y | m.run p] * (((κ y.2 - κ p : ℕ) : ℝ≥0∞) +
            ∑' z, Pr[= z | (k y.1).run y.2] * ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞)) := by
          rw [add_assoc, ← mul_add, ← ENNReal.tsum_add]
          simp only [mul_add]
      _ = _ := by
          congr 2
          refine tsum_eq_of_support _ _ _ fun y hy => ?_
          rw [← tsum_probOutput_mul_const_add]
          refine tsum_eq_of_support _ _ _ fun z hz => ?_
          have h1 := (hms y hy).2
          have h2 := ((hk y.1 y.2 (hms y hy).1).1 z hz).2
          rw [← Nat.cast_add]
          congr 1
          change κ y.2 - κ p + (κ z.2 - κ y.2) = κ z.2 - κ p
          change κ p ≤ κ y.2 at h1
          change κ y.2 ≤ κ z.2 at h2
          omega

/-- A run of the trial oracle of the split world does not raise the stopped potential. It
is `monitoredOracle_run_risk_le` with the stop and with the flags. -/
theorem keyedSplitOracle_run_stopRisk_le (x : SigningSecurityProof.Keys3 C)
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {β : Type}
    (ob : OracleComp (Query C →ₒ HashOutput) β)
    (s : (HashCache C × Monitor) × (XmssSecurity.LeafIndex → Bool)) (hcov : CacheSeen s.1.1 s.1.2) :
    ∑' r, Pr[= r | (simulateQ (SigningOneRunProof.keyedSplitOracle keyOf) ob).run s] *
        SigningOwnR1.stopRisk x r.2.1.1 r.2.1.2 ≤ SigningOwnR1.stopRisk x s.1.1 s.1.2 := by
  by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 s.1.1
  · refine (SigningPartnerBoundProof.tsum_probOutput_mul_le_of_const _ _ 0 fun r hr => ?_).trans zero_le
    have hle := SigningReleasedAlignProof.keyed_run_cache_le keyOf ob s r hr
    simp only [SigningOwnR1.stopRisk, if_pos (SigningGuessProof.alternativeCommitment_mono _ _ _ _ hle halt),
      le_refl]
  rw [SigningOwnR1.stopRisk, if_neg halt]
  have hpt : ∀ (cache : HashCache C) (n : Monitor), SigningOwnR1.stopRisk x cache n ≤ n.risk := by
    intro cache n
    unfold SigningOwnR1.stopRisk
    split_ifs
    · exact zero_le
    · exact le_rfl
  refine (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hpt _ _) _).trans ?_
  have h := monitoredOracle_run_risk_le keyOf ob s.1 hcov
  rw [← SigningOneRunProof.keyedSplitOracle_run_forget keyOf ob s.1 s.2, tsum_probOutput_map_mul] at h
  exact h

/-- A run of the trial oracle of the split world keeps each cached input seen by the monitor. -/
theorem keyedSplitOracle_run_cacheSeen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    {β : Type} (ob : OracleComp (Query C →ₒ HashOutput) β)
    (s : (HashCache C × Monitor) × (XmssSecurity.LeafIndex → Bool)) (hcov : CacheSeen s.1.1 s.1.2)
    (v : β × (HashCache C × Monitor) × (XmssSecurity.LeafIndex → Bool))
    (hv : v ∈ support ((simulateQ (SigningOneRunProof.keyedSplitOracle keyOf) ob).run s)) :
    CacheSeen v.2.1.1 v.2.1.2 := by
  have hv' : (v.1, v.2.1) ∈ support ((simulateQ (monitoredOracle keyOf) ob).run s.1) := by
    rw [← SigningOneRunProof.keyedSplitOracle_run_forget keyOf ob s.1 s.2, support_map]
    exact ⟨v, hv, rfl⟩
  exact monitoredOracle_run_cacheSeen keyOf ob s.1 hcov _ hv'

/-- One call of the ledger world pays its rise of the stopped potential with its charge. -/
theorem ledgerStep_world (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain)
    (ht : ¬SigningHitLaneProof.IsProgram t) : LedgerStep x (ledgerWorld prims x t) := by
  intro p hp
  set keyOf := XmssSecurity.encodingInputLeafIndex? x.1
  have hcarry : ∀ y ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1.1, p.2)),
      ∃ l ∈ support ((SigningCostProof.loggedImpl prims t).run p.1.1.1.1), y = (l.1, (l.2, p.2)) := by
    intro y hy
    simp only [carry, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨l, hl, rfl⟩
  have hseen : ∀ w ∈ support ((SigningReleasedLinkProof.world prims x t).run (p.1.1, p.2)),
      CacheSeen w.2.1.1.1.1.1 w.2.1.1.2 := by
    intro w hw
    simp only [SigningReleasedLinkProof.world, SigningOneRunProof.keyedSplitWorld, StateT.run_mk, mem_support_bind_iff,
      support_map, Set.mem_image] at hw
    obtain ⟨y, hy, v, hv, rfl⟩ := hw
    obtain ⟨l, hl, rfl⟩ := hcarry y hy
    exact keyedSplitOracle_run_cacheSeen keyOf _ _
      (logged_query_cacheSeen prims keyOf t p.1.1.1.1 p.1.1.1.2 hp ht l hl) v (by with_reducible exact hv)
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨hw, hledger⟩ := ledgerWorld_support prims x t p z hz
    exact ⟨hseen _ hw, hledger ▸ Nat.le_add_right _ _⟩
  have hcost : ∑' z, Pr[= z | (ledgerWorld prims x t).run p] * ((z.2.1.2 - p.1.2 : ℕ) : ℝ≥0∞) =
      (stopCharge x p.1.1.1.1.1.1 t : ℝ≥0∞) := by
    rw [tsum_eq_of_support _ _ (fun _ => (stopCharge x p.1.1.1.1.1.1 t : ℝ≥0∞) + 0) fun z hz => by
        rw [(ledgerWorld_support prims x t p z hz).2, Nat.add_sub_cancel_left, add_zero],
      tsum_probOutput_mul_const_add]
    simp
  rw [hcost]
  by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 p.1.1.1.1.1.1
  · refine (SigningPartnerBoundProof.tsum_probOutput_mul_le_of_const _ _ 0 fun z hz => ?_).trans zero_le
    have hle := world_cache_le prims x t (p.1.1, p.2) _ (ledgerWorld_support prims x t p z hz).1
    simp only [SigningOwnR1.stopRisk, if_pos (SigningGuessProof.alternativeCommitment_mono _ _ _ _ hle halt),
      le_refl]
  rw [stopCharge, if_neg halt]
  simp only [ledgerWorld, StateT.run_mk, tsum_probOutput_map_mul]
  simp only [SigningReleasedLinkProof.world, SigningOneRunProof.keyedSplitWorld, StateT.run_mk,
    tsum_probOutput_bind_mul,
    tsum_probOutput_map_mul]
  calc _ ≤ ∑' y, Pr[= y | (carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1.1, p.2)] *
          SigningOwnR1.stopRisk x y.2.1.1.1 (queryEntryStep keyOf p.1.1.1.2 (hashEntry ⟨t, y.1⟩)) := by
        refine tsum_le_of_support _ _ _ fun y hy => ?_
        obtain ⟨l, hl, rfl⟩ := hcarry y hy
        exact keyedSplitOracle_run_stopRisk_le x keyOf _ _
          (logged_query_cacheSeen prims keyOf t p.1.1.1.1 p.1.1.1.2 hp ht l hl)
    _ ≤ _ := by
        simp only [carry, StateT.run_mk, tsum_probOutput_map_mul]
        exact SigningOwnR1.logged_query_stopRisk_le prims x keyOf t p.1.1.1.1 p.1.1.1.2 hp ht

theorem ledgerStep_simulateQ_world (x : SigningSecurityProof.Keys3 C) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (h : SigningHitProof.ProgramFree oa) :
    LedgerStep x (simulateQ (ledgerWorld prims x) oa) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => exact ledgerStep_pure x a
  | query_bind t k ih =>
    have hb := (isQueryBoundP_query_bind_iff SigningHitLaneProof.IsProgram t k 0).mp h
    have ht : ¬SigningHitLaneProof.IsProgram t := by simpa using hb.1
    have hk : ∀ u, SigningHitProof.ProgramFree (k u) := by
      simpa [SigningHitProof.ProgramFree, ht] using hb.2
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact ledgerStep_bind x (ledgerStep_world prims x t ht) fun u => ih u (hk u)

theorem ledgerStep_simulateQ (x : SigningSecurityProof.Keys3 C) {ι : Type} {spec : OracleSpec ι}
    (V : QueryImpl spec (StateT (LedgerState C) ProbComp)) (hV : ∀ t, LedgerStep x (V t)) {α : Type}
    (oa : OracleComp spec α) : LedgerStep x (simulateQ V oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ledgerStep_pure x a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact ledgerStep_bind x (hV t) ih

theorem ledgerStep_flatWith (x : SigningSecurityProof.Keys3 C) {ι : Type} {spec : OracleSpec ι}
    (outer : QueryImpl spec (StateT (OpeningState C) (OracleComp (WorldSpec C))))
    (hfree : ∀ t s, SigningHitProof.ProgramFree ((outer t).run s)) (t : spec.Domain) :
    LedgerStep x (flatWith outer (ledgerWorld prims x) t) := by
  intro p hp
  obtain ⟨hs, hr⟩ := ledgerStep_simulateQ_world prims x _ (hfree t p.2) p hp
  simp only [flatWith, StateT.run_mk, support_map, Set.mem_image, tsum_probOutput_map_mul]
  refine ⟨?_, hr⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hs z hz

theorem ledgerStep_getCarried (x : SigningSecurityProof.Keys3 C) :
    LedgerStep (C := C) x (getCarried (σ := OpeningState C)) := by
  intro p hp
  exact ledgerStep_pure (C := C) x p.2 p hp

/-- The ledger game pays each rise of the stopped potential with the ledger. -/
theorem ledgerStep_game (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    LedgerStep x (ledgerGame prims A x) := by
  unfold ledgerGame jointGameWith
  dsimp only
  have hsetup : SigningHitProof.ProgramFree (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  refine ledgerStep_bind x (ledgerStep_simulateQ_world prims x _ hsetup) fun r => ?_
  rcases r with _ | (top | tree)
  · exact ledgerStep_pure x _
  · refine ledgerStep_bind x (ledgerStep_simulateQ x _
      (fun t => ledgerStep_flatWith prims x _ (programFree_openingOracles x top) t) _) fun a => ?_
    refine ledgerStep_bind x (ledgerStep_getCarried x) fun s => ?_
    refine ledgerStep_bind x (ledgerStep_simulateQ_world prims x _
      (programFree_tsigFinishLogged x top s.2.1 _)) fun w => ?_
    exact ledgerStep_pure x _
  · exact ledgerStep_pure x _

/-- The stopped potential at the end of the ledger run costs `2^-128` for each unit of the
ledger. -/
theorem ledgerRun_stopRisk_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr[= z | ledgerRun prims A x] * SigningOwnR1.stopRisk x z.2.1.1.1.1.1.1 z.2.1.1.1.2 ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' z, Pr[= z | ledgerRun prims A x] * (z.2.1.2 : ℝ≥0∞) := by
  have hinit : CacheSeen (ledgerInit (C := C)).1.1.1.1.1.1 (ledgerInit (C := C)).1.1.1.2 :=
    fun input h => (h rfl).elim
  have h := (ledgerStep_game prims A x ledgerInit hinit).2
  have hrisk : SigningOwnR1.stopRisk x (ledgerInit (C := C)).1.1.1.1.1.1 (ledgerInit (C := C)).1.1.1.2 = 0 := by
    unfold SigningOwnR1.stopRisk
    split_ifs
    · rfl
    · simp [ledgerInit, SigningOneRunProof.monitoredInit, Monitor.risk, Monitor.empty,
        XmssSecurity.CappedEncodingMonitor.State.pendingRisk_empty]
  have hledger : (ledgerInit (C := C)).1.2 = 0 := rfl
  rw [hrisk, zero_add, hledger] at h
  simp only [Nat.sub_zero] at h
  exact h

end SigningOwnStop

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.logCost_logQuery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.logCost_logQuery

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_forgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_forgets

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerGame_forgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerGame_forgets

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerRun_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerRun_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_support

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.keyedSplitOracle_run_stopRisk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.keyedSplitOracle_run_stopRisk_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.keyedSplitOracle_run_cacheSeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.keyedSplitOracle_run_cacheSeen

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_world

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_simulateQ_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_simulateQ_world

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_simulateQ

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_flatWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_flatWith

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_getCarried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_getCarried

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerStep_game

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerRun_stopRisk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerRun_stopRisk_le
