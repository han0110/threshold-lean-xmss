import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SeedHit

/-!
# The cost of the forger with the own budget

- `HasSigningOwnBound A q` (`ThresholdLeanXmss/Statement.lean`) states that the forger makes at most
  `q` own calls of `H` or `PRG` and round-2 requests on each path.
- `forgerCost prims A x c` is the expected cost of the queries of the forger on the flat run, for a
  cost `c` of each query. The honest work of a handler costs nothing.
- `forgerCost_le` bounds it by `q` when `c` is at most `ownUnit`. `forgerCost_add` shows that it is
  additive in the cost.
- `units_le` shows that the four domains of the charged lane share one unit of a query.
- `flat_potential_le` is the frame of one potential on the logged run. The dealer, each query of the
  forger and the finish have one rise each.
- `ownKeyed_source_le_forgerCost` shows that the own bottom digest calls of the source run are
  queries of the forger. The dealer, the signing oracles and the finish call the free copy only.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnForger

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitLaneProof SigningCostProof SigningFlatProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The unit of one query of the forger, one for each own call of `H` or `PRG` and for each round-2
request. -/
def ownUnit : (LocalSpec C + TsigSpec C).Domain → ℕ
  | .inl (.inr _) => 1
  | .inr (.round2 ..) => 1
  | _ => 0

/-- The unit of an own call of the forger in one domain of `H`, as `rawDomainCost` on the counted
copy. -/
def ownDomainUnit (relevant : Query C → Prop) : (LocalSpec C + TsigSpec C).Domain → ℕ
  | .inl (.inr (.inl input)) => if relevant input then 1 else 0
  | .inl (.inr (.inr input)) => if relevant (.streamKey input.2.1) then 1 else 0
  | _ => 0

/-- The unit of a round-2 request. -/
def round2Unit : (LocalSpec C + TsigSpec C).Domain → ℕ
  | .inr (.round2 ..) => 1
  | _ => 0

/-- A bottom digest input, the domain of the R1 monitor. -/
def BottomDigestInput (x : Keys3 C) : Query C → Prop
  | .hash input => (XmssSecurity.encodingInputLeafIndex? x.1 input).isSome
  | _ => False

/-- The run of the dealer in the flat run. -/
def dealerRun (x : Keys3 C) : ProbComp (Option TreeOutput × FlatState C) :=
  (simulateQ (flatWorld prims) (referenceTree (fun oa => liftFree (tweakable oa))
    (fun p => liftFree (prfValue x.2.1 p)) x.1 emptyTop .top)).run
      (loggedInit, (tsigInit, false))

/-- The expected cost of the forger in the flat run, for a cost `c` of each of its queries. The
honest calls of the oracles cost nothing here. -/
def forgerCost (A : TsigAdversary C) (x : Keys3 C) (c : (LocalSpec C + TsigSpec C).Domain → ℕ) :
    ℝ≥0∞ :=
  ∑' r, Pr[= r | dealerRun prims x] * match r.1 with
    | some (.top top) => XmssSecurity.expectedSimulatedCost
        (flatOracles prims x (SigningHitProof.actualDealt x top)) (fun t _ => (c t : ℝ≥0∞))
        (A ⟨top.root, x.1⟩ top) r.2
    | _ => 0

/-- The own budget bounds the expected cost of the forger. -/
theorem forgerCost_le (A : TsigAdversary C) (q : ℕ) (x : Keys3 C)
    (c : (LocalSpec C + TsigSpec C).Domain → ℕ) (hown : HasSigningOwnBound A q)
    (hc : ∀ t, c t ≤ ownUnit t) : forgerCost prims A x c ≤ q := by
  unfold forgerCost
  refine SigningPartnerBoundProof.tsum_probOutput_mul_le_of_const _ _ _ fun r _ => ?_
  obtain ⟨o, p⟩ := r
  rcases o with _ | (top | tree)
  · simp
  · dsimp only
    refine le_trans (XmssSecurity.expectedSimulatedCost_mono _
      (right := fun t _ => if SigningOwnCounted t then 1 else 0) (fun t _ => ?_) _ _) ?_
    · have h : c t ≤ if SigningOwnCounted t then 1 else 0 := by
        refine (hc t).trans ?_
        rcases t with (n | t) | (i | b | ⟨i, J, e, m⟩ | ⟨i, J, e, m, parts⟩) <;>
          simp [ownUnit, SigningOwnCounted]
      have h' := (Nat.cast_le (α := ℝ≥0∞)).2 h
      simpa [Nat.cast_ite] using h'
    · rw [XmssSecurity.expectedSimulatedCost_indicator]
      exact XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ _ _ q
        (hown ⟨top.root, x.1⟩ top)
  · simp

/-- The expected cost of the forger is additive in the cost. -/
theorem forgerCost_add (A : TsigAdversary C) (x : Keys3 C)
    (c d : (LocalSpec C + TsigSpec C).Domain → ℕ) :
    forgerCost prims A x (fun t => c t + d t) = forgerCost prims A x c + forgerCost prims A x d := by
  unfold forgerCost
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun r => ?_
  rw [← mul_add]
  congr 1
  obtain ⟨o, p⟩ := r
  rcases o with _ | (top | tree)
  · simp
  · dsimp only
    simp only [Nat.cast_add]
    exact XmssSecurity.expectedSimulatedCost_add _ _ _ _ _
  · simp

/-- The four domains of the charged lane are disjoint, so one query of the forger pays in at most
one of them. -/
theorem units_le (x : Keys3 C) (t : (LocalSpec C + TsigSpec C).Domain) :
    ownDomainUnit (SigningHitProof.forestRelevant x.1) t +
      (ownDomainUnit (SigningGuessProof.RawCommitmentInput x.1) t + round2Unit t) +
      ownDomainUnit (SigningGuessProof.anyTopDigestInput x.1) t +
      ownDomainUnit (BottomDigestInput x) t ≤ ownUnit t := by
  obtain ⟨T, -, -⟩ := SigningHitProof.terms_cons C
  have hworld : ∀ (t' : (WorldSpec C).Domain), SeedHitProof.signCost t' ≤ 1 →
      SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t' +
        (SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1) t' + 0) +
        SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t' +
        SigningPartnerBoundProof.keyedCost (XmssSecurity.encodingInputLeafIndex? x.1) t' ≤ 1 := by
    intro t' hsign
    have h1 := SigningGuessProof.structural_commitment_digest_cost_le x T t'
    have h2 := SigningGuessProof.commitment_rawCost_le x.1 t'
    have h3 := SigningPartnerLinkProof.topDigest_add_bottomDigestCost x t'
    have h4 := SigningPartnerBoundProof.keyedCost_le_bottomDigestCost x t'
    have h5 : SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t' ≤
        SigningGuessProof.structuralHitCost x T t' := Nat.le_add_right _ _
    omega
  rcases t with (n | (input | input)) | (i | b | ⟨i, J, e, m⟩ | ⟨i, J, e, m, parts⟩)
  · simp [ownDomainUnit, round2Unit, ownUnit]
  · have h := hworld (.inl (.inl (.inr (.inl input)))) le_rfl
    have hk : ownDomainUnit (BottomDigestInput x) (.inl (.inr (.inl input))) =
        SigningPartnerBoundProof.keyedCost (C := C) (XmssSecurity.encodingInputLeafIndex? x.1)
          (.inl (.inl (.inr (.inl input)))) := by
      cases input <;> simp [ownDomainUnit, BottomDigestInput, SigningPartnerBoundProof.keyedCost]
    rw [hk]
    exact h
  · have h := hworld (.inl (.inl (.inr (.inr input)))) le_rfl
    have hk : ownDomainUnit (BottomDigestInput x) (.inl (.inr (.inr input))) =
        SigningPartnerBoundProof.keyedCost (C := C) (XmssSecurity.encodingInputLeafIndex? x.1)
          (.inl (.inl (.inr (.inr input)))) := by
      simp [ownDomainUnit, BottomDigestInput, SigningPartnerBoundProof.keyedCost]
    rw [hk]
    exact h
  · simp [ownDomainUnit, round2Unit, ownUnit]
  · simp [ownDomainUnit, round2Unit, ownUnit]
  · simp [ownDomainUnit, round2Unit, ownUnit]
  · simp [ownDomainUnit, round2Unit, ownUnit]

set_option maxRecDepth 100000 in
/-- The frame of one potential on the logged run. The dealer, each query of the forger and the
finish have one rise each. The honest work of a handler is inside its rise. The invariant reads the
top tree of the dealer. -/
theorem flat_potential_le (A : TsigAdversary C) (x : Keys3 C) (f : LoggedState C → ℝ≥0∞)
    (Inv : TopTree → LoggedState C → Prop) (c : (LocalSpec C + TsigSpec C).Domain → ℕ)
    (dealer finish : ℕ)
    (hdealer : ∑' r, Pr[= r | dealerRun prims x] * f r.2.1 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * dealer)
    (hdealerInv : ∀ r ∈ support (dealerRun prims x), ∀ top, r.1 = some (.top top) → Inv top r.2.1)
    (hstep : ∀ (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C), Inv top p.1 →
      ∑' r, Pr[= r | (flatOracles prims x (SigningHitProof.actualDealt x top) t).run p] * f r.2.1 ≤
        f p.1 + (2 ^ 128 : ℝ≥0∞)⁻¹ * c t)
    (hstepInv : ∀ (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C),
      Inv top p.1 →
      ∀ r ∈ support ((flatOracles prims x (SigningHitProof.actualDealt x top) t).run p), Inv top r.2.1)
    (hfinish : ∀ (top : TopTree) (forgery : Forgery) (st : TsigState C) (s : LoggedState C),
      Inv top s →
      ∑' r, Pr[= r | (simulateQ (loggedImpl prims)
          (tsigFinish (SigningHitProof.actualDealt x top) (forgery, st))).run s] * f r.2 ≤
        f s + (2 ^ 128 : ℝ≥0∞)⁻¹ * finish) :
    ∑' z, Pr[= z | loggedRun prims A x] * f z.2 ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (forgerCost prims A x c + (dealer + finish : ℕ)) := by
  set ε := (2 ^ 128 : ℝ≥0∞)⁻¹
  rw [← flatRun_logged prims A x, tsum_probOutput_map_mul]
  unfold flatRun
  rw [tsum_probOutput_bind_mul]
  change ∑' r, Pr[= r | dealerRun prims x] * _ ≤ _
  calc
    _ ≤ ∑' r, Pr[= r | dealerRun prims x] * (f r.2.1 + ε * (match r.1 with
          | some (.top top) => XmssSecurity.expectedSimulatedCost
              (flatOracles prims x (SigningHitProof.actualDealt x top)) (fun t _ => (c t : ℝ≥0∞))
              (A ⟨top.root, x.1⟩ top) r.2
          | _ => 0) + ε * finish) := by
      refine ENNReal.tsum_le_tsum fun r => ?_
      by_cases hr : r ∈ support (dealerRun prims x)
      swap
      · simp [probOutput_eq_zero_of_not_mem_support hr]
      gcongr
      rcases r with ⟨_ | (top | tree), p⟩
      · dsimp only
        rw [tsum_probOutput_pure_mul]
        exact le_add_right (le_add_right le_rfl)
      · dsimp only
        let impl := flatOracles prims x (SigningHitProof.actualDealt x top)
        let run := (simulateQ impl (A ⟨top.root, x.1⟩ top)).run p
        have hp : Inv top p.1 := hdealerInv _ hr top rfl
        have hinv : ∀ z ∈ support run, Inv top z.2.1 :=
          SeedHitProof.support_simulateQ_inv impl (fun q => Inv top q.1) (fun t q hq => hstepInv top t q hq) _ p hp
        have hfinal := XmssSecurity.expectedFinal_le impl (Inv := fun q => Inv top q.1)
          (fun t q hq => hstepInv top t q hq) (fun q => f q.1) (fun t _ => ε * (c t : ℝ≥0∞))
          (fun t q hq => hstep top t q hq) (A ⟨top.root, x.1⟩ top) p hp
        rw [XmssSecurity.expectedSimulatedCost_const_mul] at hfinal
        rw [tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
        change ∑' z, Pr[= z | run] * _ ≤ (f p.1 + ε * XmssSecurity.expectedSimulatedCost impl
          (fun t _ => (c t : ℝ≥0∞)) (A ⟨top.root, x.1⟩ top) p) + ε * finish
        calc
          _ ≤ ∑' z, Pr[= z | run] * (f z.2.1 + ε * finish) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hz : z ∈ support run
            swap
            · simp [probOutput_eq_zero_of_not_mem_support hz]
            gcongr
            rw [tsum_probOutput_bind_mul]
            simp only [tsum_probOutput_pure_mul]
            rw [flatWorld, carry_run, tsum_probOutput_map_mul]
            exact hfinish top z.1 z.2.2.1 z.2.1 (hinv z hz)
          _ = XmssSecurity.expectedFinal impl (fun q => f q.1) (A ⟨top.root, x.1⟩ top) p +
              (∑' z, Pr[= z | run]) * (ε * finish) := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
            rfl
          _ ≤ _ := add_le_add hfinal (mul_le_of_le_one_left' tsum_probOutput_le_one)
      · dsimp only
        rw [tsum_probOutput_pure_mul]
        exact le_add_right (le_add_right le_rfl)
    _ = (∑' r, Pr[= r | dealerRun prims x] * f r.2.1) + ε * forgerCost prims A x c +
          (∑' r, Pr[= r | dealerRun prims x]) * (ε * finish) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, forgerCost,
        ← ENNReal.tsum_mul_left]
      congr 2
      refine tsum_congr fun r => ?_
      ring
    _ ≤ ε * dealer + ε * forgerCost prims A x c + 1 * (ε * finish) :=
      add_le_add (add_le_add hdealer le_rfl) (mul_le_mul_left tsum_probOutput_le_one _)
    _ = _ := by
      push_cast
      ring

/-- The unit of an own bottom digest call of the forger in the world, the keyed calls of the R1
monitor on the counted copy. -/
def ownKeyedCost (x : Keys3 C) : (WorldSpec C).Domain → ℕ
  | .inl (.inl (.inr (.inl (.hash input)))) =>
      if (XmssSecurity.encodingInputLeafIndex? x.1 input).isSome then 1 else 0
  | _ => 0

/-- A run through a handler with no own bottom digest call makes no such call. -/
theorem keyedFree_simulate {ι α : Type} {spec : OracleSpec ι} (x : Keys3 C)
    (impl : QueryImpl spec (OracleComp (WorldSpec C)))
    (h : ∀ t, (impl t).IsQueryBoundP (fun t => ownKeyedCost x t = 1) 0) (oa : OracleComp spec α) :
    (simulateQ impl oa).IsQueryBoundP (fun t => ownKeyedCost x t = 1) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact isQueryBoundP_bind (n := 0) (m := 0) (h t) fun a _ => ih a

/-- A run of the free copy makes no own bottom digest call. -/
theorem keyedFree_free {α : Type} (x : Keys3 C) (oa : OracleComp (LocalSpec C) α) :
    (free oa).IsQueryBoundP (fun t => ownKeyedCost x t = 1) 0 := by
  refine keyedFree_simulate x _ (fun t => ?_) oa
  change (liftM (OracleSpec.query (spec := WorldSpec C) (.inr t)) : OracleComp (WorldSpec C) _).IsQueryBoundP
    (fun t => ownKeyedCost x t = 1) 0
  exact (isQueryBoundP_query_iff _ _ _).mpr fun h => by simp [ownKeyedCost] at h

set_option maxRecDepth 100000 in
/-- The finish makes no own bottom digest call. -/
theorem keyedFree_finish (x : Keys3 C) (top : TopTree) (r : Forgery × TsigState C) :
    (tsigFinish (SigningHitProof.actualDealt x top) r).IsQueryBoundP
      (fun t => ownKeyedCost x t = 1) 0 := by
  rcases r with ⟨forgery, st⟩
  unfold SigningCoreProof.tsigFinish
  refine isQueryBoundP_bind (p := fun t => ownKeyedCost x t = 1) (n := 0) (m := 0)
    (keyedFree_free x _) fun verified _ => ?_
  dsimp only
  split_ifs
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (p := fun t => ownKeyedCost x t = 1) (n := 0) (m := 0) ?_
      fun _ _ => by simp only [pure_bind]; exact isQueryBoundP_pure _ _ _
    erw [SigningCacheProof.liftFree_honestSignature]
    exact keyedFree_free x _

set_option maxRecDepth 100000 in
/-- One query of the forger makes at most one own bottom digest call, and only when the query is an
own call of `H` on a bottom digest input. -/
theorem keyed_flaggedOracles (x : Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TsigState C × Bool) :
    ((flaggedOracles x (SigningHitProof.actualDealt x top) t).run s).IsQueryBoundP
      (fun t => ownKeyedCost x t = 1) (ownDomainUnit (BottomDigestInput x) t) := by
  cases t with
  | inl t =>
    simp only [flaggedOracles, StateT.run_mk, isQueryBoundP_map_iff]
    erw [adversary_query, isQueryBoundP_query_iff]
    rcases t with n | ((input | input) | input) <;>
      simp +contextual [ownKeyedCost, ownDomainUnit, BottomDigestInput, Option.isSome_iff_ne_none]
  | inr q =>
    simp only [flaggedOracles, StateT.run_mk, isQueryBoundP_map_iff]
    rw [SigningHitProof.tsigOracles_free]
    exact (keyedFree_free x _).mono (Nat.zero_le _)

/-- The expected count of the calls of `inner` in a layered run is at most the expected cost on the
flat run, when each call of `outer` costs at most `cost`. -/
theorem queryCount_layered_le {ι ι' α σ τ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (outer : QueryImpl spec (StateT σ (OracleComp spec'))) (inner : QueryImpl spec' (StateT τ ProbComp))
    (predicate : spec'.Domain → Prop) [DecidablePred predicate] (cost : spec.Domain → ℕ)
    (h : ∀ t s u, XmssSecurity.expectedSimulatedQueryCount inner predicate ((outer t).run s) u ≤ cost t)
    (oa : OracleComp spec α) (s : σ) (u : τ) :
    XmssSecurity.expectedSimulatedQueryCount inner predicate ((simulateQ outer oa).run s) u ≤
      XmssSecurity.expectedSimulatedCost (flat outer inner) (fun t _ => (cost t : ℝ≥0∞)) oa (u, s) := by
  induction oa using OracleComp.inductionOn generalizing s u with
  | pure a => simp
  | query_bind t k ih =>
    rw [XmssSecurity.expectedSimulatedCost_query_bind]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [XmssSecurity.expectedSimulatedQueryCount_bind]
    refine add_le_add (h t s u) ?_
    rw [flat, StateT.run_mk, tsum_probOutput_map_mul, carry_run, tsum_probOutput_map_mul]
    refine ENNReal.tsum_le_tsum fun z => ?_
    gcongr
    exact ih z.1.1 z.1.2 z.2

set_option maxRecDepth 100000 in
/-- The own bottom digest calls of the source run are queries of the forger. The dealer, the
signing oracles and the finish call the free copy only. -/
theorem ownKeyed_source_le_forgerCost (A : TsigAdversary C) (x : Keys3 C) :
    SigningGuessProof.sourceExpectedCost prims A x (ownKeyedCost x) ≤
      forgerCost prims A x (ownDomainUnit (BottomDigestInput x)) := by
  have hind : (fun t (_ : LoggedState C) => (ownKeyedCost x t : ℝ≥0∞)) =
      fun t _ => if ownKeyedCost x t = 1 then 1 else 0 := by
    funext t _
    have h : ownKeyedCost x t = 0 ∨ ownKeyedCost x t = 1 := by
      unfold ownKeyedCost
      split <;> (try split_ifs) <;> simp
    rcases h with h | h <;> simp [h]
  unfold SigningGuessProof.sourceExpectedCost forgerCost SigningDescentProof.finalRun
  rw [hind, XmssSecurity.expectedSimulatedCost_indicator, XmssSecurity.expectedSimulatedQueryCount_bind]
  have hhead := XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP (loggedImpl prims)
    (fun t => ownKeyedCost x t = 1) (referenceTree (fun oa => liftFree (tweakable oa))
      (fun p => liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) loggedInit 0 (by
        rw [show referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
            x.1 emptyTop .top = liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
          referenceTree_φ _ _ _ _]
        exact keyedFree_free x _)
  rw [Nat.cast_zero, nonpos_iff_eq_zero] at hhead
  rw [hhead, zero_add, dealerRun, flatWorld, carry_run, tsum_probOutput_map_mul]
  refine ENNReal.tsum_le_tsum fun r => ?_
  gcongr
  rcases r with ⟨_ | (top | tree), l⟩
  · simp
  · dsimp only
    rw [XmssSecurity.expectedSimulatedQueryCount_bind]
    rw [ENNReal.tsum_eq_zero.mpr fun z => ?_, add_zero]
    · exact queryCount_layered_le _ _ _ _ (fun t s u =>
        XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ _ _ _
          (keyed_flaggedOracles x top t s)) _ _ _
    · refine mul_eq_zero_of_right _ (nonpos_iff_eq_zero.mp ?_)
      exact (XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ _ _ 0
        ((isQueryBoundP_map_iff _ _ _).mpr (keyedFree_finish x top _))).trans (by simp)
  · simp

end ThresholdLeanXmssSecurity.SigningOwnForger

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.forgerCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.forgerCost_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.forgerCost_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.forgerCost_add

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.units_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.units_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.flat_potential_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.flat_potential_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.keyedFree_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.keyedFree_simulate

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.keyedFree_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.keyedFree_free

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.keyedFree_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.keyedFree_finish

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.keyed_flaggedOracles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.keyed_flaggedOracles

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.queryCount_layered_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.queryCount_layered_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnForger.ownKeyed_source_le_forgerCost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnForger.ownKeyed_source_le_forgerCost
