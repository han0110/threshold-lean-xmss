import ThresholdLeanXmssSecurity.Proof.SigningOwnHit
import ThresholdLeanXmssSecurity.Proof.SigningOwnGateBlock

/-!
# The hit bound for a forger with an own budget

- `HitOwn` bounds a win with a hit by the own structural calls of the forger, `2 ^ 16` units for the
  top gates and `382` units for the verification.
- `hitInv_dealer` and `hitInv_step` show that `HitInv` holds after the dealer and after each query
  of the forger.
- `hitOwn_of_gate` gives `HitOwn` from the gate bound of a top key. It applies `flat_potential_le`
  to the structural hit potential with the rises `hit_dealer_rise`, `hit_step_rise` and
  `hit_finish_rise`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnHitBound

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitLaneProof SigningCostProof SigningFlatProof SigningOwnForger SigningOwnHit
open SigningOwnGateBlock

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The hit bound with the own budget. `2 ^ 16` units pay the first read of each top gate, and `382`
units pay the structural calls of the verification. -/
def HitOwn : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C), x ∈ support (keyGen3 (C := C)) →
    ¬KeyCollision x.2.1 x.2.2 → HasSigningOwnBound A q → q + signingSlack < 2 ^ 127 →
    Pr[WinHit prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (forgerCost prims A x (ownDomainUnit (SigningHitProof.forestRelevant x.1)) +
        (2 ^ 16 + 382 : ℕ))

/-- A logged run keeps the raw reachability of a state without a programming query. -/
theorem reachable_run {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C)
    (hs : ¬Programmed s.2 → SigningHitProof.RawReachable prims s) :
    ∀ r ∈ support ((simulateQ (loggedImpl prims) oa).run s),
      ¬Programmed r.2.2 → SigningHitProof.RawReachable prims r.2 :=
  SeedHitProof.support_simulateQ_inv _
    (fun s : LoggedState C => ¬Programmed s.2 → SigningHitProof.RawReachable prims s)
    (fun t s hs r hr hn => by
      have hn' : ¬Programmed s.2 ∧ ¬IsProgram t := by
        rw [loggedImpl_log prims t s r hr, programmed_logQuery, not_or] at hn
        exact hn
      exact .step t s (hs hn'.1) hn'.2 r hr) oa s hs

/-- A logged run keeps `HitInv`. -/
theorem hitInv_run (x : Keys3 C) (T : C.Term) (top : TopTree) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : LoggedState C) (hs : HitInv prims x T top s) :
    ∀ r ∈ support ((simulateQ (loggedImpl prims) oa).run s), HitInv prims x T top r.2 := by
  intro r hr
  have h := runInv_run prims x T top oa s ⟨hs.2.1, hs.2.2⟩ r hr
  exact ⟨reachable_run prims oa s hs.1 r hr, h.1, h.2⟩

/-- One query of the forger keeps `HitInv`. -/
theorem hitInv_step (x : Keys3 C) (T : C.Term) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C) (hp : HitInv prims x T top p.1) :
    ∀ r ∈ support ((flatOracles prims x (SigningHitProof.actualDealt x top) t).run p),
      HitInv prims x T top r.2.1 := by
  intro r hr
  rw [flatOracles, flat, StateT.run_mk, support_map, carry_run_pair, support_map] at hr
  obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hr
  exact hitInv_run prims x T top _ p.1 hp w hw

set_option maxRecDepth 100000 in
/-- The dealer asks each top gate. -/
theorem dealer_gate (x : Keys3 C) (T : C.Term) (b : XmssSecurity.TopIndex) :
    SigningHitProof.EnsuresGate prims (.inr (.inr (.inl (SigningHitProof.topGateInput x T b))))
      (referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
        x.1 emptyTop .top) := by
  unfold referenceTree ceremonyOutput
  apply SigningHitProof.ensuresGate_bind_left prims
  apply SigningHitProof.ensuresGate_map prims
  let job : Job := ⟨.chainEnd (topKey b) ⟨0, by decide⟩,
    [.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0)]⟩
  apply SigningHitProof.ensuresGate_mapM prims _ _ job
  · unfold referenceJob
    apply SigningHitProof.ensuresGate_bind_left prims
    apply SigningHitProof.ensuresGate_mapM prims _ _ (.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0))
    · exact SigningHitProof.ensuresGate_prfValue prims _ _ T
    · simp [job]
  · simp only [topJobs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨b, ⟨0, by decide⟩, rfl⟩

set_option maxRecDepth 100000 in
/-- `HitInv` holds after the dealer. -/
theorem hitInv_dealer (x : Keys3 C) (T : C.Term) :
    ∀ r ∈ support (dealerRun prims x), ∀ top, r.1 = some (.top top) → HitInv prims x T top r.2.1 := by
  intro r hr top htop
  rw [dealerRun, flatWorld, carry_run, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  refine ⟨reachable_run prims _ loggedInit (fun _ => .initial) z hz,
    fun b => dealer_gate prims x T b loggedInit z hz, ?_⟩
  have hprog : referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
      x.1 emptyTop .top = liftFree (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
        (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top)) := by
    rw [show referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
        x.1 emptyTop .top = liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _, ← SigningHitProof.hashEmbed_referenceTree]
  rw [hprog] at hz
  have hres := logged_hashEmbed_resolves prims _ loggedInit z hz
  rw [show z.1 = some (.top top) from htop] at hres
  exact hres

set_option maxRecDepth 100000 in
/-- The hit bound with the own budget, from the gate bound, the frame `flat_potential_le` and
the three rises `hit_dealer_rise`, `hit_step_rise` and `hit_finish_rise`. -/
theorem hitOwn_of_gate (hgate : KeyGateBoundOwn prims C) : HitOwn prims (C := C) := by
  intro A q x hx hno hown hsmall
  obtain ⟨T, hT⟩ := hgate A q x hx hno hown hsmall
  have hf := flat_potential_le prims A x (guarded (SigningGuessProof.structuralHitPotential prims A x T))
    (HitInv prims x T) (ownDomainUnit (SigningHitProof.forestRelevant x.1)) (2 ^ 16) 382
    (hit_dealer_rise prims A x T hT) (hitInv_dealer prims x T)
    (fun top t p hp => hit_step_rise prims A x T top t p hp)
    (fun top t p hp => hitInv_step prims x T top t p hp)
    (fun top forgery st s hs => hit_finish_rise prims A x T top forgery st s hs)
  refine le_trans ?_ hf
  rw [SigningHitLaneProof.winHit_logged, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support (loggedRun prims A x)
  · by_cases hw : WinHit prims x (z.1, z.2.1)
    · simp only [hw, if_true, guarded, if_neg (noProgramQuery prims C A x z hz)]
      simpa only [mul_one] using mul_le_mul_right
        (SigningGuessProof.structuralHitPotential_terminal prims A x T z hz hw) (Pr[= z | loggedRun prims A x])
    · simp [hw]
  · simp [probOutput_eq_zero_of_not_mem_support hz]

end ThresholdLeanXmssSecurity.SigningOwnHitBound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHitBound.reachable_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHitBound.reachable_run

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHitBound.hitInv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHitBound.hitInv_run

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHitBound.hitInv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHitBound.hitInv_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHitBound.dealer_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHitBound.dealer_gate

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHitBound.hitInv_dealer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHitBound.hitInv_dealer

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHitBound.hitOwn_of_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHitBound.hitOwn_of_gate
