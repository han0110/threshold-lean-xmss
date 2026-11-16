import ThresholdLeanXmssSecurity.Proof.SigningOwnForger
import ThresholdLeanXmssSecurity.Proof.SigningOwnPotential
import ThresholdLeanXmssSecurity.Proof.SigningOwnCover
import ThresholdLeanXmssSecurity.Proof.SigningOwnVerify

/-!
# The rise of the structural hit potential for a forger with an own budget

The structural hit potential rises by one unit for each top gate over the dealer, by the own
structural call of one query of the forger, and by the `382` structural calls of the verification
over the finish. The honest builds are blocks that the forest completion covers, and the other
honest calls are outside the structural domain or on cached inputs.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnHit

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitLaneProof SigningCostProof SigningFlatProof SigningOwnForger

variable {C : Committee} (prims : Primitives)
attribute [local irreducible] MonadAttach.support

section Gate

open SigningHitProof

open Classical in
/-- `gatedContinuation_sum_step` with the charge at an unseen gate only. A later call of a gate
input costs nothing. -/
theorem gatedContinuation_sum_step_unseen {ι α : Type} [Fintype ι]
    (oa : OracleComp (WorldSpec C) α) (event : ι → α × LoggedState C → Prop)
    (gate : ι → (WorldSpec C).Domain) (hinj : Function.Injective gate)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ε : ℝ≥0∞)
    (hgate : ∀ i, ¬GateSeen (gate i) s.2 → t = gate i →
      (∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * continuationReserve prims oa (event i) r.2) ≤ ε) :
    (∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] *
      ∑ i, gatedContinuation prims oa (event i) (gate i) r.2) ≤
      (∑ i, gatedContinuation prims oa (event i) (gate i) s) +
        if ∃ i, t = gate i ∧ ¬GateSeen (gate i) s.2 then ε else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc
    _ ≤ ∑ i, (gatedContinuation prims oa (event i) (gate i) s +
        if ¬GateSeen (gate i) s.2 ∧ t = gate i then ε else 0) :=
      Finset.sum_le_sum fun i _ => gatedContinuation_step prims oa (event i) (gate i) t s ε (hgate i)
    _ = _ + ∑ i, if ¬GateSeen (gate i) s.2 ∧ t = gate i then ε else 0 := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add le_rfl
      by_cases hex : ∃ i, t = gate i
      · obtain ⟨i, hi⟩ := hex
        rw [Finset.sum_eq_single i]
        · by_cases hs : GateSeen (gate i) s.2
          · simp [hs]
          · rw [if_pos ⟨hs, hi⟩, if_pos ⟨i, hi, hs⟩]
        · intro j _ hji
          have hne : t ≠ gate j := fun h => hji (hinj (h.symm.trans hi))
          simp [hne]
        · simp
      · have hn : ∀ i, t ≠ gate i := by simpa using hex
        simp [hn]

open Classical in
/-- The expected number of calls on a gate that is not seen is at most the number of the gates.
Each such call makes its gate seen. -/
theorem unseenGate_cost_le {ι α : Type} [Fintype ι] (gate : ι → (WorldSpec C).Domain)
    (hinj : Function.Injective gate) (oa : OracleComp (WorldSpec C) α) (s : LoggedState C) :
    XmssSecurity.expectedSimulatedCost (loggedImpl prims)
      (fun t s => if ∃ i, t = gate i ∧ ¬GateSeen (gate i) s.2 then 1 else 0) oa s ≤
        (Fintype.card ι : ℝ≥0∞) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let f : LoggedState C → ℝ≥0∞ := fun s =>
    ((Finset.univ.filter fun i => GateSeen (gate i) s.2).card : ℝ≥0∞)
  have hstep : ∀ t (s : LoggedState C), True →
      f s + (if ∃ i, t = gate i ∧ ¬GateSeen (gate i) s.2 then 1 else 0) ≤
        ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * f r.2 := by
    intro t s _
    calc _ = ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] *
          (f s + if ∃ i, t = gate i ∧ ¬GateSeen (gate i) s.2 then 1 else 0) := by
          rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support ((loggedImpl prims t).run s)
          · gcongr
            have hseen : ∀ i, GateSeen (gate i) r.2.2 ↔ GateSeen (gate i) s.2 ∨ t = gate i := by
              intro i
              rw [loggedImpl_log prims t s r hr, gateSeen_logQuery]
            have hsub : (Finset.univ.filter fun i => GateSeen (gate i) s.2) ⊆
                Finset.univ.filter fun i => GateSeen (gate i) r.2.2 := by
              intro i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, hseen]
              exact Or.inl
            split_ifs with hex
            · obtain ⟨i, hi, hun⟩ := hex
              have hlt : (Finset.univ.filter fun i => GateSeen (gate i) s.2).card + 1 ≤
                  (Finset.univ.filter fun i => GateSeen (gate i) r.2.2).card := by
                rw [← Finset.card_insert_of_notMem (by simpa using hun)]
                refine Finset.card_le_card (Finset.insert_subset ?_ hsub)
                simp [hseen, hi]
              simp only [f]
              exact_mod_cast hlt
            · simp only [f, add_zero]
              exact_mod_cast Finset.card_le_card hsub
          · simp [prEvent_eq_zero_of_not_mem_support _ hr]
  have hge := XmssSecurity.expectedFinal_ge (loggedImpl prims) (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) f _ hstep oa s trivial
  have hle : XmssSecurity.expectedFinal (loggedImpl prims) f oa s ≤ (Fintype.card ι : ℝ≥0∞) := by
    unfold XmssSecurity.expectedFinal
    refine SigningPartnerBoundProof.tsum_probOutput_mul_le_of_const _ _ _ fun r _ => ?_
    simp only [f]
    exact_mod_cast Finset.card_le_univ _
  exact (le_add_left le_rfl).trans (hge.trans hle)

end Gate

attribute [local instance] Classical.propDecidable

/-- The invariant of the hit potential after the dealer. Each top gate is seen, and the top tree
is resolved in the cache. -/
def HitInv (x : Keys3 C) (T : C.Term) (top : TopTree) (s : LoggedState C) : Prop :=
  (¬Programmed s.2 → SigningHitProof.RawReachable prims s) ∧
  (∀ b, SigningHitProof.GateSeen (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s.2) ∧
  DeterministicSigning.Resolves s.1.1
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top)
    (some (.top top))

/-- The premise of the gates for one term, the conclusion of `KeyGateBoundOwn`. -/
def GateFunded (A : TsigAdversary C) (x : Keys3 C) (T : C.Term) : Prop :=
  ∀ (b : XmssSecurity.TopIndex) s, SigningHitProof.RawReachable prims s →
    ¬SigningHitProof.GateSeen (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s.2 →
    (∑' r, Pr{let z ← (loggedImpl prims (.inr (.inr (.inl (SigningHitProof.topGateInput x T b))))).run s}[z = r] *
      SigningHitProof.continuationReserve prims (SigningDescentProof.finalRun A x)
        (SigningHitProof.ForestExceptionAt prims x b) r.2) ≤ (2 ^ 128 : ℝ≥0∞)⁻¹

section Calculus

variable (A : TsigAdversary C) (x : Keys3 C) (T : C.Term)

/-- Each top gate is in the log. -/
def AllSeen (s : LoggedState C) : Prop :=
  ∀ b, SigningHitProof.GateSeen (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s.2

/-- The invariant of the honest work after the dealer. Each top gate is seen, and the cache
resolves the top tree. -/
def RunInv (top : TopTree) (s : LoggedState C) : Prop :=
  AllSeen x T s ∧ DeterministicSigning.Resolves s.1.1
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top)
    (some (.top top))

theorem loggedImpl_cache_le (t : (WorldSpec C).Domain) (s : LoggedState C)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    s.1.1 ≤ r.2.1.1 := by
  simp only [loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  exact SigningCacheProof.countImpl_grows prims t s.1 z hz

theorem allSeen_step (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : AllSeen x T s)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    AllSeen x T r.2 := fun b => by
  rw [loggedImpl_log prims t s r hr, SigningHitProof.gateSeen_logQuery]
  exact Or.inl (hs b)

theorem runInv_run {α : Type} (top : TopTree) (oa : OracleComp (WorldSpec C) α) (s : LoggedState C)
    (hs : RunInv x T top s) :
    ∀ r ∈ support ((simulateQ (loggedImpl prims) oa).run s), RunInv x T top r.2 :=
  SeedHitProof.support_simulateQ_inv _ _ (fun t s hs r hr =>
    ⟨allSeen_step prims x T t s hs.1 r hr, hs.2.mono (loggedImpl_cache_le prims t s r hr)⟩) oa s hs

theorem programmed_run {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C)
    (hs : Programmed s.2) :
    ∀ r ∈ support ((simulateQ (loggedImpl prims) oa).run s), Programmed r.2.2 :=
  SeedHitProof.support_simulateQ_inv _ (fun s : LoggedState C => Programmed s.2) (fun t s hs r hr => by
    rw [loggedImpl_log prims t s r hr, programmed_logQuery]
    exact Or.inl hs) oa s hs

theorem topGate_injective : Function.Injective fun b : XmssSecurity.TopIndex =>
    (.inr (.inr (.inl (SigningHitProof.topGateInput x T b))) : (WorldSpec C).Domain) := by
  intro b c h
  exact SigningHitProof.topGateInput_injective x T (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))

/-- The gate part of the hit potential does not rise at a call when each gate is seen. -/
theorem gateSum_step (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : AllSeen x T s) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] *
        ∑ b, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
          (SigningHitProof.ForestExceptionAt prims x b)
          (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) r.2 ≤
      ∑ b, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
        (SigningHitProof.ForestExceptionAt prims x b)
        (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s := by
  have hg := gatedContinuation_sum_step_unseen prims (SigningDescentProof.finalRun A x)
    (SigningHitProof.ForestExceptionAt prims x) _ (topGate_injective x T) t s 0
    (fun b hb _ => (hb (hs b)).elim)
  simpa only [ite_self, add_zero] using hg

/-- The gate part of the hit potential does not rise over a program when each gate is seen. -/
theorem gateSum_run_le {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C)
    (hs : AllSeen x T s) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] *
        ∑ b, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
          (SigningHitProof.ForestExceptionAt prims x b)
          (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) r.2 ≤
      ∑ b, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
        (SigningHitProof.ForestExceptionAt prims x b)
        (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s := by
  have h := XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := AllSeen x T)
    (fun t s hs r hr => allSeen_step prims x T t s hs r hr)
    (fun s => ∑ b, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
      (SigningHitProof.ForestExceptionAt prims x b)
      (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s) (fun _ _ => 0 * 0)
    (fun t s hs => (gateSum_step prims A x T t s hs).trans (le_add_right le_rfl)) oa s hs
  rw [XmssSecurity.expectedSimulatedCost_const_mul, zero_mul, add_zero] at h
  exact h

/-- One call raises the guarded hit potential by its structural cost when each gate is seen. -/
theorem hit_seen_step (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : AllSeen x T s) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s +
        (2 ^ 128 : ℝ≥0∞)⁻¹ *
          (SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t : ℝ≥0∞) := by
  refine SigningGuessProof.guarded_domain_step prims (AllSeen x T)
    (SigningGuessProof.structuralHitPotential prims A x T)
    (fun t => (2 ^ 128 : ℝ≥0∞)⁻¹ *
      (SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t : ℝ≥0∞))
    (fun t s hs _ ht => ?_) t s (fun _ => hs)
  have hc := SigningGuessProof.cachePotential_domain_step prims (SigningHitProof.forestRelevant x.1)
    (SigningHitProof.completionPotential (SigningHitProof.forestRelevant x.1)
      (SigningHitProof.forestCompletion x))
    (SigningHitProof.completionPotential_randomOracle_step _ _
      (SigningHitProof.forestCompletion_reads x)) t s ht
  have hg := gateSum_step prims A x T t s hs
  simp only [SigningGuessProof.structuralHitPotential, mul_add, ENNReal.tsum_add]
  refine (add_le_add hc hg).trans_eq ?_
  ring

/-- A program raises the guarded hit potential by its expected structural cost when each gate is
seen. -/
theorem hit_run_le {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C)
    (hs : AllSeen x T s) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s +
        (2 ^ 128 : ℝ≥0∞)⁻¹ * XmssSecurity.expectedSimulatedCost (loggedImpl prims)
          (fun t _ => (SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t : ℝ≥0∞))
          oa s := by
  have h := XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := AllSeen x T)
    (fun t s hs r hr => allSeen_step prims x T t s hs r hr) _ _
    (fun t s hs => hit_seen_step prims A x T t s hs) oa s hs
  rwa [XmssSecurity.expectedSimulatedCost_const_mul] at h

theorem rawDomainCost_le_one (relevant : Query C → Prop) (t : (WorldSpec C).Domain) :
    SigningGuessProof.rawDomainCost relevant t ≤ 1 := by
  unfold SigningGuessProof.rawDomainCost
  split <;> (try split_ifs) <;> simp

/-- A program with at most `n` structural calls raises the guarded hit potential by at most `n`
units when each gate is seen. -/
theorem hit_run_bound {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (hb : oa.IsQueryBoundP
      (fun t => SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t ≠ 0) n)
    (s : LoggedState C) (hs : AllSeen x T s) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s +
        (2 ^ 128 : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞) := by
  refine (hit_run_le prims A x T oa s hs).trans (add_le_add le_rfl ?_)
  gcongr
  refine (XmssSecurity.expectedSimulatedCost_mono _ (right := fun t _ =>
    if SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t ≠ 0 then 1 else 0)
    (fun t _ => ?_) _ _).trans ?_
  · have h := rawDomainCost_le_one (SigningHitProof.forestRelevant x.1) t
    split_ifs with hne
    · exact_mod_cast h
    · simp only [ne_eq, not_not] at hne
      simp [hne]
  · rw [XmssSecurity.expectedSimulatedCost_indicator]
    exact XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ _ n _ hb

/-- A block of honest hash calls that the forest completion covers does not raise the guarded hit
potential when each gate is seen. -/
theorem hit_block_le {β : Type} (block : OracleComp (Query C →ₒ HashOutput) β) (s : LoggedState C)
    (hs : AllSeen x T s)
    (hcovered : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningHitProof.recordReads (SigningHitProof.forestRun x) ∅)).run s.1.1),
      ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningHitProof.recordReads block ∅)).run z.2),
      ∀ input, SigningHitProof.forestRelevant x.1 input → (w.1.2 input).isSome →
        (z.1.2 input).isSome ∨ (s.1.1 input).isSome) :
    ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (liftFree (SigningHitProof.hashEmbed block))).run s)}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s := by
  by_cases hp : Programmed s.2
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun r => ?_) zero_le
    by_cases hr : r ∈ support ((simulateQ (loggedImpl prims)
      (liftFree (SigningHitProof.hashEmbed block))).run s)
    · simp [guarded, programmed_run prims _ s hp r hr]
    · simp [prEvent_eq_zero_of_not_mem_support _ hr]
  rw [guarded, if_neg hp]
  have hc := SigningOwnPotential.logged_block_potential_le prims (SigningHitProof.forestRelevant x.1)
    (SigningHitProof.forestRun x) (fun _ record => SigningHitProof.forestTargets x.1 record) block s
    hcovered
  have hg := gateSum_run_le prims A x T (liftFree (SigningHitProof.hashEmbed block)) s hs
  calc _ ≤ ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (liftFree (SigningHitProof.hashEmbed block))).run s)}[z = r] *
          SigningGuessProof.structuralHitPotential prims A x T r.2 := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        gcongr
        unfold guarded
        split_ifs <;> simp
    _ ≤ _ := by
        simp only [SigningGuessProof.structuralHitPotential, mul_add, ENNReal.tsum_add]
        exact add_le_add hc hg

/-- A program that the cache resolves does not raise the guarded hit potential when each gate is
seen. Each of its calls is on a cached input. -/
theorem hit_replay_le {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β) (v : β)
    (s : LoggedState C) (hs : AllSeen x T s) (hres : DeterministicSigning.Resolves s.1.1 oa v) :
    ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (liftFree (SigningHitProof.hashEmbed oa))).run s)}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s := by
  refine hit_block_le prims A x T oa s hs fun z hz w hw input _ hread => Or.inr ?_
  have hsz := DeterministicSigning.cache_le_of_run _ _ z hz
  have hzw := DeterministicSigning.cache_le_of_run _ _ w hw
  have hle := SigningOwnCover.recordReads_le_of_resolves oa ∅ z.2 s.1.1 v
    (fun _ _ h => by cases h) hres w hw (hsz.trans hzw)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hread
  simp [hle hu]

/-- A call of the honest operators on `H` that the structural cost charges. -/
def RoRelevant : (RoSpec C).Domain → Prop
  | .inl q => SigningHitProof.forestRelevant x.1 q
  | .inr _ => False

theorem liftFree_query_bind {α : Type} (t : (RoSpec C).Domain)
    (k : (RoSpec C).Range t → OracleComp (RoSpec C) α) :
    liftFree (liftM ((RoSpec C).query t) >>= k) =
      liftM ((WorldSpec C).query (.inr (.inr t))) >>= fun u => liftFree (k u) := by
  simp [liftFree, free]
  rfl

/-- The free copy of an honest program has as many structural calls as the program. -/
theorem liftFree_bound {α : Type} (R : OracleComp (RoSpec C) α) (n : ℕ)
    (h : R.IsQueryBoundP (RoRelevant x) n) :
    (liftFree R).IsQueryBoundP
      (fun t => SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1) t ≠ 0) n := by
  induction R using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftFree_query_bind, isQueryBoundP_query_bind_iff]
    have hiff : SigningGuessProof.rawDomainCost (SigningHitProof.forestRelevant x.1)
        (.inr (.inr t) : (WorldSpec C).Domain) ≠ 0 ↔ RoRelevant x t := by
      rcases t with q | p
      · simp [SigningGuessProof.rawDomainCost, RoRelevant]
      · have hn : ¬SigningHitProof.forestRelevant (C := C) x.1 (.streamKey p.2.1) := by
          rintro ⟨_, _, _, _, h, _⟩
          cases h
        simp [SigningGuessProof.rawDomainCost, RoRelevant, hn]
    simp only [hiff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- An honest program that does not raise the guarded hit potential from a state with the
invariant. -/
def HonestFlat (top : TopTree) {α : Type} (R : OracleComp (RoSpec C) α) : Prop :=
  ∀ s, RunInv x T top s →
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) (liftFree R)).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s

theorem honestFlat_bind (top : TopTree) {α β : Type} {R : OracleComp (RoSpec C) α}
    {f : α → OracleComp (RoSpec C) β} (hR : HonestFlat prims A x T top R)
    (hf : ∀ a, HonestFlat prims A x T top (f a)) : HonestFlat prims A x T top (R >>= f) := by
  intro s hs
  rw [show ∀ {α β : Type} (R : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β),
    liftFree (R >>= f) = liftFree R >>= fun a => liftFree (f a) from φ_bind, simulateQ_bind, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) (hR s hs)
  by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) (liftFree R)).run s)
  · gcongr
    exact hf z.1 z.2 (runInv_run prims x T top _ s hs z hz)
  · simp [prEvent_eq_zero_of_not_mem_support _ hz]

theorem honestFlat_of_bound (top : TopTree) {α : Type} (R : OracleComp (RoSpec C) α)
    (h : R.IsQueryBoundP (RoRelevant x) 0) : HonestFlat prims A x T top R := fun s hs => by
  simpa using hit_run_bound prims A x T (liftFree R) 0 (liftFree_bound x R 0 h) s hs.1

theorem honestFlat_pure (top : TopTree) {α : Type} (a : α) :
    HonestFlat prims A x T top (pure a : OracleComp (RoSpec C) α) :=
  honestFlat_of_bound prims A x T top _ (isQueryBoundP_pure _ _ _)

theorem honestFlat_map (top : TopTree) {α β : Type} {R : OracleComp (RoSpec C) α} (g : α → β)
    (hR : HonestFlat prims A x T top R) : HonestFlat prims A x T top (g <$> R) := by
  rw [map_eq_bind_pure_comp]
  exact honestFlat_bind prims A x T top hR fun a => honestFlat_pure prims A x T top _

set_option maxRecDepth 100000 in
/-- The build of a bottom tree does not raise the guarded hit potential. -/
theorem honestFlat_bottom (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    HonestFlat prims A x T top (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
      (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b))) := fun s hs =>
  hit_block_le prims A x T _ s hs.1 fun z hz w hw input hrel hread =>
    Or.inl (SigningOwnCover.forestRun_covers_bottom x top b s.1.1 hs.2 z hz w hw input hrel hread)

theorem forestRelevant_hash {P : PublicParameter} {q : Query C}
    (h : SigningHitProof.forestRelevant P q) : ∃ input, q = .hash input := by
  obtain ⟨_, _, _, _, he, _⟩ := h
  exact ⟨_, he⟩

theorem message_not_forestRelevant (P P' : PublicParameter) (lay : Layer) (key : KeyIndex)
    (payload : HashInput) :
    ¬SigningHitProof.forestRelevant (C := C) P
      (.hash (tweakableHashInput P' (.message lay key) payload)) := by
  rintro ⟨domain, payload', _, hd, he, _⟩
  have h := Query.hash.inj he
  have heq :
      XmssSecurity.bytesLE 16 P' ++
          XmssSecurity.fieldBytes (XmssSecurity.tweakFields 12 0 (layerHi lay 0) key.val) ++ payload =
        XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields domain) ++
          (payload' ++ XmssSecurity.domainSuffix domain) := by
    rw [← XmssSecurity.Bridge.tweakableHashInput_eq P domain payload', ← h]
    rfl
  have ht := congrArg (fun fields => fields.tag.toNat) (XmssSecurity.Bridge.prefix_inj heq).2.1
  cases domain <;> simp only [SigningHitProof.StructuralDomain] at hd <;>
    norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at ht

theorem mapM_bound_zero {ι α β : Type} {spec : OracleSpec ι} (xs : List α)
    (f : α → OracleComp spec β) (p : ι → Prop) [DecidablePred p]
    (hf : ∀ a, (f a).IsQueryBoundP p 0) : (xs.mapM f).IsQueryBoundP p 0 := by
  induction xs with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons a xs ih =>
      simp only [List.mapM_cons]
      exact isQueryBoundP_bind (n := 0) (m := 0) (hf a) (fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0) ih (fun _ _ => isQueryBoundP_pure _ _ _))

theorem sequenceFin_bound_zero {ι α : Type} {spec : OracleSpec ι} {n : ℕ}
    (f : Fin n → OracleComp spec α) (p : ι → Prop) [DecidablePred p]
    (hf : ∀ a, (f a).IsQueryBoundP p 0) : (OverPermutation.sequenceFin f).IsQueryBoundP p 0 := by
  induction n with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ n ih =>
      unfold OverPermutation.sequenceFin
      exact isQueryBoundP_bind (n := 0) (m := 0) (hf 0) (fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0) (ih _ fun i => hf i.succ) (fun _ _ => isQueryBoundP_pure _ _ _))

theorem hashEmbed_query_bind {α : Type} (q : Query C) (k : HashOutput → OracleComp (Query C →ₒ HashOutput) α) :
    SigningHitProof.hashEmbed (liftM ((Query C →ₒ HashOutput).query q) >>= k) =
      liftM ((RoSpec C).query (.inl q)) >>= fun u => SigningHitProof.hashEmbed (k u) := by
  simp [SigningHitProof.hashEmbed, hashQuery]

theorem hashEmbed_bound {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) (n : ℕ)
    (h : oa.IsQueryBoundP (SigningHitProof.forestRelevant x.1) n) :
    (SigningHitProof.hashEmbed oa).IsQueryBoundP (RoRelevant x) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [hashEmbed_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem tweakable_bound {α : Type} (oa : OracleComp HashSpec α)
    (h : oa.IsQueryBoundP (fun input => SigningHitProof.forestRelevant (C := C) x.1 (.hash input)) 0) :
    (tweakable oa : OracleComp (RoSpec C) α).IsQueryBoundP (RoRelevant x) 0 := by
  rw [← SigningHitProof.hashEmbed_forestHash]
  exact hashEmbed_bound x _ 0 (SigningOwnCover.forestHash_irrelevant x.1 oa h)

theorem prfValue_bound (seeds : C.Term → HashOutput) (pt : Point) :
    (prfValue seeds pt).IsQueryBoundP (RoRelevant x) 0 := by
  rw [← SigningHitProof.hashEmbed_forestValue]
  exact hashEmbed_bound x _ 0 (SigningOwnCover.forestValue_irrelevant x.1 seeds pt)

theorem eval_bound (keys : Keys C) (i : C.Party) (J : C.Quorum) (pt : Point) (message : Message) :
    (eval keys i J pt message).IsQueryBoundP (RoRelevant x) 0 := by
  unfold eval
  refine isQueryBoundP_bind (n := 0) (m := 0) (mapM_bound_zero _ _ _ fun T => ?_) fun _ _ =>
    isQueryBoundP_bind (n := 0) (m := 0) (mapM_bound_zero _ _ _ fun j => ?_) fun _ _ =>
      isQueryBoundP_pure _ _ _
  · simp only [prf, hashQuery, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h =>
      (SigningHitProof.forestRelevant_prf (C := C) x.1 _ _ h).elim
  · simp only [hashQuery, isQueryBoundP_map_iff]
    refine (isQueryBoundP_query_iff _ _ _).2 fun h => ?_
    obtain ⟨_, he⟩ := forestRelevant_hash (C := C) (P := x.1) h
    cases he

theorem grind_bound (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomizer) : ∀ attempts trial,
    (grind P lay key message base attempts trial : OracleComp HashSpec _).IsQueryBoundP
      (fun input => SigningHitProof.forestRelevant (C := C) x.1 (.hash input)) 0
  | 0, _ => isQueryBoundP_pure _ _ _
  | attempts + 1, trial => by
    rw [grind]
    unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash Verification.thWithHash
      Verification.oracleHashWithHash
    simp only [bind_assoc, pure_bind]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => ?_
    · exact (isQueryBoundP_query_iff _ _ _).2 fun hf =>
        (message_not_forestRelevant _ _ _ _ _ hf).elim
    · split
      · exact isQueryBoundP_pure _ _ _
      · exact grind_bound P lay key message base attempts (trial + 1)

theorem signCodeword_bound (P : PublicParameter) (commitment : Digest) (e : KeyIndex)
    (message : Message) (ρ : Digest) :
    (signCodeword P commitment e message ρ).IsQueryBoundP (RoRelevant x) 0 := by
  unfold signCodeword
  refine tweakable_bound x _ ?_
  unfold Verification.oracleHashWithHash
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => ?_
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hf =>
      (SigningGuessProof.forestRelevant_not_commitment x.1 _ hf ⟨_, _, _, rfl⟩).elim
  · simp only []
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => grind_bound x _ _ _ _ _ _ _
      exact (isQueryBoundP_query_iff _ _ _).2 fun hf =>
        (SigningOwnCover.randomizer_not_forestRelevant _ _ _ _ _ _ hf).elim

/-- The honest operators with the keys of `x` and the top tree `top`, in the hash world. -/
abbrev honestDealt (top : TopTree) : Dealt C (OracleComp (RoSpec C)) :=
  dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1)

theorem honestFlat_bottomOnce (top : TopTree) (b : Fin (2 ^ layerHeight)) (st : TsigState C) :
    HonestFlat prims A x T top ((bottomOnce (honestDealt x top) b).run st) := by
  unfold bottomOnce
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact honestFlat_pure prims A x T top _
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    refine honestFlat_bind prims A x T top ?_ fun _ => honestFlat_of_bound prims A x T top _ (by simp)
    simp only [honestDealt, dealtWith]
    rw [← SigningHitProof.hashEmbed_referenceTree]
    exact honestFlat_map prims A x T top _ (honestFlat_bottom prims A x T top b)

theorem signRound2With_bound (part : Point → OracleComp (RoSpec C) Digest)
    (hpart : ∀ pt, (part pt).IsQueryBoundP (RoRelevant x) 0) (P : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    (signRound2With (fun oa => oa) part P J commitment e message parts).IsQueryBoundP
      (RoRelevant x) 0 := by
  unfold signRound2With
  refine isQueryBoundP_bind (n := 0) (m := 0) (signCodeword_bound x _ _ _ _ _) fun r _ => ?_
  rcases r with _ | ⟨_, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) (sequenceFin_bound_zero _ _ fun l => ?_)
      fun _ _ => isQueryBoundP_pure _ _ _
    split_ifs
    · simpa using hpart _
    · exact isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- A signing oracle does not raise the guarded hit potential. Its builds are covered by the
forest completion, and its other calls are not structural. -/
theorem honestFlat_tsigOracles (top : TopTree) (q : (TsigSpec C).Domain) (st : TsigState C) :
    HonestFlat prims A x T top ((tsigOracles (fun oa => oa) (honestDealt x top) q).run st) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    apply honestFlat_of_bound
    split_ifs <;> simp
  · simp only [tsigOracles, StateT.run_bind]
    refine honestFlat_bind prims A x T top (honestFlat_bottomOnce prims A x T top b st) fun p => ?_
    apply honestFlat_of_bound
    rcases p with ⟨_ | tree, st'⟩
    · simp
    · simp
      exact prfValue_bound x _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    apply honestFlat_of_bound
    split_ifs
    · simp
    · simp
      exact eval_bound x _ _ _ _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simpa using honestFlat_pure prims A x T top _
    · simp only [StateT.run_bind]
      refine honestFlat_bind prims A x T top (honestFlat_bottomOnce prims A x T top _ st) fun p => ?_
      apply honestFlat_of_bound
      rcases p with ⟨_ | tree, st'⟩
      · simp
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
        simp only [pure_bind]
        refine isQueryBoundP_bind (n := 0) (m := 0) (eval_bound x _ _ _ _ _) fun own _ => ?_
        refine isQueryBoundP_bind (n := 0) (m := 0)
          (signRound2With_bound x _ (fun pt => eval_bound x _ _ _ _ _) _ _ _ _ _ _) fun r _ => ?_
        rcases r with _ | values <;> simp

/-- A bottom tree that resolves to a tree resolves the Merkle root of the chain ends of that tree. -/
theorem resolves_bottom_root (cache : HashCache C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (tree : BottomTree)
    (h : DeterministicSigning.Resolves cache (referenceTree SigningHitProof.forestHash
      (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b)) (some (.bottom tree))) :
    ∃ root, DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (merkleNode x.1 bottomLayer (fun e l => (tree.cpk e l).2.2) layerHeight b.val) root := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, htail⟩ := h.of_bind
  obtain ⟨values, hvalues, rfl⟩ := houtputs.of_map
  obtain ⟨root, hroot, hrest⟩ := htail.of_bind
  obtain ⟨base, -, hrest⟩ := hrest.of_bind
  obtain ⟨selected, -, hrest⟩ := hrest.of_bind
  rcases selected with _ | ⟨randomness, encoding⟩
  · cases hrest.pure_inv
  obtain ⟨outs, -, hrest⟩ := hrest.of_bind
  rcases outs with _ | outs
  · cases hrest.pure_inv
  obtain ⟨path, -, hrest⟩ := hrest.of_bind
  obtain ⟨topRoot, -, hrest⟩ := hrest.of_bind
  split_ifs at hrest
  · cases hrest.pure_inv
  have ht := hrest.pure_inv
  simp only [Option.some.injEq, TreeOutput.bottom.injEq] at ht
  subst ht
  exact ⟨root, SigningHitProof.resolves_forestHash _ _ _ hroot⟩

theorem xor_one_div_two (d : ℕ) : Nat.xor d 1 / 2 = d / 2 := by
  rcases Nat.even_or_odd' d with ⟨n, rfl | rfl⟩
  · rw [SigningOwnCover.xor_one_even]
    omega
  · rw [SigningOwnCover.xor_one_odd]
    omega

/-- The cache and replay fact of the bottom path. A bottom tree that resolves to a tree resolves
the authentication path of each key of the tree under the chain ends of that tree. -/
theorem resolves_bottomPath (cache : HashCache C) (top : TopTree) (e : KeyIndex) (tree : BottomTree)
    (h : DeterministicSigning.Resolves cache (referenceTree SigningHitProof.forestHash
      (SigningHitProof.forestValue x.2.1) x.1 top (.bottom (treeOf e))) (some (.bottom tree))) :
    ∃ path, DeterministicSigning.Resolves cache (SigningHitProof.forestHash
      (merklePath x.1 bottomLayer (fun e l => (tree.cpk e l).2.2) e)) path := by
  obtain ⟨root, hroot⟩ := resolves_bottom_root x cache top _ tree h
  have hlev : ∀ level : Fin layerHeight, ∃ u, DeterministicSigning.Resolves
      (SigningDescentProof.thView cache)
      (merkleNode x.1 bottomLayer (fun e l => (tree.cpk e l).2.2) level.val
        (Nat.xor (e.val / 2 ^ level.val) 1)) u := by
    intro level
    have hl : level.val < 16 := level.isLt
    have hsplit : ∀ a, a / 2 ^ (16 - level.val) = a / 2 / 2 ^ (15 - level.val) := by
      intro a
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      congr 2
      omega
    have hb : (treeOf e).val = Nat.xor (e.val / 2 ^ level.val) 1 / 2 ^ (16 - level.val) := by
      rw [hsplit, xor_one_div_two, ← hsplit, Nat.div_div_eq_div_mul, ← pow_add]
      simp only [treeOf, layerHeight]
      congr 2
      omega
    have hpos : 0 < 2 ^ (16 - level.val) := by positivity
    obtain ⟨u, hu⟩ := SigningHitProof.resolves_merkleNode_descendant _ x.1 bottomLayer _ layerHeight
      (treeOf e).val root hroot (16 - level.val) (by simp only [layerHeight]; omega)
      (Nat.xor (e.val / 2 ^ level.val) 1 % 2 ^ (16 - level.val)) (Nat.mod_lt _ hpos)
    have hheight : layerHeight - (16 - level.val) = level.val := by
      simp only [layerHeight]
      omega
    have hindex : (treeOf e).val * 2 ^ (16 - level.val) +
        Nat.xor (e.val / 2 ^ level.val) 1 % 2 ^ (16 - level.val) = Nat.xor (e.val / 2 ^ level.val) 1 := by
      rw [hb, mul_comm]
      exact Nat.div_add_mod _ _
    rw [hheight, hindex] at hu
    exact ⟨u, hu⟩
  choose us hus using hlev
  refine ⟨us, SigningOwnCover.forestHash_resolves _ _ _ ?_⟩
  unfold merklePath
  rw [XmssSecurity.Bridge.sequenceFin_eq]
  exact DeterministicSigning.Resolves.sequenceFin hus

theorem bound_bind_le {ι α β : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {a b n : ℕ} (h1 : oa.IsQueryBoundP p a)
    (h2 : ∀ y, (ob y).IsQueryBoundP p b) (h : a + b ≤ n) : (oa >>= ob).IsQueryBoundP p n :=
  (isQueryBoundP_bind h1 fun y _ => h2 y).mono h

theorem bound_of_calls {α : Type} {oa : OracleComp HashSpec α} {n : ℕ}
    (h : SigningOwnVerify.Calls oa n) (p : HashInput → Prop) [DecidablePred p] :
    oa.IsQueryBoundP p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    unfold SigningOwnVerify.Calls at h ih
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    simp only [not_true_eq_false, false_or, if_true] at h
    refine ⟨Or.inr h.1, fun u => ?_⟩
    split_ifs
    · exact ih u (h.2 u)
    · exact (ih u (h.2 u)).mono (Nat.sub_le _ _)

attribute [local irreducible] layerHeight chainCount in
/-- One layer of the verification makes at most `191` structural calls. Its message digest call is
not structural. -/
theorem layerRoot_relevant (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    (Verification.layerRootWithHash P lay key message part : OracleComp HashSpec (Option Digest)).IsQueryBoundP
      (fun input => SigningHitProof.forestRelevant (C := C) x.1 (.hash input)) 191 := by
  unfold Verification.layerRootWithHash Verification.otsLeafWithHash
  refine bound_bind_le (a := 175) (b := 16) (bound_bind_le (a := 0) (b := 175) ?_
    (fun digest => ?_) le_rfl) (fun leaf => ?_) le_rfl
  · unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash Verification.thWithHash
      Verification.oracleHashWithHash
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _
    exact (isQueryBoundP_query_iff _ _ _).2 fun hf => (message_not_forestRelevant _ _ _ _ _ hf).elim
  · refine bound_of_calls ?_ _
    cases Codeword.decode digest with
    | none => exact isQueryBoundP_pure _ _ _
    | some encoding =>
        dsimp only
        refine SigningOwnVerify.calls_bind_le (SigningOwnVerify.calls_sequenceFin (b := 3) _
          fun chainIdx => (SigningOwnVerify.calls_chainWalk _ _ _ _ _ _ _).mono ?_) (b := 1)
          (fun _ => SigningOwnVerify.calls_bind_le (SigningOwnVerify.calls_tweakableHash _ _ _) (b := 0)
            (fun _ => isQueryBoundP_pure _ _ _) le_rfl) (by unfold chainCount; omega)
        unfold chainLength winternitzBits
        omega
  · refine bound_of_calls ?_ _
    cases leaf with
    | none => exact isQueryBoundP_pure _ _ _
    | some leaf =>
        exact SigningOwnVerify.calls_bind_le (SigningOwnVerify.calls_treeFold P lay key part.authenticationPath
          layerHeight leaf) (b := 0) (fun _ => isQueryBoundP_pure _ _ _) (by unfold layerHeight; omega)

/-- The verification makes at most `382` structural calls. -/
theorem verify_relevant (publicKey : PublicKey) (message : Message) (signature : Signature) :
    (Verification.verifyWithHash publicKey message signature : OracleComp HashSpec Bool).IsQueryBoundP
      (fun input => SigningHitProof.forestRelevant (C := C) x.1 (.hash input)) 382 := by
  unfold Verification.verifyWithHash
  refine bound_bind_le (layerRoot_relevant x _ _ _ _ _) (b := 191) (fun bottomRoot => ?_) le_rfl
  cases bottomRoot with
  | none => exact isQueryBoundP_pure _ _ _
  | some bottomRoot =>
      refine bound_bind_le (layerRoot_relevant x _ _ _ _ _) (b := 0) (fun root => ?_) le_rfl
      cases root <;> exact isQueryBoundP_pure _ _ _

theorem forestHash_bound {α : Type} (oa : OracleComp HashSpec α) (n : ℕ)
    (h : oa.IsQueryBoundP (fun input => SigningHitProof.forestRelevant (C := C) x.1 (.hash input)) n) :
    (SigningHitProof.forestHash (C := C) oa).IsQueryBoundP (SigningHitProof.forestRelevant x.1) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [SigningHitProof.forestHash, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem logged_cache_le {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C) :
    ∀ r ∈ support ((simulateQ (loggedImpl prims) oa).run s), s.1.1 ≤ r.2.1.1 :=
  SeedHitProof.support_simulateQ_inv _ (fun p : LoggedState C => s.1.1 ≤ p.1.1)
    (fun t p hp r hr => hp.trans (loggedImpl_cache_le prims t p r hr)) oa s le_rfl

theorem logged_hashEmbed_resolves {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β)
    (s : LoggedState C) (z : β × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) (liftFree (SigningHitProof.hashEmbed oa))).run s)) :
    DeterministicSigning.Resolves z.2.1.1 oa z.1 := by
  have hlog := SigningCoreProof.simulateQ_run_forget (loggedImpl prims)
    (SigningCacheProof.countImpl prims) (fun t s b => by simp [loggedImpl, Functor.map_map])
    (liftFree (SigningHitProof.hashEmbed oa)) s.1 s.2
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (liftFree (SigningHitProof.hashEmbed oa))).run s.1) := by
    rw [← hlog, support_map]
    exact ⟨z, hz, rfl⟩
  exact SigningHitProof.run_hashEmbed_resolves prims oa s.1 _ hz'

/-- An honest program that does not raise the guarded hit potential from a state with the invariant
whose cache resolves `oa` to `v`. -/
def HonestFlatAfter (top : TopTree) {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β) (v : β)
    {α : Type} (R : OracleComp (RoSpec C) α) : Prop :=
  ∀ s, RunInv x T top s → DeterministicSigning.Resolves s.1.1 oa v →
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) (liftFree R)).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s

theorem honestFlatAfter_bind (top : TopTree) {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β)
    (v : β) {α γ : Type} {R : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) γ}
    (hR : HonestFlatAfter prims A x T top oa v R) (hf : ∀ a, HonestFlatAfter prims A x T top oa v (f a)) :
    HonestFlatAfter prims A x T top oa v (R >>= f) := by
  intro s hs hres
  rw [show ∀ {α β : Type} (R : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β),
    liftFree (R >>= f) = liftFree R >>= fun a => liftFree (f a) from φ_bind, simulateQ_bind, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) (hR s hs hres)
  by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) (liftFree R)).run s)
  · gcongr
    exact hf z.1 z.2 (runInv_run prims x T top _ s hs z hz)
      (hres.mono (logged_cache_le prims _ s z hz))
  · simp [prEvent_eq_zero_of_not_mem_support _ hz]

theorem honestFlatAfter_of (top : TopTree) {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β)
    (v : β) {α : Type} {R : OracleComp (RoSpec C) α} (hR : HonestFlat prims A x T top R) :
    HonestFlatAfter prims A x T top oa v R := fun s hs _ => hR s hs

theorem honestFlatAfter_replay (top : TopTree) {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β)
    (v : β) : HonestFlatAfter prims A x T top oa v (SigningHitProof.hashEmbed oa) := fun s hs hres =>
  hit_replay_le prims A x T oa v s hs.1 hres

set_option maxRecDepth 100000 in
/-- The honest signature does not raise the guarded hit potential. Its build is covered by the
forest completion, and its authentication path is on cached inputs. -/
theorem honestFlat_honestSignature (top : TopTree) (e : KeyIndex) (message : Message) :
    HonestFlat prims A x T top (honestSignature (fun oa => oa) (honestDealt x top) e message) := by
  unfold honestSignature
  simp only [honestDealt, dealtWith]
  rw [← SigningHitProof.hashEmbed_referenceTree, map_eq_bind_pure_comp, bind_assoc]
  intro s hs
  rw [show ∀ {α β : Type} (R : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β),
    liftFree (R >>= f) = liftFree R >>= fun a => liftFree (f a) from φ_bind, simulateQ_bind, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) (honestFlat_bottom prims A x T top (treeOf e) s hs)
  by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) (liftFree (SigningHitProof.hashEmbed
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top
      (.bottom (treeOf e)))))).run s)
  swap
  · simp [prEvent_eq_zero_of_not_mem_support _ hz]
  gcongr
  have hres := logged_hashEmbed_resolves prims _ s z hz
  have hinv := runInv_run prims x T top _ s hs z hz
  rcases z with ⟨out, s'⟩
  rcases out with _ | (top' | tree)
  · simpa using honestFlat_pure prims A x T top _ s' hinv
  · simpa using honestFlat_pure prims A x T top _ s' hinv
  · obtain ⟨path, hpath⟩ := resolves_bottomPath x _ top e tree hres
    simp only [Function.comp_apply, pure_bind]
    refine honestFlatAfter_bind prims A x T top _ path (honestFlatAfter_of prims A x T top _ path
      (honestFlat_of_bound prims A x T top _ (prfValue_bound x _ _))) (fun ρ => ?_) s' hinv hpath
    refine honestFlatAfter_bind prims A x T top _ path (honestFlatAfter_of prims A x T top _ path
      (honestFlat_of_bound prims A x T top _ (signCodeword_bound x _ _ _ _ _))) fun r => ?_
    rcases r with _ | ⟨randomness, encoding⟩
    · exact honestFlatAfter_of prims A x T top _ path (honestFlat_pure prims A x T top _)
    refine honestFlatAfter_bind prims A x T top _ path (honestFlatAfter_of prims A x T top _ path
      (honestFlat_of_bound prims A x T top _ (sequenceFin_bound_zero _ _ fun l => ?_))) fun values => ?_
    · split
      · exact prfValue_bound x _ _
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind (n := 0) (m := 0) (prfValue_bound x _ _) fun _ _ =>
          isQueryBoundP_pure _ _ _
    refine honestFlatAfter_bind prims A x T top _ path ?_ fun _ =>
      honestFlatAfter_of prims A x T top _ path (honestFlat_pure prims A x T top _)
    rw [← SigningHitProof.hashEmbed_forestHash]
    exact honestFlatAfter_replay prims A x T top _ path

theorem hit_bind_le {α β : Type} (oa : OracleComp (WorldSpec C) α) (ob : α → OracleComp (WorldSpec C) β)
    (s : LoggedState C) (a b : ℝ≥0∞)
    (h1 : ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s + a)
    (h2 : ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s),
      ∑' r, Pr{let y ← (simulateQ (loggedImpl prims) (ob z.1)).run z.2}[y = r] *
          guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
        guarded (SigningGuessProof.structuralHitPotential prims A x T) z.2 + b) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) (oa >>= ob)).run s}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s + (a + b) := by
  rw [simulateQ_bind, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' z, Pr{let y ← (simulateQ (loggedImpl prims) oa).run s}[y = z] *
        (guarded (SigningGuessProof.structuralHitPotential prims A x T) z.2 + b) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run s)
        · gcongr
          exact h2 z hz
        · simp [prEvent_eq_zero_of_not_mem_support _ hz]
    _ ≤ (guarded (SigningGuessProof.structuralHitPotential prims A x T) s + a) + 1 * b := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        exact add_le_add h1 (mul_le_mul_left (OracleComp.tsum_prEvent_le_one _) _)
    _ = _ := by rw [one_mul, add_assoc]

end Calculus

set_option maxRecDepth 100000 in
/-- The dealer raises the hit potential by one unit for each top gate. Its structural calls are
reads of the forest completion. -/
theorem hit_dealer_rise (A : TsigAdversary C) (x : Keys3 C) (T : C.Term)
    (hgate : GateFunded prims A x T) :
    ∑' r, Pr{let z ← dealerRun prims x}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2.1 ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ((2 ^ 16 : ℕ) : ℝ≥0∞) := by
  set ε := (2 ^ 128 : ℝ≥0∞)⁻¹
  let gate : XmssSecurity.TopIndex → (WorldSpec C).Domain :=
    fun b => .inr (.inr (.inl (SigningHitProof.topGateInput x T b)))
  let G : LoggedState C → ℝ≥0∞ := fun s => ∑ b, SigningHitProof.gatedContinuation prims
    (SigningDescentProof.finalRun A x) (SigningHitProof.ForestExceptionAt prims x b) (gate b) s
  let Inv : LoggedState C → Prop := fun s => ¬Programmed s.2 → SigningHitProof.RawReachable prims s
  let prog := liftFree (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
    (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top))
  have hinv : ∀ t s, Inv s → ∀ r ∈ support ((loggedImpl prims t).run s), Inv r.2 := by
    intro t s hs r hr hn
    have hn' : ¬Programmed s.2 ∧ ¬IsProgram t := by
      rw [loggedImpl_log prims t s r hr, programmed_logQuery, not_or] at hn
      exact hn
    exact .step t s (hs hn'.1) hn'.2 r hr
  have hstep : ∀ t s, Inv s → ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * guarded G r.2 ≤
      guarded G s + ε * (if ∃ b, t = gate b ∧ ¬SigningHitProof.GateSeen (gate b) s.2 then 1 else 0) := by
    intro t s hs
    by_cases hb : Programmed s.2 ∨ IsProgram t
    · refine le_trans (le_of_eq (OracleComp.tsum_prEvent_mul_of_const_on_support _ (c := 0)
        (fun r hr => ?_))) zero_le
      rw [guarded, if_pos (by rw [loggedImpl_log prims t s r hr, programmed_logQuery]; exact hb)]
    push Not at hb
    rw [guarded, if_neg hb.1]
    have h1 := gatedContinuation_sum_step_unseen prims (SigningDescentProof.finalRun A x)
      (SigningHitProof.ForestExceptionAt prims x) gate (topGate_injective x T) t s ε
      (fun b hb' he => by subst he; exact hgate b s (hs hb.1) hb')
    refine (ENNReal.tsum_le_tsum fun r => ?_).trans (h1.trans ?_)
    · gcongr
      unfold guarded
      split_ifs
      · exact zero_le
      · exact le_rfl
    · split_ifs <;> simp only [mul_one, mul_zero] <;> exact le_rfl
  have hG := XmssSecurity.expectedFinal_le (loggedImpl prims) hinv (guarded G)
    (fun t s => ε * (if ∃ b, t = gate b ∧ ¬SigningHitProof.GateSeen (gate b) s.2 then 1 else 0))
    hstep prog loggedInit (fun _ => .initial)
  rw [XmssSecurity.expectedSimulatedCost_const_mul] at hG
  have hcost := unseenGate_cost_le prims gate (topGate_injective x T) prog loggedInit
  have hG0 : guarded G loggedInit = 0 := by
    rw [guarded, if_neg (by simp [loggedInit, Programmed])]
    exact Finset.sum_eq_zero fun b _ =>
      if_neg (by simp [SigningHitProof.GateSeen, loggedInit])
  have hc := SigningOwnPotential.logged_block_potential_le prims (SigningHitProof.forestRelevant x.1)
    (SigningHitProof.forestRun x) (fun _ record => SigningHitProof.forestTargets x.1 record)
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top)
    loggedInit fun z hz w hw input hrel hread =>
      Or.inl (SigningOwnCover.forestRun_covers_top x _ z hz w hw input hrel hread)
  rw [show (loggedInit (C := C)).1.1 = ∅ from rfl, SigningHitProof.completionPotential_empty] at hc
  have hprog : referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
      x.1 emptyTop .top = prog := by
    rw [show referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
        x.1 emptyTop .top = liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _, ← SigningHitProof.hashEmbed_referenceTree]
  rw [dealerRun, flatWorld, carry_run, OracleComp.tsum_prEvent_map_mul, hprog]
  change ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) prog).run loggedInit}[z = r] *
    guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤ _
  calc _ ≤ ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) prog).run loggedInit}[z = r] *
        (SigningHitProof.completionPotential (SigningHitProof.forestRelevant x.1)
          (SigningHitProof.forestCompletion x) r.2.1.1 + guarded G r.2) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        gcongr
        simp only [guarded, SigningGuessProof.structuralHitPotential, G, gate]
        split_ifs <;> simp
    _ = _ + XmssSecurity.expectedFinal (loggedImpl prims) (guarded G) prog loggedInit := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
        rfl
    _ ≤ 0 + ε * (Fintype.card XmssSecurity.TopIndex : ℝ≥0∞) := by
        refine add_le_add hc (hG.trans ?_)
        rw [hG0, zero_add]
        gcongr
        refine (XmssSecurity.expectedSimulatedCost_mono _ (fun t s => ?_) prog loggedInit).trans hcost
        split_ifs <;> exact le_rfl
    _ = _ := by
        rw [zero_add, Fintype.card_fin]
        rfl

/-- One query of the forger raises the hit potential by its own structural call only. A build, a
part and a round-2 check add nothing. -/
theorem hit_step_rise (A : TsigAdversary C) (x : Keys3 C) (T : C.Term) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C) (hp : HitInv prims x T top p.1) :
    ∑' r, Pr{let z ← (flatOracles prims x (SigningHitProof.actualDealt x top) t).run p}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2.1 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) p.1 +
        (2 ^ 128 : ℝ≥0∞)⁻¹ * (ownDomainUnit (SigningHitProof.forestRelevant x.1) t : ℝ≥0∞) := by
  rw [flatOracles, flat, StateT.run_mk, OracleComp.tsum_prEvent_map_mul, carry_run_pair, OracleComp.tsum_prEvent_map_mul]
  cases t with
  | inl t =>
    simp only [flaggedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, OracleComp.tsum_prEvent_map_mul]
    erw [adversary_query, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    erw [id_map]
    refine (hit_seen_step prims A x T (.inl (.inl t)) p.1 hp.2.1).trans_eq ?_
    rcases t with n | (q | q) <;> rfl
  | inr q =>
    simp only [flaggedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, OracleComp.tsum_prEvent_map_mul]
    rw [SigningHitProof.tsigOracles_free]
    refine (honestFlat_tsigOracles prims A x T top q p.2.1 p.1 ⟨hp.2.1, hp.2.2⟩).trans ?_
    simp [ownDomainUnit]

/-- The finish raises the hit potential by the `382` structural calls of the verification. The
second build of the tail adds nothing. -/
theorem hit_finish_rise (A : TsigAdversary C) (x : Keys3 C) (T : C.Term) (top : TopTree)
    (forgery : Forgery) (st : TsigState C) (s : LoggedState C) (hs : HitInv prims x T top s) :
    ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
          (tsigFinish (SigningHitProof.actualDealt x top) (forgery, st))).run s)}[z = r] *
        guarded (SigningGuessProof.structuralHitPotential prims A x T) r.2 ≤
      guarded (SigningGuessProof.structuralHitPotential prims A x T) s +
        (2 ^ 128 : ℝ≥0∞)⁻¹ * ((382 : ℕ) : ℝ≥0∞) := by
  have hinv : RunInv x T top s := ⟨hs.2.1, hs.2.2⟩
  unfold SigningCoreProof.tsigFinish
  dsimp only
  have hverify := hit_run_bound prims A x T
    (liftFree (tweakable (Verification.verifyWithHash ⟨top.root, x.1⟩ forgery.message forgery.signature))) 382
    (liftFree_bound x _ 382 (by
      rw [← SigningHitProof.hashEmbed_forestHash]
      exact hashEmbed_bound x _ 382 (forestHash_bound x _ 382 (verify_relevant x _ _ _)))) s hs.2.1
  rw [← add_zero ((2 ^ 128 : ℝ≥0∞)⁻¹ * ((382 : ℕ) : ℝ≥0∞))]
  refine hit_bind_le prims A x T _ _ s _ 0 hverify fun z hz => ?_
  have hz' := runInv_run prims x T top _ s hinv z hz
  split_ifs
  · simp only [pure_bind, simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
    exact le_add_right le_rfl
  · rw [← add_zero (0 : ℝ≥0∞)]
    refine hit_bind_le prims A x T _ _ z.2 0 0 ?_ fun w _ => ?_
    swap
    · simp only [pure_bind, simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
      exact le_add_right le_rfl
    have hsig := honestFlat_honestSignature prims A x T top forgery.signature.leafIndex forgery.message
      z.2 hz'
    rw [← SigningCacheProof.liftFree_honestSignature] at hsig
    exact hsig.trans (le_add_right le_rfl)

end ThresholdLeanXmssSecurity.SigningOwnHit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.gatedContinuation_sum_step_unseen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.gatedContinuation_sum_step_unseen

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.unseenGate_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.unseenGate_cost_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.loggedImpl_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.loggedImpl_cache_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.allSeen_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.allSeen_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.runInv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.runInv_run

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.programmed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.programmed_run

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.topGate_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.topGate_injective

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.gateSum_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.gateSum_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.gateSum_run_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.gateSum_run_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_seen_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_seen_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_run_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_run_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.rawDomainCost_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.rawDomainCost_le_one

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_run_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_block_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_block_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_replay_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_replay_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.liftFree_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.liftFree_query_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.liftFree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.liftFree_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_of_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_map

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.forestRelevant_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.forestRelevant_hash

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.message_not_forestRelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.message_not_forestRelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.mapM_bound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.mapM_bound_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.sequenceFin_bound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.sequenceFin_bound_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hashEmbed_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hashEmbed_query_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hashEmbed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hashEmbed_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.tweakable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.tweakable_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.prfValue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.prfValue_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.eval_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.eval_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.grind_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.grind_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.signCodeword_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.signCodeword_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_bottomOnce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_bottomOnce

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.signRound2With_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.signRound2With_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_tsigOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_tsigOracles

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.resolves_bottom_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.resolves_bottom_root

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.xor_one_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.xor_one_div_two

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.resolves_bottomPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.resolves_bottomPath

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.bound_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.bound_bind_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.bound_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.bound_of_calls

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.layerRoot_relevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.layerRoot_relevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.verify_relevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.verify_relevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.forestHash_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.forestHash_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.logged_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.logged_cache_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.logged_hashEmbed_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.logged_hashEmbed_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlatAfter_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlatAfter_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlatAfter_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlatAfter_of

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlatAfter_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlatAfter_replay

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_honestSignature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.honestFlat_honestSignature

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_bind_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_dealer_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_dealer_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_step_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_step_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnHit.hit_finish_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnHit.hit_finish_rise
