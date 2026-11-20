import ThresholdLeanXmssSecurity.Proof.SigningOwnHit
import ThresholdLeanXmssSecurity.Proof.SigningOwnTop

/-!
# The top partner bound for a forger with an own budget

- `TopOwn` bounds a resolved top partner by the own top digest calls of the forger and one unit for
  the top digest call of the verification.
- `top_dealer_rise`, `top_step_rise` and `top_finish_rise` are the three rises of the guarded top
  partner potential. A build is one block that the canonical top search of each key covers
  (`canonicalTopGrind_covers_bottom`). The other honest calls make no top digest call.
- `topOwn` applies `flat_potential_le` to these rises.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnTopBound

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitLaneProof SigningCostProof SigningFlatProof SigningOwnForger
open SigningOwnCommit SigningSelectionProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)
attribute [local irreducible] MonadAttach.support

/-- The top partner bound with the own budget. One unit pays the top digest call of the
verification. -/
def TopOwn : Prop :=
  ∀ (A : TsigAdversary C) (x : Keys3 C),
    Pr{let r ←
        SigningDescentProof.exposedRun prims A x}[∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (forgerCost prims A x
        (ownDomainUnit (SigningGuessProof.anyTopDigestInput x.1)) + (1 : ℕ))

section Calculus

variable (x : Keys3 C)

/-- The top partner potential, guarded by the programming flag. -/
abbrev topPotential : LoggedState C → ℝ≥0∞ :=
  guarded fun s => SigningGuessProof.topPartnerPotential x s.1.1

/-- One call raises the guarded top partner potential by its top digest cost. -/
theorem top_step (t : (WorldSpec C).Domain) (s : LoggedState C) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * topPotential x r.2 ≤
      topPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ *
        (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t : ℝ≥0∞) := by
  refine SigningGuessProof.guarded_domain_step prims (fun _ => True)
    (fun s => SigningGuessProof.topPartnerPotential x s.1.1)
    (fun t => (2 ^ 128 : ℝ≥0∞)⁻¹ *
      (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t : ℝ≥0∞))
    (fun t s _ _ ht => ?_) t s (fun _ => trivial)
  simpa only [mul_comm] using SigningGuessProof.cachePotential_domain_step prims
    (SigningGuessProof.anyTopDigestInput x.1) (SigningGuessProof.topPartnerPotential x)
    (fun input cache => by convert SigningGuessProof.topPartnerPotential_step x input cache using 1) t s ht

/-- A program raises the guarded top partner potential by its expected top digest cost. -/
theorem top_run_le {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] * topPotential x r.2 ≤
      topPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ * XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t : ℝ≥0∞))
        oa s := by
  have h := XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) _ _ (fun t s _ => top_step prims x t s) oa s trivial
  rwa [XmssSecurity.expectedSimulatedCost_const_mul] at h

/-- A program with at most `n` top digest calls raises the guarded top partner potential by at most
`n` units. -/
theorem top_run_bound {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (hb : oa.IsQueryBoundP
      (fun t => SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t ≠ 0) n)
    (s : LoggedState C) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] * topPotential x r.2 ≤
      topPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞) := by
  refine (top_run_le prims x oa s).trans (add_le_add le_rfl ?_)
  gcongr
  refine (XmssSecurity.expectedSimulatedCost_mono _ (right := fun t _ =>
    if SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t ≠ 0 then 1 else 0)
    (fun t _ => ?_) _ _).trans ?_
  · have h := SigningOwnHit.rawDomainCost_le_one (SigningGuessProof.anyTopDigestInput x.1) t
    split_ifs with hne
    · exact_mod_cast h
    · simp only [ne_eq, not_not] at hne
      simp [hne]
  · rw [XmssSecurity.expectedSimulatedCost_indicator]
    exact XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ _ n _ hb

/-- A block of honest hash calls does not raise the guarded top partner potential, if for each key
the canonical top search covers its top digest reads. -/
theorem top_block_le {β : Type} (block : OracleComp (Query C →ₒ HashOutput) β) (s : LoggedState C)
    (hcovered : ∀ key, ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningHitProof.recordReads (SigningGuessProof.canonicalTopGrind x key) ∅)).run s.1.1),
      ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningHitProof.recordReads block ∅)).run z.2),
      ∀ input, SigningGuessProof.topDigestInput x.1 key input → (w.1.2 input).isSome →
        (z.1.2 input).isSome ∨ (s.1.1 input).isSome) :
    ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (liftFree (SigningHitProof.hashEmbed block))).run s)}[z = r] * topPotential x r.2 ≤
      topPotential x s := by
  by_cases hp : Programmed s.2
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun r => ?_) zero_le
    by_cases hr : r ∈ support ((simulateQ (loggedImpl prims)
      (liftFree (SigningHitProof.hashEmbed block))).run s)
    · simp [guarded, SigningOwnHit.programmed_run prims _ s hp r hr]
    · simp [prEvent_eq_zero_of_not_mem_support _ hr]
  rw [topPotential, guarded, if_neg hp]
  calc _ ≤ ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (liftFree (SigningHitProof.hashEmbed block))).run s)}[z = r] *
          SigningGuessProof.topPartnerPotential x r.2.1.1 := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        gcongr
        unfold guarded
        split_ifs <;> simp
    _ = ∑ key : XmssSecurity.TopIndex, ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
        (liftFree (SigningHitProof.hashEmbed block))).run s)}[z = r] *
          SigningHitProof.completionPotential (SigningGuessProof.topDigestInput x.1 key)
            (SigningGuessProof.canonicalTopCompletion x key) r.2.1.1 := by
        simp only [SigningGuessProof.topPartnerPotential, Finset.mul_sum]
        exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ _ := Finset.sum_le_sum fun key _ => SigningOwnPotential.logged_block_potential_le prims
        (SigningGuessProof.topDigestInput x.1 key) (SigningGuessProof.canonicalTopGrind x key)
        (SigningGuessProof.topGrindTargets x.1 key) block s (hcovered key)

theorem top_bind_le {α β : Type} (oa : OracleComp (WorldSpec C) α) (ob : α → OracleComp (WorldSpec C) β)
    (s : LoggedState C) (a b : ℝ≥0∞)
    (h1 : ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] * topPotential x r.2 ≤
      topPotential x s + a)
    (h2 : ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s),
      ∑' r, Pr{let y ← (simulateQ (loggedImpl prims) (ob z.1)).run z.2}[y = r] * topPotential x r.2 ≤
        topPotential x z.2 + b) :
    ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) (oa >>= ob)).run s}[z = r] * topPotential x r.2 ≤
      topPotential x s + (a + b) := by
  rw [simulateQ_bind, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' z, Pr{let y ← (simulateQ (loggedImpl prims) oa).run s}[y = z] * (topPotential x z.2 + b) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run s)
        · gcongr
          exact h2 z hz
        · simp [prEvent_eq_zero_of_not_mem_support _ hz]
    _ ≤ (topPotential x s + a) + 1 * b := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        exact add_le_add h1 (mul_le_mul_left (OracleComp.tsum_prEvent_le_one _) _)
    _ = _ := by rw [one_mul, add_assoc]

/-- A call of the honest operators on `H` that the top digest cost charges. -/
def TopRelevant : (RoSpec C).Domain → Prop
  | .inl q => SigningGuessProof.anyTopDigestInput x.1 q
  | .inr _ => False

/-- The free copy of an honest program has as many top digest calls as the program. -/
theorem liftFree_top_bound {α : Type} (R : OracleComp (RoSpec C) α) (n : ℕ)
    (h : R.IsQueryBoundP (TopRelevant x) n) :
    (liftFree R).IsQueryBoundP
      (fun t => SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t ≠ 0) n := by
  induction R using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [SigningOwnHit.liftFree_query_bind, isQueryBoundP_query_bind_iff]
    have hiff : SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1)
        (.inr (.inr t) : (WorldSpec C).Domain) ≠ 0 ↔ TopRelevant x t := by
      rcases t with q | p
      · simp [SigningGuessProof.rawDomainCost, TopRelevant]
      · have hn : ¬SigningGuessProof.anyTopDigestInput (C := C) x.1 (.streamKey p.2.1) := by
          rintro ⟨_, _, h⟩
          cases h
        simp [SigningGuessProof.rawDomainCost, TopRelevant, hn]
    simp only [hiff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem hashEmbed_top_bound {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) (n : ℕ)
    (h : oa.IsQueryBoundP (SigningGuessProof.anyTopDigestInput x.1) n) :
    (SigningHitProof.hashEmbed oa).IsQueryBoundP (TopRelevant x) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [SigningOwnHit.hashEmbed_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem forestHash_top_bound {α : Type} (oa : OracleComp HashSpec α) (n : ℕ)
    (h : oa.IsQueryBoundP (fun input => SigningGuessProof.anyTopDigestInput (C := C) x.1 (.hash input)) n) :
    (SigningHitProof.forestHash (C := C) oa).IsQueryBoundP (SigningGuessProof.anyTopDigestInput x.1) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [SigningHitProof.forestHash, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- A hash computation with at most `n` top digest calls keeps this bound as an honest program on
`H`. -/
theorem tweakable_top_bound {α : Type} (oa : OracleComp HashSpec α) (n : ℕ)
    (h : oa.IsQueryBoundP (fun input => SigningGuessProof.anyTopDigestInput (C := C) x.1 (.hash input)) n) :
    (tweakable oa : OracleComp (RoSpec C) α).IsQueryBoundP (TopRelevant x) n := by
  rw [← SigningHitProof.hashEmbed_forestHash]
  exact hashEmbed_top_bound x _ n (forestHash_top_bound x oa n h)

/-- A top digest input is at the top digest address of its key. -/
theorem anyTop_address {P : PublicParameter} {input : HashInput}
    (h : SigningGuessProof.anyTopDigestInput (C := C) P (.hash input)) :
    ∃ key, XmssSecurity.AtHashAddress P (.topEncoding key) input := by
  obtain ⟨key, payload, he⟩ := h
  rw [Query.hash.inj he]
  exact ⟨key, (XmssSecurity.atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl⟩

/-- No structural tweakable input is a top digest input. -/
theorem structural_not_anyTop (P : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hd : ∀ lay e, domain ≠ .message lay e) :
    ¬(fun input => SigningGuessProof.anyTopDigestInput (C := C) P (.hash input))
      (tweakableHashInput P domain payload) := fun h => by
  obtain ⟨key, hk⟩ := anyTop_address h
  exact SigningOwnTop.structural_not_topDigest P key domain payload hd hk

/-- The message digest of the bottom layer is not a top digest call. -/
theorem bottomDigest_noCall (P : PublicParameter) (e : KeyIndex) (message : Message)
    (randomness : Randomizer) :
    NoCall (fun input => SigningGuessProof.anyTopDigestInput (C := C) P (.hash input))
      (Verification.messageDigestWithHash P bottomLayer e (littleEndianBytes 32 message) randomness :
        OracleComp HashSpec Digest) := by
  unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash
  refine noCall_bind _ (noCall_query _ _ ?_) fun _ => noCall_pure _ _
  rintro ⟨key, payload, he⟩
  replace he := (congrArg (Query.hash (C := C)) (XmssSecurity.Bridge.message_input P e message randomness)).symm.trans he
  cases XmssSecurity.domain_eq_of_tweakableHashInput_eq P (Query.hash.inj he)

/-- The search of the bottom layer makes no top digest call. -/
theorem grind_bottom_noCall (P : PublicParameter) (e : KeyIndex) (message : Message) (base : Randomizer)
    (attempts trial : ℕ) :
    NoCall (fun input => SigningGuessProof.anyTopDigestInput (C := C) P (.hash input))
      (grind P bottomLayer e (littleEndianBytes 32 message) base attempts trial) :=
  grind_noCall P _ bottomLayer e _ base (fun r => bottomDigest_noCall P e message r) attempts trial

theorem prfValue_top_bound (seeds : C.Term → HashOutput) (pt : Point) :
    (prfValue seeds pt).IsQueryBoundP (TopRelevant x) 0 := by
  unfold prfValue
  refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.mapM_bound_zero _ _ _ fun T => ?_)
    fun _ _ => isQueryBoundP_pure _ _ _
  simp only [prf, hashQuery, isQueryBoundP_map_iff]
  refine (isQueryBoundP_query_iff _ _ _).2 fun h => ?_
  obtain ⟨_, _, he⟩ := h
  cases he

theorem eval_top_bound (keys : Keys C) (i : C.Party) (J : C.Quorum) (pt : Point) (message : Message) :
    (eval keys i J pt message).IsQueryBoundP (TopRelevant x) 0 := by
  unfold eval
  refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.mapM_bound_zero _ _ _ fun T => ?_)
    fun _ _ => isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.mapM_bound_zero _ _ _ fun j => ?_)
      fun _ _ => isQueryBoundP_pure _ _ _
  · simp only [prf, hashQuery, isQueryBoundP_map_iff]
    refine (isQueryBoundP_query_iff _ _ _).2 fun h => ?_
    obtain ⟨_, _, he⟩ := h
    cases he
  · simp only [hashQuery, isQueryBoundP_map_iff]
    refine (isQueryBoundP_query_iff _ _ _).2 fun h => ?_
    obtain ⟨_, _, he⟩ := h
    cases he

/-- A commitment input is not a top digest input. -/
theorem commitment_not_anyTop (P : PublicParameter) (e : KeyIndex) (ρ : Digest) :
    ¬SigningGuessProof.anyTopDigestInput (C := C) P (.hash (commitmentInput P e ρ)) := by
  rintro ⟨key, ⟨root, randomness⟩, he⟩
  have ht := XmssSecurity.Bridge.topMessage_input P key root randomness
  have he' : commitmentInput P e ρ = tweakableHashInput P (.message topLayer (XmssSecurity.Bridge.topKey key))
      (littleEndianBytes 16 root ++ littleEndianBytes 16 randomness) := (Query.hash.inj he).trans ht.symm
  exact SigningGuessProof.commitmentInput_ne_tweakableHashInput P P e ρ _ _ he'

theorem signCodeword_top_bound (commitment : Digest) (e : KeyIndex) (message : Message) (ρ : Digest) :
    (signCodeword x.1 commitment e message ρ).IsQueryBoundP (TopRelevant x) 0 := by
  unfold signCodeword
  refine tweakable_top_bound x _ 0 ((noCall_iff _ _).1 ?_)
  unfold Verification.oracleHashWithHash
  refine noCall_bind _ (noCall_query _ _ (commitment_not_anyTop x.1 e ρ)) fun _ => ?_
  simp only []
  split_ifs
  · exact noCall_pure _ _
  · refine noCall_bind _ (noCall_query _ _ fun h => ?_) fun _ => grind_bottom_noCall x.1 e message _ _ _
    obtain ⟨key, hk⟩ := anyTop_address h
    exact SigningOwnTop.randomizer_not_topDigest x.1 key _ _ _ _ hk

theorem signRound2With_top_bound (part : Point → OracleComp (RoSpec C) Digest)
    (hpart : ∀ pt, (part pt).IsQueryBoundP (TopRelevant x) 0) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    (signRound2With (fun oa => oa) part x.1 J commitment e message parts).IsQueryBoundP
      (TopRelevant x) 0 := by
  unfold signRound2With
  refine isQueryBoundP_bind (n := 0) (m := 0) (signCodeword_top_bound x _ _ _ _) fun r _ => ?_
  rcases r with _ | ⟨_, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.sequenceFin_bound_zero _ _ fun l => ?_)
      fun _ _ => isQueryBoundP_pure _ _ _
    split_ifs
    · simpa using hpart _
    · exact isQueryBoundP_pure _ _ _

/-- One layer of the verification makes at most one top digest call. -/
theorem layerRoot_top_bound (lay : Layer) (key : KeyIndex) (message : HashInput) (part : LayerSignature) :
    (Verification.layerRootWithHash x.1 lay key message part : OracleComp HashSpec (Option Digest)).IsQueryBoundP
      (fun input => SigningGuessProof.anyTopDigestInput (C := C) x.1 (.hash input)) 1 := by
  have hs := structural_not_anyTop (C := C) x.1
  unfold Verification.layerRootWithHash Verification.otsLeafWithHash
  refine SigningOwnHit.bound_bind_le (a := 1) (b := 0) (SigningOwnHit.bound_bind_le (a := 1) (b := 0)
    (SigningOwnHit.bound_of_calls (SigningOwnVerify.calls_tweakableHash _ _ _) _) (fun digest => ?_) le_rfl)
    (fun leaf => ?_) le_rfl
  · rw [← noCall_iff]
    split
    · refine noCall_bind _ (noCall_sequenceFin _ _ fun _ => ?_) fun _ => ?_
      · unfold Verification.recoverChainWithHash; exact chainWalk_noCall x.1 _ hs _ _ _ _ _ _
      · exact noCall_map _ _ (tweakableHash_noCall x.1 _ hs _ _ (fun _ _ h => by cases h))
    · exact noCall_pure _ _
  · rw [← noCall_iff]
    rcases leaf with _ | leaf
    · exact noCall_pure _ _
    · exact noCall_bind _ (treeFold_noCall x.1 _ hs _ _ _ _ _) fun _ => noCall_pure _ _

/-- The verification makes at most one top digest call. -/
theorem verify_top_bound (root : Digest) (message : Message) (signature : Signature) :
    (Verification.verifyWithHash ⟨root, x.1⟩ message signature : OracleComp HashSpec Bool).IsQueryBoundP
      (fun input => SigningGuessProof.anyTopDigestInput (C := C) x.1 (.hash input)) 1 := by
  have hs := structural_not_anyTop (C := C) x.1
  unfold Verification.verifyWithHash
  refine SigningOwnHit.bound_bind_le (a := 0) (b := 1) ?_ (fun bottomRoot => ?_) le_rfl
  · rw [← noCall_iff]
    exact layerRoot_noCall x.1 _ hs _ _ _ _ (bottomDigest_noCall x.1 _ _ _)
  cases bottomRoot with
  | none => exact isQueryBoundP_pure _ _ _
  | some bottomRoot =>
      refine SigningOwnHit.bound_bind_le (layerRoot_top_bound x _ _ _ _) (b := 0) (fun root => ?_) le_rfl
      cases root <;> exact isQueryBoundP_pure _ _ _

/-- A program with no call at the top digest address of each key makes no top digest call. -/
theorem anyTop_bound_zero {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (h : ∀ key, oa.IsQueryBoundP (SigningGuessProof.topDigestAddress x.1 key) 0) :
    oa.IsQueryBoundP (SigningGuessProof.anyTopDigestInput x.1) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self, Nat.lt_irrefl, or_false] at h ⊢
    refine ⟨fun hq => ?_, fun u => ih u fun key => (h key).2 u⟩
    obtain ⟨key, payload, rfl⟩ := hq
    exact (h key).1 ((XmssSecurity.atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)

set_option maxRecDepth 100000 in
attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- The ceremony of the top tree reads no top digest input. -/
theorem topTree_no_topDigest :
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 emptyTop
      .top).IsQueryBoundP (SigningGuessProof.anyTopDigestInput x.1) 0 := by
  refine anyTop_bound_zero x _ fun key => ?_
  have hs := SigningOwnTop.structural_not_topDigest x.1 key
  unfold referenceTree ceremonyOutput
  refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_map_iff _ _ _).2
    (SigningHitProof.mapM_bound_zero _ _ _ fun job =>
      SigningGuessProof.referenceJob_no_topDigest x key job)) fun outputs _ => ?_
  rcases outputs with _ | outputs
  · exact isQueryBoundP_pure _ _ _
  dsimp only
  exact isQueryBoundP_bind (n := 0) (m := 0) (forestHash_noCall (C := C) _ _
    (merkleNode_noCall x.1 _ hs _ _ _ _)) fun _ _ => isQueryBoundP_pure _ _ _

/-- An honest program that does not raise the guarded top partner potential. -/
def TopFlat {α : Type} (R : OracleComp (RoSpec C) α) : Prop :=
  ∀ s, ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) (liftFree R)).run s}[z = r] * topPotential x r.2 ≤
    topPotential x s

theorem topFlat_bind {α β : Type} {R : OracleComp (RoSpec C) α}
    {f : α → OracleComp (RoSpec C) β} (hR : TopFlat prims x R)
    (hf : ∀ a, TopFlat prims x (f a)) : TopFlat prims x (R >>= f) := by
  intro s
  rw [show ∀ {α β : Type} (R : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β),
    liftFree (R >>= f) = liftFree R >>= fun a => liftFree (f a) from φ_bind, simulateQ_bind,
    StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum fun z => ?_) (hR s)
  gcongr
  exact hf z.1 z.2

theorem topFlat_of_bound {α : Type} (R : OracleComp (RoSpec C) α)
    (h : R.IsQueryBoundP (TopRelevant x) 0) : TopFlat prims x R := fun s => by
  simpa using top_run_bound prims x (liftFree R) 0 (liftFree_top_bound x R 0 h) s

theorem topFlat_pure {α : Type} (a : α) : TopFlat prims x (pure a : OracleComp (RoSpec C) α) :=
  topFlat_of_bound prims x _ (isQueryBoundP_pure _ _ _)

theorem topFlat_map {α β : Type} {R : OracleComp (RoSpec C) α} (g : α → β)
    (hR : TopFlat prims x R) : TopFlat prims x (g <$> R) := by
  rw [map_eq_bind_pure_comp]
  exact topFlat_bind prims x hR fun a => topFlat_pure prims x _

set_option maxRecDepth 100000 in
/-- The build of a bottom tree does not raise the guarded top partner potential. -/
theorem topFlat_bottom (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    TopFlat prims x (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
      (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b))) := fun s =>
  top_block_le prims x _ s fun key z hz w hw input hrel hread =>
    Or.inl (SigningOwnTop.canonicalTopGrind_covers_bottom x top key b s.1.1 z hz w hw input hrel hread)

theorem topFlat_bottomOnce (top : TopTree) (b : Fin (2 ^ layerHeight)) (st : TsigState C) :
    TopFlat prims x ((bottomOnce (SigningOwnHit.honestDealt x top) b).run st) := by
  unfold bottomOnce
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact topFlat_pure prims x _
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    refine topFlat_bind prims x ?_ fun _ => topFlat_of_bound prims x _ (by simp)
    simp only [SigningOwnHit.honestDealt, dealtWith]
    rw [← SigningHitProof.hashEmbed_referenceTree]
    exact topFlat_map prims x _ (topFlat_bottom prims x top b)

set_option backward.isDefEq.respectTransparency false in
/-- A signing oracle does not raise the guarded top partner potential. Its builds are covered by the
canonical top searches, and its other calls are not top digest calls. -/
theorem topFlat_tsigOracles (top : TopTree) (q : (TsigSpec C).Domain) (st : TsigState C) :
    TopFlat prims x ((tsigOracles (fun oa => oa) (SigningOwnHit.honestDealt x top) q).run st) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    apply topFlat_of_bound
    split_ifs <;> simp
  · simp only [tsigOracles, StateT.run_bind]
    refine topFlat_bind prims x (topFlat_bottomOnce prims x top b st) fun p => ?_
    apply topFlat_of_bound
    rcases p with ⟨_ | tree, st'⟩
    · simp
    · simp
      exact prfValue_top_bound x _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    apply topFlat_of_bound
    split_ifs
    · simp
    · simp
      exact eval_top_bound x _ _ _ _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simpa using topFlat_pure prims x _
    · simp only [StateT.run_bind]
      refine topFlat_bind prims x (topFlat_bottomOnce prims x top _ st) fun p => ?_
      apply topFlat_of_bound
      rcases p with ⟨_ | tree, st'⟩
      · simp
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
        simp only [pure_bind]
        refine isQueryBoundP_bind (n := 0) (m := 0) (eval_top_bound x _ _ _ _ _) fun own _ => ?_
        refine isQueryBoundP_bind (n := 0) (m := 0)
          (signRound2With_top_bound x _ (fun pt => eval_top_bound x _ _ _ _ _) _ _ _ _ _) fun r _ => ?_
        rcases r with _ | values <;> simp

/-- The honest signature does not raise the guarded top partner potential. Its build is covered by
the canonical top searches, and its other calls are not top digest calls. -/
theorem topFlat_honestSignature (top : TopTree) (e : KeyIndex) (message : Message) :
    TopFlat prims x (honestSignature (fun oa => oa) (SigningOwnHit.honestDealt x top) e message) := by
  have hs := structural_not_anyTop (C := C) x.1
  unfold honestSignature
  simp only [SigningOwnHit.honestDealt, dealtWith]
  rw [← SigningHitProof.hashEmbed_referenceTree, map_eq_bind_pure_comp, bind_assoc]
  refine topFlat_bind prims x (topFlat_bottom prims x top (treeOf e)) fun out => ?_
  apply topFlat_of_bound
  rcases out with _ | (top' | tree)
  · simp
  · simp
  simp only [Function.comp_apply, pure_bind]
  refine isQueryBoundP_bind (n := 0) (m := 0) (prfValue_top_bound x _ _) fun ρ _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) (signCodeword_top_bound x _ _ _ _) fun r _ => ?_
  rcases r with _ | ⟨randomness, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.sequenceFin_bound_zero _ _ fun l => ?_)
    fun values _ => ?_
  · split
    · exact prfValue_top_bound x _ _
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_bind (n := 0) (m := 0) (prfValue_top_bound x _ _) fun _ _ =>
        isQueryBoundP_pure _ _ _
  refine isQueryBoundP_bind (n := 0) (m := 0) (tweakable_top_bound x _ 0 ((noCall_iff _ _).1
    (merklePath_noCall x.1 _ hs _ _ _))) fun _ _ => isQueryBoundP_pure _ _ _

end Calculus

set_option maxRecDepth 100000 in
/-- The dealer does not raise the top partner potential. The ceremony of the top tree makes no
top digest call. -/
theorem top_dealer_rise (x : Keys3 C) :
    ∑' r, Pr{let z ← dealerRun prims x}[z = r] * topPotential x r.2.1 ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞) := by
  let prog := liftFree (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
    (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top))
  have hprog : referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
      x.1 emptyTop .top = prog := by
    rw [show referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
        x.1 emptyTop .top = liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _, ← SigningHitProof.hashEmbed_referenceTree]
  rw [dealerRun, flatWorld, carry_run, OracleComp.tsum_prEvent_map_mul, hprog]
  have h := top_run_bound prims x prog 0
    (liftFree_top_bound x _ 0 (hashEmbed_top_bound x _ 0 (topTree_no_topDigest x))) loggedInit
  have h0 : topPotential x (loggedInit (C := C)) = 0 := by
    simp [topPotential, guarded, loggedInit, Programmed, SigningGuessProof.topPartnerPotential_zero]
  rw [h0, zero_add] at h
  exact h

/-- One query of the forger raises the top partner potential by its own top digest call only. A
build, a part and a round-2 check add nothing. -/
theorem top_step_rise (x : Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C) :
    ∑' r, Pr{let z ← (flatOracles prims x (SigningHitProof.actualDealt x top) t).run p}[z = r] *
        topPotential x r.2.1 ≤
      topPotential x p.1 +
        (2 ^ 128 : ℝ≥0∞)⁻¹ * (ownDomainUnit (SigningGuessProof.anyTopDigestInput x.1) t : ℝ≥0∞) := by
  rw [flatOracles, flat, StateT.run_mk, OracleComp.tsum_prEvent_map_mul, carry_run_pair, OracleComp.tsum_prEvent_map_mul]
  cases t with
  | inl t =>
    simp only [flaggedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, OracleComp.tsum_prEvent_map_mul]
    erw [adversary_query, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    erw [id_map]
    refine (top_step prims x (.inl (.inl t)) p.1).trans_eq ?_
    rcases t with n | (q | q) <;> rfl
  | inr q =>
    simp only [flaggedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, OracleComp.tsum_prEvent_map_mul]
    rw [SigningHitProof.tsigOracles_free]
    refine (topFlat_tsigOracles prims x top q p.2.1 p.1).trans ?_
    simp [ownDomainUnit]

/-- The finish raises the top partner potential by the one top digest call of the verification. The
second build of the tail adds nothing. -/
theorem top_finish_rise (x : Keys3 C) (top : TopTree) (forgery : Forgery) (st : TsigState C)
    (s : LoggedState C) :
    ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
          (tsigFinish (SigningHitProof.actualDealt x top) (forgery, st))).run s)}[z = r] *
        topPotential x r.2 ≤
      topPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((1 : ℕ) : ℝ≥0∞) := by
  unfold SigningCoreProof.tsigFinish
  dsimp only
  have hverify := top_run_bound prims x
    (liftFree (tweakable (Verification.verifyWithHash ⟨top.root, x.1⟩ forgery.message forgery.signature))) 1
    (liftFree_top_bound x _ 1 (tweakable_top_bound x _ 1 (verify_top_bound x _ _ _))) s
  rw [← add_zero ((2 ^ 128 : ℝ≥0∞)⁻¹ * ((1 : ℕ) : ℝ≥0∞))]
  refine top_bind_le prims x _ _ s _ 0 hverify fun z hz => ?_
  split_ifs
  · simp only [pure_bind, simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
    exact le_add_right le_rfl
  · rw [← add_zero (0 : ℝ≥0∞)]
    refine top_bind_le prims x _ _ z.2 0 0 ?_ fun w _ => ?_
    swap
    · simp only [pure_bind, simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
      exact le_add_right le_rfl
    have hsig := topFlat_honestSignature prims x top forgery.signature.leafIndex forgery.message z.2
    rw [← SigningCacheProof.liftFree_honestSignature] at hsig
    exact hsig.trans (le_add_right le_rfl)

set_option maxRecDepth 100000 in
/-- The top partner bound with the own budget, from the frame `flat_potential_le` and the three
rises `top_dealer_rise`, `top_step_rise` and `top_finish_rise`. -/
theorem topOwn : TopOwn prims (C := C) := by
  intro A x
  have hf := flat_potential_le prims A x (topPotential x) (fun _ _ => True)
    (ownDomainUnit (SigningGuessProof.anyTopDigestInput x.1)) 0 1
    (top_dealer_rise prims x) (fun _ _ _ _ => trivial)
    (fun top t p _ => top_step_rise prims x top t p) (fun _ _ _ _ _ _ => trivial)
    (fun top forgery st s _ => top_finish_rise prims x top forgery st s)
  refine le_trans ?_ (hf.trans_eq (by norm_num))
  rw [← loggedRun_forget, prEvent_map, OracleComp.prEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support (loggedRun prims A x)
  · by_cases hw : ∃ key, SigningGuessProof.ResolvedTopPartner x key z.2.1.1
    · simp only [hw, if_true, topPotential, guarded,
        if_neg (noProgramQuery prims C A x z hz)]
      simpa only [mul_one] using mul_le_mul_right
        (SigningGuessProof.topPartnerPotential_terminal x z.2.1.1 hw) (Pr{let y ← loggedRun prims A x}[y = z])
    · simp [hw]
  · simp [prEvent_eq_zero_of_not_mem_support _ hz]

end ThresholdLeanXmssSecurity.SigningOwnTopBound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_run_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_run_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_run_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_block_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_block_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_bind_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.liftFree_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.liftFree_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.hashEmbed_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.hashEmbed_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.forestHash_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.forestHash_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.tweakable_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.tweakable_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.anyTop_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.anyTop_address

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.structural_not_anyTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.structural_not_anyTop

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.bottomDigest_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.bottomDigest_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.grind_bottom_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.grind_bottom_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.prfValue_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.prfValue_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.eval_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.eval_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.commitment_not_anyTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.commitment_not_anyTop

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.signCodeword_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.signCodeword_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.signRound2With_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.signRound2With_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.layerRoot_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.layerRoot_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.verify_top_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.verify_top_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.anyTop_bound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.anyTop_bound_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topTree_no_topDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topTree_no_topDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_of_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_map

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_bottomOnce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_bottomOnce

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_tsigOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_tsigOracles

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_honestSignature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topFlat_honestSignature

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_dealer_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_dealer_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_step_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_step_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.top_finish_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.top_finish_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTopBound.topOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTopBound.topOwn
