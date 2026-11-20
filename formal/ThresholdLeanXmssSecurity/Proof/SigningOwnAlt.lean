import ThresholdLeanXmssSecurity.Proof.SigningOwnHit
import ThresholdLeanXmssSecurity.Proof.SigningOwnCommit

/-!
# The bound of a second opening of a commitment for a forger with an own budget

- `AltOwn` bounds a second opening of a commitment by the own commitment calls of the forger and one
  unit for each round-2 request.
- The commitment potential does not rise over the dealer (`alt_dealer_rise`). One query of the
  forger raises it by its own commitment call, and a round-2 request by the one check of `c_e`
  (`alt_step_rise`). The finish does not raise it (`alt_finish_rise`).
- A build of a bottom tree is a block that the commitment completion covers. The check of `c_e` in
  the tail repeats the commitment call of the build. `resolves_rawCommitment` states that a resolved
  bottom tree resolves the canonical commitment of each of its keys.
- `altOwn` applies `flat_potential_le` with the three rises.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnAlt

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitLaneProof SigningCostProof SigningFlatProof SigningOwnForger

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)
attribute [local irreducible] MonadAttach.support

/-- The bound of a second opening of a commitment with the own budget. A round-2 request pays one
unit, the check of `c_e`. The verification makes no commitment call. -/
def AltOwn : Prop :=
  ∀ (A : TsigAdversary C) (x : Keys3 C),
    Pr{let r ←
        SigningDescentProof.exposedRun prims A x}[SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * forgerCost prims A x
        (fun t => ownDomainUnit (SigningGuessProof.RawCommitmentInput x.1) t + round2Unit t)

section Calculus

variable (x : Keys3 C)

/-- The guarded commitment potential. -/
abbrev altPotential : LoggedState C → ℝ≥0∞ :=
  guarded fun s => SigningHitProof.completionPotential (SigningGuessProof.RawCommitmentInput x.1)
    (SigningGuessProof.commitmentCompletion x.2.1 x.1) s.1.1

/-- A program raises the commitment potential by at most `n` units from `s`. -/
def AltLe {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ) (s : LoggedState C) : Prop :=
  ∑' r, Pr{let z ← (simulateQ (loggedImpl prims) oa).run s}[z = r] * altPotential x r.2 ≤
    altPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)

/-- One call raises the commitment potential by its commitment cost. -/
theorem alt_step (t : (WorldSpec C).Domain) (s : LoggedState C) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * altPotential x r.2 ≤
      altPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ *
        (SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1) t : ℝ≥0∞) := by
  refine SigningGuessProof.guarded_domain_step prims (fun _ => True)
    (fun s => SigningHitProof.completionPotential (SigningGuessProof.RawCommitmentInput x.1)
      (SigningGuessProof.commitmentCompletion x.2.1 x.1) s.1.1)
    (fun t => (2 ^ 128 : ℝ≥0∞)⁻¹ *
      (SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1) t : ℝ≥0∞))
    (fun t s _ _ ht => ?_) t s (fun _ => trivial)
  simpa only [mul_comm] using SigningGuessProof.cachePotential_domain_step prims
    (SigningGuessProof.RawCommitmentInput x.1)
    (SigningHitProof.completionPotential (SigningGuessProof.RawCommitmentInput x.1)
      (SigningGuessProof.commitmentCompletion x.2.1 x.1))
    (SigningHitProof.completionPotential_randomOracle_step _ _
      (SigningHitProof.recordedCompletion_reads _ _ _)) t s ht

/-- A program with at most `n` commitment calls raises the commitment potential by at most `n`
units. -/
theorem alt_run_bound {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (hb : oa.IsQueryBoundP
      (fun t => SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1) t ≠ 0) n)
    (s : LoggedState C) : AltLe prims x oa n s := by
  have h := XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) _ _ (fun t s _ => alt_step prims x t s) oa s trivial
  rw [XmssSecurity.expectedSimulatedCost_const_mul] at h
  refine h.trans (add_le_add le_rfl ?_)
  gcongr
  refine (XmssSecurity.expectedSimulatedCost_mono _ (right := fun t _ =>
    if SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1) t ≠ 0 then 1 else 0)
    (fun t _ => ?_) _ _).trans ?_
  · have h := SigningOwnHit.rawDomainCost_le_one (SigningGuessProof.RawCommitmentInput x.1) t
    split_ifs with hne
    · exact_mod_cast h
    · simp only [ne_eq, not_not] at hne
      simp [hne]
  · rw [XmssSecurity.expectedSimulatedCost_indicator]
    exact XmssSecurity.expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ _ n _ hb

/-- The rises of a program and of its continuation add. -/
theorem altLe_bind {α β : Type} (oa : OracleComp (WorldSpec C) α) (ob : α → OracleComp (WorldSpec C) β)
    (s : LoggedState C) (a b n : ℕ) (h1 : AltLe prims x oa a s)
    (h2 : ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s), AltLe prims x (ob z.1) b z.2)
    (h : a + b ≤ n) : AltLe prims x (oa >>= ob) n s := by
  unfold AltLe at h1 h2 ⊢
  rw [simulateQ_bind, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' z, Pr{let y ← (simulateQ (loggedImpl prims) oa).run s}[y = z] *
        (altPotential x z.2 + (2 ^ 128 : ℝ≥0∞)⁻¹ * (b : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run s)
        · gcongr
          exact h2 z hz
        · simp [prEvent_eq_zero_of_not_mem_support _ hz]
    _ ≤ (altPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞)) + 1 * ((2 ^ 128 : ℝ≥0∞)⁻¹ * (b : ℝ≥0∞)) := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        exact add_le_add h1 (mul_le_mul_left (OracleComp.tsum_prEvent_le_one _) _)
    _ ≤ _ := by
        rw [one_mul, add_assoc, ← mul_add]
        gcongr
        exact_mod_cast h

/-- A block of honest hash calls that the commitment completion covers does not raise the
commitment potential. -/
theorem altLe_block {β : Type} (block : OracleComp (Query C →ₒ HashOutput) β) (s : LoggedState C)
    (hcovered : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningHitProof.recordReads (SigningGuessProof.rawCommitmentForest x.2.1 x.1) ∅)).run s.1.1),
      ∀ w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningHitProof.recordReads block ∅)).run z.2),
      ∀ input, SigningGuessProof.RawCommitmentInput x.1 input → (w.1.2 input).isSome →
        (z.1.2 input).isSome ∨ (s.1.1 input).isSome) :
    AltLe prims x (liftFree (SigningHitProof.hashEmbed block)) 0 s := by
  rw [AltLe, Nat.cast_zero, mul_zero, add_zero]
  by_cases hp : Programmed s.2
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun r => ?_) zero_le
    by_cases hr : r ∈ support ((simulateQ (loggedImpl prims)
      (liftFree (SigningHitProof.hashEmbed block))).run s)
    · simp [guarded, SigningOwnHit.programmed_run prims _ s hp r hr]
    · simp [prEvent_eq_zero_of_not_mem_support _ hr]
  conv_rhs => rw [altPotential, guarded, if_neg hp]
  have hc := SigningOwnPotential.logged_block_potential_le prims
    (SigningGuessProof.RawCommitmentInput x.1) (SigningGuessProof.rawCommitmentForest x.2.1 x.1)
    (fun _ => SigningGuessProof.commitmentTargets x.2.1 x.1) block s hcovered
  refine le_trans (ENNReal.tsum_le_tsum fun r => ?_) hc
  gcongr
  simp only [altPotential, guarded]
  split_ifs <;> simp [SigningGuessProof.commitmentCompletion]

/-- A program that the cache resolves does not raise the commitment potential. -/
theorem altLe_replay {β : Type} (oa : OracleComp (Query C →ₒ HashOutput) β) (v : β)
    (s : LoggedState C) (hres : DeterministicSigning.Resolves s.1.1 oa v) :
    AltLe prims x (liftFree (SigningHitProof.hashEmbed oa)) 0 s := by
  refine altLe_block prims x oa s fun z hz w hw input _ hread => Or.inr ?_
  have hsz := DeterministicSigning.cache_le_of_run _ _ z hz
  have hzw := DeterministicSigning.cache_le_of_run _ _ w hw
  have hle := SigningOwnCover.recordReads_le_of_resolves oa ∅ z.2 s.1.1 v
    (fun _ _ h => by cases h) hres w hw (hsz.trans hzw)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hread
  simp [hle hu]

/-- A program that the cache resolves to `v` is followed by its continuation at `v`. -/
theorem altLe_resolved_bind {β γ : Type} (oa : OracleComp (Query C →ₒ HashOutput) β) (v : β)
    (f : β → OracleComp (RoSpec C) γ) (n : ℕ) (s : LoggedState C)
    (hres : DeterministicSigning.Resolves s.1.1 oa v)
    (hf : ∀ s' : LoggedState C, s.1.1 ≤ s'.1.1 → AltLe prims x (liftFree (f v)) n s') :
    AltLe prims x (liftFree (SigningHitProof.hashEmbed oa >>= f)) n s := by
  rw [show liftFree (SigningHitProof.hashEmbed oa >>= f) =
    liftFree (SigningHitProof.hashEmbed oa) >>= fun a => liftFree (f a) from φ_bind _ _]
  refine altLe_bind prims x _ _ s 0 n n (altLe_replay prims x oa v s hres) (fun z hz => ?_) (by omega)
  have hcache := SigningOwnHit.logged_cache_le prims _ s z hz
  have hz1 : v = z.1 := (hres.mono hcache).unique (SigningOwnHit.logged_hashEmbed_resolves prims oa s z hz)
  rw [← hz1]
  exact hf z.2 hcache

/-- An honest program raises the commitment potential by at most `n` units from each state. -/
def AltRise {α : Type} (R : OracleComp (RoSpec C) α) (n : ℕ) : Prop :=
  ∀ s, AltLe prims x (liftFree R) n s

theorem altRise_bind {α β : Type} {R : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    {a b n : ℕ} (hR : AltRise prims x R a) (hf : ∀ y, AltRise prims x (f y) b) (h : a + b ≤ n) :
    AltRise prims x (R >>= f) n := fun s => by
  rw [show liftFree (R >>= f) = liftFree R >>= fun a => liftFree (f a) from φ_bind _ _]
  exact altLe_bind prims x _ _ s a b n (hR s) (fun z _ => hf z.1 z.2) h

/-- A call of the honest operators on `H` in the commitment domain. -/
def RoCommit : (RoSpec C).Domain → Prop
  | .inl q => SigningGuessProof.RawCommitmentInput x.1 q
  | .inr _ => False

/-- The free copy of an honest program has as many commitment calls as the program. -/
theorem liftFree_commit_bound {α : Type} (R : OracleComp (RoSpec C) α) (n : ℕ)
    (h : R.IsQueryBoundP (RoCommit x) n) :
    (liftFree R).IsQueryBoundP
      (fun t => SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1) t ≠ 0) n := by
  induction R using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [SigningOwnHit.liftFree_query_bind, isQueryBoundP_query_bind_iff]
    have hiff : SigningGuessProof.rawDomainCost (SigningGuessProof.RawCommitmentInput x.1)
        (.inr (.inr t) : (WorldSpec C).Domain) ≠ 0 ↔ RoCommit x t := by
      rcases t with q | p
      · simp [SigningGuessProof.rawDomainCost, RoCommit]
      · simp [SigningGuessProof.rawDomainCost, RoCommit, SigningGuessProof.RawCommitmentInput]
    simp only [hiff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem altRise_of_bound {α : Type} (R : OracleComp (RoSpec C) α) (n : ℕ)
    (h : R.IsQueryBoundP (RoCommit x) n) : AltRise prims x R n := fun s =>
  alt_run_bound prims x (liftFree R) n (liftFree_commit_bound x R n h) s

theorem hashEmbed_commit_bound {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) (n : ℕ)
    (h : oa.IsQueryBoundP (SigningGuessProof.RawCommitmentInput x.1) n) :
    (SigningHitProof.hashEmbed oa).IsQueryBoundP (RoCommit x) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [SigningOwnHit.hashEmbed_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem tweakable_commit_bound {α : Type} (oa : OracleComp HashSpec α) (n : ℕ)
    (h : oa.IsQueryBoundP (fun input => SigningGuessProof.RawCommitmentInput (C := C) x.1 (.hash input)) n) :
    (tweakable oa : OracleComp (RoSpec C) α).IsQueryBoundP (RoCommit x) n := by
  rw [← SigningHitProof.hashEmbed_forestHash]
  refine hashEmbed_commit_bound x _ n ?_
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [SigningHitProof.forestHash, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem tweakable_noCommit {α : Type} (oa : OracleComp HashSpec α)
    (h : SigningSelectionProof.NoCall
      (fun input => SigningGuessProof.RawCommitmentInput (C := C) x.1 (.hash input)) oa) :
    (tweakable oa : OracleComp (RoSpec C) α).IsQueryBoundP (RoCommit x) 0 :=
  tweakable_commit_bound x oa 0 ((SigningSelectionProof.noCall_iff _ _).1 h)

theorem prfValue_commit (seeds : C.Term → HashOutput) (pt : Point) :
    (prfValue seeds pt).IsQueryBoundP (RoCommit x) 0 := by
  rw [← SigningHitProof.hashEmbed_forestValue]
  exact hashEmbed_commit_bound x _ 0 (SigningOwnCommit.forestValue_noCommitment x.1 seeds pt)

theorem eval_commit (keys : Keys C) (i : C.Party) (J : C.Quorum) (pt : Point) (message : Message) :
    (eval keys i J pt message).IsQueryBoundP (RoCommit x) 0 := by
  unfold eval
  refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.mapM_bound_zero _ _ _ fun T => ?_) fun _ _ =>
    isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.mapM_bound_zero _ _ _ fun j => ?_) fun _ _ =>
      isQueryBoundP_pure _ _ _
  · simp only [prf, hashQuery, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => by
      simp [RoCommit, SigningGuessProof.RawCommitmentInput] at h
  · simp only [hashQuery, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => by
      simp [RoCommit, SigningGuessProof.RawCommitmentInput] at h

/-- `signCodeword` makes one commitment call and then no other. -/
theorem signCodeword_split (commitment : Digest) (e : KeyIndex) (message : Message) (ρ : Digest) :
    ∃ K : HashOutput → OracleComp HashSpec (Option (Randomizer × Encoding)),
      signCodeword (C := C) x.1 commitment e message ρ =
        tweakable (Verification.oracleHashWithHash (commitmentInput x.1 e ρ) : OracleComp HashSpec HashOutput) >>=
          (fun o => tweakable (K o)) ∧
      ∀ o, SigningSelectionProof.NoCall
        (fun input => SigningGuessProof.RawCommitmentInput (C := C) x.1 (.hash input)) (K o) := by
  refine ⟨_, by unfold signCodeword tweakable; exact simulateQ_bind _ _ _, fun o => ?_⟩
  dsimp only
  split_ifs
  · exact SigningSelectionProof.noCall_pure _ _
  · refine SigningSelectionProof.noCall_bind _ (SigningSelectionProof.noCall_query _ _ fun h => ?_) fun _ =>
      SigningOwnCommit.grind_noCall x.1 _ _ _ _ _ (SigningOwnCommit.messageDigest_noCall x.1 _ _ _ _
        fun payload => SigningOwnCommit.not_rawCommitment_tweakable x.1 x.1 _ payload) _ _
    obtain ⟨e', ρ', he⟩ := (SigningOwnCommit.rawCommitmentInput_hash_iff x.1 _).1 h
    exact SigningGuessProof.commitmentInput_ne_randomizerInput x.1 e' _ _ ρ' _ _ he

theorem signCodeword_commit (commitment : Digest) (e : KeyIndex) (message : Message) (ρ : Digest) :
    (signCodeword (C := C) x.1 commitment e message ρ).IsQueryBoundP (RoCommit x) 1 := by
  obtain ⟨K, hK, hKn⟩ := signCodeword_split x commitment e message ρ
  rw [hK]
  refine SigningOwnHit.bound_bind_le (a := 1) (b := 0) (tweakable_commit_bound x _ 1 ?_)
    (fun o => tweakable_noCommit x _ (hKn o)) le_rfl
  unfold Verification.oracleHashWithHash
  exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

theorem signRound2With_commit (part : Point → OracleComp (RoSpec C) Digest)
    (hpart : ∀ pt, (part pt).IsQueryBoundP (RoCommit x) 0) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    (signRound2With (fun oa => oa) part x.1 J commitment e message parts).IsQueryBoundP
      (RoCommit x) 1 := by
  unfold signRound2With
  refine SigningOwnHit.bound_bind_le (a := 1) (b := 0) (signCodeword_commit x _ _ _ _) (fun r => ?_) le_rfl
  rcases r with _ | ⟨_, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.sequenceFin_bound_zero _ _ fun l => ?_)
      fun _ _ => isQueryBoundP_pure _ _ _
    split_ifs
    · simpa using hpart _
    · exact isQueryBoundP_pure _ _ _

set_option maxRecDepth 100000 in
/-- The build of a bottom tree does not raise the commitment potential. -/
theorem altRise_bottom (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    AltRise prims x (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
      (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b))) 0 := fun s =>
  altLe_block prims x _ s fun z hz w hw input hrel hread =>
    Or.inl (SigningOwnCommit.commitmentForest_covers_bottom x top b s.1.1 z hz w hw input hrel hread)

theorem altRise_bottomOnce (top : TopTree) (b : Fin (2 ^ layerHeight)) (st : TsigState C) :
    AltRise prims x ((bottomOnce (SigningOwnHit.honestDealt x top) b).run st) 0 := by
  unfold bottomOnce
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact altRise_of_bound prims x _ 0 (isQueryBoundP_pure _ _ _)
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    refine altRise_bind prims x (a := 0) (b := 0) ?_ (fun _ => altRise_of_bound prims x _ 0 (by simp))
      (by omega)
    simp only [SigningOwnHit.honestDealt, dealtWith]
    rw [← SigningHitProof.hashEmbed_referenceTree, map_eq_bind_pure_comp]
    exact altRise_bind prims x (altRise_bottom prims x top b)
      (fun _ => altRise_of_bound prims x _ 0 (isQueryBoundP_pure _ _ _)) (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- A signing oracle raises the commitment potential by the one check of `c_e` of a round-2
request. Its builds are covered by the commitment completion. -/
theorem altRise_tsigOracles (top : TopTree) (q : (TsigSpec C).Domain) (st : TsigState C) :
    AltRise prims x ((tsigOracles (fun oa => oa) (SigningOwnHit.honestDealt x top) q).run st)
      (round2Unit (C := C) (.inr q)) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    apply altRise_of_bound
    split_ifs <;> simp
  · simp only [tsigOracles, StateT.run_bind]
    refine altRise_bind prims x (b := 0) (altRise_bottomOnce prims x top b st) (fun p => ?_)
      (by simp [round2Unit])
    apply altRise_of_bound
    rcases p with ⟨_ | tree, st'⟩
    · simp
    · simp
      exact prfValue_commit x _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    apply altRise_of_bound
    split_ifs
    · simp
    · simp
      exact eval_commit x _ _ _ _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact altRise_of_bound prims x _ _ (by simp)
    · simp only [StateT.run_bind]
      refine altRise_bind prims x (b := 1) (altRise_bottomOnce prims x top _ st) (fun p => ?_)
        (by simp [round2Unit])
      apply altRise_of_bound
      rcases p with ⟨_ | tree, st'⟩
      · simp
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
        simp only [pure_bind]
        refine SigningOwnHit.bound_bind_le (a := 0) (b := 1) (eval_commit x _ _ _ _ _) (fun own => ?_)
          (by omega)
        refine SigningOwnHit.bound_bind_le (a := 1) (b := 0)
          (signRound2With_commit x _ (fun pt => eval_commit x _ _ _ _ _) _ _ _ _ _) (fun r => ?_)
          (by omega)
        rcases r with _ | values <;> simp

attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- The canonical commitment replay fact. A resolved bottom tree resolves the canonical
commitment of each of its keys. -/
theorem resolves_rawCommitment (cache : HashCache C) (top : TopTree) (e : KeyIndex)
    (out : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache (referenceTree SigningHitProof.forestHash
      (SigningHitProof.forestValue x.2.1) x.1 top (.bottom (treeOf e))) out) :
    DeterministicSigning.Resolves cache (SigningGuessProof.rawCommitment x.2.1 x.1 e) () := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, -⟩ := h.of_bind
  obtain ⟨values, hvalues, -⟩ := houtputs.of_map
  have hmem : (⟨.commitment e, [.randomizer bottomLayer e]⟩ : Job) ∈ bottomJobs (treeOf e) := by
    have hk := bottomKey_treeOf e
    simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
      List.mem_singleton]
    exact Or.inl (Or.inr ⟨_, by rw [hk]⟩)
  obtain ⟨bits, hjob⟩ := SigningHitProof.resolves_mapM_member _ _ _ hvalues _ hmem
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, bind_pure_comp, map_pure] at hjob
  rw [bind_map_left] at hjob
  obtain ⟨ρ, hρ, hrest⟩ := hjob.of_bind
  obtain ⟨a', hq, -⟩ := hrest.of_map
  unfold SigningGuessProof.rawCommitment
  rw [SigningOwnCommit.rawRandomizer_eq]
  refine hρ.bind ?_
  exact hq.bind (f := fun _ => (pure () : OracleComp (Query C →ₒ HashOutput) Unit)) (.pure ())

theorem altLe_pure {α : Type} (a : α) (n : ℕ) (s : LoggedState C) :
    AltLe prims x (pure a : OracleComp (WorldSpec C) α) n s := by
  simp only [AltLe, simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
  exact le_add_right le_rfl

set_option maxRecDepth 100000 in
/-- The honest signature does not raise the commitment potential. Its build is covered by the
commitment completion, and its check of `c_e` repeats the canonical commitment call of the build. -/
theorem altRise_honestSignature (top : TopTree) (e : KeyIndex) (message : Message) :
    AltRise prims x (honestSignature (fun oa => oa) (SigningOwnHit.honestDealt x top) e message) 0 := by
  unfold honestSignature
  simp only [SigningOwnHit.honestDealt, dealtWith]
  rw [← SigningHitProof.hashEmbed_referenceTree, map_eq_bind_pure_comp, bind_assoc]
  intro s
  rw [show ∀ {α β : Type} (R : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β),
    liftFree (R >>= f) = liftFree R >>= fun a => liftFree (f a) from φ_bind]
  refine altLe_bind prims x _ _ s 0 0 0 (altRise_bottom prims x top (treeOf e) s) (fun z hz => ?_) le_rfl
  have hres := SigningOwnHit.logged_hashEmbed_resolves prims _ s z hz
  have hcom := resolves_rawCommitment x _ top e _ hres
  unfold SigningGuessProof.rawCommitment at hcom
  rw [SigningOwnCommit.rawRandomizer_eq] at hcom
  obtain ⟨ρ, hρ, hq⟩ := hcom.of_bind
  obtain ⟨a, ha, -⟩ := hq.query_inv
  rcases z with ⟨out, s'⟩
  rcases out with _ | (top' | tree)
  · exact altRise_of_bound prims x _ 0 (by simp) s'
  · exact altRise_of_bound prims x _ 0 (by simp) s'
  · simp only [Function.comp_apply, pure_bind]
    rw [← SigningHitProof.hashEmbed_forestValue]
    refine altLe_resolved_bind prims x _ ρ _ 0 s' hρ fun s'' hs'' => ?_
    obtain ⟨K, hK, hKn⟩ := signCodeword_split x (tree.commitment e) e message ρ
    rw [hK, bind_assoc, ← SigningHitProof.hashEmbed_forestHash]
    refine altLe_resolved_bind prims x _ a _ 0 s'' ?_ fun s3 _ => ?_
    · exact SigningOwnCover.forestHash_resolves _ _ _
        (.query _ a (show SigningDescentProof.thView s''.1.1 _ = some a from hs'' ha) _ _ (.pure _))
    refine altRise_of_bound prims x _ 0 ?_ s3
    refine SigningOwnHit.bound_bind_le (a := 0) (b := 0) (tweakable_noCommit x _ (hKn a)) (fun r => ?_) le_rfl
    rcases r with _ | ⟨randomness, encoding⟩
    · exact isQueryBoundP_pure _ _ _
    refine isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnHit.sequenceFin_bound_zero _ _ fun l => ?_)
      fun _ _ => isQueryBoundP_bind (n := 0) (m := 0) (tweakable_noCommit x _
        (SigningOwnCommit.merklePath_noCall x.1 _ (SigningOwnCommit.structural_not_commitment x.1) _ _ _))
        fun _ _ => isQueryBoundP_pure _ _ _
    split
    · exact prfValue_commit x _ _
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_bind (n := 0) (m := 0) (prfValue_commit x _ _) fun _ _ =>
        isQueryBoundP_pure _ _ _

/-- The verification makes no commitment call. -/
theorem verify_noCommit (publicKey : PublicKey) (message : Message) (signature : Signature) :
    SigningSelectionProof.NoCall
      (fun input => SigningGuessProof.RawCommitmentInput (C := C) x.1 (.hash input))
      (Verification.verifyWithHash publicKey message signature : OracleComp HashSpec Bool) := by
  have hs := fun P domain payload (_ : ∀ lay key, domain ≠ HashDomain.message lay key) =>
    SigningOwnCommit.not_rawCommitment_tweakable (C := C) x.1 P domain payload
  have hm := fun P lay key payload =>
    SigningOwnCommit.not_rawCommitment_tweakable (C := C) x.1 P (.message lay key) payload
  unfold Verification.verifyWithHash
  refine SigningSelectionProof.noCall_bind _ (SigningOwnCommit.layerRoot_noCall _ _ (hs _) _ _ _ _
    (SigningOwnCommit.messageDigest_noCall _ _ _ _ _ (hm _ _ _) _)) fun bottomRoot => ?_
  cases bottomRoot with
  | none => exact SigningSelectionProof.noCall_pure _ _
  | some bottomRoot =>
      refine SigningSelectionProof.noCall_bind _ (SigningOwnCommit.layerRoot_noCall _ _ (hs _) _ _ _ _
        (SigningOwnCommit.messageDigest_noCall _ _ _ _ _ (hm _ _ _) _)) fun root => ?_
      cases root <;> exact SigningSelectionProof.noCall_pure _ _

set_option maxRecDepth 100000 in
attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- The ceremony of the top tree makes no commitment call. -/
theorem topTree_noCommit :
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top).IsQueryBoundP
      (SigningGuessProof.RawCommitmentInput x.1) 0 := by
  unfold referenceTree ceremonyOutput
  refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_map_iff _ _ _).2
    (SigningOwnCommit.mapM_bound_zero_of_mem _ _ _ fun job hjob => ?_)) fun outputs _ => ?_
  · simp only [topJobs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hjob
    obtain ⟨b, l, rfl⟩ := hjob
    exact SigningOwnCommit.referenceJob_noCommitment x _ fun _ h => by cases h
  rcases outputs with _ | outputs
  · exact isQueryBoundP_pure _ _ _
  dsimp only
  exact isQueryBoundP_bind (n := 0) (m := 0) (SigningOwnCommit.forestHash_noCall _ _
    (SigningOwnCommit.merkleNode_noCall x.1 _ (SigningOwnCommit.structural_not_commitment x.1) _ _ _ _))
    fun _ _ => isQueryBoundP_pure _ _ _

end Calculus

set_option maxRecDepth 100000 in
/-- The dealer does not raise the commitment potential. The ceremony of the top tree makes no commitment
call. -/
theorem alt_dealer_rise (x : Keys3 C) :
    ∑' r, Pr{let z ← dealerRun prims x}[z = r] * altPotential x r.2.1 ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞) := by
  have hprog : referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
      x.1 emptyTop .top = liftFree (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
        (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top)) := by
    rw [show referenceTree (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p))
        x.1 emptyTop .top = liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _, ← SigningHitProof.hashEmbed_referenceTree]
  rw [dealerRun, flatWorld, carry_run, OracleComp.tsum_prEvent_map_mul, hprog]
  have h := altRise_of_bound prims x _ 0 (hashEmbed_commit_bound x _ 0 (topTree_noCommit x)) loggedInit
  have h0 : altPotential x loggedInit = 0 := by
    simp [guarded, loggedInit, Programmed, SigningHitProof.completionPotential_empty]
  unfold AltLe at h
  rw [h0, zero_add] at h
  exact h

/-- One query of the forger raises the commitment potential by its own commitment call, and a
round-2 request by its check of `c_e`. -/
theorem alt_step_rise (x : Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C) :
    ∑' r, Pr{let z ← (flatOracles prims x (SigningHitProof.actualDealt x top) t).run p}[z = r] *
        altPotential x r.2.1 ≤
      altPotential x p.1 + (2 ^ 128 : ℝ≥0∞)⁻¹ *
        ((ownDomainUnit (SigningGuessProof.RawCommitmentInput x.1) t + round2Unit t : ℕ) : ℝ≥0∞) := by
  rw [flatOracles, flat, StateT.run_mk, OracleComp.tsum_prEvent_map_mul, carry_run_pair, OracleComp.tsum_prEvent_map_mul]
  cases t with
  | inl t =>
    simp only [flaggedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, OracleComp.tsum_prEvent_map_mul]
    erw [adversary_query, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    erw [id_map]
    refine (alt_step prims x (.inl (.inl t)) p.1).trans_eq ?_
    rcases t with n | (q | q) <;> rfl
  | inr q =>
    simp only [flaggedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, OracleComp.tsum_prEvent_map_mul]
    rw [SigningHitProof.tsigOracles_free]
    refine (altRise_tsigOracles prims x top q p.2.1 p.1).trans ?_
    simp [ownDomainUnit]

/-- The finish does not raise the commitment potential. The verification makes no commitment call,
and the tail repeats the commitment call of its build. -/
theorem alt_finish_rise (x : Keys3 C) (top : TopTree) (forgery : Forgery) (st : TsigState C)
    (s : LoggedState C) :
    ∑' r, Pr{let z ← ((simulateQ (loggedImpl prims)
          (tsigFinish (SigningHitProof.actualDealt x top) (forgery, st))).run s)}[z = r] *
        altPotential x r.2 ≤
      altPotential x s + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞) := by
  show AltLe prims x _ 0 s
  unfold SigningCoreProof.tsigFinish
  dsimp only
  have hverify : AltLe prims x (liftFree (tweakable (Verification.verifyWithHash ⟨top.root, x.1⟩ forgery.message
      forgery.signature))) 0 s :=
    altRise_of_bound prims x _ 0 (tweakable_noCommit x _ (verify_noCommit x _ _ _)) s
  refine altLe_bind prims x _ _ s 0 0 0 hverify (fun z _ => ?_) le_rfl
  split_ifs
  · simp only [pure_bind]
    exact altLe_pure prims x _ 0 z.2
  · refine altLe_bind prims x _ _ z.2 0 0 0 ?_ (fun w _ => ?_) le_rfl
    · have hsig := altRise_honestSignature prims x top forgery.signature.leafIndex forgery.message z.2
      rw [← SigningCacheProof.liftFree_honestSignature] at hsig
      exact hsig
    · exact altLe_bind prims x _ _ w.2 0 0 0 (altLe_pure prims x _ 0 w.2)
        (fun v _ => altLe_pure prims x _ 0 v.2) le_rfl

set_option maxRecDepth 100000 in
/-- The bound of a second opening of a commitment with the own budget. -/
theorem altOwn : AltOwn prims (C := C) := by
  intro A x
  have hf := flat_potential_le prims A x (altPotential x) (fun _ _ => True)
    (fun t => ownDomainUnit (SigningGuessProof.RawCommitmentInput x.1) t + round2Unit t) 0 0
    (alt_dealer_rise prims x) (fun _ _ _ _ => trivial)
    (fun top t p _ => alt_step_rise prims x top t p) (fun _ _ _ _ _ _ => trivial)
    (fun top forgery st s _ => alt_finish_rise prims x top forgery st s)
  rw [Nat.add_zero, Nat.cast_zero, add_zero] at hf
  refine le_trans ?_ hf
  rw [← loggedRun_forget, prEvent_map, OracleComp.prEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support (loggedRun prims A x)
  · by_cases hw : SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1
    · simp only [hw, if_true, guarded, if_neg (noProgramQuery prims C A x z hz)]
      rw [SigningHitProof.completionPotential_terminal _ _ _
        (SigningGuessProof.alternativeCommitment_completed x.2.1 x.1 _ hw), mul_one]
    · simp [hw]
  · simp [prEvent_eq_zero_of_not_mem_support _ hz]

end ThresholdLeanXmssSecurity.SigningOwnAlt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.alt_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.alt_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.alt_run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.alt_run_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_block

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_replay

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_resolved_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_resolved_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.liftFree_commit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.liftFree_commit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_of_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.hashEmbed_commit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.hashEmbed_commit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.tweakable_commit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.tweakable_commit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.tweakable_noCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.tweakable_noCommit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.prfValue_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.prfValue_commit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.eval_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.eval_commit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.signCodeword_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.signCodeword_split

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.signCodeword_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.signCodeword_commit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.signRound2With_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.signRound2With_commit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_bottomOnce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_bottomOnce

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_tsigOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_tsigOracles

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.resolves_rawCommitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.resolves_rawCommitment

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altLe_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_honestSignature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altRise_honestSignature

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.verify_noCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.verify_noCommit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.topTree_noCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.topTree_noCommit

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.alt_dealer_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.alt_dealer_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.alt_step_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.alt_step_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.alt_finish_rise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.alt_finish_rise

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnAlt.altOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnAlt.altOwn
