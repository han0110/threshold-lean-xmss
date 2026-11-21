import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CountsParts
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Rest

/-!
# The free and programming calls of the reference suffix

The cost `cost (callCharge (FreeCharged D T parts))` of the reference suffix is at most `(n + 1) k`.

* The commit calls, the parameter cells, the pair cells and the shared key cells are no cells of a
  shift (`charges_shape`). The derivations of `T` ask `markCell`, whose list is empty. A derivation of
  another hidden term asks its hidden cell, whose shift is in `hiddenShifts`.
* `programBlock` programs one term cell for each known term (`cost_programBlock`).
* Each honest operator derives one cell for each held known term (`cost_revealNextAt`), and a round of
  `levelRound` has one local step for each operator (`cost_levelRound`).
* The rest of the game makes no free call of the seed generation and no programming call.

`partsWalk` proves `PartsWalk`, and `partsCount` proves `PartsCount`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal (seedGenAt commitAddress commitDrawsAt deriveAt
  revealNextAt openAddress sharedAddress levelRound commitMail commitInbox revealReady
  programBlock echoNext noCall_secRest_seedGenCell SeedGenCell)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)
open PFunctor.FreeM (cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The cost through the embeddings -/

section Embed

variable (p : (WorldSpec C).Domain → Prop)

theorem cost_free {β : Type} (oa : OracleComp (LocalSpec C) β) :
    cost (callCharge p) (free oa) ≤ cost (callCharge fun u => p (.inr u)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact le_rfl
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, cost, cost, costWith_query_bind, costWith_query_bind]
    exact add_le_add le_rfl (iSup_mono ih)

theorem cost_liftComp_hash (c : (LocalSpec C).Domain → ℕ∞) {β : Type} (oa : OracleComp (RoSpec C) β) :
    cost c (liftComp oa (LocalSpec C)) ≤ cost (fun r => c (.inr r)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact le_rfl
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u => liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e, cost, cost, costWith_query_bind, costWith_query_bind]
    exact add_le_add le_rfl (iSup_mono ih)

theorem cost_liftComp_sample (c : (LocalSpec C).Domain → ℕ∞) (hc : ∀ n, c (.inl n) = 0) {β : Type}
    (oa : ProbComp β) : cost c (liftComp oa (LocalSpec C)) ≤ 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact cost_pure_le _ _ _
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inl t)) : OracleComp (LocalSpec C) _) >>= fun u => liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e, cost, costWith_query_bind, hc, zero_add]
    exact iSup_le ih

theorem cost_program (q : Query C) (v : HashOutput) :
    cost (callCharge p) (ThresholdLeanXmss.program q v) ≤ callCharge p (.inl (.inr (q, v))) := by
  unfold ThresholdLeanXmss.program counted
  erw [simulateQ_query]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  exact cost_query_le _

end Embed

/-! ## The cells that a shift names -/

section Cells

variable (D : C.Coalition) (T : C.Term) (parts : C.Party → Parts C)

/-- The cell of a shift outside `hiddenShifts`. -/
def Charges (Y : Query C) : Prop := ∃ δ, Y = shiftCell T parts δ ∧ δ ∉ hiddenShifts D T parts

theorem freeCharged_free (q : Query C) : FreeCharged D T parts (.inr (.inr (.inl q))) ↔ Charges D T parts q := by
  constructor
  · rintro ⟨⟨δ, hc, hδ⟩, -⟩
    exact ⟨δ, Option.some_injective _ hc, hδ⟩
  · rintro ⟨δ, rfl, hδ⟩
    exact ⟨⟨δ, rfl, hδ⟩, fun h => h⟩

theorem freeCharged_program (x : Query C × HashOutput) :
    FreeCharged D T parts (.inl (.inr x)) ↔ Charges D T parts x.1 := by
  constructor
  · rintro ⟨⟨δ, hc, hδ⟩, -⟩
    exact ⟨δ, Option.some_injective _ hc, hδ⟩
  · rintro ⟨δ, he, hδ⟩
    exact ⟨⟨δ, by rw [← he]; rfl, hδ⟩, fun h => h⟩

theorem holdersList_ne_nil_of_t : SeedCompare.holdersList T ≠ [] := by
  have hc := SeedCompare.card_holders T
  have hpos : 0 < Fintype.card {k // k ∈ C.holders T} := by
    have := C.one_le_t
    omega
  obtain ⟨⟨k, hk⟩⟩ := Fintype.card_pos_iff.1 hpos
  intro h
  have hmem : k ∈ SeedCompare.holdersList T := by
    simp [SeedCompare.holdersList, Committee.parties, hk]
  rw [h] at hmem
  exact List.not_mem_nil hmem

/-- A charged cell is a term cell of the seed generation with a list that is not empty. -/
theorem charges_shape {Y : Query C} (h : Charges D T parts Y) : ∃ L, Y = .derive .seedGen .term L ∧ L ≠ [] := by
  obtain ⟨δ, rfl, -⟩ := h
  rw [shiftCell_eq]
  exact ⟨_, rfl, by simpa using holdersList_ne_nil_of_t T⟩

theorem not_charges_markCell : ¬ Charges D T parts markCell := by
  intro h
  obtain ⟨L, hL, hne⟩ := charges_shape D T parts h
  simp only [markCell, Query.derive.injEq, true_and] at hL
  exact hne hL.symm

theorem not_charges_hidden {T' : C.Term} (hne : T' ≠ T) (hT' : ¬ KnownTo D.1 T') :
    ¬ Charges D T parts (SeedCompare.hiddenInput parts T') := by
  rintro ⟨δ, he, hδ⟩
  exact hδ ⟨T', hne, hT', he.symm⟩

/-- The charge of a computation of `H` and `PRG` of an honest operator. -/
abbrev roCharge : (RoSpec C).Domain → ℕ∞ := fun r => callCharge (FreeCharged D T parts) (.inr (.inr r))

theorem cost_hashQuery (q : Query C) :
    cost (roCharge D T parts) (hashQuery q) ≤ if Charges D T parts q then 1 else 0 := by
  unfold hashQuery
  refine (cost_query_le _).trans (le_of_eq ?_)
  simp only [roCharge, callCharge, freeCharged_free]
  split_ifs <;> rfl

theorem cost_hashQuery_zero (q : Query C) (hq : ¬ Charges D T parts q) : cost (roCharge D T parts) (hashQuery q) ≤ 0 :=
  (cost_hashQuery D T parts q).trans (by simp [hq])

theorem cost_program_zero (q : Query C) (v : HashOutput) (hq : ¬ Charges D T parts q) :
    cost (callCharge (FreeCharged D T parts)) (ThresholdLeanXmss.program q v) ≤ 0 :=
  (cost_program _ q v).trans (by simp [callCharge, freeCharged_program, hq])

theorem cost_free_ro {β : Type} (oa : OracleComp (RoSpec C) β) :
    cost (callCharge (FreeCharged D T parts)) (free (liftComp oa (LocalSpec C))) ≤ cost (roCharge D T parts) oa :=
  (cost_free _ _).trans (cost_liftComp_hash _ oa)

theorem cost_free_sample {β : Type} (oa : ProbComp β) :
    cost (callCharge (FreeCharged D T parts)) (free (liftComp oa (LocalSpec C))) ≤ 0 :=
  (cost_free _ _).trans (cost_liftComp_sample _ (fun n => by simp [callCharge, FreeCharged, ShiftCharged, cellOf]) oa)

theorem cost_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    cost (callCharge (FreeCharged D T parts)) (worldRoles.adversary oa) ≤ 0 := by
  have h := SetupBudgets.honestP_adversary (fun u : (LocalSpec C).Domain => ∃ q, u = .inr (.inl q)) oa
  exact (cost_callCharge_le_iff _ _ 0).2 (FirstCounts.isQueryBoundP_add (freeCharged_cases D T parts) _ 0 0 h
    ((noCall_iff _ _).1 (Collision.noProgram_adversary oa)))

/-- The known terms are `k` in the list of all terms. -/
theorem sum_known : (C.terms.map fun T' => if KnownTo D.1 T' then (1 : ℕ∞) else 0).sum = (knownTerms D).card := by
  unfold Committee.terms
  rw [Finset.sum_map_toList]
  simp [knownTerms, Finset.sum_boole]

end Cells

/-! ## The programming block -/

section Block

variable {E : Type} (D : C.Coalition) (T : C.Term) (parts : C.Party → Parts C)

theorem cost_programBlock (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) :
    cost (callCharge (FreeCharged D T parts)) (programBlock D log sent parameter dealt parts) ≤ (knownTerms D).card := by
  unfold programBlock
  refine (cost_bind_le_add (cost_free_sample D T parts _) fun _ => cost_bind_le_add
    (cost_program_zero D T parts _ _ fun h => ?_) fun _ => cost_bind_le_add
      (cost_mapM_le _ (fun T' => if KnownTo D.1 T' then (1 : ℕ∞) else 0) (fun T' => ?_) C.terms) fun _ =>
        cost_bind_le_add (cost_mapM_le _ (fun _ => 0) (fun j => cost_mapM_le _ (fun _ => 0) (fun i => ?_) _ |>.trans
          (by simp)) _) fun _ => cost_pure_le _ _ 0).trans ?_
  · obtain ⟨L, hL, -⟩ := charges_shape D T parts h
    cases hL
  · split
    · rename_i j hj
      have hk : KnownTo D.1 T' := by
        have h2 := List.find?_some hj
        simp only [decide_eq_true_eq] at h2
        exact ⟨j, h2.1, h2.2⟩
      simp only [hk, ↓reduceIte]
      exact (cost_program _ _ _).trans (by simp only [callCharge]; split_ifs <;> simp)
    · exact cost_pure_le _ _ _
  · split
    · exact cost_program_zero D T parts _ _ fun h => by
        obtain ⟨L, hL, -⟩ := charges_shape D T parts h
        cases hL
    · exact cost_pure_le _ _ _
  · rw [sum_known]
    simp

end Block

/-! ## The local step of round 2 -/

section Reveal

variable {E : Type} (D : C.Coalition) (T : C.Term) (parts : C.Party → Parts C)

theorem cost_deriveAt (i : C.Party) (inbox : Mail C E) :
    cost (roCharge D T parts) (deriveAt D parts (termMark D parts T) i inbox) ≤ (knownTerms D).card := by
  unfold deriveAt
  refine (cost_bind_le_add (cost_hashQuery_zero D T parts _ fun h => ?_) fun _ => cost_bind_le_add
    (cost_mapM_le _ (fun T' => if KnownTo D.1 T' then (1 : ℕ∞) else 0) (fun T' => ?_) C.terms) fun _ =>
      cost_bind_le_add (cost_mapM_le _ (fun _ => 0) (fun j => ?_) _) fun _ => cost_pure_le _ _ 0).trans ?_
  · obtain ⟨L, hL, -⟩ := charges_shape D T parts h
    cases hL
  · by_cases hi : i ∈ C.holders T'
    · simp only [hi, ↓reduceIte]
      refine (cost_hashQuery D T parts _).trans ?_
      by_cases hk : KnownTo D.1 T'
      · simp only [hk, ↓reduceIte]
        split_ifs
        · exact le_rfl
        · exact zero_le
      · have hc : ¬ Charges D T parts (termMark D parts T i inbox T') := by
          unfold termMark
          split_ifs with he
          · exact not_charges_markCell D T parts
          · rw [SeedNormal.termAddress_hidden D parts i inbox T' hk]
            exact not_charges_hidden D T parts he hk
        simp only [hc, hk, ↓reduceIte, le_refl]
    · simp only [hi, ↓reduceIte]
      exact cost_pure_le _ _ _
  · split_ifs
    · exact cost_pure_le _ _ _
    · exact cost_hashQuery_zero D T parts _ fun h => by
        obtain ⟨L, hL, -⟩ := charges_shape D T parts h
        cases hL
  · rw [sum_known]
    simp

theorem cost_revealNextAt (committed : C.Party → Mail C E) (i : C.Party) (inbox : Mail C E) :
    cost (callCharge (FreeCharged D T parts))
      (free (revealNextAt D parts (commitAddress parts) (termMark D parts T) committed i inbox)) ≤
        (knownTerms D).card := by
  refine (cost_free _ _).trans ?_
  unfold revealNextAt
  refine (cost_bind_le_add (m := (knownTerms D).card) ((cost_liftComp_hash _ _).trans
    (cost_mapM_le _ (fun _ => 0) (fun k => cost_hashQuery_zero D T parts _ fun h => ?_) _)) fun opens => ?_).trans
      (by simp)
  · obtain ⟨L, hL, -⟩ := charges_shape D T parts h
    split_ifs at hL <;> cases hL
  · split_ifs
    · refine (cost_bind_le_add ((cost_liftComp_hash _ _).trans (cost_deriveAt D T parts i inbox)) fun keys =>
        cost_bind_le_add ((cost_liftComp_hash _ _).trans (cost_mapM_le _ (fun _ => 0) (fun j =>
          cost_hashQuery_zero D T parts _ fun h => ?_) _)) fun _ => cost_pure_le _ _ 0).trans (by simp)
      obtain ⟨L, hL, -⟩ := charges_shape D T parts h
      cases hL
    · exact cost_pure_le _ _ _

end Reveal

/-! ## A round of a phase -/

section Level

variable {E : Type} (D : C.Coalition) (T : C.Term) (parts : C.Party → Parts C)

theorem cost_levelRound (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type} (fuel : ℕ) (state : net.State)
    (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (b B : ℕ∞) (hnext : ∀ j x inbox, cost (callCharge (FreeCharged D T parts)) (free (next j x inbox)) ≤ b)
    (hcont : ∀ f s d', cost (callCharge (FreeCharged D T parts)) (cont f s d') ≤ B) :
    cost (callCharge (FreeCharged D T parts)) (levelRound D net fuel state d out next cont) ≤ C.n * b + B := by
  cases fuel with
  | zero => exact cost_pure_le _ _ _
  | succ fuel =>
    rw [levelRound]
    by_cases h1 : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left h1]
      exact cost_pure_le _ _ _
    rw [ite_eq_right h1]
    refine (cost_bind_le_add (cost_adversary D T parts _) fun r => ?_).trans (le_of_eq (zero_add _))
    by_cases h2 : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left h2]
      exact cost_pure_le _ _ _
    rw [ite_eq_right h2]
    refine cost_bind_le_add ((cost_sequenceFin_sum _ (fun _ => b) fun j => ?_).trans (le_of_eq ?_)) fun d' =>
      hcont fuel r.1 d'
    · split_ifs <;> (try split) <;> first | exact cost_pure_le _ _ _ | exact hnext _ _ _
    · simp [Finset.sum_const, nsmul_eq_mul]

end Level

/-! ## The reference suffix -/

section Suffix

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem cost_seedGenAt (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (T : C.Term) :
    cost (callCharge (FreeCharged D T parts))
      (seedGenAt D net state early parameter dealt parts (commitAddress parts) (termMark D parts T)) ≤
        ((C.n + 1) * (knownTerms D).card : ℕ) := by
  unfold seedGenAt
  have hdraws : cost (callCharge (FreeCharged D T parts)) (commitDrawsAt D (commitAddress parts)) ≤ 0 := by
    unfold commitDrawsAt
    refine (cost_sequenceFin_sum _ (fun _ => 0) fun i => ?_).trans (by simp)
    split_ifs
    · exact cost_pure_le _ _ _
    · exact (cost_free_ro D T parts _).trans (cost_mapM_le _ (fun _ => 0) (fun j =>
        cost_hashQuery_zero D T parts _ fun h => by
          obtain ⟨L, hL, -⟩ := charges_shape D T parts h
          cases hL) _ |>.trans (by simp))
  have hobs : ∀ (β : Type) (oa : OracleComp (LocalSpec C) β),
      cost (callCharge (FreeCharged D T parts)) (observe oa) ≤ 0 := fun β oa =>
    (cost_callCharge_le_iff _ _ 0).2 (noFree_observe D T parts oa)
  refine (cost_bind_le_add hdraws fun commitments => cost_bind_le_add (hobs _ _) fun r =>
    cost_bind_le_add (cost_programBlock D T parts _ _ _ _) fun _ =>
      cost_levelRound D T parts net _ _ _ _ _ _ ((knownTerms D).card) (C.n * 0 + 0)
        (fun j _ inbox => cost_revealNextAt D T parts _ j inbox) fun f2 s2 d2 =>
          cost_levelRound D T parts net _ _ _ _ _ _ 0 0 (fun _ _ _ => ?_) fun _ _ _ => cost_pure_le _ _ _).trans ?_
  · exact (cost_free _ _).trans (cost_pure_le _ _ _)
  · push_cast
    simp only [zero_add, mul_zero, add_zero]
    rw [add_mul, one_mul, add_comm]

omit [Fintype E] [DecidableEq E] in
/-- The rest of the game makes no free call at a charged cell and no programming call. -/
theorem noFree_secRest (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (parts : C.Party → Parts C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (st : RealState C A.net.State) :
    IsQueryBoundP ((secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A parameter seeds dealt emu).run' st)
      (FreeCharged D T parts) 0 := by
  have hcases : ∀ t, FreeCharged D T parts t → SeedGenCell t ∨ WorldProgramQuery t := by
    intro t ht
    rcases freeCharged_cases D T parts t ht with h | h
    · rcases t with u | u
      · exact h.elim
      · obtain ⟨q, rfl⟩ := h
        left
        have hc := (freeCharged_free D T parts q).1 ht
        obtain ⟨L, rfl, -⟩ := charges_shape D T parts hc
        exact ⟨_, rfl, rfl⟩
    · exact Or.inr h
  have hprog : NoCall WorldProgramQuery
      ((secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A parameter seeds dealt emu).run' st) := by
    rw [StateT.run'_eq]
    exact SigningSelectionProof.noCall_map _ _ (UsedHit.NoProg.bind (noProg_secRuns K circuits settings runLimit D _
      (fun _ => rfl) A.net parameter seeds dealt emu .top runLimit)
      (fun _ => noProg_secSigning K circuits settings runLimit D _ (fun _ => rfl) A parameter seeds dealt emu) st)
  exact FirstCounts.isQueryBoundP_add hcases _ 0 0 ((noCall_iff _ _).1 (noCall_secRest_seedGenCell K circuits
    settings runLimit D _ (fun _ => rfl) A parameter seeds dealt emu st)) ((noCall_iff _ _).1 hprog)

omit [Fintype E] [DecidableEq E] in
theorem partsWalk : PartsWalk K circuits settings runLimit := by
  intro D A T x hT
  rw [suffixAt_eq, ← cost_callCharge_le_iff]
  unfold suffixOf
  refine (cost_bind_le_add (cost_seedGenAt D A.net _ _ _ _ x.2.2 T) fun p => ?_).trans (le_of_eq (add_zero _))
  refine (cost_bind_le_add ((cost_callCharge_le_iff _ _ 0).2 (noFree_secRest K circuits settings runLimit D A T
    x.2.2 _ _ _ _ _)) fun _ => cost_pure_le _ _ 0).trans (le_of_eq (add_zero _))

omit [Fintype E] [DecidableEq E] in
theorem partsCount : PartsCount prims K circuits settings runLimit :=
  partsCount_of_walk prims K circuits settings runLimit (partsWalk K circuits settings runLimit)

end Suffix

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsCount
