import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ListShiftAlias

/-!
# The law of the round-2 mail from a change of the honest commit cells

`midShiftLaw_of_commit` proves `MidShiftLaw` from `MidCommitLaw`.

* `listPreAt` is `listPre` with the commit cells of the honest operators as a parameter. On the
  parts with the term parts of a hidden term `T'` shifted, `listPre` is `listPreAt` on the unshifted
  parts with the commit cells of the shifted parts (`listPre_shift`). Only the commit cells of two
  honest holders of `T'` change.
* `listPreAt` makes no free call at a hidden cell, so `compWorld` runs it as `loggedWorld`
  (`compWorld_listPreAt`). The seeds drop out.
* The draw of the parts does not change under the shift of the parts of `T'` (`evalDist_shiftAll`).
* `MidCommitLaw` states that the law of the round-2 mail of `listPreAt` in `loggedWorld` does not
  change when the commit cells between two honest operators change. Such an answer goes only to the
  honest receiver, and nobody reads it before round 2.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_mapM
  noCall_sequenceFin noCall_query)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

section Hidden

variable (D : C.Coalition) (parts : C.Party → Parts C)

/-- A free call of `H` at a hidden cell. -/
def HiddenFree : (WorldSpec C).Domain → Prop := fun t => ∃ q, t = .inr (.inr (.inl q)) ∧ HiddenCell D parts q

theorem compWorld_of_not_hiddenFree (prims : Primitives) (seed : C.Term → HashOutput) (t : (WorldSpec C).Domain)
    (ht : ¬ HiddenFree D parts t) : compWorld prims D parts seed t = loggedWorld prims D t := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  rotate_left 5
  · have hn : hiddenTermOf D parts q = none := by
      unfold hiddenTermOf
      split_ifs with h
      · exact absurd ⟨q, rfl, h⟩ ht
      · rfl
    simp only [compWorld, hn]
  all_goals rfl

theorem noCall_counted_hidden {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    NoCall (HiddenFree D parts) (counted oa) := by
  rw [noCall_iff]
  induction oa using OracleComp.inductionOn with
  | pure a => simp [counted]
  | query_bind t k ih =>
    have e : counted (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inl t)) : OracleComp (WorldSpec C) _) >>= fun u => counted (k u) := by
      unfold counted
      rw [simulateQ_bind, simulateQ_spec_query]
      rfl
    have ht : ¬ HiddenFree D parts (.inl t) := by
      rintro ⟨q, e, -⟩
      cases e
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht, fun u => by simpa [ht] using ih u⟩

theorem noCall_free_liftComp_hidden {α : Type} (X : OracleComp (RoSpec C) α)
    (h : NoCall (fun t : (RoSpec C).Domain => ∃ q, t = .inl q ∧ HiddenCell D parts q) X) :
    NoCall (HiddenFree D parts) (free (liftComp X (LocalSpec C))) := by
  rw [noCall_iff] at h ⊢
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ ∃ q, t = .inl q ∧ HiddenCell D parts q := h.1.resolve_right (by omega)
    have ht' : ¬ HiddenFree D parts (.inr (.inr t)) := by
      rintro ⟨q, e, hq⟩
      cases e
      exact ht ⟨q, rfl, hq⟩
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inr t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht', fun u => by simpa [ht'] using ih u (by simpa [ht] using h.2 u)⟩

theorem noCall_free_liftComp_prob {α : Type} (X : ProbComp α) :
    NoCall (HiddenFree D parts) (free (liftComp X (LocalSpec C))) := by
  rw [noCall_iff]
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have ht' : ¬ HiddenFree D parts (.inr (.inl t)) := by
      rintro ⟨q, e, -⟩
      cases e
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht', fun u => by simpa [ht'] using ih u⟩

end Hidden

/-! ## The list program with the commit cells as a parameter -/

section At

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- `listPre` with the commit cells `commitAt` of the honest operators. -/
def listPreAt (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) (commitAt : C.Party → C.Party → Query C) : OracleComp (WorldSpec C) (ListMid C E net.State) :=
  commitDrawsAt D commitAt >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  if ∀ i, i ∉ D.1 → revealReady (commitInbox D commitments r.1.2) i = none then pure (commitments, r, none) else
  counted (liftComp (net.round r.1.1 (levelMail D (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i)))) _) >>= fun r2 => pure (commitments, r, some r2)

theorem listPre_eq_at (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) :
    listPre D net state early parameter dealt parts = listPreAt D net state early parameter dealt parts (commitAddress parts) :=
  rfl

/-- On the parts with the term parts of a hidden term shifted, `listPre` is `listPreAt` on the unshifted
parts with the commit cells of the shifted parts. -/
theorem listPre_shift (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) (T : C.Term) (c : C.Party → HashOutput) (hT : ¬ KnownTo D.1 T) :
    listPre D net state early parameter dealt (shiftAll T c parts) =
      listPreAt D net state early parameter dealt parts (commitAddress (shiftAll T c parts)) := by
  have hblock : ∀ (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E)),
      programBlock D log sent parameter dealt (shiftAll T c parts) = programBlock D log sent parameter dealt parts := by
    intro log sent
    rw [programBlock_eq_view, programBlock_eq_view]
    refine programBlockView_congr D parameter dealt _ _ (fun i j => ?_) (fun i j m => ?_) (fun i j T' hT' => ?_)
    · split_ifs <;> rfl
    · split_ifs
      · rfl
      · exact shiftAll_pair T c parts j m
    · split_ifs
      · rfl
      · exact SeedNormal.shiftAll_term_ne T T' c parts j (known_ne D T T' hT hT')
  have hmail : ∀ d : C.Party → Option Unit, levelMail D d (fun i _ => revealOutbox (E := E) .seedGen i (shiftAll T c parts i)) =
      levelMail D d (fun i _ => revealOutbox .seedGen i (parts i)) := by
    intro d
    funext c' i
    unfold levelMail
    split_ifs with h
    · rcases d i with _ | x
      · rfl
      · dsimp only
        unfold revealOutbox
        split_ifs
        · rfl
        · rw [revealTo_shiftAll T c parts i c' fun hc => hT ⟨c', h.1, hc⟩]
    · rfl
  unfold listPre listPreAt
  rw [show commitDraws D (shiftAll T c parts) = commitDrawsAt D (commitAddress (shiftAll T c parts)) from rfl]
  refine bind_congr fun commitments => bind_congr fun r => ?_
  rw [hblock, hmail]

theorem noCall_listPreAt (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts parts' : C.Party → Parts C) (commitAt : C.Party → C.Party → Query C)
    (h : ∀ i j, ¬ HiddenCell D parts' (commitAt i j)) :
    NoCall (HiddenFree D parts') (listPreAt D net state early parameter dealt parts commitAt) := by
  unfold listPreAt
  refine noCall_bind _ ?_ fun commitments => noCall_bind _ ?_ fun r => noCall_bind _ ?_ fun _ => ?_
  · unfold commitDrawsAt
    refine noCall_sequenceFin _ _ fun i => ?_
    split_ifs
    · exact noCall_pure _ _
    · refine noCall_free_liftComp_hidden D parts' _ (noCall_mapM _ _ _ fun j => noCall_query _ _ ?_)
      rintro ⟨q, e, hq⟩
      cases e
      exact h i j hq
  · rw [observe_eq]
    exact noCall_counted_hidden D parts' _
  · rw [programBlock_eq_view]
    unfold programBlockView
    refine noCall_bind _ (noCall_free_liftComp_prob D parts' _) fun high =>
      noCall_bind _ (noCall_counted_hidden D parts' _) fun _ => noCall_bind _ ?_ fun _ => noCall_bind _ ?_ fun _ =>
        noCall_pure _ _
    · refine noCall_mapM _ _ _ fun T => ?_
      split
      · exact noCall_counted_hidden D parts' _
      · exact noCall_pure _ _
    · refine noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_
      split_ifs
      · exact noCall_counted_hidden D parts' _
      · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact noCall_bind _ (noCall_counted_hidden D parts' _) fun _ => noCall_pure _ _

theorem not_hiddenCell_commitAddress (parts parts' : C.Party → Parts C) (i j : C.Party) :
    ¬ HiddenCell D parts' (commitAddress parts i j) :=
  not_hiddenCell_commit D parts' _ _ _

/-- `compWorld` runs `listPreAt` with commit cells as `loggedWorld` does. -/
theorem compWorld_listPreAt (prims : Primitives) (seed : C.Term → HashOutput) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts parts' commitParts : C.Party → Parts C) :
    simulateQ (compWorld prims D parts' seed) (listPreAt D net state early parameter dealt parts (commitAddress commitParts)) =
      simulateQ (loggedWorld prims D) (listPreAt D net state early parameter dealt parts (commitAddress commitParts)) :=
  simulateQ_congr_of_noCall (HiddenFree D parts') _ _ (compWorld_of_not_hiddenFree D parts' prims seed) _
    (noCall_listPreAt D net state early parameter dealt parts parts' _
      (not_hiddenCell_commitAddress D commitParts parts'))

end At

/-! ## The statement and the glue -/

section Glue

variable (prims : Primitives)

/-- The law of the round-2 mail under a change of the honest commit cells. Two families of commit cells
that agree for each corrupt receiver and that are commit cells of the seed generation for each honest
pair give one law of the round-2 mail of `listPreAt` in `loggedWorld`, from each state. An honest pair
cell has its answer read before round 2 by no step, since `commitOutbox` sends to each operator only
its own commitment. A counted call at such a cell sees a uniform value, whether the cell holds a
commitment or not. -/
def MidCommitLaw : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (commitAt commitAt' : C.Party → C.Party → Query C) (s : LogState C),
    (∀ i j, i ∉ D.1 → j ∈ D.1 → commitAt i j = commitAt' i j) →
    (∀ i j, i ∉ D.1 → j ∉ D.1 → ∃ r r', commitAt i j = .commit .seedGen i j r ∧ commitAt' i j = .commit .seedGen i j r') →
    (fun z : ListMid C E net.State × LogState C => z.1.2.2.map Prod.snd) <$>
        (simulateQ (loggedWorld prims D) (listPreAt D net state early parameter dealt parts commitAt)).run s =ᵈ
      (fun z : ListMid C E net.State × LogState C => z.1.2.2.map Prod.snd) <$>
        (simulateQ (loggedWorld prims D) (listPreAt D net state early parameter dealt parts commitAt')).run s

theorem shiftAll_shiftAll (T : C.Term) (c : C.Party → HashOutput) (parts : C.Party → Parts C) :
    shiftAll T c (shiftAll T c parts) = parts := by
  funext k
  simp only [shiftAll, shiftParts]
  congr 1
  · funext T'
    split_ifs <;> simp [BitVec.xor_assoc]

/-- `MidCommitLaw` gives `MidShiftLaw`. -/
theorem midShiftLaw_of_commit (law : MidCommitLaw (C := C) (E := E) prims) : MidShiftLaw (C := C) (E := E) prims := by
  intro D A T hT c
  unfold listMidRun
  rw [prefix_run]
  simp only [bind_assoc, pure_bind, map_bind, map_pure]
  refine EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun b => ?_
  have hu := (evalDist_shiftAll T c).symm.bind_left (fun parts =>
    $ᵗ (C.Term → HashOutput) >>= fun seed =>
      (simulateQ (compWorld prims D parts seed)
        (listPre D A.net a.1.1 a.1.2 b.1 b.2.2 parts)).run a.2 >>= fun m =>
          (pure (m.1.2.2.map Prod.snd, shiftAll T c parts) :
            ProbComp (Option (C.Party → C.Party → Option (Msg E)) × (C.Party → Parts C))))
  rw [bind_map_left] at hu
  refine hu.trans (EvalDistEq.bind_right _ fun parts => EvalDistEq.bind_right _ fun seed => ?_)
  simp only [shiftAll_shiftAll]
  rw [listPre_shift D A.net a.1.1 a.1.2 b.1 b.2.2 parts T c hT, listPre_eq_at,
    compWorld_listPreAt, compWorld_listPreAt]
  have h := (law D A.net a.1.1 a.1.2 b.1 b.2.2 parts (commitAddress (shiftAll T c parts)) (commitAddress parts) a.2
    (fun i j _ hj => by
      unfold commitAddress
      rw [revealTo_shiftAll T c parts i j fun hh => hT ⟨j, hj, hh⟩])
    (fun i j _ _ => ⟨_, _, rfl, rfl⟩)).map fun o => (o, parts)
  simp only [Functor.map_map] at h
  simpa [map_eq_bind_pure_comp, midMail] using h

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.midShiftLaw_of_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.midShiftLaw_of_commit
