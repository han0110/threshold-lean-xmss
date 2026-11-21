import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ListShiftLaw
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepCommitWalk

/-!
# The law of the round-2 mail under a change of the honest commit cells

`midCommitLaw` proves `MidCommitLaw`.

* An answer of a free call at a commit cell between two honest operators goes in `listPreAt` only into
  the commitments, which the round-2 mail reads only at corrupt receivers and through abort tags. So
  the answer can be replaced by zero (`listPreAt_mask`).
* A free call whose answer is not used, at a commit cell that no later call programs, drops in
  `loggedWorld` with no change of the law of the result (`wp_loggedWorld_drop`, from `wp_dropWrite`).
  A later read of the cell samples it then, as a corrupt receiver cell that aliases the cell does.
* `CtxEq` states that two programs give one law of the result in each context. It passes through
  `bind`, `mapM` and `sequenceFin`. After the drops the program reads only the commit cells of the
  corrupt receivers, which the two families share.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_mono noCall_bind noCall_pure
  noCall_mapM noCall_sequenceFin noCall_map)
open ThresholdLeanXmssSecurity.DkgSecurityProof (mainCell loggedWorld_freeHash loggedWorld_countedHash)
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- A commit cell of the seed generation. -/
def CommitCell (q : Query C) : Prop := ∃ i j r, q = .commit .seedGen i j r

/-! ## A dropped read in `loggedWorld` -/

section Drop

variable (prims : Primitives) (D : C.Coalition)

theorem loggedWorld_read {q : Query C} (hfix : ¬ IsFixed q) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr (.inl q))) ∨ t = .inr (.inr (.inl q))) (w : LogState C) (hw : w.1.1 q = none) :
    (loggedWorld prims D t).run w = ($ᵗ HashOutput) >>= fun u => (loggedWorld prims D t).run (putLog q (some u) w) := by
  have e : ∀ (u : HashOutput) (cache : HashCache C),
      ((Query C →ₒ HashOutput).randomOracle q).run (putAt q (some u) cache) = pure (u, putAt q (some u) cache) := by
    intro u cache
    rw [randomOracle.run_eq, putAt_self]
  rcases ht with rfl | rfl
  · simp only [loggedWorld_countedHash, hashAnswer_of_not_isFixed prims hfix, putLog, e, map_pure]
    rw [randomOracle.run_eq, hw]
    simp only [map_bind, map_pure, cacheQuery_eq_putAt hw]
  · simp only [loggedWorld_freeHash, hashAnswer_of_not_isFixed prims hfix, putLog, e, map_pure]
    rw [randomOracle.run_eq, hw]
    simp only [map_bind, map_pure, cacheQuery_eq_putAt hw]

/-- A free call at a commit cell whose answer is not used drops, when no later call programs the cell.
The law of the result does not change, from each world state. -/
theorem wp_loggedWorld_drop {q : Query C} (hq : CommitCell q) {α : Type} (G : α → ℝ≥0∞)
    (k : OracleComp (WorldSpec C) α) (hk : NoCall (OffCall D CommitCell) k) (w : LogState C) :
    wp ((simulateQ (loggedWorld prims D)
        ((liftM ((WorldSpec C).query (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) HashOutput) >>= fun _ => k)).run w)
      (fun z => G z.1) = wp ((simulateQ (loggedWorld prims D) k).run w) (fun z => G z.1) := by
  obtain ⟨i, j, r, rfl⟩ := hq
  have hfix : ¬ IsFixed (Query.commit .seedGen i j r : Query C) := fun ⟨_, h, _⟩ => by cases h
  have hX : ∀ k', (Query.commit .seedGen i j r : Query C) ≠ .streamKey k' := fun _ h => by cases h
  simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, liftM, monadLift_self, wp_bind]
  rw [loggedWorld_freeHash, hashAnswer_of_not_isFixed prims hfix, randomOracle.run_eq]
  cases hc : w.1.1 (.commit .seedGen i j r) with
  | some v => simp [Prod.mk.eta]
  | none =>
    simp only [map_bind, map_pure, wp_bind, wp_pure, cacheQuery_eq_putAt hc]
    refine wp_dropWrite (loggedWorld prims D) (fun w u => putLog (.commit .seedGen i j r) (some u) w)
      (fun w => w.1.1 (.commit .seedGen i j r) = none)
      (fun t => t = .inl (.inl (.inr (.inl (.commit .seedGen i j r)))) ∨ t = .inr (.inr (.inl (.commit .seedGen i j r))))
      (fun t => ∃ p, t = .inl (.inr p) ∧ p.1 = .commit .seedGen i j r)
      (fun t hr hp w u _ => loggedWorld_putLog _ prims D hX _ t (mainCell_ne_of t hr hp) w)
      (fun t hr hp w hw z hz => ?_) (fun t hr w hw => loggedWorld_read prims D hfix t hr w hw) _
      (fun _ _ _ _ => rfl) k (noCall_mono _ (fun t ⟨p, e, hp⟩ => Or.inl ⟨p, e, ⟨i, j, r, hp⟩⟩) hk) w hc
    have hw' : putLog (.commit .seedGen i j r) none w = w := by
      obtain ⟨⟨cache, hidden⟩, log⟩ := w
      simp only [putLog]
      rw [putAt_of_none _ hw]
    rw [← hw', loggedWorld_putLog _ prims D hX none t (mainCell_ne_of t hr hp)] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨z', _, rfl⟩ := hz
    simp [putLog, putAt_self]

end Drop

/-! ## Two programs with one law in each context -/

section Ctx

variable (prims : Primitives) (D : C.Coalition)

/-- `A` and `A'` give one law of the result in each context that programs no commit cell, from each
world state. -/
def CtxEq {β : Type} (A A' : OracleComp (WorldSpec C) β) : Prop :=
  ∀ {γ : Type} (K : β → OracleComp (WorldSpec C) γ), (∀ b, NoCall (OffCall D CommitCell) (K b)) →
    ∀ (G : γ → ℝ≥0∞) (w : LogState C),
      wp ((simulateQ (loggedWorld prims D) (A >>= K)).run w) (fun z => G z.1) =
        wp ((simulateQ (loggedWorld prims D) (A' >>= K)).run w) (fun z => G z.1)

theorem CtxEq.refl {β : Type} (A : OracleComp (WorldSpec C) β) : CtxEq prims D A A := fun _ _ _ _ => rfl

theorem CtxEq.bind {β β' : Type} {A A' : OracleComp (WorldSpec C) β} {B B' : β → OracleComp (WorldSpec C) β'}
    (hA : CtxEq prims D A A') (hB : ∀ b, CtxEq prims D (B b) (B' b)) (hBn : ∀ b, NoCall (OffCall D CommitCell) (B b)) :
    CtxEq prims D (A >>= B) (A' >>= B') := by
  intro γ K hK G w
  rw [bind_assoc, bind_assoc, hA (fun a => B a >>= K) (fun a => noCall_bind _ (hBn a) hK) G w]
  simp only [simulateQ_bind, StateT.run_bind, wp_bind]
  refine congrArg _ (funext fun z => ?_)
  have h := hB z.1 K hK G z.2
  simp only [simulateQ_bind, StateT.run_bind, wp_bind] at h
  exact h

theorem CtxEq.drop {q : Query C} (hq : CommitCell q) :
    CtxEq prims D ((fun _ => (0 : HashOutput)) <$> free (liftComp (hashQuery q) (LocalSpec C))) (pure 0) := by
  intro γ K hK G w
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_def, pure_bind]
  exact wp_loggedWorld_drop prims D hq G (K 0) (hK 0) w

theorem CtxEq.mapM {α β : Type} (l : List α) {g g' : α → OracleComp (WorldSpec C) β}
    (h : ∀ a, CtxEq prims D (g a) (g' a)) (hn : ∀ a, NoCall (OffCall D CommitCell) (g a)) :
    CtxEq prims D (l.mapM g) (l.mapM g') := by
  induction l with
  | nil => exact CtxEq.refl prims D _
  | cons a l ih =>
    simp only [List.mapM_cons]
    exact CtxEq.bind prims D (h a) (fun x => CtxEq.bind prims D ih (fun _ => CtxEq.refl prims D _)
      (fun _ => noCall_pure _ _)) (fun x => noCall_bind _ (noCall_mapM _ _ _ hn) fun _ => noCall_pure _ _)

theorem CtxEq.sequenceFin {β : Type} : ∀ {n : ℕ} {f f' : Fin n → OracleComp (WorldSpec C) β},
    (∀ i, CtxEq prims D (f i) (f' i)) → (∀ i, NoCall (OffCall D CommitCell) (f i)) →
    CtxEq prims D (OverPermutation.sequenceFin f) (OverPermutation.sequenceFin f')
  | 0, f, f', _, _ => fun _ _ _ _ => rfl
  | n + 1, f, f', h, hn => by
    simp only [OverPermutation.sequenceFin]
    exact CtxEq.bind prims D (h 0) (fun x => CtxEq.bind prims D
      (CtxEq.sequenceFin (fun i => h i.succ) (fun i => hn i.succ)) (fun _ => CtxEq.refl prims D _)
      (fun _ => noCall_pure _ _))
      (fun x => noCall_bind _ (noCall_sequenceFin _ _ fun i => hn i.succ) fun _ => noCall_pure _ _)

end Ctx

/-! ## The program with the honest pair answers dropped -/

section Program

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The commitments with zero at each honest receiver. -/
def maskC (cm : C.Party → List HashOutput) : C.Party → List HashOutput :=
  fun i => List.zipWith (fun j a => if j ∈ D.1 then a else 0) C.parties (cm i)

/-- The commit calls with the answers at honest receivers replaced by zero. -/
def commitDrawsZ (commitAt : C.Party → C.Party → Query C) : OracleComp (WorldSpec C) (C.Party → List HashOutput) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure [] else
    C.parties.mapM fun j => (fun a => if j ∈ D.1 then a else 0) <$> free (liftComp (hashQuery (commitAt i j)) (LocalSpec C))

/-- The commit calls of the corrupt receivers only, with zero at each honest receiver. -/
def commitDrawsN (commitAt : C.Party → C.Party → Query C) : OracleComp (WorldSpec C) (C.Party → List HashOutput) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure [] else
    C.parties.mapM fun j => if j ∈ D.1 then free (liftComp (hashQuery (commitAt i j)) (LocalSpec C)) else pure 0

theorem free_liftComp_mapM {α β : Type} (l : List α) (g : α → OracleComp (RoSpec C) β) :
    free (liftComp (l.mapM g) (LocalSpec C)) = l.mapM fun a => free (liftComp (g a) (LocalSpec C)) := by
  rw [liftComp_def]
  unfold free
  rw [simulateQ_list_mapM, simulateQ_list_mapM]
  rfl

theorem commitDrawsAt_mask (commitAt : C.Party → C.Party → Query C) :
    maskC D <$> commitDrawsAt D commitAt = commitDrawsZ D commitAt := by
  unfold commitDrawsAt commitDrawsZ
  rw [map_eq_bind_pure_comp,
    show (pure ∘ maskC D : (C.Party → List HashOutput) → OracleComp (WorldSpec C) _) =
      fun rs => pure fun i => (fun _ r => List.zipWith (fun j a => if j ∈ D.1 then a else 0) C.parties r) i (rs i) from rfl,
    ← sequenceFin_bind_pure]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, ite_false, free_liftComp_mapM]
    rw [mapM_map_zipWith (fun j a => if j ∈ D.1 then a else 0) (fun j => free (liftComp (hashQuery (commitAt i j)) _)),
      map_eq_bind_pure_comp]
    rfl

theorem commitDrawsN_congr (commitAt commitAt' : C.Party → C.Party → Query C)
    (h : ∀ i j, i ∉ D.1 → j ∈ D.1 → commitAt i j = commitAt' i j) : commitDrawsN D commitAt = commitDrawsN D commitAt' := by
  unfold commitDrawsN
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, ite_false]
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true, h i j hi hj]
    · simp only [hj, ite_false]

/-- The part of `listPreAt` after the commit calls. -/
def restMid (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) (commitments : C.Party → List HashOutput) : OracleComp (WorldSpec C) (ListMid C E net.State) :=
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  if ∀ i, i ∉ D.1 → revealReady (commitInbox D commitments r.1.2) i = none then pure (commitments, r, none) else
  counted (liftComp (net.round r.1.1 (levelMail D (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i)))) _) >>= fun r2 => pure (commitments, r, some r2)

theorem listPreAt_eq_rest (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) (commitAt : C.Party → C.Party → Query C) :
    listPreAt D net state early parameter dealt parts commitAt =
      commitDrawsAt D commitAt >>= restMid D net state early parameter dealt parts := rfl

/-- The round-2 mail reads the commitments only at corrupt receivers and through abort tags. -/
theorem restMid_mask (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) (cm : C.Party → List HashOutput)
    (hlen : ∀ i, i ∉ D.1 → (cm i).length = C.parties.length) :
    (fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$> restMid D net state early parameter dealt parts cm =
      (fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$>
        restMid D net state early parameter dealt parts (maskC D cm) := by
  have hmail : commitMail (E := E) D (maskC D cm) = commitMail D cm := by
    funext x i
    unfold commitMail
    split_ifs with h
    · have hxi : x ≠ i := fun e => h.2 (e ▸ h.1)
      simp only [commitOutbox, hxi, ite_false, maskC, getD_zipWith_parties _ _ (hlen i h.2), h.1, ite_true]
    · rfl
  have hready : ∀ sent : C.Party → C.Party → Option (Msg E),
      revealReady (commitInbox D (maskC D cm) sent) = revealReady (commitInbox D cm sent) := by
    intro sent
    funext i
    have hk : ∀ k, Msg.isAbort (commitInbox D (maskC D cm) sent i k) = Msg.isAbort (commitInbox D cm sent i k) := by
      intro k
      unfold commitInbox
      split_ifs
      · rfl
      · unfold commitOutbox
        split_ifs <;> rfl
    unfold revealReady anyAbort
    simp only [hk]
  unfold restMid
  simp only [map_bind, hmail, hready]
  refine bind_congr fun r => bind_congr fun _ => ?_
  split_ifs <;> simp

end Program

/-! ## The calls of the rest -/

section Calls

variable (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

theorem noCall_restMid (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) (cm : C.Party → List HashOutput) :
    NoCall (OffCall D CommitCell)
      ((fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$> restMid D net state early parameter dealt parts cm) := by
  have hnc : ∀ q : Query C, (∀ (i j : C.Party) (r : List HashOutput), q ≠ .commit .seedGen i j r) → ¬ CommitCell q :=
    fun q hq ⟨i, j, r, e⟩ => hq i j r e
  refine noCall_map _ _ ?_
  unfold restMid
  refine noCall_bind _ ?_ fun r => noCall_bind _ ?_ fun _ => ?_
  · rw [observe_eq]
    exact noCall_counted_lift D _ _
  · rw [programBlock_eq_view]
    unfold programBlockView
    refine noCall_bind _ (noCall_free_prob D _ _) fun high => noCall_bind _ (noCall_program D _ _ _
      (hnc _ fun _ _ _ h => by cases h)) fun _ =>
      noCall_bind _ ?_ fun _ => noCall_bind _ ?_ fun _ => noCall_pure _ _
    · refine noCall_mapM _ _ _ fun T => ?_
      split
      · exact noCall_program D _ _ _ (hnc _ fun _ _ _ h => by cases h)
      · exact noCall_pure _ _
    · refine noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_
      split_ifs
      · exact noCall_program D _ _ _ (hnc _ fun _ _ _ h => by cases h)
      · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact noCall_bind _ (noCall_counted_lift D _ _) fun _ => noCall_pure _ _

theorem noCall_free_hashQuery_commit (q : Query C) :
    NoCall (OffCall D CommitCell) (free (liftComp (hashQuery q) (LocalSpec C))) :=
  noCall_free_ro D _ _ (noCall_hashQuery_ro D _ _ fun ⟨i, j, r, _, _, e⟩ => ⟨i, j, r, e⟩)

theorem ctxEq_commitDraws (prims : Primitives) (commitAt : C.Party → C.Party → Query C)
    (hshape : ∀ i j, i ∉ D.1 → j ∉ D.1 → CommitCell (commitAt i j)) :
    CtxEq prims D (commitDrawsZ D commitAt) (commitDrawsN D commitAt) := by
  unfold commitDrawsZ commitDrawsN
  refine CtxEq.sequenceFin prims D (fun i => ?_) (fun i => ?_)
  · by_cases hi : i ∈ D.1
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact CtxEq.refl prims D _
    · simp only [hi, ite_false]
      refine CtxEq.mapM prims D _ (fun j => ?_) (fun j => noCall_map _ _ (noCall_free_hashQuery_commit D _))
      by_cases hj : j ∈ D.1
      · have e1 : ((fun a => if j ∈ D.1 then a else 0) <$> free (liftComp (hashQuery (commitAt i j)) (LocalSpec C))) =
            free (liftComp (hashQuery (commitAt i j)) (LocalSpec C)) := by simp [hj]
        rw [e1, ite_eq_left hj]
        exact CtxEq.refl prims D _
      · simp only [hj, ite_false]
        exact CtxEq.drop prims D (hshape i j hi hj)
  · split_ifs
    · exact noCall_pure _ _
    · exact noCall_mapM _ _ _ fun j => noCall_map _ _ (noCall_free_hashQuery_commit D _)

end Calls

/-! ## The statement -/

section Glue

variable (prims : Primitives)

/-- The law of the round-2 mail of one family of commit cells is the law with the honest pair reads
dropped. -/
theorem wp_listPreAt_drop (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (commitAt : C.Party → C.Party → Query C) (hshape : ∀ i j, i ∉ D.1 → j ∉ D.1 → CommitCell (commitAt i j))
    (G : Option (C.Party → C.Party → Option (Msg E)) → ℝ≥0∞) (s : LogState C) :
    wp ((simulateQ (loggedWorld prims D) (listPreAt D net state early parameter dealt parts commitAt)).run s)
        (fun z => G (z.1.2.2.map Prod.snd)) =
      wp ((simulateQ (loggedWorld prims D) (commitDrawsN D commitAt >>= fun cm =>
        (fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$> restMid D net state early parameter dealt parts cm)).run s)
        (fun z => G z.1) := by
  have e : (fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$>
      listPreAt D net state early parameter dealt parts commitAt =
      commitDrawsZ D commitAt >>= fun cm =>
        (fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$> restMid D net state early parameter dealt parts cm := by
    rw [listPreAt_eq_rest, map_bind, ← commitDrawsAt_mask, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun cm hcm => ?_
    exact restMid_mask D net state early parameter dealt parts cm (length_commitDrawsAt D commitAt cm hcm)
  have e2 : wp ((simulateQ (loggedWorld prims D) (listPreAt D net state early parameter dealt parts commitAt)).run s)
      (fun z => G (z.1.2.2.map Prod.snd)) =
      wp ((simulateQ (loggedWorld prims D) ((fun m : ListMid C E net.State => m.2.2.map Prod.snd) <$>
        listPreAt D net state early parameter dealt parts commitAt)).run s) (fun z => G z.1) := by
    rw [simulateQ_map, StateT.run_map, wp_map]
    rfl
  rw [e2, e]
  exact ctxEq_commitDraws D prims commitAt hshape _ (fun cm => noCall_restMid D net state early parameter dealt parts cm)
    G s

/-- The proof of `MidCommitLaw`. -/
theorem midCommitLaw : MidCommitLaw (C := C) (E := E) prims := by
  intro D net state early parameter dealt parts commitAt commitAt' s h1 h2
  have hshape : ∀ i j, i ∉ D.1 → j ∉ D.1 → CommitCell (commitAt i j) := fun i j hi hj => by
    obtain ⟨r, r', e, -⟩ := h2 i j hi hj
    exact ⟨i, j, r, e⟩
  have hshape' : ∀ i j, i ∉ D.1 → j ∉ D.1 → CommitCell (commitAt' i j) := fun i j hi hj => by
    obtain ⟨r, r', -, e⟩ := h2 i j hi hj
    exact ⟨i, j, r', e⟩
  intro p
  rw [prEvent_map, prEvent_map, prEvent_eq_wp_indicator, prEvent_eq_wp_indicator]
  rw [wp_listPreAt_drop prims D net state early parameter dealt parts commitAt hshape (fun o => if p o then 1 else 0) s,
    wp_listPreAt_drop prims D net state early parameter dealt parts commitAt' hshape' (fun o => if p o then 1 else 0) s,
    commitDrawsN_congr D commitAt commitAt' h1]

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.midCommitLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.midCommitLaw
