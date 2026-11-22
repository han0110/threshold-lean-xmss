import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.Walk

/-!
# One key for each hidden name in a setup

`Draws.setupRounds_oneKey` states that after the commit round and the reveal round of one
synchronized PRSS setup each honest operator aborted or waits at its echo, and that for each hidden
name its holders hold the cached answer of one derive input. `Draws.executePhase_oneKey` carries this
through a phase whose honest programs start with a setup, with the static walk `CellsIn`. The theorems
`ledgerHidden` and `hiddenNames` follow.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace Draws

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

variable (D : C.Coalition)

/-! ## The static walk

A property `Inv` of the world that each free call outside a local predicate `bad` keeps holds through
the rounds, when each honest step makes no call of `bad` and each call of `bad` is in class `stream`. -/

section Static

variable (prims : Primitives)

open SetupBudgets (HonestP PartyP)

/-- Each hidden cell of the world is under a name and a key that `A` allows. -/
def CellsIn (A : KeyName C → HashOutput → Prop) (w : StreamState C) : Prop :=
  ∀ name key ρ idx position, w.2 ((name, key), ρ, idx, position) ≠ none → A name key

/-- A free `PRG` call under a hidden name that `A` does not allow. -/
def WorldBad (A : KeyName C → HashOutput → Prop) : (WorldSpec C).Domain → Prop
  | .inr t => BadDraw D A t
  | _ => False

theorem streamWorld_cellsIn (A : KeyName C → HashOutput → Prop) (t : (WorldSpec C).Domain)
    (ht : ¬ WorldBad D A t) (w : StreamState C) (hw : CellsIn A w) :
    ∀ y ∈ support ((streamWorld prims D t).run w), CellsIn A y.2 := by
  intro y hy
  rcases t with ((u | p) | (u | q | x))
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · change y ∈ support ((if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w) at hy
    split_ifs at hy with hx
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      intro name key ρ idx position hcell
      rcases FirstCounts.randomOracle_cells _ _ r hr _ hcell with h | h
      · exact hw name key ρ idx position h
      · have h1 : name = x.1 := congrArg (fun y => y.1.1) h
        have h2 : key = x.2.1 := congrArg (fun y => y.1.2) h
        subst h1 h2
        by_contra hA
        exact ht ⟨hx, hA⟩
    · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
      exact hw

variable {prims}

/-- A computation of the world with no call of `p` keeps `Inv`, when each call of `bad` is a call of
`p`. -/
theorem inv_of_noCall {bad : (LocalSpec C).Domain → Prop} {Inv : StreamState C → Prop}
    (hstep : ∀ t, ¬ HonestP bad t → ∀ w, Inv w → ∀ y ∈ support ((streamWorld prims D t).run w), Inv y.2)
    (p : (WorldSpec C).Domain → Prop) (hp : ∀ t, HonestP bad t → p t) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    IsQueryBoundP oa p 0 → ∀ w, Inv w → ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run w), Inv z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ w hw z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  | query_bind t f ih =>
    intro h w hw z hz
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hpt : ¬ p t := h.1.resolve_right (lt_irrefl 0)
    have hcont : IsQueryBoundP (f y.1) p 0 := by simpa only [hpt, ite_false] using h.2 y.1
    exact ih y.1 hcont y.2 (hstep t (fun hb => hpt (hp t hb)) w hw y hy) z hz

theorem free_honestP (bad : (LocalSpec C).Domain → Prop) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP oa bad 0 → IsQueryBoundP (free oa) (HonestP bad) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; trivial
  | query_bind t k ih =>
    intro h
    rw [isQueryBoundP_query_bind_iff] at h
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    have ht : ¬ bad t := h.1.resolve_right (lt_irrefl 0)
    refine ⟨Or.inl ht, fun u => ?_⟩
    have hu := ih u (by simpa only [ht, ite_false] using h.2 u)
    simpa only [show ¬ HonestP bad (.inr t) from ht, ite_false] using hu

/-- The continuation of a stopped program makes no call of `bad`. -/
def StepNo (bad : (LocalSpec C).Domain → Prop) {α : Type} : Step C E RealSpec α → Prop
  | .wait _ resume => ∀ inbox, IsQueryBoundP (resume inbox) (PartyP bad) 0
  | _ => True

/-- The local work of the next round of a stopped program makes no call of `bad`. -/
def RoundNo (bad : (LocalSpec C).Domain → Prop) {α : Type} : Step C E RealSpec α → Prop
  | .wait _ resume => ∀ inbox, IsQueryBoundP (advance (resume inbox)) bad 0
  | _ => True

theorem advance_no (bad : (LocalSpec C).Domain → Prop) {α : Type}
    (oa : OracleComp (PartySpec C E RealSpec) (Option α)) :
    IsQueryBoundP oa (PartyP bad) 0 →
      IsQueryBoundP (advance oa) bad 0 ∧ ∀ step ∈ support (advance oa), StepNo bad step := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro _
    refine ⟨trivial, fun step hs => ?_⟩
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    trivial
  | query_bind t k ih =>
    intro h
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · have ht : ¬ bad q := h.1.resolve_right (lt_irrefl 0)
      have hk : ∀ u, IsQueryBoundP (k u) (PartyP bad) 0 := fun u => by
        simpa only [show ¬ PartyP (E := E) bad (.inl (.inl q)) from ht, ite_false] using h.2 u
      change IsQueryBoundP (advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inl q))) >>= k)) _ _ ∧ ∀ step ∈ support (advance (OracleComp.lift
          (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl q))) >>= k)), _
      rw [advance_query_bind]
      refine ⟨(isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl ht, fun u => ?_⟩, fun step hs => ?_⟩
      · simpa only [ht, ite_false] using (ih u (hk u)).1
      · rw [mem_support_bind_iff] at hs
        obtain ⟨u, -, hu⟩ := hs
        exact (ih u (hk u)).2 step hu
    · have hk : ∀ u, IsQueryBoundP (k u) (PartyP bad) 0 := fun u => by
        simpa only [show ¬ PartyP (E := E) bad (.inl (.inr outbox)) from id, ite_false] using h.2 u
      change IsQueryBoundP (pure (Step.wait outbox k) : OracleComp (LocalSpec C) _) _ _ ∧
        ∀ step ∈ support (pure (Step.wait outbox k) : OracleComp (LocalSpec C) _), _
      refine ⟨trivial, fun step hs => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact hk
    · exact input.elim

theorem StepNo.roundNo {bad : (LocalSpec C).Domain → Prop} {α : Type} {step : Step C E RealSpec α}
    (h : StepNo bad step) : RoundNo bad step := by
  rcases step with _ | ⟨outbox, resume⟩ | _
  · trivial
  · exact fun inbox => (advance_no bad _ (h inbox)).1
  · trivial

/-- One round keeps `Inv` when the local work of each honest step makes no call of `bad`. -/
theorem stepRound_inv {Ia α : Type} {bad : (LocalSpec C).Domain → Prop} {Inv : StreamState C → Prop}
    (hstep : ∀ t, ¬ HonestP bad t → ∀ w, Inv w → ∀ y ∈ support ((streamWorld prims D t).run w), Inv y.2)
    (hq : ∀ t, bad t → InClass .stream t) (B : Adversary C E Ia PEmpty PEmpty)
    (st : B.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ j, j ∉ D.1 → RoundNo bad (steps j))
    (w : StreamState C) (hw : Inv w)
    (y : (B.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D B noFunctionality st steps)).run w)) :
    Inv y.2 := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRound at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, ha, v, hv, rfl⟩ := hy
  have ha' : Inv a.2 := inv_of_noCall D hstep (HonestIn .stream)
    (fun t ht => by
      rcases t with _ | u
      · exact ht.elim
      · exact hq u ht) _ (DigestBudgets.honestIn_adversary .stream _) w hw a ha
  refine (sequenceFin_keeps D prims Inv a.2 (fun _ _ _ => True) _ (fun _ _ _ _ _ _ => trivial)
    (fun j w' u _ hw' hu => ⟨?_, trivial⟩) a.2 v le_rfl ha' hv).1
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact hw'
  · by_cases hj : j ∈ D.1
    · simp only [hsj, hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact hw'
    · simp only [hsj, hj, ↓reduceIte] at hu
      have hr := hsteps j hj
      rw [hsj] at hr
      exact inv_of_noCall D hstep (HonestP bad) (fun _ h => h) _ (free_honestP bad _ (hr _)) w' hw' u hu
  · exact input.elim

/-- One round keeps `StepNo bad` at each honest operator. -/
theorem stepRound_stepNo {Ia α : Type} (bad : (LocalSpec C).Domain → Prop) (B : Adversary C E Ia PEmpty PEmpty)
    (st : B.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ j, j ∉ D.1 → StepNo bad (steps j))
    (w : StreamState C)
    (y : (B.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D B noFunctionality st steps)).run w)) :
    ∀ j, j ∉ D.1 → StepNo bad (y.1.2.1 j) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRound at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, -, v, hv, rfl⟩ := hy
  refine sequenceFin_streamWorld prims D (fun j next _ => j ∉ D.1 → StepNo bad next) _
    (fun _ _ _ _ h _ => h) (fun j w' u hu hj => ?_) a.2 v hv
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    trivial
  · simp only [hsj, hj, ↓reduceIte] at hu
    have hr := hsteps j hj
    rw [hsj] at hr
    have hmem : u.1 ∈ support (advance (OptionT.mk (resume (roundInbox D a.1.2 steps j))).run) :=
      mem_support_advance_of_handler (streamWorld prims D) _ w' _ (by
        rw [StateT.run'_eq, support_map]
        exact ⟨u, hu, rfl⟩)
    exact (advance_no bad _ (hr _)).2 _ hmem
  · exact input.elim

/-- The rounds keep `Inv` when each honest step makes no call of `bad`. -/
theorem executeRounds_inv {Ia α : Type} {bad : (LocalSpec C).Domain → Prop} {Inv : StreamState C → Prop}
    (hstep : ∀ t, ¬ HonestP bad t → ∀ w, Inv w → ∀ y ∈ support ((streamWorld prims D t).run w), Inv y.2)
    (hq : ∀ t, bad t → InClass .stream t) (B : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (st : B.State) (steps : C.Party → Step C E RealSpec α) (w : StreamState C),
      (∀ j, j ∉ D.1 → StepNo bad (steps j)) → Inv w →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (executeRounds worldRoles D B noFunctionality fuel st steps)).run w),
        Inv z.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro st steps w _ hw z hz
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  | succ fuel ih =>
    intro st steps w hs hw z hz
    unfold executeRounds at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hw
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      exact ih y.1.1 y.1.2.1 y.2 (stepRound_stepNo D bad B st steps hs w y hy)
        (stepRound_inv D hstep hq B st steps (fun j hj => (hs j hj).roundNo) w hw y hy) z hz

end Static

/-! ## The steps of a PRSS setup with a continuation -/

section SetupSteps

attribute [local instance] Set.monad

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mapM noCall_query)
open SetupAgree (cacheAnswer StepNext mem_setBind prssOf)

variable {β : Type}

/-- The first step of a PRSS setup with the continuation `R` on its keys. -/
def commitStepK (i : C.Party) (own : Parts C) (commitments : List HashOutput) (R : PrssKeys C → PartyM C E RealSpec β) :
    Step C E RealSpec β :=
  .wait (commitOutbox i commitments) (exchangeResume fun committed =>
    exchange (revealOutbox .prss i own) >>= fun revealed =>
      setupRest .prss i own committed revealed >>= fun keys => R (prssOf keys))

/-- The step of a PRSS setup after the commit round, with the continuation `R`. -/
def revealStepK (i : C.Party) (own : Parts C) (committed : Mail C E) (R : PrssKeys C → PartyM C E RealSpec β) :
    Step C E RealSpec β :=
  .wait (revealOutbox .prss i own) (exchangeResume fun revealed =>
    setupRest .prss i own committed revealed >>= fun keys => R (prssOf keys))

/-- The step of a PRSS setup after the reveal round, with the derived keys and the continuation `R`. -/
def echoStepK (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (R : PrssKeys C → PartyM C E RealSpec β) : Step C E RealSpec β :=
  .wait (echoOutbox .prss i keys shared) (exchangeResume fun received =>
    require (echoCheck .prss i keys shared received) >>= fun _ => R (prssOf keys))

theorem advance_prssSetup_bind (i : C.Party) (R : PrssKeys C → PartyM C E RealSpec β) :
    advance (prssSetup i >>= R).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .prss i own) (LocalSpec C) >>= fun commitments =>
          pure (commitStepK i own commitments R) := by
  have h : (prssSetup i : PartyM C E RealSpec (PrssKeys C)) = localStep (liftComp sampleParts _) >>= fun own =>
      commitRevealEcho .prss i own >>= fun keys => pure (prssOf keys) := rfl
  rw [h]
  simp only [bind_assoc, pure_bind]
  rw [advance_localStep_bind]
  refine bind_congr fun own => ?_
  rw [advance_setup_start]
  rfl

theorem commit_nextK (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (commitments : List HashOutput) (R : PrssKeys C → PartyM C E RealSpec β) (next : Step C E RealSpec β)
    (h : StepNext s inbox (commitStepK i own commitments R) next) :
    next = .done none ∨ next = revealStepK i own inbox R := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · right
    rw [advance_exchange_bind, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    exact h

theorem reveal_nextK (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (committed : Mail C E) (R : PrssKeys C → PartyM C E RealSpec β) (next : Step C E RealSpec β)
    (h : StepNext s inbox (revealStepK i own committed R) next) :
    next = .done none ∨ (C.parties.any fun j => Msg.isAbort (inbox j)) = false ∧ ∃ keys shared,
      keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss i (setupView .prss i own inbox)) (LocalSpec C)) ∧
      next = echoStepK i keys shared R := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with habort
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · rw [advance_setupRest] at h
    simp only [simulateQ_bind] at h
    obtain ⟨opens, -, h⟩ := mem_setBind.1 h
    split_ifs at h
    · right
      refine ⟨by simpa using habort, ?_⟩
      simp only [simulateQ_bind, simulateQ_pure] at h
      obtain ⟨keys, hkeys, h⟩ := mem_setBind.1 h
      obtain ⟨shared, -, h⟩ := mem_setBind.1 h
      rw [Set.pure_def, Set.mem_singleton_iff] at h
      exact ⟨keys, shared, hkeys, h⟩
    · left
      simpa [Set.pure_def] using h

variable {D}

theorem noBad_of_stream {A : KeyName C → HashOutput → Prop} {γ : Type} {oa : OracleComp (LocalSpec C) γ}
    (h : IsQueryBoundP oa (InClass .stream) 0) : IsQueryBoundP oa (BadDraw D A) 0 :=
  IsQueryBoundP.of_imp (fun t ht => badDraw_stream t ht) h

theorem noBad_hashList {A : KeyName C → HashOutput → Prop} {γ : Type} (l : List γ) (q : γ → Query C) :
    IsQueryBoundP (liftComp (l.mapM fun a => hashQuery (q a)) (LocalSpec C)) (BadDraw D A) 0 :=
  liftComp_ro_noBad _ ((noCall_iff _ _).1 (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => h))

theorem roundOk_commitStepK (A : KeyName C → HashOutput → Prop) (i : C.Party) (own : Parts C)
    (commitments : List HashOutput) (R : PrssKeys C → PartyM C E RealSpec β) :
    RoundNo (BadDraw D A) (commitStepK i own commitments R) := by
  intro inbox
  unfold exchangeResume
  split_ifs
  · trivial
  · rw [advance_exchange_bind]
    trivial

theorem roundOk_revealStepK (A : KeyName C → HashOutput → Prop) (i : C.Party) (own : Parts C)
    (committed : Mail C E) (R : PrssKeys C → PartyM C E RealSpec β) :
    RoundNo (BadDraw D A) (revealStepK i own committed R) := by
  intro inbox
  unfold exchangeResume
  split_ifs
  · trivial
  · rw [advance_setupRest]
    refine isQueryBoundP_bind (n := 0) (m := 0) (noBad_hashList _ _) fun opens _ => ?_
    split_ifs
    · refine isQueryBoundP_bind (n := 0) (m := 0) (liftComp_ro_noBad _ ((noCall_iff _ _).1
        (noCall_roBad_of_stream (DigestBudgets.noCall_deriveKeys (c := .stream) (by decide) _ _)))) fun keys _ => ?_
      exact isQueryBoundP_bind (n := 0) (m := 0) (noBad_hashList _ _) fun _ _ => trivial
    · trivial

theorem stepNoBad_echoStepK (A : KeyName C → HashOutput → Prop) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (R : PrssKeys C → PartyM C E RealSpec β) (hR : NoBad D A (R (prssOf keys))) :
    StepNo (BadDraw D A) (echoStepK i keys shared R) := by
  intro inbox
  unfold exchangeResume
  split_ifs
  · trivial
  · exact NoBad.bind (NoBad.of_class (DigestBudgets.ClassBound.require _)) fun _ => hR

end SetupSteps

/-! ## One key for each hidden name in a setup -/

section OneKey

attribute [local instance] Set.monad

open SetupAgree (cacheAnswer StepNext mem_setBind prssOf mapM_getD mem_hashQuery parties_getElem parties_length)

/-- The key of a held term is the cached derived key of the parts of the term in the view. -/
theorem term_cached {s : HashCache C} (i : C.Party) (view : C.Party → Parts C)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (h : keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss i view) (LocalSpec C))) (T : C.Term)
    (hT : i ∈ C.holders T) :
    s (.derive .prss .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)) =
      some (keys.2.1 T) := by
  unfold deriveKeys at h
  simp only [reduceCtorEq, ↓reduceIte, liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure, pure_bind] at h
  obtain ⟨term, hterm, h⟩ := mem_setBind.1 h
  obtain ⟨pair, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  subst h
  have hmem : T ∈ C.terms := by simp [Committee.terms]
  have hj := mapM_getD _ C.terms term hterm (C.terms.idxOf T) (List.idxOf_lt_length_of_mem hmem) 0
  rw [List.getElem_idxOf] at hj
  simp only [hT, ↓reduceIte] at hj
  exact (mem_hashQuery hj).resolve_left fun ⟨_, hq, _⟩ => by cases hq

/-- The view of `i` of a term part of `h` is the part of `h` that `h` revealed to `i`. -/
theorem setupView_term (i h : C.Party) (hhi : h ≠ i) (own own' : Parts C) (inbox : Mail C E)
    (hrev : inbox h = revealOutbox .prss h own' i) (T : C.Term) (hi : i ∈ C.holders T) (hh : h ∈ C.holders T) :
    (setupView .prss i own inbox h).term T = own'.term T := by
  have hmem : T ∈ sharedTerms h i := by simp [sharedTerms, Committee.terms, hi, hh]
  simp only [setupView, hhi, ↓reduceIte, hrev, revealOutbox, Ne.symm hhi, Msg.hashesOf, readReveal, revealTo,
    reduceCtorEq, List.nil_append, Nat.zero_add]
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_left (by simp [List.idxOf_lt_length_of_mem hmem])]
  simp

/-- The derive input of a PRSS key of the name `N` from the parts `own` of the operators. -/
def deriveInput (own : C.Party → Parts C) : KeyName C → Query C
  | .parameter => .derive .prss .parameter []
  | .term T => .derive .prss .term ((C.parties.filter (· ∈ C.holders T)).map fun h => (own h).term T)
  | .pair p => .derive .prss .pair [(own p.1.1).pair p.1.2, (own p.1.2).pair p.1.1]

theorem pairOf_ends (i j : C.Party) (h : i ≠ j) :
    ((C.pairOf i j h).1.1 = i ∧ (C.pairOf i j h).1.2 = j) ∨ ((C.pairOf i j h).1.1 = j ∧ (C.pairOf i j h).1.2 = i) := by
  unfold Committee.pairOf
  split_ifs <;> simp

variable (prims : Primitives) {β : Type}

/-- The commit round of a synchronized PRSS setup. Each honest operator aborted or waits at its
reveal. -/
theorem commitRound_shape (G : C.Party → (PrssKeys C → PartyM C E RealSpec β) → Prop)
    (B : Adversary C E Unit PEmpty PEmpty) (st : B.State) (steps : C.Party → Step C E RealSpec β)
    (h0 : ∀ j, j ∉ D.1 → steps j = .done none ∨ ∃ own commitments R, steps j = commitStepK j own commitments R ∧ G j R)
    (w : StreamState C)
    (q1 : (B.State × (C.Party → Step C E RealSpec β) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hq1 : q1 ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D B noFunctionality st steps)).run w)) :
    ∀ j, j ∉ D.1 → q1.1.2.1 j = .done none ∨
      ∃ own committed R, q1.1.2.1 j = revealStepK j own committed R ∧ G j R := by
  have hn1 := (SetupAgree.stepRound_cache prims D B st steps w q1 hq1).2
  intro j hj
  rcases h0 j hj with h | ⟨own, commitments, R, h, hG⟩
  · have hs := hn1 j hj q1.2.1 le_rfl
    rw [h] at hs
    exact Or.inl hs
  · have hs := hn1 j hj q1.2.1 le_rfl
    rw [h] at hs
    rcases commit_nextK q1.2.1 _ j own commitments R _ hs with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨own, _, R, h', hG⟩

/-- One synchronized PRSS setup, two rounds from its start. The honest operators start the setup in
the same round, each with its own continuation, or they aborted. After the commit round and the reveal
round each honest operator aborted or waits at its echo with derived keys. For each hidden name there
is one derive input, and each such operator holds under that name the cached answer of that input. So
the holders of a hidden name hold one key, on each outcome. -/
theorem setupRounds_oneKey (G : C.Party → (PrssKeys C → PartyM C E RealSpec β) → Prop)
    (B : Adversary C E Unit PEmpty PEmpty) (st : B.State) (steps : C.Party → Step C E RealSpec β)
    (h0 : ∀ j, j ∉ D.1 → steps j = .done none ∨ ∃ own commitments R, steps j = commitStepK j own commitments R ∧ G j R)
    (w : StreamState C)
    (q1 : (B.State × (C.Party → Step C E RealSpec β) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hq1 : q1 ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D B noFunctionality st steps)).run w))
    (q2 : (B.State × (C.Party → Step C E RealSpec β) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hq2 : q2 ∈ support ((simulateQ (streamWorld prims D)
      (stepRound worldRoles D B noFunctionality q1.1.1 q1.1.2.1)).run q1.2)) :
    ∃ input : KeyName C → Query C, ∀ j, j ∉ D.1 → q2.1.2.1 j = .done none ∨
      ∃ keys shared R, q2.1.2.1 j = echoStepK j keys shared R ∧ G j R ∧
        ∀ N k, Hidden D N → NameKey j (prssOf keys) N k → q2.2.1 (input N) = some k := by
  classical
  have hn2 := (SetupAgree.stepRound_cache prims D B q1.1.1 q1.1.2.1 q1.2 q2 hq2).2
  have hdone : ∀ (s : HashCache C) (m : Mail C E) (a b : Step C E RealSpec β), a = .done none → StepNext s m a b →
      b = .done none := fun s m a b ha hb => by
    subst ha
    exact hb
  have h1 := commitRound_shape D prims G B st steps h0 w q1 hq1
  let ownOf : C.Party → Parts C := fun h =>
    if H : ∃ own committed R, q1.1.2.1 h = revealStepK h own committed R ∧ G h R then H.choose
    else ⟨0, fun _ => 0, fun _ => 0⟩
  have hown : ∀ h, (∃ own committed R, q1.1.2.1 h = revealStepK h own committed R ∧ G h R) →
      ∃ committed R, q1.1.2.1 h = revealStepK h (ownOf h) committed R ∧ G h R := by
    intro h H
    simp only [ownOf, H, ↓reduceDIte]
    exact H.choose_spec
  refine ⟨deriveInput ownOf, fun j hj => ?_⟩
  rcases h1 j hj with h | H
  · exact Or.inl (hdone _ _ _ _ h (hn2 j hj q2.2.1 le_rfl))
  obtain ⟨committed, R, hr, hG⟩ := hown j H
  have hs := hn2 j hj q2.2.1 le_rfl
  rw [hr] at hs
  rcases reveal_nextK q2.2.1 _ j (ownOf j) committed R _ hs with h' | ⟨habort, keys, shared, hkeys, h'⟩
  · exact Or.inl h'
  refine Or.inr ⟨keys, shared, R, h', hG, ?_⟩
  -- The reveal of each other honest operator reached `j`.
  have hrev : ∀ h, h ∉ D.1 → h ≠ j →
      roundInbox D q2.1.2.2 q1.1.2.1 j h = revealOutbox .prss h (ownOf h) j := by
    intro h hh hhj
    rcases h1 h hh with hd | H'
    · exfalso
      have hab : Msg.isAbort (roundInbox D q2.1.2.2 q1.1.2.1 j h) = true := by
        simp [roundInbox, hh, hd, Msg.isAbort]
      have := List.any_eq_false.1 habort h (List.mem_finRange h)
      rw [hab] at this
      exact this rfl
    · obtain ⟨c', R', hr', -⟩ := hown h H'
      simp [roundInbox, hh, hr', revealStepK]
  have hview : setupView .prss j (ownOf j) (roundInbox D q2.1.2.2 q1.1.2.1 j) j = ownOf j := by
    simp [setupView]
  intro N k hN hk
  rcases hk with ⟨T, hT, rfl, rfl⟩ | ⟨j', hj', rfl, rfl⟩
  · show _ = some (keys.2.1 T)
    rw [← term_cached j _ keys hkeys T hT]
    simp only [deriveInput]
    congr 2
    refine List.map_congr_left fun h hmem => ?_
    have hhT : h ∈ C.holders T := by simpa using (List.mem_filter.1 hmem).2
    have hhD : h ∉ D.1 := fun hD => hN ⟨h, hD, hhT⟩
    by_cases hhj : h = j
    · subst hhj
      rw [hview]
    · exact (setupView_term j h hhj _ _ _ (hrev h hhD hhj) T hT hhT).symm
  · have hc := SetupAgree.pair_cached j _ keys hkeys j' hj'
    simp only [prssOf]
    rw [← hc]
    simp only [deriveInput]
    obtain ⟨hD1, hD2⟩ := hN
    have hjj' : j ≠ j' := Ne.symm hj'
    rcases pairOf_ends j j' hjj' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      rw [e1] at hD1
      rw [e2] at hD2
      rw [hview, SetupAgree.setupView_pair j j' hjj' _ _ _ (hrev j' hD2 hj') j]
    · rw [e1, e2]
      rw [e1] at hD1
      rw [e2] at hD2
      rw [hview, SetupAgree.setupView_pair j j' hjj' _ _ _ (hrev j' hD1 hj') j]

end OneKey

/-! ## One key for each hidden name in a phase that starts with a setup -/

section Ledger

open SetupAgree (prssOf)

variable (prims : Primitives) {β : Type}

/-- Each honest program aborts at once, or it is a PRSS setup and then a program that draws only
under the keys of that setup. -/
def SetupFirst (program : C.Party → PartyM C E RealSpec β) : Prop :=
  ∀ j, j ∉ D.1 → program j = failure ∨
    ∃ R : PrssKeys C → PartyM C E RealSpec β, program j = prssSetup j >>= R ∧ ∀ prss, NoBad D (NameKey j prss) (R prss)

theorem executeRounds_cases {Ia α : Type} (B : Adversary C E Ia PEmpty PEmpty) (n : ℕ) (st : B.State)
    (steps : C.Party → Step C E RealSpec α) (w : StreamState C) (z : (B.State × (C.Party → Option α)) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executeRounds worldRoles D B noFunctionality (n + 1) st steps)).run w)) :
    z.2 = w ∨ ∃ q ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D B noFunctionality st steps)).run w),
      z ∈ support ((simulateQ (streamWorld prims D)
        (executeRounds worldRoles D B noFunctionality n q.1.1 q.1.2.1)).run q.2) := by
  rw [executeRounds] at hz
  split_ifs at hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact Or.inr ⟨q, hq, hz⟩

theorem executeRounds_zero_world {Ia α : Type} (B : Adversary C E Ia PEmpty PEmpty) (st : B.State)
    (steps : C.Party → Step C E RealSpec α) (w : StreamState C) (z : (B.State × (C.Party → Option α)) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executeRounds worldRoles D B noFunctionality 0 st steps)).run w)) : z.2 = w := by
  simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

variable {D}

/-- The first steps of programs that start with a setup. Each honest operator aborted or waits at the
commit round, and no hidden cell is written. -/
theorem startSteps_setupFirst (program : C.Party → PartyM C E RealSpec β) (h : SetupFirst D program)
    (A : KeyName C → HashOutput → Prop) (w : StreamState C) (hw : CellsIn A w)
    (a : (C.Party → Step C E RealSpec β) × StreamState C)
    (ha : a ∈ support ((simulateQ (streamWorld prims D) (startSteps worldRoles D program)).run w)) :
    CellsIn A a.2 ∧ ∀ j, j ∉ D.1 → a.1 j = .done none ∨
      ∃ own commitments R, a.1 j = commitStepK j own commitments R ∧ ∀ prss, NoBad D (NameKey j prss) (R prss) := by
  unfold startSteps at ha
  refine sequenceFin_keeps D prims (CellsIn A) w (fun j v _ => j ∉ D.1 → v = (Step.done none : Step C E RealSpec β) ∨
      ∃ own commitments R, v = commitStepK j own commitments R ∧ ∀ prss, NoBad D (NameKey j prss) (R prss)) _
    (fun _ _ _ _ h _ => h) (fun j w' u _ hw' hu => ?_) w a le_rfl hw ha
  by_cases hj : j ∈ D.1
  · simp only [hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨hw', fun h => absurd hj h⟩
  simp only [hj, ↓reduceIte] at hu
  rcases h j hj with hf | ⟨R, hR, hnb⟩
  · rw [hf, advance_run_failure] at hu
    simp only [worldRoles, free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨hw', fun _ => Or.inl rfl⟩
  rw [hR] at hu
  have hadv : IsQueryBoundP (advance (prssSetup j >>= R).run) (BadDraw D A) 0 := by
    rw [advance_prssSetup_bind]
    exact isQueryBoundP_bind (n := 0) (m := 0) (noBad_of_stream (DigestBudgets.liftComp_prob_bound .stream _))
      fun own _ => isQueryBoundP_bind (n := 0) (m := 0) (noBad_hashList _ _) fun _ _ => trivial
  refine ⟨inv_of_noCall D (streamWorld_cellsIn D prims A) (WorldBad D A) (fun _ h => h) _
    (free_honestP (BadDraw D A) _ hadv) w' hw' u hu,
    fun _ => Or.inr ?_⟩
  have hmem : u.1 ∈ support (advance (prssSetup j >>= R).run) :=
    mem_support_advance_of_handler (streamWorld prims D) _ w' _ (by
      rw [StateT.run'_eq, support_map]
      exact ⟨u, hu, rfl⟩)
  rw [advance_prssSetup_bind] at hmem
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨own, -, commitments, -, he⟩ := hmem
  exact ⟨own, commitments, R, he, hnb⟩

/-- A phase whose honest programs start with a PRSS setup writes, under each hidden name, hidden
cells under at most one new key. Each new cell is under the cached answer of one derive input of its
name. It holds on each outcome, also with an abort at each point. -/
theorem executePhase_oneKey (B : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (st : B.State)
    (program : C.Party → PartyM C E RealSpec β) (h : SetupFirst D program) (w : StreamState C) :
    ∀ r ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D B noFunctionality fuel st program)).run w),
      ∃ input : KeyName C → Query C, CellsIn (fun N k =>
        (∃ ρ idx position, w.2 ((N, k), ρ, idx, position) ≠ none) ∨ r.2.1 (input N) = some k) r.2 := by
  intro r hr
  unfold executePhase at hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  let Old : KeyName C → HashOutput → Prop := fun N k => ∃ ρ idx position, w.2 ((N, k), ρ, idx, position) ≠ none
  have hw0 : CellsIn Old w := fun N k ρ idx position hc => ⟨ρ, idx, position, hc⟩
  obtain ⟨ha1, ha2⟩ := startSteps_setupFirst prims program h Old w hw0 a ha
  have hstop : CellsIn Old r.2 → ∃ input : KeyName C → Query C, CellsIn (fun N k => Old N k ∨ r.2.1 (input N) = some k) r.2 :=
    fun hc => ⟨fun _ => .derive .prss .parameter [], fun N k ρ idx position hcell => Or.inl (hc N k ρ idx position hcell)⟩
  rcases fuel with _ | fuel
  · exact hstop (by rw [executeRounds_zero_world D prims B st a.1 a.2 r hr]; exact ha1)
  rcases executeRounds_cases D prims B fuel st a.1 a.2 r hr with he | ⟨q1, hq1, hr⟩
  · exact hstop (by rw [he]; exact ha1)
  have hq1c : CellsIn Old q1.2 := stepRound_inv D (streamWorld_cellsIn D prims Old) badDraw_stream B st a.1 (fun j hj => by
    rcases ha2 j hj with hd | ⟨own, commitments, R, he, -⟩
    · rw [hd]; trivial
    · rw [he]; exact roundOk_commitStepK Old j own commitments R) a.2 ha1 q1 hq1
  have h1 := commitRound_shape D prims _ B st a.1 ha2 a.2 q1 hq1
  rcases fuel with _ | fuel
  · exact hstop (by rw [executeRounds_zero_world D prims B _ _ _ r hr]; exact hq1c)
  rcases executeRounds_cases D prims B fuel _ _ _ r hr with he | ⟨q2, hq2, hr⟩
  · exact hstop (by rw [he]; exact hq1c)
  have hq2c : CellsIn Old q2.2 := stepRound_inv D (streamWorld_cellsIn D prims Old) badDraw_stream B _ _ (fun j hj => by
    rcases h1 j hj with hd | ⟨own, committed, R, he, -⟩
    · rw [hd]; trivial
    · rw [he]; exact roundOk_revealStepK Old j own committed R) q1.2 hq1c q2 hq2
  obtain ⟨input, hk⟩ := setupRounds_oneKey D prims _ B st a.1 ha2 a.2 q1 hq1 q2 hq2
  let A₂ : KeyName C → HashOutput → Prop := fun N k => Old N k ∨ q2.2.1 (input N) = some k
  have hsteps : ∀ j, j ∉ D.1 → StepNo (BadDraw D A₂) (q2.1.2.1 j) := by
    intro j hj
    rcases hk j hj with hd | ⟨keys, shared, R, he, hG, hkey⟩
    · rw [hd]; trivial
    · rw [he]
      refine stepNoBad_echoStepK A₂ j keys shared R (IsQueryBoundP.of_imp (fun t ht => ?_) (hG (prssOf keys)))
      rcases t with ((_ | _ | x) | _) | _
      · exact ht.elim
      · exact ht.elim
      · exact ⟨ht.1, fun hn => ht.2 (Or.inr (hkey _ _ ht.1 hn))⟩
      · exact ht.elim
      · exact ht.elim
  have hfin := executeRounds_inv D (streamWorld_cellsIn D prims A₂) badDraw_stream B fuel _ _ q2.2 hsteps
    (fun N k ρ idx position hc => Or.inl (hq2c N k ρ idx position hc)) r hr
  have hle : q2.2.1 ≤ r.2.1 := streamWorld_run_mono prims D _ q2.2 r hr
  exact ⟨input, fun N k ρ idx position hc => (hfin N k ρ idx position hc).imp id fun h' => hle h'⟩

end Ledger

section CeremonyLedger

variable {D} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The honest programs of one ceremony start with a PRSS setup. -/
theorem ceremonyProgram_setupFirst {σ : Type} (c : CeremonyStart C σ) :
    SetupFirst D fun i => ceremonyProgram K circuits settings i c := by
  intro j _
  beta_reduce
  unfold ceremonyProgram
  split
  · rename_i keys _
    obtain ⟨f, hf, hnb⟩ := ceremonyRun_split (D := D) K circuits settings j keys c.jobs
    refine Or.inr ⟨fun prss => (f prss).run c.counters >>= fun p =>
      p.1.elim failure fun outputs => pure (outputs, p.2), ?_, fun prss => NoBad.bind (hnb prss _) fun p => ?_⟩
    · rw [hf, StateT.run_bind, StateT.run_lift, bind_assoc]
      simp only [pure_bind, bind_assoc]
    · rcases p with ⟨_ | outputs, counters⟩
      · exact NoBad.of_class DigestBudgets.ClassBound.failure
      · exact NoBad.of_class (DigestBudgets.ClassBound.pure _)
  · exact Or.inl rfl


end CeremonyLedger

end Draws

/-! ## One key under each hidden name, and the count of the names -/

section Leaves

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The ledger of the hidden keys. One ceremony adds at most one key under each hidden name, on each
outcome. -/
theorem ledgerHidden : LedgerHidden prims K circuits settings := by
  intro D net rounds n c world hb r hr
  obtain ⟨input, hc⟩ := Draws.executePhase_oneKey prims net rounds c.adversary _
    (Draws.ceremonyProgram_setupFirst K circuits settings c) world r hr
  intro N
  obtain ⟨K0, hK0, hcells⟩ := hb N
  refine ⟨K0 ∪ (r.2.1 (input N)).toFinset, ?_, fun key ρ idx position hcell => ?_⟩
  · calc (K0 ∪ (r.2.1 (input N)).toFinset).card ≤ K0.card + (r.2.1 (input N)).toFinset.card :=
          Finset.card_union_le _ _
      _ ≤ n + 1 := by
          gcongr
          cases r.2.1 (input N) <;> simp
  · rcases hc N key ρ idx position hcell with ⟨ρ', idx', position', hold⟩ | hnew
    · exact Finset.mem_union_left _ (hcells key ρ' idx' position' hold)
    · exact Finset.mem_union_right _ (Option.mem_toFinset.2 hnew)

omit [Field E] [Algebra Bit E] in
/-- The hidden names exclude the parameter and number at most the PRSS keys of one setup, the terms
and the pairs. -/
theorem hiddenNames : HiddenNames C := by
  intro D
  refine ⟨(Finset.univ : Finset C.Term).map ⟨KeyName.term, fun _ _ h => KeyName.term.inj h⟩ ∪
    (Finset.univ : Finset C.Pair).map ⟨KeyName.pair, fun _ _ h => KeyName.pair.inj h⟩, ?_, fun name h => ?_⟩
  · refine (Finset.card_union_le _ _).trans (le_of_eq ?_)
    rw [Finset.card_map, Finset.card_map, Finset.card_univ, Finset.card_univ, ThresholdLeanXmssSecurity.card_term,
      TprfSecurityProof.card_pair]
    rfl
  · cases name with
    | parameter => exact h.elim
    | term T => exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ (Finset.mem_univ T))
    | pair p => exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ (Finset.mem_univ p))

end Leaves

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerHidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerHidden

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.hiddenNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.hiddenNames

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Draws.setupRounds_oneKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Draws.setupRounds_oneKey
