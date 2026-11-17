import ThresholdLeanXmssSecurity.Proof.PrssRand.KeyHop

/-!
# The PRSS setup makes no free stream call under a hidden name

`streamWorld` answers each free stream call under a hidden name from a lazy uniform table. A
computation with no such call runs in `streamWorld` as in `worldAnswer`, and the table stays as it
is (`streamWorld_run_of_noHidden`).

* `executePhase_free` is the frame of a phase on the real network. A free call in `Q` comes only from
  a local call of an honest program in `Q`, because the adversary is on the counted copy and a
  functionality with the input type `PEmpty` never runs.
* `setupKeys_partyFree` states that an operator of the PRSS setup hashes only `.commit`, `.derive`
  and `.sharedKeys` queries of the setup, and that it makes no `PRG` call.
* `setupNoStreamKey` states that the honest operators of a PRSS setup make no `PRG` call and hash no
  stream key, from every state of the adversary.
* `setupNoHidden` is the premise of `streamWorld_run_of_noHidden` for the real run of the setup, and
  `streamWorld_setup` is its use.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Free stream calls -/

section Predicate

variable {C : Committee}

/-- A free stream call under a hidden name. -/
def FreeHiddenStream (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr x)) => Hidden D x.1
  | _ => False

/-- A free call that reads the hash cell of a stream key, namely a free hash of a stream key or a
free `PRG` call. -/
def FreeStreamKey : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inl (.streamKey _))) => True
  | .inr (.inr (.inr _)) => True
  | _ => False

/-- A free stream call under a hidden name reads the hash cell of a stream key. -/
theorem freeStreamKey_of_freeHiddenStream (D : C.Coalition) (t : (WorldSpec C).Domain)
    (h : FreeHiddenStream D t) : FreeStreamKey t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals first | exact h.elim | trivial

/-- The steps of the adversary and of the distinguisher are on the counted copy. So they make no free
call, for each computation. -/
theorem isQueryBoundP_adversary_noStreamKey {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) :
    IsQueryBoundP (worldRoles.adversary oa) (FreeStreamKey (C := C)) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

theorem isQueryBoundP_adversary_noHidden (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) :
    IsQueryBoundP (worldRoles.adversary oa) (FreeHiddenStream D) n :=
  (isQueryBoundP_adversary_noStreamKey oa n).of_imp (freeStreamKey_of_freeHiddenStream D)

end Predicate

/-! ## The stream world on a computation with no hidden call -/

section Bridge

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

theorem streamWorld_apply_of_not (t : (WorldSpec C).Domain) (ht : ¬ FreeHiddenStream D t) :
    streamWorld prims D t = onHash (worldAnswer prims t) := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals try rfl
  simp only [FreeHiddenStream] at ht
  simp only [streamWorld, ht, ↓reduceIte]
  rfl

theorem onHash_run {α : Type} (m : StateT (HashCache C) ProbComp α) (h : HashCache C) (hc : HiddenCache C) :
    (onHash m).run (h, hc) = (fun r => (r.1, (r.2, hc))) <$> m.run h := rfl

/-- A computation with no free stream call under a hidden name runs in the stream world as in the
ordinary world, and the hidden table does not change. -/
theorem streamWorld_run_of_noHidden {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hoa : IsQueryBoundP oa (FreeHiddenStream D) 0) (h : HashCache C) (hc : HiddenCache C) :
    (simulateQ (streamWorld prims D) oa).run (h, hc) =
      (fun r => (r.1, (r.2, hc))) <$> (simulateQ (worldAnswer prims) oa).run h := by
  induction oa using OracleComp.inductionOn generalizing h with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeHiddenStream D t := by
      rcases hoa.1 with h' | h'
      · exact h'
      · exact absurd h' (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (FreeHiddenStream D) 0 := fun u => by
      simpa only [ht, ↓reduceIte] using hoa.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, streamWorld_apply_of_not prims D t ht, onHash_run, bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 (hk r.1) r.2

end Bridge

variable {C : Committee} {E : Type}

/-! ## The frame of a phase -/

section Frame

variable {ι : Type} {G : OracleSpec ι} {α : Type}

/-- A local call of an operator program that is a free call in `Q` on the world. -/
def PartyFree (Q : (WorldSpec C).Domain → Prop) : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => Q (.inr t)
  | _ => False

/-- The rest of a stopped program makes no local call in `Q`. -/
def StepFree (Q : (WorldSpec C).Domain → Prop) : Step C E G α → Prop
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyFree (E := E) (G := G) Q) 0
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyFree (E := E) (G := G) Q) 0

/-- If a continuation makes no call in `Q` on each value in `S`, then `oa` with that continuation makes no
call in `Q`. -/
def BindFree (Q : (WorldSpec C).Domain → Prop) {β : Type} (S : β → Prop) (oa : OracleComp (WorldSpec C) β) :
    Prop :=
  ∀ (γ : Type) (k : β → OracleComp (WorldSpec C) γ), (∀ b, S b → IsQueryBoundP (k b) Q 0) →
    IsQueryBoundP (oa >>= k) Q 0

variable (Q : (WorldSpec C).Domain → Prop) (hQ : ∀ t, ¬ Q (.inl (.inl t)))

include hQ in
/-- The steps of the adversary are on the counted copy. -/
theorem isQueryBoundP_adversary_free {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (worldRoles.adversary oa) Q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have hq : (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) = OracleComp.lift (OracleSpec.query t) := rfl
    rw [hq, adversary_bind, adversary_query, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (hQ t), fun u => by simpa only [hQ t, ite_false] using ih u⟩

theorem bindFree_pure {β : Type} (S : β → Prop) (b : β) (hb : S b) : BindFree Q S (pure b) :=
  fun _ k hk => by rw [pure_bind]; exact hk b hb

/-- Advancing a program on the free copy keeps the bound of its rest. -/
theorem bindFree_free_advance (oa : OracleComp (PartySpec C E G) (Option α))
    (h : IsQueryBoundP oa (PartyFree (E := E) (G := G) Q) 0) :
    BindFree Q (StepFree (E := E) (G := G) Q) (free (advance oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro γ k hk
    rw [advance_pure, free_pure, pure_bind]
    exact hk _ trivial
  | query_bind t f ih =>
    intro γ k hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · have hq : ¬ Q (.inr q) := h.1.resolve_right (lt_irrefl 0)
      have e : free (advance (liftM (OracleSpec.query (Sum.inl (Sum.inl q))) >>= f)) =
          (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>= fun u => free (advance (f u)) := by
        rw [show (liftM (OracleSpec.query (Sum.inl (Sum.inl q))) : OracleComp (PartySpec C E G) _) =
          OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl q))) from rfl,
          advance_query_bind, free_bind]
        rfl
      rw [e, bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl hq, fun u => by
        simpa only [hq, ite_false] using ih u (by simpa only [PartyFree, hq, ite_false] using h.2 u) _ k hk⟩
    · change IsQueryBoundP (free (pure (Step.wait outbox f)) >>= k) Q 0
      rw [free_pure, pure_bind]
      exact hk _ fun inbox => by simpa only [Nat.zero_sub, ite_self] using h.2 inbox
    · change IsQueryBoundP (free (pure (Step.call input f)) >>= k) Q 0
      rw [free_pure, pure_bind]
      exact hk _ fun out => by simpa only [Nat.zero_sub, ite_self] using h.2 out

theorem bindFree_sequenceFin {β : Type} (S : β → Prop) : ∀ {N : ℕ} (ms : Fin N → OracleComp (WorldSpec C) β),
    (∀ i, BindFree Q S (ms i)) → BindFree Q (fun bs => ∀ i, S (bs i)) (OverPermutation.sequenceFin ms)
  | 0, ms, _ => by
    intro γ k hk
    simp only [OverPermutation.sequenceFin, pure_bind]
    exact hk _ fun i => Fin.elim0 i
  | N + 1, ms, h => by
    intro γ k hk
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    exact h 0 _ _ fun b0 hb0 => bindFree_sequenceFin S (fun i : Fin N => ms i.succ) (fun i => h i.succ) _ _
      fun bs hbs => hk _ fun i => Fin.cases hb0 hbs i

variable {Ia L R O : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R)

include hQ in
theorem bindFree_stepRound (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α)
    (h : ∀ j, StepFree Q (steps j)) :
    BindFree Q (fun r => ∀ j, StepFree Q (r.2.1 j)) (stepRound worldRoles D A F state steps) := by
  intro γ k hk
  have hcall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, -, hi⟩, -⟩
    cases hs : steps i with
    | done out => simp [hs, Step.callInput] at hi
    | wait out resume => simp [hs, Step.callInput] at hi
    | call input resume => exact input.elim
  unfold stepRound
  rw [ite_eq_right hcall]
  simp only [bind_assoc]
  refine isQueryBoundP_bind_zero _ _ (isQueryBoundP_adversary_free Q hQ _) fun result => ?_
  refine bindFree_sequenceFin Q (StepFree Q) _ (fun j => ?_) _ _ fun sts hsts => by
    rw [pure_bind]
    exact hk _ hsts
  have hj := h j
  split
  · exact bindFree_pure Q (StepFree Q) (Step.done _) trivial
  · rename_i resume hs
    rw [hs] at hj
    by_cases hD : j ∈ D.1
    · rw [ite_eq_left hD]
      exact bindFree_pure Q (StepFree Q) (Step.done _) trivial
    · rw [ite_eq_right hD, worldRoles_honest]
      exact bindFree_free_advance Q _ (hj _)
  · exact bindFree_pure Q (StepFree Q) (Step.done _) trivial

include hQ in
theorem executeRounds_free : ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α),
    (∀ j, StepFree Q (steps j)) → IsQueryBoundP (executeRounds worldRoles D A F fuel state steps) Q 0
  | 0, _, _, _ => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact bindFree_stepRound Q hQ D A F state steps h _ _ fun ⟨st, sts, _⟩ hr =>
        executeRounds_free fuel st sts hr

include hQ in
/-- A phase on the real network makes no free call in `Q`, when no honest program makes a local call
in `Q`. -/
theorem executePhase_free (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec PEmpty O) α)
    (hp : ∀ i, i ∉ D.1 → IsQueryBoundP (program i).run (PartyFree (E := E) (G := CallSpec PEmpty O) Q) 0) :
    IsQueryBoundP (executePhase worldRoles D A F fuel state program) Q 0 := by
  unfold executePhase startSteps
  refine bindFree_sequenceFin Q (StepFree Q) _ (fun i => ?_) _ _ fun sts hsts =>
    executeRounds_free Q hQ D A F fuel state sts hsts
  by_cases hi : i ∈ D.1
  · rw [ite_eq_left hi]
    exact bindFree_pure Q (StepFree Q) (Step.done _) trivial
  · rw [ite_eq_right hi, worldRoles_honest]
    exact bindFree_free_advance Q _ (hp i hi)

end Frame

/-! ## The program of the PRSS setup -/

section Program

variable {ι : Type} {G : OracleSpec ι}

section Closure

variable (p : (PartySpec C E G).Domain → Prop)

theorem isQueryBoundP_partyBind {β γ : Type} (x : PartyM C E G β) (f : β → PartyM C E G γ)
    (hx : IsQueryBoundP x.run p 0) (hf : ∀ b, IsQueryBoundP (f b).run p 0) :
    IsQueryBoundP (x >>= f).run p 0 := by
  rw [OptionT.run_bind, Option.elimM]
  refine isQueryBoundP_bind_zero _ _ hx fun o => ?_
  cases o with
  | none => exact isQueryBoundP_pure _ _ _
  | some b => exact hf b

theorem isQueryBoundP_partyPure {β : Type} (b : β) : IsQueryBoundP (pure b : PartyM C E G β).run p 0 := by
  rw [OptionT.run_pure]
  exact isQueryBoundP_pure _ _ _

theorem isQueryBoundP_require (condition : Prop) :
    IsQueryBoundP (require condition : PartyM C E G Unit).run p 0 := by
  unfold require
  split_ifs
  · exact isQueryBoundP_partyPure p ()
  · exact isQueryBoundP_pure _ _ _

theorem isQueryBoundP_exchange (hp : ∀ outbox, ¬ p (.inl (.inr outbox))) (outbox : Mail C E) :
    IsQueryBoundP (exchange outbox : PartyM C E G (Mail C E)).run p 0 := by
  unfold exchange
  refine isQueryBoundP_partyBind p _ _ ?_ fun inbox => ?_
  · rw [OptionT.run_lift]
    exact ⟨Or.inl (hp outbox), fun _ => trivial⟩
  · split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_partyPure p inbox

theorem isQueryBoundP_localStep {β : Type} (oa : OracleComp (LocalSpec C) β)
    (h : IsQueryBoundP oa (fun t => p (.inl (.inl t))) 0) :
    IsQueryBoundP (localStep oa : PartyM C E G β).run p 0 := by
  unfold localStep
  rw [OptionT.run_lift]
  refine isQueryBoundP_bind_zero _ _ ?_ fun _ => isQueryBoundP_pure _ _ _
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k : OracleComp (LocalSpec C) _) (PartySpec C E G) =
        (liftM ((PartySpec C E G).query (.inl (.inl t))) : OracleComp (PartySpec C E G) _) >>=
          fun u => liftComp (k u) _ := by
      rw [liftComp_bind]
      rcases t with n | x | x <;> rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => by
      simpa only [Nat.zero_sub, ite_self] using ih u (by simpa only [Nat.zero_sub, ite_self] using h.2 u)⟩

end Closure

/-- A cell of the setup domain of `phase`. -/
def SetupCell (phase : Phase) : Query C → Prop
  | .commit ph _ _ _ => ph = phase
  | .derive ph _ _ => ph = phase
  | .sharedKeys ph _ => ph = phase
  | _ => False

theorem isQueryBoundP_hashQuery (q : Query C) (hq : SetupCell .prss q) :
    IsQueryBoundP (hashQuery q) (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0 := by
  show IsQueryBoundP (liftM ((RoSpec C).query (.inl q)) : OracleComp (RoSpec C) _) _ 0
  rw [isQueryBoundP_query_iff]
  intro h
  cases q <;> first | exact h.elim | exact hq.elim

theorem isQueryBoundP_mapM_zero {κ β : Type} {S : OracleSpec κ} (r : κ → Prop) {δ : Type} (f : δ → OracleComp S β)
    (l : List δ) (h : ∀ x ∈ l, IsQueryBoundP (f x) r 0) : IsQueryBoundP (l.mapM f) r 0 := by
  simpa using queryBound_mapM r f 0 l h

theorem isQueryBoundP_oracleStep {β : Type} (oa : OracleComp (RoSpec C) β)
    (h : IsQueryBoundP oa (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0) :
    IsQueryBoundP (oracleStep oa : PartyM C E G β).run (PartyFree (E := E) (G := G) (FreeStreamKey (C := C))) 0 :=
  isQueryBoundP_localStep _ _ (isQueryBoundP_liftComp_ro _ oa h)

theorem isQueryBoundP_deriveKeys (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys .prss i view) (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0 := by
  unfold deriveKeys
  refine isQueryBoundP_bind_zero _ _ ?_ fun _ => isQueryBoundP_bind_zero _ _ ?_ fun _ =>
    isQueryBoundP_bind_zero _ _ ?_ fun _ => isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_mapM_zero _ _ _ fun T _ => ?_
    split_ifs
    · exact isQueryBoundP_hashQuery _ rfl
    · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_mapM_zero _ _ _ fun j _ => ?_
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_hashQuery _ rfl


theorem commitRevealEcho_partyFree (i : C.Party) (own : Parts C) :
    IsQueryBoundP (commitRevealEcho .prss i own : PartyM C E G _).run
      (PartyFree (E := E) (G := G) (FreeStreamKey (C := C))) 0 := by
  have hx : ∀ outbox : Mail C E, ¬ PartyFree (E := E) (G := G) (FreeStreamKey (C := C)) (.inl (.inr outbox)) :=
    fun _ h => h
  unfold commitRevealEcho
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_oracleStep _
    (isQueryBoundP_mapM_zero _ _ _ fun j _ => isQueryBoundP_hashQuery _ rfl)) fun commitments => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_exchange _ hx _) fun committed => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_exchange _ hx _) fun revealed => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_oracleStep _
    (isQueryBoundP_mapM_zero _ _ _ fun j _ => isQueryBoundP_hashQuery _ rfl)) fun opens => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_require _ _) fun _ => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_oracleStep _ (isQueryBoundP_deriveKeys i _)) fun keys => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_oracleStep _
    (isQueryBoundP_mapM_zero _ _ _ fun j _ => isQueryBoundP_hashQuery _ rfl)) fun shared => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_exchange _ hx _) fun received => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_require _ _) fun _ => ?_
  exact isQueryBoundP_partyPure _ _


/-- An operator of the PRSS setup hashes only queries of the setup domain, and it makes no `PRG`
call. -/
theorem setupKeys_partyFree (i : C.Party) :
    IsQueryBoundP (setupKeys .prss i : PartyM C E RealSpec (Keys C)).run
      (PartyFree (E := E) (G := RealSpec) (FreeStreamKey (C := C))) 0 := by
  unfold setupKeys setupWith
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_localStep _ _
    (isQueryBoundP_liftComp_prob_of_sample _ (fun _ h => h) _)) fun own => ?_
  exact isQueryBoundP_partyBind _ _ _ (commitRevealEcho_partyFree i own) fun _ => isQueryBoundP_partyPure _ _

end Program

/-! ## The run of the setup -/

/-- The honest operators of a PRSS setup make no `PRG` call and hash no stream key, from every state
of the adversary. -/
theorem setupNoStreamKey {Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty PEmpty L R) (st : A.State) :
    IsQueryBoundP (executePhase worldRoles D A F setupRounds st
      fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) (FreeStreamKey (C := C)) 0 :=
  executePhase_free _ (fun _ h => h) D A F setupRounds st _ fun i _ => setupKeys_partyFree i

/-- The real run of the setup reads no hash cell of a stream key on the free copy. -/
theorem realExecution_setup_noStreamKey (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    IsQueryBoundP (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z) (FreeStreamKey (C := C)) 0 :=
  isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_adversary_noStreamKey _ 0) fun st _ =>
    setupNoStreamKey D A noFunctionality st

/-- The real run of the setup makes no free stream call under a hidden name. This is the premise of
`streamWorld_run_of_noHidden`. -/
theorem setupNoHidden (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    IsQueryBoundP (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z) (FreeHiddenStream D) 0 :=
  (realExecution_setup_noStreamKey D A x z).of_imp (freeStreamKey_of_freeHiddenStream D)

/-- The real run of the setup in the stream world is its run in the ordinary world, and the hidden
table does not change. -/
theorem streamWorld_setup (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (cache : HashCache C)
    (table : HiddenCache C) :
    (simulateQ (streamWorld prims D) (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)).run (cache, table) =
      (fun r => (r.1, (r.2, table))) <$> (simulateQ (worldAnswer prims) (realExecution D A noFunctionality
        setupRounds (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)).run cache :=
  streamWorld_run_of_noHidden prims D _ (setupNoHidden D A x z) cache table

end ThresholdLeanXmssSecurity
