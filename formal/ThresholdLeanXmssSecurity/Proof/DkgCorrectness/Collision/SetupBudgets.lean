import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets

/-!
# The honest budgets of the echo hashes and of the derived keys of the PRSS setups

The network bound of `HonestBudgets.lean` holds for each predicate `p` on the local calls in the place
of a class. `treeHonestP` bounds the honest calls of `p` in one run of a tree by `n` times the calls of
one operator, when the calls of `p` are in the class `prssSetup`. The PRSS setup of one operator makes
at most `n` echo hashes and at most `termCount C + n` derivations.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace SetupBudgets

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_sequenceFin noCall_query)
open DigestBudgets (ClassBound StateBound)

attribute [local instance] Classical.propDecidable

/-! ## The honest calls of a predicate on the network -/

section Network

variable {C : Committee} {E : Type} (p : (LocalSpec C).Domain → Prop)

/-- A local call of an operator that satisfies `p`. -/
def PartyP : (PartySpec C E RealSpec).Domain → Prop
  | .inl (.inl t) => p t
  | _ => False

/-- An honest call that satisfies `p`, namely a call on the free copy. -/
def HonestP : (WorldSpec C).Domain → Prop
  | .inr t => p t
  | _ => False

/-- The budget of `p` of the continuation of a stopped program. -/
def StepBoundP {α : Type} (st : Step C E RealSpec α) (n : ℕ) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyP (C := C) (E := E) p) n
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyP (C := C) (E := E) p) n

/-- The adversary role makes no honest call. -/
theorem honestP_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (worldRoles.adversary oa) (HonestP p) 0 := by
  suffices h : ∀ n, IsQueryBoundP (worldRoles.adversary oa) (HonestP p) n from h 0
  induction oa using OracleComp.inductionOn with
  | pure a => intro n; trivial
  | query_bind t k ih =>
    intro n
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, ThresholdLeanXmssSecurity.adversary_query]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

/-- Advancing an honest operator on the free copy spends its budget of `p` and leaves the rest for its
continuation. -/
theorem free_advance_bindP {α β : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α))
    (k : Step C E RealSpec α → OracleComp (WorldSpec C) β) (extra : ℕ) :
    ∀ n, IsQueryBoundP oa (PartyP p) n →
      (∀ st b, b ≤ n → StepBoundP p st b → IsQueryBoundP (k st) (HonestP p) (extra + b)) →
      IsQueryBoundP (free (advance oa) >>= k) (HonestP p) (extra + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ hk
    rw [advance_pure, free_pure, pure_bind]
    exact hk _ n le_rfl trivial
  | query_bind t f ih =>
    intro n h hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · have e : free (advance (liftM (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= f)) =
          (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>= fun u => free (advance (f u)) := by
        change free (advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (Sum.inl (Sum.inl q))) >>= f)) = _
        rw [advance_query_bind, free_bind]
        rfl
      rw [e, bind_assoc, isQueryBoundP_query_bind_iff]
      by_cases hq : p q
      · have hn : 0 < n := h.1.resolve_left (not_not.2 hq)
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        have hu := ih u (n - 1) (by
          have hq' : PartyP (E := E) p (Sum.inl (Sum.inl q)) := hq
          simpa only [hq', ↓reduceIte] using h.2 u)
          (fun st b hb hs => hk st b (by omega) hs)
        simp only [HonestP, hq, ↓reduceIte]
        exact hu.mono (by omega)
      · refine ⟨Or.inl hq, fun u => ?_⟩
        simp only [HonestP, hq, ↓reduceIte]
        exact ih u n (by
          have hq' : ¬ PartyP (E := E) p (Sum.inl (Sum.inl q)) := hq
          simpa only [hq', ↓reduceIte] using h.2 u) hk
    · change IsQueryBoundP (free (pure (Step.wait outbox f)) >>= k) (HonestP p) (extra + n)
      rw [free_pure, pure_bind]
      exact hk _ n le_rfl fun inbox => by
        have ho : ¬ PartyP p (Sum.inl (Sum.inr outbox)) := not_false
        simpa only [ho, ↓reduceIte] using h.2 inbox
    · exact input.elim

/-- Advancing the honest operators one after another spends the budget of each. -/
theorem sequenceFin_free_advance_bindP {α β : Type} : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E RealSpec) (Option α)) (budget : Fin N → ℕ)
    (_ : ∀ i, IsQueryBoundP (oa i) (PartyP p) (budget i))
    (k : (Fin N → Step C E RealSpec α) → OracleComp (WorldSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) → (∀ i, StepBoundP p (st i) (b i)) →
      IsQueryBoundP (k st) (HonestP p) (extra + ∑ i, b i)) →
    IsQueryBoundP ((OverPermutation.sequenceFin fun i => free (advance (oa i))) >>= k) (HonestP p)
      (extra + ∑ i, budget i)
  | 0, _, _, _, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    refine free_advance_bindP p (oa 0) _ _ (budget 0) (h 0) (fun st0 b0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 =
        (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine sequenceFin_free_advance_bindP (fun i : Fin N => oa i.succ) (fun i => budget i.succ)
      (fun i => h i.succ) (fun st => k (Fin.cases st0 st)) (extra + b0) (fun st b hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases hs0 hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

variable {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)

theorem roundResume_boundP {α : Type} (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBoundP p (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (roundResume D sent steps j) (PartyP p) (budget j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k => exact isQueryBoundP_pure _ _ _
  | wait out k =>
    dsimp only
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [StepBoundP, hs] at hj
      exact hj _

/-- One round on the real network spends the budgets of the honest operators. -/
theorem stepRound_bind_boundP {α β : Type} (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (budget : C.Party → ℕ) (h : ∀ j, StepBoundP p (steps j) (budget j))
    (k : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) →
      OracleComp (WorldSpec C) β) (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ), (∀ j, b j ≤ budget j) → (∀ j, StepBoundP p (st.2.1 j) (b j)) →
      IsQueryBoundP (k st) (HonestP p) (extra + ∑ j, b j)) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps >>= k) (HonestP p)
      (extra + ∑ j, budget j) := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  simp only [bind_assoc, pure_bind]
  apply (isQueryBoundP_bind (n := 0) (m := extra + ∑ j, budget j) (honestP_adversary p _)
    (fun result _ => ?_)).mono (by omega)
  have he : (fun j => match steps j with
      | .done out => pure (Step.done out)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          worldRoles.honest (advance (resume fun k => if k ∈ D.1 then result.2 k j else (steps k).delivered j))
      | .call _ _ => pure (Step.done none)) = fun j => free (advance (roundResume D result.2 steps j)) := by
    funext j
    cases hs : steps j with
    | done out => simp only [roundResume, hs, advance_pure, free_pure]
    | call input k => simp only [roundResume, hs, advance_pure, free_pure]
    | wait out k =>
      simp only [roundResume, hs]
      split_ifs
      · simp only [advance_pure, free_pure]
      · rfl
  have hseq := sequenceFin_free_advance_bindP p
    (fun j => roundResume D result.2 steps j) budget (roundResume_boundP p D result.2 steps budget h)
    (fun st => k (result.1, st, result.2)) extra
    (fun st b hb hs => hk (result.1, st, result.2) b hb hs)
  convert (congrArg (fun f : C.Party → OracleComp (WorldSpec C) (Step C E RealSpec α) =>
    IsQueryBoundP (OverPermutation.sequenceFin f >>= fun st => k (result.1, st, result.2))
      (HonestP p) (extra + ∑ j, budget j)) he).mpr hseq using 1
  congr 2
  funext j
  cases steps j <;> rfl

/-- The rounds on the real network spend the budgets of the honest operators. -/
theorem executeRounds_boundP {α : Type} :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α) (budget : C.Party → ℕ),
      (∀ j, StepBoundP p (steps j) (budget j)) →
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps) (HonestP p) (∑ j, budget j)
  | 0, state, steps, budget, h => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, budget, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine (stepRound_bind_boundP p D A state steps budget h _ 0 ?_).mono (by omega)
      intro st b hb hs
      exact (executeRounds_boundP fuel st.1 st.2.1 b hs).mono (by omega)

/-- A phase on the real network makes at most the sum of the budgets of `p` of the honest programs of
honest calls of `p`. -/
theorem executePhase_boundP {α : Type} (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (budget : C.Party → ℕ) (hp : ∀ j, j ∉ D.1 → IsQueryBoundP (program j).run (PartyP p) (budget j)) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program) (HonestP p) (∑ j, budget j) := by
  unfold executePhase startSteps
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs
    · simp only [advance_pure, free_pure]
    · rfl
  change IsQueryBoundP ((OverPermutation.sequenceFin _) >>= _) _ _
  rw [he]
  refine (sequenceFin_free_advance_bindP p _ budget ?_ _ 0 ?_).mono (Nat.zero_add _).le
  · intro j
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
  · intro st b hb hs
    exact (executeRounds_boundP p D A fuel state st b hs).mono (Nat.zero_add _).ge

end Network

/-! ## The calls of a predicate of one operator -/

section Party

variable {C : Committee} {E : Type} (p : (LocalSpec C).Domain → Prop)

/-- An operator program makes at most `n` local calls of `p` on each path. -/
def PBound {α : Type} (prog : PartyM C E RealSpec α) (n : ℕ) : Prop :=
  IsQueryBoundP prog.run (PartyP p) n

/-- A program on a state makes at most `n` local calls of `p` from each state. -/
def PState {σ α : Type} (prog : StateT σ (PartyM C E RealSpec) α) (n : ℕ) : Prop :=
  ∀ s, PBound p (prog.run s) n

variable {p}

theorem PBound.mono {α : Type} {prog : PartyM C E RealSpec α} {n m : ℕ} (h : PBound p prog n) (hnm : n ≤ m) :
    PBound p prog m :=
  IsQueryBoundP.mono h hnm

theorem PBound.pure {α : Type} (a : α) : PBound p (pure a : PartyM C E RealSpec α) 0 :=
  isQueryBoundP_pure _ _ _

theorem PBound.bind {α β : Type} {prog : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} {n m : ℕ}
    (h : PBound p prog n) (hf : ∀ a, PBound p (f a) m) : PBound p (prog >>= f) (n + m) := by
  unfold PBound
  simp only [OptionT.run_bind]
  apply isQueryBoundP_bind h
  intro a _
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact hf a

/-- A class bound gives the bound of a predicate that implies the class. -/
theorem PBound.of_class {c : HashClass} (hp : ∀ t, p t → InClass c t) {α : Type} {prog : PartyM C E RealSpec α}
    {n : ℕ} (h : ClassBound c prog n) : PBound p prog n :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with (t | _) | _
    · exact hp t ht
    · exact ht.elim
    · exact ht.elim) h

theorem liftComp_partyP {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ n, IsQueryBoundP oa p n → IsQueryBoundP (liftComp oa (PartySpec C E RealSpec)) (PartyP p) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (PartySpec C E RealSpec) =
        (liftM ((PartySpec C E RealSpec).query (.inl (.inl t))) : OracleComp (PartySpec C E RealSpec) _) >>=
          fun u => liftComp (k u) (PartySpec C E RealSpec) := by
      rw [liftComp_bind]
      rcases t with _ | _ | _ <;> rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem liftComp_roP {α : Type} (oa : OracleComp (RoSpec C) α) :
    ∀ n, IsQueryBoundP oa (fun t => p (.inr t)) n → IsQueryBoundP (liftComp oa (LocalSpec C)) p n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem PBound.localStep {α : Type} {oa : OracleComp (LocalSpec C) α} {n : ℕ} (h : IsQueryBoundP oa p n) :
    PBound p (ThresholdLeanXmss.localStep oa : PartyM C E RealSpec α) n := by
  unfold PBound ThresholdLeanXmss.localStep
  change IsQueryBoundP (liftComp oa (PartySpec C E RealSpec) >>= fun a => Pure.pure (some a)) _ _
  exact (isQueryBoundP_bind (m := 0) (liftComp_partyP oa n h) fun _ _ => isQueryBoundP_pure _ _ _).mono
    (Nat.add_zero _).le

theorem PBound.oracleStep {α : Type} {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => p (.inr t)) n) :
    PBound p (ThresholdLeanXmss.oracleStep oa : PartyM C E RealSpec α) n :=
  PBound.localStep (liftComp_roP oa n h)

theorem PState.mono {σ α : Type} {prog : StateT σ (PartyM C E RealSpec) α} {n m : ℕ} (h : PState p prog n)
    (hnm : n ≤ m) : PState p prog m := fun s => (h s).mono hnm

theorem PState.pure {σ α : Type} (a : α) : PState p (pure a : StateT σ (PartyM C E RealSpec) α) 0 :=
  fun _ => PBound.pure _

theorem PState.bind {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n m : ℕ} (h : PState p prog n) (hf : ∀ a, PState p (f a) m) :
    PState p (prog >>= f) (n + m) := fun s =>
  PBound.bind (h s) fun a => hf a.1 a.2

theorem PState.lift {σ α : Type} {prog : PartyM C E RealSpec α} {n : ℕ} (h : PBound p prog n) :
    PState p (StateT.lift prog : StateT σ (PartyM C E RealSpec) α) n := fun s => by
  change PBound p (prog >>= fun a => Pure.pure (a, s)) n
  simpa using PBound.bind h fun a => PBound.pure (p := p) (a, s)

theorem PState.of_class {c : HashClass} (hp : ∀ t, p t → InClass c t) {σ α : Type}
    {prog : StateT σ (PartyM C E RealSpec) α} {n : ℕ} (h : StateBound c prog n) : PState p prog n :=
  fun s => PBound.of_class hp (h s)

end Party

/-! ## The PRSS setup of one operator -/

section Setup

variable {C : Committee} {E : Type} {p : (LocalSpec C).Domain → Prop}

/-- The PRSS setup of one operator makes the calls of `p` of its derivation and of its `n` echo
hashes, when its commitments make none. -/
theorem commitRevealEcho_pbound (hp : ∀ t, p t → InClass .prssSetup t) (i : C.Party) (own : Parts C) (a b : ℕ)
    (hcommit : ∀ j k l, ¬ p (.inr (.inl (.commit .prss j k l))))
    (hderive : ∀ view, IsQueryBoundP (deriveKeys .prss i view) (fun t => p (.inr t)) a)
    (hshared : ∀ l, IsQueryBoundP (hashQuery (C := C) (.sharedKeys .prss l)) (fun t => p (.inr t)) b) :
    PBound p (commitRevealEcho .prss i own : PartyM C E RealSpec _) (a + C.parties.length * b) := by
  have hc : ∀ j k l, IsQueryBoundP (hashQuery (C := C) (.commit .prss j k l)) (fun t => p (.inr t)) 0 :=
    fun j k l => (noCall_iff _ _).1 (noCall_query _ _ (hcommit j k l))
  have hzero : ∀ (l : List C.Party) (f : C.Party → Query C), (∀ j, ∃ x y z, f j = .commit .prss x y z) →
      IsQueryBoundP (l.mapM fun j => hashQuery (f j)) (fun t => p (.inr t)) 0 := fun l f hf => by
    simpa using queryBound_mapM _ _ 0 l fun j _ => by
      obtain ⟨x, y, z, e⟩ := hf j
      rw [e]
      exact hc x y z
  have hex : ∀ outbox : Mail C E, PBound p (exchange outbox : PartyM C E RealSpec _) 0 :=
    fun outbox => PBound.of_class hp (DigestBudgets.ClassBound.exchange outbox)
  have hreq : ∀ q : Prop, PBound p (require q : PartyM C E RealSpec Unit) 0 :=
    fun q => PBound.of_class hp (DigestBudgets.ClassBound.require q)
  unfold commitRevealEcho
  refine (PBound.bind (n := 0) (PBound.oracleStep (hzero _ _ fun j => ⟨_, _, _, rfl⟩)) fun _ =>
    PBound.bind (n := 0) (hex _) fun _ => PBound.bind (n := 0) (hex _) fun _ =>
    PBound.bind (n := 0) (PBound.oracleStep (hzero _ _ fun j => ⟨_, _, _, rfl⟩)) fun _ =>
    PBound.bind (n := 0) (hreq _) fun _ => PBound.bind (PBound.oracleStep (hderive _)) fun _ =>
    PBound.bind (PBound.oracleStep (queryBound_mapM _ _ b C.parties fun j _ => hshared _)) fun _ =>
    PBound.bind (n := 0) (hex _) fun _ => PBound.bind (n := 0) (hreq _) fun _ => PBound.pure _).mono (by omega)

/-- The PRSS setup of one operator, with its sampled parts. -/
theorem prssSetup_pbound (hp : ∀ t, p t → InClass .prssSetup t) (i : C.Party) (a b : ℕ)
    (hcommit : ∀ j k l, ¬ p (.inr (.inl (.commit .prss j k l))))
    (hderive : ∀ view, IsQueryBoundP (deriveKeys .prss i view) (fun t => p (.inr t)) a)
    (hshared : ∀ l, IsQueryBoundP (hashQuery (C := C) (.sharedKeys .prss l)) (fun t => p (.inr t)) b) :
    PBound p (prssSetup i : PartyM C E RealSpec _) (a + C.parties.length * b) := by
  unfold prssSetup prssSetupWith
  refine (PBound.bind (n := 0) (PBound.localStep ((DigestBudgets.liftComp_prob_bound .prssSetup _).of_imp hp))
    fun own => PBound.bind (m := 0) (commitRevealEcho_pbound hp i own a b hcommit hderive hshared)
      fun _ => PBound.pure _).mono (by omega)

/-- A derivation of the PRSS setup makes at most `termCount C + n` calls. -/
theorem deriveKeys_count (q : (RoSpec C).Domain → Prop) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys .prss i view) q (C.terms.length + C.parties.length) := by
  have h1 : ∀ x : Query C, IsQueryBoundP (hashQuery x) q 1 := fun x =>
    (hashQuery_queryBound x).of_imp fun _ _ => trivial
  unfold deriveKeys
  refine (isQueryBoundP_bind (n := 0) ?_ fun _ _ => isQueryBoundP_bind (queryBound_mapM q _ 1 _ fun T _ => ?_)
    fun _ _ => isQueryBoundP_bind (queryBound_mapM q _ 1 _ fun j _ => ?_)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (by simp)
  · exact isQueryBoundP_pure _ _ _
  · split_ifs
    · exact h1 _
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · split
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · exact h1 _

/-- A derivation of the PRSS setup makes no call of `p` when no derived key is a call of `p`. -/
theorem deriveKeys_zero (i : C.Party) (view : C.Party → Parts C)
    (hq : ∀ kind l, ¬ p (.inr (.inl (.derive .prss kind l)))) :
    IsQueryBoundP (deriveKeys .prss i view) (fun t => p (.inr t)) 0 := by
  rw [← noCall_iff]
  unfold deriveKeys
  refine noCall_bind _ (by exact noCall_pure _ _) fun _ => noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
    noCall_bind _ (noCall_mapM _ _ _ fun j => ?_) fun _ => noCall_pure _ _
  · split_ifs
    · exact noCall_query _ _ (hq _ _)
    · exact noCall_pure _ _
  · split
    · exact noCall_pure _ _
    · exact noCall_query _ _ (hq _ _)

end Setup

/-! ## The runs of a tree -/

section Tree

open DigestBudgets

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) {p : (LocalSpec C).Domain → Prop}

omit [Field E] [Algebra Bit E] in
theorem PState.bind_le {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n m k : ℕ} (h : PState p prog n) (hf : ∀ a, PState p (f a) m)
    (hk : n + m ≤ k) : PState p (prog >>= f) k :=
  (PState.bind h hf).mono hk

/-- One ceremony makes the calls of `p` of its PRSS setup and none in its batches. -/
theorem ceremonyRun_pbound (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (i : C.Party) (keys : Keys C)
    (jobs : List Job) :
    PState p (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) R := by
  unfold ceremonyRun
  refine PState.bind_le (PState.lift (hsetup i)) (fun prss => PState.of_class hp ?_) (Nat.add_zero R).le
  unfold batched
  dsimp only
  refine StateBound.bind_zero' ((StateBound.mapM _ (digestCost C .prssSetup + copyCost C .prssSetup)
    (fun batch => ?_) _).mono (by simp [digestCost, copyCost])) fun _ => StateBound.pure _
  refine StateBound.zero_bind StateBound.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine StateBound.zero_bind (StateBound.lift_zero ((ClassBound.mapM _ 0
    (fun job => inputShares_bound _ (by decide) job) _).mono (by simp))) fun inputs => ?_
  refine StateBound.bind_zero' (StateBound.lift (runJobs_bound K _ (by decide) (by decide) _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact StateBound.bind_zero (StateBound.set _) fun _ => StateBound.pure _

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree make the calls of `p` of `treeSetups tree` runs. -/
theorem ceremonyOutput_pbound (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), PState p (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (R : ℕ)
    (hrun : ∀ jobs, PState p (run jobs) R) (top : TopTree) (tree : Tree) :
    PState p (ceremonyOutput lift parameter run top tree) (treeSetups tree * R) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine PState.bind_le (hrun topJobs) (m := 0) (fun out => ?_) (by simp [treeSetups])
    rcases out with _ | outputs
    · exact PState.pure _
    · exact PState.bind_le (hlift _) (fun _ => PState.pure _) le_rfl
  | bottom b =>
    unfold ceremonyOutput
    refine PState.bind_le (hrun (bottomJobs b)) (m := R) (fun out => ?_) (by simp [treeSetups]; omega)
    rcases out with _ | outputs
    · exact (PState.pure _).mono (Nat.zero_le _)
    refine PState.bind_le (hlift _) (m := R) (fun root => ?_) (by omega)
    refine PState.bind_le (hlift _) (m := R) (fun base => ?_) (by omega)
    refine PState.bind_le (hlift _) (m := R) (fun found => ?_) (by omega)
    rcases found with _ | ⟨randomness, encoding⟩
    · exact (PState.pure _).mono (Nat.zero_le _)
    refine PState.bind_le (hrun _) (m := 0) (fun out => ?_) (by omega)
    rcases out with _ | values
    · exact PState.pure _
    refine PState.bind_le (hlift _) (m := 0) (fun path => ?_) (by omega)
    refine PState.bind_le (hlift _) (m := 0) (fun topRoot => ?_) (by omega)
    split_ifs
    · exact PState.pure _
    · exact PState.pure _

/-- The ceremonies of a tree at one operator make the calls of `p` of `treeSetups tree` PRSS setups. -/
theorem newTree_pbound (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (i : C.Party) (keys : Keys C)
    (top : TopTree) (tree : Tree) :
    PBound p (newTree K circuits settings i keys top tree : PartyM C E RealSpec _) (treeSetups tree * R) := by
  have hrun := ceremonyOutput_pbound (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => PState.of_class hp (lift_tweakable_bound (by decide) oa)) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) R
    (fun jobs => ceremonyRun_pbound K circuits settings hp R hsetup i keys jobs) top tree (0, 0)
  unfold newTree
  refine (PBound.bind (m := 0) ?_ fun out => ?_).mono (Nat.add_zero _).le
  · unfold StateT.run'
    unfold PBound at hrun ⊢
    simp only [OptionT.run_map]
    exact (isQueryBoundP_map_iff _ _ _).2 hrun
  · rcases out with _ | output
    · exact isQueryBoundP_pure _ _ _
    · exact PBound.pure _

/-- The program of an operator in a run of a tree makes the calls of `p` of `treeSetups tree` PRSS
setups. -/
theorem treeProgram_pbound (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (i : C.Party) (operator : OperatorState C)
    (tree : Tree) : PBound p (treeProgram K circuits settings i operator tree) (treeSetups tree * R) := by
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact newTree_pbound K circuits settings hp R hsetup _ _ _ _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact newTree_pbound K circuits settings hp R hsetup _ _ _ _

/-- One run of a tree on the network makes at most `n * (treeSetups tree * R)` honest calls of `p`, when
the PRSS setup of each operator makes at most `R`. -/
theorem treeHonestP (hp : ∀ t, p t → InClass .prssSetup t) (R : ℕ)
    (hsetup : ∀ i, PBound p (prssSetup i : PartyM C E RealSpec _) R) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
      fun i => treeProgram K circuits settings i (s.operators i) tree) (HonestP p) (C.n * (treeSetups tree * R)) := by
  refine (executePhase_boundP p D net _ _ _ (fun _ => treeSetups tree * R)
    fun j _ => treeProgram_pbound K circuits settings hp R hsetup j _ tree).mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Tree

end SetupBudgets

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets.treeHonestP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets.treeHonestP
