import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Counts

/-!
# The honest budgets of the classes `digest` and `copy`

`treeHonest`, `seedHonest` and `signQuiet` bound the honest calls of each class in a run of a tree, in
the seed generation and in the signing oracles. The honest calls of a predicate on the network are at
most the sum of the budgets of the honest programs (`SetupBudgets.executePhase_boundP`), and a class is
the case of the predicate `InClass c`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace DigestBudgets

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_sequenceFin noCall_query)

attribute [local instance] Classical.propDecidable

/-! ## The calls of `H` and `PRG` in a class -/

section Ro

variable {C : Committee}

/-- A call of `H` or `PRG` in class `c`. -/
def RoIn (c : HashClass) : (RoSpec C).Domain → Prop := fun t => InClass c (.inr t)

/-- A computation of `H` and `PRG` with at most `n` calls in class `c` makes at most `n` calls of a
predicate `p` of the world on the free copy, when `p` is the class `c` on the free copy. -/
theorem free_liftComp_bound (c : HashClass) (p : (WorldSpec C).Domain → Prop)
    (hp : ∀ t, p (.inr (.inr t)) ↔ RoIn c t) {α : Type} (oa : OracleComp (RoSpec C) α) :
    ∀ n, IsQueryBoundP oa (RoIn c) n → IsQueryBoundP (free (liftComp oa (LocalSpec C))) p n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inr t))) : OracleComp (WorldSpec C) _) >>=
          fun u => free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    refine ⟨?_, fun u => ?_⟩
    · rw [hp]; exact h.1
    · have := ih u _ (h.2 u)
      simpa only [hp] using this

/-- A computation of `H` and `PRG` on `.hash` and `.prf` only makes no call in a class other than
`signing`. -/
theorem noCall_of_onlySign {c : HashClass} (hc : c ≠ .signing) {α : Type} {oa : OracleComp (RoSpec C) α}
    (h : GameCount.OnlySign oa) : NoCall (RoIn c) oa := by
  rw [noCall_iff]
  refine (isQueryBoundP_congr_pred fun _ => not_not).1 ((isQueryBoundP_zero_iff _ _).2
    (((GameCount.onlySign_iff _).1 h).mono fun t ht => ?_))
  rcases t with q | _
  · cases q <;> simp_all [GameCount.SignCall, RoIn, InClass, queryClass, eq_comm]
  · exact ht.elim

/-- A call of `H` on an input outside class `c` makes no call in class `c`. -/
theorem noCall_hashQuery {c : HashClass} (q : Query C) (hq : RoIn c (.inl q) → False) :
    NoCall (RoIn c) (hashQuery q) :=
  noCall_query _ _ hq

/-- `Eval'` calls `H` only on `.prf` and `.mask`. -/
theorem noCall_eval {c : HashClass} (hc : c ≠ .signing) (keys : Keys C) (i : C.Party) (J : C.Quorum)
    (x : Point) (message : Message) : NoCall (RoIn c) (eval keys i J x message) := by
  unfold eval
  refine noCall_bind _ (noCall_mapM _ _ _ fun T => noCall_map _ _ (noCall_hashQuery _ ?_)) fun _ =>
    noCall_bind _ (noCall_mapM _ _ _ fun j => noCall_map _ _ (noCall_hashQuery _ ?_)) fun _ => noCall_pure _ _
  · simp [RoIn, InClass, queryClass, Ne.symm hc]
  · simp [RoIn, InClass, queryClass, Ne.symm hc]

end Ro

/-! ## The signing oracles -/

section Sign

variable {C : Committee}

/-- The signing oracles on the dealt keys of `prfValue seeds`, as a computation of `H` and `PRG`,
make no call in a class other than `signing`. -/
theorem noCall_tsigOracles {c : HashClass} (hc : c ≠ .signing) (keys : Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (q : (TsigSpec C).Domain) (t : TsigState C) :
    NoCall (RoIn c) ((tsigOracles (fun oa => oa)
      (dealtWith (fun oa => oa) keys.parameter (fun _ => keys) top (prfValue seeds)) q).run t) := by
  have hbottom : ∀ (b : Fin (2 ^ layerHeight)) (s : TsigState C),
      NoCall (RoIn c) ((bottomOnce (dealtWith (fun oa => oa) keys.parameter (fun _ => keys) top
        (prfValue seeds)) b).run s) := by
    intro b s
    simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, StateT.run_modify,
        StateT.run_pure, pure_bind]
      refine noCall_bind _ (noCall_map _ _ (noCall_of_onlySign hc (GameCount.onlySign_referenceTree _ _ _ _)))
        fun _ => noCall_pure _ _
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact noCall_pure _ _
  · simp only [tsigOracles, StateT.run_bind]
    refine noCall_bind _ (hbottom b t) fun ⟨o, st⟩ => ?_
    rcases o with _ | tree
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact noCall_bind _ (noCall_of_onlySign hc (GameCount.onlySign_prfValue _ _)) fun _ => noCall_pure _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact noCall_bind _ (noCall_bind _ (noCall_eval hc _ _ _ _ _) fun _ => noCall_pure _ _) fun _ =>
        noCall_pure _ _
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact noCall_pure _ _
    · simp only [StateT.run_bind]
      refine noCall_bind _ (hbottom _ t) fun ⟨o, st⟩ => ?_
      rcases o with _ | tree
      · exact noCall_pure _ _
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
        refine noCall_bind _ (noCall_eval hc _ _ _ _ _) fun own => ?_
        refine noCall_bind _ ?_ fun r => ?_
        · unfold signRound2With
          refine noCall_bind _ (noCall_of_onlySign hc ?_) fun r => ?_
          · unfold signCodeword
            exact GameCount.onlySign_tweakable _
          · rcases r with _ | ⟨_, encoding⟩
            · exact noCall_pure _ _
            · refine noCall_bind _ (noCall_sequenceFin _ _ fun l => ?_) fun _ => noCall_pure _ _
              split_ifs
              · exact noCall_map _ _ (noCall_eval hc _ _ _ _ _)
              · exact noCall_pure _ _
        · rcases r with ⟨_ | values, st'⟩
          · exact noCall_pure _ _
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            exact noCall_pure _ _

/-- The answers of the honest operators to the signing requests on the free copy make no call of
`Adds c` for a class other than `signing`. -/
theorem signQuiet {c : HashClass} (hc : c ≠ .signing) : FirstCounts.SignQuiet (C := C) c := by
  intro D operators keys top q t
  let seeds := gameSeeds D fun i => (operators i).keys
  let dealt₀ : Dealt C (OracleComp (RoSpec C)) :=
    dealtWith (fun oa => oa) keys.parameter (fun _ => keys) top (prfValue seeds)
  have hdealt : SeedHitProof.Dealt.hmap DkgCompletenessProof.freeHom dealt₀ =
      dealtWith (fun oa => free (liftComp oa (LocalSpec C))) keys.parameter (fun _ => keys) top
        (fun x => free (liftComp (prfValue seeds x) (LocalSpec C))) := by
    simp only [SeedHitProof.Dealt.hmap, dealt₀, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
    rfl
  have hom := SeedHitProof.hom_tsigOracles DkgCompletenessProof.freeHom (fun oa => oa) dealt₀ q t
  rw [hdealt] at hom
  change IsQueryBoundP ((tsigOracles (fun oa => DkgCompletenessProof.freeHom oa) (dealtWith (fun oa => free (liftComp oa (LocalSpec C)))
    keys.parameter (fun _ => keys) top (fun x => free (liftComp (prfValue seeds x) (LocalSpec C)))) q).run t) _ 0
  rw [← hom]
  exact free_liftComp_bound c _ (fun _ => Iff.rfl) _ 0 ((noCall_iff _ _).1 (noCall_tsigOracles hc keys top seeds q t))

end Sign

/-! ## The honest calls of a predicate on the network

The lemmas give the network bound of `ThresholdLeanXmssSecurity/Proof/Check.lean` for `worldRoles`
and a predicate `p` on the local calls in the place of `localRoles` and `Counted`. The class bounds
of `DigestBudgets` are the case of the predicate `InClass c`. -/

end DigestBudgets

namespace SetupBudgets

attribute [local instance] Classical.propDecidable

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

theorem PState.bind_zero {σ α β : Type} {prog : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} (h : PState p prog 0) (hf : ∀ a, PState p (f a) 0) :
    PState p (prog >>= f) 0 :=
  PState.bind h hf

theorem PState.foldlM {σ α γ : Type} (f : α → γ → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a g, PState p (f a g) 0) : ∀ (xs : List γ) (a : α), PState p (xs.foldlM f a) 0
  | [], a => by simpa using PState.pure (p := p) (σ := σ) a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact (hf a g).bind_zero fun a' => PState.foldlM f hf xs a'

/-- A class bound gives the bound of a predicate that implies the class. -/
theorem PBound.of_class {c : HashClass} (hp : ∀ t, p t → InClass c t) {α : Type} {prog : PartyM C E RealSpec α}
    {n : ℕ} (h : PBound (InClass c) prog n) : PBound p prog n :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with (t | _) | _
    · exact hp t ht
    · exact ht.elim
    · exact ht.elim) h

theorem PState.of_class {c : HashClass} (hp : ∀ t, p t → InClass c t) {σ α : Type}
    {prog : StateT σ (PartyM C E RealSpec) α} {n : ℕ} (h : PState (InClass c) prog n) : PState p prog n :=
  fun s => PBound.of_class hp (h s)

end Party

end SetupBudgets

namespace DigestBudgets

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_sequenceFin noCall_query)

attribute [local instance] Classical.propDecidable

/-! ## The honest calls of a class on the network -/

section Network

variable {C : Committee} {E : Type} (c : HashClass)

/-- A local call of an operator in class `c`. -/
def PartyIn : (PartySpec C E RealSpec).Domain → Prop
  | .inl (.inl t) => InClass c t
  | _ => False

/-- The adversary role makes no honest call. -/
theorem honestIn_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (worldRoles.adversary oa) (HonestIn c) 0 :=
  SetupBudgets.honestP_adversary (InClass c) oa

variable {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)

/-- A phase on the real network makes at most the sum of the budgets of class `c` of the honest
programs of honest calls in class `c`. -/
theorem executePhase_bound {α : Type} (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (budget : C.Party → ℕ) (hp : ∀ j, j ∉ D.1 → IsQueryBoundP (program j).run (PartyIn c) (budget j)) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program) (HonestIn c) (∑ j, budget j) :=
  SetupBudgets.executePhase_boundP (InClass c) D A fuel state program budget hp

/-- A real execution makes at most the sum of the budgets of class `c` of the honest programs of
honest calls in class `c`. -/
theorem realExecution_bound {I O : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → I → PartyM C E RealSpec O) (x : C.Party → I) (z : Aux) (budget : C.Party → ℕ)
    (hp : ∀ j, j ∉ D.1 → IsQueryBoundP (program j (x j)).run (PartyIn c) (budget j)) :
    IsQueryBoundP (realExecution D A noFunctionality fuel program x z) (HonestIn c) (∑ j, budget j) := by
  unfold realExecution
  exact (isQueryBoundP_bind (m := ∑ j, budget j) (honestIn_adversary c _) fun state _ =>
    executePhase_bound c D A fuel state _ budget hp).mono (by omega)

end Network

/-! ## The calls of a class of one operator -/

section Party

variable {C : Committee} {E : Type} (c : HashClass)

/-- A private sample makes no call in a class. -/
theorem liftComp_prob_bound {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) (InClass c) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inl t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    have ht : ¬ InClass (C := C) c (Sum.inl t) := fun h => h.elim
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl ht, fun u => by
      simpa only [ht, ↓reduceIte] using ih u⟩

/-- An operator program makes at most `n` local calls in class `c` on each path. -/
def ClassBound {α : Type} (p : PartyM C E RealSpec α) (n : ℕ) : Prop :=
  IsQueryBoundP p.run (PartyIn c) n

/-- A program on a state makes at most `n` local calls in class `c` from each state. -/
def StateBound {σ α : Type} (p : StateT σ (PartyM C E RealSpec) α) (n : ℕ) : Prop :=
  ∀ s, ClassBound c (p.run s) n

variable {c}

theorem ClassBound.mono {α : Type} {p : PartyM C E RealSpec α} {n m : ℕ} (h : ClassBound c p n) (hnm : n ≤ m) :
    ClassBound c p m :=
  IsQueryBoundP.mono h hnm

theorem ClassBound.pure {α : Type} (a : α) : ClassBound c (pure a : PartyM C E RealSpec α) 0 :=
  isQueryBoundP_pure _ _ _

theorem ClassBound.failure {α : Type} : ClassBound c (failure : PartyM C E RealSpec α) 0 :=
  isQueryBoundP_pure _ _ _

theorem ClassBound.bind {α β : Type} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} {n m : ℕ}
    (h : ClassBound c p n) (hf : ∀ a, ClassBound c (f a) m) : ClassBound c (p >>= f) (n + m) :=
  SetupBudgets.PBound.bind h hf

theorem ClassBound.localStep {α : Type} {oa : OracleComp (LocalSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (InClass c) n) : ClassBound c (ThresholdLeanXmss.localStep oa : PartyM C E RealSpec α) n :=
  SetupBudgets.PBound.localStep h

theorem ClassBound.oracleStep {α : Type} {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (RoIn c) n) : ClassBound c (ThresholdLeanXmss.oracleStep oa : PartyM C E RealSpec α) n :=
  SetupBudgets.PBound.oracleStep h

theorem ClassBound.oracleStep_zero {α : Type} {oa : OracleComp (RoSpec C) α} (h : NoCall (RoIn c) oa) :
    ClassBound c (ThresholdLeanXmss.oracleStep oa : PartyM C E RealSpec α) 0 :=
  ClassBound.oracleStep ((noCall_iff _ _).1 h)

theorem ClassBound.require (p : Prop) : ClassBound c (ThresholdLeanXmss.require p : PartyM C E RealSpec Unit) 0 := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact ClassBound.pure ()
  · exact ClassBound.failure

theorem ClassBound.exchange (outbox : Mail C E) :
    ClassBound c (ThresholdLeanXmss.exchange outbox : PartyM C E RealSpec _) 0 := by
  unfold ThresholdLeanXmss.exchange ClassBound
  simp only [OptionT.run_bind, OptionT.run_lift]
  refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ fun a _ => ?_).mono (Nat.add_zero _).le
  · simp only [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun h => h.elim
  · rcases a with _ | inbox
    · exact isQueryBoundP_pure _ _ _
    · dsimp only [Option.elim]
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_pure _ _ _

theorem StateBound.mono {σ α : Type} {p : StateT σ (PartyM C E RealSpec) α} {n m : ℕ} (h : StateBound c p n)
    (hnm : n ≤ m) : StateBound c p m := fun s => (h s).mono hnm

theorem StateBound.pure {σ α : Type} (a : α) : StateBound c (pure a : StateT σ (PartyM C E RealSpec) α) 0 :=
  fun _ => ClassBound.pure _

theorem StateBound.bind {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n m : ℕ} (h : StateBound c p n) (hf : ∀ a, StateBound c (f a) m) :
    StateBound c (p >>= f) (n + m) := fun s =>
  ClassBound.bind (h s) fun a => hf a.1 a.2

theorem StateBound.lift {σ α : Type} {p : PartyM C E RealSpec α} {n : ℕ} (h : ClassBound c p n) :
    StateBound c (StateT.lift p : StateT σ (PartyM C E RealSpec) α) n :=
  SetupBudgets.PState.lift h

theorem StateBound.get {σ : Type} : StateBound c (get : StateT σ (PartyM C E RealSpec) σ) 0 :=
  fun _ => ClassBound.pure _

theorem StateBound.set {σ : Type} (s : σ) : StateBound c (set s : StateT σ (PartyM C E RealSpec) PUnit) 0 :=
  fun _ => ClassBound.pure _

theorem StateBound.modify {σ : Type} (f : σ → σ) : StateBound c (modify f : StateT σ (PartyM C E RealSpec) PUnit) 0 :=
  fun _ => ClassBound.pure _

theorem StateBound.modifyGet {σ α : Type} (f : σ → α × σ) :
    StateBound c (modifyGet f : StateT σ (PartyM C E RealSpec) α) 0 :=
  fun _ => ClassBound.pure _

theorem StateBound.foldlM {σ α γ : Type} (f : α → γ → StateT σ (PartyM C E RealSpec) α) (n : ℕ)
    (hf : ∀ a g, StateBound c (f a g) n) : ∀ (xs : List γ) (a : α), StateBound c (xs.foldlM f a) (xs.length * n)
  | [], a => by simpa using StateBound.pure (c := c) (σ := σ) a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using (hf a g).bind fun a' => StateBound.foldlM f n hf xs a'

theorem StateBound.mapM {σ α β : Type} (f : α → StateT σ (PartyM C E RealSpec) β) (n : ℕ)
    (hf : ∀ a, StateBound c (f a) n) : ∀ xs : List α, StateBound c (xs.mapM f) (xs.length * n)
  | [] => by simpa using StateBound.pure (c := c) (σ := σ) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hf a).bind fun b => (StateBound.mapM f n hf xs).bind fun bs => StateBound.pure (c := c) (b :: bs)

theorem ClassBound.mapM {α β : Type} (f : α → PartyM C E RealSpec β) (n : ℕ)
    (hf : ∀ a, ClassBound c (f a) n) : ∀ xs : List α, ClassBound c (xs.mapM f) (xs.length * n)
  | [] => by simpa using ClassBound.pure (c := c) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hf a).bind fun b => (ClassBound.mapM f n hf xs).bind fun bs => ClassBound.pure (c := c) (b :: bs)

end Party

/-! ## The setups -/

section Setup

variable {C : Committee} {E : Type} {c : HashClass}

/-- The calls of `H` of a setup of `phase` are in the class of `phase`. -/
theorem noCall_setupQuery {phase : Phase} (hc : c ≠ phaseClass phase) (q : Query C)
    (hq : queryClass q = phaseClass phase) : NoCall (RoIn c) (hashQuery q) := by
  refine noCall_hashQuery q fun h => ?_
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [RoIn, InClass, queryClass, phaseClass, eq_comm]

/-- `deriveKeys` makes no call outside the class of `phase`. -/
theorem noCall_deriveKeys {phase : Phase} (hc : c ≠ phaseClass phase) (i : C.Party) (view : C.Party → Parts C) :
    NoCall (RoIn c) (deriveKeys phase i view) := by
  unfold deriveKeys
  dsimp only
  split_ifs <;> refine noCall_bind _ ?_ fun _ => noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
    noCall_bind _ (noCall_mapM _ _ _ fun j => ?_) fun _ => noCall_pure _ _
  all_goals first
    | exact noCall_pure _ _
    | exact noCall_setupQuery hc _ rfl
    | (split_ifs
       · exact noCall_setupQuery hc _ rfl
       · exact noCall_pure _ _)
    | (split
       · exact noCall_pure _ _
       · exact noCall_setupQuery hc _ rfl)

/-- A setup with commit, reveal and echo makes no call outside the class of `phase`. -/
theorem commitRevealEcho_bound {phase : Phase} (hc : c ≠ phaseClass phase) (i : C.Party) (own : Parts C) :
    ClassBound c (commitRevealEcho phase i own : PartyM C E RealSpec _) 0 := by
  unfold commitRevealEcho
  refine ClassBound.bind (n := 0) (m := 0)
    (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun j => noCall_setupQuery hc _ rfl)) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.exchange _) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.exchange _) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0)
    (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun j => noCall_setupQuery hc _ rfl)) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.require _) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.oracleStep_zero (noCall_deriveKeys hc _ _)) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0)
    (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun j => noCall_setupQuery hc _ rfl)) fun _ => ?_
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.exchange _) fun _ => ?_
  exact ClassBound.bind (n := 0) (m := 0) (ClassBound.require _) fun _ => ClassBound.pure _

theorem seedGen_bound (hc : c ≠ .seedGen) (i : C.Party) : ClassBound c (seedGen i : PartyM C E RealSpec _) 0 := by
  unfold seedGen seedGenWith
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.localStep (liftComp_prob_bound c _)) fun _ => ?_
  exact ClassBound.bind (n := 0) (m := 0) (commitRevealEcho_bound (phase := .seedGen) hc _ _)
    fun _ => ClassBound.pure _

theorem prssSetup_bound (hc : c ≠ .prssSetup) (i : C.Party) : ClassBound c (prssSetup i : PartyM C E RealSpec _) 0 := by
  unfold prssSetup prssSetupWith
  refine ClassBound.bind (n := 0) (m := 0) (ClassBound.localStep (liftComp_prob_bound c _)) fun _ => ?_
  exact ClassBound.bind (n := 0) (m := 0) (commitRevealEcho_bound (phase := .prss) hc _ _)
    fun _ => ClassBound.pure _

/-- The seed generation on the network makes no honest call outside the class `seedGen`. -/
theorem seedHonest {E : Type} (hc : c ≠ .seedGen) : FirstCounts.SeedHonest (C := C) (E := E) c 0 := by
  intro D net
  rw [GameCount.bound_iff]
  have h := realExecution_bound c D net setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [] (fun _ => 0)
    fun j _ => seedGen_bound hc j
  simpa using h

end Setup

/-! ## The building blocks of a batch -/

section Blocks

variable {C : Committee} {E : Type} {c : HashClass}

theorem ClassBound.bind_zero {α β : Type} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (h : ClassBound c p 0) (hf : ∀ a, ClassBound c (f a) 0) : ClassBound c (p >>= f) 0 :=
  ClassBound.bind h hf

theorem StateBound.bind_zero {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} (h : StateBound c p 0) (hf : ∀ a, StateBound c (f a) 0) :
    StateBound c (p >>= f) 0 :=
  StateBound.bind h hf

theorem StateBound.lift_zero {σ α : Type} {p : PartyM C E RealSpec α} (h : ClassBound c p 0) :
    StateBound c (StateT.lift p : StateT σ (PartyM C E RealSpec) α) 0 :=
  StateBound.lift h

theorem StateBound.zero_bind {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n : ℕ} (h : StateBound c p 0) (hf : ∀ a, StateBound c (f a) n) :
    StateBound c (p >>= f) n :=
  (StateBound.bind h hf).mono (Nat.zero_add _).le

theorem StateBound.bind_zero' {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n : ℕ} (h : StateBound c p n) (hf : ∀ a, StateBound c (f a) 0) :
    StateBound c (p >>= f) n :=
  (StateBound.bind h hf).mono (Nat.add_zero _).le

/-- The calls of `PRG` are in class `stream`. -/
theorem noCall_prgBits (hc : c ≠ .stream) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    NoCall (RoIn c) (prgBits name key ρ idx count) := by
  unfold prgBits
  exact noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => hc h) fun _ => noCall_pure _ _

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

omit [Field E] [Algebra Bit E] in
theorem noCall_bitCodec (hc : c ≠ .stream) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    NoCall (RoIn c) ((bitCodec (C := C) (E := E)).draw name key ρ idx count) :=
  noCall_prgBits hc name key ρ idx count

theorem noCall_elementCodec (hc : c ≠ .stream) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    NoCall (RoIn c) ((elementCodec K).draw name key ρ idx count) :=
  noCall_bind _ (noCall_prgBits hc _ _ _ _ _) fun _ => noCall_pure _ _

omit [Field E] [Algebra Bit E] in
theorem prssRandomness_bound {R : Type} [Zero R] (codec : Codec C E R)
    (hdraw : ∀ name key ρ idx count, NoCall (RoIn c) (codec.draw name key ρ idx count)) (idx count : ℕ) :
    StateBound c (prssRandomness ctx codec idx count : RunM C E RealSpec _) 0 := by
  unfold prssRandomness freshLabel
  refine StateBound.bind_zero (StateBound.modifyGet _) fun ρ => ?_
  refine StateBound.bind_zero (StateBound.lift_zero (ClassBound.oracleStep_zero
    (noCall_mapM _ _ _ fun T => ?_))) fun _ => ?_
  · split_ifs
    · exact hdraw _ _ _ _ _
    · exact noCall_pure _ _
  refine StateBound.bind_zero (StateBound.lift_zero (ClassBound.oracleStep_zero
    (noCall_mapM _ _ _ fun j => ?_))) fun _ => StateBound.pure _
  split
  · exact noCall_pure _ _
  · exact hdraw _ _ _ _ _

theorem record_bound {R : Type} (codec : Codec C E R) (mode : ReshareMode) (z : Shares C R) (count : ℕ) :
    StateBound c (record K ctx codec mode z count : RunM C E RealSpec Unit) 0 :=
  StateBound.modify _

theorem reshare_bound {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : StateBound c (reshare K ctx codec randomness v count : RunM C E RealSpec _) 0 := by
  rcases randomness with ⟨r, Z⟩
  unfold reshare
  exact StateBound.bind_zero (StateBound.lift_zero (ClassBound.exchange _)) fun _ =>
    StateBound.bind_zero (record_bound K ctx _ _ _ _) fun _ => StateBound.pure _

theorem reshareCollector_bound (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    StateBound c (reshareCollector K ctx randomness v count : RunM C E RealSpec _) 0 := by
  rcases randomness with ⟨r, Z⟩
  unfold reshareCollector
  exact StateBound.bind_zero (StateBound.lift_zero (ClassBound.exchange _)) fun _ =>
    StateBound.bind_zero (StateBound.lift_zero (ClassBound.exchange _)) fun _ =>
      StateBound.bind_zero (record_bound K ctx _ _ _ _) fun _ => StateBound.pure _

theorem openSh_bound (v : ℕ → E) (count : ℕ) : ClassBound c (openSh K ctx v count : PartyM C E RealSpec _) 0 :=
  ClassBound.bind_zero (ClassBound.exchange _) fun _ =>
    ClassBound.bind_zero (ClassBound.require _) fun _ => ClassBound.pure _

/-- The calls of the challenge search are in class `challenge`. -/
theorem noCall_findChallenge (hc : c ≠ .challenge) (key : HashOutput) :
    ∀ tries index, NoCall (RoIn c) (findChallenge K key tries index) := by
  intro tries
  induction tries with
  | zero => intro index; exact noCall_pure _ _
  | succ tries ih =>
    intro index
    unfold findChallenge
    refine noCall_bind _ (noCall_hashQuery _ fun h => hc (by simpa [RoIn, InClass, queryClass, eq_comm] using h))
      fun r => ?_
    dsimp only
    generalize Classical.propDecidable (elementOfHash K r ≠ 0 ∧ elementOfHash K r ≠ 1) = d
    rcases d with ⟨_ | _, _⟩
    · exact ih _
    · exact noCall_pure _ _

theorem coin_bound (hc : c ≠ .stream) (count : ℕ) :
    StateBound c ((realCheckBuildingBlocks K ctx).coin count : RunM C E RealSpec _) 0 := by
  unfold realCheckBuildingBlocks coinWith
  exact StateBound.bind_zero (prssRandomness_bound ctx _ (noCall_elementCodec K hc) _ _) fun _ =>
    StateBound.bind_zero (StateBound.lift_zero (openSh_bound K ctx _ _)) fun _ => StateBound.pure _

theorem extendMult_bound (hc : c ≠ .stream) (products : List (Product C E)) :
    StateBound c ((realCheckBuildingBlocks K ctx).extendMult products : RunM C E RealSpec _) 0 := by
  unfold realCheckBuildingBlocks
  exact StateBound.bind_zero (prssRandomness_bound ctx _ (noCall_elementCodec K hc) _ _) fun _ =>
    reshare_bound K ctx _ _ _ _

theorem coinKey_bound (hc : c ≠ .stream) (hc' : c ≠ .challenge) :
    StateBound c (coinKey K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) 0 := by
  unfold coinKey
  exact StateBound.bind_zero StateBound.get fun _ => StateBound.bind_zero (coin_bound K ctx hc 2) fun _ =>
    StateBound.lift_zero (ClassBound.oracleStep_zero (noCall_hashQuery _ fun h => hc'
      (by simpa [RoIn, InClass, queryClass, eq_comm] using h)))

theorem challenge_bound (hc : c ≠ .stream) (hc' : c ≠ .challenge) :
    StateBound c (challenge K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) 0 := by
  unfold challenge
  refine StateBound.bind_zero (coinKey_bound K ctx hc hc') fun key => ?_
  refine StateBound.bind_zero (StateBound.lift_zero (ClassBound.oracleStep_zero
    (noCall_findChallenge K hc' key _ _))) fun r => ?_
  split
  · exact StateBound.pure _
  · exact StateBound.lift_zero ClassBound.failure

theorem expand_bound (hc' : c ≠ .challenge) (key : HashOutput) (count : ℕ) :
    StateBound c (expand K key count : RunM C E RealSpec _) 0 := by
  unfold expand
  exact StateBound.lift_zero (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun _ =>
    noCall_map _ _ (noCall_hashQuery _ fun h => hc' (by simpa [RoIn, InClass, queryClass, eq_comm] using h))))

/-- The digest calls of one comparison, two for each held term. -/
def digestCost (C : Committee) (c : HashClass) : ℕ := if c = .digest then C.terms.length * 2 else 0

/-- The copy calls of one `OpenRep`, two for each term. -/
def copyCost (C : Committee) (c : HashClass) : ℕ := if c = .copy then C.terms.length * 2 else 0

omit [Field E] [Algebra Bit E] in
theorem compareDigests_bound (salts : Shares C Bit) :
    StateBound c (compareDigests ctx salts : RunM C E RealSpec Unit) (digestCost C c) := by
  unfold compareDigests digestCost
  split_ifs with hc
  · refine (StateBound.bind (n := 0) StateBound.get fun st => ?_).mono (Nat.zero_add _).le
    refine (StateBound.bind (m := 0) (StateBound.lift (ClassBound.oracleStep
      (queryBound_mapM _ _ 2 C.terms fun T _ => ?_))) fun _ => ?_).mono (Nat.add_zero _).le
    · split_ifs
      · exact isQueryBoundP_bind ((hashQuery_queryBound _).of_imp fun _ _ => trivial) fun _ _ =>
          (hashQuery_queryBound _).of_imp fun _ _ => trivial
      · exact (isQueryBoundP_pure _ _ _)
    · exact StateBound.bind_zero (StateBound.lift_zero (ClassBound.exchange _)) fun _ =>
        StateBound.lift_zero (ClassBound.require _)
  · have hq : ∀ q : Query C, queryClass q = .digest → NoCall (RoIn c) (hashQuery q) := fun q hq =>
      noCall_hashQuery _ fun h => by
        rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
          simp_all [RoIn, InClass, queryClass, eq_comm]
    refine StateBound.bind_zero StateBound.get fun st => ?_
    refine StateBound.bind_zero (StateBound.lift_zero (ClassBound.oracleStep_zero
      (noCall_mapM _ _ _ fun T => ?_))) fun _ => ?_
    · split_ifs
      · exact noCall_bind _ (hq _ rfl) fun _ => hq _ rfl
      · exact noCall_pure _ _
    · exact StateBound.bind_zero (StateBound.lift_zero (ClassBound.exchange _)) fun _ =>
        StateBound.lift_zero (ClassBound.require _)

theorem openRep_bound (v : Shares C Bit) (count : ℕ) :
    ClassBound c (openRep K ctx v count : PartyM C E RealSpec _) (copyCost C c) := by
  unfold openRep copyCost
  split_ifs with hc
  · have hmap : ∀ f : C.Term → Query C, IsQueryBoundP (C.terms.mapM fun T => hashQuery (f T)) (RoIn c)
        (C.terms.length * 1) := fun f =>
      queryBound_mapM _ _ 1 C.terms fun T _ => (hashQuery_queryBound _).of_imp fun _ _ => trivial
    refine (ClassBound.bind (ClassBound.oracleStep (hmap _)) fun _ =>
      ClassBound.bind (m := C.terms.length * 1) (ClassBound.exchange _) fun _ =>
        ClassBound.bind (m := 0) (ClassBound.oracleStep (hmap _)) fun _ =>
          ClassBound.bind_zero (ClassBound.require _) fun _ => ClassBound.pure _).mono (by omega)
  · have hq : ∀ T : C.Term, ∀ l, NoCall (RoIn c) (hashQuery (C := C) (.copy l)) := fun T l =>
      noCall_hashQuery _ fun h => hc (by simpa [RoIn, InClass, queryClass, eq_comm] using h)
    exact ClassBound.bind_zero (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun T => hq T _)) fun _ =>
      ClassBound.bind_zero (ClassBound.exchange _) fun _ =>
        ClassBound.bind_zero (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun T => hq T _)) fun _ =>
          ClassBound.bind_zero (ClassBound.require _) fun _ => ClassBound.pure _

/-- The real check makes the digest calls of one comparison. -/
theorem check_bound (hc : c ≠ .stream) (hc' : c ≠ .challenge) (tuples : List (Tuple C)) :
    StateBound c (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) (digestCost C c) := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact (StateBound.pure _).mono (Nat.zero_le _)
  refine StateBound.zero_bind (coinKey_bound K ctx hc hc') fun key => ?_
  refine StateBound.zero_bind (expand_bound K hc' key _) fun τ => ?_
  refine StateBound.zero_bind (StateBound.lift_zero (ClassBound.require _)) fun _ => ?_
  refine StateBound.zero_bind (StateBound.foldlM _ 0 (fun v j => ?_) _ _ |>.mono (by simp)) fun v => ?_
  · rcases v with ⟨xs, ys, D⟩
    exact StateBound.bind_zero (extendMult_bound K ctx hc _) fun _ =>
      StateBound.bind_zero (challenge_bound K ctx hc hc') fun _ => StateBound.pure _
  rcases v with ⟨xs, ys, D⟩
  refine StateBound.zero_bind (StateBound.foldlM _ 0 (fun v j => ?_) _ _ |>.mono (by simp)) fun v => ?_
  · rcases v with ⟨A, B, D⟩
    exact StateBound.bind_zero (extendMult_bound K ctx hc _) fun _ =>
      StateBound.bind_zero (challenge_bound K ctx hc hc') fun _ => StateBound.pure _
  rcases v with ⟨A, B, D⟩
  refine StateBound.zero_bind (prssRandomness_bound ctx _ (noCall_elementCodec K hc) _ _) fun w => ?_
  refine StateBound.zero_bind (extendMult_bound K ctx hc _) fun q => ?_
  refine StateBound.zero_bind (prssRandomness_bound ctx _ (noCall_bitCodec hc) _ _) fun salts => ?_
  refine StateBound.bind_zero' (compareDigests_bound ctx _) fun _ => ?_
  exact StateBound.bind_zero (challenge_bound K ctx hc hc') fun _ =>
    StateBound.bind_zero (StateBound.lift_zero (openSh_bound K ctx _ _)) fun _ =>
      StateBound.lift_zero (ClassBound.require _)

/-- `mult` of the real run makes no call outside the class `stream`. -/
theorem mult_bound (hc : c ≠ .stream) (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) :
    StateBound c ((realRunBuildingBlocks K ctx mode).mult x y count : RunM C E RealSpec _) 0 := by
  unfold realRunBuildingBlocks reshareWith
  refine StateBound.zero_bind (prssRandomness_bound ctx _ (noCall_bitCodec hc) _ _) fun r => ?_
  cases mode
  · exact reshare_bound K ctx _ _ _ _
  · exact reshareCollector_bound K ctx _ _ _

/-- A run of a batch makes the digest calls of one comparison and the copy calls of one `OpenRep`. -/
theorem runJobs_bound (hc : c ≠ .stream) (hc' : c ≠ .challenge) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    StateBound c (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _)
      (digestCost C c + copyCost C c) := by
  unfold runJobs
  refine StateBound.zero_bind (StateBound.foldlM _ 0 (fun v layer => ?_) _ _ |>.mono (by simp)) fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact StateBound.bind_zero (mult_bound K ctx hc mode _ _ _) fun _ => StateBound.pure _
  rcases v with ⟨wires, tuples⟩
  refine StateBound.zero_bind (?_ : StateBound c ((realRunBuildingBlocks K ctx mode).rerand _ _) 0) fun v' => ?_
  · unfold realRunBuildingBlocks
    exact StateBound.zero_bind (prssRandomness_bound ctx _ (noCall_bitCodec hc) _ _) fun _ =>
      reshare_bound K ctx _ _ _ _
  refine StateBound.bind (check_bound K ctx hc hc' _) fun _ => ?_
  exact StateBound.bind_zero' (StateBound.lift (openRep_bound K ctx _ _)) fun _ => StateBound.pure _

omit [Field E] [Algebra Bit E] in
theorem noCall_flatMapM {α β : Type} {p : (RoSpec C).Domain → Prop} (f : α → OracleComp (RoSpec C) (List β))
    (hf : ∀ a, NoCall p (f a)) : ∀ xs : List α, NoCall p (xs.flatMapM f)
  | [] => noCall_pure _ _
  | a :: xs => by
    rw [List.flatMapM_cons]
    exact noCall_bind _ (hf a) fun _ => noCall_bind _ (noCall_flatMapM f hf xs) fun _ => noCall_pure _ _

omit [Field E] [Algebra Bit E] in
/-- The input sharings call `H` only on `.prf`. -/
theorem inputShares_bound (hc : c ≠ .signing) (job : Job) :
    ClassBound c (inputShares ctx job : PartyM C E RealSpec _) 0 := by
  unfold inputShares
  refine ClassBound.bind_zero (ClassBound.oracleStep_zero (noCall_mapM _ _ _ fun T => ?_)) fun _ =>
    ClassBound.pure _
  split_ifs
  · exact noCall_flatMapM _ (fun x => noCall_map _ _ (noCall_map _ _ (noCall_hashQuery _ fun h =>
      hc (by simpa [RoIn, InClass, queryClass, eq_comm] using h)))) _
  · exact noCall_pure _ _

end Blocks

/-! ## The runs of a tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) {c : HashClass}

/-- One ceremony makes the calls of its batches. -/
theorem ceremonyRun_bound (hc : c ≠ .stream) (hc' : c ≠ .challenge) (hc'' : c ≠ .signing) (hp : c ≠ .prssSetup)
    (i : C.Party) (keys : Keys C) (jobs : List Job) :
    StateBound c (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _)
      ((chunks settings.batchSize jobs).length * (digestCost C c + copyCost C c)) := by
  unfold ceremonyRun batched
  refine StateBound.zero_bind (StateBound.lift_zero (prssSetup_bound hp i)) fun prss => ?_
  refine StateBound.bind_zero' (StateBound.mapM _ _ (fun batch => ?_) _) fun _ => StateBound.pure _
  refine StateBound.zero_bind StateBound.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine StateBound.zero_bind (StateBound.lift_zero ((ClassBound.mapM _ 0 (fun job => inputShares_bound _ hc'' job)
    _).mono (by simp))) fun inputs => ?_
  refine StateBound.bind_zero' (StateBound.lift (runJobs_bound K _ hc hc' _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact StateBound.bind_zero (StateBound.set _) fun _ => StateBound.pure _

omit [Field E] [Algebra Bit E] in
theorem lift_tweakable_bound (hc : c ≠ .signing) {α : Type} (oa : OracleComp HashSpec α) :
    StateBound c (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) 0 :=
  StateBound.lift_zero (ClassBound.oracleStep_zero (noCall_of_onlySign hc (GameCount.onlySign_tweakable _)))

omit [Field E] [Algebra Bit E] in
/-- The signature ceremony has the same number of batches for each encoding. -/
theorem chunks_signJobs (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    (chunks settings.batchSize (signJobs b encoding)).length =
      (chunks settings.batchSize (signJobs b fun _ => digit 0)).length := by
  have hc : ∀ {α : Type} (items : List α),
      (chunks settings.batchSize items).length = (items.length + settings.batchSize - 1) / settings.batchSize :=
    fun items => by unfold chunks; rw [List.length_map, List.length_range]
  have hs : ∀ encoding : Encoding, (signJobs b encoding).length = chainCount := fun encoding => by
    unfold signJobs; rw [List.length_map, List.length_finRange]
  rw [hc, hc, hs, hs]

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree make the calls of the batches of the tree. -/
theorem ceremonyOutput_bound (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), StateBound c (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (P : ℕ)
    (hrun : ∀ jobs, StateBound c (run jobs) ((chunks settings.batchSize jobs).length * P)) (top : TopTree)
    (tree : Tree) :
    StateBound c (ceremonyOutput lift parameter run top tree) (treeBatches settings tree * P) := by
  cases tree with
  | top =>
    rw [treeBatches.eq_1]
    unfold ceremonyOutput
    refine StateBound.bind_zero' (hrun topJobs) fun out => ?_
    rcases out with _ | outputs
    · exact StateBound.pure _
    · exact StateBound.bind_zero (hlift _) fun _ => StateBound.pure _
  | bottom b =>
    rw [treeBatches.eq_2, Nat.add_mul]
    unfold ceremonyOutput
    refine StateBound.bind (hrun (bottomJobs b)) fun out => ?_
    rcases out with _ | outputs
    · exact (StateBound.pure _).mono (Nat.zero_le _)
    refine StateBound.zero_bind (hlift _) fun root => ?_
    refine StateBound.zero_bind (hlift _) fun base => ?_
    refine StateBound.zero_bind (hlift _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact (StateBound.pure _).mono (Nat.zero_le _)
    rw [← chunks_signJobs settings b encoding]
    refine StateBound.bind_zero' (hrun _) fun out => ?_
    rcases out with _ | values
    · exact StateBound.pure _
    refine StateBound.bind_zero (hlift _) fun path => ?_
    refine StateBound.bind_zero (hlift _) fun topRoot => ?_
    split_ifs
    · exact StateBound.pure _
    · exact StateBound.pure _

/-- The ceremonies of a tree at one operator make the calls of the batches of the tree. -/
theorem newTree_bound (hc : c = .digest ∨ c = .copy) (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    ClassBound c (newTree K circuits settings i keys top tree : PartyM C E RealSpec _)
      (treeBatches settings tree * (digestCost C c + copyCost C c)) := by
  have hs : c ≠ .stream := by rcases hc with rfl | rfl <;> decide
  have hch : c ≠ .challenge := by rcases hc with rfl | rfl <;> decide
  have hsig : c ≠ .signing := by rcases hc with rfl | rfl <;> decide
  have hp : c ≠ .prssSetup := by rcases hc with rfl | rfl <;> decide
  have hrun := ceremonyOutput_bound settings (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => lift_tweakable_bound hsig oa) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) _
    (fun jobs => ceremonyRun_bound K circuits settings hs hch hsig hp i keys jobs) top tree (0, 0)
  unfold newTree
  refine (ClassBound.bind (m := 0) ?_ fun out => ?_).mono (Nat.add_zero _).le
  · unfold StateT.run'
    unfold ClassBound at hrun ⊢
    simp only [OptionT.run_map]
    exact (isQueryBoundP_map_iff _ _ _).2 hrun
  · rcases out with _ | output
    · exact ClassBound.failure
    · exact ClassBound.pure _

/-- The program of an operator in a run of a tree makes the calls of the batches of the tree. -/
theorem treeProgram_bound (hc : c = .digest ∨ c = .copy) (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    ClassBound c (treeProgram K circuits settings i operator tree)
      (treeBatches settings tree * (digestCost C c + copyCost C c)) := by
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact ClassBound.failure.mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact newTree_bound K circuits settings hc _ _ _ _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact ClassBound.failure.mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact ClassBound.failure.mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact ClassBound.failure.mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact newTree_bound K circuits settings hc _ _ _ _

/-- One run of a tree on the network makes at most `treeBatches settings tree * termHashes C` honest
calls of class `digest` or `copy`. -/
theorem treeHonest (hc : c = .digest ∨ c = .copy) :
    FirstCounts.TreeHonest K circuits settings c fun tree => treeBatches settings tree * termHashes C := by
  intro D net tree s
  rw [GameCount.bound_iff]
  refine (executePhase_bound c D net _ _ _ (fun _ => treeBatches settings tree * (digestCost C c + copyCost C c))
    fun j _ => treeProgram_bound K circuits settings hc j _ tree).mono (le_of_eq ?_)
  have hcost : digestCost C c + copyCost C c = C.terms.length * 2 := by
    rcases hc with rfl | rfl <;> simp [digestCost, copyCost]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hcost, check_terms_length]
  unfold termHashes termCount
  ring

end Tree

/-! ## The premises of the count of the classes `digest` and `copy` -/

section Premises

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)
end Premises

end DigestBudgets

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.signQuiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.signQuiet

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.seedHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.seedHonest

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.treeHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.treeHonest
