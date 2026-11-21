import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.ProgramBlock

/-!
# The two rewrites on the real network

`ProvWhole p` states that each local call of `Touch` of the operator program `p` is inside a check
block, namely the draws of the salts of the held terms, the pair draws and the digest calls, with a
continuation that does not read the salts. `prov_advance_bind` gives `Prov []` for the local steps of
such a program and a continuation for each stopped program with `ProvWhole` continuations. The
network walk `prov_executePhase` gives `Prov []` for a phase whose honest programs have `ProvWhole`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (PartyP HonestP)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

/-! ## The programs with check blocks -/

section Whole

variable {C : Committee} {E : Type}

/-- A local call of `Touch`. -/
def LocalTouch (t : (LocalSpec C).Domain) : Prop := Touch (C := C) (.inr t)

/-- Each local call of `Touch` of the program is inside a check block. -/
inductive ProvWhole {γ : Type} : OracleComp (PartySpec C E RealSpec) γ → Prop
  | pure (x : γ) : ProvWhole (pure x)
  | queryLocal (q : (LocalSpec C).Domain) (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) γ)
      (hq : ¬ LocalTouch q) (h : ∀ r, ProvWhole (k r)) : ProvWhole (.liftBind (.inl (.inl q)) k)
  | round (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ r, ProvWhole (k r)) : ProvWhole (.liftBind (.inl (.inr out)) k)
  | block (self : C.Party) (keyOf : C.Term → HashOutput) (ρ : ℕ) {Z : Type} (pairs : OracleComp (RoSpec C) Z)
      (hpairs : NoCall (fun t => Touch (C := C) (.inr (.inr t))) pairs) (hist : C.Term → List Bit)
      (k : Z → List HashOutput → OracleComp (PartySpec C E RealSpec) γ) (h : ∀ z ds, ProvWhole (k z ds)) :
      ProvWhole (liftComp (liftComp (termDrawsOn self keyOf ρ C.terms) (LocalSpec C)) (PartySpec C E RealSpec) >>=
        fun r => liftComp (liftComp pairs (LocalSpec C)) (PartySpec C E RealSpec) >>= fun z =>
          liftComp (liftComp (digestsAt self C.terms (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) hist)
            (LocalSpec C)) (PartySpec C E RealSpec) >>= fun ds => k z ds)

theorem ProvWhole.bind {γ δ : Type} {p : OracleComp (PartySpec C E RealSpec) γ}
    {f : γ → OracleComp (PartySpec C E RealSpec) δ} (hp : ProvWhole p) (hf : ∀ x, ProvWhole (f x)) :
    ProvWhole (p >>= f) := by
  induction hp with
  | pure x => rw [pure_bind]; exact hf x
  | queryLocal q k hq _ ih => exact ProvWhole.queryLocal q _ hq ih
  | round out k _ ih => exact ProvWhole.round out _ ih
  | block self keyOf ρ pairs hpairs hist k _ ih =>
    simp only [bind_assoc]
    exact ProvWhole.block self keyOf ρ pairs hpairs hist _ ih

/-- A program with no local call of `Touch` has its calls of `Touch` inside check blocks. -/
theorem ProvWhole.of_noCall {γ : Type} (p : OracleComp (PartySpec C E RealSpec) γ)
    (h : IsQueryBoundP p (PartyP (E := E) LocalTouch) 0) : ProvWhole p := by
  induction p using OracleComp.inductionOn with
  | pure x => exact ProvWhole.pure x
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | out) | input
    · have hq : ¬ LocalTouch q := h.1.resolve_right (by omega)
      exact ProvWhole.queryLocal q _ hq fun r => ih r (by
        have hq' : ¬ PartyP (E := E) LocalTouch (Sum.inl (Sum.inl q)) := hq
        simpa only [hq', ↓reduceIte] using h.2 r)
    · exact ProvWhole.round out _ fun r => ih r (by
        have ho : ¬ PartyP (E := E) LocalTouch (Sum.inl (Sum.inr out)) := not_false
        simpa only [ho, ↓reduceIte] using h.2 r)
    · exact input.elim

/-- A stopped program whose continuation has its calls of `Touch` inside check blocks. -/
def StepProv {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ k => ∀ inbox, ProvWhole (k inbox)
  | .call _ _ => True

end Whole

/-! ## The local steps and the network -/

section Network

variable {C : Committee} {E : Type} (D : C.Coalition) (δ : Fin 256 → Bit)

theorem prov_query (q : ProvQueue C) (t : (WorldSpec C).Domain) (ht : ¬ Touch t) :
    Prov D δ q (liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) := by
  refine prov_of_noTouch D δ q _ ?_
  rw [noCall_iff]
  exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h ht

/-- The local steps of a program with check blocks, and then a continuation with `Prov []` for each
stopped program with check blocks, have `Prov []`. -/
theorem prov_advance_bind {α β : Type} {p : OracleComp (PartySpec C E RealSpec) (Option α)} (hp : ProvWhole p)
    (g : Step C E RealSpec α → OracleComp (WorldSpec C) β) (hg : ∀ st, StepProv st → Prov D δ [] (g st)) :
    Prov D δ [] (free (advance p) >>= g) := by
  induction hp generalizing g with
  | pure x =>
    rw [advance_pure, free_pure, pure_bind]
    exact hg _ trivial
  | queryLocal q k hq _ ih =>
    have e : free (advance (.liftBind (.inl (.inl q)) k : OracleComp (PartySpec C E RealSpec) (Option α))) =
        (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>= fun u => free (advance (k u)) := by
      change free (advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inl q))) >>= k)) = _
      rw [advance_query_bind, free_bind]
      rfl
    rw [e, bind_assoc]
    exact (prov_query D δ [] (.inr q) hq).bind fun u => ih u g hg
  | round out k h =>
    change Prov D δ [] (free (pure (Step.wait out k)) >>= g)
    rw [free_pure, pure_bind]
    exact hg _ h
  | block self keyOf ρ pairs hpairs hist k _ ih =>
    rw [advance_liftComp_bind, free_bind]
    simp only [advance_liftComp_bind, free_bind, bind_assoc]
    exact prov_block D δ self keyOf ρ pairs hpairs hist _ fun z ds => ih z ds g hg

theorem prov_sequenceFin_bind {α β : Type} : ∀ {N : ℕ} (oa : Fin N → OracleComp (PartySpec C E RealSpec) (Option α)),
    (∀ i, ProvWhole (oa i)) → ∀ (k : (Fin N → Step C E RealSpec α) → OracleComp (WorldSpec C) β),
      (∀ st, (∀ i, StepProv (st i)) → Prov D δ [] (k st)) →
      Prov D δ [] ((OverPermutation.sequenceFin fun i => free (advance (oa i))) >>= k)
  | 0, _, _, k, hk => by
    simp only [OverPermutation.sequenceFin, pure_bind]
    exact hk _ fun i => i.elim0
  | N + 1, oa, h, k, hk => by
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    refine prov_advance_bind D δ (h 0) _ fun st0 hs0 => ?_
    exact prov_sequenceFin_bind (fun i : Fin N => oa i.succ) (fun i => h i.succ) (fun st => k (Fin.cases st0 st))
      fun st hst => hk _ fun i => Fin.cases hs0 hst i

theorem provWhole_roundResume {α : Type} (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec α) (h : ∀ j, StepProv (steps j)) (j : C.Party) :
    ProvWhole (roundResume D sent steps j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact ProvWhole.pure _
  | call input k => exact ProvWhole.pure _
  | wait out k =>
    dsimp only
    split_ifs
    · exact ProvWhole.pure _
    · rw [hs] at hj
      exact hj _

theorem noTouch_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) : NoCall Touch (worldRoles.adversary oa) := by
  rw [noCall_iff]
  refine IsQueryBoundP.of_imp (fun t ht => ?_) (SetupBudgets.honestP_adversary (LocalTouch (C := C)) oa)
  rcases t with t | t
  · exact ht.elim
  · exact ht

variable {Ia : Type} (A : Adversary C E Ia PEmpty PEmpty)

/-- One round on the real network, and then a continuation with `Prov []` for steps with check
blocks, has `Prov []`. -/
theorem prov_stepRound_bind {α β : Type} (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (h : ∀ j, StepProv (steps j))
    (k : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) → OracleComp (WorldSpec C) β)
    (hk : ∀ st, (∀ j, StepProv (st.2.1 j)) → Prov D δ [] (k st)) :
    Prov D δ [] (stepRound worldRoles D A noFunctionality state steps >>= k) := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  simp only [bind_assoc, pure_bind]
  refine (prov_of_noTouch D δ [] _ (noTouch_adversary _)).bind fun result => ?_
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
  have hseq := prov_sequenceFin_bind D δ (fun j => roundResume D result.2 steps j)
    (provWhole_roundResume D result.2 steps h) (fun st => k (result.1, st, result.2)) fun st hst => hk _ hst
  rw [← he] at hseq
  convert hseq using 3
  funext j
  cases steps j <;> rfl

/-- The rounds on the real network from steps with check blocks have `Prov []`. -/
theorem prov_executeRounds {α : Type} :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α), (∀ j, StepProv (steps j)) →
      Prov D δ [] (executeRounds worldRoles D A noFunctionality fuel state steps)
  | 0, state, steps, h => prov_pure _ _
  | fuel + 1, state, steps, h => by
    unfold executeRounds
    split_ifs
    · exact prov_pure _ _
    · exact prov_stepRound_bind D δ A state steps h _ fun st hst => prov_executeRounds fuel st.1 st.2.1 hst

/-- A phase on the real network whose honest programs have check blocks has `Prov []`. -/
theorem prov_executePhase {α : Type} (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ j, j ∉ D.1 → ProvWhole (program j).run) :
    Prov D δ [] (executePhase worldRoles D A noFunctionality fuel state program) := by
  unfold executePhase startSteps
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs
    · simp only [advance_pure, free_pure]
    · rfl
  change Prov D δ [] ((OverPermutation.sequenceFin _) >>= _)
  rw [he]
  refine prov_sequenceFin_bind D δ _ (fun j => ?_) _ fun st hst => prov_executeRounds D δ A fuel state st hst
  split_ifs with hj
  · exact ProvWhole.pure _
  · exact hp j hj

end Network

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.prov_executePhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.prov_executePhase
