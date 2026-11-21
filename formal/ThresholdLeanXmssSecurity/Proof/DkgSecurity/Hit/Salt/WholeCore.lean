import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Cache

/-!
# Whole salt draws and an invariant of the world at the rounds

`SaltWhole p` states that each call of `SaltDraw` of the operator program `p` is the first call of a
whole draw `prgBits (.term T) key ρ 2 256`, which reads the 256 cells of one salt in one local step.

`KeepsQ impl Inv oa Q` states that from each world with `Inv`, each end of `oa` under `impl` has `Inv`
and a result with `Q`. Two facts on the world give it for the network.

* `CallKeeps`, each call that is not an honest call of `SaltDraw` keeps `Inv`.
* `DrawKeeps`, each whole draw on the free copy keeps `Inv`.

`keepsQ_advance` gives `KeepsQ` for the local steps of an operator with `SaltWhole`, and
`keepsQ_executePhase` gives it for a phase on the real network whose honest programs have `SaltWhole`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (PartyP HonestP)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

/-! ## The programs with whole salt draws -/

section Whole

variable {C : Committee} {E : Type}

/-- Each call of `SaltDraw` of the program is the first call of a whole draw of a salt. -/
inductive SaltWhole {γ : Type} : OracleComp (PartySpec C E RealSpec) γ → Prop
  | pure (x : γ) : SaltWhole (pure x)
  | queryLocal (q : (LocalSpec C).Domain) (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) γ)
      (hq : ¬ SaltDraw q) (h : ∀ r, SaltWhole (k r)) : SaltWhole (.liftBind (.inl (.inl q)) k)
  | round (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ r, SaltWhole (k r)) : SaltWhole (.liftBind (.inl (.inr out)) k)
  | draw (T : C.Term) (key : HashOutput) (ρ : ℕ) (k : (ℕ → Bit) → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ bits, SaltWhole (k bits)) :
      SaltWhole (liftComp (liftComp (prgBits (.term T) key ρ 2 256) (LocalSpec C)) (PartySpec C E RealSpec) >>= k)

theorem SaltWhole.bind {γ δ : Type} {p : OracleComp (PartySpec C E RealSpec) γ}
    {f : γ → OracleComp (PartySpec C E RealSpec) δ} (hp : SaltWhole p) (hf : ∀ x, SaltWhole (f x)) :
    SaltWhole (p >>= f) := by
  induction hp with
  | pure x => rw [pure_bind]; exact hf x
  | queryLocal q k hq _ ih => exact SaltWhole.queryLocal q _ hq ih
  | round out k _ ih => exact SaltWhole.round out _ ih
  | draw T key ρ k _ ih => rw [bind_assoc]; exact SaltWhole.draw T key ρ _ ih

/-- A program with no local call of `SaltDraw` has whole salt draws. -/
theorem SaltWhole.of_noCall {γ : Type} (p : OracleComp (PartySpec C E RealSpec) γ)
    (h : IsQueryBoundP p (PartyP (E := E) SaltDraw) 0) : SaltWhole p := by
  induction p using OracleComp.inductionOn with
  | pure x => exact SaltWhole.pure x
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | out) | input
    · have hq : ¬ SaltDraw q := h.1.resolve_right (by omega)
      exact SaltWhole.queryLocal q _ hq fun r => ih r (by
        have hq' : ¬ PartyP (E := E) SaltDraw (Sum.inl (Sum.inl q)) := hq
        simpa only [hq', ↓reduceIte] using h.2 r)
    · exact SaltWhole.round out _ fun r => ih r (by
        have ho : ¬ PartyP (E := E) SaltDraw (Sum.inl (Sum.inr out)) := not_false
        simpa only [ho, ↓reduceIte] using h.2 r)
    · exact input.elim

/-- A stopped program whose continuation has whole salt draws. -/
def StepWhole {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ k => ∀ inbox, SaltWhole (k inbox)
  | .call _ _ => True

end Whole

/-! ## The invariant of the world -/

section World

variable {C : Committee} {E : Type} {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp))
  (Inv : W → Prop)

/-- From each world with `Inv`, each end of `oa` has `Inv` and a result with `Q`. -/
def KeepsQ {α : Type} (oa : OracleComp (WorldSpec C) α) (Q : α → Prop) : Prop :=
  ∀ w, Inv w → ∀ z ∈ support ((simulateQ impl oa).run w), Inv z.2 ∧ Q z.1

/-- Each call that is not an honest call of `SaltDraw` keeps `Inv`. -/
def CallKeeps : Prop :=
  ∀ t, ¬ HonestP SaltDraw t → ∀ w, Inv w → ∀ z ∈ support ((impl t).run w), Inv z.2

/-- Each whole draw of a salt on the free copy keeps `Inv`. -/
def DrawKeeps : Prop :=
  ∀ (T : C.Term) (key : HashOutput) (ρ : ℕ),
    KeepsQ impl Inv (free (liftComp (prgBits (.term T) key ρ 2 256) (LocalSpec C))) fun _ => True

variable {impl Inv}

theorem keepsQ_pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) : KeepsQ impl Inv (pure a) Q := by
  intro w hw z hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hw, h⟩

theorem KeepsQ.bind {α β : Type} {oa : OracleComp (WorldSpec C) α} {P : α → Prop}
    {f : α → OracleComp (WorldSpec C) β} {Q : β → Prop} (h : KeepsQ impl Inv oa P)
    (hf : ∀ a, P a → KeepsQ impl Inv (f a) Q) : KeepsQ impl Inv (oa >>= f) Q := by
  intro w hw z hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨hy₁, hy₂⟩ := h w hw y hy
  exact hf y.1 hy₂ y.2 hy₁ z hz

theorem KeepsQ.mono {α : Type} {oa : OracleComp (WorldSpec C) α} {P Q : α → Prop} (h : KeepsQ impl Inv oa P)
    (hPQ : ∀ a, P a → Q a) : KeepsQ impl Inv oa Q := fun w hw z hz =>
  ⟨(h w hw z hz).1, hPQ _ (h w hw z hz).2⟩

variable (impl Inv) in
/-- A world program with no honest call of `SaltDraw` keeps `Inv`. -/
theorem KeepsQ.of_noCall (h₁ : CallKeeps impl Inv) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : IsQueryBoundP oa (HonestP SaltDraw) 0) : KeepsQ impl Inv oa fun _ => True := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact keepsQ_pure trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ HonestP SaltDraw t := h.1.resolve_right (by omega)
    intro w hw z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact ih y.1 (by simpa only [ht, ↓reduceIte] using h.2 y.1) y.2 (h₁ t ht w hw y hy) z hz

/-! ## The local steps and the network -/

variable (h₁ : CallKeeps impl Inv) (h₂ : DrawKeeps impl Inv)
include h₁ h₂

/-- The local steps of an operator with whole salt draws keep `Inv` and stop at a step whose
continuation has whole salt draws. -/
theorem keepsQ_advance {α : Type} {p : OracleComp (PartySpec C E RealSpec) (Option α)} (hp : SaltWhole p) :
    KeepsQ impl Inv (free (advance p)) StepWhole := by
  induction hp with
  | pure x =>
    rw [advance_pure, free_pure]
    exact keepsQ_pure trivial
  | queryLocal q k hq _ ih =>
    have e : free (advance (.liftBind (.inl (.inl q)) k : OracleComp (PartySpec C E RealSpec) (Option α))) =
        (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>= fun u => free (advance (k u)) := by
      change free (advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inl q))) >>= k)) = _
      rw [advance_query_bind, free_bind]
      rfl
    rw [e]
    refine KeepsQ.bind (P := fun _ => True) (fun w hw z hz => ⟨?_, trivial⟩) fun u _ => ih u
    rw [simulateQ_spec_query] at hz
    exact h₁ (.inr q) hq w hw z hz
  | round out k h =>
    change KeepsQ impl Inv (free (pure (Step.wait out k))) StepWhole
    rw [free_pure]
    exact keepsQ_pure h
  | draw T key ρ k _ ih =>
    rw [advance_liftComp_bind, free_bind]
    exact (h₂ T key ρ).bind fun bits _ => ih bits

omit h₁ h₂ in
/-- A sequence of world programs, each with its result property, keeps `Inv`. -/
theorem keepsQ_sequenceFin {β : Type} : ∀ {n : ℕ} (Q : Fin n → β → Prop) (f : Fin n → OracleComp (WorldSpec C) β),
    (∀ i, KeepsQ impl Inv (f i) (Q i)) → KeepsQ impl Inv (OverPermutation.sequenceFin f) fun v => ∀ i, Q i (v i)
  | 0, _, _, _ => keepsQ_pure fun i => i.elim0
  | n + 1, Q, f, hf => by
    simp only [OverPermutation.sequenceFin]
    refine (hf 0).bind fun a ha => ?_
    refine (keepsQ_sequenceFin (fun i => Q i.succ) (fun i => f i.succ) fun i => hf i.succ).bind fun t ht => ?_
    refine keepsQ_pure fun i => ?_
    cases i using Fin.cases with
    | zero => exact ha
    | succ i => exact ht i

omit h₂ in
/-- The adversary role keeps `Inv`. -/
theorem keepsQ_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    KeepsQ impl Inv (worldRoles.adversary oa) fun _ => True :=
  KeepsQ.of_noCall impl Inv h₁ _ (SetupBudgets.honestP_adversary SaltDraw oa)

omit h₁ h₂ in
theorem saltWhole_roundResume {α : Type} (D : C.Coalition) (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec α) (h : ∀ j, StepWhole (steps j)) (j : C.Party) :
    SaltWhole (roundResume D sent steps j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact SaltWhole.pure _
  | call input k => exact SaltWhole.pure _
  | wait out k =>
    dsimp only
    split_ifs
    · exact SaltWhole.pure _
    · rw [hs] at hj
      exact hj _

variable {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)

/-- One round on the real network keeps `Inv` and steps whose continuations have whole salt draws. -/
theorem keepsQ_stepRound {α : Type} (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (h : ∀ j, StepWhole (steps j)) :
    KeepsQ impl Inv (stepRound worldRoles D A noFunctionality state steps) fun r => ∀ j, StepWhole (r.2.1 j) := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  refine (keepsQ_adversary h₁ _).bind fun result _ => ?_
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
  have hseq := keepsQ_sequenceFin (fun _ s => StepWhole s) _
    fun j => keepsQ_advance h₁ h₂ (saltWhole_roundResume D result.2 steps h j)
  rw [← he] at hseq
  refine KeepsQ.bind (KeepsQ.mono ?_ fun _ h => h) fun st hst => keepsQ_pure hst
  convert hseq using 2
  funext j
  cases steps j <;> rfl

/-- The rounds on the real network keep `Inv`. -/
theorem keepsQ_executeRounds {α : Type} :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α), (∀ j, StepWhole (steps j)) →
      KeepsQ impl Inv (executeRounds worldRoles D A noFunctionality fuel state steps) fun _ => True
  | 0, state, steps, h => keepsQ_pure trivial
  | fuel + 1, state, steps, h => by
    unfold executeRounds
    split_ifs
    · exact keepsQ_pure trivial
    · exact (keepsQ_stepRound h₁ h₂ D A state steps h).bind fun st hst =>
        keepsQ_executeRounds fuel st.1 st.2.1 hst

/-- A phase on the real network whose honest programs have whole salt draws keeps `Inv`. -/
theorem keepsQ_executePhase {α : Type} (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ j, j ∉ D.1 → SaltWhole (program j).run) :
    KeepsQ impl Inv (executePhase worldRoles D A noFunctionality fuel state program) fun _ => True := by
  unfold executePhase startSteps
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs
    · simp only [advance_pure, free_pure]
    · rfl
  change KeepsQ impl Inv ((OverPermutation.sequenceFin _) >>= _) _
  rw [he]
  refine (keepsQ_sequenceFin (fun _ s => StepWhole s) _ fun j => keepsQ_advance h₁ h₂ ?_).bind fun st hst =>
    keepsQ_executeRounds h₁ h₂ D A fuel state st hst
  split_ifs with hj
  · exact SaltWhole.pure _
  · exact hp j hj

end World

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.keepsQ_executePhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.keepsQ_executePhase
