import ThresholdLeanXmssSecurity.Proof.PhaseSplit

/-!
# Phases with more fuel and with mapped outputs

`executePhase_extra` states that a phase of timed honest programs with more fuel than their rounds
has the law of the phase with exactly their rounds. `executePhase_map` states that a phase of
programs with mapped outputs is the phase of the programs with its outputs mapped.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace WorldSplit

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## More fuel than the rounds -/

section Extra

variable {C : Committee} {E : Type} {I O L R Ia α : Type} {σ : Type}
  {impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)}
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

theorem executeRounds_of_allDone (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (h : ∀ i, i ∉ D.1 → (steps i).isDone) :
    executeRounds worldRoles D A F fuel st steps = pure (st, fun i => (steps i).output) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [executeRounds, ite_eq_left h]

/-- Rounds of timed honest steps with more fuel than their rounds have the law of the rounds with
exactly their rounds. -/
theorem executeRounds_extra (m : ℕ) : ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimed n (steps i)) →
    WorldRun impl (executeRounds worldRoles D A F (n + m) st steps) (executeRounds worldRoles D A F n st steps)
  | 0, st, steps, _, ht => by
    rw [Nat.zero_add, executeRounds_of_allDone D A F m st steps fun i hi => (ht i hi).isDone,
      executeRounds_of_allDone D A F 0 st steps fun i hi => (ht i hi).isDone]
    exact WorldRun.refl impl _
  | n + 1, st, steps, hD, ht => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    unfold executeRounds
    split_ifs
    · exact WorldRun.refl impl _
    · refine WorldRun.bind_support impl _ fun r hr => ?_
      obtain ⟨hD', ht'⟩ := stepRound_timed_world D A F n st steps hD ht r hr
      exact executeRounds_extra m n r.1 r.2.1 hD' ht'

/-- A phase of timed honest programs with more fuel than their rounds has the law of the phase with
exactly their rounds. -/
theorem executePhase_extra (n m : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α)
    (hp : ∀ i ∉ D.1, Timed n (p i).run) :
    WorldRun impl (executePhase worldRoles D A F (n + m) st p) (executePhase worldRoles D A F n st p) := by
  unfold executePhase
  refine WorldRun.bind_support impl _ fun s0 hs0 => ?_
  obtain ⟨hD, ht⟩ := startSteps_timed_world D n p hp s0 hs0
  exact executeRounds_extra D A F m n st s0 hD ht

end Extra

/-! ## Mapped outputs -/

section Map

variable {C : Committee} {E : Type} {Ia L R O α β : Type}

/-- A step with its output mapped by `f`. -/
def stepMapOut (f : α → β) : Step C E (CallSpec PEmpty O) α → Step C E (CallSpec PEmpty O) β
  | .done out => .done (out.map f)
  | .wait outbox resume => .wait outbox fun inbox => Option.map f <$> resume inbox
  | .call input resume => .call input fun r => Option.map f <$> resume r

theorem advance_mapOut (f : α → β) (oa : OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α)) :
    advance (Option.map f <$> oa) = stepMapOut f <$> advance oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [map_pure, advance_pure, advance_pure, map_pure]
    rfl
  | query_bind t k ih =>
    rcases t with (q | outbox) | input
    · rw [map_bind]
      change (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (Option.map f <$> k r)) =
        stepMapOut f <$> (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r))
      rw [map_bind]
      exact bind_congr ih
    · rw [map_bind]
      change pure (Step.wait outbox fun inbox => Option.map f <$> k inbox) = stepMapOut f <$> pure (Step.wait outbox k)
      rw [map_pure]
      rfl
    · exact input.elim

theorem stepMapOut_outbox (f : α → β) (s : Step C E (CallSpec PEmpty O) α) : (stepMapOut f s).outbox = s.outbox := by
  cases s <;> rfl

theorem stepMapOut_delivered (f : α → β) (s : Step C E (CallSpec PEmpty O) α) :
    (stepMapOut f s).delivered = s.delivered := by
  rcases s with (_ | _) | _ | _ <;> rfl

theorem stepMapOut_isDone (f : α → β) (s : Step C E (CallSpec PEmpty O) α) : (stepMapOut f s).isDone ↔ s.isDone := by
  cases s <;> exact Iff.rfl

theorem stepMapOut_output (f : α → β) (s : Step C E (CallSpec PEmpty O) α) :
    (stepMapOut f s).output = s.output.map f := by
  cases s <;> rfl

theorem step_noCall {γ : Type} (D : C.Coalition) (steps : C.Party → Step C E (CallSpec PEmpty O) γ) :
    ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
  rintro ⟨⟨i, -, hi⟩, -⟩
  cases hs : steps i with
  | done out => rw [hs] at hi; exact absurd hi (by simp [Step.callInput])
  | wait outbox resume => rw [hs] at hi; exact absurd hi (by simp [Step.callInput])
  | call input resume => exact input.elim

theorem sequenceFin_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ ε : Type} {n : ℕ}
    {X : Fin n → m γ} {Y : Fin n → m δ} {g : Fin n → γ → δ} (h : ∀ j, Y j = X j >>= fun s => pure (g j s))
    (k : (Fin n → δ) → m ε) :
    (OverPermutation.sequenceFin Y >>= k) = OverPermutation.sequenceFin X >>= fun xs => k fun i => g i (xs i) := by
  rw [funext h, sequenceFin_bind_pure, bind_assoc]
  simp only [pure_bind]

variable (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R)

theorem stepRound_mapOut (f : C.Party → α → β) (st : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α) :
    stepRound worldRoles D A F st (fun i => stepMapOut (f i) (steps i)) =
      (fun r => (r.1, (fun i => stepMapOut (f i) (r.2.1 i)), r.2.2)) <$> stepRound worldRoles D A F st steps := by
  unfold stepRound
  rw [ite_eq_right (step_noCall D _), ite_eq_right (step_noCall D steps)]
  simp only [stepMapOut_outbox, stepMapOut_delivered, map_bind, map_pure]
  refine bind_congr fun r => ?_
  refine (sequenceFin_map_eq (g := fun j s => stepMapOut (f j) s) (fun j => ?_)
    (fun steps' => pure (r.1, steps', r.2))).trans rfl
  cases hs : steps j with
  | done out => simp only [stepMapOut, pure_bind]
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp only [stepMapOut, hj, ↓reduceIte, pure_bind]
      rfl
    · simp only [stepMapOut, hj, ↓reduceIte]
      rw [advance_mapOut, worldRoles_honest_map, map_eq_bind_pure_comp]
      rfl
  | call input resume => exact input.elim

theorem executeRounds_mapOut (f : C.Party → α → β) : ∀ (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec PEmpty O) α),
    executeRounds worldRoles D A F fuel st (fun i => stepMapOut (f i) (steps i)) =
      (fun r => (r.1, fun i => (r.2 i).map (f i))) <$> executeRounds worldRoles D A F fuel st steps
  | 0, st, steps => by simp [executeRounds, stepMapOut_output]
  | fuel + 1, st, steps => by
    unfold executeRounds
    simp only [stepMapOut_isDone]
    split_ifs
    · simp [stepMapOut_output]
    · rw [stepRound_mapOut, map_bind, bind_map_left]
      exact bind_congr fun r => executeRounds_mapOut f fuel r.1 r.2.1

theorem startSteps_mapOut (f : C.Party → α → β) (p : C.Party → PartyM C E (CallSpec PEmpty O) α) :
    startSteps worldRoles D (fun i => f i <$> p i) =
      (fun s i => stepMapOut (f i) (s i)) <$> startSteps worldRoles D p := by
  unfold startSteps
  rw [← bind_pure (OverPermutation.sequenceFin _), map_eq_bind_pure_comp]
  refine (sequenceFin_map_eq (g := fun j s => stepMapOut (f j) s) (fun j => ?_) pure).trans rfl
  by_cases hj : j ∈ D.1
  · simp only [hj, ↓reduceIte, pure_bind]
    rfl
  · simp only [hj, ↓reduceIte]
    rw [OptionT.run_map, advance_mapOut, worldRoles_honest_map, map_eq_bind_pure_comp]
    rfl

/-- A phase of programs with mapped outputs is the phase with its outputs mapped. -/
theorem executePhase_map (f : C.Party → α → β) (fuel : ℕ) (st : A.State)
    (p : C.Party → PartyM C E (CallSpec PEmpty O) α) :
    executePhase worldRoles D A F fuel st (fun i => f i <$> p i) =
      (fun r => (r.1, fun i => (r.2 i).map (f i))) <$> executePhase worldRoles D A F fuel st p := by
  unfold executePhase
  rw [startSteps_mapOut, bind_map_left, map_bind]
  exact bind_congr fun s => executeRounds_mapOut D A F f fuel st s

end Map

end WorldSplit

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.executePhase_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.executePhase_map

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.executePhase_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.executePhase_extra
