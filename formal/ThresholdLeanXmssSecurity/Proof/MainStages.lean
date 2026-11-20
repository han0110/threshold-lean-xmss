import ThresholdLeanXmssSecurity.Proof.Main

/-!
# The rounds of a batch that end

`liftComp_mapM_local` moves `liftComp` through `List.mapM`, and `main_honest_exists` gives an honest
operator. A run of rounds in which every honest step is done stays as it is
(`stages_executeRounds_done`, `executeRounds_allDone`), and a run in which the honest operators abort
ends with their abort (`stages_executeRounds_abort`).
-/

noncomputable section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem liftComp_mapM_local {α β : Type} (f : α → OracleComp (RoSpec C) β) :
    ∀ L : List α, liftComp (L.mapM f) (LocalSpec C) = L.mapM fun a => liftComp (f a) (LocalSpec C)
  | [] => by simp
  | a :: L => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure]
    refine bind_congr fun b => ?_
    rw [← liftComp_mapM_local f L]

theorem main_honest_exists (D : C.Coalition) : ∃ i : C.Party, i ∉ D.1 := by
  obtain ⟨T, -⟩ := main_lacked_exists D
  obtain ⟨i, -, hi⟩ := main_exists_honest_holder D T
  exact ⟨i, hi⟩

end ThresholdLeanXmssSecurity

end

noncomputable section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem stages_sequenceFin_eq_pure {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type} {n : ℕ}
    (f : Fin n → m β) (g : Fin n → β) (h : ∀ i, f i = pure (g i)) : OverPermutation.sequenceFin f = pure g := by
  rw [show f = fun i => pure (g i) from funext h]
  exact sequenceFin_pure g

section Abort

variable {E' Ia I O L R α : Type} (D : C.Coalition) (A : Adversary C E' Ia L R) (F : Functionality C I O L R)

theorem stages_executeRounds_done (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E' (CallSpec I O) α)
    (h : ∀ i, steps i = .done none) :
    executeRounds localRoles D A F fuel st steps = pure (st, fun _ => none) := by
  cases fuel with
  | zero => simp [executeRounds, h, Step.output]
  | succ fuel =>
    rw [executeRounds, if_pos (fun i _ => by simp [h, Step.isDone])]
    simp [h, Step.output]

/-- Rounds from steps that are all done return their outputs, for each pair of roles. -/
theorem executeRounds_allDone {m : Type → Type} [Monad m] (Ro : Roles C m) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E' (CallSpec I O) α) (h : ∀ i, (steps i).isDone) :
    executeRounds Ro D A F fuel st steps = pure (st, fun i => (steps i).output) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [executeRounds, if_pos (fun i _ => h i)]

theorem stages_executeRounds_allDone (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E' (CallSpec I O) α)
    (h : ∀ i, (steps i).isDone) :
    executeRounds localRoles D A F fuel st steps = pure (st, fun i => (steps i).output) :=
  executeRounds_allDone D A F localRoles fuel st steps h

/-- A partial abort: some honest operator aborted, and the others call. Then everyone aborts. -/
theorem stages_executeRounds_abort (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E' (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none)
    (h : ∀ i ∉ D.1, steps i = .done none ∨
      ∃ input resume, steps i = .call input resume ∧ advance (resume none) = pure (.done none))
    (hab : ∃ i ∉ D.1, steps i = .done none) :
    executeRounds localRoles D A F fuel st steps = pure (st, fun _ => none) := by
  cases fuel with
  | zero =>
    simp only [executeRounds]
    congr 2
    funext i
    by_cases hi : i ∈ D.1
    · simp [hD i hi, Step.output]
    · rcases h i hi with h' | ⟨input, resume, h', -⟩ <;> simp [h', Step.output]
  | succ fuel =>
    rw [executeRounds]
    split_ifs with hdone
    · congr 2
      funext i
      by_cases hi : i ∈ D.1
      · simp [hD i hi, Step.output]
      · rcases h i hi with h' | ⟨input, resume, h', -⟩
        · simp [h', Step.output]
        · have := hdone i hi
          rw [h'] at this
          exact this.elim
    · have hstep : stepRound localRoles D A F st steps = pure (st, fun _ => .done none, fun _ _ => none) := by
        unfold stepRound
        obtain ⟨i₀, hi₀, hdone₀⟩ := hab
        have hcall : ∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome := by
          by_contra hc
          push Not at hc
          apply hdone
          intro i hi
          rcases h i hi with h' | ⟨input, resume, h', -⟩
          · simp [h', Step.isDone]
          · have := hc i hi
            simp [h', Step.callInput] at this
        rw [if_pos ⟨hcall, fun i hi => by
          rcases h i hi with h' | ⟨input, resume, h', -⟩
          · simp [h', Step.isDone]
          · simp [h', Step.callInput]⟩]
        unfold runFunctionality
        rw [if_pos (fun hall => by simpa [hi₀, hdone₀, Step.callInput] using hall i₀ hi₀)]
        simp only [pure_bind]
        rw [stages_sequenceFin_eq_pure _ (fun _ => Step.done none) (fun j => ?_), pure_bind]
        by_cases hj : j ∈ D.1
        · simp [hD j hj]
        · rcases h j hj with h' | ⟨input, resume, h', hres⟩
          · simp [h']
          · simp [h', hj, localRoles, hres]
      rw [hstep, pure_bind]
      exact stages_executeRounds_done D A F fuel st _ fun _ => rfl

end Abort

end ThresholdLeanXmssSecurity

end
