import ThresholdLeanXmss.Statement.DkgGame

/-!
# The vote after a setup ceremony

The facts on `broadcast`, `decision`, `committed` and `split` of `Statement/DkgGame.lean` that the
proofs of the three claims of the setup share.

* `split_committed` states the unanimous delivery. The outputs after the vote have no split, for
  each round of the adversary.
* `committed_eq_some` states that the vote only removes outputs.
* `keep_none` states that an operator that keeps nothing has its old state.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.Vote

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E α : Type}

@[simp] theorem committed_true (outputs : C.Party → Option α) : committed true outputs = outputs := rfl

@[simp] theorem committed_false (outputs : C.Party → Option α) : committed false outputs = fun _ => none := rfl

/-- An output after the vote is an output before the vote. -/
theorem committed_eq_some {ok : Bool} {outputs : C.Party → Option α} {i : C.Party} {a : α}
    (h : committed ok outputs i = some a) : outputs i = some a := by
  cases ok <;> simp_all [committed]

/-- A yes of the vote means that no honest operator sent `abort`. -/
theorem ne_abort_of_decision {D : C.Coalition} {honest : C.Party → Msg E}
    {sent : C.Party → C.Party → Option (Msg E)} (h : decision (broadcast D honest sent) = true) {i : C.Party}
    (hi : i ∉ D.1) : honest i ≠ Msg.abort := by
  simp only [decision, decide_eq_true_eq] at h
  obtain ⟨v, hv, hall⟩ := h
  have hi' := hall i
  simp only [broadcast, hi, ite_false, Option.some.injEq] at hi'
  exact hi' ▸ hv

/-- Unanimous delivery. When each honest operator with no output sends `abort`, the outputs after the
vote have no split, for each round `sent` of the adversary. -/
theorem split_committed (D : C.Coalition) (honest : C.Party → Msg E) (sent : C.Party → C.Party → Option (Msg E))
    (outputs : C.Party → Option α) (habort : ∀ i, i ∉ D.1 → outputs i = none → honest i = Msg.abort) :
    split D (committed (decision (broadcast D honest sent)) outputs) = false := by
  simp only [split, decide_eq_false_iff_not]
  rintro ⟨i, j, -, hj, hsome, hnone⟩
  cases hok : decision (broadcast D honest sent) with
  | false => simp [committed, hok] at hsome
  | true =>
    have hne := ne_abort_of_decision hok hj
    simp only [committed, hok, ite_true, Option.isNone_iff_eq_none] at hnone
    exact hne (habort j hj hnone)

/-- An operator that keeps nothing has its old state. -/
theorem keep_none (operator : OperatorState C) (tree : Tree) : operator.keep none tree = operator := by
  cases tree <;> simp [OperatorState.keep, TreeOutput.topTree, bottomOf]

end ThresholdLeanXmssSecurity.Vote
