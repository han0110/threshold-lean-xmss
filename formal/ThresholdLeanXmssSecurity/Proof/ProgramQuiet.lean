import ThresholdLeanXmssSecurity.Proof.Execution

/-!
# Computations with no programming query

`Programming` is the programming branch of the world interface. A computation is quiet when it makes
no programming query. `free_quiet` and `counted_quiet` state that the free copy and the counted copy
of a local computation are quiet.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.ProgramQuiet

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The programming branch of the world interface. -/
def Programming : (WorldSpec C).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

theorem qb0_simulateQ {ι κ α : Type} {spec : OracleSpec ι} {spec' : OracleSpec κ}
    {p : κ → Prop} [DecidablePred p] (impl : QueryImpl spec (OracleComp spec'))
    (h : ∀ t, IsQueryBoundP (impl t) p 0) (oa : OracleComp spec α) :
    IsQueryBoundP (simulateQ impl oa) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    simpa using isQueryBoundP_bind (m := 0) (h t) fun a _ => ih a

theorem qb0_bind' {ι α β : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {f : α → OracleComp spec β} (h : IsQueryBoundP oa p 0)
    (hf : ∀ a, IsQueryBoundP (f a) p 0) : IsQueryBoundP (oa >>= f) p 0 := by
  simpa using isQueryBoundP_bind (m := 0) h fun a _ => hf a

theorem free_quiet {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (free oa) Programming 0 := by
  apply qb0_simulateQ
  intro t
  apply (isQueryBoundP_query_iff _ _ _).2
  intro h
  exact absurd h (by simp [Programming])

theorem counted_quiet {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) Programming 0 := by
  change IsQueryBoundP (counted (liftComp oa _)) Programming 0
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftComp_bind, counted_bind]
    have e : counted (liftComp (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _)
        (SimulatorSpec C)) =
        (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
      rcases t with t | (q | x) <;> rfl
    rw [e]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [Programming]), fun u => by simpa [Programming] using ih u⟩

/-- info: 'ThresholdLeanXmssSecurity.ProgramQuiet.free_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms free_quiet

/-- info: 'ThresholdLeanXmssSecurity.ProgramQuiet.counted_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counted_quiet

end ThresholdLeanXmssSecurity.ProgramQuiet
