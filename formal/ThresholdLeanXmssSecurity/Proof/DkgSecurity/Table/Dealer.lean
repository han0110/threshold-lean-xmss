import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Steps
import ThresholdLeanXmssSecurity.Proof.PhaseSplit

/-!
# The dealer commutes with the world

The computations of the dealer make only `WorldSafe` queries, the queries of `H` outside the setup
domains and the sampling. In `streamWorld` such a query commutes with each query that is no
programming query of a cell outside the setup domains (`commutes_worldSafe`). So a computation of the
dealer commutes with each such computation (`commutes_simulateQ_PQ`), as lazy sampling.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Two simulations commute when each call of the first satisfies `P`, each call of the second
satisfies `P'`, and two such calls commute. -/
theorem commutes_simulateQ_PQ {κ σ : Type} {spec : OracleSpec κ} (I : QueryImpl spec (StateT σ ProbComp))
    (P P' : κ → Prop) (hI : ∀ t t', P t → P' t' → Commutes (I t) (I t')) {α β : Type} (oa : OracleComp spec α)
    (hoa : AllQueriesSatisfy oa P) (ob : OracleComp spec β) (hob : AllQueriesSatisfy ob P') :
    Commutes (simulateQ I oa) (simulateQ I ob) := by
  have hquery : ∀ t, P t → ∀ {β : Type} (ob : OracleComp spec β), AllQueriesSatisfy ob P' →
      Commutes (I t) (simulateQ I ob) := by
    intro t ht β ob hob
    induction ob using OracleComp.inductionOn with
    | pure b => rw [simulateQ_pure]; exact commutes_pure (I t) b
    | query_bind t' k ih =>
        rw [allQueriesSatisfy_query_bind_iff] at hob
        rw [simulateQ_bind, simulateQ_query]
        exact ((hI t t' ht hob.1).map_right _).bind_right fun u => ih u (hob.2 u)
  induction oa using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact (commutes_pure (simulateQ I ob) a).symm
  | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      rw [simulateQ_bind, simulateQ_query]
      exact ((hquery t hoa.1 ob hob).map_left _).bind_left fun u => ih u (hoa.2 u)

/-- A sampling that ignores the state commutes with each step. -/
theorem commutes_lift_any {σ α β : Type} (p : ProbComp α) (y : StateT σ ProbComp β) :
    Commutes (StateT.lift p : StateT σ ProbComp α) y := fun s => by
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- A query of `H` and a programming query of another cell commute. -/
theorem commutes_hash_program (prims : Primitives) {q q' : Query C} (hne : q ≠ q') (value : HashOutput) :
    Commutes (hashAnswer prims q) (programAnswer (C := C) (q', value)) := fun s => by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm]
    exact (commutes_pure _ _).symm s
  · rw [hashAnswer_of_not_isFixed prims hq]
    simp only [randomOracle.apply_eq, programAnswer, StateT.run_bind, StateT.run_get, pure_bind,
      bind_assoc]
    by_cases hp : (∃ input, q' = .hash input ∧ MpcInput input) ∨ (s q').isSome
    · rcases hs : s q with _ | u
      · simp [hp, hs, StateT.run_bind, StateT.run_modifyGet, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)]
      · simp [hp, hs]
    · rcases hs : s q with _ | u
      · simp [hp, hs, StateT.run_bind, StateT.run_modifyGet, StateT.run_set,
          QueryCache.cacheQuery_of_ne _ _ hne, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)]
        simp only [QueryCache.cacheQuery_comm s hne, EvalDistEq.refl]
      · simp [hp, hs, StateT.run_set, QueryCache.cacheQuery_of_ne _ _ hne]

/-- A query that is no programming query of a cell outside the setup domains. -/
def NoOuterProgram : (WorldSpec C).Domain → Prop
  | .inl (.inr x) => isSetupQuery x.1 = true
  | _ => True

/-- A local query outside the setup domains commutes in `streamWorld` with each query that is no
programming query of a cell outside the setup domains. -/
theorem commutes_localSafe (prims : Primitives) (D : C.Coalition) {t : (LocalSpec C).Domain}
    (ht : ¬ SetupOnly t) {t' : (WorldSpec C).Domain} (ht' : NoOuterProgram t') :
    Commutes (onHash (localAnswer prims t)) (streamWorld prims D t') := by
  have hatom : StreamAtom (onHash (localAnswer prims t)) := Or.inl ⟨_, isAtom_localAnswer prims t, rfl⟩
  rcases t' with (t' | x) | t'
  · exact commutes_of_streamAtom hatom (Or.inl ⟨_, isAtom_localAnswer prims t', rfl⟩)
  · obtain ⟨q', value⟩ := x
    change Commutes _ (onHash (programAnswer (q', value)))
    refine commutes_onHash ?_
    rcases t with n | q | y
    · exact commutes_lift_any _ _
    · have hq : isSetupQuery q = false := by simpa [SetupOnly, isSetupRo] using ht
      have hne : q ≠ q' := fun e => by
        have h' : isSetupQuery q' = true := ht'
        rw [← e, hq] at h'
        exact absurd h' (by simp)
      exact commutes_hash_program prims hne value
    · exact (ht (by simp [SetupOnly, isSetupRo])).elim
  · exact commutes_of_streamAtom hatom (streamAtom_free prims D t')

/-- A `WorldSafe` query commutes in `streamWorld` with each query that is no programming query of a
cell outside the setup domains. -/
theorem commutes_worldSafe (prims : Primitives) (D : C.Coalition) {t t' : (WorldSpec C).Domain}
    (ht : WorldSafe t) (ht' : NoOuterProgram t') :
    Commutes (streamWorld prims D t) (streamWorld prims D t') := by
  rcases t with (t | x) | t
  · exact commutes_localSafe prims D ht ht'
  · exact ht.elim
  · rw [streamWorld_safeQuery (.inr t) ht]
    exact commutes_localSafe prims D ht ht'

/-- Lazy sampling with programming. A computation with only `WorldSafe` queries commutes in
`streamWorld` with a computation that programs no cell outside the setup domains. -/
theorem worldRun_safe_swap (prims : Primitives) (D : C.Coalition) {α β γ : Type} {x : OracleComp (WorldSpec C) α}
    (hx : AllQueriesSatisfy x WorldSafe) {y : OracleComp (WorldSpec C) β} (hy : AllQueriesSatisfy y NoOuterProgram)
    (k : α → β → OracleComp (WorldSpec C) γ) :
    WorldRun (streamWorld prims D) (do let a ← x; let b ← y; k a b) (do let b ← y; let a ← x; k a b) := by
  intro s
  simp only [simulateQ_bind]
  exact (commutes_simulateQ_PQ (streamWorld prims D) WorldSafe NoOuterProgram
    (fun _ _ ht ht' => commutes_worldSafe prims D ht ht') x hx y hy).bind _ s

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.worldRun_safe_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.worldRun_safe_swap
