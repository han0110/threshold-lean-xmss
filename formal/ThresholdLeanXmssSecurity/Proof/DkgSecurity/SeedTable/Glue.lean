import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Budget
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Represent

/-!
# The three shared hops of the seed table from the general statements

`sharedSeedReal_of_general` and `sharedSeedIdeal_of_general` derive `SharedSeedReal` and
`SharedSeedIdeal` from the general statements `SeedRealGeneral` and `SeedIdealGeneral` and from named
facts on the inside of the shared rest. `sharedSeedBound_of_rest` derives `SharedSeedBound` from the
representation on the private table and the cost of the program of the shared rest.
`sharedRestTable` and `sharedRestLogged` prove two of the named facts from the representation of the
shared rest.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open PFunctor.FreeM (cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The shared forms -/

/-- `loggedWorld` with the log dropped is `streamWorld`. -/
theorem loggedWorld_drop (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) (w : StreamState C)
    (log : List (Query C)) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (loggedWorld prims D) oa).run (w, log) =
      (simulateQ (streamWorld prims D) oa).run w := by
  induction oa using OracleComp.inductionOn generalizing w log with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    simp only [loggedWorld, StateT.run_mk, bind_map_left]
    exact bind_congr fun z => ih z.1 z.2 _

/-- The program of the shared rest makes no programming query. -/
def SharedProgramNoProgram : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State) (keys : C.Party → Option (Keys C)),
    AllQueriesSatisfy (sharedProgram K circuits settings runLimit D A state keys) fun t => ¬ PeekProgramQuery t

/-- The shared rest on the private table is its program with reads of the blind view. -/
def SharedRestTable : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State) (keys : C.Party → Option (Keys C))
    (table : HashCache C),
    (sharedRestOf K circuits settings runLimit (tableWorld prims D) id false D A state keys).run' (table, ∅) =
      (simulateQ (withPeek (tableWorld prims D) id) (sharedProgram K circuits settings runLimit D A state keys)).run'
        (table, ∅)

/-- The shared rest in `loggedWorld` has the law of its program with reads of the blind view in
`streamWorld`. -/
def SharedRestLogged : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State) (keys : C.Party → Option (Keys C))
    (w : StreamState C) (log : List (Query C)),
    (sharedRestOf K circuits settings runLimit (loggedWorld prims D) Prod.fst false D A state keys).run' (w, log) =ᵈ
      (simulateQ (withPeek (streamWorld prims D) id) (sharedProgram K circuits settings runLimit D A state keys)).run' w

omit [Fintype E] [DecidableEq E] in
/-- The proof of `SharedRestTable`, from the representation of the shared rest. -/
theorem sharedRestTable : SharedRestTable prims K circuits settings runLimit := fun D A state keys table =>
  sharedRestOf_eq_program K circuits settings runLimit (tableWorld prims D) id D A state keys (table, ∅)

omit [Fintype E] [DecidableEq E] in
/-- The proof of `SharedRestLogged`, from the representation of the shared rest and the erasure of the
log. -/
theorem sharedRestLogged : SharedRestLogged prims K circuits settings runLimit := fun D A state keys w log => by
  rw [sharedRestOf_logged]

theorem clean_iff (r : Bool × Bool) : Clean r ↔ (r.1 && !r.2) = true := by
  rcases r with ⟨_ | _, _ | _⟩ <;> simp [Clean]

omit [Fintype E] [DecidableEq E] in
theorem sharedSeedReal_of_general (general : SeedRealGeneral (C := C) (E := E) prims)
    (noProgram : SharedProgramNoProgram K circuits settings runLimit)
    (table : SharedRestTable prims K circuits settings runLimit)
    (logged : SharedRestLogged prims K circuits settings runLimit) :
    SharedSeedReal prims K circuits settings runLimit := by
  intro D A
  have h := general D A.net Bool
    (fun s k => (fun x => x.1 && !x.2) <$> sharedProgram K circuits settings runLimit D A s k)
    (fun s k => allQueries_map _ (noProgram D A s k))
  rw [accepts_eq_probOutput]
  unfold distinguish tableRestShared realProb sharedReal
  have ht : ∀ r : (tableNet prims A.net).State × (C.Party → Option (Keys C)),
      (sharedRestOf K circuits settings runLimit (tableWorld prims D) id false D A r.1.1 r.2).run' (r.1.2, ∅) =
        (simulateQ (withPeek (tableWorld prims D) id) (sharedProgram K circuits settings runLimit D A r.1.1 r.2)).run'
          (r.1.2, ∅) := fun r => table D A r.1.1 r.2 r.1.2
  have hp : ∀ (P : OracleComp (PeekSpec C) (Bool × Bool)) (w : StreamState C),
      (fun x => x.1 && !x.2) <$> (simulateQ (withPeek (tableWorld prims D) id) P).run' w =
        (simulateQ (withPeek (tableWorld prims D) id) ((fun x => x.1 && !x.2) <$> P)).run' w := fun P w => by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp only [ht, hp]
  rw [h.prEvent_eq]
  congr 1
  rw [← loggedWorld_drop prims D _ (∅, ∅) [], bind_map_left, StateT.run_bind]
  refine prEvent_bind_congr_support _ _ _ _ _ fun z hz => ?_
  have e := (logged D A z.1.1 z.1.2 z.2.1 z.2.2).prEvent_eq Clean
  simp only [StateT.run'_eq, Functor.map_map, simulateQ_map, StateT.run_map, clean_iff] at e ⊢
  exact e.symm

/-- On each result of `worldSeedGen` in `loggedWorld`, the shared rest with the keys of the dealer of
each emulated operator with keys and the shared rest with the data of the dealer give "win and no
flag" with one probability. -/
def SharedDealtAgree : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) (worldSeedGen D A.net)).run ((∅, ∅), [])),
      Pr{let r ← (sharedRestOf K circuits settings runLimit (loggedWorld prims D) Prod.fst false D A z.1.1
          fun i => (z.1.2.2.2.2 i).map fun _ => z.1.2.2.2.1 i).run' z.2}[Clean r] =
        Pr{let r ← (sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A
          z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2
            (startState D z.1.1 fun i => (z.1.2.2.2.2 i).map fun _ => z.1.2.2.2.1 i)).run' z.2}[Clean r]

omit [Fintype E] [DecidableEq E] in
theorem sharedSeedIdeal_of_general (general : SeedIdealGeneral (C := C) (E := E) prims)
    (noProgram : SharedProgramNoProgram K circuits settings runLimit)
    (table : SharedRestTable prims K circuits settings runLimit)
    (logged : SharedRestLogged prims K circuits settings runLimit)
    (agree : SharedDealtAgree prims K circuits settings runLimit) :
    SharedSeedIdeal prims K circuits settings runLimit := by
  intro D A
  have h := general D A.net Bool
    (fun s k => (fun x => x.1 && !x.2) <$> sharedProgram K circuits settings runLimit D A s k)
    (fun s k => allQueries_map _ (noProgram D A s k))
  rw [accepts_eq_probOutput]
  unfold distinguish tableRestShared dealtProb sharedDealt
  have ht : ∀ r : (tableNet prims A.net).State × (C.Party → Option (Keys C)),
      (sharedRestOf K circuits settings runLimit (tableWorld prims D) id false D A r.1.1 r.2).run' (r.1.2, ∅) =
        (simulateQ (withPeek (tableWorld prims D) id) (sharedProgram K circuits settings runLimit D A r.1.1 r.2)).run'
          (r.1.2, ∅) := fun r => table D A r.1.1 r.2 r.1.2
  have hp : ∀ (P : OracleComp (PeekSpec C) (Bool × Bool)) (w : StreamState C),
      (fun x => x.1 && !x.2) <$> (simulateQ (withPeek (tableWorld prims D) id) P).run' w =
        (simulateQ (withPeek (tableWorld prims D) id) ((fun x => x.1 && !x.2) <$> P)).run' w := fun P w => by
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp only [ht, hp]
  rw [h.prEvent_eq]
  congr 1
  rw [← loggedWorld_drop prims D _ (∅, ∅) [], bind_map_left, StateT.run_bind]
  refine prEvent_bind_congr_support _ _ _ _ _ fun z hz => ?_
  have e := (logged D A z.1.1 (fun i => (z.1.2.2.2.2 i).map fun _ => z.1.2.2.2.1 i) z.2.1 z.2.2).prEvent_eq Clean
  have e' := agree D A z hz
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map, simulateQ_map, StateT.run_map, clean_iff] at e e' ⊢
  rw [← e, e']


/-! ## The hops from the proved general statements -/

omit [Fintype E] [DecidableEq E] in
theorem sharedSeedReal_of_rest (noProgram : SharedProgramNoProgram K circuits settings runLimit)
    (table : SharedRestTable prims K circuits settings runLimit)
    (logged : SharedRestLogged prims K circuits settings runLimit) :
    SharedSeedReal prims K circuits settings runLimit :=
  sharedSeedReal_of_general prims K circuits settings runLimit (seedRealGeneral prims) noProgram table logged

omit [Fintype E] [DecidableEq E] in
theorem sharedSeedIdeal_of_rest (noProgram : SharedProgramNoProgram K circuits settings runLimit)
    (table : SharedRestTable prims K circuits settings runLimit)
    (logged : SharedRestLogged prims K circuits settings runLimit)
    (agree : SharedDealtAgree prims K circuits settings runLimit) :
    SharedSeedIdeal prims K circuits settings runLimit :=
  sharedSeedIdeal_of_general prims K circuits settings runLimit (seedIdealGeneral prims) noProgram table logged agree

/-! ## The budget -/

/-- The calls of the class of the seed generation in the shared rest are the calls of the rounds of
`A.net` after the seed generation and the calls of `A.forge`. -/
def SharedProgramClassBound : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ),
    (∀ state sent, QueryCostAtMost (A.net.round state sent) ownCost step) →
    (∀ pk top, QueryCostAtMost (A.forge pk top) forgeCost forge) →
    ∀ (state : A.net.State) (keys : C.Party → Option (Keys C)),
      cost classCharge (sharedProgram K circuits settings runLimit D A state keys) ≤
        (((dkgTsigRounds circuits settings runLimit - setupRounds) * step + forge : ℕ) : ℕ∞)

theorem budget_arith (start step forge q : ℕ)
    (hq : start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q) :
    start + setupRounds * step + ((dkgTsigRounds circuits settings runLimit - setupRounds) * step + forge) ≤ q := by
  obtain ⟨m, hm⟩ : ∃ m, dkgTsigRounds circuits settings runLimit = setupRounds + m := ⟨_, rfl⟩
  rw [hm] at hq ⊢
  have e : setupRounds + m - setupRounds = m := by omega
  rw [e]
  have := add_mul setupRounds m step
  omega

omit [Fintype E] [DecidableEq E] in
theorem sharedSeedBound_of_rest (table : SharedRestTable prims K circuits settings runLimit)
    (classBound : SharedProgramClassBound K circuits settings runLimit) :
    SharedSeedBound prims K circuits settings runLimit := by
  intro D A q hA
  obtain ⟨start, step, forge, hq, hs, hr, hf⟩ := hA
  refine isQueryBounded_table prims A.net _ start step
    ((dkgTsigRounds circuits settings runLimit - setupRounds) * step + forge) q
    (budget_arith circuits settings runLimit start step forge q hq) hs hr fun r => ?_
  unfold tableRestShared
  rw [table D A r.1.1 r.2 r.1.2]
  refine isQueryBoundP_of_cost (cost_map_le _ ?_)
  rw [StateT.run'_eq]
  exact cost_map_le _ ((cost_tableWorld prims D _ _).trans (classBound D A step forge hr hf r.1.1 r.2))

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedBound_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedBound_of_rest

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedIdeal_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedIdeal_of_rest

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedReal_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSeedReal_of_rest
