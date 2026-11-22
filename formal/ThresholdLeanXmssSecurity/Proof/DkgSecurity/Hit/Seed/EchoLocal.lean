import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoPair

/-!
# Free programs of `compWorld` on the hash cache

* `compLocal` is `compWorld` on the free copy, as a world on the hash cache alone. A free call of `H` at
  the derive input of a hidden term gives the seed of the term, and each other call is `localAnswer`.
  Each call is an atom of the lazy random oracle, so two programs commute (`commutes_compLocal`).
* `compWorld_free_run` states that a free program with no stream call runs in `compWorld` as in
  `compLocal`, with the hidden cache and the log unchanged.
* `RunEq I X Y` states that `X` and `Y` give one law of the result and the end state from each state.
  `runEq_sequenceFin_split` is the reorder of a sequence of two-part steps into the first parts of all
  steps and then the second parts, in a world where each two programs commute.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## Equal runs and the reorder -/

section Reorder

variable {σ κ : Type} {spec : OracleSpec κ} (I : QueryImpl spec (StateT σ ProbComp))

/-- `X` and `Y` give one law of the result and the end state from each state. -/
def RunEq {α : Type} (X Y : OracleComp spec α) : Prop :=
  ∀ s, (simulateQ I X).run s =ᵈ (simulateQ I Y).run s

variable {I}

theorem RunEq.refl {α : Type} (X : OracleComp spec α) : RunEq I X X := fun _ => EvalDistEq.rfl

theorem RunEq.of_eq {α : Type} {X Y : OracleComp spec α} (h : X = Y) : RunEq I X Y := h ▸ RunEq.refl X

theorem RunEq.trans {α : Type} {X Y Z : OracleComp spec α} (h : RunEq I X Y) (h' : RunEq I Y Z) : RunEq I X Z :=
  fun s => (h s).trans (h' s)

theorem RunEq.bind {α β : Type} {X Y : OracleComp spec α} {f g : α → OracleComp spec β} (h : RunEq I X Y)
    (hfg : ∀ a, RunEq I (f a) (g a)) : RunEq I (X >>= f) (Y >>= g) := fun s => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact (h s).bind fun p => hfg p.1 p.2

theorem RunEq.bind_right {α β : Type} (X : OracleComp spec α) {f g : α → OracleComp spec β}
    (hfg : ∀ a, RunEq I (f a) (g a)) : RunEq I (X >>= f) (X >>= g) :=
  (RunEq.refl X).bind hfg

/-- Two commuting programs swap. -/
theorem runEq_swap (hI : ∀ {α β : Type} (oa : OracleComp spec α) (ob : OracleComp spec β),
    Commutes (simulateQ I oa) (simulateQ I ob)) {α β γ : Type} (oa : OracleComp spec α) (ob : OracleComp spec β)
    (k : α → β → OracleComp spec γ) :
    RunEq I (oa >>= fun a => ob >>= fun b => k a b) (ob >>= fun b => oa >>= fun a => k a b) := fun s => by
  simp only [simulateQ_bind]
  exact (hI oa ob).bind (fun a b => simulateQ I (k a b)) s

/-- In a world where each two programs commute, a sequence of steps `A j` and then `B j` has the law of
the first parts `A j` of all steps and then the second parts `B j`. -/
theorem runEq_sequenceFin_split (hI : ∀ {α β : Type} (oa : OracleComp spec α) (ob : OracleComp spec β),
    Commutes (simulateQ I oa) (simulateQ I ob)) {α β : Type} :
    ∀ {n : ℕ} (A : Fin n → OracleComp spec α) (B : Fin n → α → OracleComp spec β),
    RunEq I (OverPermutation.sequenceFin fun j => A j >>= B j)
      (OverPermutation.sequenceFin A >>= fun ks => OverPermutation.sequenceFin fun j => B j (ks j))
  | 0, A, B => by
    refine RunEq.of_eq ?_
    simp only [OverPermutation.sequenceFin, pure_bind]
  | n + 1, A, B => by
    have ih := runEq_sequenceFin_split hI (fun j : Fin n => A j.succ) (fun j => B j.succ)
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    refine RunEq.bind_right _ fun k0 => ?_
    refine (RunEq.bind_right _ fun b0 => ih.bind fun rs => RunEq.refl _).trans ?_
    simp only [bind_assoc]
    refine (runEq_swap hI (B 0 k0) _ _).trans ?_
    refine RunEq.bind_right _ fun ks => ?_
    refine RunEq.bind_right _ fun b0 => RunEq.bind_right _ fun rs => RunEq.of_eq ?_
    congr 2

end Reorder

/-! ## The free copy of `compWorld` on the hash cache -/

section Local

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

/-- `compWorld` on the free copy, as a world on the hash cache. -/
def compLocal : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp) := fun t =>
  match t with
  | .inr (.inl q) =>
      match hiddenTermOf D parts q with
      | some T => pure (seed T)
      | none => localAnswer prims (.inr (.inl q))
  | t => localAnswer prims t

theorem isAtom_compLocal (t : (LocalSpec C).Domain) : IsAtom (compLocal prims D parts seed t) := by
  rcases t with n | q | x
  · exact isAtom_localAnswer prims _
  · simp only [compLocal]
    split
    · exact isAtom_pure _
    · exact isAtom_localAnswer prims _
  · exact isAtom_localAnswer prims _

theorem commutes_compLocal {α β : Type} (oa : OracleComp (LocalSpec C) α) (ob : OracleComp (LocalSpec C) β) :
    Commutes (simulateQ (compLocal prims D parts seed) oa) (simulateQ (compLocal prims D parts seed) ob) :=
  commutes_simulateQ _ (fun t t' => commutes_of_isAtom (isAtom_compLocal prims D parts seed t)
    (isAtom_compLocal prims D parts seed t')) oa ob

/-- A local call that is no stream call. -/
def NoStream : (LocalSpec C).Domain → Prop
  | .inr (.inr _) => False
  | _ => True

/-- A free program with no stream call runs in `compWorld` as in `compLocal`. -/
theorem compWorld_free_run {α : Type} (X : OracleComp (LocalSpec C) α) (hX : AllQueriesSatisfy X NoStream)
    (w : LogState C) :
    (simulateQ (compWorld prims D parts seed) (free X)).run w =
      (fun r => (r.1, ((r.2, w.1.2), w.2))) <$> (simulateQ (compLocal prims D parts seed) X).run w.1.1 := by
  induction X using OracleComp.inductionOn generalizing w with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hX
    obtain ⟨ht, hk⟩ := hX
    have hf : free (liftM (OracleSpec.query t) >>= k : OracleComp (LocalSpec C) _) =
        liftM (OracleSpec.query (spec := WorldSpec C) (.inr t)) >>= fun a => free (k a) := by
      simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      rfl
    rw [hf, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind]
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases t with n | q | x
    · simp only [compWorld, compLocal, loggedWorld, streamWorld, onHash, countedCells, StateT.run_mk,
        List.append_nil, bind_map_left]
      refine bind_congr fun r => ?_
      rw [ih r.1 (hk r.1)]
    · simp only [compWorld, compLocal]
      rcases hT : hiddenTermOf D parts q with _ | T
      · simp only [loggedWorld, streamWorld, onHash, countedCells, StateT.run_mk, List.append_nil, bind_map_left]
        refine bind_congr fun r => ?_
        rw [ih r.1 (hk r.1)]
      · simp only [StateT.run_pure, pure_bind]
        rw [ih (seed T) (hk (seed T))]
    · exact absurd ht id

end Local

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.runEq_sequenceFin_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.runEq_sequenceFin_split

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compWorld_free_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compWorld_free_run
