import ThresholdLeanXmssSecurity.Proof.PrssRealRand.Streams
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.Coupling
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.View

/-!
# One PRSS setup and the streams of its keys, the proof

`prssRealRandSecurity` proves `PrssRealRandSecurityStatement` with the simulator
`prssRealRandSimulator` and the overhead `0`.

1. `prssRealRand_queryBound` counts the calls of the ideal run. `A.start`, the rounds of `A` in the
   emulated setup and `Z` run on the counted copy. The honest operators and the known streams run on
   the free copy.
2. `prssRealRand_key` bounds the stream-key event of `keyWorld_coupling` on the real run, from
   `prssRealRand_coupling` and `prssRealRand_view`.
3. `prssRealRand_streamHop` bounds the distance of the real run with random hidden streams and the
   ideal run by the event that the keys of the setup do not agree.

`abs_sub_le_of_hops` joins the two hops at the PRF reduction `prgReduction`. The PRF step follows
the PRSS of CDI05, Section 4.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Bound

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A simulation whose every answer costs nothing costs nothing. -/
theorem costLe_simulateQ_zero {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ t st, CostLe prims ((impl t).run st) 0) (oa : OracleComp spec α) :
    ∀ st, CostLe prims ((simulateQ impl oa).run st) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st; exact CostLe.pure prims _
  | query_bind t k ih =>
    intro st
    rw [simulateQ_bind, simulateQ_query, StateT.run_bind]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact CostLe.bind prims (himpl t st) fun p => ih p.1 p.2

/-- A phase with the adversary on the counted copy costs at most `fuel` rounds of the adversary. The
honest operators run on the free copy. -/
theorem costLe_executePhase_world {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (step : ℕ) (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (fuel : ℕ)
    (state : A.State) (program : C.Party → PartyM C E RealSpec α) :
    CostLe prims (executePhase worldRoles D A noFunctionality fuel state program) (fuel * step) := by
  unfold executePhase startSteps
  refine (CostLe.bind prims (CostLe.sequenceFin prims _ fun i => ?_) fun steps => by
    rw [← seedGenEraseLog_executeRounds]
    exact CostLe.map prims _ (CostLe.executeRounds_observed prims D A step hround fuel state steps)).mono prims
      (Nat.zero_add _).le
  split_ifs
  · exact CostLe.pure prims _
  · exact CostLe.free prims _

variable [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

omit [Algebra Bit E] in
/-- The calls of `F_rand` cost nothing when each local query and each leak of a call cost nothing. -/
theorem costLe_simulateQ_callLeaks [SampleableType E] {σ : Type}
    (impl : QueryImpl (LocalSpec C + (RandLeak →ₒ RandReplies C E)) (StateT σ (OracleComp (WorldSpec C))))
    (hlocal : ∀ t st, CostLe prims ((impl (.inl t)).run st) 0)
    (hcall : ∀ l st, CostLe prims ((impl (.inr (.inr l))).run st) 0) (D : C.Coalition)
    (inputs : C.Party → Option Unit) :
    ∀ (calls : List RandCall) st, CostLe prims ((simulateQ impl (calls.mapM fun call => simulateQ callLeaks
      (((Frand (C := C) E).sum (Frand Bit)).run D fun i => (inputs i).map fun _ => call.input))).run st) 0
  | [], st => CostLe.pure prims _
  | call :: calls, st => by
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind]
    refine (CostLe.bind prims ?_ fun p => ?_).mono prims (Nat.zero_add _).le
    · rw [← QueryImpl.simulateQ_compose]
      refine costLe_simulateQ_zero prims _ (fun t st => ?_) _ st
      rw [QueryImpl.apply_compose]
      unfold callLeaks
      rcases t with t | l
      · erw [QueryImpl.add_apply_inl, simulateQ_query]
        simpa using hlocal t st
      · erw [QueryImpl.add_apply_inr]
        rw [simulateQ_bind, StateT.run_bind]
        refine (CostLe.bind prims (m := 0) (costLe_simulateQ_leak prims impl _ st (hcall l st))
          fun r => ?_).mono prims le_rfl
        rcases r with ⟨_ | _, st'⟩ <;> exact CostLe.pure prims _
    · rw [simulateQ_bind, StateT.run_bind]
      exact (CostLe.bind prims (costLe_simulateQ_callLeaks impl hlocal hcall D inputs calls p.2) fun r =>
        CostLe.pure prims _).mono prims le_rfl

omit [Algebra Bit E] in
/-- The run of `FrandCalls` costs at most the cost `M` of the leak of the receivers, when each local
query and each leak of a call cost nothing. -/
theorem costLe_simulateQ_FrandCalls [SampleableType E] {σ : Type}
    (impl : QueryImpl (LocalSpec C + (RandLeak →ₒ RandReplies C E)) (StateT σ (OracleComp (WorldSpec C))))
    (M : ℕ) (hlocal : ∀ t st, CostLe prims ((impl (.inl t)).run st) 0)
    (hreceivers : ∀ st, CostLe prims ((impl (.inr (.inl ()))).run st) M)
    (hcall : ∀ l st, CostLe prims ((impl (.inr (.inr l))).run st) 0) (calls : List RandCall) (D : C.Coalition)
    (inputs : C.Party → Option Unit) (st : σ) :
    CostLe prims ((simulateQ impl ((FrandCalls calls).run D inputs)).run st) M := by
  unfold FrandCalls
  simp only [simulateQ_bind, StateT.run_bind]
  have hfirst : CostLe prims (do
      let p ← (simulateQ impl (leak (C := C) (R := RandReplies C E) (Sum.inl () : RandLeak))).run st
      (simulateQ impl (match p.1 with
        | Sum.inl receivers => pure receivers
        | Sum.inr _ => pure ∅)).run p.2) (M + 0) :=
    CostLe.bind prims (costLe_simulateQ_leak prims impl _ st (hreceivers st)) fun p => by
      rcases p with ⟨_ | _, st'⟩ <;> exact CostLe.pure prims _
  refine (CostLe.bind prims hfirst (m := 0 + 0) fun p =>
    CostLe.bind prims (costLe_simulateQ_callLeaks prims impl hlocal hcall D inputs calls p.2)
      fun r => CostLe.pure prims _).mono prims (by simp)

/-- The ideal run of `FrandCalls calls` with `prssRealRandSimulator` makes at most `q` counted calls,
for a `q`-query adversary and distinguisher. -/
theorem prssRealRand_queryBound (K : Constants C E) [SampleableType E] (label : ℕ) (calls : List RandCall)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D (FrandCalls calls)
      (prssRealRandSimulator K label calls D A) x z) Z)) q := by
  obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  refine (CostLe.bind prims (m := final) (CostLe.bind prims (m := setupRounds * step + 0)
    (CostLe.bind prims (m := 0) (CostLe.of_counted prims _ _ (hs _ _)) fun _ => CostLe.pure prims _)
    fun st => ?_) fun r => CostLe.of_counted prims _ _ (hz _)).mono prims (by omega)
  refine CostLe.bind prims (costLe_simulateQ_FrandCalls prims _ _ ?_ ?_ ?_ calls D _ st) fun p => ?_
  · intro t st
    change CostLe prims ((StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t)))).run st) 0
    rw [StateT.run_lift]
    exact CostLe.bind prims (CostLe.free prims _) fun _ => CostLe.pure prims _
  · intro st
    change CostLe prims ((prssRealRandSimulator K label calls D A).answer st (.inl ()) >>= fun p =>
      pure (p.2, p.1)) _
    exact (CostLe.bind prims (m := 0) (CostLe.bind prims (m := 0)
      (costLe_executePhase_world prims D A step hr setupRounds _ _) fun _ => CostLe.pure prims _)
      fun _ => CostLe.pure prims _).mono prims le_rfl
  · intro l st
    change CostLe prims ((prssRealRandSimulator K label calls D A).answer st (.inr l) >>= fun p =>
      pure (p.2, p.1)) _
    refine CostLe.bind prims (m := 0) ?_ fun _ => CostLe.pure prims _
    unfold prssRealRandSimulator
    dsimp only
    rcases st.calls with _ | ⟨_ | _, rest⟩
    · exact CostLe.pure prims _
    · exact CostLe.bind prims (CostLe.free prims _) fun _ => CostLe.pure prims _
    · exact CostLe.bind prims (CostLe.free prims _) fun _ => CostLe.pure prims _
  · rcases p with ⟨outputs, state⟩
    exact CostLe.bind prims (CostLe.pure prims _) fun _ => CostLe.pure prims _

end Bound

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- One PRSS setup and the `Rand` calls from its keys securely compute a fixed public list of
`F_rand` calls with selective abort, on the real network, with the simulator `prssRealRandSimulator`. -/
theorem prssRealRandSecurity [SampleableType E] (prims : Primitives) (K : Constants C E) :
    PrssRealRandSecurityStatement prims K := by
  classical
  have : Fintype E := Fintype.ofEquiv _ K.encode.symm
  intro label calls D A x z Z q _ hq
  refine ⟨by simpa only [Nat.add_zero] using prssRealRand_queryBound prims K label calls D A x z Z q hq, ?_⟩
  have h := abs_sub_le_of_hops prims D (prssRealRandGame K label calls D A x z Z)
    (distinguish (idealExecution (fun oa => oa) D (FrandCalls calls) (prssRealRandSimulator K label calls D A) x z) Z)
    (prssSetupHashError C (q + C.n * (termCount C + C.n)) / 2 + prssRandHashError C (q + C.n * (termCount C + C.n)))
    (prssSetupHashError C q)
    (by
      unfold reductionReal
      rw [prfRealExp_prgReduction]
      exact (keyWorld_coupling prims D _).trans (prssRealRand_key K prims label calls
        (prssRealRand_coupling K prims label calls) (prssRealRand_view K prims label calls) D A x z Z q hq))
    (by
      unfold reductionIdeal
      rw [prfIdealExp_prgReduction]
      exact prssRealRand_streamHop K prims label calls D A x z Z q hq)
  unfold prssRealRandGame at h
  unfold prssRealRandHashError
  linarith

end ThresholdLeanXmssSecurity
