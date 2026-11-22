import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.Ideal

/-!
# The coupling of the seed generation of the simulator with the private table

`worldSeedGen_coupling` proves `WorldSeedGenCoupling`, so `seedIdealGeneral` proves
`SeedIdealGeneral`.

* `observe_eq` writes `observe` as a computation on the counted copy that returns its log
  (`logged`). The log of `tableNet` has only the calls of the class of the seed generation
  (`logged_table`), and `extractReveal .seedGen` reads only such calls (`extractReveal_classLog`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

open SeedPartition SeedEmulation
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned (isPrivate)

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The log of an observed computation -/

/-- A local computation with the log of its calls of `H`. -/
def logImpl : QueryImpl (LocalSpec C) (WriterT (CallLog C) (OracleComp (LocalSpec C))) := fun t =>
  match t with
  | .inr (.inl q) => do
      let y ← liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))
      tell [(q, y)]
      pure y
  | t => liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))

/-- A local computation that returns the log of its calls of `H`. -/
def logged {α : Type} (oa : OracleComp (LocalSpec C) α) : OracleComp (LocalSpec C) (α × CallLog C) :=
  (simulateQ logImpl oa).run

/-- The calls of the class of the seed generation in a log. -/
def classLog (log : CallLog C) : CallLog C := log.filter fun e => isSeedGenQuery e.1

theorem observe_eq {α : Type} (oa : OracleComp (LocalSpec C) α) :
    observe oa = worldRoles.adversary (logged oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [observe, logged]
  | query_bind t k ih =>
    simp only [observe, logged] at ih ⊢
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      WriterT.run_bind, ih, ThresholdLeanXmssSecurity.adversary_bind, adversary_map]
    rcases t with n | q | x
    all_goals congr 1

theorem logged_bind {α β : Type} (oa : OracleComp (LocalSpec C) α) (k : α → OracleComp (LocalSpec C) β) :
    logged (oa >>= k) = logged oa >>= fun p => (fun r => (r.1, p.2 ++ r.2)) <$> logged (k p.1) := by
  simp [logged, WriterT.run_bind]

theorem logged_liftComp {α : Type} (p : ProbComp α) :
    logged (liftComp p (LocalSpec C)) = (fun a => (a, [])) <$> liftComp p (LocalSpec C) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [logged]
  | query_bind n k ih =>
    have e : liftComp (liftM (unifSpec.query n) : ProbComp _) (LocalSpec C) =
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl n)) : OracleComp _ _) := rfl
    rw [liftComp_bind, e, logged_bind]
    simp only [ih]
    simp only [logged, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, logImpl]
    simp [WriterT.run_liftM, map_bind, Functor.map_map]

theorem classLog_append (a b : CallLog C) : classLog (a ++ b) = classLog a ++ classLog b := by
  simp [classLog, List.filter_append]

/-- The log of the run of `b` under the private table has the calls of the class of `b`. -/
theorem logged_table (prims : Primitives) {α : Type} (b : OracleComp (LocalSpec C) α) (T : HashCache C) :
    (fun r => ((r.1.1, r.2), classLog r.1.2)) <$>
        (simulateQ (Partitioned.tableLocal seedGenOutside prims) (logged b)).run T =
      logged ((simulateQ (Partitioned.tableLocal seedGenOutside prims) b).run T) := by
  induction b using OracleComp.inductionOn generalizing T with
  | pure a => simp [logged, classLog]
  | query_bind t k ih =>
    rw [logged_bind]
    simp only [logged] at ih
    have hl : ∀ {β : Type} (p : ProbComp β), (simulateQ logImpl (liftM p : OracleComp (LocalSpec C) β)).run =
        (fun a => (a, [])) <$> (liftM p : OracleComp (LocalSpec C) β) := fun p => by
      rw [← liftComp_eq_liftM]
      exact logged_liftComp p
    rcases t with n | q | x
    · simp [logged, logImpl, Partitioned.tableLocal, isPrivate, WriterT.run_liftM, map_bind]
      refine bind_congr fun a => ?_
      exact ih a T
    · by_cases hq : isSeedGenQuery q = true
      · simp [logged, logImpl, Partitioned.tableLocal, isPrivate, seedGenOutside, hq, WriterT.run_liftM,
          WriterT.run_bind, map_bind]
        refine bind_congr fun a => ?_
        rw [← ih a T, Functor.map_map]
        simp [classLog, hq]
      · simp [logged, logImpl, Partitioned.tableLocal, isPrivate, seedGenOutside, hq, WriterT.run_liftM,
          WriterT.run_bind, map_bind, hl]
        refine bind_congr fun a => ?_
        rw [← ih a.1 a.2]
        simp [classLog, hq]
    · have hx : isSeedGenQuery (C := C) (Query.streamKey x.2.1) = false := rfl
      simp [logged, logImpl, Partitioned.tableLocal, isPrivate, seedGenOutside, hx, WriterT.run_liftM,
        map_bind, hl]
      refine bind_congr fun a => ?_
      exact ih a.1 a.2

/-- `extractReveal` of the seed generation reads only the calls of its class. -/
theorem extractReveal_classLog (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E)) (j i : C.Party) :
    extractReveal .seedGen (classLog log) sent j i = extractReveal .seedGen log sent j i := by
  unfold extractReveal
  congr 1
  induction log with
  | nil => rfl
  | cons e log ih =>
    obtain ⟨q, y⟩ := e
    by_cases hq : isSeedGenQuery q = true
    · simp only [classLog, List.filter_cons, hq, ite_true, List.findSome?_cons]
      rw [← ih]
      rfl
    · simp only [classLog, List.filter_cons, hq, Bool.false_eq_true, ite_false, List.findSome?_cons]
      simp only [classLog] at ih
      rw [ih]
      cases q with
      | commit phase a b r =>
        cases phase
        · simp [isSeedGenQuery] at hq
        · simp
      | derive phase _ _ => simp
      | sharedKeys phase _ => simp
      | _ => simp

variable (prims : Primitives)

/-- An observed computation of `net` in `streamWorld` on the merged cache. -/
theorem observe_stream (D : C.Coalition) {α : Type} (b : OracleComp (LocalSpec C) α) (S T : HashCache C)
    (H : HiddenCache C) :
    (simulateQ (streamWorld prims D) (observe b)).run (merge seedGenOutside S T, H) =
      (fun z => (z.1.1, (merge seedGenOutside z.2 z.1.2, H))) <$>
        (simulateQ (worldAnswer prims) (worldRoles.adversary
          ((simulateQ (Partitioned.tableLocal seedGenOutside prims) (logged b)).run T))).run S := by
  rw [observe_eq, adversary_coupling seedGenOutside prims D (logged b) S T H]

/-- The observed computation of `net` under the private table over the world. -/
theorem observe_table {α : Type} (b : OracleComp (LocalSpec C) α) (S T : HashCache C) :
    (simulateQ (worldAnswer prims) (observe ((simulateQ (Partitioned.tableLocal seedGenOutside prims) b).run T))).run S =
      (fun z => (((z.1.1.1, z.1.2), classLog z.1.1.2), z.2)) <$>
        (simulateQ (worldAnswer prims) (worldRoles.adversary
          ((simulateQ (Partitioned.tableLocal seedGenOutside prims) (logged b)).run T))).run S := by
  rw [observe_eq, ← logged_table, adversary_map, simulateQ_map, StateT.run_map]

omit prims in
theorem run_sequenceFin_lift {β : Type} : ∀ {n : ℕ} (p : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) β)
    (q : Fin n → OracleComp (WorldSpec C) β), (∀ i, (p i).run = (fun a => (a, [])) <$> q i) →
      (OverPermutation.sequenceFin p).run = (fun a => (a, [])) <$> OverPermutation.sequenceFin q
  | 0, p, q, _ => by simp [OverPermutation.sequenceFin]
  | n + 1, p, q, h => by
    simp only [OverPermutation.sequenceFin, WriterT.run_bind, h 0, bind_map_left, map_bind]
    refine bind_congr fun a => ?_
    rw [run_sequenceFin_lift (fun i => p i.succ) (fun i => q i.succ) fun i => h i.succ]
    simp [Functor.map_map]

omit prims in
/-- A round of the real network with the observed adversary. -/
theorem stepRound_observed {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    (stepRound observedRoles D A noFunctionality st steps).run =
      observe (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) >>= fun p =>
        (fun steps' => ((p.1.1, steps', p.1.2), p.2)) <$> UsedHit.nextSteps D steps p.1.2 := by
  unfold stepRound
  rw [ite_eq_right (by simp [callInput_real])]
  simp only [WriterT.run_bind]
  change observe _ >>= _ = _
  refine bind_congr fun p => ?_
  rw [run_sequenceFin_lift _ (fun j => match steps j with
    | .done out => pure (Step.done out)
    | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (resume fun k => if k ∈ D.1 then p.1.2 k j else (steps k).delivered j))
    | .call _ _ => pure (Step.done none)) fun j => ?_]
  · simp only [UsedHit.nextSteps, WriterT.run_pure, map_pure, Functor.map_map, bind_pure_comp,
      List.empty_eq, List.append_nil]
    rfl
  · cases steps j with
    | done out => simp
    | wait outbox resume =>
      by_cases hj : j ∈ D.1
      · simp [hj]
      · simp only [hj, ite_false]
        simp [observedRoles, WriterT.run_liftM]
    | call input resume => exact input.elim

/-! ## The seed generation of the simulator -/

section Coupling

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

omit prims in
theorem free_sample_worldSafe {α : Type} (p : ProbComp α) :
    AllQueriesSatisfy (free (liftComp p (LocalSpec C))) (WorldSafe seedGenOutside) := by
  refine free_worldSafe seedGenOutside seedGenOutside_streamKey ?_
  exact AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) p)
    fun t _ => (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 rfl

omit prims in
theorem program_worldSafe (q : Query C) (v : HashOutput) (hq : isSeedGenQuery q = true) :
    AllQueriesSatisfy (program q v) (WorldSafe seedGenOutside) := by
  unfold program counted
  rw [simulateQ_query]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inr (q, v))) _).2
    (by simp [WorldSafe, seedGenOutside, hq])

omit prims in
theorem run_eraseLog {σ α γ : Type} (W : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (X : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) (s : σ) (f : (α × CallLog C) × σ → ProbComp γ)
    (hf : ∀ p, f p = f ((p.1.1, []), p.2)) :
    ((simulateQ W X.run).run s >>= f) = ((simulateQ W (seedGenEraseLog X)).run s >>= fun p => f ((p.1, []), p.2)) := by
  simp only [seedGenEraseLog, simulateQ_map, StateT.run_map, bind_map_left]
  exact bind_congr fun p => hf p

omit prims [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem nextSteps_stepPublic {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepPublic seedGenOutside (steps i)) (sent : C.Party → C.Party → Option (Msg E))
    (z : C.Party → Step C E RealSpec α) (hz : z ∈ support (UsedHit.nextSteps D steps sent)) :
    ∀ i, StepPublic seedGenOutside (z i) := by
  intro i
  have hi := mem_support_sequenceFin_oc _ z hz i
  have hpi := hsteps i
  revert hi hpi
  cases steps i with
  | done out =>
    intro hi _
    simp only [support_pure, Set.mem_singleton_iff] at hi
    rw [hi]
    trivial
  | wait outbox resume =>
    intro hi hpi
    dsimp only at hi
    split_ifs at hi
    · simp only [support_pure, Set.mem_singleton_iff] at hi
      rw [hi]
      trivial
    · exact advance_stepPublic seedGenOutside _ (hpi _) _ (support_simulateQ_subset _ _ hi)
  | call input resume => exact input.elim

/-- A state of `net` with a table as a state of `tableNet net`. -/
def tablePair (net : Adversary C E Unit PEmpty PEmpty) (p : net.State × HashCache C) : (tableNet prims net).State := p

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The observed start of `tableNet` over the world. -/
theorem observe_tableNet_start (net : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Option Unit) (z : Aux)
    (S : HashCache C) :
    (simulateQ (worldAnswer prims) (observe ((tableNet prims net).start x z))).run S =
      (fun w => ((tablePair prims net (w.1.1.1, w.1.2), classLog w.1.1.2), w.2)) <$>
        (simulateQ (worldAnswer prims) (worldRoles.adversary
          ((simulateQ (Partitioned.tableLocal seedGenOutside prims) (logged (net.start x z))).run ∅))).run S :=
  (congrArg (fun b => (simulateQ (worldAnswer prims) (observe b)).run S) (tableNet_start prims net x z)).trans
    (observe_table prims _ S ∅)

omit prims in
theorem observe_map {α β : Type} (f : α → β) (oa : OracleComp (LocalSpec C) α) :
    observe (f <$> oa) = (fun p => (f p.1, p.2)) <$> observe oa := by
  rw [observe_eq, observe_eq, ← adversary_map]
  congr 1
  simp [logged, simulateQ_map, WriterT.run_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The observed round of `tableNet` over the world. -/
theorem observe_tableNet_round (net : Adversary C E Unit PEmpty PEmpty) (st : net.State × HashCache C)
    (msgs : C.Party → C.Party → Option (Msg E)) (S : HashCache C) :
    (simulateQ (worldAnswer prims) (observe ((tableNet prims net).round (tablePair prims net st) msgs))).run S =
      (fun w => (((tablePair prims net (w.1.1.1.1, w.1.2), w.1.1.1.2), classLog w.1.1.2), w.2)) <$>
        (simulateQ (worldAnswer prims) (worldRoles.adversary
          ((simulateQ (Partitioned.tableLocal seedGenOutside prims) (logged (net.round st.1 msgs))).run st.2))).run S := by
  have h := tableNet_round prims net st msgs
  have e : observe ((tableNet prims net).round (tablePair prims net st) msgs) =
      (fun p => ((tablePair prims net (p.1.1.1, p.1.2), p.1.1.2), p.2)) <$>
        observe ((simulateQ (Partitioned.tableLocal seedGenOutside prims) (net.round st.1 msgs)).run st.2) := by
    have hm := observe_map (β := (tableNet prims net).State × (C.Party → C.Party → Option (Msg E)))
      (fun r => ((r.1.1, r.2), r.1.2))
      ((simulateQ (Partitioned.tableLocal seedGenOutside prims) (net.round st.1 msgs)).run st.2)
    exact (congrArg observe h).trans hm
  rw [e, simulateQ_map, StateT.run_map, observe_table, Functor.map_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem worldSeedGen_coupling : WorldSeedGenCoupling (C := C) (E := E) prims := by
  intro D net S H
  unfold worldSeedGen
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  rw [observe_stream, observe_tableNet_start, bind_map_left, bind_map_left]
  apply bind_congr; intro z
  dsimp only
  rw [simulate_frame seedGenOutside prims D (free_sample_worldSafe _), bind_map_left]
  apply bind_congr; intro keyGen
  rw [simulate_frame seedGenOutside prims D (free_sample_worldSafe _), bind_map_left]
  apply bind_congr; intro parts
  rw [simulate_frame seedGenOutside prims D (startSteps_worldSafe D _ fun i => seedGenWith_public i _),
    bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro steps hsteps
  dsimp only
  simp only [stepRound_observed, simulateQ_bind, StateT.run_bind]
  rw [observe_stream, observe_tableNet_round, bind_map_left, bind_map_left]
  dsimp only
  simp only [bind_assoc]
  apply bind_congr; intro a
  have hpub := startSteps_stepPublic prims D _ (fun i => seedGenWith_public i _) _ steps hsteps
  rw [simulate_frame seedGenOutside prims D (allQueries_map _ (nextSteps_worldSafe D _ hpub _)), bind_map_left]
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro b hb
  rw [simulate_frame seedGenOutside prims D (free_sample_worldSafe _), bind_map_left]
  apply bind_congr; intro high
  dsimp only
  simp only [← classLog_append, extractReveal_classLog]
  rw [simulate_frame seedGenOutside prims D (program_worldSafe _ _ rfl), bind_map_left]
  apply bind_congr; intro w1
  rw [simulate_frame seedGenOutside prims D (UsedHit.mapM_satisfy _ _ (fun T => by
    split
    · exact program_worldSafe _ _ rfl
    · exact allQueriesSatisfy_pure _ _) _), bind_map_left]
  apply bind_congr; intro w2
  rw [simulate_frame seedGenOutside prims D (UsedHit.mapM_satisfy _ _ (fun j => UsedHit.mapM_satisfy _ _
    (fun i => by
      split
      · exact program_worldSafe _ _ rfl
      · exact allQueriesSatisfy_pure _ _) _) _), bind_map_left]
  apply bind_congr; intro w3
  have hb' : b.1 ∈ support (UsedHit.nextSteps D steps.1 a.1.1.1.2) :=
    support_simulateQ_run'_subset (worldAnswer prims) _ a.2 (by rw [StateT.run'_eq, support_map]; exact ⟨b, hb, rfl⟩)
  have hpub' := nextSteps_stepPublic D steps.1 hpub _ b.1 hb'
  dsimp only
  rw [run_eraseLog _ _ _ _ fun _ => rfl, run_eraseLog _ _ _ _ fun _ => rfl, seedGenEraseLog_executeRounds,
    seedGenEraseLog_executeRounds, executeRounds_coupling prims D net _ _ _ hpub' w3.2 a.1.2 H, bind_map_left]
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The ideal end of the seed generation claim, general over the rest. -/
theorem seedIdealGeneral (prims : Primitives) : SeedIdealGeneral (C := C) (E := E) prims :=
  seedIdealGeneral_of_coupling prims (worldSeedGen_coupling prims)

end Coupling

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.seedIdealGeneral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.seedIdealGeneral
