import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgDisc
import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestLog

/-!
# Hidden-cache freshness at the first-run check

The hidden cache starts empty in setup. The actual initial-program discipline
preserves its future region through scheduler passes, and the decoder's full
first-pass equality transfers that region to the boundary prefix. Its cutoff
is the exact hybrid label, for first-run checkpoints only.

Scheduler and setup proofs port `TreeCheckHonestLog`; query and retained-prefix
frames reuse `TreeCheckPrgWindow`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgFirstFresh
open TreeCheckWalkDef (Decoded initial index_support)
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckPrgDisc TreeCheckPrgWindow TreeSimHashCount
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E α β : Type}
variable (prims : Primitives) (D : C.Coalition)

/-- Port of `advance_honest`, replacing the log/key invariant by freshness. -/
theorem advance_futureEmpty (limit : ℕ)
    (P : OracleComp (PartySpec C E RealSpec) (Option α))
    (disc : PrgDisc limit 1 P) (s : TreeSimState C)
    (honest : TreeSimFutureEmpty limit s.1.2)
    (r : Step C E RealSpec α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (advance P))).run s)) :
    TreeSimFutureEmpty limit r.2.1.2 := by
  induction P using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [advance_pure, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact honest
  | query_bind t k ih =>
    rcases t with (q | out) | impossible
    · rw [advance_query_bind, free_bind] at run
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨mid, hmid, hrun⟩ := run
      have hquery : mid ∈ support ((treeSimLoggedWorld prims D (.inr q)).run s) := by
        change mid ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr q)))).run s) at hmid
        simpa only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map] using hmid
      have honest' := quiet_query prims D limit (.inr q) disc.local_inv.1 s mid honest hquery
      exact ih mid.1 (disc.local_inv.2 mid.1) mid.2 honest' r hrun
    · change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (pure (.wait out k) : OracleComp (LocalSpec C) _))).run s) at run
      simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      exact honest
    · exact impossible.elim

theorem start_futureEmpty (limit : ℕ) (program : C.Party → PartyM C E RealSpec α)
    (disc : ∀ i, i ∉ D.1 → PrgDisc limit 1 (program i).run)
    (s : TreeSimState C) (honest : TreeSimFutureEmpty limit s.1.2)
    (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D program)).run s)) :
    TreeSimFutureEmpty limit r.2.1.2 := by
  unfold startSteps at run
  rw [simulateQ_sequenceFin] at run
  apply TreeCheckHonestLog.sequenceFin_preserves (fun s : TreeSimState C => TreeSimFutureEmpty limit s.1.2) _ _ s honest r run
  intro i s hs r hr
  split_ifs at hr with hi
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hs
  · exact advance_futureEmpty prims D limit (program i).run (disc i hi) s
      hs r hr

variable {A : Adversary C E (Keys C) PEmpty PEmpty}

theorem next_futureEmpty (limit : ℕ) (Z : Distinguisher C A.State TreeOutput)
    (fuel : ℕ) (p q : TreeCheckWalkDef.Pending A)
    (honest : TreeSimFutureEmpty limit p.world.1.2)
    (disc : ∀ i, i ∉ D.1 → PrgDisc limit 1 (p.program i).run)
    (run : .inl q ∈ support (TreeCheckWalkDef.next prims D Z fuel p)) :
    TreeSimFutureEmpty limit q.world.1.2 := by
  unfold TreeCheckWalkDef.next at run
  simp only [mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  have honest' := start_futureEmpty prims D limit p.program disc p.world honest started hs
  split_ifs at run
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨_, _, impossible⟩ := run
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
    obtain ⟨reply, hr, rfl⟩ := run
    exact run_quiet prims D limit _ (counted_zero limit _) _ honest' reply hr

section Setup
variable [Field E] [Algebra Bit E]

theorem phase_futureEmpty_quiet (limit : ℕ) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α)
    (quiet : ∀ i, PartyBudget (PrgFrom limit) (program i) 0)
    (s : TreeSimState C) (honest : TreeSimFutureEmpty limit s.1.2)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run s)) :
    TreeSimFutureEmpty limit r.2.1.2 := by
  unfold executePhase at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, hs, hrun⟩ := run
  have honest' := start_futureEmpty prims D limit program
    (fun i _ => PrgDisc.of_quiet (quiet i) 1) s honest started hs
  apply rounds_futureEmpty prims D limit fuel state started.1 _ started.2 honest' r hrun
  intro i
  have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, mem_support_pure_iff] at each
    rw [each]
    trivial
  · simp only [if_neg hi, worldRoles] at each
    exact advance_stepBudget (PrgFrom limit) _ (quiet i) _ (treeSimCheck_support_free _ each)

-- Port of TreeCheckHonestLog derive/sample/setup quietness: setup has no PRG reads.
theorem derive_prg_zero (limit : ℕ) (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (fun t => PrgFrom (C := C) limit (.inr t)) 0 := by
  unfold deriveKeys
  dsimp only
  rw [← ite_bind]
  refine isQueryBoundP_bind (p := fun t => PrgFrom limit (.inr t))
    (n := 0) (m := 0) ?_ (fun parameter _ => ?_)
  · split_ifs
    · exact hash_zero limit _
    · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun terms _ => ?_)
    · simpa using queryBound_mapM (fun t => PrgFrom (C := C) limit (.inr t)) _ 0 C.terms
        (fun T _ => by
          split_ifs
          · exact hash_zero limit _
          · exact isQueryBoundP_pure _ _ _)
    · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun pairs _ => isQueryBoundP_pure _ _ _)
      simpa using queryBound_mapM (fun t => PrgFrom (C := C) limit (.inr t)) _ 0 C.parties
        (fun j _ => by
          split_ifs
          · exact isQueryBoundP_pure _ _ _
          · exact hash_zero limit _)

theorem sample_prg_zero (limit : ℕ) (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) (PrgFrom limit) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) (PrgFrom limit) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PrgFrom]), fun u => by simpa [PrgFrom] using ih u⟩

theorem setup_prg_zero (limit : ℕ) (i : C.Party) :
    PartyBudget (PrgFrom limit) (prssSetup i : PartyM C E RealSpec _) 0 := by
  have hm (f : C.Party → Query C) :
      PartyBudget (PrgFrom limit) (oracleStep (C.parties.mapM fun j => hashQuery (f j)) :
        PartyM C E RealSpec _) 0 := by
    apply oracle_bound (E := E)
    simpa using queryBound_mapM (fun t => PrgFrom (C := C) limit (.inr t))
      (fun j => hashQuery (f j)) 0 C.parties (fun j _ => hash_zero limit _)
  unfold prssSetup
  refine (localStep_bound (E := E) (G := RealSpec) (sample_prg_zero limit (sampleParts (C := C)))).bind (m := 0) fun own => ?_
  unfold commitRevealEcho
  simp only [bind_assoc]
  exact (hm _).bind fun commits =>
    (party_quiet_of_zero limit (PartyBound.exchange _)).bind fun committed =>
      (party_quiet_of_zero limit (PartyBound.exchange _)).bind fun revealed =>
        (hm _).bind fun opens =>
          (party_quiet_of_zero limit (PartyBound.require _)).bind fun _ =>
            (oracle_bound (derive_prg_zero limit _ _ _)).bind fun keys =>
              (hm _).bind fun shared =>
                (party_quiet_of_zero limit (PartyBound.exchange _)).bind fun received =>
                  (party_quiet_of_zero limit (PartyBound.require _)).bind fun _ =>
                    (PartyBudget.pure _).bind fun result => PartyBudget.pure _

theorem setup_futureEmpty (limit : ℕ) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : p ∈ support (treeSaltSetup prims D A x z)) :
    TreeSimFutureEmpty limit p.2.1.2 := by
  unfold treeSaltSetup at run
  rw [mem_support_bind_iff] at run
  obtain ⟨start, hs, run⟩ := run
  have honest : TreeSimFutureEmpty limit start.2.1.2 :=
    run_quiet prims D limit _ (counted_zero limit _) _ (by intro a ha; rfl) start hs
  apply phase_futureEmpty_quiet prims D limit _ _ _ (fun i => setup_prg_zero limit i) _ honest p
  simpa only [simulateQ_executePhase, treeSimRealRoles] using run


end Setup

theorem reached_futureEmpty (limit N : ℕ) (Z : Distinguisher C A.State TreeOutput)
    (start : TreeCheckWalkDef.Pending A)
    (honest : TreeSimFutureEmpty limit start.world.1.2)
    (disc : ∀ i, i ∉ D.1 → PrgDisc limit (N + 1) (start.program i).run)
    {m : ℕ} {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z start m q) (below : m ≤ N) :
    TreeSimFutureEmpty limit q.world.1.2 := by
  induction reached with
  | start => exact honest
  | @next n fuel p q reached fuelLeft run ih =>
    apply next_futureEmpty prims D limit Z fuel p q (ih (by omega)) _ run
    intro i hi
    exact ((disc i hi).residual (Reached.residual prims D Z reached i hi) (by omega)).antitone (by omega)

section Actual
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8000 in
/-- Port of `sourceWalk_honest`: freshness from setup at the literal boundary
cutoff, without a liveness or incoming-cache premise. -/
theorem sourceWalk_futureEmpty (z : Aux) (j : ℕ) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (first : j < (firstChunks settings tree).length)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (c : Decoded (decode prims K D A circuits settings top tree x p.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : (Decoded (decode prims K D A circuits settings top tree x p.1.2 j) ×
        TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A) ∈ support
      ((sourceWalk prims K D A circuits settings top tree x j Z step p).cut prims K circuits settings D Z).pre) :
    let W := sourceWalk prims K D A circuits settings top tree x j Z step p
    TreeSimFutureEmpty ((W.boundary c).batch.initial.1 +
      depth ((W.boundary c).batch.jobs.map (circuits (W.boundary c).batch.parameter ·.kind)) + 1) o.2.1.2 := by
  let W := sourceWalk prims K D A circuits settings top tree x j Z step p
  let limit := firstLimit K D circuits settings tree x j
  have label : (W.boundary c).batch.initial.1 +
      depth ((W.boundary c).batch.jobs.map (circuits (W.boundary c).batch.parameter ·.kind)) + 1 = limit := by
    change lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings c.1.2.encoding tree) j +
      depth (((lockstepChunks settings c.1.2.encoding tree).getD j []).map
        (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1 = limit
    rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree c.1.2.encoding j first,
      TreeCheckWalkState.lockstepStart_first circuits settings tree _ c.1.2.encoding j first.le]
    rfl
  have hc : .inl c ∈ support W.pre := by
    with_reducible exact index_support prims D Z K circuits settings W c o run
  have ho : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (W := W) (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      (D := D) (Z := Z) (c := c) (o := o) run)
  have hit : ∃ m, m ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j ∧
      Reached prims D Z (initial K circuits settings top tree x p) m c.1.1 := by
    with_reducible exact TreeCheckHonestLog.walk_first_hit prims D K A circuits settings top tree x Z p dealt j first c hc
  obtain ⟨m, below, reached⟩ := hit
  have initialDisc := initial_program_prgDisc K D circuits settings top tree x A p dealt
  have initialFresh : TreeSimFutureEmpty limit (initial K circuits settings top tree x p).world.1.2 :=
    setup_futureEmpty prims D limit A x z p hp
  have fresh := reached_futureEmpty prims D limit
    (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) Z
    (initial K circuits settings top tree x p) initialFresh
    (fun i _ => initialDisc i j first) reached below
  have disc : ∀ i, i ∉ D.1 → PrgDisc limit 1 (c.1.1.program i).run := by
    intro i hi
    exact ((initialDisc i j first).residual (Reached.residual prims D Z reached i hi)
      (by omega)).antitone (by omega)
  have fits := decode_sound prims K D A circuits settings top tree x p.1.2 j c
  apply boundary_pre_futureEmpty prims D K circuits settings (W.boundary c) _ _ o ho
  · intro i
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  · intro r hr
    rw [label]
    apply start_futureEmpty prims D limit c.1.1.program disc c.1.1.world fresh r
    rw [fits.2.2]
    exact hr

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8000 in
/-- The exact hidden-cache premise of the check kernel on first-run walk
checkpoints. All source hypotheses come from `AtWalk`. -/
theorem walkCheckpoint_futureEmpty (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun _ tree D _ _ _ Z _ _ j _ W =>
      j.val < (firstChunks settings tree).length →
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
          TreeSimFutureEmpty ((W.cut prims K circuits settings D Z).hybrid (.inl (c, o))).label o.2.1.2 := by
  intro _ top tree D A x z Z q dealt bounded small j p hp first c o run
  with_reducible
    have fresh := sourceWalk_futureEmpty prims D K A circuits settings top tree x Z
      z j (TreeCheckQueryBudget.ofBound bounded).step p dealt first hp c o run
  simpa only [TreeCheckTailWalk.cut, family, sourceWalk, TreeCheckWalkDef.hybrid,
    TreeCheckWalkDef.boundary] using fresh

end Actual
end TreeCheckPrgFirstFresh
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.advance_futureEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.advance_futureEmpty

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.reached_futureEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.reached_futureEmpty

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.setup_futureEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.setup_futureEmpty

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.sourceWalk_futureEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.sourceWalk_futureEmpty

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.walkCheckpoint_futureEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgFirstFresh.walkCheckpoint_futureEmpty
