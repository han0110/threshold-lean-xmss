import ThresholdLeanXmssSecurity.Proof.TreeEvents
import ThresholdLeanXmssSecurity.Proof.Tprf

/-!
# The tree simulation hop from the cache of earlier phases

`TreeSimulationHop` (`Tree.lean:4463`) starts `streamWorld` from the empty cache `(∅, ∅)`. Decision D6
of `FIX.md` lets a ceremony start from the cache of earlier phases. `TreeSimulationHopFrom` models this cache as the cache
that a prefix `pre` leaves under `localAnswer`, the lazy random oracle of `H`, from the empty cache. The
prefix makes at most `q0` counted calls (`IsQueryBoundP pre Counted q0`). Its output is the auxiliary
input `z`, so the adversary can carry its view of the earlier phases. Only the hash cache starts from
the prefix. The cache of the hidden streams stays empty.

## The reduction

`withPrefix A pre` runs `pre` and then `A.start`. Both executions run the adversary start first
(`realExecution`, `Statement.lean:228`, and `treeSimulator.start`, `Reductions.lean:130`). So the
games of `withPrefix A pre` are the games of `A` after `pre`.

* `streamWorld_treeRealGame_withPrefix` is this fact for the real side. It uses
  `treeSim_stream_adversary` (`TreeSim.lean:903`).
* `world_treeIdealGame_withPrefix` is this fact for the ideal side. `treeSimulator` adds the calls of
  `pre` to its log. The log is never read (`Reductions.lean:133-150`), so `treeSimImpl_run_view`
  removes it.
* `treeSimulationHopFrom_of_hop` applies `TreeSimulationHop` to `withPrefix A pre` with the budget
  `q0 + q` (`isQueryBounded_withPrefix`).

The error is the error of `TreeSimulationHop` at `q0 + q`. Its hash term
`treeHashError (q0 + q)` is the D6 birthday term over `q0 + q + treeSecrets`. The check term
`treeCheckError (q0 + q)` also grows. A prefix can query `.coinKey` points and give the answers to the
adversary, and `checkErrorOf` charges such a hit at `1 / |E|` (`Statement.lean:365`). The split term
is `split (q0 + q)`. `treeSimulationHop_of_from` shows that `q0 = 0` gives `TreeSimulationHop`.

## Audit of the premises of `treeSimulationHop_of_events2` (`TreeEvents.lean:325`)

No premise quantifies over the start cache. Each one starts from the literal empty cache.

* `TreeSimStagesGoal2` (`TreeEvents.lean:110`) unfolds to `TreeSimStages` (`TreeSim.lean:10018`). Its
  round stages start from each state in the support of `treeSimCommonPrefix` (`TreeSim.lean:1892`).
  That prefix runs the dealer from `∅` (`TreeSim.lean:1897`).
* `TreeSimHashHonestBudget` (`TreeSimHashFinish.lean:238`) runs `treeSimHashProgram` from `∅`
  (`TreeSimHashFinish.lean:245`).
* `TreeSimHashRawSaltEstimate` (`TreeSimHash.lean:5283`), `TreeSimSaltReuseEstimate`
  (`TreeEvents.lean:207`) and `TreeSimCheckBoundGoal` (`TreeSim.lean:10448`) read
  `treeSimLoggedRun`, which runs from `(∅, ∅)` (`TreeSim.lean:1484`).

A literal from-cache form of each premise needs the D6 hypothesis on the cache. An arbitrary cache
breaks the check and the hash events. For example, a cache that already holds the `.coinKey` points
of a batch fixes its challenges before the coin opens. The reduction above avoids these forms. Every
premise quantifies over all adversaries, auxiliary inputs and budgets, so `withPrefix A pre` at
`q0 + q` is an instance of the premises as they are. So `treeSimulationHopFrom_of_events2` uses the
same named premises.

The calls of `pre` enter the log as counted calls `.inl (.inl _)`. The events of `treeSimEvents2`
change as follows.

* `TreeSimHashCollision` (`TreeSim.lean:1531`) needs two different queries. Some points repeat in every
  batch and every run, such as `.copy` of zeros (`Scheme.lean:540`), `.history []` of an unfilled term
  (`Scheme.lean:577-579`) and points that the adversary chooses. A repeated point is one query and
  makes no collision. The prefix adds at most `q0` points of the collision domain. The bound
  `(q0 + q + treeSecrets - 2 * prssKeyCount)² / 2^256` counts them.
* `TreeSimSaltGuess` (`TreeSim.lean:1544`) fires when a counted `.digest` query uses a hidden salt. An
  earlier salt in the cache is such a query. `TreeSimHashRawSaltEstimate` at `q0 + q` charges it.
* `TreeSimSaltReuse` (`TreeEvents.lean:47`) reads only free-copy stream draws. The prefix makes none,
  so this event does not grow.
* `TreeSimWrongOutput` (`TreeSim.lean:1572`) is a wrong honest output. A prefix that knows the
  `.coinKey` answers of a batch makes it more likely. `TreeSimCheckBoundGoal` at `q0 + q` bounds it.
* `TreeSimHashHonestBudget` counts only free-copy queries. The prefix adds none.

## Limits

* The prefix cannot program `H`. A lifetime must first replace the programmed keygen points by sampled
  ones.
* `top`, `tree` and `x` are fixed before the prefix.
* The hidden-key hop `TreeKeyHop` needs the same from-cache form at `q0 + q` for the two hops to
  compose as in `treeSecurityDistance_of_hops` (`Tree.lean:4472`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The earlier phases under the lazy random oracle of `H`, from the empty cache. The result is
their output and the cache that they leave. -/
def prefixRun (pre : OracleComp (LocalSpec C) Aux) : ProbComp (Aux × HashCache C) :=
  (simulateQ (localAnswer prims) pre).run ∅

/-- `TreeSimulationHop` from the cache of a prefix with at most `q0` counted calls (D6). The
output of the prefix is the auxiliary input. Only the hash cache of `streamWorld` starts from the
cache of the prefix. The error is the error of `TreeSimulationHop` at `q0 + q`, so the hash term is
the birthday bound over `q0 + q + treeSecrets`. -/
def TreeSimulationHopFrom (split : ℕ → ℝ) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (pre : OracleComp (LocalSpec C) Aux) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ),
    DealtInputs D x → IsQueryBoundP pre Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |(Pr[= true | prefixRun prims pre >>= fun p =>
        (simulateQ (streamWorld prims D) (treeRealGame K circuits settings top tree D A x p.1 Z)).run'
          (p.2, ∅)]).toReal -
      (Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeIdealGame K circuits settings top tree D A x p.1 Z)).run.run'
          p.2]).toReal| ≤
      treeCheckError (E := E) circuits settings tree (q0 + q) +
        (treeHashError circuits settings C tree (q0 + q) - split (q0 + q))

/-- The adversary that runs the prefix before its start. -/
abbrev withPrefix {I L R : Type} (A : Adversary C E I L R) (pre : OracleComp (LocalSpec C) Aux) :
    Adversary C E I L R :=
  { A with start := fun corrupt _ => pre >>= A.start corrupt }

theorem stepRound_withPrefix {m : Type → Type} [Monad m] {I O L R α Ia : Type} (Ro : Roles C m)
    (D : C.Coalition) (A : Adversary C E Ia L R) (pre : OracleComp (LocalSpec C) Aux)
    (F : Functionality C I O L R) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    stepRound Ro D (withPrefix A pre) F state steps = stepRound Ro D A F state steps := by
  unfold stepRound runFunctionality
  rfl

theorem executeRounds_withPrefix {m : Type → Type} [Monad m] {I O L R α Ia : Type} (Ro : Roles C m)
    (D : C.Coalition) (A : Adversary C E Ia L R) (pre : OracleComp (LocalSpec C) Aux)
    (F : Functionality C I O L R) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    executeRounds Ro D (withPrefix A pre) F fuel state steps = executeRounds Ro D A F fuel state steps := by
  induction fuel generalizing state steps with
  | zero => rfl
  | succ fuel ih =>
    simp only [executeRounds, stepRound_withPrefix, ih]

theorem executePhase_withPrefix {m : Type → Type} [Monad m] {I O L R α Ia : Type} (Ro : Roles C m)
    (D : C.Coalition) (A : Adversary C E Ia L R) (pre : OracleComp (LocalSpec C) Aux)
    (F : Functionality C I O L R) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E (CallSpec I O) α) :
    executePhase Ro D (withPrefix A pre) F fuel state program = executePhase Ro D A F fuel state program := by
  simp only [executePhase, executeRounds_withPrefix]

theorem treeRealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    treeRealGame K circuits settings top tree D (withPrefix A pre) x z Z =
      worldRoles.adversary pre >>= fun w => treeRealGame K circuits settings top tree D A x w Z := by
  unfold treeRealGame distinguish realExecution
  simp only [executePhase_withPrefix]
  simp only [worldRoles, liftComp_bind, counted_bind, bind_assoc]

/-- The real side of the absorbed adversary is the real side from the cache of the prefix. -/
theorem streamWorld_treeRealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    (simulateQ (streamWorld prims D) (treeRealGame K circuits settings top tree D (withPrefix A pre) x z Z)).run'
        (∅, ∅) =
      prefixRun prims pre >>= fun p =>
        (simulateQ (streamWorld prims D) (treeRealGame K circuits settings top tree D A x p.1 Z)).run' (p.2, ∅) := by
  rw [treeRealGame_withPrefix, simulateQ_bind, treeSim_stream_adversary]
  simp only [StateT.run'_eq, StateT.run_bind, onHash, StateT.run_mk, prefixRun, map_bind, bind_map_left]

/-- The state of `treeSimulator` without its log. -/
def treeSimView {σ : Type} (st : SimulatorState C (Keys C) σ) : σ × (C.Party → Option (Keys C)) :=
  (st.adversary, st.corrupt)

/-- The oracles of `F_tree` in `idealExecution` with `treeSimulator`. -/
def treeSimImpl (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) :
    QueryImpl (LocalSpec C + ((PublicParameter × List (List (List Bit))) →ₒ Finset C.Party))
      (StateT (SimulatorState C (Keys C) A.State) (OracleComp (WorldSpec C))) :=
  (fun (t : (LocalSpec C).Domain) =>
    (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) : StateT _ _ _)) +
  (fun l => (StateT.mk fun st => do
    let (st, r) ← (treeSimulator K circuits settings top tree D A).answer st l
    pure (r, st) : StateT _ (OracleComp (WorldSpec C)) _))

/-- `treeSimImpl` on the state without the log, which starts each step from the empty log. -/
def treeSimViewImpl (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) :
    QueryImpl (LocalSpec C + ((PublicParameter × List (List (List Bit))) →ₒ Finset C.Party))
      (StateT (A.State × (C.Party → Option (Keys C))) (OracleComp (WorldSpec C))) := fun t =>
  StateT.mk fun p => Prod.map id treeSimView <$>
    (treeSimImpl K circuits settings top tree D A t).run ⟨p.1, [], p.2⟩

/-- The answer of `treeSimulator` does not read the log. -/
theorem treeSimulator_answer_view (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (st : SimulatorState C (Keys C) A.State)
    (l : PublicParameter × List (List (List Bit))) :
    Prod.map treeSimView id <$> (treeSimulator K circuits settings top tree D A).answer st l =
      Prod.map treeSimView id <$> (treeSimulator K circuits settings top tree D A).answer
        ⟨st.adversary, [], st.corrupt⟩ l := by
  simp only [treeSimulator, map_bind, map_pure, Prod.map, treeSimView]

/-- The run of `F_tree` with `treeSimulator` depends only on the state without the log. -/
theorem treeSimImpl_run_view (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) {α : Type}
    (oa : OracleComp (LocalSpec C + ((PublicParameter × List (List (List Bit))) →ₒ Finset C.Party)) α)
    (st : SimulatorState C (Keys C) A.State) :
    Prod.map id treeSimView <$> (simulateQ (treeSimImpl K circuits settings top tree D A) oa).run st =
      (simulateQ (treeSimViewImpl K circuits settings top tree D A) oa).run (treeSimView st) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro t s
  simp only [treeSimViewImpl, StateT.run_mk]
  rcases t with t | l
  · change Prod.map id treeSimView <$>
        (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) :
          StateT (SimulatorState C (Keys C) A.State) (OracleComp (WorldSpec C)) _).run s =
      Prod.map id treeSimView <$>
        (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) :
          StateT (SimulatorState C (Keys C) A.State) (OracleComp (WorldSpec C)) _).run ⟨s.adversary, [], s.corrupt⟩
    simp [StateT.run_lift, treeSimView]
  · change Prod.map id treeSimView <$> ((treeSimulator K circuits settings top tree D A).answer s l >>=
        fun r => pure (r.2, r.1)) =
      Prod.map id treeSimView <$> ((treeSimulator K circuits settings top tree D A).answer
        ⟨s.adversary, [], s.corrupt⟩ l >>= fun r => pure (r.2, r.1))
    have h := congrArg (fun p => (fun r => (r.2, r.1)) <$> p)
      (treeSimulator_answer_view K circuits settings top tree D A s l)
    simp only [Functor.map_map, bind_pure_comp, Prod.map_fst, Prod.map_snd, Prod.map_apply, id] at h ⊢
    exact h

/-- The run of `F_tree` with `treeSimulator` from the state without the log, with the output of
`idealExecution`. -/
def treeSimViewRun (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (p : A.State × (C.Party → Option (Keys C))) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option TreeOutput)) :=
  (fun r => (r.2.1, r.1)) <$> (simulateQ (treeSimViewImpl K circuits settings top tree D A)
    ((Ftree circuits settings top tree).run D fun i => if i ∈ D.1 then none else some (x i))).run p

/-- The ideal execution with `treeSimulator` is the start of `A`, then the run without the log. -/
theorem idealExecution_treeSimulator (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    idealExecution (fun oa => oa) D (Ftree circuits settings top tree)
        (treeSimulator K circuits settings top tree D A) x z =
      worldRoles.adversary (A.start (corruptInputs D x) z) >>= fun a =>
        treeSimViewRun K circuits settings top tree D A x (a, corruptInputs D x) := by
  change (observe (A.start (corruptInputs D x) z) >>= fun r =>
      pure (⟨r.1, r.2, corruptInputs D x⟩ : SimulatorState C (Keys C) A.State)) >>= (fun st =>
      (simulateQ (treeSimImpl K circuits settings top tree D A)
        ((Ftree circuits settings top tree).run D fun i => if i ∈ D.1 then none else some (x i))).run st >>=
          fun d => pure (d.2.adversary, d.1)) = _
  rw [← fst_observe, bind_map_left, bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind, treeSimViewRun, show (r.1, corruptInputs D x) =
      treeSimView (⟨r.1, r.2, corruptInputs D x⟩ : SimulatorState C (Keys C) A.State) from rfl,
    ← treeSimImpl_run_view, Functor.map_map, bind_pure_comp]
  rfl

theorem treeSimulator_answer_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (pre : OracleComp (LocalSpec C) Aux) :
    (treeSimulator K circuits settings top tree D (withPrefix A pre)).answer =
      (treeSimulator K circuits settings top tree D A).answer := by
  unfold treeSimulator
  simp only [executePhase_withPrefix]

theorem treeSimViewRun_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (pre : OracleComp (LocalSpec C) Aux) (x : C.Party → Keys C) :
    treeSimViewRun K circuits settings top tree D (withPrefix A pre) x =
      treeSimViewRun K circuits settings top tree D A x := by
  unfold treeSimViewRun treeSimViewImpl treeSimImpl
  rw [treeSimulator_answer_withPrefix]
  rfl

theorem treeIdealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    treeIdealGame K circuits settings top tree D (withPrefix A pre) x z Z =
      worldRoles.adversary pre >>= fun w => treeIdealGame K circuits settings top tree D A x w Z := by
  unfold treeIdealGame distinguish
  simp only [idealExecution_treeSimulator, treeSimViewRun_withPrefix]
  simp only [worldRoles, liftComp_bind, counted_bind, bind_assoc]

/-- The ideal side of the absorbed adversary is the ideal side from the cache of the prefix. -/
theorem world_treeIdealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    (fun r => r.1) <$> (simulateQ (world prims)
        (treeIdealGame K circuits settings top tree D (withPrefix A pre) x z Z)).run.run' ∅ =
      prefixRun prims pre >>= fun p => (fun r => r.1) <$>
        (simulateQ (world prims) (treeIdealGame K circuits settings top tree D A x p.1 Z)).run.run' p.2 := by
  simp only [world, fst_map_run_withAddCost]
  rw [treeIdealGame_withPrefix, simulateQ_bind]
  simp only [worldRoles, simulateQ_counted, TprfSecurityProof.simulateQ_liftComp_local]
  simp only [StateT.run'_eq, StateT.run_bind, map_bind, prefixRun]

/-- The absorbed adversary makes at most `q0 + q` counted calls. -/
theorem isQueryBounded_withPrefix {I L R O : Type} (A : Adversary C E I L R) (Z : Distinguisher C A.State O)
    (pre : OracleComp (LocalSpec C) Aux) (fuel q0 q : ℕ) (hpre : IsQueryBoundP pre Counted q0)
    (hq : IsQueryBounded A Z fuel q) : IsQueryBounded (withPrefix A pre) Z fuel (q0 + q) := by
  obtain ⟨start, step, final, hle, hstart, hround, hanswer, hfinal⟩ := hq
  exact ⟨q0 + start, step, final, by omega,
    fun corrupt _ => isQueryBoundP_bind hpre fun w _ => hstart corrupt w, hround, hanswer, hfinal⟩

/-- The hop from the cache of a prefix follows from the hop from the empty cache at `q0 + q`. The
adversary runs the prefix first. -/
theorem treeSimulationHopFrom_of_hop (split : ℕ → ℝ)
    (hop : TreeSimulationHop prims K circuits settings split) :
    TreeSimulationHopFrom prims K circuits settings split := by
  intro hb top tree D A x pre Z q0 q hx hpre hq
  have h := hop hb top tree D (withPrefix A pre) x [] Z (q0 + q) hx
    (isQueryBounded_withPrefix A Z pre _ q0 q hpre hq)
  rw [streamWorld_treeRealGame_withPrefix] at h
  have hideal : Pr[fun r => r.1 = true | runWorld prims
      (treeIdealGame K circuits settings top tree D (withPrefix A pre) x [] Z)] =
      Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeIdealGame K circuits settings top tree D A x p.1 Z)).run.run' p.2] := by
    have hmap := congrArg (fun m => Pr[(· = true) | m])
      (world_treeIdealGame_withPrefix prims K circuits settings top tree D A x pre [] Z)
    simp only [← map_bind, probEvent_map] at hmap
    exact hmap
  unfold accepts at h
  rw [hideal] at h
  exact h

/-- The hop from the cache of a prefix with `q0 = 0` is the hop from the empty cache. -/
theorem treeSimulationHop_of_from (split : ℕ → ℝ)
    (hop : TreeSimulationHopFrom prims K circuits settings split) :
    TreeSimulationHop prims K circuits settings split := by
  intro hb top tree D A x z Z q hx hq
  have h := hop hb top tree D A x (pure z) Z 0 q hx (isQueryBoundP_pure _ z 0) hq
  simp only [prefixRun, simulateQ_pure, StateT.run_pure, pure_bind, zero_add] at h
  exact h

/-- The hop from the cache of a prefix from the premises of `treeSimulationHop_of_events2`. -/
theorem treeSimulationHopFrom_of_events2
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseEstimate prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHopFrom prims K circuits settings (keySplit C) :=
  treeSimulationHopFrom_of_hop prims K circuits settings (keySplit C)
    (treeSimulationHop_of_events2 prims K circuits settings stages honest salt reuse checkBound)

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHopFrom_of_hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHopFrom_of_hop

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_from

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHopFrom_of_events2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHopFrom_of_events2

end ThresholdLeanXmssSecurity
