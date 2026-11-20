import Sketch.Completeness
import ThresholdLeanXmssSecurity.Proof.Dealer

/-!
# The runs of a tree in the game as local runs

The honest runs of a tree in the game, with no corrupt operator and the honest adversary, are a local
computation on the free copy. `localRuns` is that computation, and `treeRuns_run` is the link.

`firstRun_coupling` is the step of the hops for each tree. The first real run of a tree, followed by
any continuation that reads the cache, is at distance `treeAbortError tree` from the dealer of the
tree followed by the same continuation on the output of the dealer.

The other lemmas link the games to local runs from the empty cache (`honestDkg_eq`,
`topDealtDkg_eq`, `fst_runWorld_free`), join a bound over the outcomes of the seed generation
(`tvDist_bind_le_of_support`, `seedGen_dealt`), and replace the dealer of a tree by `referenceTree`
jointly with the cache (`dealer_continuation`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The honest phase -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One phase with no corrupt operator and the honest adversary is the honest network on the free
copy. -/
theorem executePhase_honest {I O L R Ia α : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (state : (honestAdversary (C := C) (E := E) (I := Ia) reply).State)
    (program : C.Party → PartyM C E (CallSpec I O) α) :
    executePhase worldRoles noCoalition (honestAdversary (I := Ia) reply) F fuel state program =
      (fun o => (state, o)) <$> free (honestStart program >>= honestRounds F reply fuel) := by
  unfold executePhase
  rw [startSteps_honest]
  simp only [free_bind, map_bind]
  exact bind_congr fun steps => executeRounds_honest F reply state fuel steps

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `executePhase_honest` for `honestNet` on the real network. -/
theorem executePhase_honestNet {α : Type} (fuel : ℕ) (state : (honestNet (C := C) (E := E)).State)
    (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles noCoalition honestNet noFunctionality fuel state program =
      (fun o => (state, o)) <$> free (honestStart program >>= honestRounds noFunctionality (fun l => l.elim) fuel) :=
  executePhase_honest _ _ _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `realExecution_honest` for the seed generation with `honestNet`. -/
theorem realExecution_honestNet :
    realExecution noCoalition honestNet noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [] =
      (fun o => ((), o)) <$> free (honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds) :=
  realExecution_honest _ _ _ _ _

/-! ## The local runs of a tree -/

/-- The state of the game in an honest run. -/
abbrev HonestState (C : Committee) (E : Type) := RealState C (honestNet (C := C) (E := E)).State

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- One honest run of `tree` with the operators `operators`, as a local computation. -/
def localTreeRun (operators : C.Party → OperatorState C) (tree : Tree) :
    OracleComp (LocalSpec C) (C.Party → Option TreeOutput) :=
  honestStart (fun i => treeProgram K circuits settings i (operators i) tree) >>=
    honestRounds noFunctionality (fun l => l.elim) (treeFuel circuits settings)

/-- The state after a run of `tree` with `outputs` and no monitor. Each operator keeps its first
output. -/
def afterRun {σ : Type} (s : RealState C σ) (outputs : C.Party → Option TreeOutput) (tree : Tree) : RealState C σ :=
  ⟨s.adversary, fun i => (s.operators i).keep (outputs i) tree, Function.update s.runs tree (s.runs tree + 1),
    s.closed, s.flag || false⟩

/-- At most `count` honest runs of `tree`, as a local computation. -/
def localRuns (tree : Tree) : ℕ → HonestState C E → OracleComp (LocalSpec C) (HonestState C E)
  | 0, s => pure s
  | count + 1, s =>
    if mayRun runLimit noCoalition s tree then
      localTreeRun K circuits settings s.operators tree >>= fun outputs =>
        localRuns tree count (afterRun s outputs tree)
    else pure s

omit [Fintype E] [DecidableEq E] in
/-- The honest runs of a tree in the game are the local runs on the free copy. -/
theorem treeRuns_run (tree : Tree) : ∀ (count : ℕ) (s : HonestState C E),
    (treeRuns K circuits settings runLimit noMonitor noCoalition honestNet tree count).run s =
      (fun s' => ((), s')) <$> free (localRuns K circuits settings runLimit tree count s)
  | 0, s => by simp [treeRuns, localRuns]
  | count + 1, s => by
    simp only [treeRuns, localRuns, treeRun, noMonitor, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with h
    · rw [StateT.run_bind, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_lift,
        executePhase_honestNet]
      simp only [localTreeRun, afterRun, free_bind, map_bind, bind_map_left, bind_assoc, StateT.run_bind,
        StateT.run_lift, pure_bind, StateT.run_set, treeRuns_run tree count, Bool.or_false]
    · simp

/-! ## The first run of a tree with a continuation -/

/-- The dealer of a tree, then the real run of the tree, from a start cache. The real output differs
from the dealer output with probability at most `treeAbortError tree`. It is the bound inside the
proof of `treeRunFrom`. -/
theorem jointTree_bound_from (prims : Primitives) (hsize : 0 < settings.batchSize) (top : TopTree) (tree : Tree)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (s : HashCache C) (hs : StartInvariant s) :
    (Pr{let p ← (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree >>=
        fun a => realTree K circuits settings top tree parameter seeds pairKeys >>= fun z => pure (z, a))).run' s}[
          p.1 ≠ p.2]).toReal ≤ treeAbortError (E := E) circuits settings tree := by
  let : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩⟩
  have hbound : Pr{let p ← (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree >>=
      fun a => realTree K circuits settings top tree parameter seeds pairKeys >>= fun z => pure (z, a))).run' s}[p.1 ≠ p.2] ≤
      chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
    rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
    obtain ⟨hn, hc, o₀, heq, ho⟩ := idealTree_value_from circuits settings prims parameter seeds top tree hsize s hs z hz
    have hreal := realTree_bound prims K circuits settings parameter seeds pairKeys top tree o₀ z.2 hn hc ho hsize
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure, heq]
    rw [bind_pure_comp]
    simpa only [StateT.run'_eq, prEvent_map, Function.comp_def] using hreal
  have hreal := ENNReal.toReal_mono (chunksBudget_ne_top (E := E)
    (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0) hbound
  rwa [chunksBudget_toReal circuits settings tree] at hreal

/-- The first real run of `tree` from a start cache, followed by a continuation `f` that may read the
cache, is at distance `treeAbortError tree` from the dealer of the tree followed by `f`. The proof
puts the dealer first, charges the event that the real output differs from the dealer output, and
then removes the real run, whose result nothing reads. -/
theorem firstRun_coupling (prims : Primitives) (hsize : 0 < settings.batchSize) (top : TopTree) (tree : Tree)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (s : HashCache C) (hs : StartInvariant s) {α : Type}
    (f : (C.Party → Option TreeOutput) → OracleComp (LocalSpec C) α) :
    letI : MeasurableSpace α := ⊤
    measureTVDist
        ((simulateQ (localAnswer prims) (realTree K circuits settings top tree parameter seeds pairKeys >>= f)).run' s)
        ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree >>= f)).run' s) ≤
      treeAbortError (E := E) circuits settings tree := by
  let : MeasurableSpace α := ⊤
  set I := idealTree circuits settings parameter seeds top tree
  set R := realTree K circuits settings top tree parameter seeds pairKeys
  set J := I >>= fun a => R >>= fun z => pure (z, a)
  have hL : (simulateQ (localAnswer prims) (R >>= f)).run' s =ᵈ
      ((simulateQ (localAnswer prims) J).run s >>= fun q => (simulateQ (localAnswer prims) (f q.1.1)).run' q.2) := by
    refine (evalDist_run'_prepend prims I (R >>= f) s).symm.trans ?_
    simp only [J, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, bind_assoc, StateT.run_pure,
      pure_bind, map_bind]
    exact .rfl
  have hR : (simulateQ (localAnswer prims) (I >>= f)).run' s =ᵈ
      ((simulateQ (localAnswer prims) J).run s >>= fun q => (simulateQ (localAnswer prims) (f q.1.2)).run' q.2) := by
    have hdrop := evalDist_run'_bind_congr prims I f (fun a => R >>= fun _ => f a) s
      fun p _ => (evalDist_run'_prepend prims R (f p.1) p.2).symm
    refine hdrop.trans ?_
    simp only [J, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, bind_assoc, StateT.run_pure,
      pure_bind, map_bind]
    exact .rfl
  have hbad := measureTVDist_bind_left_le_prEvent_of_evalDistEq ((simulateQ (localAnswer prims) J).run s)
    (fun q => (simulateQ (localAnswer prims) (f q.1.1)).run' q.2)
    (fun q => (simulateQ (localAnswer prims) (f q.1.2)).run' q.2) (fun q => q.1.1 ≠ q.1.2)
    fun q hq => by rw [not_not] at hq; rw [hq]
  have hevent : Pr{let q ← (simulateQ (localAnswer prims) J).run s}[q.1.1 ≠ q.1.2] =
      Pr{let p ← (simulateQ (localAnswer prims) J).run' s}[p.1 ≠ p.2] := by
    rw [StateT.run'_eq, prEvent_map]
  calc measureTVDist ((simulateQ (localAnswer prims) (R >>= f)).run' s)
        ((simulateQ (localAnswer prims) (I >>= f)).run' s)
      = measureTVDist ((simulateQ (localAnswer prims) J).run s >>= fun q =>
          (simulateQ (localAnswer prims) (f q.1.1)).run' q.2)
        ((simulateQ (localAnswer prims) J).run s >>= fun q =>
          (simulateQ (localAnswer prims) (f q.1.2)).run' q.2) := by
        unfold measureTVDist; rw [hL.evalDist_eq, hR.evalDist_eq]
    _ ≤ _ := hbad
    _ ≤ _ := by
        rw [hevent]
        exact jointTree_bound_from K circuits settings prims hsize top tree parameter seeds pairKeys s hs

/-! ## The game as a local computation -/

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The output of a computation on the free copy in the world is its local run from the empty
cache. -/
theorem fst_runWorld_free (prims : Primitives) {α : Type} (X : OracleComp (LocalSpec C) α) :
    Prod.fst <$> runWorld prims (free X) = (simulateQ (localAnswer prims) X).run' ∅ := by
  have h := fst_map_runWorld prims (free X)
  rw [simulateQ_free] at h
  exact h

/-- A bound on the continuations at each reachable outcome bounds the distance after the prefix. -/
theorem measureTVDist_bind_left_le_of_support {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.AnswerMeasure spec] [∀ t, Finite (spec.Range t)] {α β : Type} [MeasurableSpace β]
    (oa : OracleComp spec α) (f g : α → OracleComp spec β) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ a ∈ support oa, measureTVDist (f a) (g a) ≤ δ) :
    measureTVDist (oa >>= f) (oa >>= g) ≤ δ := by
  rw [bind_eq_attach_bind oa f, bind_eq_attach_bind oa g]
  exact measureTVDist_bind_left_le_of_forall_le _ _ _ hδ fun a => h a.1 a.2

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Two local continuations of one prefix, at distance at most `δ` from each reachable outcome and
cache of the prefix, give runs at distance at most `δ`. -/
theorem tvDist_bind_le_of_support (prims : Primitives) {α β : Type} (m : OracleComp (LocalSpec C) β)
    (f g : β → OracleComp (LocalSpec C) α) (s : HashCache C) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ p ∈ support ((simulateQ (localAnswer prims) m).run s),
      letI : MeasurableSpace α := ⊤
      measureTVDist ((simulateQ (localAnswer prims) (f p.1)).run' p.2)
        ((simulateQ (localAnswer prims) (g p.1)).run' p.2) ≤ δ) :
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ (localAnswer prims) (m >>= f)).run' s)
      ((simulateQ (localAnswer prims) (m >>= g)).run' s) ≤ δ := by
  let : MeasurableSpace α := ⊤
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact measureTVDist_bind_left_le_of_support _ _ _ hδ fun p hp => by simpa [StateT.run'_eq] using h p hp

omit [Fintype E] [DecidableEq E] in
/-- The operators after the runs of `tree` depend only on the operators, the closed trees and the
runs of `tree` at the start. -/
theorem localRuns_operators_congr (tree : Tree) : ∀ (count : ℕ) (s₁ s₂ : HonestState C E),
    s₁.operators = s₂.operators → s₁.closed = s₂.closed → s₁.runs tree = s₂.runs tree →
    RealState.operators <$> localRuns K circuits settings runLimit tree count s₁ =
      RealState.operators <$> localRuns K circuits settings runLimit tree count s₂
  | 0, s₁, s₂, ho, _, _ => by simp [localRuns, ho]
  | count + 1, s₁, s₂, ho, hc, hr => by
    have hmay : mayRun runLimit noCoalition s₁ tree ↔ mayRun runLimit noCoalition s₂ tree := by
      cases tree <;> simp [mayRun, ho, hc, hr]
    simp only [localRuns]
    by_cases h : mayRun runLimit noCoalition s₁ tree
    · simp only [h, hmay.1 h, ↓reduceIte, map_bind]
      rw [ho]
      refine bind_congr fun outputs => localRuns_operators_congr tree count _ _ ?_ ?_ ?_
      · simp [afterRun, ho]
      · simp [afterRun, hc]
      · simp [afterRun, hr]
    · simp [h, mt hmay.2 h, ho]

/-- The honest seed generation as a local computation. -/
def seedGenLocal : OracleComp (LocalSpec C) (C.Party → Option (Keys C)) :=
  honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
    honestRounds noFunctionality (fun l => l.elim) setupRounds

/-- The outputs of the operators in a state, with bottom tree `b`. -/
def outputsOf (b : Fin (2 ^ layerHeight)) (s : HonestState C E) : SetupOutputs C :=
  fun i => ((s.operators i).keys, (s.operators i).top, (s.operators i).bottom b)

/-- `honestDkg b` as a local computation. -/
def honestLocal (b : Fin (2 ^ layerHeight)) : OracleComp (LocalSpec C) (SetupOutputs C) :=
  seedGenLocal (E := E) >>= fun keys =>
    localRuns K circuits settings runLimit .top runLimit (startState noCoalition () keys) >>= fun s =>
      localRuns K circuits settings runLimit (.bottom b) runLimit s >>= fun s => pure (outputsOf b s)

omit [Fintype E] [DecidableEq E] in
/-- `honestDkg b` is `honestLocal b` on the free copy. -/
theorem honestDkg_eq (b : Fin (2 ^ layerHeight)) :
    honestDkg K circuits settings runLimit b = free (honestLocal K circuits settings runLimit b) := by
  unfold honestDkg honestLocal seedGenLocal
  rw [realExecution_honestNet]
  simp only [treeRuns_run, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    free_bind, free_pure]
  exact (bind_assoc _ _ _).trans (bind_congr fun x => (bind_assoc _ _ _).trans
    (bind_congr fun y => by simp only [Function.comp_apply]; rfl))

/-- `dealtTop` as a local computation. -/
def dealtTopLocal (keys : C.Party → Option (Keys C)) : OracleComp (LocalSpec C) (Option TopTree) :=
  if ∀ i, (keys i).isSome then
    liftComp (TreeOutput.topTree <$> referenceTree (fun oa => tweakable oa)
      (prfValue (gameSeeds noCoalition keys)) (gameParameter noCoalition keys) emptyTop .top) _
  else pure none

/-- The state after the seed generation with the outputs `keys`, where each operator holds the top
tree `top`. -/
def withTop (keys : C.Party → Option (Keys C)) (top : Option TopTree) : HonestState C E :=
  let start : HonestState C E := startState noCoalition () keys
  { start with operators := fun i => { start.operators i with top := top } }

/-- `topDealtDkg b` as a local computation. -/
def topDealtLocal (b : Fin (2 ^ layerHeight)) : OracleComp (LocalSpec C) (SetupOutputs C) :=
  seedGenLocal (E := E) >>= fun keys => dealtTopLocal keys >>= fun top =>
    localRuns K circuits settings runLimit (.bottom b) runLimit (withTop keys top) >>= fun s => pure (outputsOf b s)

omit [Fintype E] [DecidableEq E] in
/-- `dealtTop` is `dealtTopLocal` on the free copy. -/
theorem dealtTop_eq (keys : C.Party → Option (Keys C)) : dealtTop keys = free (dealtTopLocal keys) := by
  unfold dealtTop dealtTopLocal
  split_ifs <;> simp

omit [Fintype E] [DecidableEq E] in
/-- `topDealtDkg b` is `topDealtLocal b` on the free copy. -/
theorem topDealtDkg_eq (b : Fin (2 ^ layerHeight)) :
    topDealtDkg K circuits settings runLimit b = free (topDealtLocal K circuits settings runLimit b) := by
  unfold topDealtDkg topDealtLocal seedGenLocal
  rw [realExecution_honestNet]
  simp only [treeRuns_run, dealtTop_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, free_bind, free_pure]
  exact (bind_assoc _ _ _).trans (bind_congr fun x => (bind_assoc _ _ _).trans
    (bind_congr fun y => by simp only [Function.comp_apply]; rfl))

/-! ## Dealt keys -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- On dealt keys, the seeds of the game are the dealt seeds. -/
theorem gameSeeds_dealt (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) :
    gameSeeds noCoalition (fun i => some (dealtKeys parameter seeds pairKeys i)) = seeds := by
  funext T
  unfold gameSeeds
  split
  · rename_i i hi
    have h := List.find?_some hi
    simp only [decide_eq_true_eq] at h
    simp [dealtKeys, h.1]
  · rename_i hnone
    obtain ⟨j, hj⟩ := exists_holder T
    rw [List.find?_eq_none] at hnone
    exact absurd (hnone j (by simp [Committee.parties])) (by simp [hj, noCoalition])

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- On dealt keys, the parameter of the game is the dealt parameter. -/
theorem gameParameter_dealt (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) :
    gameParameter noCoalition (fun i => some (dealtKeys parameter seeds pairKeys i)) = parameter := by
  unfold gameParameter
  split
  · simp [dealtKeys]
  · rename_i hnone
    rw [List.find?_eq_none] at hnone
    have j : C.Party := ⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩
    exact absurd (hnone j (by simp [Committee.parties])) (by simp [noCoalition])

omit [Fintype E] [DecidableEq E] in
/-- With no allowed run, the runs of a tree change nothing. -/
theorem localRuns_of_not_mayRun (tree : Tree) (s : HonestState C E) (h : ¬ mayRun runLimit noCoalition s tree) :
    ∀ count, localRuns K circuits settings runLimit tree count s = pure s
  | 0 => rfl
  | count + 1 => by simp [localRuns, h]

omit [Fintype E] [DecidableEq E] in
/-- The outputs after the runs of `tree` depend only on the operators, the closed trees and the runs
of `tree` at the start. -/
theorem localRuns_outputs_congr (tree : Tree) (b : Fin (2 ^ layerHeight)) (count : ℕ) (s₁ s₂ : HonestState C E)
    (ho : s₁.operators = s₂.operators) (hc : s₁.closed = s₂.closed) (hr : s₁.runs tree = s₂.runs tree) :
    (localRuns K circuits settings runLimit tree count s₁ >>= fun st => pure (outputsOf b st)) =
      localRuns K circuits settings runLimit tree count s₂ >>= fun st => pure (outputsOf b st) := by
  have h := congrArg (fun x => (fun (ops : C.Party → OperatorState C) i => ((ops i).keys, (ops i).top, (ops i).bottom b)) <$> x)
    (localRuns_operators_congr K circuits settings runLimit tree count s₁ s₂ ho hc hr)
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at h
  exact h

/-! ## The dealer of a tree with a continuation -/

/-- A run of a computation of `H` and `PRG` and then a local continuation. -/
theorem run'_liftComp_bind (prims : Primitives) {α β : Type} (X : OracleComp (RoSpec C) β)
    (k : β → OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp X (LocalSpec C) >>= k)).run' s =
      roRun prims X s >>= fun p => (simulateQ (localAnswer prims) (k p.1)).run' p.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, localRun_liftComp, map_bind]
  rfl

/-- When the circuits compute `Th`, the dealer of a tree followed by a continuation runs as
`referenceTree` followed by the same continuation, from each cache. -/
theorem dealer_continuation (prims : Primitives) (hc : CircuitsCompute circuits prims.Th)
    (hsize : 0 < settings.batchSize) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (tree : Tree) {α : Type} (k : Option TreeOutput → OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (localAnswer prims)
        (idealTree circuits settings parameter seeds top tree >>= fun a => k (a (firstParty C)))).run' s =
      (simulateQ (localAnswer prims)
        (liftComp (referenceTree tweakable (prfValue seeds) parameter top tree) (LocalSpec C) >>= k)).run' s := by
  have hI : idealTree circuits settings parameter seeds top tree >>= (fun a => k (a (firstParty C))) =
      liftComp (Prod.fst <$> dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C) >>= k := by
    simp only [idealTree, liftComp_map, bind_map_left]
  rw [hI, run'_liftComp_bind, run'_liftComp_bind, roRun_dealer prims circuits settings hc hsize]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each outcome of the honest seed generation from the empty cache gives each operator the keys
of one dealing. -/
theorem seedGen_dealt (prims : Primitives) (z : (C.Party → Option (Keys C)) × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (seedGenLocal (E := E))).run ∅)) :
    ∃ parameter seeds pairKeys, z.1 = fun i => some (dealtKeys parameter seeds pairKeys i) := by
  rw [seedGenLocal, support_eq_of_evalDistEq (sameRun_seedGen prims ∅)] at hz
  obtain ⟨-, hn, hsupp⟩ := localRun_support _ ∅ z hz
  obtain ⟨h, hgood, hagree⟩ := exists_good prims z.2 (hn noMpc_empty)
  have hh := hsupp h hgood hagree
  simp only [simulateQ_bind, support_bind, Set.mem_iUnion, simulateQ_fixedLocal_seedGenRest, support_pure,
    Set.mem_singleton_iff] at hh
  obtain ⟨parts, -, hparts⟩ := hh
  exact ⟨truncateHash (h (parameterInput parts)), fun T => h (termInput .seedGen parts T),
    fun p => h (pairInput .seedGen parts p), hparts⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `SeedGenEnd` from the frame of the seed generation. It reduces the premise to the fact that the
seed generation writes no coin key and no expansion. -/
theorem seedGenEnd_of_frame (prims : Primitives) (frame : FrameL prims (seedGenLocal (C := C) (E := E))) :
    SeedGenEnd (C := C) (E := E) prims := fun z hz =>
  ⟨(localRun_support _ ∅ z hz).2.1 noMpc_empty, cacheOK_of_frame cacheOK_empty (frame ∅ z hz)⟩

/-! ## The run of a tree on dealt keys -/

omit [Fintype E] [DecidableEq E] in
/-- A run of the top tree with dealt keys at each operator is `realTree` of the top tree. -/
theorem localTreeRun_top (operators : C.Party → OperatorState C) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (hkeys : ∀ i, (operators i).keys = some (dealtKeys parameter seeds pairKeys i)) :
    localTreeRun K circuits settings operators .top = realTree K circuits settings emptyTop .top parameter seeds pairKeys := by
  unfold localTreeRun realTree treeFuel
  congr 2
  funext i
  simp only [treeProgram, hkeys i]

omit [Fintype E] [DecidableEq E] in
/-- A run of bottom tree `b` with dealt keys and the top tree `top` at each operator is `realTree` of
bottom tree `b`. -/
theorem localTreeRun_bottom (operators : C.Party → OperatorState C) (b : Fin (2 ^ layerHeight)) (top : TopTree)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (hkeys : ∀ i, (operators i).keys = some (dealtKeys parameter seeds pairKeys i))
    (htop : ∀ i, (operators i).top = some top) :
    localTreeRun K circuits settings operators (.bottom b) =
      realTree K circuits settings top (.bottom b) parameter seeds pairKeys := by
  unfold localTreeRun realTree treeFuel
  congr 2
  funext i
  simp only [treeProgram, hkeys i, htop i]

end ThresholdLeanXmss.Sketch
