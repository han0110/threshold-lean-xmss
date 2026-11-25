import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.Hops
import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.VoteHonest

/-!
# The runs of the top tree

The honest runs of a tree in the game, with no corrupt operator and the honest adversary, are a local
computation on the free copy. `localRuns` is that computation, and `treeRuns_run` is the link. Each
local run ends with its vote `localVote`.
`firstRun_coupling` is the step of the hops for each tree. The first real run of a tree, followed by
any continuation that reads the cache, is at distance `treeAbortError tree` from the dealer of the
tree followed by the same continuation on the output of the dealer.

`topRunsHop_of_seedGenEnd` proves `TopRunsHop` from `SeedGenEnd`. The honest seed generation gives
dealt keys and a start cache. All operators vote on one parameter, so the vote of the seed
generation says yes, and its call of `H` changes no later output (`run'_localVote_const`). From
there the first run of the top tree couples with the dealer top tree by `firstRun_coupling`. The
vote of a run is in the continuation of `firstRun_coupling`. The dealer top tree never fails, so
the later runs of the top tree do nothing, and the dealer is `referenceTree` jointly with the cache
by `dealer_continuation`.

`seedGenEnd` proves `SeedGenEnd`. The honest seed generation makes no query of a coin key or of an
expansion, so from the empty cache it ends in a cache with `StartInvariant`. `SafeProg` is the
property of a program of an operator that every local query on every path is no coin query.
`advance_safe` and `honestRounds_safe` carry `StartInvariant` through the honest network for
programs with this property. `topRunsHop` is then `TopRunsHop` with no premise.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCompletenessProof

section Bridge

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

/-- The state after a run of `tree` with the outputs `outputs` after its vote and no monitor. Each
operator keeps its first output. -/
def afterRun {σ : Type} (s : RealState C σ) (outputs : C.Party → Option TreeOutput) (tree : Tree) : RealState C σ :=
  ⟨s.adversary, fun i => (s.operators i).keep (outputs i) tree, Function.update s.runs tree (s.runs tree + 1),
    s.closed, s.flag || split noCoalition outputs⟩

/-- At most `count` honest runs of `tree`, each with its vote, as a local computation. -/
def localRuns (tree : Tree) : ℕ → HonestState C E → OracleComp (LocalSpec C) (HonestState C E)
  | 0, s => pure s
  | count + 1, s =>
    if mayRun runLimit noCoalition s tree then
      localTreeRun K circuits settings s.operators tree >>= fun outputs =>
        localVote (E := E) (fun i => (outputs i).map (treeVote tree)) >>= fun ok =>
          localRuns tree count (afterRun s (committed ok outputs) tree)
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
        StateT.run_lift, pure_bind, StateT.run_set, treeRuns_run tree count, Bool.or_false, voteRound_honestNet]
    · simp

/-! ## The first run of a tree with a continuation -/

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
        exact jointTreeRun_toReal_le prims K circuits settings top tree parameter seeds pairKeys hsize s hs.1 hs.2

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
      refine bind_congr fun outputs => bind_congr fun ok => localRuns_operators_congr tree count _ _ ?_ ?_ ?_
      · simp [afterRun, ho]
      · simp [afterRun, hc]
      · simp [afterRun, hr]
    · simp [h, mt hmay.2 h, ho]

/-- The honest seed generation as a local computation. -/
def seedGenLocal : OracleComp (LocalSpec C) (C.Party → Option (Keys C)) :=
  honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
    honestRounds noFunctionality (fun l => l.elim) setupRounds

/-- The outputs of the operators in a state, with bottom tree `b`. -/
def setupOutputsOf (b : Fin (2 ^ layerHeight)) (s : HonestState C E) : SetupOutputs C :=
  fun i => ((s.operators i).keys, (s.operators i).top, (s.operators i).bottom b)

/-- `honestDkg b` as a local computation. -/
def honestLocal (b : Fin (2 ^ layerHeight)) : OracleComp (LocalSpec C) (SetupOutputs C) :=
  seedGenLocal (E := E) >>= fun keys => localVote (E := E) (fun i => (keys i).map seedVote) >>= fun ok =>
    localRuns K circuits settings runLimit .top runLimit (seedState noCoalition () keys ok) >>= fun s =>
      localRuns K circuits settings runLimit (.bottom b) runLimit s >>= fun s => pure (setupOutputsOf b s)

omit [Fintype E] [DecidableEq E] in
/-- `honestDkg b` is `honestLocal b` on the free copy. -/
theorem honestDkg_eq (b : Fin (2 ^ layerHeight)) :
    honestDkg K circuits settings runLimit b = free (honestLocal K circuits settings runLimit b) := by
  unfold honestDkg honestLocal seedGenLocal
  rw [realExecution_honestNet]
  simp only [treeRuns_run, voteRound_honestNet, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, free_bind, free_pure]
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
    localRuns K circuits settings runLimit (.bottom b) runLimit (withTop keys top) >>= fun s => pure (setupOutputsOf b s)

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
    (localRuns K circuits settings runLimit tree count s₁ >>= fun st => pure (setupOutputsOf b st)) =
      localRuns K circuits settings runLimit tree count s₂ >>= fun st => pure (setupOutputsOf b st) := by
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

end Bridge

section TopRuns

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- For dealt keys and a start cache, the runs of the top tree and then of bottom tree `b` are at
distance `treeAbortError .top` from the dealer top tree and then the runs of bottom tree `b`. -/
theorem topRuns_from (prims : Primitives) (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (hlimit : 0 < runLimit) (b : Fin (2 ^ layerHeight)) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (s : HashCache C) (hs : StartInvariant s) (count : ℕ) (hcount : 0 < count) :
    letI : MeasurableSpace (SetupOutputs C) := ⊤
    measureTVDist
      ((simulateQ (localAnswer prims)
        (localRuns K circuits settings runLimit .top count
            (startState noCoalition () fun i => some (dealtKeys parameter seeds pairKeys i)) >>= fun st =>
          localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (setupOutputsOf b st))).run' s)
      ((simulateQ (localAnswer prims)
        (dealtTopLocal (fun i => some (dealtKeys parameter seeds pairKeys i)) >>= fun top =>
          localRuns K circuits settings runLimit (.bottom b) runLimit
            (withTop (fun i => some (dealtKeys parameter seeds pairKeys i)) top) >>= fun st =>
              pure (setupOutputsOf b st))).run' s) ≤
      treeAbortError (E := E) circuits settings .top := by
  let : MeasurableSpace (SetupOutputs C) := ⊤
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcount.ne'
  set keys : C.Party → Option (Keys C) := fun i => some (dealtKeys parameter seeds pairKeys i) with hkeys
  set st0 : HonestState C E := startState noCoalition () keys with hst0
  have hmay : mayRun runLimit noCoalition st0 .top :=
    ⟨hlimit, firstParty C, by simp [noCoalition], rfl⟩
  have hreal : localTreeRun K circuits settings st0.operators .top =
      realTree K circuits settings emptyTop .top parameter seeds pairKeys :=
    localTreeRun_top K circuits settings _ parameter seeds pairKeys fun _ => rfl
  set f : (C.Party → Option TreeOutput) → OracleComp (LocalSpec C) (SetupOutputs C) := fun z =>
    localVote (E := E) (fun i => (z i).map (treeVote .top)) >>= fun ok =>
      localRuns K circuits settings runLimit .top n (afterRun st0 (committed ok z) .top) >>= fun st =>
        localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (setupOutputsOf b st) with hf
  have hleft : (localRuns K circuits settings runLimit .top (n + 1) st0 >>= fun st =>
      localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (setupOutputsOf b st)) =
      realTree K circuits settings emptyTop .top parameter seeds pairKeys >>= f := by
    simp only [localRuns, hmay, ↓reduceIte, hreal, bind_assoc, hf]
  have hcouple := firstRun_coupling K circuits settings prims hsize emptyTop .top parameter seeds pairKeys s hs f
  set g : Option TopTree → OracleComp (LocalSpec C) (SetupOutputs C) := fun top =>
    localRuns K circuits settings runLimit (.bottom b) runLimit (withTop keys top) >>= fun st =>
      pure (setupOutputsOf b st) with hg
  have hsupp : (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds emptyTop .top >>= f)).run' s =ᵈ
      (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds emptyTop .top >>= fun a =>
        g (TreeOutput.topTree (a (firstParty C))))).run' s := by
    refine evalDist_run'_bind_congr prims _ _ _ s fun p hp => ?_
    obtain ⟨hn, -, o₀, heq, ho⟩ :=
      idealTree_value prims circuits settings parameter seeds emptyTop .top hsize s hs.1 hs.2 p hp
    obtain ⟨h, hgood, hagree⟩ := exists_good prims p.2 hn
    have ho₀ := ho h p.2 hgood le_rfl hagree
    rw [ceremonyAt_top] at ho₀
    rw [heq, ho₀]
    set t : TopTree := _ with ht
    have hnot : ¬ mayRun runLimit noCoalition (afterRun st0 (committed true fun _ => some (.top t)) .top) .top := by
      simp [mayRun, afterRun, committed, OperatorState.keep, TreeOutput.topTree]
    have hfg : (localRuns K circuits settings runLimit .top n (afterRun st0 (committed true fun _ => some (.top t)) .top)
        >>= fun st => localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st =>
          pure (setupOutputsOf b st)) = g (some t) := by
      simp only [hg]
      rw [localRuns_of_not_mayRun K circuits settings runLimit .top _ hnot, pure_bind]
      refine localRuns_outputs_congr K circuits settings runLimit (.bottom b) b runLimit _ _ ?_ rfl ?_
      · funext i
        simp [afterRun, committed, withTop, OperatorState.keep, TreeOutput.topTree, hst0, startState]
      · simp [afterRun, withTop, hst0, startState]
    have hvote := run'_localVote_const (E := E) prims (some (treeVote .top (.top t)))
      (fun ok => localRuns K circuits settings runLimit .top n (afterRun st0 (committed ok fun _ => some (.top t)) .top)
        >>= fun st => localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st =>
          pure (setupOutputsOf b st)) p.2
    simp only [Option.isSome_some, hfg] at hvote
    exact hvote
  have hD : (dealtTopLocal keys >>= g) = liftComp (referenceTree tweakable (prfValue seeds) parameter emptyTop .top)
      (LocalSpec C) >>= fun o => g (TreeOutput.topTree o) := by
    simp only [dealtTopLocal, hkeys, Option.isSome_some, implies_true, ↓reduceIte, gameSeeds_dealt,
      gameParameter_dealt, liftComp_map, bind_map_left]
  have hright := dealer_continuation circuits settings prims hc hsize parameter seeds emptyTop .top
    (fun o => g (TreeOutput.topTree o)) s
  rw [← hD] at hright
  rw [hleft]
  unfold measureTVDist
  rw [← hright, ← hsupp.evalDist_eq]
  exact hcouple

/-- `TopRunsHop` from `SeedGenEnd`. The seed generation gives dealt keys and a start cache, and then
`topRuns_from` bounds the rest of the game for each outcome. -/
theorem topRunsHop_of_seedGenEnd (seedGenEnd : ∀ prims, SeedGenEnd (C := C) (E := E) prims) :
    TopRunsHop K circuits settings runLimit := by
  intro hsize hruns prims hc b
  let : MeasurableSpace (SetupOutputs C) := ⊤
  rw [honestDkg_eq, topDealtDkg_eq, fst_runWorld_free, fst_runWorld_free]
  unfold honestLocal topDealtLocal
  refine tvDist_bind_le_of_support prims _ _ _ ∅
    (by unfold treeAbortError coinFailure coinKeyCollision; positivity) fun p hp => ?_
  obtain ⟨parameter, seeds, pairKeys, hkeys⟩ := seedGen_dealt prims p hp
  have hs : StartInvariant p.2 := seedGenEnd prims p hp
  rw [hkeys]
  have hstart : seedState (σ := (honestNet (C := C) (E := E)).State) noCoalition ()
      (fun i => some (dealtKeys parameter seeds pairKeys i)) true =
      startState (σ := (honestNet (C := C) (E := E)).State) noCoalition () fun i =>
        some (dealtKeys parameter seeds pairKeys i) := by
    unfold seedState
    dsimp only
    congr 1
    simp [split]
  have hvote := run'_localVote_const (E := E) prims (some (.vote 0 0 [bitsOfDigest parameter] : Query C))
    (fun ok => localRuns K circuits settings runLimit .top runLimit
      (seedState noCoalition () (fun i => some (dealtKeys parameter seeds pairKeys i)) ok) >>= fun st =>
        localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (setupOutputsOf b st)) p.2
  simp only [Option.isSome_some] at hvote
  have h := topRuns_from K circuits settings runLimit prims hc hsize hruns b parameter seeds pairKeys p.2 hs runLimit hruns
  unfold measureTVDist at h ⊢
  refine le_of_eq_of_le ?_ h
  congr 1
  refine hvote.evalDist_eq.trans ?_
  rw [hstart]

end TopRuns

section SeedGenEnd

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## Programs with no coin query -/

/-- A query of the local oracles that is no coin key and no expansion. -/
def LocalSafe : (LocalSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.inl q) => ¬ IsCoin q
  | .inr (.inr _) => True

/-- A query of the program of an operator whose local part is `LocalSafe`. -/
def PartySafe {ι : Type} {G : OracleSpec ι} : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => LocalSafe t
  | _ => True

/-- A program of an operator that makes no coin query on any path. -/
def SafeProg {ι : Type} {G : OracleSpec ι} {α : Type} (p : OracleComp (PartySpec C E G) α) : Prop :=
  AllQueriesSatisfy p (PartySafe (C := C) (E := E) (G := G))

/-- A step whose continuation makes no coin query on any path. -/
def StepSafe {ι : Type} {G : OracleSpec ι} {α : Type} : Step C E G α → Prop
  | .done _ => True
  | .wait _ k => ∀ m, SafeProg (k m)
  | .call _ k => ∀ r, SafeProg (k r)

/-- A local query that is no coin query keeps `StartInvariant`. -/
theorem localAnswer_startInvariant (prims : Primitives) (t : (LocalSpec C).Domain) (ht : LocalSafe t)
    (s : HashCache C) (hs : StartInvariant s) (z : (LocalSpec C).Range t × HashCache C)
    (hz : z ∈ support ((localAnswer prims t).run s)) : StartInvariant z.2 := by
  refine ⟨(localAnswer_support (prims := prims) (fun _ => 0) t s z hz).2.1 hs.1, cacheOK_of_frame hs.2 ?_⟩
  rcases t with n | q | x
  · change z ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s) at hz
    simp [unifFwdImpl] at hz
    obtain ⟨a, rfl⟩ := hz
    exact fun _ _ => rfl
  · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (ThresholdLeanXmss.hashQuery q) =
        hashAnswer prims q := (simulateQ_query _ _).trans (id_map _)
    exact FrameR.hashQuery (prims := prims) ht s z (by rw [h1]; exact hz)
  · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) = prgAnswer prims x :=
      (simulateQ_query _ _).trans (id_map _)
    exact FrameR.prg (prims := prims) x s z (by rw [h1]; exact hz)

/-- `advance` of a program with no coin query keeps `StartInvariant` and stops at a step whose
continuation makes no coin query. -/
theorem advance_safe (prims : Primitives) {ι : Type} {G : OracleSpec ι} {α : Type}
    (p : OracleComp (PartySpec C E G) (Option α)) (hp : SafeProg p) :
    ∀ (s : HashCache C) (z : Step C E G α × HashCache C), StartInvariant s →
      z ∈ support ((simulateQ (localAnswer prims) (advance p)).run s) → StartInvariant z.2 ∧ StepSafe z.1 := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro s z hs hz
    change z ∈ support ((simulateQ (localAnswer prims) (pure (Step.done x))).run s) at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hs, trivial⟩
  | query_bind t k ih =>
    intro s z hs hz
    rw [SafeProg, allQueriesSatisfy_query_bind_iff] at hp
    rcases t with (t | outbox) | input
    · change z ∈ support ((simulateQ (localAnswer prims)
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (k r))).run s) at hz
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      have hy' : y ∈ support ((localAnswer prims t).run s) := by
        simpa [simulateQ_query] using hy
      exact ih y.1 (hp.2 y.1) y.2 z (localAnswer_startInvariant prims t hp.1 s hs y hy') hz
    · change z ∈ support ((simulateQ (localAnswer prims) (pure (Step.wait outbox k))).run s) at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hs, hp.2⟩
    · change z ∈ support ((simulateQ (localAnswer prims) (pure (Step.call input k))).run s) at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hs, hp.2⟩

/-- Local computations that keep an invariant and give results with a property, in sequence. -/
theorem sequenceFin_inv (prims : Primitives) {β : Type} (Inv : HashCache C → Prop) (Q : β → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) β),
      (∀ i s z, Inv s → z ∈ support ((simulateQ (localAnswer prims) (f i)).run s) → Inv z.2 ∧ Q z.1) →
      ∀ s z, Inv s → z ∈ support ((simulateQ (localAnswer prims) (OverPermutation.sequenceFin f)).run s) →
        Inv z.2 ∧ ∀ i, Q (z.1 i)
  | 0, f, _, s, z, hs, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hs, fun i => i.elim0⟩
  | n + 1, f, hf, s, z, hs, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    obtain ⟨hy1, hy2⟩ := hf 0 s y hs hy
    obtain ⟨hw1, hw2⟩ := sequenceFin_inv prims Inv Q (fun i : Fin n => f i.succ) (fun i => hf i.succ) y.2 w hy1 hw
    refine ⟨hw1, fun i => ?_⟩
    cases i using Fin.cases with
    | zero => exact hy2
    | succ i => exact hw2 i

/-- One honest step of programs with no coin query keeps `StartInvariant`, and the next steps make no
coin query. -/
theorem honestStep_safe (prims : Primitives) {α : Type} (reply : PEmpty → PEmpty)
    (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepSafe (steps i)) (s : HashCache C)
    (z : (C.Party → Step C E RealSpec α) × HashCache C) (hs : StartInvariant s)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestStep noFunctionality reply steps)).run s)) :
    StartInvariant z.2 ∧ ∀ i, StepSafe (z.1 i) := by
  unfold honestStep at hz
  split_ifs at hz with hcall
  · obtain ⟨⟨i, hi⟩, -⟩ := hcall
    revert hi
    cases steps i with
    | done _ => simp [Step.callInput]
    | wait _ _ => simp [Step.callInput]
    | call input _ => exact input.elim
  · refine sequenceFin_inv prims StartInvariant StepSafe _ (fun j s' z' hs' hz' => ?_) s z hs hz
    have hj := hsteps j
    split at hz'
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz'
      subst hz'
      exact ⟨hs', trivial⟩
    · rename_i heq
      rw [heq] at hj
      exact advance_safe prims _ (hj _) s' z' hs' hz'
    · rename_i input _ _
      exact input.elim

/-- The honest rounds of programs with no coin query keep `StartInvariant`. -/
theorem honestRounds_safe (prims : Primitives) {α : Type} (reply : PEmpty → PEmpty) :
    ∀ (fuel : ℕ) (steps : C.Party → Step C E RealSpec α), (∀ i, StepSafe (steps i)) →
      ∀ s z, StartInvariant s →
        z ∈ support ((simulateQ (localAnswer prims) (honestRounds noFunctionality reply fuel steps)).run s) →
          StartInvariant z.2
  | 0, steps, _, s, z, hs, hz => by
    simp only [honestRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | fuel + 1, steps, hsteps, s, z, hs, hz => by
    unfold honestRounds at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
    · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      obtain ⟨hy1, hy2⟩ := honestStep_safe prims reply steps hsteps s y hs hy
      exact honestRounds_safe prims reply fuel y.1 hy2 y.2 z hy1 hz

/-! ## The programs of the seed generation -/

/-- A query of `H` and `PRG` that is no coin query. -/
def RoSafe : (RoSpec C).Domain → Prop
  | .inl q => ¬ IsCoin q
  | .inr _ => True

/-- A program of an operator with no coin query on any path, as a program of `PartyM`. -/
def SafeM {ι : Type} {G : OracleSpec ι} {α : Type} (x : PartyM C E G α) : Prop := SafeProg x.run

theorem liftComp_local_safe {ι : Type} {G : OracleSpec ι} {β : Type} (oa : OracleComp (LocalSpec C) β)
    (h : AllQueriesSatisfy oa LocalSafe) :
    SafeProg (E := E) (liftComp oa (PartySpec C E G)) := by
  refine AllQueriesSatisfy.simulateQ h fun t ht => ?_
  rw [liftM_query_local]
  exact (allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inl t)) _).2 ht

theorem liftComp_ro_safe {β : Type} (oa : OracleComp (RoSpec C) β) (h : AllQueriesSatisfy oa RoSafe) :
    AllQueriesSatisfy (liftComp oa (LocalSpec C)) LocalSafe := by
  refine AllQueriesSatisfy.simulateQ h fun t ht => ?_
  rcases t with q | x
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inl q)) _).2 ht
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inr x)) _).2 trivial

theorem liftComp_prob_safe {β : Type} (oa : ProbComp β) :
    AllQueriesSatisfy (liftComp oa (LocalSpec C)) LocalSafe := by
  refine AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) oa)
    fun t _ => ?_
  exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 trivial

section SafeM

variable {ι : Type} {G : OracleSpec ι}

theorem SafeM.pure {α : Type} (a : α) : SafeM (C := C) (E := E) (G := G) (Pure.pure a : PartyM C E G α) := by
  unfold SafeM SafeProg
  rw [OptionT.run_pure]
  exact allQueriesSatisfy_pure _ _

theorem SafeM.failure {α : Type} : SafeM (C := C) (E := E) (G := G) (Alternative.failure : PartyM C E G α) := by
  unfold SafeM SafeProg
  rw [OptionT.run_failure]
  exact allQueriesSatisfy_pure _ _

theorem SafeM.bind {α β : Type} {x : PartyM C E G α} {f : α → PartyM C E G β} (hx : SafeM x)
    (hf : ∀ a, SafeM (f a)) : SafeM (x >>= f) := by
  unfold SafeM SafeProg at *
  rw [OptionT.run_bind]
  refine allQueriesSatisfy_bind hx fun o => ?_
  cases o with
  | none => exact allQueriesSatisfy_pure _ _
  | some a => exact hf a

theorem SafeM.localStep {β : Type} {oa : OracleComp (LocalSpec C) β} (h : AllQueriesSatisfy oa LocalSafe) :
    SafeM (C := C) (E := E) (G := G) (localStep oa) := by
  unfold SafeM SafeProg ThresholdLeanXmss.localStep
  simp only [OptionT.run_lift]
  exact allQueriesSatisfy_bind (liftComp_local_safe oa h) fun _ => allQueriesSatisfy_pure _ _

theorem SafeM.oracleStep {β : Type} {oa : OracleComp (RoSpec C) β} (h : AllQueriesSatisfy oa RoSafe) :
    SafeM (C := C) (E := E) (G := G) (oracleStep oa) :=
  SafeM.localStep (liftComp_ro_safe oa h)

theorem SafeM.exchange (outbox : Mail C E) : SafeM (C := C) (E := E) (G := G) (exchange outbox) := by
  unfold SafeM SafeProg ThresholdLeanXmss.exchange
  simp only [OptionT.run_bind, OptionT.run_lift]
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inr outbox)) _).2
    trivial) fun inbox => ?_
  rcases inbox with _ | x
  · exact allQueriesSatisfy_pure _ _
  · dsimp only [Option.elim]
    split_ifs
    exacts [SafeM.failure (C := C) (E := E) (G := G) (α := Mail C E), SafeM.pure (C := C) (E := E) (G := G) x]

theorem SafeM.require (c : Prop) : SafeM (C := C) (E := E) (G := G) (require c) := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact SafeM.pure _
  · exact SafeM.failure

end SafeM

theorem mapM_safe {ι : Type} {spec : OracleSpec ι} {α β : Type} (P : ι → Prop) (f : α → OracleComp spec β)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : ∀ l : List α, AllQueriesSatisfy (l.mapM f) P
  | [] => allQueriesSatisfy_pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf a) fun _ =>
      allQueriesSatisfy_bind (mapM_safe P f hf l) fun _ => allQueriesSatisfy_pure _ _

theorem hashQuery_safe {q : Query C} (hq : ¬ IsCoin q) : AllQueriesSatisfy (ThresholdLeanXmss.hashQuery q) RoSafe :=
  (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 hq

theorem deriveKeys_safe (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    AllQueriesSatisfy (deriveKeys phase i view) RoSafe := by
  unfold ThresholdLeanXmss.deriveKeys
  have hq : ∀ (k : KeyKind) (l : List HashOutput),
      AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.derive phase k l)) RoSafe :=
    fun _ _ => hashQuery_safe (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)
  have hrest : ∀ parameter : HashOutput, AllQueriesSatisfy (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        ThresholdLeanXmss.hashQuery (C := C)
          (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else Pure.pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then Pure.pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      Pure.pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun (j : C.Party) => pair.getD j.val 0))
      RoSafe := fun parameter =>
    allQueriesSatisfy_bind (mapM_safe _ _ (fun T => by split_ifs; exacts [hq _ _, allQueriesSatisfy_pure _ _]) _)
      fun _ => allQueriesSatisfy_bind
        (mapM_safe _ _ (fun j => by split_ifs; exacts [allQueriesSatisfy_pure _ _, hq _ _]) _)
        fun _ => allQueriesSatisfy_pure _ _
  split_ifs
  · exact allQueriesSatisfy_bind (hq _ _) hrest
  · exact allQueriesSatisfy_bind (allQueriesSatisfy_pure _ _) hrest

theorem commitRevealEcho_safe {ι : Type} {G : OracleSpec ι} (phase : Phase) (i : C.Party) (own : Parts C) :
    SafeM (C := C) (E := E) (G := G) (commitRevealEcho phase i own) := by
  have hc : ∀ a b l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.commit phase a b l)) RoSafe :=
    fun _ _ _ => hashQuery_safe (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)
  have hs : ∀ l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.sharedKeys phase l)) RoSafe :=
    fun _ => hashQuery_safe (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)
  unfold commitRevealEcho
  refine SafeM.bind (SafeM.oracleStep (mapM_safe _ _ (fun _ => hc _ _ _) _)) fun commitments => ?_
  refine SafeM.bind (SafeM.exchange _) fun committed => ?_
  refine SafeM.bind (SafeM.exchange _) fun revealed => ?_
  refine SafeM.bind (SafeM.oracleStep (mapM_safe _ _ (fun _ => hc _ _ _) _)) fun opens => ?_
  refine SafeM.bind (SafeM.require _) fun _ => ?_
  refine SafeM.bind (SafeM.oracleStep (deriveKeys_safe _ _ _)) fun keys => ?_
  refine SafeM.bind (SafeM.oracleStep (mapM_safe _ _ (fun _ => hs _) _)) fun shared => ?_
  refine SafeM.bind (SafeM.exchange _) fun received => ?_
  refine SafeM.bind (SafeM.require _) fun _ => ?_
  exact SafeM.pure _

theorem seedGen_safe (i : C.Party) : SafeProg (seedGen (E := E) (G := RealSpec) i).run := by
  change SafeM (seedGen (E := E) (G := RealSpec) i)
  unfold seedGen seedGenWith
  refine SafeM.bind (SafeM.localStep (liftComp_prob_safe _)) fun own => ?_
  refine SafeM.bind (commitRevealEcho_safe _ _ _) fun keys => ?_
  exact SafeM.pure _

/-! ## The start cache and the top hop -/

section Hop

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The honest seed generation from the empty cache ends in a cache with `StartInvariant`. -/
theorem seedGenEnd (prims : Primitives) : SeedGenEnd (C := C) (E := E) prims := by
  intro z hz
  unfold honestStart at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨hy1, hy2⟩ := sequenceFin_inv prims StartInvariant StepSafe _
    (fun i s w hs hw => advance_safe prims _ (seedGen_safe i) s w hs hw) ∅ y ⟨noMpc_empty, cacheOK_empty⟩ hy
  exact honestRounds_safe prims _ setupRounds y.1 hy2 y.2 z hy1 hz

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `TopRunsHop` holds. -/
theorem topRunsHop : TopRunsHop K circuits settings runLimit :=
  topRunsHop_of_seedGenEnd K circuits settings runLimit seedGenEnd

end Hop

end SeedGenEnd

/-- info: 'ThresholdLeanXmssSecurity.DkgCompletenessProof.topRunsHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topRunsHop

end ThresholdLeanXmssSecurity.DkgCompletenessProof
