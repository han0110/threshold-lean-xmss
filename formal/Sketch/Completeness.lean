import Sketch.DkgGame
import ThresholdLeanXmssSecurity.Proof.Tree

/-!
# `DkgCompleteness`, the honest run

`DkgCompleteness` follows from four hops on the honest run.

* `TopRunsHop` replaces the runs of the top tree by the top tree of the dealer on the seeds of the
  game, at distance `treeAbortError .top`.
* `BottomRunsHop` replaces the runs of bottom tree `b` by the bottom tree of the dealer, at distance
  `treeAbortError (.bottom b)`.
* `SeedGenHop` replaces the keys of the seed generation by the keys of `prawnsKeyGen`, at distance
  `derivedKeyCollision C`.
* `DealerAbort` bounds the probability that the dealer gives no bottom tree by `searchFailure`.

`dkgCompleteness_of_hops` adds the four terms. `StartInvariant` is the invariant of a start cache.
`SeedGenEnd`, `TreeRunFrom` and `startInvariant_idealTree` are claims from a start cache for the
phases of the hops. The hops put the dealer tree before the real runs of a tree, so that each real
run starts from a cache with the invariant.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The start cache -/

/-- The invariant of a start cache of a tree run. The cache has no cell of `Th` on an input of the
MPC, and no coin key and no expanded value of a coin key. -/
def StartInvariant (s : HashCache C) : Prop := NoMpc s ∧ CacheOK ∅ 0 s

/-! ## The intermediate runs -/

/-- The top tree of the dealer on the seeds and the parameter of the game. It is `none` when an
operator has no keys, because then every run of a tree stops at all operators. -/
def dealtTop (keys : C.Party → Option (Keys C)) : OracleComp (WorldSpec C) (Option TopTree) :=
  if ∀ i, (keys i).isSome then
    free (liftComp (TreeOutput.topTree <$> referenceTree (fun oa => tweakable oa)
      (prfValue (gameSeeds noCoalition keys)) (gameParameter noCoalition keys) emptyTop .top) _)
  else pure none

/-- Bottom tree `b` of the dealer on the seeds and the parameter of the game and on the top tree
`top`. -/
def dealtBottom (keys : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) :
    Option TopTree → OracleComp (WorldSpec C) (Option BottomTree)
  | some top => free (liftComp (bottomOf <$> referenceTree (fun oa => tweakable oa)
      (prfValue (gameSeeds noCoalition keys)) (gameParameter noCoalition keys) top (.bottom b)) _)
  | none => pure none

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The honest run with the top tree of the dealer in place of the runs of the top tree. Each
operator holds that top tree, and then bottom tree `b` runs `runLimit` times. -/
def topDealtDkg (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (SetupOutputs C) := do
  let (state, keys) ← realExecution noCoalition honestNet noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let top ← dealtTop keys
  let start := startState noCoalition state keys
  let (_, s) ← (treeRuns K circuits settings runLimit noMonitor noCoalition honestNet (.bottom b) runLimit).run
    { start with operators := fun i => { start.operators i with top := top } }
  pure fun i => ((s.operators i).keys, (s.operators i).top, (s.operators i).bottom b)

/-- The honest seed generation with the top tree and bottom tree `b` of the dealer in place of the
runs of the trees. -/
def referenceDkg (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (SetupOutputs C) := do
  let (_, keys) ← realExecution noCoalition honestNet noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let top ← dealtTop keys
  let bottom ← dealtBottom keys b top
  pure fun i => (keys i, top, bottom)

/-! ## The hops -/

/-- Hop C5a. The runs of the top tree give the top tree of the dealer, except when an honest check
of the first run aborts. -/
def TopRunsHop : Prop :=
  0 < settings.batchSize → 0 < runLimit → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ b : Fin (2 ^ layerHeight),
      letI : MeasurableSpace (SetupOutputs C) := ⊤
      measureTVDist (Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b))
          (Prod.fst <$> runWorld prims (topDealtDkg K circuits settings runLimit b)) ≤
        treeAbortError (E := E) circuits settings .top

/-- Hop C5b. The runs of bottom tree `b` give bottom tree `b` of the dealer, except when an honest
check of the first run aborts. A failed search fails in each run and at the dealer. -/
def BottomRunsHop : Prop :=
  0 < settings.batchSize → 0 < runLimit → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ b : Fin (2 ^ layerHeight),
      letI : MeasurableSpace (SetupOutputs C) := ⊤
      measureTVDist (Prod.fst <$> runWorld prims (topDealtDkg K circuits settings runLimit b))
          (Prod.fst <$> runWorld prims (referenceDkg (E := E) b)) ≤
        treeAbortError (E := E) circuits settings (.bottom b)

/-- Hop C5c. The honest seed generation gives the keys of `prawnsKeyGen`, except when two derived
keys collide. The trees of the dealer read no cell of the seed generation. -/
def SeedGenHop : Prop :=
  ∀ (prims : Primitives) (b : Fin (2 ^ layerHeight)),
    letI : MeasurableSpace (SetupOutputs C) := ⊤
    measureTVDist (Prod.fst <$> runWorld prims (referenceDkg (E := E) b))
        (Prod.fst <$> runWorld prims (dealerDkg (C := C) b)) ≤
      derivedKeyCollision C

/-- Hop C5d. The dealer gives keys, a top tree and bottom tree `b` to each operator, except when the
randomizer search of bottom tree `b` fails. -/
def DealerAbort : Prop :=
  ∀ (prims : Primitives) (b : Fin (2 ^ layerHeight)),
    (Pr{let r ← runWorld prims (dealerDkg (C := C) b)}[∃ i,
        (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none]).toReal ≤ searchFailure

/-! ## The phase claims from a start cache -/

/-- The honest seed generation from the empty cache ends in a start cache. It writes only cells of
the phase `.seedGen` of `.commit`, `.derive` and `.sharedKeys`. -/
def SeedGenEnd (prims : Primitives) : Prop :=
  ∀ z ∈ support ((simulateQ (localAnswer prims)
      (honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds)).run ∅),
    StartInvariant z.2

/-- An honest run of `tree` on dealt keys from a start cache is at distance `treeAbortError tree`
from the dealer of the tree from that cache. -/
def TreeRunFrom (prims : Primitives) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (s : HashCache C), StartInvariant s →
    letI : MeasurableSpace (C.Party → Option TreeOutput) := ⊤
    measureTVDist ((simulateQ (localAnswer prims) (realTree K circuits settings top tree parameter seeds pairKeys)).run' s)
        ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree)).run' s) ≤
      treeAbortError (E := E) circuits settings tree

/-- `idealTree_value` of the library from a start cache. -/
theorem idealTree_value_from (prims : Primitives) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (tree : Tree) (hsize : 0 < settings.batchSize) (s : HashCache C) (hs : StartInvariant s) (z)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree)).run s)) :
    NoMpc z.2 ∧ CacheOK ∅ 0 z.2 ∧ ∃ o₀, z.1 = (fun _ => o₀) ∧
      ∀ h s', Good prims h → z.2 ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree := by
  obtain ⟨hle, hn, hsupp⟩ := localRun_support _ s z hz
  have hn' := hn hs.1
  have hfr : FrameL prims (idealTree circuits settings parameter seeds top tree) :=
    FrameL.liftComp ((FrameR.dealerCeremony prims circuits settings parameter seeds top tree).map _)
  refine ⟨hn', cacheOK_of_frame hs.2 (hfr s z hz), ?_⟩
  have hval : ∀ h s', Good prims h → z.2 ≤ s' → Agrees h s' →
      z.1 = fun _ => ceremonyAt prims circuits parameter seeds h top tree := by
    intro h s' hg hle' ha
    have hv := hsupp h hg (ha.mono hle')
    simp only [idealTree, simulateQ_fixedLocal_liftComp, D_map, support_pure, Set.mem_singleton_iff] at hv
    rw [D_dealerCeremony prims circuits settings parameter seeds h top tree hsize] at hv
    exact hv
  let h₀ := hashOf prims z.2
  have heq := hval h₀ z.2 (good_hashOf prims z.2) le_rfl (agrees_hashOf prims hn')
  refine ⟨ceremonyAt prims circuits parameter seeds h₀ top tree, heq, ?_⟩
  intro h s' hg hle' ha
  have e := hval h s' hg hle' ha
  rw [heq] at e
  exact congrFun e ⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩

/-- `TreeRunFrom` holds. It is `treeCompleteness` of the library from a start cache. -/
theorem treeRunFrom (prims : Primitives) : TreeRunFrom K circuits settings prims := by
  intro hsize top tree parameter seeds pairKeys s hs
  let : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩⟩
  refine (tvDist_le_joint prims _ _ s).trans ?_
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

/-- The dealer of a tree keeps the invariant of a start cache. -/
theorem startInvariant_idealTree (prims : Primitives) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (tree : Tree) (hsize : 0 < settings.batchSize) (s : HashCache C) (hs : StartInvariant s) (z)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree)).run s)) :
    StartInvariant z.2 :=
  let ⟨hn, hc, _⟩ := idealTree_value_from circuits settings prims parameter seeds top tree hsize s hs z hz
  ⟨hn, hc⟩

/-! ## The assembly -/

omit [DecidableEq E] in
/-- `DkgCompleteness` from the four hops. The distance adds the three hops, and the abort
is the distance and the abort of the dealer. -/
theorem dkgCompleteness_of_hops (topRuns : TopRunsHop K circuits settings runLimit)
    (bottomRuns : BottomRunsHop K circuits settings runLimit) (seedGenHop : SeedGenHop (C := C) (E := E))
    (dealer : DealerAbort (C := C)) (batch : 0 < settings.batchSize) (runs : 0 < runLimit)
    (prims : Primitives) (compute : CircuitsCompute circuits prims.Th) (b : Fin (2 ^ layerHeight)) :
    (Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[∃ i,
        (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none]).toReal ≤
        dkgAbortError (E := E) circuits settings C b ∧
      letI : MeasurableSpace (SetupOutputs C) := ⊤
      measureTVDist (Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b))
          (Prod.fst <$> runWorld prims (dealerDkg b)) ≤
        dkgCompletenessError (E := E) circuits settings C b := by
  let : MeasurableSpace (SetupOutputs C) := ⊤
  set honest := Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b)
  set topDealt := Prod.fst <$> runWorld prims (topDealtDkg K circuits settings runLimit b)
  set reference := Prod.fst <$> runWorld prims (referenceDkg (E := E) b)
  set dealt := Prod.fst <$> runWorld prims (dealerDkg (C := C) b)
  have distance : measureTVDist honest dealt ≤ dkgCompletenessError (E := E) circuits settings C b := by
    have h₁ := topRuns batch runs prims compute b
    have h₂ := bottomRuns batch runs prims compute b
    have h₃ := seedGenHop prims b
    have t₁ := measureTVDist_triangle honest topDealt dealt
    have t₂ := measureTVDist_triangle topDealt reference dealt
    unfold dkgCompletenessError
    linarith
  refine ⟨?_, distance⟩
  set event : SetupOutputs C → Prop := fun r => ∃ i, (r i).1 = none ∨ (r i).2.1 = none ∨ (r i).2.2 = none
  have transfer := abs_prEvent_toReal_sub_le_measureTVDist honest dealt event (measurable_from_top)
  have honestEvent : Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[event r.1] =
      Pr{let r ← honest}[event r] := by
    simp only [honest, prEvent_map]
  have dealtEvent : Pr{let r ← runWorld prims (dealerDkg (C := C) b)}[event r.1] = Pr{let r ← dealt}[event r] := by
    simp only [dealt, prEvent_map]
  have abort := dealer prims b
  change (Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[event r.1]).toReal ≤ _
  change (Pr{let r ← runWorld prims (dealerDkg (C := C) b)}[event r.1]).toReal ≤ _ at abort
  rw [honestEvent]
  rw [dealtEvent] at abort
  have := (abs_le.mp transfer).2
  unfold dkgAbortError
  unfold dkgCompletenessError at distance
  linarith

/-- info: 'ThresholdLeanXmss.Sketch.treeRunFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeRunFrom

end ThresholdLeanXmss.Sketch
