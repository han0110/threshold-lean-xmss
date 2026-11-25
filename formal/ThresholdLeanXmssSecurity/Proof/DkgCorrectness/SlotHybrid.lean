import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Game

/-!
# The hybrid over the PRSS setup slots

`isPrivate` marks the local calls that touch a private cell, and `tableLocal` answers them from a
table. `hybridGame j` is `dkgTreeGame` in which each run samples fresh keys for its slots below `j`.
`HybridContract`, `HybridEnd` and `HybridTableContract` state the steps of the hybrid, and
`hybridStart` proves `HybridStart`, which says that hybrid `0` is `dkgTreeGame`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned

variable {C : Committee} (Q : Query C → Bool)

/-! ## The private domains -/

/-- A local call that touches a cell with `Q`. -/
def isPrivate : (LocalSpec C).Domain → Bool
  | .inl _ => false
  | .inr (.inl q) => Q q
  | .inr (.inr x) => Q (.streamKey x.2.1)

/-- The handler of an emulator on `LocalSpec C` alone. -/
def tableLocal (prims : Primitives) :
    QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (LocalSpec C))) := fun t =>
  if isPrivate Q t then StateT.mk fun table => liftComp ((localAnswer prims t).run table) _
  else liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupEmulation

open Partitioned (isPrivate tableLocal)

variable {C : Committee} {E : Type}

/-- The cells outside the setups of `phase`. -/
def outsideSetup (phase : Phase) (q : Query C) : Bool := decide (queryClass q ≠ phaseClass phase)

/-! ## One private table through a phase -/

section Phase

variable (Q : Query C → Bool) (prims : Primitives)

/-- The adversary `A` with one private table for the cells with `Q` in its state. Each piece of `A` runs
under `tableLocal Q prims` on the table of the state, and the start begins with the table `p0`. -/
abbrev tableAdversary {I L R : Type} (A : Adversary C E I L R) (p0 : HashCache C) : Adversary C E I L R where
  State := A.State × HashCache C
  start x z := (simulateQ (tableLocal Q prims) (A.start x z)).run p0
  round st sent :=
    (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (tableLocal Q prims) (A.round st.1 sent)).run st.2
  answer st l :=
    (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (tableLocal Q prims) (A.answer st.1 l)).run st.2

/-- The distinguisher `Z` on the table of the state of `tableAdversary`. -/
def tableDistinguisher {σ O : Type} (Z : Distinguisher C σ O) : Distinguisher C (σ × HashCache C) O :=
  fun r => (simulateQ (tableLocal Q prims) (Z (r.1.1, r.2))).run' r.1.2

end Phase

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupEmulation

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The slots -/

section Slots

variable {C : Committee}

/-- The PRSS setups of the runs `runs`. A run of the top tree has one setup and a run of a bottom
tree has two. -/
def setupsBefore (runs : Tree → ℕ) : ℕ :=
  runs .top * treeSetups .top + ∑ b : Fin (2 ^ layerHeight), runs (.bottom b) * treeSetups (.bottom b)

/-- The fresh keys of one slot, namely a seed for each term and a key for each pair. -/
abbrev FreshKeys (C : Committee) := (C.Term → HashOutput) × (C.Pair → HashOutput)

/-- The fresh keys of one slot, sampled as `seedGenHiddenZ` samples them. -/
def sampleFresh : ProbComp (FreshKeys C) := do
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairs ← $ᵗ (C.Pair → HashOutput)
  pure (seeds, pairs)

/-- Fresh keys for slot `slot` when it is below `j`. -/
def sampleSlot (j slot : ℕ) : ProbComp (Option (FreshKeys C)) :=
  if slot < j then some <$> sampleFresh else pure none

/-- The PRSS keys `prss` of operator `i` with the hidden coordinates of the fresh keys `fresh`. It is
the overlay of `seedGenHiddenZ` on the dealt keys of `fresh`. -/
def prssOverlay (D : C.Coalition) (i : C.Party) (prss : PrssKeys C) (fresh : FreshKeys C) : PrssKeys C :=
  let keys := seedGenHiddenOverlay D i ⟨0, prss.term, prss.pair⟩ (dealtKeys 0 fresh.1 fresh.2 i)
  ⟨keys.seed, keys.pairKey⟩

end Slots

/-! ## The hybrid games -/

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- One ceremony at operator `i`, as `ceremonyRun` of `newTree`. The inner state counts the ceremonies
of the run. When `fresh c` has fresh keys for ceremony `c`, the operator replaces the hidden
coordinates of its PRSS keys by them. -/
def slotCeremony (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C)
    (jobs : List Job) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (Option (List (List Bit))) := do
  let c ← StateT.lift (get : StateT ℕ (PartyM C E RealSpec) ℕ)
  StateT.lift (set (c + 1) : StateT ℕ (PartyM C E RealSpec) Unit)
  let prss ← StateT.lift (StateT.lift (prssSetup i))
  let ctx : Context C := ⟨i, keys, ((fresh c).map (prssOverlay D i prss)).getD prss⟩
  batched settings.batchSize (fun jobs => do
    let (label, k) ← get
    let inputs ← StateT.lift (StateT.lift (jobs.mapM (inputShares ctx)))
    let (outputs, state) ← StateT.lift (StateT.lift ((runJobs K (realRunBuildingBlocks K ctx settings.mode)
      (jobs.map (circuits keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩))
    set (state.label, k + 1)
    pure (some outputs)) jobs

/-- The ceremonies of a tree at operator `i`, as `newTree`, with the fresh keys `fresh`. -/
def slotTree (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C)
    (top : TopTree) (tree : Tree) : PartyM C E RealSpec TreeOutput := do
  let some output ← ((ceremonyOutput (m := StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)))
      (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
      (slotCeremony K circuits settings D fresh i keys) top tree).run' (0, 0)).run' 0 | failure
  pure output

/-- The program of operator `i` in a run of `tree`, as `treeProgram`, with the fresh keys `fresh`. -/
def slotProgram (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (operator : OperatorState C) : Tree → PartyM C E RealSpec TreeOutput
  | .top => match operator.keys with
    | some keys => slotTree K circuits settings D fresh i keys emptyTop .top
    | none => failure
  | .bottom b => match operator.keys, operator.top with
    | some keys, some top => slotTree K circuits settings D fresh i keys top (.bottom b)
    | _, _ => failure

/-- One run of `tree` in hybrid `j`, as `treeRun`. The run takes the slots from `setupsBefore s.runs`
on, and it samples on the free copy fresh keys for each of its slots below `j`. -/
def hybridTreeRun (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  let fresh ← StateT.lift (free (liftComp ((List.range (treeSetups tree)).mapM fun c =>
    sampleSlot (C := C) j (setupsBefore s.runs + c)) _))
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
    s.adversary fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) tree)
  let bad ← StateT.lift (monitor (fun i => (s.operators i).keys) tree outputs)
  let (state, ok) ← StateT.lift (voteRound worldRoles D net state fun i => (outputs i).map (treeVote tree))
  let kept := committed ok outputs
  let operators := fun i => (s.operators i).keep (kept i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad || split D kept⟩ : RealState C net.State)

/-- At most `count` runs of `tree` in hybrid `j`, as `treeRuns`. -/
def hybridTreeRuns (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      hybridTreeRun K circuits settings j monitor D net tree
      hybridTreeRuns j monitor D net tree count

/-- A request of bottom tree `b` in hybrid `j`, as `treeRequest`. -/
def hybridTreeRequest (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) : RealM C net.State (Option (BottomTree × Digest)) := do
  hybridTreeRuns K circuits settings runLimit j monitor D net (.bottom b) 1
  let s ← get
  match heldBottom D s.operators b with
  | some tree => pure (some (tree, ← gameValue D s.operators (.randomizer topLayer (topKey b))))
  | none => pure none

/-- The signing oracles in hybrid `j`, as `realOracles`. -/
def hybridOracles (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => StateT.lift (hybridTreeRequest K circuits settings runLimit j monitor D A.net b)
  | .round1 i J e message => signRequest D i e (.round1 i J e message)
  | .round2 i J e message parts => signRequest D i e (.round2 i J e message parts)

/-- The signing phase in hybrid `j`, as `dkgSigning`. -/
def hybridSigning (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    RealM C A.net.State Bool := do
  let s ← get
  let some (keys, top) := topHolder D s.operators | pure false
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  let (forgery, st) ← (simulateQ (forger + (hybridOracles K circuits settings runLimit j monitor D A + cell))
    (A.forge ⟨top.root, keys.parameter⟩ top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
  let s ← get
  forgeryWins realLift (canonicalDealt D s.operators keys.parameter top) st forgery

/-- The run of the game in hybrid `j`, as `dkgTsigRun`. -/
def hybridRun (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) (Bool × Bool) := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (state, ok) ← voteRound worldRoles D A.net state fun i => (keys i).map seedVote
  let (win, s) ← (do
      hybridTreeRuns K circuits settings runLimit j monitor D A.net .top runLimit
      hybridSigning K circuits settings runLimit j monitor D A).run (seedState D state keys ok)
  pure (win, s.flag)

/-- Hybrid `j` of `dkgTreeGame`. The slots below `j` have fresh hidden keys. -/
def hybridGame (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  Prod.snd <$> hybridRun K circuits settings runLimit j (wrongOutput D) D A

variable (prims : Primitives)

/-- `p j`, the probability of `UsedHit` at the end of hybrid `j` in `jointKeyWorld`. -/
def hybridProb (D : C.Coalition) (A : DkgTsigAdversary C E) (j : ℕ) : ℝ :=
  usedHitProb prims D (hybridGame K circuits settings runLimit j D A)

/-! ## The contract and the end points -/

/-- The standalone real execution of one PRSS setup, as in `SetupHiddenFresh`. -/
abbrev setupExec (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (z : Aux) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Keys C))) :=
  realExecution D A noFunctionality setupRounds
    (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) (fun _ => ()) z

/-- The contract of the hybrid. For each slot `j` there is a standalone PRSS setup with an adversary
and a distinguisher of budget `2 * q + honestSetupCalls`, whose acceptance is `hybridProb j`, and whose
acceptance with the fresh hidden keys of `seedGenHiddenZ` is `hybridProb (j + 1)`. The budget has
`2 * q` because `IsQueryBounded` adds the worst-case calls before and after the setup, and the forger can
spend `q` calls before the slot on one path and `q` calls after it on another path. -/
def HybridContract : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ j < gameSetups runLimit, ∃ (Aj : Adversary C E Unit PEmpty PEmpty) (Zj : Distinguisher C Aj.State (Keys C))
      (z : Aux), IsQueryBounded Aj Zj setupRounds (2 * q + honestSetupCalls runLimit C) ∧
      hybridProb K circuits settings runLimit prims D A j = accepts prims (distinguish (setupExec D Aj z) Zj) ∧
      hybridProb K circuits settings runLimit prims D A (j + 1) =
        accepts prims (distinguish (setupExec D Aj z) (seedGenHiddenZ D Zj))

/-- The start point. Hybrid `0` has the probability of the event of `UsedHitHop`. -/
def HybridStart : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    hybridProb K circuits settings runLimit prims D A 0 =
      usedHitProb prims D (dkgTreeGame K circuits settings runLimit D A)

/-- The end point. Hybrid `gameSetups runLimit`, in which every slot has fresh hidden keys, has
probability at most `freshKeyError`. -/
def HybridEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    hybridProb K circuits settings runLimit prims D A (gameSetups runLimit) ≤ freshKeyError runLimit C q

/-! ## The assembly -/

/-- The contract with a private table. The budget counts the calls of the table form of the reduction
`Bj`, `Yj`, with one private table for the cells outside the class `prssSetup`. The two acceptance
probabilities use the plain `Bj` and `Yj`. -/
def HybridTableContract : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ j < gameSetups runLimit, ∃ (Bj : Adversary C E Unit PEmpty PEmpty) (Yj : Distinguisher C Bj.State (Keys C))
      (z : Aux), IsQueryBounded (SetupEmulation.tableAdversary (SetupEmulation.outsideSetup .prss) prims Bj ∅)
        (SetupEmulation.tableDistinguisher (SetupEmulation.outsideSetup .prss) prims Yj) setupRounds
        (2 * q + honestSetupCalls runLimit C) ∧
      hybridProb K circuits settings runLimit prims D A j = accepts prims (distinguish (setupExec D Bj z) Yj) ∧
      hybridProb K circuits settings runLimit prims D A (j + 1) =
        accepts prims (distinguish (setupExec D Bj z) (seedGenHiddenZ D Yj))

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace HybridStartProof

section Erases

variable {P : Type → Type} [Monad P] [LawfulMonad P] {σ : Type}

/-- The program `x` with an extra counter erases to `y`. From each state and each counter, the run of
`x` with the counter dropped is the run of `y`. -/
def Erases {α : Type} (x : StateT σ (StateT ℕ P) α) (y : StateT σ P α) : Prop :=
  ∀ s n, Prod.fst <$> (x.run s).run n = y.run s

theorem erases_pure {α : Type} (a : α) : Erases (pure a : StateT σ (StateT ℕ P) α) (pure a) := by
  intro s n
  simp

theorem erases_bind {α β : Type} {x : StateT σ (StateT ℕ P) α} {y : StateT σ P α}
    {f : α → StateT σ (StateT ℕ P) β} {g : α → StateT σ P β} (hx : Erases x y)
    (hf : ∀ a, Erases (f a) (g a)) : Erases (x >>= f) (y >>= g) := by
  intro s n
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, ← hx s n, bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  exact hf p.1.1 p.1.2 p.2

theorem erases_lift {α : Type} (x : P α) :
    Erases (StateT.lift (StateT.lift x) : StateT σ (StateT ℕ P) α) (StateT.lift x) := by
  intro s n
  simp

theorem erases_get : Erases (get : StateT σ (StateT ℕ P) σ) get := by
  intro s n
  simp

theorem erases_set (s' : σ) : Erases (set s' : StateT σ (StateT ℕ P) PUnit) (set s') := by
  intro s n
  simp

/-- A step of the counter that no later step reads erases. -/
theorem erases_tick {α : Type} {f : ℕ → StateT σ (StateT ℕ P) α} {y : StateT σ P α}
    (hf : ∀ c, Erases (f c) y) :
    Erases (StateT.lift (get : StateT ℕ P ℕ) >>= fun c =>
      StateT.lift (set (c + 1) : StateT ℕ P PUnit) >>= fun _ => f c) y := by
  intro s n
  simpa using hf n s (n + 1)

theorem erases_mapM {α β : Type} {f : α → StateT σ (StateT ℕ P) β} {g : α → StateT σ P β}
    (hf : ∀ a, Erases (f a) (g a)) : ∀ l : List α, Erases (l.mapM f) (l.mapM g)
  | [] => by simpa using erases_pure []
  | a :: l => by
    simp only [List.mapM_cons]
    exact erases_bind (hf a) fun b => erases_bind (erases_mapM hf l) fun bs => erases_pure _

theorem erases_batched (size : ℕ) {run : List Job → StateT σ (StateT ℕ P) (Option (List (List Bit)))}
    {run' : List Job → StateT σ P (Option (List (List Bit)))} (hr : ∀ js, Erases (run js) (run' js))
    (jobs : List Job) : Erases (batched size run jobs) (batched size run' jobs) := by
  unfold batched
  exact erases_bind (erases_mapM hr _) fun _ => erases_pure _

/-- `ceremonyOutput` keeps the erasure of its hash computations and of its runs. -/
theorem erases_ceremonyOutput
    {lift : ∀ {β : Type}, OracleComp HashSpec β → StateT σ (StateT ℕ P) β}
    {lift' : ∀ {β : Type}, OracleComp HashSpec β → StateT σ P β}
    (hl : ∀ {β : Type} (oa : OracleComp HashSpec β), Erases (lift oa) (lift' oa))
    (parameter : PublicParameter) {run : List Job → StateT σ (StateT ℕ P) (Option (List (List Bit)))}
    {run' : List Job → StateT σ P (Option (List (List Bit)))} (hr : ∀ js, Erases (run js) (run' js))
    (top : TopTree) (tree : Tree) :
    Erases (ceremonyOutput lift parameter run top tree) (ceremonyOutput lift' parameter run' top tree) := by
  cases tree with
  | top =>
    refine erases_bind (hr _) fun o => ?_
    rcases o with _ | outputs
    · exact erases_pure _
    · exact erases_bind (hl _) fun _ => erases_pure _
  | bottom b =>
    refine erases_bind (hr _) fun o => ?_
    rcases o with _ | outputs
    · exact erases_pure _
    · refine erases_bind (hl _) fun root => erases_bind (hl _) fun base => erases_bind (hl _) fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · exact erases_pure _
      · refine erases_bind (hr _) fun o => ?_
        rcases o with _ | values
        · exact erases_pure _
        · refine erases_bind (hl _) fun path => erases_bind (hl _) fun topRoot => ?_
          split_ifs
          · exact erases_pure _
          · exact erases_pure _

end Erases

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- With no fresh keys, a slot ceremony erases to `ceremonyRun` of `newTree`. -/
theorem erases_slotCeremony (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (hfresh : ∀ c, fresh c = none)
    (i : C.Party) (keys : Keys C) (jobs : List Job) :
    Erases (slotCeremony K circuits settings D fresh i keys jobs)
      (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs) := by
  unfold slotCeremony ceremonyRun
  simp only [hfresh, Option.map_none, Option.getD_none]
  exact erases_tick fun _ => erases_bind (erases_lift _) fun prss => erases_batched _ (fun js =>
    erases_bind erases_get fun p => erases_bind (erases_lift _) fun inputs => erases_bind (erases_lift _) fun out =>
      erases_bind (erases_set _) fun _ => erases_pure _) _

omit [Fintype E] [DecidableEq E] in
/-- With no fresh keys, the ceremonies of a tree are `newTree`. -/
theorem slotTree_eq (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (hfresh : ∀ c, fresh c = none)
    (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    slotTree K circuits settings D fresh i keys top tree = newTree K circuits settings i keys top tree := by
  have key := erases_ceremonyOutput
    (fun oa => erases_lift (oracleStep (tweakable oa) : PartyM C E RealSpec _)) keys.parameter
    (erases_slotCeremony K circuits settings D fresh hfresh i keys) top tree (0, 0) 0
  unfold slotTree newTree
  simp only [StateT.run'_eq, StateT.run_map, ← key, Functor.map_map]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- With no fresh keys, the program of an operator is `treeProgram`. -/
theorem slotProgram_eq (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (hfresh : ∀ c, fresh c = none)
    (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    slotProgram K circuits settings D fresh i operator tree = treeProgram K circuits settings i operator tree := by
  cases tree <;> simp only [slotProgram, treeProgram, slotTree_eq K circuits settings D fresh hfresh] <;> rfl

/-- Hybrid `0` samples no fresh keys in a slot. -/
theorem sampleSlot_zero (slot : ℕ) : sampleSlot (C := C) 0 slot = pure none := by
  simp [sampleSlot]

theorem mapM_sampleSlot_zero (start : ℕ) (l : List ℕ) :
    l.mapM (fun c => sampleSlot (C := C) 0 (start + c)) = pure (l.map fun _ => none) := by
  simp [sampleSlot_zero]

omit [Fintype E] [DecidableEq E] in
/-- A run of a tree in hybrid `0` is `treeRun`. -/
theorem hybridTreeRun_zero (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) :
    hybridTreeRun K circuits settings 0 monitor D net tree = treeRun K circuits settings monitor D net tree := by
  unfold hybridTreeRun treeRun
  have hnone : (fun c => (List.map (fun _ => (none : Option (FreshKeys C)))
      (List.range (treeSetups tree))).getD c none) = fun _ => none := by
    funext c
    simp [List.getD_eq_getElem?_getD]
  have hlift : ∀ {α : Type} (a : α),
      (StateT.lift (pure a : OracleComp (WorldSpec C) α) : RealM C net.State α) = pure a := fun a => rfl
  simp only [mapM_sampleSlot_zero, liftComp_pure, free, simulateQ_pure, hlift, pure_bind, hnone,
    slotProgram_eq K circuits settings D (fun _ => none) (fun _ => rfl)]

omit [Fintype E] [DecidableEq E] in
/-- The runs of a tree in hybrid `0` are `treeRuns`. -/
theorem hybridTreeRuns_zero (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ∀ count, hybridTreeRuns K circuits settings runLimit 0 monitor D net tree count =
      treeRuns K circuits settings runLimit monitor D net tree count
  | 0 => rfl
  | count + 1 => by
    simp only [hybridTreeRuns, treeRuns, hybridTreeRun_zero, hybridTreeRuns_zero monitor D net tree count]

omit [Fintype E] [DecidableEq E] in
/-- The signing oracles of hybrid `0` are `realOracles`. -/
theorem hybridOracles_zero (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    hybridOracles K circuits settings runLimit 0 monitor D A = realOracles K circuits settings runLimit monitor D A := by
  funext q
  cases q with
  | tree b =>
    simp only [hybridOracles, realOracles, hybridTreeRequest, treeRequest, hybridTreeRuns_zero]
    rfl
  | _ => rfl

omit [Fintype E] [DecidableEq E] in
/-- The signing phase of hybrid `0` is `dkgSigning`. -/
theorem hybridSigning_zero (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    hybridSigning K circuits settings runLimit 0 monitor D A = dkgSigning K circuits settings runLimit monitor D A := by
  simp only [hybridSigning, dkgSigning, hybridOracles_zero]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- Hybrid `0` is the game `dkgTreeGame`. -/
theorem hybridGame_zero (D : C.Coalition) (A : DkgTsigAdversary C E) :
    hybridGame K circuits settings runLimit 0 D A = dkgTreeGame K circuits settings runLimit D A := by
  simp only [hybridGame, dkgTreeGame, hybridRun, dkgTsigRun, hybridTreeRuns_zero, hybridSigning_zero]

omit [Fintype E] [DecidableEq E] in
/-- The start point of the hybrid. Hybrid `0` has the probability of the event of `UsedHitHop`. -/
theorem hybridStart (prims : Primitives) : HybridStart K circuits settings runLimit prims := by
  intro D A
  unfold hybridProb
  rw [hybridGame_zero]

end HybridStartProof

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.HybridStartProof.hybridStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.HybridStartProof.hybridStart
