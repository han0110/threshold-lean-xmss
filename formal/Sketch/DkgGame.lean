import ThresholdLeanXmss.Statement.Signing

/-!
# The signing game with the real setup

`dkgTsigGame` is the game `G^tsig` of PRAWNS, Figure 3, in which the real setup replaces the trusted
dealer. The seed generation, the top tree and each bottom tree run as the real protocols on the
network, with one adversary that plays a static coalition `D`. Each honest operator keeps its own
keys and the first output of its own runs of each tree, and it signs only with them. The four rules
of the deployment contract (`statement.tex`, Section "The deployment contract") are code of the game.

* Rule 1 is `breaksOneMessagePerKey` of `tsigOracles`.
* By rule 2, an operator uses only its own keys and its own trees.
* By rule 3, each tree has at most `runLimit` runs on the same seeds, one run at a time. The top tree
  runs again while an honest operator has no top tree. The adversary asks for each run of a bottom
  tree by `tree b`. The first signing request on a bottom tree ends its runs.
* By rule 4, the game keeps only the outputs of a run.

The game restricts the execution in four points.

* `Th` is the fixed function `prims.Th` on the inputs that the MPC evaluates, with fixed circuits.
* Each run is atomic. No signing request runs during a run of a tree.
* The coalition is static.
* Each tree has at most `runLimit` runs.

The file states three claims.

* `DkgSecurity` is the security preservation of Gurkan and others, Definition 8, with an explicit
  reduction to `tsigGame` and a fixed bound.
* `DkgCorrectness` is correctness with abort. It bounds inconsistent seeds and wrong tree outputs
  against the adversary.
* `DkgCompleteness` bounds the abort and the distance to `dealerKeyGen` of an honest run.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

/-! ## The work of one operator in the signing game -/

section Operator

variable {C : Committee} {m : Type → Type} [Monad m]

/-- The answer `none` to each query of the signing game. -/
def noAnswer : (q : TsigQuery C) → TsigSpec C q
  | .corrupt _ => none
  | .tree _ => none
  | .round1 .. => none
  | .round2 .. => none

/-- `tsigOracles` with the bottom trees `bottoms` of one operator in place of the trees of the
state. -/
def ownAnswer (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m)
    (bottoms : Fin (2 ^ layerHeight) → Option BottomTree) (q : TsigQuery C) :
    StateT (TsigState C) m (TsigSpec C q) := do
  modify fun st => { st with trees := fun b => some (bottoms b) }
  tsigOracles lift dealt q

/-- `ownAnswer` is `tsigOracles` on the state with the bottom trees of the operator. -/
theorem ownAnswer_run [LawfulMonad m] (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (dealt : Dealt C m) (bottoms : Fin (2 ^ layerHeight) → Option BottomTree) (q : TsigQuery C)
    (st : TsigState C) :
    (ownAnswer lift dealt bottoms q).run st =
      (tsigOracles lift dealt q).run { st with trees := fun b => some (bottoms b) } := by
  simp [ownAnswer]

end Operator

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The adversary -/

/-- A query of the state of the adversary, namely a read or a write. -/
inductive StateQuery (σ : Type)
  | read
  | write (state : σ)

/-- The oracle of the state of the adversary. A read gives the state, and a write sets it. -/
def StateSpec (σ : Type) : OracleSpec (StateQuery σ)
  | .read => σ
  | .write _ => Unit

/-- An adversary of the signing game with the real setup. `net` plays the corrupt operators in each
run of the setup on the network. `forge` is the forger of the signing game. Both use one state.
`forge` reads and writes it by `StateSpec`, and each run of a bottom tree continues from it. -/
structure DkgTsigAdversary (C : Committee) (E : Type) where
  net : Adversary C E Unit PEmpty PEmpty
  forge : PublicKey → TopTree → OracleComp (LocalSpec C + (TsigSpec C + StateSpec net.State)) Forgery

/-- The cost of an own call of the adversary in a run of the setup. A call of `H` or of `PRG` costs
one, and private sampling costs nothing. -/
def ownCost : (LocalSpec C).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The cost of a call of `forge`. It is `adversaryCost` of the signing game, and a read or a write
of the state costs nothing. -/
def forgeCost {σ : Type} : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain → ℕ
  | .inl t => adversaryCost (C := C) (.inl t)
  | .inr (.inl t) => adversaryCost (C := C) (.inr t)
  | .inr (.inr _) => 0

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The steps of one run of a tree, as in `TreeCompletenessStatement`. -/
def treeFuel : ℕ := setupRounds + ceremonyFuel circuits settings

/-- The most rounds of the adversary in one game, namely the seed generation and `runLimit` runs of
the top tree and of each bottom tree. -/
def dkgTsigRounds : ℕ := setupRounds + runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings

/-- The budget of an adversary, in the form of `IsQueryBounded`. Its start makes at most `start`
calls of `H` and `PRG`, each round at most `step`, and `forge` has cost at most `forge` on every
path. For the most rounds of a game, the sum is at most `q`. -/
def DkgTsigBounded (A : DkgTsigAdversary C E) (q : ℕ) : Prop :=
  ∃ start step forge : ℕ, start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q ∧
    (∀ x z, QueryCostAtMost (A.net.start x z) ownCost start) ∧
    (∀ state sent, QueryCostAtMost (A.net.round state sent) ownCost step) ∧
    (∀ pk top, QueryCostAtMost (A.forge pk top) forgeCost forge)

/-! ## The state of the operators -/

/-- The outputs that one operator holds, namely its keys, its top tree and its output of each bottom
tree. Each is the first valid output of its own runs. -/
structure OperatorState (C : Committee) where
  keys : Option (Keys C)
  top : Option TopTree
  bottom : Fin (2 ^ layerHeight) → Option BottomTree

/-- The bottom tree of a tree output. -/
def bottomOf : Option TreeOutput → Option BottomTree
  | some (.bottom tree) => some tree
  | _ => none

/-- The state of an operator after a run of `tree` with `output`. It keeps its first output. -/
def OperatorState.keep (operator : OperatorState C) (output : Option TreeOutput) : Tree → OperatorState C
  | .top => { operator with top := operator.top <|> TreeOutput.topTree output }
  | .bottom b => { operator with bottom := Function.update operator.bottom b (operator.bottom b <|> bottomOf output) }

/-- The state of the game besides the state of the signing game. It holds the state of the
adversary, the state of each operator, the runs of each tree, the bottom trees with a signing
request, and the flag of the monitors. -/
structure RealState (C : Committee) (σ : Type) where
  adversary : σ
  operators : C.Party → OperatorState C
  runs : Tree → ℕ
  closed : Fin (2 ^ layerHeight) → Bool
  flag : Bool

/-- The monad of the game after the seed generation. -/
abbrev RealM (C : Committee) (σ : Type) := StateT (RealState C σ) (OracleComp (WorldSpec C))

/-- The local oracles of the honest operators on the free copy. -/
def realLift {σ β : Type} (oa : OracleComp (RoSpec C) β) : RealM C σ β := StateT.lift (free (liftComp oa _))

/-- The keys of an operator with no output. -/
def noKeys : Keys C := ⟨0, fun _ => 0, fun _ => 0⟩

/-- The seeds of the game, namely `seed_T` at the first honest holder of `T` with keys. -/
def gameSeeds (D : C.Coalition) (keys : C.Party → Option (Keys C)) (T : C.Term) : HashOutput :=
  match C.parties.find? fun i => i ∈ C.holders T ∧ i ∉ D.1 ∧ (keys i).isSome with
  | some i => ((keys i).map (·.seed T)).getD 0
  | none => 0

/-- The parameter of the game, namely `P` at the first honest operator with keys. -/
def gameParameter (D : C.Coalition) (keys : C.Party → Option (Keys C)) : PublicParameter :=
  match C.parties.find? fun i => i ∉ D.1 ∧ (keys i).isSome with
  | some i => ((keys i).map (·.parameter)).getD 0
  | none => 0

/-- The seeds differ. Two honest holders of a term hold different seeds, two honest operators of a
pair hold different pair keys, or two honest operators hold different parameters. -/
def seedsDiffer (D : C.Coalition) (keys : C.Party → Option (Keys C)) : Bool :=
  decide (∃ i j ki kj, i ∉ D.1 ∧ j ∉ D.1 ∧ keys i = some ki ∧ keys j = some kj ∧
    (ki.parameter ≠ kj.parameter ∨ (∃ T, i ∈ C.holders T ∧ j ∈ C.holders T ∧ ki.seed T ≠ kj.seed T) ∨
      (i ≠ j ∧ ki.pairKey j ≠ kj.pairKey i)))

/-- The state after the seed generation with the outputs `keys`. The flag holds when the seeds
differ. -/
def startState {σ : Type} (D : C.Coalition) (state : σ) (keys : C.Party → Option (Keys C)) : RealState C σ :=
  ⟨state, fun i => ⟨keys i, none, fun _ => none⟩, fun _ => 0, fun _ => false, seedsDiffer D keys⟩

/-- The output of bottom tree `b` at the first honest operator that holds one. -/
def heldBottom (D : C.Coalition) (operators : C.Party → OperatorState C) (b : Fin (2 ^ layerHeight)) :
    Option BottomTree :=
  (C.parties.find? fun i => i ∉ D.1 ∧ ((operators i).bottom b).isSome).bind fun i => (operators i).bottom b

/-- The keys and the top tree of the first honest operator that holds a top tree. -/
def topHolder (D : C.Coalition) (operators : C.Party → OperatorState C) : Option (Keys C × TopTree) :=
  match C.parties.find? fun i => i ∉ D.1 ∧ (operators i).top.isSome with
  | some i => match (operators i).keys, (operators i).top with
    | some keys, some top => some (keys, top)
    | _, _ => none
  | none => none

/-- `F` on the seeds of the game. -/
def gameValue {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C) (x : Point) :
    RealM C σ Digest :=
  realLift (prfValue (gameSeeds D fun i => (operators i).keys) x)

/-! ## The runs of the trees -/

/-- A test of the outputs of the honest operators after a run of a tree, from the keys of the
operators and the tree. -/
abbrev TreeMonitor (C : Committee) :=
  (C.Party → Option (Keys C)) → Tree → (C.Party → Option TreeOutput) → OracleComp (WorldSpec C) Bool

/-- The test that never fails. -/
def noMonitor : TreeMonitor C := fun _ _ _ => pure false

/-- The test of a wrong output. An honest operator has an output that is not the output of
`referenceTree` on the seeds and the parameter of the game, with the reference top tree for a bottom
tree. -/
def wrongOutput (D : C.Coalition) : TreeMonitor C := fun keys tree outputs => do
  let seeds := gameSeeds D keys
  let parameter := gameParameter D keys
  let reference ← free (liftComp (do
    let top ← referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter emptyTop .top
    match tree, TreeOutput.topTree top with
    | .top, _ => pure top
    | .bottom b, some topTree => referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter topTree (.bottom b)
    | .bottom _, none => pure none) _)
  pure (decide (∃ i, i ∉ D.1 ∧ (outputs i).isSome ∧ outputs i ≠ reference))

/-- The program of operator `i` in a run of `tree`. It is `newTree` on its own keys and its own top
tree. An operator without them stops at once, as an operator that aborts. -/
def treeProgram (i : C.Party) (operator : OperatorState C) : Tree → PartyM C E RealSpec TreeOutput
  | .top => match operator.keys with
    | some keys => newTree K circuits settings i keys emptyTop .top
    | none => failure
  | .bottom b => match operator.keys, operator.top with
    | some keys, some top => newTree K circuits settings i keys top (.bottom b)
    | _, _ => failure

/-- One run of `tree` on the network with `net`, from the state of `net`. Each operator keeps its
first output, and the run sets the flag when `monitor` holds. -/
def treeRun (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
    s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree)
  let bad ← StateT.lift (monitor (fun i => (s.operators i).keys) tree outputs)
  let operators := fun i => (s.operators i).keep (outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad⟩ : RealState C net.State)

/-- A run of `tree` is allowed. The tree has fewer than `runLimit` runs, an honest operator has no
output of it, and a bottom tree has no signing request. -/
def mayRun {σ : Type} (D : C.Coalition) (s : RealState C σ) : Tree → Prop
  | .top => s.runs .top < runLimit ∧ ∃ i, i ∉ D.1 ∧ (s.operators i).top = none
  | .bottom b => s.closed b = false ∧ s.runs (.bottom b) < runLimit ∧
      ∃ i, i ∉ D.1 ∧ (s.operators i).bottom b = none

/-- At most `count` runs of `tree`, each while a run is allowed. -/
def treeRuns (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      treeRun K circuits settings monitor D net tree
      treeRuns monitor D net tree count

/-! ## The signing oracles of the real game -/

/-- The answer of operator `i` with its own outputs `operator` to a signing request at key `e`. It
answers only with keys, a top tree and an output of the bottom tree of `e`, and then it answers as
`tsigOracles` on its own keys and trees. -/
def operatorAnswer {m : Type → Type} [Monad m] (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (value : Point → m Digest) (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    StateT (TsigState C) m (TsigSpec C q) :=
  match operator.keys, operator.top, operator.bottom (treeOf e) with
  | some keys, some top, some _ =>
      ownAnswer lift (dealtWith lift keys.parameter (fun _ => keys) top value) operator.bottom q
  | _, _, _ => pure (noAnswer q)

/-- When operator `i` holds the keys `keys i` of one dealing, the top tree `top` and an output of the
bottom tree of `e`, its answer to `round1` and `round2` at `e` is the answer of `tsigOracles` on
`dealtWith` of that dealing, on the state with its bottom trees. -/
theorem operatorAnswer_run {m : Type → Type} [Monad m] [LawfulMonad m]
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (value : Point → m Digest)
    (operator : OperatorState C) (keys : C.Party → Keys C) (parameter : PublicParameter) (top : TopTree)
    (tree : BottomTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (st : TsigState C)
    (ownKeys : operator.keys = some (keys i)) (ownParameter : (keys i).parameter = parameter)
    (ownTop : operator.top = some top) (ownBottom : operator.bottom (treeOf e) = some tree) :
    (operatorAnswer lift value operator e (.round1 i J e message)).run st =
        (tsigOracles lift (dealtWith lift parameter keys top value) (.round1 i J e message)).run
          { st with trees := fun b => some (operator.bottom b) } ∧
      (operatorAnswer lift value operator e (.round2 i J e message parts)).run st =
        (tsigOracles lift (dealtWith lift parameter keys top value) (.round2 i J e message parts)).run
          { st with trees := fun b => some (operator.bottom b) } := by
  subst ownParameter
  simp only [operatorAnswer, ownKeys, ownTop, ownBottom, ownAnswer_run]
  constructor <;> rfl

/-- A signing request to operator `i` at key `e`. It ends the runs of the bottom tree of `e`. -/
def signRequest (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    StateT (TsigState C) (RealM C σ) (TsigSpec C q) := do
  StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
  let s ← StateT.lift get
  operatorAnswer realLift (gameValue D s.operators) (s.operators i) e q

/-- A request of bottom tree `b`. It runs the tree once if a run is allowed. It gives the output of
the first honest operator that holds one, with the opened randomizer value of the top key. -/
def treeRequest (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) : RealM C net.State (Option (BottomTree × Digest)) := do
  treeRuns K circuits settings runLimit monitor D net (.bottom b) 1
  let s ← get
  match heldBottom D s.operators b with
  | some tree => pure (some (tree, ← gameValue D s.operators (.randomizer topLayer (topKey b))))
  | none => pure none

/-- The signing oracles of the real game. `corrupt` gives nothing, `tree b` runs the real protocol,
and each honest operator answers `round1` and `round2` with its own outputs. -/
def realOracles (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => StateT.lift (treeRequest K circuits settings runLimit monitor D A.net b)
  | .round1 i J e message => signRequest D i e (.round1 i J e message)
  | .round2 i J e message parts => signRequest D i e (.round2 i J e message parts)

omit [Fintype E] [DecidableEq E] in
/-- When each honest operator `i` holds the keys `keys i` of one dealing, the top tree `top` and the
bottom trees `bottoms`, the answers of `realOracles` to `round1` and `round2` of an honest operator
at a key of a held tree are the answers of `tsigOracles` on `dealtWith` of that dealing. The real
side also ends the runs of the tree of `e`. -/
theorem realOracles_round_run (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (keys : C.Party → Keys C) (parameter : PublicParameter) (top : TopTree)
    (bottoms : Fin (2 ^ layerHeight) → Option BottomTree) (s : RealState C A.net.State) (st : TsigState C)
    (consistent : ∀ i, i ∉ D.1 → (s.operators i).keys = some (keys i) ∧ (keys i).parameter = parameter ∧
      (s.operators i).top = some top ∧ (s.operators i).bottom = bottoms)
    (i : C.Party) (honest : i ∉ D.1) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (tree : BottomTree) (held : bottoms (treeOf e) = some tree) :
    let s' : RealState C A.net.State := { s with closed := Function.update s.closed (treeOf e) true }
    let dealt := dealtWith (m := RealM C A.net.State) realLift parameter keys top (gameValue D s.operators)
    let st' : TsigState C := { st with trees := fun b => some (bottoms b) }
    ((realOracles K circuits settings runLimit monitor D A (.round1 i J e message)).run st).run s =
        ((tsigOracles (m := RealM C A.net.State) realLift dealt (.round1 i J e message)).run st').run s' ∧
      ((realOracles K circuits settings runLimit monitor D A (.round2 i J e message parts)).run st).run s =
        ((tsigOracles (m := RealM C A.net.State) realLift dealt (.round2 i J e message parts)).run st').run s' := by
  obtain ⟨ownKeys, ownParameter, ownTop, ownBottom⟩ := consistent i honest
  have own := operatorAnswer_run realLift (gameValue (σ := A.net.State) D s.operators) (s.operators i) keys
    parameter top tree i J e message parts st ownKeys ownParameter ownTop (by rw [ownBottom]; exact held)
  rw [ownBottom] at own
  constructor
  · simp [realOracles, signRequest, own.1]
  · simp [realOracles, signRequest, own.2]

/-- The key generation of the win test. It has the keys of each operator, `F` on the seeds of the
game, and the first held output of each bottom tree. -/
def canonicalDealt {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (parameter : PublicParameter) (top : TopTree) : Dealt C (RealM C σ) :=
  { dealtWith (m := RealM C σ) realLift parameter (fun i => ((operators i).keys).getD noKeys) top
      (gameValue D operators) with
    bottom := fun b => pure (heldBottom D operators b) }

/-- The signing phase. The public key is the key of the first honest operator that holds a top tree.
With no such operator, the adversary does not win. `forge` runs with `realOracles` and its state.
The coalition `D` is corrupt from the start. The win test is `forgeryWins` on `canonicalDealt`. -/
def dkgSigning (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    RealM C A.net.State Bool := do
  let s ← get
  let some (keys, top) := topHolder D s.operators | pure false
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  let (forgery, st) ← (simulateQ (forger + (realOracles K circuits settings runLimit monitor D A + cell))
    (A.forge ⟨top.root, keys.parameter⟩ top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
  let s ← get
  forgeryWins realLift (canonicalDealt D s.operators keys.parameter top) st forgery

/-! ## The game -/

/-- The run of the game. The adversary starts and then plays the seed generation, the runs of the top
tree and the signing phase, with one state. The run gives the result of the win test and the flag
of the monitors. -/
def dkgTsigRun (monitor : TreeMonitor C) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) (Bool × Bool) := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (win, s) ← (do
      treeRuns K circuits settings runLimit monitor D A.net .top runLimit
      dkgSigning K circuits settings runLimit monitor D A).run (startState D state keys)
  pure (win, s.flag)

/-- The game `G^tsig` of PRAWNS with the real setup. -/
def dkgTsigGame (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  Prod.fst <$> dkgTsigRun K circuits settings runLimit noMonitor D A

/-- The game of inconsistent seeds or a wrong output. The adversary wins if two honest operators hold
inconsistent seeds after the seed generation, or if an honest operator ends a run of a tree with an
output that is not the output of `referenceTree` on the seeds of the game. -/
def dkgTreeGame (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  Prod.snd <$> dkgTsigRun K circuits settings runLimit (wrongOutput D) D A

/-- The adversary of an honest run on the network. It sends nothing. -/
def honestNet : Adversary C E Unit PEmpty PEmpty := honestAdversary fun l => l.elim

/-- A forgery with zero entries. -/
def idleForgery : Forgery := ⟨0, ⟨⟨0, by simp [lifetime]⟩, fun _ => ⟨0, fun _ => 0, fun _ => 0⟩⟩⟩

/-- An adversary that sends nothing in the setup and outputs `idleForgery` with no call. -/
def idleAdversary : DkgTsigAdversary C E := ⟨honestNet, fun _ _ => pure idleForgery⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The idle adversary has budget `0`. -/
theorem idleAdversary_bounded :
    DkgTsigBounded circuits settings runLimit (idleAdversary (C := C) (E := E)) 0 :=
  ⟨0, 0, 0, by simp, fun _ _ => by simp [QueryCostAtMost, idleAdversary, honestNet, honestAdversary],
    fun _ _ => by simp [QueryCostAtMost, idleAdversary, honestNet, honestAdversary],
    fun _ _ => OracleComp.isQueryBound_pure _ _ _ _⟩

/-! ## The terms of the bounds -/

/-- The PRSS setups of a run of a tree. -/
def treeSetups : Tree → ℕ
  | .top => 1
  | .bottom _ => 2

/-- The searches of a randomizer of a run of a tree. -/
def treeSearches : Tree → ℕ
  | .top => 0
  | .bottom _ => 1

/-- The error of the checks of the batches of a run of `tree`, with the soundness of each check and
the birthday bound of its hashes, as in `MultVerifySecurityStatement`. -/
def treeCheckError (tree : Tree) (q : ℕ) : ℝ :=
  treeBatches settings tree *
    (checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
      (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q +
     checkHashError C (maxBatch circuits settings tupleCount) q)

/-- The error of the replacement of one run of `tree` by the dealer of the signing game. A failed
search of a bottom tree leaks openings that `tree b` of `tsigGame` does not give, and
`searchFailure` pays it as a bad event. -/
def treeRunError (tree : Tree) (q : ℕ) : ℝ :=
  treeSetups tree * (prssRealRandHashError C q + streamKeyError C) +
    treeCheckError (E := E) (C := C) circuits settings tree q + treeHybridError settings C tree q +
    treeAbortError (E := E) circuits settings tree + treeSearches tree * searchFailure

/-- The statistical error of `DkgSecurity`, for the seed generation and `runLimit` runs of the top
tree and of each bottom tree. -/
def dkgError (C : Committee) (q : ℕ) : ℝ :=
  seedGenHashError C q + derivedKeyCollision C +
    runLimit * (treeRunError (E := E) (C := C) circuits settings .top q +
      ∑ b : Fin (2 ^ layerHeight), treeRunError (E := E) (C := C) circuits settings (.bottom b) q)

/-- The calls of the reduction in `.hash` and `.prf` for one run of `tree`. They are the input terms
that the coalition holds, one `.prf` call for each term and each point, and for a bottom tree the
nodes of the codeword of the root and the randomizer search. The reduction answers each other domain
of the setup from its own table. -/
def treeSigningCalls (C : Committee) : Tree → ℕ
  | .top => (topJobs.map (·.points.length)).sum * termCount C
  | .bottom b => (((bottomJobs b).map (·.points.length)).sum + chainCount) * termCount C +
      (2 ^ (layerHeight + 1) + randomizerAttemptLimit)

/-- The calls of the reduction beyond the calls of the adversary, for `runLimit` runs of each tree.
The requests of the reduction to the oracles of `tsigGame` are `corrupt` and `tree`, which cost
nothing. -/
def dkgOverhead (C : Committee) : ℕ :=
  runLimit * (treeSigningCalls C .top + ∑ b : Fin (2 ^ layerHeight), treeSigningCalls C (.bottom b))

/-- The multi-key PRF advantage of `prgReduction` against `hiddenStreams` on `game`, as in
`CeremonySecurityStatement`. It pays the streams of the PRSS under the keys that `D` lacks. -/
def streamAdvantage (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D game)).toReal

/-- The error of a wrong output in a run of `tree`. -/
def treeWrongError (tree : Tree) (q : ℕ) : ℝ :=
  treeSetups tree * prssSetupHashError C q + treeCheckError (E := E) (C := C) circuits settings tree q +
    treeBatches settings tree * copyHashError C q

/-- The error of inconsistent seeds or a wrong output in a game. -/
def dkgWrongError (C : Committee) (q : ℕ) : ℝ :=
  seedGenHashError C q +
    runLimit * (treeWrongError (E := E) (C := C) circuits settings .top q +
      ∑ b : Fin (2 ^ layerHeight), treeWrongError (E := E) (C := C) circuits settings (.bottom b) q)

/-- The probability that an honest operator has no keys, no top tree or no output of bottom tree `b`
after the honest run. -/
def dkgAbortError (C : Committee) (b : Fin (2 ^ layerHeight)) : ℝ :=
  derivedKeyCollision C + treeAbortError (E := E) circuits settings .top +
    treeAbortError (E := E) circuits settings (.bottom b) + searchFailure

/-- The distance of the honest run of the setup and of bottom tree `b` to `dealerKeyGen`. A failed
search is in both runs, so it is not in this term. -/
def dkgCompletenessError (C : Committee) (b : Fin (2 ^ layerHeight)) : ℝ :=
  derivedKeyCollision C + treeAbortError (E := E) circuits settings .top +
    treeAbortError (E := E) circuits settings (.bottom b)

/-! ## The honest run -/

/-- The outputs of each operator after a run, namely its keys, its top tree and its output of one
bottom tree. -/
abbrev SetupOutputs (C : Committee) := C.Party → Option (Keys C) × Option TopTree × Option BottomTree

/-- The honest run of the setup and of bottom tree `b`, with no corrupt operator and with `runLimit`
runs of each tree. -/
def honestDkg (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (SetupOutputs C) := do
  let (state, keys) ← realExecution noCoalition honestNet noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (_, s) ← (do
      treeRuns K circuits settings runLimit noMonitor noCoalition honestNet .top runLimit
      treeRuns K circuits settings runLimit noMonitor noCoalition honestNet (.bottom b) runLimit).run
    (startState noCoalition state keys)
  pure fun i => ((s.operators i).keys, (s.operators i).top, (s.operators i).bottom b)

/-- `dealerKeyGen` and bottom tree `b` of its trees, at each operator. -/
def dealerDkg (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (SetupOutputs C) := do
  let some dealt ← dealerKeyGen | pure fun _ => (none, none, none)
  let bottom ← dealt.bottom b
  pure fun i => (some (dealt.keys i), some dealt.top, bottom)

/-! ## The claims -/

/-- Security preservation of the real setup (Gurkan and others, Definition 8), with an explicit
reduction and a fixed bound. For each static coalition `D` and each adversary `A` of budget `q`,
`reduction prims.aes D A` is a forger of `tsigGame` with cost at most `q + dkgOverhead C`, and it wins
`tsigGame` about as often as `A` wins `dkgTsigGame`. The claim holds for each `prims` with circuits
that compute `prims.Th`. So `reduction` can depend on the circuits and on AES, and not on `prims.Th`.

The claim adapts Definition 8 in five points. Definition 8 has one adversary on both sides and a
negligible term. Here the forger `reduction prims.aes D A` is explicit, and the bound is a function
of `q`. Definition 8 has a game with one key pair. Here the game is a threshold game with key shares,
and the bottom trees are made during the signing phase. The abort is selective, and each operator
acts on what it holds. The coalition is static, while `tsigGame` has adaptive corruption. The function
`Th` is fixed. -/
def DkgSecurity (reduction : Aes → C.Coalition → DkgTsigAdversary C E → TsigAdversary C) : Prop :=
  0 < settings.batchSize → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      (∀ pk top, QueryCostAtMost (reduction prims.aes D A pk top) adversaryCost (q + dkgOverhead runLimit C)) ∧
        accepts prims (dkgTsigGame K circuits settings runLimit D A) ≤
          accepts prims (tsigGame (reduction prims.aes D A)) + dkgError (E := E) circuits settings runLimit C q +
            streamAdvantage prims D (dkgTsigGame K circuits settings runLimit D A)

/-- Correctness with selective abort of the real setup. For each static coalition `D` and each
adversary `A` of budget `q`, two honest operators hold inconsistent seeds, or an honest operator ends
a run of a tree with a wrong output, with probability at most `dkgWrongError C q` and the PRF
advantage of the streams. An abort is no win. The claim holds for each `prims` with circuits that
compute `prims.Th`. -/
def DkgCorrectness : Prop :=
  0 < settings.batchSize → 0 < runLimit → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      accepts prims (dkgTreeGame K circuits settings runLimit D A) ≤
        dkgWrongError (E := E) circuits settings runLimit C q +
          streamAdvantage prims D (dkgTreeGame K circuits settings runLimit D A)

/-- Completeness of the real setup. The claim is about an honest run with no corrupt operator, and
about one bottom tree `b` at a time. The run makes the seeds, `runLimit` runs of the top tree and
`runLimit` runs of bottom tree `b`. Each operator holds keys, a top tree and bottom tree `b` except
with probability `dkgAbortError C b`. The claim compares the outputs of all operators with the
outputs of `dealerKeyGen`, and their distance is at most `dkgCompletenessError C b`. The claim holds
for each `prims` with circuits that compute `prims.Th`. -/
def DkgCompleteness : Prop :=
  0 < settings.batchSize → 0 < runLimit → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ b : Fin (2 ^ layerHeight),
      (Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[∃ i,
          (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none]).toReal ≤
          dkgAbortError (E := E) circuits settings C b ∧
        letI : MeasurableSpace (SetupOutputs C) := ⊤
        measureTVDist (Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b))
            (Prod.fst <$> runWorld prims (dealerDkg b)) ≤
          dkgCompletenessError (E := E) circuits settings C b

/-! ## The chain of the claims -/

omit [DecidableEq E] in
/-- `DkgSecurity` and a bound `δ` of `tsigGame` in the same world, with the fixed `Th`, give a bound
of `dkgTsigGame`. No claim of the library gives the premise `signing`. -/
theorem dkgTsigGame_le (reduction : Aes → C.Coalition → DkgTsigAdversary C E → TsigAdversary C)
    (security : DkgSecurity K circuits settings runLimit reduction) (batch : 0 < settings.batchSize)
    (prims : Primitives) (compute : CircuitsCompute circuits prims.Th) (δ : ℕ → ℝ)
    (signing : ∀ (B : TsigAdversary C) (q' : ℕ), (∀ pk top, QueryCostAtMost (B pk top) adversaryCost q') →
      accepts prims (tsigGame B) ≤ δ q')
    (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    accepts prims (dkgTsigGame K circuits settings runLimit D A) ≤
      δ (q + dkgOverhead runLimit C) + dkgError (E := E) circuits settings runLimit C q +
        streamAdvantage prims D (dkgTsigGame K circuits settings runLimit D A) := by
  obtain ⟨cost, bound⟩ := security batch prims compute D A q bounded
  linarith [signing _ _ cost]

end ThresholdLeanXmss.Sketch
