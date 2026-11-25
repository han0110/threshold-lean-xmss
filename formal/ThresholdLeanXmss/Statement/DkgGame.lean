import ThresholdLeanXmss.Statement.Execution
import ThresholdLeanXmss.Statement.Signing

/-!
# The signing game with the real setup

`dkgTsigGame` is the game `G^tsig` of PRAWNS, Figure 3, in which the real setup replaces the trusted
dealer. The seed generation, the top tree and each bottom tree run as the real protocols on the
network, with one adversary that plays a static coalition `D`. Each honest operator keeps its own
keys and the first output of its own runs of each tree, and it signs only with them. The four rules
of the deployment contract (`statement.tex`) are code of the game.

* Rule 1 is `breaksOneMessagePerKey` of `tsigOracles`.
* By rule 2, an operator uses only its own keys and its own trees.
* By rule 3, each tree has at most `runLimit` runs on the same seeds, one run at a time. The top tree
  runs again while an honest operator has no top tree. The adversary asks for each run of a bottom
  tree by `tree b`. The first signing request on a bottom tree ends its runs.
* By rule 4, the game keeps only the outputs of a run.

The seed generation and each whole run of a tree end with one vote on a broadcast channel
(`voteRound`). An operator keeps its output only if the vote of each operator equals its own vote.
So each honest operator keeps its own output of that run, or each honest operator discards it. This
is the delivery clause of security with unanimous abort (Goldwasser and Lindell, ePrint 2002/040,
Definition 3). The claims of this project are games, and they do not state the comparison of that
paper between a real and an ideal execution.

* The broadcast of the status after the end of a protocol with abort is in Section 1.5 of that
  paper.
* An honest operator sends a hash of its public result when its run gives an output, and `abort`
  when it gives none. The vote says yes exactly when each operator has a vote and all votes are one
  message that is not `abort`. No source.
* A run of a bottom tree has two ceremonies and one vote. A veto of a run leaves the outputs of
  earlier runs in place. No source.
* Each corrupt receiver sees the vote of each honest operator, also in a run that the vote
  discards.

The game restricts the execution in four points.

* `Th` is the fixed function `prims.Th` on the inputs that the MPC evaluates, with fixed circuits.
* Each run is atomic. No signing request runs during a run of a tree.
* The coalition is static.
* Each tree has at most `runLimit` runs.

`dkgTreeGame` is the same run with a monitor of wrong outputs. `honestDkg` is the honest run with no
corrupt operator, and `dealerDkg` is the trusted dealer at its place. `DkgErrors.lean` holds the
error terms, and `Dkg.lean` holds the claims on these games.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

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

/-- The steps of one run of a tree on the network, namely `ceremonyFuel` and the rounds of the
second PRSS setup of a bottom tree. -/
def treeFuel : ℕ := setupRounds + ceremonyFuel circuits settings

/-- The most rounds of the adversary in one game, namely the seed generation and `runLimit` runs of
the top tree and of each bottom tree, each with its vote round. -/
def dkgTsigRounds : ℕ :=
  setupRounds + (1 + runLimit * (1 + 2 ^ layerHeight) * (treeFuel circuits settings + 1))

/-- The budget of an adversary, as a count of its calls. Its start makes at most `start`
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

/-! ## The vote at the end of a setup ceremony -/

/-- The split of the honest operators. One honest operator keeps an output and another keeps none. -/
def split {α : Type} (D : C.Coalition) (kept : C.Party → Option α) : Bool :=
  decide (∃ i j, i ∉ D.1 ∧ j ∉ D.1 ∧ (kept i).isSome ∧ (kept j).isNone)

/-- The vote of each operator on the broadcast channel. An honest operator has the one vote
`honest j` for all receivers. The vote of a corrupt operator `j` is the message `sent j j` of the
round of the adversary, one message for all receivers. -/
def broadcast (D : C.Coalition) (honest : C.Party → Msg E) (sent : C.Party → C.Party → Option (Msg E))
    (j : C.Party) : Option (Msg E) :=
  if j ∈ D.1 then sent j j else some (honest j)

/-- The decision of the vote. All votes are one vote that is not `abort`. -/
def decision (votes : C.Party → Option (Msg E)) : Bool :=
  decide (∃ v, v ≠ Msg.abort ∧ ∀ j, votes j = some v)

/-- The outputs after the vote. `true` gives the outputs as they are, and `false` gives no output
to each operator. -/
def committed {α : Type} (ok : Bool) (outputs : C.Party → Option α) (i : C.Party) : Option α :=
  if ok then outputs i else none

/-- The vote round after a ceremony, for the roles of the game and of the forger. `input i` is the
hash input of the public result of operator `i`, with no input when its ceremony gave no output.

* Each honest operator with an input hashes it and sends the hash. Each other honest operator sends
  `abort`.
* The adversary is rushing. It receives the vote of each honest operator at each corrupt receiver,
  and then it gives the messages of the corrupt operators for the round.
* The result is the decision, which all operators share. -/
def voteRound {m : Type → Type} [Monad m] (Ro : Roles C m) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (input : C.Party → Option (Query C)) :
    m (net.State × Bool) := do
  let honest ← OverPermutation.sequenceFin fun j => match input j with
    | some q => if j ∈ D.1 then pure Msg.abort else
        Ro.honest ((fun h => Msg.hashes [h]) <$> liftComp (hashQuery q) _)
    | none => pure Msg.abort
  let (state, sent) ← Ro.adversary (net.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then some (honest i) else none)
  pure (state, decision (broadcast D honest sent))

/-- The hash input of the vote of the seed generation, namely the public parameter. -/
def seedVote (keys : Keys C) : Query C := .vote 0 0 [bitsOfDigest keys.parameter]

/-- The hash input of the vote of a tree, namely its index and the digests of its public output in
the order of its jobs. A bottom tree also has the signature of its root. The last case is not
reached by an honest operator, because a run of the top tree gives an output of the top tree and a
run of a bottom tree gives an output of a bottom tree. -/
def treeVote : Tree → TreeOutput → Query C
  | .top, .top tree => .vote 1 0 ((topJobs.map fun job => match job.kind with
      | .chainEnd e l => bitsOfDigest (tree.chainEnd e l)
      | _ => []) ++ [bitsOfDigest tree.root])
  | .bottom b, .bottom tree => .vote 2 b.val (((bottomJobs b).map fun job => match job.kind with
      | .chainRow e l =>
          bitsOfDigest (tree.cpk e l).1 ++ bitsOfDigest (tree.cpk e l).2.1 ++ bitsOfDigest (tree.cpk e l).2.2
      | .commitment e => bitsOfDigest (tree.commitment e)
      | _ => []) ++ [bitsOfDigest tree.root, bitsOfDigest tree.topSignature.randomizer] ++
      ((List.finRange chainCount).map fun l => bitsOfDigest (tree.topSignature.chainValues l)) ++
      ((List.finRange layerHeight).map fun k => bitsOfDigest (tree.topSignature.authenticationPath k)))
  | _, _ => .vote 3 0 []

/-- The state after the seed generation and its vote `ok`. The operators keep the keys after the
vote. The flag holds when the seeds of the seed generation differ, also when the vote discards them,
or when the keys after the vote have a split. -/
def seedState {σ : Type} (D : C.Coalition) (state : σ) (keys : C.Party → Option (Keys C)) (ok : Bool) :
    RealState C σ :=
  { startState D state (committed ok keys) with flag := seedsDiffer D keys || split D (committed ok keys) }

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

/-- One run of `tree` on the network with `net`, from the state of `net`, and its vote. Each
operator keeps its first output after the vote. The run sets the flag when `monitor` holds on the
outputs of the ceremony, also when the vote discards them, or when the outputs after the vote have a
split. -/
def treeRun (monitor : TreeMonitor C) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
    s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree)
  let bad ← StateT.lift (monitor (fun i => (s.operators i).keys) tree outputs)
  let (state, ok) ← StateT.lift (voteRound worldRoles D net state fun i => (outputs i).map (treeVote tree))
  let kept := committed ok outputs
  let operators := fun i => (s.operators i).keep (kept i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad || split D kept⟩ : RealState C net.State)

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
  let (state, ok) ← voteRound worldRoles D A.net state fun i => (keys i).map seedVote
  let (win, s) ← (do
      treeRuns K circuits settings runLimit monitor D A.net .top runLimit
      dkgSigning K circuits settings runLimit monitor D A).run (seedState D state keys ok)
  pure (win, s.flag)

/-- The game `G^tsig` of PRAWNS with the real setup. -/
def dkgTsigGame (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  Prod.fst <$> dkgTsigRun K circuits settings runLimit noMonitor D A

/-- The game of inconsistent seeds, a wrong output or a split. The adversary wins if two honest
operators hold inconsistent seeds after the seed generation, or if an honest operator ends a run of
a tree with an output that is not the output of `referenceTree` on the seeds of the game. Both tests
take the outputs of the ceremony, so they also see an output that the vote discards. The adversary
also wins if one honest operator keeps the output of the seed generation or of a run of a tree after
its vote and another honest operator keeps none. The vote excludes this last event on each path. -/
def dkgTreeGame (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  Prod.snd <$> dkgTsigRun K circuits settings runLimit (wrongOutput D) D A

/-- The adversary of an honest run on the network. It sends nothing. -/
def honestNet : Adversary C E Unit PEmpty PEmpty := honestAdversary fun l => l.elim

/-! ## The honest run -/

/-- The outputs of each operator after a run, namely its keys, its top tree and its output of one
bottom tree. -/
abbrev SetupOutputs (C : Committee) := C.Party → Option (Keys C) × Option TopTree × Option BottomTree

/-- The honest run of the setup and of bottom tree `b`, with no corrupt operator and with at most
`runLimit` runs of each tree. -/
def honestDkg (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (SetupOutputs C) := do
  let (state, keys) ← realExecution noCoalition honestNet noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (state, ok) ← voteRound worldRoles noCoalition honestNet state fun i => (keys i).map seedVote
  let (_, s) ← (do
      treeRuns K circuits settings runLimit noMonitor noCoalition honestNet .top runLimit
      treeRuns K circuits settings runLimit noMonitor noCoalition honestNet (.bottom b) runLimit).run
    (seedState noCoalition state keys ok)
  pure fun i => ((s.operators i).keys, (s.operators i).top, (s.operators i).bottom b)

/-- `dealerKeyGen` and bottom tree `b` of its trees, at each operator. -/
def dealerDkg (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (SetupOutputs C) := do
  let some dealt ← dealerKeyGen | pure fun _ => (none, none, none)
  let bottom ← dealt.bottom b
  pure fun i => (some (dealt.keys i), some dealt.top, bottom)

end ThresholdLeanXmss
