import ThresholdLeanXmss.Statement.Theorems
import ThresholdLeanXmssSecurity.Proof.StreamWorld
import ThresholdLeanXmssSecurity.Proof.SeedGenAlias

/-!
# The games of the hops of `dkgSecurityPreservation`

The games between `dkgTsigGame` and `tsigGame (dkgReduction …)`, as programs of the world.

* `refGame` is the real game with the answers of a dealer on the seeds of the game. The dealer gives
  the public key and the top tree of `forge`, the answer of `tree b`, the signing answers and the win
  test. The runs of the trees are the real runs.
* `dealtGame m` has the seed generation of the simulator with the keys of `prawnsKeyGen`
  (`worldSeedGen`) and then the same rest. The mode `m` says if a bottom tree runs only after a
  search of the dealer that succeeds, and how many first runs of each tree are emulated runs with the
  shifted building blocks of `DkgReduction.lean`.
* `tableNet` and `tableRest` are the adversary and the distinguisher of the seed generation claim
  with a private table for each cell outside the class of the seed generation.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-- The probability that a game gives `true` in `streamWorld`, from the empty caches. -/
def streamAccepts (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr{let r ← (simulateQ (streamWorld prims D) game).run (∅, ∅)}[r.1 = true]).toReal

/-- The mode of the rest of a game. With `skip`, bottom tree `b` runs only when the search of the
dealer for `b` succeeds. Run number `r` of `tree` is an emulated run when `r < emulated tree`. -/
structure Mode where
  skip : Bool
  emulated : Tree → ℕ

/-- The mode of the real runs. -/
def Mode.real : Mode := ⟨false, fun _ => 0⟩

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The dealer of the world -/

/-- The dealer on the parameter `parameter`, the seeds `seeds` and the keys `dealt`, with its top
tree from `referenceTree`, as `dealerKeyGenWith` builds it. -/
def worldDealer {σ : Type} (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) : RealM C σ (Dealt C (RealM C σ)) := do
  let value : Point → RealM C σ Digest := fun x => realLift (prfValue seeds x)
  let output ← referenceTree (fun oa => realLift (tweakable oa)) value parameter emptyTop .top
  pure (dealtWith realLift parameter dealt ((TreeOutput.topTree output).getD emptyTop) value)

/-- The answer of the dealer to `tree b`, with no state, as `tsigOracles` gives it. -/
def dealerTree {σ : Type} (dealer : Dealt C (RealM C σ)) (b : Fin (2 ^ layerHeight)) :
    RealM C σ (Option (BottomTree × Digest)) := do
  let some tree ← dealer.bottom b | pure none
  pure (some (tree, ← dealer.value (.randomizer topLayer (topKey b))))

/-! ## The runs -/

/-- One emulated run of `tree` in the world, as `emulatedRun` of `DkgReduction.lean`. The emulated
operator `i` has the keys `emu i` and the kept outputs of operator `i`. -/
def worldEmulatedRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (emu : C.Party → Option (Keys C)) (openings : List (List (List Bit))) (randomizer : Randomizer)
    (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  let buildingBlocks := shiftedBuildingBlocks K circuits settings D (gameParameter D emu) (gameSeeds D emu) openings
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality
    (treeFuel circuits settings) s.adversary fun i =>
      emulatedProgram K circuits settings buildingBlocks randomizer i
        ⟨emu i, (s.operators i).top, (s.operators i).bottom⟩ tree)
  let operators := fun i => (s.operators i).keep (outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag⟩ : RealState C net.State)

/-- One run of `tree` in the mode `m`. An emulated run takes its openings and its randomizer from the
dealer. An emulated run of a bottom tree with a failed search of the dealer does nothing. -/
def secRun (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  if s.runs tree < m.emulated tree then do
    let dealer ← worldDealer (σ := net.State) parameter seeds dealt
    match tree with
    | .top => worldEmulatedRun K circuits settings D net emu (topLeak settings dealer.top) 0 .top
    | .bottom b => do
      let answer ← dealerTree dealer b
      match answer with
      | some (bottom, ρ) =>
          worldEmulatedRun K circuits settings D net emu (bottomLeak settings b bottom ρ)
            bottom.topSignature.randomizer (.bottom b)
      | none => pure ()
  else treeRun K circuits settings noMonitor D net tree

/-- At most `count` runs of `tree` in the mode `m`, each while a run is allowed, as `treeRuns`. -/
def secRuns (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) : ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      secRun K circuits settings m D net parameter seeds dealt emu tree
      secRuns m D net parameter seeds dealt emu tree count

/-! ## The signing phase with the answers of the dealer -/

/-- A request of bottom tree `b`, as `emulatedTreeRequest`. The dealer answers first. In the mode
`skip` the tree runs only when the dealer gave a tree. The answer is the output of the first honest
holder with the randomizer value of the dealer. -/
def secTreeRequest (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (dealer : Dealt C (RealM C net.State)) (b : Fin (2 ^ layerHeight)) :
    StateT (TsigState C) (RealM C net.State) (Option (BottomTree × Digest)) := do
  let answer : Option (BottomTree × Digest) ← tsigOracles realLift dealer (.tree b)
  if m.skip = false ∨ answer.isSome then
    StateT.lift (secRuns K circuits settings runLimit m D net parameter seeds dealt emu (.bottom b) 1)
  let s ← StateT.lift get
  match heldBottom D s.operators b, answer with
  | some tree, some (_, ρ) => pure (some (tree, ρ))
  | _, _ => pure none

/-- A signing request to operator `i` at key `e`, as `emulatedSignRequest`. It ends the runs of the
bottom tree of `e`. An operator with keys, a top tree and an output of the bottom tree of `e` answers
with the oracle of the dealer. -/
def secSignRequest {σ : Type} (dealer : Dealt C (RealM C σ)) (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    StateT (TsigState C) (RealM C σ) (TsigSpec C q) := do
  StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
  let s ← StateT.lift get
  match (s.operators i).keys, (s.operators i).top, (s.operators i).bottom (treeOf e) with
  | some _, some _, some _ => tsigOracles realLift dealer q
  | _, _, _ => pure (noAnswer q)

/-- The signing oracles with the answers of the dealer, as `forgeOracles`. -/
def secOracles (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (dealer : Dealt C (RealM C net.State)) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => secTreeRequest K circuits settings runLimit m D net parameter seeds dealt emu dealer b
  | .round1 i J e message => secSignRequest dealer i e (.round1 i J e message)
  | .round2 i J e message parts => secSignRequest dealer i e (.round2 i J e message parts)

/-- The signing phase with the answers of the dealer. With no honest holder of a top tree the
adversary does not win. `forge` gets the public key and the top tree of the dealer, and the win test
is `forgeryWins` on the dealer. -/
def secSigning (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) : RealM C A.net.State Bool := do
  let s ← get
  match topHolder D s.operators with
  | none => pure false
  | some _ => do
    let dealer ← worldDealer (σ := A.net.State) parameter seeds dealt
    let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
      fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
    let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
      match q with
      | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
      | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
    let (forgery, st) ← (simulateQ
      (forger + (secOracles K circuits settings runLimit m D A.net parameter seeds dealt emu dealer + cell))
      (A.forge ⟨dealer.top.root, dealer.parameter⟩ dealer.top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
    forgeryWins realLift dealer st forgery

/-- The rest of a game after the seed generation, namely the runs of the top tree and the signing
phase, in the mode `m`. -/
def secRest (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) : RealM C A.net.State Bool := do
  secRuns K circuits settings runLimit m D A.net parameter seeds dealt emu .top runLimit
  secSigning K circuits settings runLimit m D A parameter seeds dealt emu

/-- The rest of the game with real runs, from the state of the adversary and the keys of the honest
operators after a seed generation. The dealer has the seeds and the parameter of the game. -/
def restOf (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) : OracleComp (WorldSpec C) Bool :=
  (secRest K circuits settings runLimit Mode.real D A (gameParameter D keys) (gameSeeds D keys)
    (fun i => (keys i).getD noKeys) fun _ => none).run' (startState D state keys)

/-! ## The games -/

/-- The real game with the answers of the dealer on the seeds of the game. -/
def refGame (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  restOf K circuits settings runLimit D A state keys

/-- The seed generation of the simulator in the world, with the keys of `prawnsKeyGen`. It is
`idealExecution` of `FseedGen` with `seedGenSimulator`, and it also gives the parameter, the seeds
and the keys of the dealer and the keys of the emulated operators. The emulated operators run
`seedGenWith` on fresh parts. The cells of `P`, of each seed with a corrupt holder and of each pair
key with one corrupt operator get the values of the dealer. -/
def worldSeedGen (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    OracleComp (WorldSpec C)
      (net.State × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))) := do
  let (state, early) ← observe (net.start (corruptInputs D fun _ => ()) [])
  let (parameter, seeds, dealt) ← free (liftComp (prawnsKeyGen (C := C)) _)
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D net noFunctionality state steps).run
  let log := early ++ calls
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
  let high ← free (liftComp ($ᵗ HashOutput) _)
  let _ ← program (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view (firstHonest (C.holders T)) k).term T)) ((dealt j).seed T)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]) ((dealt j).pairKey i)
    else pure true
  let ((state, keys), _) ← (executeRounds observedRoles D net noFunctionality (setupRounds - 1) state steps).run
  pure (state, parameter, seeds, dealt, keys)

/-- The game with the keys of the dealer in the mode `m`, with the parameter, the seeds and the keys
of the dealer and the keys of the emulated operators. An honest operator holds the key of the dealer
when its emulated operator ends the seed generation with keys. -/
def dealtRun (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C)
      (Bool × PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) × (C.Party → Option (Keys C))) := do
  let (state, parameter, seeds, dealt, emu) ← worldSeedGen D A.net
  let keys := fun i => (emu i).map fun _ => dealt i
  let win ← (secRest K circuits settings runLimit m D A parameter seeds dealt emu).run' (startState D state keys)
  pure (win, parameter, seeds, dealt, emu)

/-- The game with the keys of the dealer in the mode `m`. -/
def dealtGame (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool :=
  (·.1) <$> dealtRun K circuits settings runLimit m D A

/-! ## The adversary and the distinguisher with a private table -/

/-- A cell of the class of the seed generation. -/
def isSeedGenQuery : Query C → Bool
  | .commit .seedGen _ _ _ => true
  | .derive .seedGen _ _ => true
  | .sharedKeys .seedGen _ => true
  | _ => false

/-- The local oracles with a private table. A call of `H` in the class of the seed generation and
each sampling go to the outer oracles. Each other call of `H` and each call of `PRG` get their answer
from the table, with `Th` on the inputs of the MPC. -/
def tableLocal (prims : Primitives) : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (LocalSpec C))) :=
  fun t => match t with
  | .inl n => StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl n)))
  | .inr (.inl q) =>
      if isSeedGenQuery q then StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))
      else StateT.mk fun s => liftComp ((hashAnswer prims q).run s) (LocalSpec C)
  | .inr (.inr x) => StateT.mk fun s => liftComp ((prgAnswer prims x).run s) (LocalSpec C)

/-- The adversary `net` with a private table in its state. -/
def tableNet (prims : Primitives) (net : Adversary C E Unit PEmpty PEmpty) : Adversary C E Unit PEmpty PEmpty where
  State := net.State × HashCache C
  start x z := (simulateQ (tableLocal prims) (net.start x z)).run ∅
  round st sent := do
    let ((state, out), table) ← (simulateQ (tableLocal prims) (net.round st.1 sent)).run st.2
    pure ((state, table), out)
  answer _ l := l.elim

/-- The world on a private table and a private table of the hidden streams, over the outer local
oracles. Both copies use `tableLocal`. A free stream under a hidden name is a lazy uniform table. A
programming query gives `false`. -/
def tableWorld (prims : Primitives) (D : C.Coalition) :
    QueryImpl (WorldSpec C) (StateT (HashCache C × HiddenCache C) (OracleComp (LocalSpec C))) := fun t =>
  let onTable := fun {α : Type} (m : StateT (HashCache C) (OracleComp (LocalSpec C)) α) =>
    (StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> m.run st.1 :
      StateT (HashCache C × HiddenCache C) (OracleComp (LocalSpec C)) α)
  match t with
  | .inl (.inl t) => onTable (tableLocal prims t)
  | .inl (.inr _) => pure false
  | .inr (.inr (.inr x)) =>
      if Hidden D x.1 then StateT.mk fun st => (fun r => (r.1, (st.1, r.2))) <$>
        liftComp (((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle ((x.1, x.2.1), x.2.2)).run st.2)
          (LocalSpec C)
      else onTable (tableLocal prims (.inr (.inr x)))
  | .inr t => onTable (tableLocal prims t)

/-- The distinguisher of the seed generation claim. It runs the rest of the game with real runs on
the private table of `tableNet` and a fresh table of the hidden streams. -/
def tableRest (prims : Primitives) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Distinguisher C (tableNet prims A.net).State (Keys C) := fun r =>
  (simulateQ (tableWorld prims D) (restOf K circuits settings runLimit D A r.1.1 r.2)).run' (r.1.2, ∅)

end ThresholdLeanXmssSecurity.DkgSecurityProof
