import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Record

/-!
# The rest of a game with the shared bad event

A run sets the flag of the game when `PassBad` holds, when a hidden key of the run has a stream cell
from before the run (`ReusedBefore`), or when the world has a global event after the run. The flag
starts as `seedsDiffer`.

`sharedRest` is the rest of a game after the seed generation with recorded runs and this flag. It is
generic in the handler of the world, so that it runs in `loggedWorld` for the games and on the
private table for the distinguisher of the seed generation. With `own` it has the signing oracles
and the win test of the real game, and with no `own` those of the dealer, in the mode of
`Games.lean`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The rest of a game with the shared event -/

section Rest

variable {M : Type → Type} [Monad M] {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W M))
  (view : W → StreamState C)

/-- The monad of a game with the shared event, over a world with the state `W`. -/
abbrev SharedM (C : Committee) (M : Type → Type) (W σ : Type) := StateT (RealState C σ) (StateT W M)

/-- A computation of the world in the game. -/
def inWorld {σ β : Type} (oa : OracleComp (WorldSpec C) β) : SharedM C M W σ β :=
  StateT.lift (simulateQ impl oa)

/-- The local oracles of the honest operators on the free copy. -/
def sharedLift {σ β : Type} (oa : OracleComp (RoSpec C) β) : SharedM C M W σ β :=
  inWorld impl (free (liftComp oa _))

/-- The dealer, as `worldDealer`. -/
def sharedDealer {σ : Type} (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) : SharedM C M W σ (Dealt C (SharedM C M W σ)) := do
  let value : Point → SharedM C M W σ Digest := fun x => sharedLift impl (prfValue seeds x)
  let output ← referenceTree (fun oa => sharedLift impl (tweakable oa)) value parameter emptyTop .top
  pure (dealtWith (sharedLift impl) parameter dealt ((TreeOutput.topTree output).getD emptyTop) value)

/-- One recorded run of `tree` with the programs `program`. It sets the flag for a bad check, a
reused hidden key or a global event after the run. -/
def sharedRunWith (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (program : C.Party → RecM C E TreeOutput) (tree : Tree) : SharedM C M W net.State Unit := do
  let s ← get
  let before ← StateT.lift (view <$> get)
  let (state, steps) ← inWorld impl (executePhaseR worldRoles D net noFunctionality ([] : Record C E)
    (treeFuel circuits settings) s.adversary fun i => (program i).run.run)
  let after ← StateT.lift (view <$> get)
  let records := fun i => (steps i).record []
  let bad := decide (PassBad K D records ∨ ReusedBefore D before.2 records ∨ GlobalEvent after)
  let operators := fun i => (s.operators i).keep (steps i).output tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad⟩ : RealState C net.State)

/-- One run of `tree` in the mode `m`, as `secRun`, with its record. -/
def sharedRun (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) : SharedM C M W net.State Unit := do
  let s ← get
  if s.runs tree < m.emulated tree then do
    let dealer ← sharedDealer impl (σ := net.State) parameter seeds dealt
    match tree with
    | .top =>
        sharedRunWith K circuits settings impl view D net (fun i =>
          passTree K circuits settings
            (shiftedShares circuits D (gameParameter D emu) (gameSeeds D emu) (topLeak settings dealer.top)) (some 0) i
            ⟨emu i, (s.operators i).top, (s.operators i).bottom⟩ .top) .top
    | .bottom b => do
      let some bottom ← dealer.bottom b | pure ()
      let ρ ← dealer.value (.randomizer topLayer (topKey b))
      sharedRunWith K circuits settings impl view D net (fun i =>
        passTree K circuits settings
          (shiftedShares circuits D (gameParameter D emu) (gameSeeds D emu) (bottomLeak settings b bottom ρ))
          (some bottom.topSignature.randomizer) i ⟨emu i, (s.operators i).top, (s.operators i).bottom⟩ (.bottom b))
        (.bottom b)
  else
    sharedRunWith K circuits settings impl view D net (fun i =>
      passTree K circuits settings plainShares none i (s.operators i) tree) tree

/-- At most `count` runs of `tree`, each while a run is allowed. -/
def sharedRuns (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) : ℕ → SharedM C M W net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      sharedRun K circuits settings impl view m D net parameter seeds dealt emu tree
      sharedRuns m D net parameter seeds dealt emu tree count

/-- The signing oracles of the real game, as `realOracles`, with recorded runs. -/
def sharedOwnOracles (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (SharedM C M W net.State)) := fun q =>
  let value := fun (operators : C.Party → OperatorState C) (x : Point) =>
    (sharedLift impl (prfValue (gameSeeds D fun i => (operators i).keys) x) : SharedM C M W net.State Digest)
  let sign := fun (i : C.Party) (e : KeyIndex) (q : TsigQuery C) =>
    (do
      StateT.lift (modify fun s : RealState C net.State =>
        { s with closed := Function.update s.closed (treeOf e) true })
      let s ← StateT.lift get
      operatorAnswer (sharedLift impl) (value s.operators) (s.operators i) e q :
        StateT (TsigState C) (SharedM C M W net.State) (TsigSpec C q))
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => StateT.lift (do
      sharedRuns K circuits settings runLimit impl view m D net parameter seeds dealt emu (.bottom b) 1
      let s ← get
      match heldBottom D s.operators b with
      | some tree => pure (some (tree, ← value s.operators (.randomizer topLayer (topKey b))))
      | none => pure none)
  | .round1 i J e message => sign i e (.round1 i J e message)
  | .round2 i J e message parts => sign i e (.round2 i J e message parts)

/-- The signing oracles with the answers of the dealer, as `secOracles`, with recorded runs. -/
def sharedDealerOracles (m : Mode) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (dealer : Dealt C (SharedM C M W net.State)) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (SharedM C M W net.State)) := fun q =>
  let sign := fun (i : C.Party) (e : KeyIndex) (q : TsigQuery C) =>
    (do
      StateT.lift (modify fun s : RealState C net.State =>
        { s with closed := Function.update s.closed (treeOf e) true })
      let s ← StateT.lift get
      match (s.operators i).keys, (s.operators i).top, (s.operators i).bottom (treeOf e) with
      | some _, some _, some _ => tsigOracles (sharedLift impl) dealer q
      | _, _, _ => pure (noAnswer q) : StateT (TsigState C) (SharedM C M W net.State) (TsigSpec C q))
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => do
      let answer : Option (BottomTree × Digest) ← tsigOracles (sharedLift impl) dealer (.tree b)
      if m.skip = false ∨ answer.isSome then
        StateT.lift (sharedRuns K circuits settings runLimit impl view m D net parameter seeds dealt emu (.bottom b) 1)
      let s ← StateT.lift get
      match heldBottom D s.operators b, answer with
      | some tree, some (_, ρ) => pure (some (tree, ρ))
      | _, _ => pure none
  | .round1 i J e message => sign i e (.round1 i J e message)
  | .round2 i J e message parts => sign i e (.round2 i J e message parts)

/-- The signing phase with the shared event. With `own` it is `dkgSigning`, and with no `own` it is
`secSigning`. -/
def sharedSigning (own : Bool) (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) : SharedM C M W A.net.State Bool := do
  let s ← get
  match topHolder D s.operators with
  | none => pure false
  | some (keys, top) => do
    let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (SharedM C M W A.net.State)) :=
      fun t => StateT.lift (inWorld impl (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
    let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (SharedM C M W A.net.State)) := fun q =>
      match q with
      | .read => StateT.lift ((·.adversary) <$> (get : SharedM C M W A.net.State _))
      | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
    if own then do
      let (forgery, st) ← (simulateQ
        (forger + (sharedOwnOracles K circuits settings runLimit impl view m D A.net parameter seeds dealt emu + cell))
        (A.forge ⟨top.root, keys.parameter⟩ top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
      let s ← get
      let value : Point → SharedM C M W A.net.State Digest := fun x =>
        sharedLift impl (prfValue (gameSeeds D fun i => (s.operators i).keys) x)
      forgeryWins (sharedLift impl)
        { dealtWith (m := SharedM C M W A.net.State) (sharedLift impl) keys.parameter
            (fun i => ((s.operators i).keys).getD noKeys) top value with
          bottom := fun b => pure (heldBottom D s.operators b) } st forgery
    else do
      let dealer ← sharedDealer impl (σ := A.net.State) parameter seeds dealt
      let (forgery, st) ← (simulateQ
        (forger + (sharedDealerOracles K circuits settings runLimit impl view m D A.net parameter seeds dealt emu
          dealer + cell))
        (A.forge ⟨dealer.top.root, dealer.parameter⟩ dealer.top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
      forgeryWins (sharedLift impl) dealer st forgery

/-- The rest of a game with the shared event, from the state `start`. It gives the result of the win
test and the flag. -/
def sharedRest (own : Bool) (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (start : RealState C A.net.State) : StateT W M (Bool × Bool) := do
  let (win, s) ← (do
      sharedRuns K circuits settings runLimit impl view m D A.net parameter seeds dealt emu .top runLimit
      sharedSigning K circuits settings runLimit impl view own m D A parameter seeds dealt emu).run start
  pure (win, s.flag)

/-- The rest with real runs after a seed generation with the keys `keys`, as `restOf`. -/
def sharedRestOf (own : Bool) (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) : StateT W M (Bool × Bool) :=
  sharedRest K circuits settings runLimit impl view own Mode.real D A (gameParameter D keys) (gameSeeds D keys)
    (fun i => (keys i).getD noKeys) (fun _ => none) (startState D state keys)

end Rest

end ThresholdLeanXmssSecurity.DkgSecurityProof
