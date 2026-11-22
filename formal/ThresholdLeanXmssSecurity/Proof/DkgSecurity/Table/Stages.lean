import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.DealerFirstForger

/-!
# The two stages of `DealerFirstForger`

`givenDealerGame` is `dealerFirstGame` with the dealer of the first top tree passed to each run and to
the signing phase in the place of `worldDealer`.

* `ReplayStage` states that `dealerFirstGame` and `givenDealerGame` win with the same probability. The
  two games differ only in a computation of the dealer again, from a cache that holds its first run.
* `StructureStage` states that `givenDealerGame` wins at most as often as `forgerWorldGame`. The two
  games differ in the bottom tree of the dealer that a run computes again, the log of the calls of
  `A`, the corruption calls, the keys of the start state, the order of the state layers and the branch
  with no top holder.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

/-- One run of `tree` in the mode `m`, as `secRun`, with the dealer `dealer` in the place of
`worldDealer`. -/
def secRunD (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  if s.runs tree < m.emulated tree then do
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

/-- `secRuns` with the dealer `dealer`. -/
def secRunsD (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) (tree : Tree) : ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      secRunD K circuits settings D m net dealer emu tree
      secRunsD m net dealer emu tree count

/-- `secTreeRequest` with the dealer `dealer` also in the runs. -/
def secTreeRequestD (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) :
    StateT (TsigState C) (RealM C net.State) (Option (BottomTree × Digest)) := do
  let answer : Option (BottomTree × Digest) ← tsigOracles realLift dealer (.tree b)
  if m.skip = false ∨ answer.isSome then
    StateT.lift (secRunsD K circuits settings runLimit D m net dealer emu (.bottom b) 1)
  let s ← StateT.lift get
  match heldBottom D s.operators b, answer with
  | some tree, some (_, ρ) => pure (some (tree, ρ))
  | _, _ => pure none

/-- `secOracles` with the dealer `dealer` also in the runs. -/
def secOraclesD (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => secTreeRequestD K circuits settings runLimit D m net dealer emu b
  | .round1 i J e message => secSignRequest dealer i e (.round1 i J e message)
  | .round2 i J e message parts => secSignRequest dealer i e (.round2 i J e message parts)

/-- `secSigning` with the dealer `dealer`. -/
def secSigningD (m : Mode) (A : DkgTsigAdversary C E) (dealer : Dealt C (RealM C A.net.State))
    (emu : C.Party → Option (Keys C)) : RealM C A.net.State Bool := do
  let s ← get
  match topHolder D s.operators with
  | none => pure false
  | some _ => do
    let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
      fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
    let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
      match q with
      | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
      | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
    let (forgery, st) ← (simulateQ
      (forger + (secOraclesD K circuits settings runLimit D m A.net dealer emu + cell))
      (A.forge ⟨dealer.top.root, dealer.parameter⟩ dealer.top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
    forgeryWins realLift dealer st forgery

/-- `secRest` with the dealer `dealer`. -/
def secRestD (m : Mode) (A : DkgTsigAdversary C E) (dealer : Dealt C (RealM C A.net.State))
    (emu : C.Party → Option (Keys C)) : RealM C A.net.State Bool := do
  secRunsD K circuits settings runLimit D m A.net dealer emu .top runLimit
  secSigningD K circuits settings runLimit D m A dealer emu

/-- The dealer of a run of its top tree. -/
def dealerOf {σ : Type} (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
    (output : Option TreeOutput) : Dealt C (RealM C σ) :=
  dealtWith realLift r.1 r.2.2 ((TreeOutput.topTree output).getD emptyTop) fun x => realLift (prfValue r.2.1 x)

/-- `dealerFirstGame` with the dealer of the first top tree passed on. -/
def givenDealerGame (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let output ← dealerTop r.1 r.2.1
  let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
  let te ← seedGenTail D A.net o.1 o.2 r.1 r.2.2
  (secRestD K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r output) te.2).run'
    (startState D te.1 (keysOf r.2.2 te.2))

variable (prims : Primitives)

/-- `dealerFirstGame` and `givenDealerGame` win with the same probability, for a positive run limit. -/
def ReplayStage : Prop :=
  0 < runLimit → ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (dealerFirstGame K circuits settings runLimit D A) =
      streamAccepts prims D (givenDealerGame K circuits settings runLimit D A)

/-- `givenDealerGame` wins at most as often as `forgerWorldGame`, for a positive run limit. -/
def StructureStage : Prop :=
  0 < runLimit → ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (givenDealerGame K circuits settings runLimit D A) ≤
      streamAccepts prims D (forgerWorldGame K circuits settings runLimit D A)

/-- `DealerFirstForger` from the two stages. -/
theorem dealerFirstForger_of_stages (replay : ReplayStage K circuits settings runLimit prims)
    (structure' : StructureStage K circuits settings runLimit prims) :
    DealerFirstForger prims K circuits settings runLimit := fun hrun D A => by
  rw [replay hrun D A]
  exact structure' hrun D A

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dealerFirstForger_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dealerFirstForger_of_stages
