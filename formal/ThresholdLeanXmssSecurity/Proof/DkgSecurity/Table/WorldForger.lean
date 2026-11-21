import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.SetupFrame

/-!
# The forger of the setup in the world

`forgerWorldGame` is `tsigGame (dkgReduction …)` with the table of the forger moved into the world.

* A call of `A` goes to the counted copy, and a call of `H` of `A` in a setup domain also goes into
  the log of the setup calls.
* A call of an emulated operator goes to the free copy, where `streamWorld` answers a stream under a
  hidden key with a random function.
* A write of the forger is a programming query.
* A query to `tsigGame` is a step of `tsigOracles` on the state of the signing game.

`bodyR` is the body of `dkgReduction` on its table, and `bodyW` is the same code in the world.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## The operations in the world -/

/-- The world of the forger. The state is the log of the setup calls of `A` and the state of the
signing game. -/
abbrev WorldM (C : Committee) := StateT (CallLog C) (StateT (TsigState C) (OracleComp (WorldSpec C)))

/-- A computation of the world in the world of the forger. -/
def toWorld {α : Type} (oa : OracleComp (WorldSpec C) α) : WorldM C α := StateT.lift (StateT.lift oa)

/-- A call of `A` in the world, as `adversaryCall`. -/
def worldAdversaryCall : QueryImpl (LocalSpec C) (WorldM C) := fun t =>
  match t with
  | .inr (.inl q) =>
      if isSetupQuery q then do
        let y : HashOutput ← toWorld (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)))
        modify fun log : CallLog C => log ++ [(q, y)]
        pure y
      else toWorld (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)))
  | t => toWorld (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))

/-- A call of an emulated operator in the world, as `honestCall`. -/
def worldHonestCall : QueryImpl (LocalSpec C) (WorldM C) := fun t =>
  toWorld (worldRoles.honest (OracleComp.lift (OracleSpec.query t)))

/-- `A` and the emulated operators in the world, as `reductionRoles`. -/
def forgerWorldRoles : Roles C (WorldM C) :=
  ⟨fun oa => simulateQ worldAdversaryCall oa, fun oa => simulateQ worldHonestCall oa⟩

/-- A write in the world, as `writeTable`. -/
def worldWrite (q : Query C) (value : HashOutput) : WorldM C Unit := do
  let _ ← toWorld (program q value)
  pure ()

/-- A query to the signing oracles in the world, as `tsigCall`. -/
def worldTsig (dealt : Dealt C (OracleComp (WorldSpec C))) (q : TsigQuery C) : WorldM C (TsigSpec C q) :=
  StateT.lift (tsigOracles (fun oa => SigningCoreProof.honestLift oa) dealt q)

/-! ## The forger in the world -/

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (aes : Aes)
  (D : C.Coalition)

/-- `seedGenEmulation` in the world. -/
def seedGenWorld (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C))
    (net : Adversary C E Unit PEmpty PEmpty) : WorldM C (net.State × (C.Party → Option (Keys C))) := do
  let Ro := forgerWorldRoles (C := C)
  let state ← Ro.adversary (net.start (corruptInputs D fun _ => ()) [])
  let parts ← Ro.honest (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps Ro D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let (state, steps, sent) ← stepRound Ro D net noFunctionality state steps
  let log ← get
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
  let high ← Ro.honest (liftComp ($ᵗ HashOutput) _)
  worldWrite (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  for T in C.terms do
    match C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T with
    | some j =>
        worldWrite (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
          (view (firstHonest (C.holders T)) k).term T)) (((corrupt j).map (·.seed T)).getD 0)
    | none => pure ()
  for j in C.parties do
    for i in C.parties do
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        worldWrite (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((corrupt j).map (·.pairKey i)).getD 0)
  executeRounds Ro D net noFunctionality (setupRounds - 1) state steps

/-- The monad of the forger in the world after the seed generation. -/
abbrev RedW (C : Committee) (σ : Type) := StateT (RealState C σ) (WorldM C)

/-- `emulatedRun` in the world. -/
def emulatedRunW (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) : RedW C net.State Unit := do
  let s ← get
  let keys := fun i => (s.operators i).keys
  let buildingBlocks := shiftedBuildingBlocks K circuits settings D (gameParameter D keys) (gameSeeds D keys) openings
  let (state, outputs) ← StateT.lift (executePhase (forgerWorldRoles (C := C)) D net noFunctionality
    (treeFuel circuits settings) s.adversary fun i =>
      emulatedProgram K circuits settings buildingBlocks randomizer i (s.operators i) tree)
  let operators := fun i => (s.operators i).keep (outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag⟩ : RealState C net.State)

/-- `emulatedRuns` in the world. -/
def emulatedRunsW (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) : ℕ → RedW C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      emulatedRunW K circuits settings D net openings randomizer tree
      emulatedRunsW net openings randomizer tree count

variable (dealt : Dealt C (OracleComp (WorldSpec C)))

/-- `emulatedTreeRequest` in the world. -/
def emulatedTreeRequestW (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    RedW C net.State (Option (BottomTree × Digest)) := do
  let answer : Option (BottomTree × Digest) ← StateT.lift (worldTsig dealt (.tree b))
  match answer with
  | some (tree, ρ) =>
      emulatedRunsW K circuits settings runLimit D net (bottomLeak settings b tree ρ) tree.topSignature.randomizer
        (.bottom b) 1
  | none => pure ()
  let s ← get
  match heldBottom D s.operators b, answer with
  | some tree, some (_, ρ) => pure (some (tree, ρ))
  | _, _ => pure none

/-- `emulatedSignRequest` in the world. -/
def emulatedSignRequestW {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) : RedW C σ (TsigSpec C q) := do
  modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true }
  let s ← get
  match (s.operators i).keys, (s.operators i).top, (s.operators i).bottom (treeOf e) with
  | some _, some _, some _ => StateT.lift (worldTsig dealt q)
  | _, _, _ => pure (noAnswer q)

/-- `forgeOracles` in the world. -/
def forgeOraclesW (net : Adversary C E Unit PEmpty PEmpty) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec net.State)) (RedW C net.State) := fun t =>
  match t with
  | .inl t => StateT.lift (worldAdversaryCall t)
  | .inr (.inl (.corrupt i)) => pure (noAnswer (.corrupt i))
  | .inr (.inl (.tree b)) => emulatedTreeRequestW K circuits settings runLimit D dealt net b
  | .inr (.inl (.round1 i J e message)) => emulatedSignRequestW dealt i e (.round1 i J e message)
  | .inr (.inl (.round2 i J e message parts)) => emulatedSignRequestW dealt i e (.round2 i J e message parts)
  | .inr (.inr .read) => (·.adversary) <$> (get : RedW C net.State _)
  | .inr (.inr (.write state)) => modify fun s : RealState C net.State => { s with adversary := state }

/-- The body of `dkgReduction` in the world. -/
def bodyW (A : DkgTsigAdversary C E) (pk : PublicKey) (top : TopTree) : WorldM C Forgery := do
  let corrupt ← OverPermutation.sequenceFin fun i =>
    if i ∈ D.1 then worldTsig dealt (.corrupt i) else (pure none : WorldM C (Option (Keys C)))
  let (state, keys) ← seedGenWorld D pk.parameter corrupt A.net
  let start : RealState C A.net.State :=
    ⟨state, fun i => ⟨keys i, none, fun _ => none⟩, fun _ => 0, fun _ => false, false⟩
  (do
    emulatedRunsW K circuits settings runLimit D A.net (topLeak settings top) 0 .top runLimit
    match topHolder D (← get).operators with
    | none => pure idleForgery
    | some _ => simulateQ (forgeOraclesW K circuits settings runLimit D dealt A.net) (A.forge pk top)).run' start

/-- `tsigGame (dkgReduction …)` with the table of the forger in the world. -/
def forgerWorldGame (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  let some dealt ← dealerKeyGen | pure false
  let ((forgery, _), st) ← ((bodyW K circuits settings runLimit D dealt A ⟨dealt.top.root, dealt.parameter⟩
    dealt.top).run []).run SigningCoreProof.tsigInit
  forgeryWins (fun oa => SigningCoreProof.honestLift oa) dealt st forgery

/-! ## The body of `dkgReduction` -/

/-- The body of `dkgReduction` on the table of the forger. -/
def bodyR (A : DkgTsigAdversary C E) (pk : PublicKey) (top : TopTree) : TableM C Forgery := do
  let corrupt ← OverPermutation.sequenceFin fun i =>
    if i ∈ D.1 then tsigCall (.corrupt i) else (pure none : TableM C (Option (Keys C)))
  let (state, keys) ← seedGenEmulation aes D pk.parameter corrupt A.net
  let start : RealState C A.net.State :=
    ⟨state, fun i => ⟨keys i, none, fun _ => none⟩, fun _ => 0, fun _ => false, false⟩
  (do
    emulatedRuns K circuits settings runLimit aes D A.net (topLeak settings top) 0 .top runLimit
    match topHolder D (← get).operators with
    | none => pure idleForgery
    | some _ => simulateQ (forgeOracles K circuits settings runLimit aes D A.net) (A.forge pk top)).run' start

omit [Fintype E] [DecidableEq E] in
theorem dkgReduction_eq (A : DkgTsigAdversary C E) (pk : PublicKey) (top : TopTree) :
    dkgReduction K circuits settings runLimit aes D A pk top =
      (bodyR K circuits settings runLimit aes D A pk top).run' ⟨∅, ∅, []⟩ := rfl

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgReduction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dkgReduction_eq
