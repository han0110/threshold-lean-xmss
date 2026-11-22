import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Games
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Basics

/-!
# The recorded programs and the shared bad event of one run

An honest operator records the start of the check of a batch before the check, and the pass of the
check before the copy hashes and the exchange of `OpenRep` (`passCheckOpen`). So the record of a pass
exists when the adversary reads the opening and sends an abort in the same round. `passTree` is the
program of an operator in a run of a tree with this record, with the opened sharing `plainShares` of
a real run or `shiftedShares` of an emulated run.

`PassBad` says that in one run each honest operator reached a check, its tuples have a wrong tuple
or split copies, and an honest operator passed it. `ReusedBefore` says that a hidden key of the run
has a stream cell from before the run.
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

/-! ## The recorded programs -/

/-- The sharing that an operator opens, from the start of the check and the tag of the batch. -/
abbrev Opened (C : Committee) (E : Type) := BatchStart C → ℕ → PartyM C E RealSpec (Shares C Bit)

/-- The opened sharing of a real run, the sharing after `Rerand`. -/
def plainShares : Opened C E := fun b _ => pure b.v'

/-- The opened sharing of an emulated run, as `shiftedBuildingBlocks` shifts it. -/
def shiftedShares (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) : Opened C E := fun b k => do
  let clear ← oracleStep (b.jobs.mapM (evalJob circuits parameter seeds))
  let shift := fun g => ((openings.getD k []).flatten.getD g 0) + (clear.flatten.getD g 0)
  pure fun T g => if lackedTerm D.1 = some T then b.v' T g + shift g else b.v' T g

/-- The check and the opening of a batch with its record, after `recCheckOpen`. It records the start
`b` before the check and the pass before the copy hashes and the exchange of `OpenRep`. -/
def passCheckOpen (opened : Opened C E) (b : BatchStart C) (k : ℕ) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  StateT.lift (RecM.record [.start b])
  let (_, s3) ← RecM.liftS (StateT.lift (((realRunBuildingBlocks (G := RealSpec) K b.ctx b.mode).verify
    (batchTuples K b.mode b.circuits b.inputs b.zs b.v')).run b.state))
  StateT.lift (RecM.record [.opened b.v' fun _ => none])
  let w ← RecM.liftS (StateT.lift (opened b k))
  let digests ← RecM.liftS (StateT.lift (oracleStep (C.terms.mapM fun T =>
    hashQuery (.copy (vector (outputsOf b.circuits).length (w T))))))
  let inbox ← RecM.liftS (StateT.lift (exchange (repOutbox K b.ctx.self w (outputsOf b.circuits).length digests)))
  let values ← RecM.liftS (StateT.lift (repRest K b.ctx.self w (outputsOf b.circuits).length inbox))
  StateT.lift (RecM.record [.output (ThresholdLeanXmssSecurity.assemble b.circuits values)])
  set (s3.label, k + 1)
  pure (some (ThresholdLeanXmssSecurity.assemble b.circuits values))

/-- One batch with its record, after `recBatch`. -/
def passBatch (opened : Opened C E) (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let (label, k) ← get
  let cs := jobs.map (circuits parameter ·.kind)
  let B := realRunBuildingBlocks (G := RealSpec) K ctx settings.mode
  let inputs ← RecM.liftS (StateT.lift (jobs.mapM (inputShares ctx)))
  let (zs, s1) ← RecM.liftS (StateT.lift ((recLayers K B cs inputs (depth cs)).run ⟨fun _ => [], label, k⟩))
  let (v', s2) ← RecM.liftS (StateT.lift ((B.rerand (outputShares K cs
    (layerPrefix K B.mode cs inputs zs (depth cs)).1) (outputsOf cs).length).run s1))
  passCheckOpen K opened ⟨B.mode, jobs, parameter, cs, inputs, zs, v', ctx, s2⟩ k

/-- One ceremony with its record, after `recRun`. -/
def passRun (opened : Opened C E) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let prss ← RecM.liftS (StateT.lift (prssSetup i))
  batched settings.batchSize (passBatch K circuits settings opened ⟨i, keys, prss⟩ keys.parameter) jobs

/-- The program of operator `i` in a run of `tree` with its record. With no randomizer it is
`treeProgram`, and with a randomizer it is `emulatedProgram`. -/
def passTree (opened : Opened C E) (randomizer : Option Randomizer) (i : C.Party) (operator : OperatorState C) :
    Tree → RecM C E TreeOutput
  | .top => match operator.keys with
    | some keys => do
      let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (RecM C E))
          (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
          (passRun K circuits settings opened i keys) emptyTop .top).run' (0, 0) | failure
      pure output
    | none => failure
  | .bottom b => match operator.keys, operator.top with
    | some keys, some top => do
      let some output ← (match randomizer with
          | none => ceremonyOutput (m := StateT (ℕ × ℕ) (RecM C E))
              (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
              (passRun K circuits settings opened i keys) top (.bottom b)
          | some r => bottomOutputWith (m := StateT (ℕ × ℕ) (RecM C E))
              (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
              (passRun K circuits settings opened i keys) top b r).run' (0, 0) | failure
      pure output
    | _, _ => failure

/-! ## The shared bad event of one run -/

/-- The tuples of check `k` at each operator, from the records of a run. -/
def passTuples (k : ℕ) (records : C.Party → Record C E) : C.Party → List (Tuple C) := fun i =>
  (((startsOf (records i))[k]?).map fun b => batchTuples K b.mode b.circuits b.inputs b.zs b.v').getD []

/-- A bad check in the records of one run. Each honest operator recorded the start of check `k`, its
tuples have a wrong tuple or split copies, and an honest operator recorded its pass. The pass is
before the outgoing opening, and the correctness flag of the run needs such a check too. -/
def PassBad (D : C.Coalition) (records : C.Party → Record C E) : Prop :=
  ∃ k, (∀ i, i ∉ D.1 → ((startsOf (records i))[k]?).isSome) ∧
    (WrongTuple D (passTuples K k records) ∨ ¬ MultVerifyAgree D (honestTuples D (passTuples K k records))) ∧
    ∃ i, i ∉ D.1 ∧ k < (openingsOf (records i)).length

/-- A PRSS key of the run under a hidden name has a stream cell in the hidden cache `hidden` of the
start of the run. Then a mask of the run is no fresh value. -/
def ReusedBefore (D : C.Coalition) (hidden : HiddenCache C) (records : C.Party → Record C E) : Prop :=
  ∃ name key, Hidden D name ∧ (∃ i, i ∉ D.1 ∧ ∃ b ∈ startsOf (records i), NameKey i b.ctx.prss name key) ∧
    ∃ ρ idx position, hidden ((name, key), ρ, idx, position) ≠ none

end ThresholdLeanXmssSecurity.DkgSecurityProof
