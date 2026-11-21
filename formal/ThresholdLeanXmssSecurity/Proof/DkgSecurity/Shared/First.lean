import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Start
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Hops
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RunsUnion
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.GameHidden

/-!
# The game with the first record at the recorded run

`passTreeRun` is one run of a tree with the record of a pass (`passTree` with `plainShares`), answered
by `streamWorld`, with the shared event of the run. `passFirst` is the game `firstRunOf` at this run.
The run is the block run of `passBlock` (`passTreeRun_eq_blockRun`). With its records dropped, the
block is the plain phase of `treeProgram` (`executePhaseR_erase`, `treeProgram_eq_drop`), so each query
bound of the plain phase holds for the block (`passBlock_bound`), and the block keeps the honest
budgets of each domain (`passBlock_keepsBudget`) and the bound of the calls of `Adds c`
(`passBlock_adds`). Each outcome of the recorded run has an outcome of the plain phase with the same
world (`passTreeRun_world`), so the recorded run keeps the provenance of the hidden keys
(`passTreeRun_provenance`), adds at most the keys of its setups under each hidden name
(`passTreeRun_hidden`), and has the ledger of the coin keys of one run (`passTreeRun_sound`).

The hops of the game with the first record are then instances of the hops for each run.
`passSeedsHop` states `PassSeedsHop`, `passRunsUnion` states `PassRunsUnion`, and `passEchoHop`,
`passReuseHop`, `passCopyHop` and `passSplitHop` state `PassCollisionHop` at the four domains of
`GlobalEvent` with `echoError`, `reuseError`, `copyError` and `splitError`.

`PassReady` is the readiness test of a start for the shared event. Two hops are statements here.
`PassReadyHop` states that no start up to the first record fails the test `PassReady`, and
`PassFlagFirst` states that the flag of the real game with the shared event comes with a first record.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The recorded run and its game -/

/-- One recorded run of `tree` from the state `s`, answered by `streamWorld`. It gives the outputs
of the honest operators and the shared event of the run, as `sharedRunWith` computes it. -/
def passTreeRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : RunOf C net.State := fun tree s => do
  let before ← get
  let (state, steps) ← simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
    ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
      (passTree K circuits settings plainShares none i (s.operators i) tree).run.run)
  let after ← get
  let records := fun i => (steps i).record []
  pure ((state, fun i => (steps i).output),
    decide (PassBad K D records ∨ ReusedBefore D before.2 records ∨ GlobalEvent after))

/-- The real game with the shared event and the first record. -/
def passFirst (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) : ProbComp (FirstState C A.net.State × StreamState C) :=
  firstRunOf prims runLimit D A (passTreeRun prims K circuits settings D A.net) ready

/-- The probability of `event` on the final state of `passFirst`. -/
def passFirstProb (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop)
    (event : FirstState C A.net.State × StreamState C → Prop) : ℝ :=
  (Pr{let r ← passFirst prims K circuits settings runLimit D A ready}[event r]).toReal

/-- The probability that the first record has a world with a collision in the domain `P`. -/
def passCollision (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (P : Query C → Prop) : ℝ :=
  passFirstProb prims K circuits settings runLimit D A ready fun r =>
    ∃ stage world, r.1.first = some (stage, world) ∧ DomainCollision P world.1

/-! ## The block of the recorded run -/

/-- The recorded block of a run with the record of a pass. -/
def passBlock (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State) :
    OracleComp (WorldSpec C) (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) :=
  executePhaseR worldRoles D net noFunctionality ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
    (passTree K circuits settings plainShares none i (s.operators i) tree).run.run

/-- The shared event of the recorded block. -/
def passEvent (D : C.Coalition) {σ : Type} (before : StreamState C)
    (z : σ × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) (after : StreamState C) : Bool :=
  decide (PassBad K D (fun i => (z.2 i).record []) ∨ ReusedBefore D before.2 (fun i => (z.2 i).record []) ∨
    GlobalEvent after)

omit [Fintype E] [DecidableEq E] in
/-- The recorded run is the block run of `passBlock` with the shared event. -/
theorem passTreeRun_eq_blockRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    passTreeRun prims K circuits settings D net =
      blockRun prims D (passBlock K circuits settings D net) (fun z => (z.1, fun i => (z.2 i).output))
        (passEvent K D) := rfl

omit [Fintype E] [DecidableEq E] in
/-- Each query bound of the plain phase of `treeProgram` holds for the recorded block. With its
records dropped, the block is that phase. -/
theorem passBlock_bound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) {p : (WorldSpec C).Domain → Prop} {n : ℕ}
    (h : IsQueryBoundP (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
      fun i => treeProgram K circuits settings i (s.operators i) tree) p n) :
    IsQueryBoundP (passBlock K circuits settings D net tree s) p n := by
  rw [treeProgram_eq_drop K circuits settings s.operators tree] at h
  rw [executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
    ([] : Record C E) (treeFuel circuits settings) s.adversary
    (fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run),
    isQueryBoundP_map_iff] at h
  exact h

omit [Fintype E] [DecidableEq E] in
/-- The recorded block keeps the honest budgets of each domain `P` of the class `c`. The calls of the
network, the honest calls and the absence of a programming call are those of the plain phase. -/
theorem passBlock_keepsBudget {c : HashClass} {P : Query C → Prop} (hPc : ∀ q, P q → queryClass q = c)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    Collision.KeepsBudget K circuits settings c P net (passBlock K circuits settings D net) := by
  intro seed honestRun hbudget step hround tree s
  refine ⟨(GameCount.bound_iff _ _ _).2 (passBlock_bound K circuits settings D net tree s ?_),
    (GameCount.bound_iff _ _ _).2 (passBlock_bound K circuits settings D net tree s ?_)⟩
  · exact FirstCounts.isQueryBoundP_add (fun _ => Collision.counted_or hPc) _ _ _
      (FirstCounts.ownAdds_executePhase c D net step hround _ _ _)
      ((GameCount.bound_iff _ _ _).1 (hbudget.2 D net tree s))
  · exact (SigningSelectionProof.noCall_iff _ _).1 (Collision.noProgram_executePhase D net _ _ _)

omit [Fintype E] [DecidableEq E] in
/-- The recorded block makes at most `treeFuel * step` calls of the network and the honest calls of
the class budget `honestRun` of `Adds c`. -/
theorem passBlock_adds (c : HashClass) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (InClass c) step) (honestRun : Tree → ℕ)
    (htree : FirstCounts.TreeHonest K circuits settings c honestRun) (tree : Tree) (s : RealState C net.State) :
    GameCount.Bound (FirstCounts.Adds c) (passBlock K circuits settings D net tree s)
      (treeFuel circuits settings * step + honestRun tree) :=
  (GameCount.bound_iff _ _ _).2 (passBlock_bound K circuits settings D net tree s
    (FirstCounts.isQueryBoundP_add (fun _ => FirstCounts.adds_or c) _ _ _
      (FirstCounts.ownAdds_executePhase c D net step hround _ _ _)
      ((GameCount.bound_iff _ _ _).1 (htree D net tree s))))

omit [Fintype E] [DecidableEq E] in
/-- Each outcome of the recorded block in `streamWorld` has an outcome of the plain phase of
`treeProgram` with the same world. -/
theorem passBlock_world (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (w : StreamState C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (passBlock K circuits settings D net tree s)).run w),
      ∃ y ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
        (treeFuel circuits settings) s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree)).run w),
        y.2 = z.2 := by
  intro z hz
  refine ⟨((z.1.1, fun i => (z.1.2 i).output), z.2), ?_, rfl⟩
  rw [treeProgram_eq_drop K circuits settings s.operators tree, executePhaseR_erase worldRoles
    (fun g oa => worldRoles_honest_map g oa) D net noFunctionality ([] : Record C E) (treeFuel circuits settings)
    s.adversary (fun i => (passTree K circuits settings plainShares none i (s.operators i) tree).run.run),
    simulateQ_map, StateT.run_map, support_map]
  exact ⟨z, hz, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- Each outcome of the recorded run has an outcome of the plain phase of `treeProgram` with the same
world. -/
theorem passTreeRun_world (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (w : StreamState C) :
    ∀ x ∈ support ((passTreeRun prims K circuits settings D net tree s).run w),
      ∃ y ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
        (treeFuel circuits settings) s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree)).run w),
        y.2 = x.2 := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := RecordedCache.blockRun_world prims D (passBlock K circuits settings D net)
    (fun z => (z.1, fun i => (z.2 i).output)) (passEvent K D) tree s w x hx
  obtain ⟨y, hy, hyz⟩ := passBlock_world prims K circuits settings D net tree s w z hz
  exact ⟨y, hy, hyz.trans hxz.symm⟩

omit [Fintype E] [DecidableEq E] in
/-- The recorded run keeps the provenance of the hidden keys, as the plain phase does. -/
theorem passTreeRun_provenance (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    ProvenanceRun D (passTreeRun prims K circuits settings D net) := by
  intro tree s world hw x hx
  obtain ⟨y, hy, he⟩ := passTreeRun_world prims K circuits settings D net tree s world x hx
  rw [← he]
  exact treePhaseProvenance prims K circuits settings D net tree s world hw y hy

/-- The recorded run adds at most `treeSetups tree` keys under each hidden name, as the plain phase
does. -/
theorem passTreeRun_hidden (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    HiddenRun D (passTreeRun prims K circuits settings D net) := by
  intro tree s w m hpar hb x hx
  obtain ⟨y, hy, he⟩ := passTreeRun_world prims K circuits settings D net tree s w x hx
  rw [← he]
  exact treePhase_hiddenKeyBound prims K circuits settings D net tree s w m hpar hb y hy

omit [Fintype E] [DecidableEq E] in
/-- The recorded run has the ledger of the coin keys of one run, as the plain phase does. -/
theorem passTreeRun_sound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .challenge) step) :
    SoundRun circuits settings step (passTreeRun prims K circuits settings D net) := by
  intro tree s w seen keys hs x hx
  obtain ⟨y, hy, he⟩ := passTreeRun_world prims K circuits settings D net tree s w x hx
  rw [← he]
  exact treePhase_soundCache prims K circuits settings D net step hround tree s w seen keys hs y hy

/-! ## The hops of the game with the first record -/

/-- The seeds differ after the seed generation, as `SeedsHopW`. The record of the seeds is before
each run. -/
def PassSeedsHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (ready : RealState C A.net.State → StreamState C → Prop), DkgTsigBounded circuits settings runLimit A q →
    passFirstProb prims K circuits settings runLimit D A ready (fun r => ∃ world, r.1.first = some (.seeds, world)) ≤
      seedGenHashError C q

/-- A collision in the domain `P` at the world of the first record, as `CollisionHopW`. -/
def PassCollisionHop (P : Query C → Prop) (error : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (ready : RealState C A.net.State → StreamState C → Prop), DkgTsigBounded circuits settings runLimit A q →
    passCollision prims K circuits settings runLimit D A ready P ≤ error q

/-- The bound `ε tree` of a recorded run of `tree` with the shared event and no global event at its
end, from each start that passes the test `ready` and has no flag, as `RunBadW`. -/
def PassRunBad (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (ready : RealState C net.State → StreamState C → Prop) (ε : Tree → ℝ) : Prop :=
  ∀ (tree : Tree) (s : RealState C net.State) (world : StreamState C), ready s world → s.flag = false →
    (Pr{let r ← (passTreeRun prims K circuits settings D net tree s).run world}[
        r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤ ε tree

/-- The union over the runs, as `RunsUnionHopW`. -/
def PassRunsUnion : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (ready : RealState C A.net.State → StreamState C → Prop)
    (ε : Tree → ℝ), (∀ tree, 0 ≤ ε tree) → PassRunBad prims K circuits settings D A.net ready ε →
    passFirstProb prims K circuits settings runLimit D A ready (fun r =>
        ∃ tree index world, r.1.first = some (.run tree index, world) ∧ ¬ GlobalEvent world) ≤
      runLimit * (ε .top + ∑ b : Fin (2 ^ layerHeight), ε (.bottom b))

/-- The readiness of a start for the bound of the shared event. The honest keys are consistent, the
caches are within the ledger, and the hidden keys have their provenance. It is `RunReadyL` of the
library with no clause on the kept top trees. The library needs that clause for the monitor of the
outputs, and the shared event has no monitor. The bound of a ceremony needs `CeremonyReady`, which
has these three parts. -/
def PassReady (budget : StartBudget) (D : C.Coalition) {σ : Type} (s : RealState C σ) (world : StreamState C) :
    Prop :=
  seedsDiffer D (fun i => (s.operators i).keys) = false ∧ LedgerFits budget world ∧ HiddenProvenance D world

/-- The readiness of each start up to the first record, as a statement. In the game that tests
`PassReady` at each start of a run, no start is recorded as not ready with no global event. The test
reads the keys, the ledger and the provenance of the hidden keys, and no kept top tree and no flag.
So a start after a top tree that an honest operator kept from a faulty check is ready. It has the
form of `ReadyHopL`. -/
def PassReadyHop : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    passFirstProb prims K circuits settings runLimit D A
      (PassReady (startBudget circuits settings runLimit C q) D)
      (fun r => ∃ tree index world, r.1.first = some (.unready tree index, world) ∧ ¬ GlobalEvent world) = 0

/-- The flag of the real game with the shared event comes with a first record, for each readiness
test, as a statement. The log and the records of the game change no flag. It has the form of
`FlagFirstHopW`. -/
def PassFlagFirst : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (ready : RealState C A.net.State → StreamState C → Prop),
    realProb prims K circuits settings runLimit true D A (fun r => r.2 = true) ≤
      passFirstProb prims K circuits settings runLimit D A ready fun r => r.1.first ≠ none

omit [Fintype E] [DecidableEq E] in
/-- `PassSeedsHop` is `seedsHopOf` at the recorded run. -/
theorem passSeedsHop : PassSeedsHop prims K circuits settings runLimit := fun D A q ready bounded =>
  seedsHopOf prims circuits settings runLimit D A q _ ready bounded

omit [Fintype E] [DecidableEq E] in
/-- `PassRunsUnion` is `runsUnionHopOf` at the recorded run. -/
theorem passRunsUnion : PassRunsUnion prims K circuits settings runLimit := fun D A ready ε hpos hbad =>
  RunsUnion.runsUnionHopOf prims runLimit D A _ ready ε hpos hbad

omit [Fintype E] [DecidableEq E] in
/-- Two echo hashes collide at the world of the first record with probability at most `echoError`. -/
theorem passEchoHop : PassCollisionHop prims K circuits settings runLimit EchoDomain (echoError runLimit C) :=
  fun D A q ready hA => echoHopOf K circuits settings runLimit prims D A q ready hA (passBlock K circuits settings D A.net)
    (fun z => (z.1, fun i => (z.2 i).output)) (passEvent K D)
    (passBlock_keepsBudget K circuits settings echoDomain_class D A.net)

omit [Fintype E] [DecidableEq E] in
/-- Two derived keys collide at the world of the first record with probability at most `reuseError`. -/
theorem passReuseHop : PassCollisionHop prims K circuits settings runLimit DeriveDomain (reuseError runLimit C) :=
  fun D A q ready hA => reuseHopOf K circuits settings runLimit prims D A q ready hA (passBlock K circuits settings D A.net)
    (fun z => (z.1, fun i => (z.2 i).output)) (passEvent K D)
    (passBlock_keepsBudget K circuits settings deriveDomain_class D A.net)

omit [Fintype E] [DecidableEq E] in
/-- Two copy hashes collide at the world of the first record with probability at most `copyError`. -/
theorem passCopyHop : PassCollisionHop prims K circuits settings runLimit CopyDomain (copyError settings runLimit C) :=
  fun D A q ready hA => copyHopOf K circuits settings runLimit prims D A q ready hA (passBlock K circuits settings D A.net)
    (fun z => (z.1, fun i => (z.2 i).output)) (passEvent K D)
    (passBlock_keepsBudget K circuits settings copyDomain_class D A.net)

omit [Fintype E] [DecidableEq E] in
/-- Two history or digest cells collide at the world of the first record with probability at most
`splitError`. -/
theorem passSplitHop :
    PassCollisionHop prims K circuits settings runLimit SplitHashDomain (splitError settings runLimit C) :=
  fun D A q ready hA => splitHopOf K circuits settings runLimit prims D A q ready hA
    (passBlock K circuits settings D A.net) (fun z => (z.1, fun i => (z.2 i).output)) (passEvent K D)
    (passBlock_keepsBudget K circuits settings splitHashDomain_class D A.net)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passSeedsHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passSeedsHop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passRunsUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passRunsUnion

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passEchoHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passEchoHop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passReuseHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passReuseHop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passCopyHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passCopyHop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passSplitHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passSplitHop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passTreeRun_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passTreeRun_provenance

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passTreeRun_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passTreeRun_hidden

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passTreeRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passTreeRun_sound
