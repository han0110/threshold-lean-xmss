import ThresholdLeanXmssSecurity.Proof.LifetimeSlotTransport

/-!
# The lifetime lemmas at the fixed `Th`

`LifetimeSecurityStatement` fixes `prims` and `circuits`. The earlier lifetime proofs hold for each
`values : MpcDomain → HashOutput`, at `⟨thOf values, aes⟩` and `circuitsOf (thOf values)`. This file
moves them to the fixed `prims`.

* `restrictTh prims` is `prims` with `Th` set to zero outside the inputs that the MPC evaluates. It
  is the instance `values := fun x => prims.Th x.1` with `aes := prims.aes`. It is not `prims`.
* `hashAnswer` reads `Th` only on the inputs that the MPC evaluates. So the worlds of
  `restrictTh prims` and of `prims` are equal (`localAnswer_restrict`, `lifetimeWorld_restrict`,
  `world_restrict`, `prgReduction_restrict`, `jointPrefixRun_restrict`, `accepts_restrict`).
* The constant family `fun _ => circuits` has a fixed shape (`fixedShape_const`). The budget of
  `LifetimeSecurityStatement` is the earlier budget at this family (`hasLifetimeQueryBound_const`).

The five averaged contracts of the earlier proofs sample `values`. Each contract below is the same
contract at the fixed `prims` and `circuits`, and it follows from the pointwise core of the earlier
proof.

| Contract | Source of the core |
| --- | --- |
| `LifetimeKeygenHop`, by `lifetimeKeygenHop_of_programs` | `LifetimeKeygenHopProof.lean`, `hpoint` of `lifetimeKeygenHop_of_programs` |
| `real_transport` | `LifetimePrfTransportProof.lean`, `hpoint` of `real_transport` |
| `ideal_transport` | `LifetimePrfTransportProof.lean`, `hpoint` of `ideal_transport` |
| `SlotTransport`, by `slotTransport_of_kernel_overlap` | `LifetimeSlotTransport.lean`, `hpoint` of `slotTransport_of_kernel_overlap` |
| `joint_fixed_bound` | `LifetimeSlots.lean`, `hv` of `joint_average_bound` |

`SelectedKeyOverlapBound` takes `CircuitsCompute circuits prims.Th` at the fixed `prims`. The earlier
form takes `∀ Th, CircuitsCompute (circuitsOf Th) Th`, which is false for a constant family.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeO3Bridge

open LifetimeJointLink

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

section Bridges

/-- `prims` with `Th` set to zero outside the inputs that the MPC evaluates. -/
def restrictTh (prims : Primitives) : Primitives := ⟨thOf fun x => prims.Th x.1, prims.aes⟩

theorem hashAnswer_restrict (prims : Primitives) :
    hashAnswer (C := C) (restrictTh prims) = hashAnswer prims := by
  funext q
  cases q with
  | hash input =>
    by_cases h : MpcInput input
    · simp [hashAnswer, restrictTh, thOf, h]
    · simp [hashAnswer, h]
  | _ => rfl

theorem localAnswer_restrict (prims : Primitives) :
    localAnswer (C := C) (restrictTh prims) = localAnswer prims := by
  have hp : prgAnswer (C := C) (restrictTh prims) = prgAnswer prims := by
    funext x
    simp only [prgAnswer, hashAnswer_restrict]
    rfl
  simp only [localAnswer, hashAnswer_restrict, hp]

theorem lifetimeWorld_restrict (prims : Primitives) :
    lifetimeWorld (C := C) (restrictTh prims) = lifetimeWorld prims := by
  simp only [lifetimeWorld, localAnswer_restrict]

theorem world_restrict (prims : Primitives) : world (C := C) (restrictTh prims) = world prims := by
  simp only [world, localAnswer_restrict]

theorem prgReduction_restrict (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    prgReduction (restrictTh prims) D game = prgReduction prims D game := by
  simp only [prgReduction, localAnswer_restrict]

theorem jointPrefixRun_restrict (prims : Primitives) (pre : LifetimeBridge.Selector C) :
    LifetimeBridge.jointPrefixRun (restrictTh prims) pre = LifetimeBridge.jointPrefixRun prims pre := by
  simp only [LifetimeBridge.jointPrefixRun, localAnswer_restrict]

theorem accepts_restrict (prims : Primitives) (game : OracleComp (WorldSpec C) Bool) :
    accepts (restrictTh prims) game = accepts prims game := by
  simp only [accepts, runWorld, world_restrict]

/-- The run of `lifetimeRunSampled` at `values := fun x => prims.Th x.1` is `lifetimeRun prims`. -/
theorem lifetimeRun_restrict (prims : Primitives) (game : OracleComp (WorldSpec C) Bool) :
    (simulateQ (lifetimeWorld (restrictTh prims)) game).run.run' ∅ = lifetimeRun prims game := by
  rw [lifetimeWorld_restrict]
  rfl

theorem fixedShape_const (circuits : Circuits) : FixedShape fun _ => circuits :=
  fun _ _ _ _ => ⟨rfl, rfl⟩

/-- The counter of `lifetimeRun` does not change its output. -/
theorem lifetimeRun_output (prims : Primitives) (game : OracleComp (WorldSpec C) Bool) :
    Prod.fst <$> lifetimeRun prims game = (simulateQ (worldAnswer prims) game).run' ∅ :=
  fst_map_run_withAddCost _ _ game ∅

/-- `lifetimeRun` accepts with the probability `accepts`. -/
theorem probability_lifetimeRun (prims : Primitives) (game : OracleComp (WorldSpec C) Bool) :
    (Pr[fun r => r.1 = true | lifetimeRun prims game]).toReal = accepts prims game := by
  have hf : (fun r : Bool × ℕ => r.1 = true) = (fun b => b = true) ∘ Prod.fst := rfl
  rw [accepts_eq_probOutput, hf, ← probEvent_map, lifetimeRun_output, probEvent_eq_eq_probOutput]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The budget of `LifetimeSecurityStatement` is the earlier budget at the constant family. -/
theorem hasLifetimeQueryBound_const (Q : ℕ) :
    HasLifetimeQueryBound K circuits settings attempts D A Q ↔
      HasLifetimeQueryBoundAll K settings attempts (fun _ => circuits) D A Q :=
  ⟨fun h _ => h, fun h => h fun _ => 0⟩

/-- The PRF reduction of the statement is the pointwise reduction of the earlier proofs at
`restrictTh prims`. -/
theorem lifetimeRunReduction_restrict (n : ℕ) :
    lifetimeRunReduction K circuits settings attempts prims D A n =
      prgReduction (restrictTh prims) D ((fun r => r.1.1) <$>
        ((lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n)
          D A).run ∅).run) := by
  rw [prgReduction_restrict]
  rfl

/-- The chronological world `n` accepts as hybrid `n`, at the fixed `prims`. -/
theorem accepts_chronological (n : ℕ) :
    accepts prims (LifetimeHybridOrder.chronologicalGame K settings attempts D A circuits n) =
      accepts prims (LifetimeHybridOrder.emulationGame (lifetimeGameWith K circuits settings attempts
        (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) := by
  have h := LifetimePrfTransportProof.accepts_chronological K settings attempts prims.aes (fun _ => circuits)
    D A (fun x => prims.Th x.1) n
  rw [show (⟨thOf fun x => prims.Th x.1, prims.aes⟩ : Primitives) = restrictTh prims from rfl,
    accepts_restrict, accepts_restrict] at h
  exact h

/-- A pointwise lemma with `FixedShape` at the fixed `prims`. `slotSuspension` gives the premises of
the joint hop of slot `k`. -/
theorem slotSuspension_fixed (Q : ℕ) (k : Fin (lifetimeRuns attempts)) :
    (∀ p ∈ support (LifetimeBridge.jointPrefixRun prims
        (LifetimeSlots.slotInstance K settings attempts D A Q k circuits).pre),
        p.1.2.2.1 = slotTree ((LifetimeSlots.slotOrder attempts).symm k)) ∧
      IsQueryBoundP (LifetimeBridge.jointPrefix (LifetimeSlots.slotInstance K settings attempts D A Q k circuits).pre)
        Counted (Q + lifetimeOverhead C attempts Q) ∧
      IsQueryBounded (LifetimeSlots.slotInstance K settings attempts D A Q k circuits).A
        (LifetimeSlots.slotInstance K settings attempts D A Q k circuits).Z (ceremonyFuel circuits settings)
        ((ceremonyFuel circuits settings + 2) * Q) := by
  have h := LifetimeSlots.slotSuspension K settings attempts prims.aes (fun _ => circuits) D A Q
    (fixedShape_const circuits) k (fun x => prims.Th x.1)
  have hr := jointPrefixRun_restrict prims (LifetimeSlots.slotInstance K settings attempts D A Q k circuits).pre
  simp only [restrictTh] at hr
  rw [hr] at h
  exact h

end Bridges

section Contracts

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The chronological world `n` at the fixed `prims` and `circuits`. -/
def chronologicalProbability (n : ℕ) : ℝ :=
  (Pr[fun r => r.1 = true |
    lifetimeRun prims (LifetimeHybridOrder.chronologicalGame K settings attempts D A circuits n)]).toReal

/-- The real (`real = true`) or ideal PRF experiment of the reduction of run `n` of the statement. -/
def reductionProbability (real : Bool) (n : ℕ) : ℝ :=
  (Pr[= true | if real then
    (hiddenStreams prims.aes).prfRealExp (lifetimeRunReduction K circuits settings attempts prims D A n)
    else PRFScheme.prfIdealExp (lifetimeRunReduction K circuits settings attempts prims D A n)]).toReal

/-- The dealer-keygen world at the fixed `prims` and `circuits`. -/
def dealerKeygenProbability : ℝ :=
  (Pr[fun r => r.1 = true |
    lifetimeRun prims (LifetimeHybridOrder.dealerKeygenGame K settings attempts D A circuits)]).toReal

/-- The slot world `S_k` (`sep = false`) or `T_k` (`sep = true`) at the fixed `prims` and
`circuits`. -/
def slotProbability (k : ℕ) (sep : Bool) : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRun prims (LifetimeSlots.slotGame K settings attempts D A k sep circuits)]).toReal

/-- The single keygen hop after every chronological PRF hop, at the fixed `prims`. -/
def LifetimeKeygenHop (Q : ℕ) : Prop :=
  |chronologicalProbability prims K circuits settings attempts D A (lifetimeRuns attempts) -
    dealerKeygenProbability prims K circuits settings attempts D A| ≤
    keygenHashError C ((setupRounds + 2) * Q)

/-- The keygen hop at the fixed `prims` from the role pruning, the tail classification, the
keygen-only cap quietness and the real reached-tail bound at `prims` and `circuits`. -/
theorem lifetimeKeygenHop_of_programs (Q : ℕ)
    (hroles : LifetimeKeygenHopProof.ChronologicalRoles K settings attempts D A circuits)
    (hfree : LifetimeKeygenHopProof.TailProgramFree K settings attempts D A circuits)
    (hcap : LifetimeKeygenHopProof.KeygenCapQuiet D A prims Q)
    (hbound : LifetimeKeygenHopProof.RealTailBound K settings attempts D A prims circuits Q) :
    LifetimeKeygenHop prims K circuits settings attempts D A Q := by
  simpa only [LifetimeKeygenHop, chronologicalProbability, dealerKeygenProbability, probability_lifetimeRun]
    using LifetimeKeygenHopProof.endpoint_gap K settings attempts D A prims circuits Q hroles hfree hcap hbound

/-- The real side of hop `n` at the fixed `prims` is identical until the stream-key bad event of
hybrid `n` (`keyWorld_coupling`). -/
theorem real_transport (n : ℕ) :
    |chronologicalProbability prims K circuits settings attempts D A n -
      reductionProbability prims K circuits settings attempts D A true n| ≤
      probBad_streamKey prims D (LifetimeHybridOrder.emulationGame (lifetimeGameWith K circuits settings attempts
        (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) := by
  have h := keyWorld_coupling prims D (LifetimeHybridOrder.emulationGame (lifetimeGameWith K circuits settings
    attempts (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A))
  rw [← prfRealExp_prgReduction] at h
  rw [chronologicalProbability, probability_lifetimeRun, accepts_chronological]
  exact h

/-- The ideal side of hop `n` at the fixed `prims` is identical until `IdealBad`. -/
theorem ideal_transport (n : ℕ) :
    |reductionProbability prims K circuits settings attempts D A false n -
      chronologicalProbability prims K circuits settings attempts D A (n + 1)| ≤
      (Pr[LifetimePrfTransportProof.IdealBad ∘ Prod.snd |
        (simulateQ (LifetimePrfTransportProof.leftImpl prims D)
          (LifetimePrfTransportProof.program4 D K circuits settings attempts A n)).run
            LifetimePrfTransportProof.idealStart]).toReal := by
  have h := LifetimePrfTransportProof.ideal_point prims D K circuits settings attempts A n
  rw [← prfIdealExp_prgReduction] at h
  rw [chronologicalProbability, probability_lifetimeRun, accepts_chronological, accepts_eq_probOutput]
  exact h

/-- The move of slot `k` from the shared stream table of the dealer world to its own table, at the
fixed `prims`. -/
def SlotTransport (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel circuits settings + 2) * Q
  q₀ + q < 2 ^ 128 → ∀ k : Fin (lifetimeRuns attempts),
    |slotProbability prims K circuits settings attempts D A k false -
      slotProbability prims K circuits settings attempts D A k true| ≤ streamKeyError C

/-- The U4 estimate for each hidden name of the selected run in the separated world, at the fixed
`prims`. The source circuit premise and the lifetime budget are at `prims` and `circuits`. -/
def SelectedKeyOverlapBound (Q : ℕ) : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
  HasLifetimeQueryBound K circuits settings attempts D A Q →
  Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q < 2 ^ 128 →
  ∀ (k : Fin (lifetimeRuns attempts)) (name : {name : KeyName C // Hidden D name}),
    Pr[fun r => name ∈ r.2.2.overlaps |
      LifetimeSlotTransport.markedGame K circuits settings attempts k D A prims] ≤
      ((2 * (lifetimeRuns attempts - 1) + Q : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- The slot probability at the fixed `prims` is the acceptance of the evaluated kernel game. -/
theorem slotProbability_raw (k : Fin (lifetimeRuns attempts)) (sep : Bool) :
    slotProbability prims K circuits settings attempts D A k sep =
      (Pr[fun r => r.1 = true |
        LifetimeSlotTransport.rawGame K circuits settings attempts k D A prims sep]).toReal := by
  rw [slotProbability, probability_lifetimeRun, accepts_eq_probOutput,
    LifetimeSlotTransport.slotGame_eq_generic, ← LifetimeSlotTransport.rawGame_output,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

/-- The local coupling and the recorded-name estimates at the fixed `prims` give the slot
contract at `prims`. -/
theorem slotTransport_of_kernel_overlap (Q : ℕ)
    (hcompute : CircuitsCompute circuits prims.Th) (hbatch : 0 < settings.batchSize)
    (hQ : HasLifetimeQueryBound K circuits settings attempts D A Q)
    (coupled : ∀ k : Fin (lifetimeRuns attempts), LifetimeSlotTransport.KernelCoupling K circuits settings attempts D k)
    (bounded : SelectedKeyOverlapBound prims K circuits settings attempts D A Q) :
    SlotTransport prims K circuits settings attempts D A Q := by
  intro small k
  rw [slotProbability_raw, slotProbability_raw]
  exact (LifetimeSlotTransport.rawGame_gap K circuits settings attempts D A prims k (coupled k)).trans
    ((LifetimeSlotTransport.markedGame_bad_bound K circuits settings attempts D A prims k Q
      (bounded hcompute hbatch hQ small k)).trans
      (LifetimeSlotTransport.overlap_allowance attempts Q _ small))

/-- The joint hop of the tree side at the fixed `prims` pays the fixed tree error of the selected
tree. It needs no average and no `FixedShape`. -/
theorem joint_fixed_bound (inst : LifetimeSlots.JointInstance C E) (tree : Tree) (q₀ q : ℕ)
    (hjoint : LifetimeBridge.JointSimulationHopFrom prims K circuits settings (keySplit C))
    (hb : 0 < settings.batchSize)
    (htree : ∀ p ∈ support (LifetimeBridge.jointPrefixRun prims inst.pre), p.1.2.2.1 = tree)
    (hpre : IsQueryBoundP (LifetimeBridge.jointPrefix inst.pre) Counted q₀)
    (hadv : IsQueryBounded inst.A inst.Z (ceremonyFuel circuits settings) q) :
    |reductionIdeal prims D (LifetimeBridge.jointGame K circuits settings false D inst.pre inst.A inst.Z) -
        accepts prims (LifetimeBridge.jointGame K circuits settings true D inst.pre inst.A inst.Z)| ≤
      treeCheckError (E := E) circuits settings tree (q₀ + q) +
        (treeHashError circuits settings C tree (q₀ + q) - keySplit C (q₀ + q)) := by
  have h := hjoint hb D _ _ _ q₀ q hpre hadv
  rwa [jointError_fixed_tree _ _ tree _ htree] at h

end Contracts

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.localAnswer_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localAnswer_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.lifetimeWorld_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeWorld_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.world_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.prgReduction_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prgReduction_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.jointPrefixRun_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointPrefixRun_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.lifetimeRun_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeRun_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.hasLifetimeQueryBound_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasLifetimeQueryBound_const

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.lifetimeRunReduction_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeRunReduction_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.accepts_chronological' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepts_chronological

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.slotSuspension_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotSuspension_fixed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.lifetimeKeygenHop_of_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeKeygenHop_of_programs

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.real_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_transport

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.ideal_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_transport

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.slotTransport_of_kernel_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotTransport_of_kernel_overlap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3Bridge.joint_fixed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_fixed_bound

end ThresholdLeanXmssSecurity.LifetimeO3Bridge
