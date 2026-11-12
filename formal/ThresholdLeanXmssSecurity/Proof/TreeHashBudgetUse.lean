import ThresholdLeanXmssSecurity.Proof.TreeHashBudgetRun
import ThresholdLeanXmssSecurity.Proof.TreeSaltPairsProof
import ThresholdLeanXmssSecurity.Proof.TreeFromCache
import ThresholdLeanXmssSecurity.Proof.LifetimeJointSimStages

/-!
# Consumers of the honest hash budget

These wrappers supply `treeSimHashHonestBudget` to the original hash, salt,
from-cache and joint-selection lemmas. All other hypotheses and conclusions
are retained. The selected fresh-budget lemmas keep the small-tail condition
used by the clipped joint bound.

The pinned and working leanVM query-budget proofs were searched; these
protocol-specific adapters reuse the existing local results directly.
`treeSimHashProgram_not_budgetCollision` from `TreeAgreement` already transports the cache guard without an honest-budget
premise, so it needs no adapter here.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeHashBudgetUse

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `TreeSimHashFinish.treeSimHash_terminal_of_honest` with the honest budget supplied. -/
theorem treeSimHash_terminal_of_honest :
    TreeSimHashTerminalBudget prims K circuits settings := by
  letI : DecidableEq E := Classical.decEq E
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  exact ThresholdLeanXmssSecurity.treeSimHash_terminal_of_honest prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)

/-- `TreeSimHashFinish.treeSimHashBoundFinal` with the honest budget supplied. -/
theorem treeSimHashBoundFinal
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings) :
    TreeSimHashBoundGoal prims K circuits settings := by
  letI : DecidableEq E := Classical.decEq E
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  exact ThresholdLeanXmssSecurity.treeSimHashBoundFinal prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (salt := salt)

variable [Fintype E] [DecidableEq E]

/-- `TreeSaltGuard.treeSimHashBoundGoal2_of_guarded` with the honest budget supplied. -/
theorem treeSimHashBoundGoal2_of_guarded
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings) :
    TreeSimHashBoundGoal2 prims K circuits settings := by
  exact ThresholdLeanXmssSecurity.treeSimHashBoundGoal2_of_guarded prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (salt := salt)
    (reuse := reuse)

/-- `TreeSaltGuard.treeSimulationHop_of_guarded` with the honest budget supplied. -/
theorem treeSimulationHop_of_guarded
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHop_of_guarded prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (reuse := reuse)
    (checkBound := checkBound)

/-- `TreeSaltStages.treeSimulationHop_of_stages` with the honest budget supplied. -/
theorem treeSimulationHop_of_stages
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (addresses : TreeSaltStagesAddresses splits) (eager : TreeSaltStagesEager splits)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHop_of_stages (prims := prims) (K := K)
    (circuits := circuits) (settings := settings)
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (splits := splits)
    (addresses := addresses)
    (eager := eager)
    (checkBound := checkBound)

/-- `TreeSaltPairs.treeSimulationHop_of_pairs` with the honest budget supplied. -/
theorem treeSimulationHop_of_pairs
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits) (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHop_of_pairs (prims := prims) (K := K)
    (circuits := circuits) (settings := settings)
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (splits := splits)
    (pairBounds := pairBounds)
    (checkBound := checkBound)

/-- `TreeFromCache.treeSimulationHopFrom_of_events2` with the honest budget supplied. -/
theorem treeSimulationHopFrom_of_events2
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseEstimate prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHopFrom prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHopFrom_of_events2 prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (reuse := reuse)
    (checkBound := checkBound)

open LifetimeBridge LifetimeJointSim

/-- `LifetimeFreshBudget.selectedFresh_of_honest_small` with the honest budget supplied. -/
theorem selectedFresh_of_honest_small
    (hb : 0 < settings.batchSize) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (input : JointInput C) (dealt : DealtInputs D input.1) (q : ℕ)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (small : q + (treeSecrets circuits settings C input.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128)
    (cache : HashCache C) :
    TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      (selectedHash K circuits settings D A Z input) cache
      (q + (treeSecrets circuits settings C input.2.2.1 - 2 * prssKeyCount C)) := by
  exact ThresholdLeanXmssSecurity.LifetimeFreshBudget.selectedFresh_of_honest_small prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (hb := hb)
    (D := D)
    (A := A)
    (Z := Z)
    (input := input)
    (dealt := dealt)
    (q := q)
    (advBudget := advBudget)
    (small := small)
    (cache := cache)

/-- `LifetimeFreshBudget.selectedFresh_reached_small` with the honest budget supplied. -/
theorem selectedFresh_reached_small
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q : ℕ) (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (p : JointInput C × HashCache C) (reached : p ∈ support (jointPrefixRun prims pre))
    (small : q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128) :
    TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      (selectedHash K circuits settings D A Z p.1) p.2
      (q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C)) := by
  exact ThresholdLeanXmssSecurity.LifetimeFreshBudget.selectedFresh_reached_small prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (hb := hb)
    (D := D)
    (pre := pre)
    (A := A)
    (Z := Z)
    (q := q)
    (advBudget := advBudget)
    (p := p)
    (reached := reached)
    (small := small)

/-- `LifetimeFreshBudget.selected_terminal_small` with the honest budget supplied. -/
theorem selected_terminal_small
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (p : JointInput C × HashCache C) (reached : p ∈ support (jointPrefixRun prims pre))
    (small : q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128)
    (r : (Bool × HiddenCache C) × HashCache C)
    (run : r ∈ support ((simulateQ (localAnswer prims)
      (selectedHash K circuits settings D A Z p.1)).run p.2))
    (good : ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2)) :
    SplitCacheBound (splitRegionCache TreeSimHashBudgetDomain r.2)
      (q0 + (q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C))) := by
  exact ThresholdLeanXmssSecurity.LifetimeFreshBudget.selected_terminal_small prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (hb := hb)
    (D := D)
    (pre := pre)
    (A := A)
    (Z := Z)
    (q0 := q0)
    (q := q)
    (preBudget := preBudget)
    (advBudget := advBudget)
    (p := p)
    (reached := reached)
    (small := small)
    (r := r)
    (run := run)
    (good := good)

open LifetimeJointSimStages

/-- `LifetimeJointSimStages.joint_hash_bound` with the honest budget supplied. -/
theorem joint_hash_bound
    (salts : JointSaltBounds prims K circuits settings)
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    (Pr[fun r => TreeSimHashBad3 D r.2 | trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree =>
        (((q0 + tailBudget (C := C) circuits settings q tree : ℕ) : ℝ) ^ 2) / 2 ^ 256) := by
  exact ThresholdLeanXmssSecurity.LifetimeJointSimStages.joint_hash_bound prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (salts := salts)
    (hb := hb)
    (D := D)
    (pre := pre)
    (A := A)
    (Z := Z)
    (q0 := q0)
    (q := q)
    (preBudget := preBudget)
    (advBudget := advBudget)

/-- `LifetimeJointSimStages.jointSimulationFromComponent_of_contextual` with the honest budget supplied. -/
theorem jointSimulationFromComponent_of_contextual
    (events : Selector C → TreeSimEvents C E)
    (hashFlag : ∀ pre top tree D A x z Z log,
      (events pre top tree D A x z Z log).1 = decide (TreeSimHashBad3 D log))
    (stages : ContextualStages prims K circuits settings events)
    (salts : JointSaltBounds prims K circuits settings)
    (checks : ContextualCheckBound prims K circuits settings events) :
    JointSimulationFromComponent prims K circuits settings := by
  exact ThresholdLeanXmssSecurity.LifetimeJointSimStages.jointSimulationFromComponent_of_contextual prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (events := events)
    (hashFlag := hashFlag)
    (stages := stages)
    (salts := salts)
    (checks := checks)

/-- `TreeEvents3.treeSimHashBoundGoal3_of_guarded` with the honest budget supplied. -/
theorem treeSimHashBoundGoal3_of_guarded
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings) :
    TreeSimHashBoundGoal3 prims K circuits settings := by
  exact ThresholdLeanXmssSecurity.treeSimHashBoundGoal3_of_guarded prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (salt := salt)
    (reuse := reuse)

/-- `TreeEvents3.treeSimulationHop_of_guarded3` with the honest budget supplied. -/
theorem treeSimulationHop_of_guarded3
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHop_of_guarded3 prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (reuse := reuse)
    (branches := branches)

/-- `TreeEvents3.treeSimulationHop_of_pairs3` with the honest budget supplied. -/
theorem treeSimulationHop_of_pairs3
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHop_of_pairs3 prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (splits := splits)
    (pairBounds := pairBounds)
    (branches := branches)

/-- `TreeSaltPairsProof.treeSimHashBoundGoal3_of_guessGuarded` with the honest budget supplied. -/
theorem treeSimHashBoundGoal3_of_guessGuarded
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuessGuarded prims K circuits settings) :
    TreeSimHashBoundGoal3 prims K circuits settings := by
  exact ThresholdLeanXmssSecurity.treeSimHashBoundGoal3_of_guessGuarded prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (salt := salt)
    (reuse := reuse)

/-- `TreeSaltPairsProof.treeSimulationHop_of_pairsGuarded` with the honest budget supplied. -/
theorem treeSimulationHop_of_pairsGuarded
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairsGuarded splits)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact ThresholdLeanXmssSecurity.treeSimulationHop_of_pairsGuarded prims K circuits settings
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (stages := stages)
    (salt := salt)
    (splits := splits)
    (pairBounds := pairBounds)
    (branches := branches)

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimHash_terminal_of_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_terminal_of_honest

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimHashBoundFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundFinal

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimHashBoundGoal2_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundGoal2_of_guarded

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHop_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_guarded

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHop_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_stages

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHop_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairs

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHopFrom_of_events2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHopFrom_of_events2

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.selectedFresh_of_honest_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedFresh_of_honest_small

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.selectedFresh_reached_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedFresh_reached_small

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.selected_terminal_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_terminal_small

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.joint_hash_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_hash_bound

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.jointSimulationFromComponent_of_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSimulationFromComponent_of_contextual

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimHashBoundGoal3_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundGoal3_of_guarded

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHop_of_guarded3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_guarded3

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHop_of_pairs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairs3

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimHashBoundGoal3_of_guessGuarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundGoal3_of_guessGuarded

/-- info: 'ThresholdLeanXmssSecurity.TreeHashBudgetUse.treeSimulationHop_of_pairsGuarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairsGuarded

end ThresholdLeanXmssSecurity.TreeHashBudgetUse
