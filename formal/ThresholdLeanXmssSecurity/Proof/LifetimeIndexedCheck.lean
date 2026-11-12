import ThresholdLeanXmssSecurity.Proof.LifetimeContextual
import ThresholdLeanXmssSecurity.Proof.LifetimeJointSalt
import ThresholdLeanXmssSecurity.Proof.TreeCheckNoCommit

/-!
# Indexed checks on the actual selected audit

The uncounted commitment branch starts from the selector's retained cache and
log. `SetupFresh` holds there because every selector query is counted. The
reveal and echo rounds retain their one-guess estimate at each reached prefix,
including prefixes that select different ceremonies.

The proof uses the `rows_finish_guess` potential argument and preserves the
full selected input, state and transcript.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeIndexedCheck

open LifetimeBridge LifetimeJointSimStages LifetimeContextual

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} (prims : Primitives)
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

local instance : DecidableEq (JointInput C × TreeSimState C) := Classical.decEq _

/-- Every selector query is counted in the retained transcript. -/
theorem prefix_fresh (D : C.Coalition) (pre : Selector C)
    (p : JointInput C × TreeSimState C) (hp : p ∈ support (loggedPrefix prims D pre)) :
    SetupFresh D p.2 :=
  logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D)
    (jointPrefix pre) _ (setupFresh_empty D) p hp

/-- The actual initialization and setup, starting from a retained world. -/
def setupFrom (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (s : TreeSimState C) := do
  let start ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.start (corruptInputs D x) z))).run s
  (executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds start.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run start.2

/-- The setup bound from any state satisfying the counted-prefix invariant. -/
theorem setupFrom_guess (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (s : TreeSimState C) (fresh : SetupFresh D s) :
    Pr[SetupGuessEvent D | setupFrom prims D A x z s] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  unfold setupFrom
  refine probEvent_bind_le_of_forall_le fun start hstart => ?_
  have hs0 : SetupFresh D start.2 :=
    logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D) _ _
      fresh start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase]
  change Pr[SetupGuessEvent D | (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) start.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run start.2] ≤ _
  rw [executePhase_prssSetup_prefix]
  simp only [simulateQ_bind, StateT.run_bind]
  refine probEvent_bind_le_of_forall_le fun data hdata => ?_
  have hs1 : SetupFresh D data.2 :=
    logged_free_inv prims D (FreeCorruptQuery D) (SetupFresh D) (setupFresh_free prims D) _
      (prssInitialData_freeCorrupt_zero D) _ hs0 data hdata
  refine probEvent_bind_le_of_forall_le fun adv hadv => ?_
  have hs2 : SetupFresh D adv.2 :=
    logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D) _ _ hs1 adv hadv
  split_ifs with habort
  · refine le_of_eq_of_le (probEvent_eq_zero fun y hy hev => ?_) zero_le
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hy
    subst y
    obtain ⟨⟨k, -, hk⟩, -⟩ := hev
    exact hk rfl
  · simp only [simulateQ_bind, StateT.run_bind]
    refine probEvent_bind_le_of_forall_le fun adv' hadv' => ?_
    have hs3 : SetupFresh D adv'.2 :=
      logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D) _ _ hs2 adv' hadv'
    have h := rows_finish_guess prims D A
      (fun i => (C.parties.any fun j => Msg.isAbort (prssCommitInbox D data.1 adv.1.2 i j)) = false)
      (fun i => (data.1 i).1) (prssCommitInbox D data.1 adv.1.2) adv'.1.2 adv'.1.1 adv'.2 hs3
    simpa only [simulateQ_bind, StateT.run_bind] using h

/-- Splitting the audit preserves its initial state and complete final state. -/
theorem audit_split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (s : TreeSimState C) :
    (simulateQ (treeSimLoggedWorld prims D)
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)).run s =
      (setupFrom prims D A x z s >>= fun p =>
        (simulateQ (treeSimLoggedWorld prims D)
          (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2) := by
  obtain ⟨fuel, hf⟩ : ∃ fuel, ceremonyFuel circuits settings = fuel + 3 :=
    ⟨ceremonyFuel circuits settings - 3, by simp only [ceremonyFuel, setupRounds]; omega⟩
  have hc : (fun i => treeSimCheckCeremonyAudit K circuits settings i (x i) top tree) =
      fun i => prssSetup i >>= fun prss =>
        treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree := rfl
  unfold treeSimCheckAuditedGame realExecution setupFrom auditAfterProgram
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro start
  rw [hf, hc, executePhase_prssSetup_bind]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_executePhase, treeSimRealRoles,
    Nat.add_sub_cancel]
  rfl

/-- Any honest output with an uncounted opening pays a fresh guess from the
retained state, without resampling the selecting prefix. -/
theorem audit_guess (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (s : TreeSimState C) (fresh : SetupFresh D s) :
    Pr[fun r => (∃ i, i ∉ D.1 ∧ r.1.2.2 i ≠ none) ∧ TreeCheckUncounted D r.2.2 |
      (simulateQ (treeSimLoggedWorld prims D)
        (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)).run s] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [audit_split]
  refine le_trans ?_ (setupFrom_guess prims D A x z s fresh)
  refine probEvent_bind_le_probEvent fun p _ hng => probEvent_eq_zero fun y hy hev => hng ?_
  obtain ⟨⟨i, hi, hout⟩, hunc⟩ := hev
  refine ⟨?_, treeCheckUncounted_prefix D (treeSimLoggedWorld_prefix prims D _ p.2 y hy) hunc
    (treeCheckAfterSetupNoCommit_of_audit prims K circuits settings
      (treeCheckAfterSetupAuditNoCommit K circuits settings) top tree D A x Z p.1.1 p.1.2 p.2 y hy)⟩
  by_contra hn
  push Not at hn
  exact hout (auditAfter_none prims K circuits settings top tree D A x Z p.1.1 p.1.2 hn p.2 y hy i hi)

set_option linter.constructorNameAsVariable false in
/-- A selected event is averaged over the actual complete prefix state. -/
theorem selectedTrace_event_le {α : Type} (D : C.Coalition) (pre : Selector C)
    (tail : JointInput C → OracleComp (WorldSpec C) α)
    (event : (JointInput C × α) × TreeSimLog C → Prop) (e : Tree → ℝ)
    (bound : ∀ p ∈ support (loggedPrefix prims D pre),
      (Pr[fun r => event ((p.1, r.1), r.2.2) |
        (simulateQ (treeSimLoggedWorld prims D) (tail p.1)).run p.2]).toReal ≤ e p.1.2.2.1) :
    (Pr[event | selectedTrace prims D pre tail]).toReal ≤ jointError prims pre e := by
  classical
  rw [selectedTrace, LifetimeJointSim.prob_bind_eq_sum, LifetimeJointSalt.jointError_logged prims D pre]
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  simp only [probEvent_map, Function.comp_def]
  exact bound p (by rwa [mem_finSupport_iff_mem_support] at hp)

/-- Each uncounted indexed event costs one fresh-hash guess, relaxed to the
two-guess allowance and weighted by the selector's batch activation. -/
theorem uncounted_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (j : ℕ) :
    (Pr[fun r => IndexedBad prims K circuits settings D pre A j r ∧ TreeCheckUncounted D r.2 |
      auditTrace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => if j < treeBatches settings tree then
        2 * (2 : ℝ)⁻¹ ^ 256 else 0) := by
  apply selectedTrace_event_le
  intro p hp
  by_cases active : j < treeBatches settings p.1.2.2.1
  · rw [if_pos active]
    have estimate := (audit_guess prims K circuits settings p.1.2.1 p.1.2.2.1 D A p.1.1
      p.1.2.2.2 Z p.2 (prefix_fresh prims D pre p hp)).trans guess_le_bound
    have bound : Pr[fun r =>
        IndexedBad prims K circuits settings D pre A j ((p.1, r.1), r.2.2) ∧
          TreeCheckUncounted D r.2.2 |
        (simulateQ (treeSimLoggedWorld prims D) (auditTail K circuits settings D A Z p.1)).run p.2] ≤
        ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256) := by
      refine (probEvent_mono ?_).trans estimate
      intro r _ bad
      obtain ⟨⟨_, _, _, _, _, _, i, value, records, _, _, _, _, _, hi, hout, _⟩, hunc⟩ := bad
      exact ⟨⟨i, hi, by rw [hout]; exact Option.some_ne_none _⟩, hunc⟩
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top bound).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  · rw [if_neg active]
    have zero : Pr[fun r =>
        IndexedBad prims K circuits settings D pre A j ((p.1, r.1), r.2.2) ∧
          TreeCheckUncounted D r.2.2 |
        (simulateQ (treeSimLoggedWorld prims D) (auditTail K circuits settings D A Z p.1)).run p.2] = 0 :=
      probEvent_eq_zero fun _ _ bad => active bad.1.choose
    exact le_of_eq (congrArg ENNReal.toReal zero)

/-- The counted branch of the same actual joint audit. One counted non-coin
commitment pays for the setup guess, leaving the original check budget minus
one. The branch is empty at zero budget. -/
def CountedCheckBounds : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q0 + q < 2 ^ 128 →
    ∀ j ∈ Finset.range (ceremonyBatches settings),
      (Pr[fun r => IndexedBad prims K circuits settings D pre A j r ∧
          ¬ TreeCheckUncounted D r.2 |
        auditTrace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => if j < treeBatches settings tree then
        if q0 + q = 0 then 0 else
          checkErrorOf (E := E) (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
            (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q0 + q - 1)
        else 0)

/-- The uncounted estimate and the counted certificate give exactly the
original indexed target, with its selected-tree weights and full budget. -/
theorem indexedCheckBounds_of_counted
    (counted : CountedCheckBounds prims K circuits settings) :
    IndexedCheckBounds prims K circuits settings := by
  intro hb D pre A Z q0 q prefixBudget adversaryBudget small j hj
  have uncounted := uncounted_bound prims K circuits settings D pre A Z j
  have counted := counted hb D pre A Z q0 q prefixBudget adversaryBudget small j hj
  have split : Pr[IndexedBad prims K circuits settings D pre A j |
      auditTrace prims K circuits settings D pre A Z] ≤
      Pr[fun r => IndexedBad prims K circuits settings D pre A j r ∧ TreeCheckUncounted D r.2 |
        auditTrace prims K circuits settings D pre A Z] +
      Pr[fun r => IndexedBad prims K circuits settings D pre A j r ∧ ¬ TreeCheckUncounted D r.2 |
        auditTrace prims K circuits settings D pre A Z] := by
    refine (probEvent_mono'' fun r bad => ?_).trans (probEvent_or_le _ _ _)
    by_cases h : TreeCheckUncounted D r.2
    · exact .inl ⟨bad, h⟩
    · exact .inr ⟨bad, h⟩
  have realSplit := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) split
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at realSplit
  apply (realSplit.trans (add_le_add uncounted counted)).trans
  rw [← jointError_add]
  unfold jointError
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  dsimp only [selectedError]
  by_cases active : j < treeBatches settings p.1.2.2.1
  · simp only [if_pos active]
    by_cases zero : q0 + q = 0
    · simp only [zero, ↓reduceIte, add_zero]
      exact checkErrorOf_setup_zero K _ _
    · rw [if_neg zero]
      have one := checkErrorOf_setup_succ K
        (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
        (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q0 + q - 1)
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)] at one
  · simp only [if_neg active, add_zero, le_refl]

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.prefix_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_fresh

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.setupFrom_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setupFrom_guess

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.audit_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms audit_split

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.audit_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms audit_guess

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.selectedTrace_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedTrace_event_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.uncounted_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uncounted_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIndexedCheck.indexedCheckBounds_of_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms indexedCheckBounds_of_counted

end ThresholdLeanXmssSecurity.LifetimeIndexedCheck
