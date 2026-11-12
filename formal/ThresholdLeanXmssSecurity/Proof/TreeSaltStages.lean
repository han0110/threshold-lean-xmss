import ThresholdLeanXmssSecurity.Proof.TreeAgreement

/-!
# The two-stage salt addresses of the tree simulation hop

`TreeSaltSetupAddresses` is false (see `TreeAgreement.lean`). The labels where the second run of
a bottom tree reads its salts depend on the encoding, and the encoding is known only after the
first run. This module fixes the salt addresses in two stages.

* `TreeSaltStageSplit` writes the run after the PRSS setup as `first` and then `rest`. The stage
  point is the end of the first run. Each final log extends the log at the stage point.
  `TreeSaltStageSplits` is one such split for each run. The two bound Props and the hop take
  this family as a parameter, so they claim nothing about a split that is not chosen.
* `TreeSaltStagesAddresses` states the two covers. Stage 1 fixes a table from the end of the
  setup. It covers the log at the stage point. Stage 2 adds a table from the stage point. The two
  tables together have at most `treeBatches * termCount` addresses and cover the final log.
* `TreeSaltStagesEager` states that the salt reuse after the setup is at most the eager bad event
  of `treeSaltStagesGame`. The game draws the stage point, and then one fresh uniform table over
  the addresses of both stages.
* `treeSaltStagesGame_le` is the birthday bound of the game.
* `treeSimSaltReuseGuarded_of_stages` gives `TreeSimSaltReuseGuarded`, and
  `treeSimulationHop_of_stages` gives the hop. The bound and the sum of
  `treeSimHash_union_guarded` do not change.

The game gives the stage-2 choice no access to the table. So `TreeSaltStagesEager` holds only if
the stage-2 labels and the known stage-2 salts do not depend on the hidden stage-1 salts. A pair
of a hidden stage-1 salt and a known stage-2 salt is paid only under this condition.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A split of a logged run at a stage point. `log m` is the log at the stage point `m`, and each
final log of `rest m` extends it. -/
structure TreeSaltStageSplit (run : ProbComp (Bool × TreeSimLog C)) where
  View : Type
  first : ProbComp View
  log : View → TreeSimLog C
  rest : View → ProbComp (Bool × TreeSimLog C)
  split : run = first >>= rest
  extend : ∀ m ∈ support first, ∀ r ∈ support (rest m), log m <+: r.2

/-- The two covers of a split. The stage-1 table covers the log at the stage point. The stage-1
table and the stage-2 table of `m` together are injective, have at most `bound` addresses, and
cover each final log. Each cover holds outside a budget collision. -/
def TreeSaltStagesCover {run : ProbComp (Bool × TreeSimLog C)} (split : TreeSaltStageSplit run)
    (bound : ℕ) (n₁ : ℕ) (addr₁ : Fin n₁ → C.Term × HashOutput × ℕ) (n₂ : split.View → ℕ)
    (addr₂ : (m : split.View) → Fin (n₂ m) → C.Term × HashOutput × ℕ) : Prop :=
  ∀ m ∈ support split.first,
    (¬ TreeSimHashBudgetCollision (split.log m) → TreeSaltAddressesCover addr₁ (split.log m)) ∧
    Function.Injective (Fin.append addr₁ (addr₂ m)) ∧ n₁ + n₂ m ≤ bound ∧
    ∀ r ∈ support (split.rest m),
      ¬ TreeSimHashBudgetCollision r.2 → TreeSaltAddressesCover (Fin.append addr₁ (addr₂ m)) r.2

/-- A split of each run after the PRSS setup. The intended stage point is the end of the first
run of the tree. -/
def TreeSaltStageSplits : Type 1 :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C),
    TreeSaltStageSplit (treeSaltAfterSetup prims K circuits settings top tree D A x Z p)

variable {prims K circuits settings}

/-- The salt addresses in two stages at the stage points of `splits`. The end of the PRSS setup
fixes the stage-1 table. The stage point `m` fixes the stage-2 table. -/
def TreeSaltStagesAddresses (splits : TreeSaltStageSplits prims K circuits settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ p ∈ support (treeSaltSetup prims D A x z),
    ∃ (n₁ : ℕ) (addr₁ : Fin n₁ → C.Term × HashOutput × ℕ)
      (n₂ : (splits top tree D A x Z p).View → ℕ)
      (addr₂ : (m : (splits top tree D A x Z p).View) → Fin (n₂ m) → C.Term × HashOutput × ℕ),
      TreeSaltStagesCover (splits top tree D A x Z p) (treeBatches settings tree * termCount C)
        n₁ addr₁ n₂ addr₂

/-- The eager game of two stages. It draws the stage point, then one fresh uniform table over
the addresses of both stages, and reports the eager bad event. -/
def treeSaltStagesGame {View : Type} (first : ProbComp View) (n₁ : ℕ) (n₂ : View → ℕ)
    (hidden : (m : View) → Fin (n₁ + n₂ m) → Prop)
    (known : (m : View) → Fin (n₁ + n₂ m) → Fin 256 → Bit) : ProbComp Bool := do
  let m ← first
  let table ← $ᵗ (Fin (n₁ + n₂ m) → Fin 256 → Bit)
  pure (decide (TreeSaltEagerBad (hidden m) (known m) table))

/-- After the PRSS setup, the salt reuse is at most the bad event of the eager game of two
stages at the stage points of `splits`. The hidden salts of each stage are uniform and independent
of the view before them. -/
def TreeSaltStagesEager (splits : TreeSaltStageSplits prims K circuits settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSaltSetup prims D A x z),
    ∀ (n₁ : ℕ) (addr₁ : Fin n₁ → C.Term × HashOutput × ℕ)
      (n₂ : (splits top tree D A x Z p).View → ℕ)
      (addr₂ : (m : (splits top tree D A x Z p).View) → Fin (n₂ m) → C.Term × HashOutput × ℕ),
      TreeSaltStagesCover (splits top tree D A x Z p) (treeBatches settings tree * termCount C)
        n₁ addr₁ n₂ addr₂ →
      ∃ known : (m : (splits top tree D A x Z p).View) → Fin (n₁ + n₂ m) → Fin 256 → Bit,
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
          treeSaltAfterSetup prims K circuits settings top tree D A x Z p] ≤
          Pr[= true | treeSaltStagesGame (splits top tree D A x Z p).first n₁ n₂
            (fun m i => ¬ KnownTo D.1 (Fin.append addr₁ (addr₂ m) i).1) known]

/-- The birthday bound of the eager game of two stages, when each stage point has at most `N`
addresses. -/
theorem treeSaltStagesGame_le {View : Type} (first : ProbComp View) (n₁ : ℕ) (n₂ : View → ℕ)
    (hidden : (m : View) → Fin (n₁ + n₂ m) → Prop)
    (known : (m : View) → Fin (n₁ + n₂ m) → Fin 256 → Bit) {N : ℕ}
    (hn : ∀ m ∈ support first, n₁ + n₂ m ≤ N) :
    Pr[= true | treeSaltStagesGame first n₁ n₂ hidden known] ≤ ((N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
  rw [← probEvent_eq_eq_probOutput]
  unfold treeSaltStagesGame
  apply probEvent_bind_le_of_forall_le
  intro m hm
  refine le_trans (le_of_eq ?_) (treeSaltEager_le (hn m hm) (hidden m) (known m))
  rw [bind_pure_comp, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

/-- The guarded estimate from the two-stage addresses and the eager game of two stages. -/
theorem treeSimSaltReuseGuarded_of_stages
    (splits : TreeSaltStageSplits prims K circuits settings)
    (addresses : TreeSaltStagesAddresses splits) (eager : TreeSaltStagesEager splits) :
    TreeSimSaltReuseGuarded prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  have hle : Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
    rw [treeSaltSetup_split]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨n₁, addr₁, n₂, addr₂, hcover⟩ := addresses hb top tree D A x z Z hx p hp
    obtain ⟨known, hk⟩ := eager hb top tree D A x z Z q hx hq hsmall p hp n₁ addr₁ n₂ addr₂ hcover
    exact hk.trans (treeSaltStagesGame_le (splits top tree D A x Z p).first n₁ n₂ _ known
      fun m hm => (hcover m hm).2.2.1)
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp [ENNReal.toReal_div]

/-- The full hop from the old check goal, the two hash estimates, the two-stage addresses and the
eager game of two stages. -/
theorem treeSimulationHop_of_stages
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (addresses : TreeSaltStagesAddresses splits) (eager : TreeSaltStagesEager splits)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_guarded prims K circuits settings stages honest salt
    (treeSimSaltReuseGuarded_of_stages splits addresses eager) checkBound

/-- info: 'ThresholdLeanXmssSecurity.treeSaltStagesGame_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltStagesGame_le

/-- info: 'ThresholdLeanXmssSecurity.treeSimSaltReuseGuarded_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimSaltReuseGuarded_of_stages

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_stages

end ThresholdLeanXmssSecurity
