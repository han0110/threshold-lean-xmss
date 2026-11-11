import ThresholdLeanXmssSecurity.Proof.TreeLockstep
import ThresholdLeanXmssSecurity.Proof.TreeSaltPairs
import ThresholdLeanXmssSecurity.Proof.TreeCheckCut

/-!
# The tree simulation events with the budget collision

The lockstep links, the check setup branches and the salt guard all exclude
`TreeSimHashBudgetCollision`. The hash event of `treeSimEvents2` excludes only the narrower
`TreeSimHashCollision`. `treeSimEvents3` adds the budget collision to the hash event.

* `treeSimHashBoundGoal3_of_guarded` gives the hash goal. The budget collision is the first term
  of `treeSimHash_union_guarded`, so the sum and the arithmetic do not change.
* `treeSimStagesGoal3_of_goal2` and `treeSimCheckBoundGoal3_of_goal2` move the old goals. The
  stages read the events only through the two flags, and the new flags are larger.
* `treeSimStagesGoal3_of_cores` gives the stages goal from cores that exclude `TreeSimBad3`.
* `TreeSimCheckSetupBranches3` is `TreeSimCheckSetupBranches` outside the budget collision. Two
  honest operators that pass the echo with different `.sharedKeys` lists give a budget collision.
  The branch `uncounted` stays, because an opening that matches a corrupt commitment with no
  earlier query is a guess of one fresh answer and not a collision.
* `treeTwinDigestGoal3_of_lockstep` and `treeLockstepRecords_common_of_agree` are the lockstep
  links on the new guard, with no extra hypothesis.
* `treeSimulationHop_of_pairs3` and `treeSimulationHop_of_setup3` give the hop.

`TreeStagesTwinRelation` and `treeSimStagesGoal2_of_relation` use `TreeSimBad2`. The twin route
to `TreeSimStagesGoal3` needs a copy of them with `TreeSimBad3`.
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

theorem treeSimHashBudgetCollision_mono {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSimHashBudgetCollision a → TreeSimHashBudgetCollision b := by
  have mem : ∀ {v}, v ∈ a → v ∈ b := fun hv => hab.sublist.subset hv
  rintro ⟨q, r, h, hq, hr, hne, ha, hb⟩
  exact ⟨q, r, h, hq, hr, hne, ha.imp mem mem, hb.imp mem mem⟩

/-- The hash event of `treeSimEvents2` with the budget collision. -/
def TreeSimHashBad3 (D : C.Coalition) (log : TreeSimLog C) : Prop :=
  TreeSimHashBad2 D log ∨ TreeSimHashBudgetCollision log

/-- The budget collision takes the place of the collision. -/
theorem treeSimHashBad3_iff (D : C.Coalition) (log : TreeSimLog C) :
    TreeSimHashBad3 D log ↔
      TreeSimHashBudgetCollision log ∨ TreeSimSaltGuess D log ∨ TreeSimSaltReuse D log := by
  have hc := treeSimHashBudgetCollision_of_collision log
  simp only [TreeSimHashBad3, TreeSimHashBad2, TreeSimHashBad]
  tauto

theorem treeSimHashBad3_mono (D : C.Coalition) {a b : TreeSimLog C}
    (hab : a <+: b) : TreeSimHashBad3 D a → TreeSimHashBad3 D b :=
  Or.imp (treeSimHashBad2_mono D hab) (treeSimHashBudgetCollision_mono hab)

/-- The events of `treeSimEvents2` with the budget collision in the hash event. -/
def treeSimEvents3 : TreeSimEvents C E := fun top tree D A x z _ log =>
  (decide (TreeSimHashBad3 D log),
    decide (¬ TreeSimHashBad3 D log ∧ TreeSimWrongOutput prims K circuits settings top tree D A x z log))

/-- The sticky predicate of `treeSimEvents3`. -/
def TreeSimBad3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) : Prop :=
  TreeSimHashBad3 D log ∨ TreeSimWrongOutput prims K circuits settings top tree D A x z log

theorem treeSimBad3_mono (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSimBad3 prims K circuits settings top tree D A x z a →
      TreeSimBad3 prims K circuits settings top tree D A x z b := by
  rintro ((h | h) | h)
  · exact (treeSimBad2_mono prims K circuits settings top tree D A x z hab (Or.inl h)).elim
      (fun h' => Or.inl (Or.inl h')) Or.inr
  · exact Or.inl (Or.inr (treeSimHashBudgetCollision_mono hab h))
  · exact (treeSimBad2_mono prims K circuits settings top tree D A x z hab (Or.inr h)).elim
      (fun h' => Or.inl (Or.inl h')) Or.inr

theorem treeSimBad3_of_bad2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) :
    TreeSimBad2 prims K circuits settings top tree D A x z log →
      TreeSimBad3 prims K circuits settings top tree D A x z log :=
  Or.imp Or.inl id

theorem treeSimBad3_of_bad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) :
    TreeSimBad prims K circuits settings top tree D A x z log →
      TreeSimBad3 prims K circuits settings top tree D A x z log := fun h =>
  treeSimBad3_of_bad2 prims K circuits settings top tree D A x z log
    (treeSimBad2_of_bad prims K circuits settings top tree D A x z log h)

theorem not_budgetCollision_of_not_bad3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) (good : ¬ TreeSimBad3 prims K circuits settings top tree D A x z log) :
    ¬ TreeSimHashBudgetCollision log := fun h => good (Or.inl (Or.inr h))

/-- The two recorded flags of `treeSimEvents3` are exactly the sticky predicate. -/
theorem treeSimEvents3_bad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    ((treeSimEvents3 prims K circuits settings top tree D A x z Z log).1 = true ∨
      (treeSimEvents3 prims K circuits settings top tree D A x z Z log).2 = true) ↔
      TreeSimBad3 prims K circuits settings top tree D A x z log := by
  simp only [treeSimEvents3, decide_eq_true_eq, TreeSimBad3]
  tauto

/-- The stages goal for `treeSimEvents3`. -/
def TreeSimStagesGoal3 : Prop :=
  TreeSimStages prims K circuits settings (treeSimEvents3 prims K circuits settings)

/-- The hash goal for `treeSimEvents3`, with the budget of `TreeSimHashBoundGoal`. -/
def TreeSimHashBoundGoal3 : Prop :=
  TreeSimHashBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents3 prims K circuits settings))

/-- The check goal for `treeSimEvents3`, with the budget of `TreeSimCheckBoundGoal`. -/
def TreeSimCheckBoundGoal3 : Prop :=
  TreeSimCheckBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents3 prims K circuits settings))

/-- Assembly of the three goals of `treeSimEvents3`. -/
theorem treeSimulationHopClosed3
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (hashBound : TreeSimHashBoundGoal3 prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop prims K circuits settings (treeSimEvents3 prims K circuits settings)
    stages hashBound checkBound

/-- The recorded hash flag of `treeSimEvents3` is `TreeSimHashBad3` on the actual log. -/
theorem treeSimHash_flag3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents3 prims K circuits settings)
        top tree D A x z Z] =
    Pr[fun r => TreeSimHashBad3 D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] := by
  simp only [treeSimTrace, treeSimEvents3, probEvent_map, Function.comp_def, decide_eq_true_eq]

/-- The union of `treeSimHash_union_guarded` for `TreeSimHashBad3`. The added budget collision is
the first term of that union, so the three terms do not change. -/
theorem treeSimHash_union3 {α : Type} (D : C.Coalition) (p : ProbComp (α × TreeSimLog C)) :
    (Pr[fun r => TreeSimHashBad3 D r.2 | p]).toReal ≤
      (Pr[fun r => TreeSimHashBudgetCollision r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | p]).toReal := by
  have h1 := probEvent_or_le p (fun r => TreeSimHashBudgetCollision r.2)
    (fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
  have h2 := probEvent_or_le p
    (fun r => TreeSimHashBudgetCollision r.2 ∨ (¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2))
    (fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2)
  have hle : Pr[fun r => TreeSimHashBad3 D r.2 | p] ≤
      Pr[fun r => TreeSimHashBudgetCollision r.2 | p] +
      Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p] +
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | p] := by
    refine le_trans (probEvent_mono ?_) (h2.trans (add_le_add h1 le_rfl))
    intro r _ h
    by_cases hb : TreeSimHashBudgetCollision r.2
    · exact Or.inl (Or.inl hb)
    rcases h with ((hc | hg) | hu) | hc
    · exact (hb (treeSimHashBudgetCollision_of_collision _ hc)).elim
    · exact Or.inl (Or.inr ⟨fun hc => hb (treeSimHashBudgetCollision_of_collision _ hc), hg⟩)
    · exact Or.inr ⟨hb, hu⟩
    · exact (hb hc).elim
  have hab := ENNReal.add_ne_top.mpr ⟨probEvent_ne_top (mx := p)
    (p := fun r => TreeSimHashBudgetCollision r.2), probEvent_ne_top (mx := p)
    (p := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)⟩
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hab, probEvent_ne_top⟩) hle
  rwa [ENNReal.toReal_add hab probEvent_ne_top,
    ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at h

/-- The hash goal of `treeSimEvents3` from the honest count, the salt estimate and the guarded
salt reuse estimate. The sum is the sum of `treeSimHashBoundGoal2_of_guarded`. The budget
collision costs `N (N - 1) / 2^257`, the salt guess `2 H (q + H) / 2^256`, and the salt reuse
`M² / 2^257` with `M = treeBatches * termCount`. These fit in `N² / 2^256` with
`N = q + S'`, and `treeSim_hashBudget` puts `N² / 2^256` under `treeHashError - keySplit`. -/
theorem treeSimHashBoundGoal3_of_guarded
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings) :
    TreeSimHashBoundGoal3 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  by_cases hlarge : 2 ^ 128 ≤ N
  · apply le_trans _ (treeSimHash_unit_budget _ hlarge)
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (probEvent_le_one (mx := treeSimTrace prims K circuits settings
        (treeSimEvents3 prims K circuits settings) top tree D A x z Z) (p := fun r => r.2.1 = true))
  have hn : N < 2 ^ 128 := Nat.lt_of_not_ge hlarge
  have cert := treeSimHash_terminal_fresh prims K circuits settings top tree D A x z Z q hq hn
    (treeSimHash_terminal_of_honest prims K circuits settings honest hb top tree D A x z Z q hx hq hn)
  have h := treeSimHash_logged_budget_birthday prims D
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) N cert
  rw [treeSim_localReal_eq K circuits settings top tree D A x z Z] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] at hreal
  have hc : (Pr[fun r => TreeSimHashBudgetCollision r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
        ((N ^ 2 : ℕ) : ℝ) / (2 * 2 ^ 256) := by
    refine hreal.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hN : N * (N - 1) ≤ N ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_left N (Nat.sub_le N 1)
    exact_mod_cast hN
  rw [treeSimHash_flag3]
  refine (treeSimHash_union3 D _).trans ((add_le_add (add_le_add hc
    (salt hb top tree D A x z Z q hx hq hsmall)) (reuse hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [N, Nat.cast_pow, Nat.cast_add]
  apply treeSimHash_union2_arith _ _ _ _ (by positivity) (by positivity) (by positivity)
  have hs : 2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) +
      2 * ((treeBatches settings tree * termCount C : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_reuse_capacity (C := C) circuits settings tree
  linarith

/-- The hash goal of `treeSimEvents3` lies under the hash part of the hop error. -/
theorem treeSimHashBoundGoal3_le_hashError (hash : TreeSimHashBoundGoal3 prims K circuits settings)
    (hb : 0 < settings.batchSize) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hx : DealtInputs D x)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (hsmall : q < 2 ^ 128) :
    Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents3 prims K circuits settings)
        top tree D A x z Z].toReal ≤ treeHashError circuits settings C tree q - keySplit C q :=
  (hash hb top tree D A x z Z q hx hq hsmall).trans (treeSim_hashBudget circuits settings tree q)

/-- The round interface moves to events whose recorded flags are larger. Only `observeGood` and
`badRecorded` read the events. -/
def treeSimRoundStages_weaken {events events' : TreeSimEvents C E}
    (flags : ∀ top tree D (A : Adversary C E (Keys C) PEmpty PEmpty) x z Z log,
      ((events top tree D A x z Z log).1 = true ∨ (events top tree D A x z Z log).2 = true) →
      ((events' top tree D A x z Z log).1 = true ∨ (events' top tree D A x z Z log).2 = true))
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs
      z Z dealt state s) :
    TreeSimRoundStages prims K circuits settings events' top tree D A parameter seeds pairs
      z Z dealt state s where
  Bad := stages.Bad
  Inv := stages.Inv
  stage := stages.stage
  Q := stages.Q
  entry := stages.entry
  noSetup := stages.noSetup
  badPersistent := stages.badPersistent
  done := stages.done
  output := stages.output
  peerBoundary := stages.peerBoundary
  collectorBoundary := stages.collectorBoundary
  collectorNextBoundary := stages.collectorNextBoundary
  rerandBoundary := stages.rerandBoundary
  coinBoundary := stages.coinBoundary
  extendMultBoundary := stages.extendMultBoundary
  checkBoundary := stages.checkBoundary
  openingBoundary := stages.openingBoundary
  emptyOpeningBoundary := stages.emptyOpeningBoundary
  ceremony := stages.ceremony
  observeGood a b hab := OracleComp.ProgramLogic.Relational.relTriple_post_mono
    (stages.observeGood a b hab) (fun _ _ h => h.imp_left (flags _ _ _ _ _ _ _ _))
  badRecorded t ht := flags _ _ _ _ _ _ _ _ (stages.badRecorded t ht)

/-- The stages goal moves to events whose recorded flags are larger. -/
theorem treeSimStages_weaken {events events' : TreeSimEvents C E}
    (flags : ∀ top tree D (A : Adversary C E (Keys C) PEmpty PEmpty) x z Z log,
      ((events top tree D A x z Z log).1 = true ∨ (events top tree D A x z Z log).2 = true) →
      ((events' top tree D A x z Z log).1 = true ∨ (events' top tree D A x z Z log).2 = true))
    (stages : TreeSimStages prims K circuits settings events) :
    TreeSimStages prims K circuits settings events' := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  obtain ⟨padding, hpadding⟩ := stages hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨st⟩ := hpadding r hr
  exact ⟨treeSimRoundStages_weaken prims K circuits settings flags st⟩

/-- The stages goal of `treeSimEvents2` gives the stages goal of `treeSimEvents3`. -/
theorem treeSimStagesGoal3_of_goal2 (stages : TreeSimStagesGoal2 prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStages_weaken prims K circuits settings (fun top tree D A x z Z log h =>
    (treeSimEvents3_bad prims K circuits settings top tree D A x z Z log).mpr
      (treeSimBad3_of_bad2 prims K circuits settings top tree D A x z log
        ((treeSimEvents2_bad prims K circuits settings top tree D A x z Z log).mp h))) stages

/-- The check flag of `treeSimEvents3` implies the check flag of `treeSimEvents2`. -/
theorem treeSimCheckBoundGoal3_of_goal2
    (check : TreeSimCheckBoundGoal2 prims K circuits settings) :
    TreeSimCheckBoundGoal3 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  refine le_trans (ENNReal.toReal_mono probEvent_ne_top ?_)
    (check hb top tree D A x z Z q hx hq hsmall)
  simp only [treeSimTrace, probEvent_map]
  apply probEvent_mono
  intro r _ h
  simp only [Function.comp_apply, treeSimEvents3, treeSimEvents2, TreeSimHashBad3,
    decide_eq_true_eq] at h ⊢
  tauto

/-- The round interface of `treeSimEvents3` from its core, as `treeSimRoundCore_stages2`. The core
excludes `TreeSimBad3`, so it may assume no budget collision. -/
def treeSimRoundCore_stages3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (core : TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z dealt state s
      (fun t => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2)) :
    TreeSimRoundStages prims K circuits settings (treeSimEvents3 prims K circuits settings)
      top tree D A parameter seeds pairs z Z dealt state s where
  Bad t := TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2
  Inv := core.Inv
  stage := core.stage
  Q := TreeSimFinalRel D A dealt.1
  entry := core.entry
  noSetup := core.noSetup
  badPersistent _ _ hp := treeSimBad3_mono prims K circuits settings top tree D A _ z hp
  done := core.done
  output a b hab hgood := by
    obtain ⟨replay, state, cache, corrupt, success⟩ := core.outputEvidence a b hab hgood
    exact treeSim_final_of_replay prims K circuits settings top tree D A parameter seeds pairs z dealt
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      replay (fun h => hgood (treeSimBad3_of_bad prims K circuits settings top tree D A _ z _ h))
      state cache corrupt success
  peerBoundary := core.peerBoundary
  collectorBoundary := core.collectorBoundary
  collectorNextBoundary := core.collectorNextBoundary
  rerandBoundary := core.rerandBoundary
  coinBoundary := core.coinBoundary
  extendMultBoundary := core.extendMultBoundary
  checkBoundary := core.checkBoundary
  openingBoundary := core.openingBoundary
  emptyOpeningBoundary := core.emptyOpeningBoundary
  ceremony := core.ceremony
  observeGood a b hab := OracleComp.ProgramLogic.Relational.relTriple_post_mono
    (treeSim_observe_good prims D A Z dealt.1 a b hab) (fun _ _ he => Or.inr (by rw [he]))
  badRecorded t ht := (treeSimEvents3_bad prims K circuits settings top tree D A _ z Z t.2).mpr ht

/-- The stages goal of `treeSimEvents3` from cores that exclude `TreeSimBad3`. -/
theorem treeSimStagesGoal3_of_cores
    (cores : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
      (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
      ∃ padding : OracleComp (LocalSpec C) Unit,
      ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
      Nonempty (TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z p.1 p.2.1
        ((r.2, p.2.2.1.2), p.2.2.2)
        (fun t => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2))) :
    TreeSimStagesGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  obtain ⟨padding, hpadding⟩ := cores hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨core⟩ := hpadding r hr
  exact ⟨treeSimRoundCore_stages3 prims K circuits settings top tree D A parameter seeds pairs z Z
    p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) core⟩

section Check

attribute [local instance] inhabitedField

/-- The bound of each fixed indexed batch event outside the budget collision. -/
def TreeSimCheckIndexedBounds3 : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧
            TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
        ENNReal.ofReal (checkErrorOf (E := E)
          (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q)

theorem treeSimCheckIndexedBounds3_of_bounds
    (bounds : TreeSimCheckIndexedBounds prims K circuits settings) :
    TreeSimCheckIndexedBounds3 prims K circuits settings :=
  fun hb top tree D A x z Z q hx hq hsmall j =>
    (probEvent_mono fun _ _ h => h.2).trans (bounds hb top tree D A x z Z q hx hq hsmall j)

/-- The check flag of `treeSimEvents3` is covered by the indexed events outside the budget
collision. -/
theorem treeSimCheck_indexed_union3 (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun r => ¬ TreeSimHashBad3 D r.2 ∧
      TreeSimWrongOutput prims K circuits settings top tree D A x z r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
    ∑ j : Fin (treeBatches settings tree),
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧
          TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
        treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] := by
  rw [← treeSimCheck_audited_logged_erase prims K circuits settings top tree D A x z Z, probEvent_map]
  refine le_trans (probEvent_mono ?_) (probEvent_exists_finset_le_sum Finset.univ _ _)
  intro r hr h
  obtain ⟨j, hj⟩ := treeSimCheck_indexed_cover prims K circuits settings hbatch top tree D A x z Z r hr
    ⟨fun hbad => h.1 (Or.inl (Or.inl hbad)), h.2⟩
  exact ⟨j, Finset.mem_univ j, fun hc => h.1 (Or.inr hc), hj⟩

/-- The check goal of `treeSimEvents3` from the guarded indexed bounds. -/
theorem treeSimCheckBoundGoal3_of_indexedBounds3
    (indexedBounds : TreeSimCheckIndexedBounds3 prims K circuits settings) :
    TreeSimCheckBoundGoal3 prims K circuits settings := by
  letI : SampleableType E := SampleableType.ofFintype E
  intro hbatch top tree D A x z Z q hx hq hsmall
  let ε := checkErrorOf (E := E)
    (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
    (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q
  have sumBound : (∑ j : Fin (treeBatches settings tree),
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧
          TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
        treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)]) ≤
      (treeBatches settings tree : ℝ≥0∞) * ENNReal.ofReal ε := by
    calc
      _ ≤ ∑ _j : Fin (treeBatches settings tree), ENNReal.ofReal ε :=
        Finset.sum_le_sum (fun j _ => indexedBounds hbatch top tree D A x z Z q hx hq hsmall j)
      _ = _ := by simp
  have bound := (treeSimCheck_indexed_union3 prims K circuits settings hbatch top tree D A x z Z).trans
    sumBound
  have realBound := ENNReal.toReal_mono (by finiteness) bound
  simp only [treeSimTrace, probEvent_map, Function.comp_def, treeSimEvents3, decide_eq_true_eq]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (checkErrorOf_nonneg K _ _ _), ε, treeCheckError] using realBound

/-- The two setup branches of `TreeSimCheckSetupBranches` outside the budget collision. An honest
pair that passes the PRSS echo with different `.sharedKeys` lists is a budget collision, so these
branches may assume that the honest holders of each term agree on its key. The branch `uncounted`
stays. An opening that matches a corrupt commitment with no earlier query of its point is a guess
of one fresh answer, not a collision. -/
def TreeSimCheckSetupBranches3 : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree), ∃ uncounted : TreeSimLog C → Prop,
        Pr[fun r => (¬ TreeSimHashBudgetCollision r.2 ∧
            TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2) ∧
            uncounted r.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
          ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256) ∧
        Pr[fun r => (¬ TreeSimHashBudgetCollision r.2 ∧
            TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2) ∧
            ¬ uncounted r.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
          ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E)
            (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
            (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q - 1))

theorem treeSimCheckSetupBranches3_of_branches
    (branches : TreeSimCheckSetupBranches prims K circuits settings) :
    TreeSimCheckSetupBranches3 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall j
  obtain ⟨uncounted, h2, h3⟩ := branches hb top tree D A x z Z q hx hq hsmall j
  exact ⟨uncounted, (probEvent_mono fun _ _ h => ⟨h.1.2, h.2⟩).trans h2,
    (probEvent_mono fun _ _ h => ⟨h.1.2, h.2⟩).trans h3⟩

theorem treeSimCheckIndexedBounds3_of_setupBranches3
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimCheckIndexedBounds3 prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j
  obtain ⟨uncounted, h2, h3⟩ := branches hbatch top tree D A x z Z q hx hq hsmall j
  exact treeSimCheck_setup_accounting K _ _ (fun r => uncounted r.2) _ _ q h2 h3

/-- The check goal of `treeSimEvents3` from the guarded setup branches. -/
theorem treeSimCheckBoundGoal3_of_setupBranches3
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimCheckBoundGoal3 prims K circuits settings :=
  treeSimCheckBoundGoal3_of_indexedBounds3 prims K circuits settings
    (treeSimCheckIndexedBounds3_of_setupBranches3 prims K circuits settings branches)

end Check

/-- The hop from the guarded salt reuse estimate and the guarded setup branches. -/
theorem treeSimulationHop_of_guarded3
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHopClosed3 prims K circuits settings stages
    (treeSimHashBoundGoal3_of_guarded prims K circuits settings honest salt reuse)
    (treeSimCheckBoundGoal3_of_setupBranches3 prims K circuits settings branches)

/-- The hop from the pair bounds of a two-stage salt table, as `treeSimulationHop_of_pairs`. -/
theorem treeSimulationHop_of_pairs3
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairBounds : TreeSaltStagesPairs splits)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_guarded3 prims K circuits settings stages honest salt
    (treeSimSaltReuseGuarded_of_pairs splits pairBounds) branches

/-- The hop from the setup addresses and the eager model, as `treeSimulationHop_of_setup`. -/
theorem treeSimulationHop_of_setup3
    (stages : TreeSimStagesGoal3 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (addresses : TreeSaltSetupAddresses prims K circuits settings)
    (eager : TreeSaltSetupEager prims K circuits settings)
    (branches : TreeSimCheckSetupBranches3 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_guarded3 prims K circuits settings stages honest salt
    (treeSimSaltReuseGuarded_of_setup prims K circuits settings addresses eager) branches

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop)

/-- `TreeTwinDigestDrawnGoal` with the guard `¬ TreeSimBad3`. -/
def TreeTwinDigestDrawnGoal3 : Prop :=
  ∀ n (a : TreeSimConfig A (TreeSimState C)),
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
    ∀ l, u.2.2 = a.2.2 ++ l → TreeTwinDigestDrawn D a.2.2 l

/-- The field `freeHit` of `TreeStagesTwinRelation` with `TreeSimBad3`. -/
def TreeTwinFreeHit3 : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
    (∃ l, u.2.2 = a.2.2 ++ l ∧ TreeStagesFreeHit swaps l) →
    TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2

/-- The field `freeHit` with `TreeSimBad3` from the program fact, as `treeTwin_freeHit`. -/
theorem treeTwin_freeHit3
    (drawn : TreeTwinDigestDrawnGoal3 prims K circuits settings top tree D A parameter seeds pairs z p r) :
    TreeTwinFreeHit3 prims K circuits settings top tree D A parameter seeds pairs z p r Req := by
  intro n δ swaps a b reach good salts _ u hu hit
  obtain ⟨l, hl, x, hx, hist, answer, mem⟩ := hit
  obtain ⟨T', key', label', draws, fresh⟩ := drawn n a reach good u hu l hl x.1 hist answer mem
  obtain ⟨hlen, T, key, label, hidden, old⟩ := salts x hx
  refine Or.inl (Or.inl (Or.inr ⟨x.1, T, key, label, T', key', label', hlen, hidden,
    fresh T key label hidden old, fun g => ⟨?_, ?_⟩⟩))
  · rw [hl]
    exact List.mem_append_left _ (old g)
  · rw [hl]
    exact List.mem_append_right _ (draws g)

end Fields

/-- `TreeTwinDigestGoal` with the guard `¬ TreeSimBad3`. -/
def TreeTwinDigestGoal3 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    TreeTwinDigestDrawnGoal3 prims K circuits settings top tree D A parameter seeds pairs z p r

/-- The first lockstep link on the guard of `treeSimEvents3`. The guard `¬ TreeSimBad3` excludes
the budget collision, so the link needs no extra hypothesis. -/
theorem treeTwinDigestGoal3_of_lockstep
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings) :
    TreeTwinDigestGoal3 prims K circuits settings := by
  intro hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach good u hu l hl
  exact treeTwinDigestDrawn_of_lockstep circuits prims K settings hbatch lockstep draws top tree D A
    parameter seeds pairs z p hp padding r hr n a reach
    (not_budgetCollision_of_not_bad3 prims K circuits settings top tree D A _ z _ good) u hu l hl

/-- The third lockstep link on an audited run with no budget collision. Two honest operators have
the same jobs and start label at each batch that both record. -/
theorem treeLockstepRecords_common_of_agree (hbatch : 0 < settings.batchSize)
    (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) (hx : DealtInputs D x)
    (run : (Bool × (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) ×
      TreeSimLog C)
    (hrun : run ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (good : ¬ TreeSimHashBudgetCollision run.2)
    (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) (vi vj : TreeOutput)
    (ri rj : List (TreeSimCheckBatchRecord C))
    (houti : run.1.2.2 i = some (vi, ri)) (houtj : run.1.2.2 j = some (vj, rj))
    (k : ℕ) (hki : k < ri.length) (hkj : k < rj.length) :
    ri[k].jobs = rj[k].jobs ∧ ri[k].start = rj[k].start := by
  obtain ⟨parameter, enc, hrec⟩ := agree hbatch top tree D A x z Z hx run hrun good
  exact treeLockstepRecords_common circuits settings parameter tree enc enc ri rj
    (hrec i hi vi ri houti) (hrec j hj vj rj houtj) k hki hkj (Or.inl rfl)

/-- info: 'ThresholdLeanXmssSecurity.treeSimEvents3_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimEvents3_bad

/-- info: 'ThresholdLeanXmssSecurity.treeSimBad3_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimBad3_mono

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHopClosed3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHopClosed3

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBoundGoal3_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundGoal3_of_guarded

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_goal2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_goal2

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBoundGoal3_of_goal2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckBoundGoal3_of_goal2

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_cores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_cores

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBoundGoal3_of_setupBranches3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckBoundGoal3_of_setupBranches3

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckSetupBranches3_of_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckSetupBranches3_of_branches

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_guarded3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_guarded3

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_pairs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairs3

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_setup3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_setup3

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_freeHit3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_freeHit3

/-- info: 'ThresholdLeanXmssSecurity.treeTwinDigestGoal3_of_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinDigestGoal3_of_lockstep

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecords_common_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecords_common_of_agree

end ThresholdLeanXmssSecurity
