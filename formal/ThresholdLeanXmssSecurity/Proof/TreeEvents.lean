import ThresholdLeanXmssSecurity.Proof.TreeCompose
import ThresholdLeanXmssSecurity.Proof.TreeSimHashFinish
import ThresholdLeanXmssSecurity.Proof.TreeSimCheckFinish

/-!
# The corrected bad events of the tree simulation hop

`TreeCompose.lean` shows that `treeSimEvents` misses one case. A hidden digest salt can equal
the salt of another honest digest draw. `treeSimEvents2` adds this case to the hash event.

* `treeSimulationHopClosed2` gives the hop from the three goals of `treeSimEvents2`.
* `treeSimCheckBoundGoal2_of_goal` moves the check goal to the new events. The check flag
  excludes the hash event, so a larger hash event gives a smaller check event.
* `treeSimStagesGoal2_of_cores` gives the new stages goal from cores for `TreeSimBad2`.
* `treeSimHash_flag2_le` bounds the new hash flag by the old hash flag and the salt reuse.
* `treeSimHashBoundGoal2_of_estimates` gives the new hash goal from the honest count, the salt
  estimate and the new salt reuse estimate `TreeSimSaltReuseEstimate`.

The old hash goal already uses the whole budget `(q + S')² / 2^256`. So the new hash goal
does not follow from the old goal and the reuse term. It follows from the parts of the old goal,
as in `treeSimHashBound_of_terminal`.

The reuse estimate counts `N = treeBatches * termCount` distinct salt addresses. The sum fits
because `q + 2 H + 2 N ≤ q + S'`, where `H = treeBatches * (t * termCount)`. With `N = S'` the
sum does not fit at `q = 0`. The count `N` is a paper argument. The honest holders of a term
agree on its key and its label in each batch, so each batch reads one address for each term.
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

/-- A hidden digest salt that equals the salt of an honest digest draw at another address.
Several holders read one address, so the two addresses must differ. -/
def TreeSimSaltReuse (D : C.Coalition) (log : TreeSimLog C) : Prop :=
  ∃ (salt : List Bit) (T : C.Term) (key : HashOutput) (label : ℕ)
    (T' : C.Term) (key' : HashOutput) (label' : ℕ),
    salt.length = 256 ∧ ¬ KnownTo D.1 T ∧ (T, key, label) ≠ (T', key', label') ∧ ∀ g : Fin 256,
      (⟨.inr (.inr (.inr (.term T, key, label, 2, g.val))), salt.getD g.val 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log ∧
      (⟨.inr (.inr (.inr (.term T', key', label', 2, g.val))), salt.getD g.val 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log

/-- The hash event of `treeSimEvents` with the salt reuse. -/
def TreeSimHashBad2 (D : C.Coalition) (log : TreeSimLog C) : Prop :=
  TreeSimHashBad D log ∨ TreeSimSaltReuse D log

/-- The events of `treeSimEvents` with the salt reuse in the hash event. -/
def treeSimEvents2 : TreeSimEvents C E := fun top tree D A x z _ log =>
  (decide (TreeSimHashBad2 D log),
    decide (¬ TreeSimHashBad2 D log ∧ TreeSimWrongOutput prims K circuits settings top tree D A x z log))

/-- The sticky predicate of `treeSimEvents2`. -/
def TreeSimBad2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) : Prop :=
  TreeSimHashBad2 D log ∨ TreeSimWrongOutput prims K circuits settings top tree D A x z log

theorem treeSimSaltReuse_mono (D : C.Coalition) {a b : TreeSimLog C}
    (hab : a <+: b) : TreeSimSaltReuse D a → TreeSimSaltReuse D b := by
  rintro ⟨salt, T, key, label, T', key', label', hlen, hT, hne, hbits⟩
  exact ⟨salt, T, key, label, T', key', label', hlen, hT, hne, fun g =>
    ⟨hab.sublist.subset (hbits g).1, hab.sublist.subset (hbits g).2⟩⟩

theorem treeSimHashBad2_mono (D : C.Coalition) {a b : TreeSimLog C}
    (hab : a <+: b) : TreeSimHashBad2 D a → TreeSimHashBad2 D b :=
  Or.imp (treeSimHashBad_mono D hab) (treeSimSaltReuse_mono D hab)

theorem treeSimBad2_mono (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSimBad2 prims K circuits settings top tree D A x z a →
      TreeSimBad2 prims K circuits settings top tree D A x z b := by
  rintro (h | h)
  · exact Or.inl (treeSimHashBad2_mono D hab h)
  · exact (treeSimBad_mono prims K circuits settings top tree D A x z hab (Or.inr h)).elim
      (fun h' => Or.inl (Or.inl h')) Or.inr

/-- The old sticky predicate implies the new one. -/
theorem treeSimBad2_of_bad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) :
    TreeSimBad prims K circuits settings top tree D A x z log →
      TreeSimBad2 prims K circuits settings top tree D A x z log :=
  Or.imp Or.inl id

/-- The two recorded flags of `treeSimEvents2` are exactly the sticky predicate. -/
theorem treeSimEvents2_bad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    ((treeSimEvents2 prims K circuits settings top tree D A x z Z log).1 = true ∨
      (treeSimEvents2 prims K circuits settings top tree D A x z Z log).2 = true) ↔
      TreeSimBad2 prims K circuits settings top tree D A x z log := by
  simp only [treeSimEvents2, decide_eq_true_eq, TreeSimBad2]
  tauto

/-- The stages goal for `treeSimEvents2`. -/
def TreeSimStagesGoal2 : Prop :=
  TreeSimStages prims K circuits settings (treeSimEvents2 prims K circuits settings)

/-- The hash goal for `treeSimEvents2`, with the budget of `TreeSimHashBoundGoal`. -/
def TreeSimHashBoundGoal2 : Prop :=
  TreeSimHashBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents2 prims K circuits settings))

/-- The check goal for `treeSimEvents2`, with the budget of `TreeSimCheckBoundGoal`. -/
def TreeSimCheckBoundGoal2 : Prop :=
  TreeSimCheckBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents2 prims K circuits settings))

/-- The round interface of `treeSimEvents2` from its core, as `treeSimRoundCore_stages`. -/
def treeSimRoundCore_stages2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (core : TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z dealt state s
      (fun t => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2)) :
    TreeSimRoundStages prims K circuits settings (treeSimEvents2 prims K circuits settings)
      top tree D A parameter seeds pairs z Z dealt state s where
  Bad t := TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2
  Inv := core.Inv
  stage := core.stage
  Q := TreeSimFinalRel D A dealt.1
  entry := core.entry
  noSetup := core.noSetup
  badPersistent _ _ hp := treeSimBad2_mono prims K circuits settings top tree D A _ z hp
  done := core.done
  output a b hab hgood := by
    obtain ⟨replay, state, cache, corrupt, success⟩ := core.outputEvidence a b hab hgood
    exact treeSim_final_of_replay prims K circuits settings top tree D A parameter seeds pairs z dealt
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      replay (fun h => hgood (treeSimBad2_of_bad prims K circuits settings top tree D A _ z _ h))
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
  observeGood a b hab := OracleComp.ProgramLogic.Relational.relTriple_post_mono (treeSim_observe_good prims D A Z dealt.1 a b hab)
    (fun _ _ he => Or.inr (by rw [he]))
  badRecorded t ht := (treeSimEvents2_bad prims K circuits settings top tree D A _ z Z t.2).mpr ht

/-- The stages goal of `treeSimEvents2` from the cores, as `treeSimStagesGoal_of_cores`. -/
theorem treeSimStagesGoal2_of_cores
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
        (fun t => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2))) :
    TreeSimStagesGoal2 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  obtain ⟨padding, hpadding⟩ := cores hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨core⟩ := hpadding r hr
  exact ⟨treeSimRoundCore_stages2 prims K circuits settings top tree D A parameter seeds pairs z Z
    p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) core⟩

/-- Assembly of the three goals of `treeSimEvents2`. -/
theorem treeSimulationHopClosed2
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (hashBound : TreeSimHashBoundGoal2 prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal2 prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop prims K circuits settings (treeSimEvents2 prims K circuits settings)
    stages hashBound checkBound

/-- The check flag of `treeSimEvents2` implies the check flag of `treeSimEvents`. -/
theorem treeSimCheckBoundGoal2_of_goal
    (check : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimCheckBoundGoal2 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  refine le_trans (ENNReal.toReal_mono probEvent_ne_top ?_)
    (check hb top tree D A x z Z q hx hq hsmall)
  simp only [treeSimTrace, probEvent_map]
  apply probEvent_mono
  intro r _ h
  simp only [Function.comp_apply, treeSimEvents2, treeSimEvents, TreeSimHashBad2,
    decide_eq_true_eq] at h ⊢
  tauto

/-- The new hash disjunct, as a birthday bound on the `treeBatches * termCount` distinct salt
addresses. Each batch draws one salt for each term. -/
def TreeSimSaltReuseEstimate : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    (Pr[fun r => TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ) / 2 ^ 257

/-- The recorded hash flag of `treeSimEvents2` is the new union on the actual log. -/
theorem treeSimHash_flag2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents2 prims K circuits settings)
        top tree D A x z Z] =
    Pr[fun r => TreeSimHashBad2 D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] := by
  simp only [treeSimTrace, treeSimEvents2, probEvent_map, Function.comp_def, decide_eq_true_eq]

/-- The new hash flag costs at most the old hash flag and the salt reuse. -/
theorem treeSimHash_flag2_le (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents2 prims K circuits settings)
        top tree D A x z Z] ≤
    Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents prims K circuits settings)
        top tree D A x z Z] +
    Pr[fun r => TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] := by
  rw [treeSimHash_flag2, treeSimHash_flag]
  exact probEvent_or_le _ _ _

/-- The salt reuse adds one term to the union of `treeSimHash_union_clean`. -/
theorem treeSimHash_union2 {α : Type} (D : C.Coalition) (p : ProbComp (α × TreeSimLog C)) :
    (Pr[fun r => TreeSimHashBad2 D r.2 | p]).toReal ≤
      (Pr[fun r => TreeSimHashCollision r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal +
      (Pr[fun r => TreeSimSaltReuse D r.2 | p]).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
    (probEvent_or_le (mx := p) (fun r => TreeSimHashBad D r.2) (fun r => TreeSimSaltReuse D r.2))
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at h
  exact h.trans (add_le_add (treeSimHash_union_clean D p) le_rfl)

/-- The three terms fit in the square budget when it keeps `2 H + 2 N` free points. -/
theorem treeSimHash_union2_arith (M q H N : ℝ) (hq : 0 ≤ q) (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hbudget : q + 2 * H + 2 * N ≤ M) :
    M ^ 2 / (2 * 2 ^ 256) + 2 * H * (q + H) / 2 ^ 256 + N ^ 2 / 2 ^ 257 ≤ M ^ 2 / 2 ^ 256 := by
  have hs : (q + 2 * H + 2 * N) ^ 2 ≤ M ^ 2 := by nlinarith
  have hc : 4 * H * (q + H) + N ^ 2 ≤ M ^ 2 := by nlinarith [sq_nonneg q]
  rw [show (2 : ℝ) ^ 257 = 2 * 2 ^ 256 from pow_succ' 2 256]
  calc
    _ = (M ^ 2 + (4 * H * (q + H) + N ^ 2)) / (2 * 2 ^ 256) := by ring
    _ ≤ (M ^ 2 + M ^ 2) / (2 * 2 ^ 256) :=
      div_le_div_of_nonneg_right (add_le_add le_rfl hc) (by positivity)
    _ = _ := by ring

/-- The remaining budget pays twice the honest salt uses and twice the distinct salts. -/
theorem treeSimHash_reuse_capacity (tree : Tree) :
    2 * (treeBatches settings tree * (C.t * termCount C)) + 2 * (treeBatches settings tree * termCount C) ≤
      treeSecrets circuits settings C tree - 2 * prssKeyCount C := by
  rw [treeSimHash_rest]
  have ht : 2 * C.t = C.n + 1 := by
    have := C.one_le_t
    unfold Committee.n
    omega
  have he : 2 * (C.t * termCount C) + 2 * termCount C = (C.n + 3) * termCount C := by
    nlinarith
  have hb := Nat.mul_le_mul_left (treeBatches settings tree)
    (show 2 * (C.t * termCount C) + 2 * termCount C ≤ 3 * termCount C + C.n * termCount C +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2 by
        rw [he]; nlinarith)
  nlinarith

/-- The new hash goal follows from the honest count, the salt estimate and the salt reuse
estimate. -/
theorem treeSimHashBoundGoal2_of_estimates
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseEstimate prims K circuits settings) :
    TreeSimHashBoundGoal2 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  by_cases hlarge : 2 ^ 128 ≤ N
  · apply le_trans _ (treeSimHash_unit_budget _ hlarge)
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (probEvent_le_one (mx := treeSimTrace prims K circuits settings
        (treeSimEvents2 prims K circuits settings) top tree D A x z Z) (p := fun r => r.2.1 = true))
  have hn : N < 2 ^ 128 := Nat.lt_of_not_ge hlarge
  have cert := treeSimHash_terminal_fresh prims K circuits settings top tree D A x z Z q hq hn
    (treeSimHash_terminal_of_honest prims K circuits settings honest hb top tree D A x z Z q hx hq hn)
  have h := treeSimHash_logged_birthday_region prims D TreeSimHashBudgetDomain treeSimHash_domain_budget
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) N cert
  rw [treeSim_localReal_eq K circuits settings top tree D A x z Z] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] at hreal
  have hc : (Pr[fun r => TreeSimHashCollision r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
        ((N ^ 2 : ℕ) : ℝ) / (2 * 2 ^ 256) := by
    refine hreal.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hN : N * (N - 1) ≤ N ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_left N (Nat.sub_le N 1)
    exact_mod_cast hN
  rw [treeSimHash_flag2]
  refine (treeSimHash_union2 D _).trans ((add_le_add (add_le_add hc
    (salt hb top tree D A x z Z q hx hq hsmall)) (reuse hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [N, Nat.cast_pow, Nat.cast_add]
  apply treeSimHash_union2_arith _ _ _ _ (by positivity) (by positivity) (by positivity)
  have hs : 2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) +
      2 * ((treeBatches settings tree * termCount C : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_reuse_capacity (C := C) circuits settings tree
  linarith

/-- The full hop from the old check goal and the three hash estimates. -/
theorem treeSimulationHop_of_events2
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseEstimate prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHopClosed2 prims K circuits settings stages
    (treeSimHashBoundGoal2_of_estimates prims K circuits settings honest salt reuse)
    (treeSimCheckBoundGoal2_of_goal prims K circuits settings checkBound)

/-- info: 'ThresholdLeanXmssSecurity.treeSimEvents2_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimEvents2_bad

/-- info: 'ThresholdLeanXmssSecurity.treeSimBad2_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimBad2_mono

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHopClosed2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHopClosed2

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBoundGoal2_of_goal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckBoundGoal2_of_goal

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBoundGoal2_of_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundGoal2_of_estimates

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_events2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_events2

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal2_of_cores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal2_of_cores

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_flag2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_flag2_le

end ThresholdLeanXmssSecurity
