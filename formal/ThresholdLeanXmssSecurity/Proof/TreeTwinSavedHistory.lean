import ThresholdLeanXmssSecurity.Proof.TreeTwinHistoryRecords
import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedKinds

/-! # Saved check histories
Cross-run history lengths and the remaining field-record budget accompany the
same saved caller through the advancing challenge transition.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinSavedHistory
open TreeTwinSavedSchedule TreeTwinSavedKinds TreeTwinHistoryRecords
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (parameter : PublicParameter) (openings : List (List (List Bit)))

def HistAt (q : TreeStagesExtendMultChallenge K D)
    (w : SavedWitness K circuits settings top tree D parameter openings) : Prop :=
  HistoryLenRel D q.st₁ q.st₂ ∧
    FieldBudget circuits settings D (tupleCount w.caller.rest.circs) w.phase.index q.st₁

def SavedRelH (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, SavedRelAt K circuits settings top tree D parameter openings q w ∧
    HistAt K circuits settings top tree D parameter openings q w

def SavedAdvancingH (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, SavedRelAt K circuits settings top tree D parameter openings q w ∧
    HistAt K circuits settings top tree D parameter openings q w ∧
    ¬ w.phase.Finishing (tupleCount w.caller.rest.circs)

def SavedFinishingH (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ w, SavedRelAt K circuits settings top tree D parameter openings q w ∧
    HistAt K circuits settings top tree D parameter openings q w ∧
    w.phase.Finishing (tupleCount w.caller.rest.circs)

variable {K circuits settings top tree D parameter openings}
    {q : TreeStagesExtendMultChallenge K D}
    {w : SavedWitness K circuits settings top tree D parameter openings}

theorem savedRelH_cases (h : SavedRelH K circuits settings top tree D parameter openings q) :
    SavedAdvancingH K circuits settings top tree D parameter openings q ∨
      SavedFinishingH K circuits settings top tree D parameter openings q := by
  obtain ⟨w, saved, hist⟩ := h
  by_cases hf : w.phase.Finishing (tupleCount w.caller.rest.circs)
  · exact Or.inr ⟨w, saved, hist, hf⟩
  · exact Or.inl ⟨w, saved, hist, hf⟩

theorem index_lt_halvings (h : SavedRelAt K circuits settings top tree D parameter openings q w) :
    w.phase.index < halvings (tupleCount w.caller.rest.circs) := by
  have hb := h.bound
  cases he : w.phase <;> simp only [he, SavedPhase.Bound] at hb <;>
    simp only [SavedPhase.index, halvings, halvSteps] at * <;> omega

theorem HistAt.coinNext (hist : HistAt K circuits settings top tree D parameter openings q w)
    (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) :
    let n := q.coinNext K D rnd δ sent
    HistoryLenRel D n.st₁ n.st₂ ∧
      FieldBudget circuits settings D (tupleCount w.caller.rest.circs) (w.phase.index + 1) n.st₁ := by
  dsimp only
  constructor
  · exact historyLenRel_fieldExit K D (q.data K D rnd δ) _ _ hist.1
      (SavedRelAt.coinNext_exit rnd δ sent live)
  · intro i hi T
    have growth := (fieldExit_length_le K D (q.data K D rnd δ) i _ _
      (SavedRelAt.coinNext_exit rnd δ sent live i hi) T).1
    change (((q.coinNext K D rnd δ sent).st₁ i).history T).length ≤
      ((q.st₁ i).history T).length + q.count * elementBits at growth
    have count := h.count_eq_two
    have budget := hist.2 i hi T
    have index := index_lt_halvings h
    unfold elementBits at *
    omega

/-- The existing closure recipe keeps both history conditions on its exact successor. -/
theorem _root_.ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.SavedRelAt.closureH (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (hist : HistAt K circuits settings top tree D parameter openings q w)
    (adv : ¬ w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    ∃ recipe : TreeTwinHonestReductionRecipe K D q, ∀ rnd δ sent,
      (∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) →
      ∀ (values : C.Party → E) (r : E), (∀ i, i ∉ D.1 → values i = r) →
      ∃ w', SavedRelAt K circuits settings top tree D parameter openings
        ((recipe.reduction K D rnd δ sent).step K D values) w' ∧
        HistAt K circuits settings top tree D parameter openings
          ((recipe.reduction K D rnd δ sent).step K D values) w' ∧
        w'.caller = w.caller ∧ w'.phase.index = w.phase.index + 1 := by
  obtain ⟨recipe, close⟩ := h.closure adv
  refine ⟨recipe, ?_⟩
  intro rnd δ sent live values r common
  obtain ⟨w', saved, caller, index⟩ := close rnd δ sent live values r common
  have next := hist.coinNext h rnd δ sent live
  refine ⟨w', saved, ⟨?_, ?_⟩, caller, index⟩
  · exact next.1
  · unfold FieldBudget at *
    rw [caller, index]
    exact next.2

theorem fieldBudget_finishing (h : SavedRelAt K circuits settings top tree D parameter openings q w)
    (hist : HistAt K circuits settings top tree D parameter openings q w)
    (finish : w.phase.Finishing (tupleCount w.caller.rest.circs)) :
    ∀ i, i ∉ D.1 → ∀ T, ((q.st₁ i).history T).length + 4 * elementBits ≤
      TreeTwinLinked2.historyLimit circuits settings := by
  obtain ⟨j, v₁, v₂, phase, last⟩ := h.finishing_halving finish
  intro i hi T
  have budget := hist.2 i hi T
  simp only [phase, SavedPhase.index, halvings, halvSteps] at budget last
  unfold elementBits at *
  omega

section Kinds
variable (prims : Primitives) (K : Constants C E)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (openings : List (List (List Bit)))
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))

/-- Port of `TreeTwinSavedKinds.treeTwinKindNext_savedAdvancing`.
An advancing saved Coin enters the next saved field exchange or an
inherited-abort field exchange, with coverage only at honest addresses. -/
theorem treeTwinKindNext_savedAdvancingH
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1))
    (field : TreeTwinExtendChallengeStage K D (SavedRelH K circuits settings top tree D parameter openings) ∈ kinds)
    (stopped : StoppedExtendStage K D ∈ kinds) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedAdvancingH K circuits settings top tree D parameter openings)) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨step, rnd, sent, coinRnd, ⟨w, saved, hist, adv⟩, visible, future, fresh₁, fresh₂, left, right⟩ := stage
  let coin := step.coinNext K D rnd δ sent
  by_cases live : ∀ i, i ∉ D.1 → coin.live i = true
  · obtain ⟨recipe, close⟩ := saved.closureH hist adv
    let red := recipe.reduction K D rnd δ sent
    let base := (treeStagesTwin swaps a.2).1.1
    have covered : ∀ i, i ∉ D.1 → ∀ values, values.length = 1 →
        TreeStagesChallengeCovered K base (red.tag i) (red.hashLabel i) values := by
      intro i hi values length
      exact treeTwin_reached_challengeCovered prims K circuits settings top tree D A
        (dealtKeys parameter seeds pairs) p.2.1 p.2.2 seeds
        (TreeTwinLinked2.tagLabels circuits settings tree parameter) (TreeTwinLinked2.historyLimit circuits settings)
        r padding n a reach swaps _ _ (saved.address rnd δ sent i hi).2 values length
    obtain ⟨coins₁, coins₂⟩ := recipe.coin_steps K D rnd coinRnd δ sent saved.tags
    obtain ⟨related, state, _, _, _⟩ := req
    rw [left, right, coins₁, coins₂, ← state]
    apply relTriple_post_mono (coin_round_honest prims K D A red δ visible
      (fun x hx => future x (by change step.label + 1 + 2 ≤ _ at hx; omega))
      coin.live coinRnd base covered a.1.1 _ b.2 related
      (by simpa only [red, TreeTwinHonestReductionRecipe.reduction,
        TreeStagesExtendMultChallenge.reductionContext, Nat.add_assoc] using fresh₁) le_rfl)
    intro u v h
    obtain ⟨same, _, δ', caches, vis, zero, newFresh₁, _, ⟨hu, hv⟩ | ⟨nextRnd, hu, hv, _⟩⟩ := h
    · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 v.1.2.1
        (fun i _ => Or.inl ⟨congrFun hu i, congrFun hv i⟩)
      exact Or.inr ⟨[], δ', fun x hx => by simp at hx, caches, same, done, flags, Or.inl ⟨hu, hv⟩⟩
    · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 v.1.2.1 (fun i hi => by
        rw [hu, hv]
        exact treeTwin_sameKind_extendPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
      by_cases nextLive : ∀ i, i ∉ D.1 → red.nextLive K D base coinRnd u.1.2.2 i = true
      · have common (i : C.Party) (hi : i ∉ D.1) :
            red.sampled K D base coinRnd u.1.2.2 i = red.sampled K D base coinRnd u.1.2.2 step.pivotParty := by
          apply sampled_agree K D red base coinRnd u.1.2.2 i step.pivotParty hi step.pivot.honest
          · exact (saved.address rnd δ sent i hi).1.trans
              (saved.address rnd δ sent step.pivotParty step.pivot.honest).1.symm
          · exact nextLive i hi
          · exact nextLive step.pivotParty step.pivot.honest
        obtain ⟨w', saved', hist', _, _⟩ := close rnd δ sent live
          (red.sampled K D base coinRnd u.1.2.2) (red.sampled K D base coinRnd u.1.2.2 step.pivotParty) common
        refine Or.inr ⟨[], δ', fun x hx => by simp at hx, caches, same, done, flags,
          Or.inr (Or.inr ⟨_, field, red.step K D (red.sampled K D base coinRnd u.1.2.2), nextRnd,
            red.nextLive K D base coinRnd u.1.2.2, ⟨w', saved', hist'⟩, vis, ?_, ?_, hu, hv⟩)⟩
        · simpa only [TreeStagesChallengeReduction.step, Nat.add_assoc] using zero
        · change TreeSimFutureEmpty (red.label + 1 + 1) u.2.1.2
          simpa only [Nat.add_assoc] using newFresh₁
      · push Not at nextLive
        exact Or.inr ⟨[], δ', fun x hx => by simp at hx, caches, same, done, flags,
          Or.inr (Or.inr ⟨_, stopped, red.step K D (red.sampled K D base coinRnd u.1.2.2), nextRnd,
            red.nextLive K D base coinRnd u.1.2.2, nextLive, hu, hv⟩)⟩
  · push Not at live
    exact treeTwinKindNext_stoppedCoin prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      n δ swaps a b reach bound good active salts req
      ⟨coin.live, coin.count, coinRnd, coin.st₁, coin.st₂, coin.next₁, coin.next₂, live, left, right⟩

/-- The two cases of one saved witness cover its Coin kind. The finishing
transition is an explicit input from the final-segment argument. -/
theorem savedChallengeNextH
    (advancing : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedAdvancingH K circuits settings top tree D parameter openings)))
    (finishing : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedFinishingH K circuits settings top tree D parameter openings))) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedRelH K circuits settings top tree D parameter openings)) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨step, rnd, sent, coinRnd, saved, rest⟩ := stage
  rcases savedRelH_cases saved with ha | hf
  · exact advancing n δ swaps a b reach bound good active salts req ⟨step, rnd, sent, coinRnd, ha, rest⟩
  · exact finishing n δ swaps a b reach bound good active salts req ⟨step, rnd, sent, coinRnd, hf, rest⟩

end Kinds

end ThresholdLeanXmssSecurity.TreeTwinSavedHistory

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedHistory.savedRelH_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedHistory.savedRelH_cases

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedHistory.index_lt_halvings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedHistory.index_lt_halvings

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedHistory.HistAt.coinNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedHistory.HistAt.coinNext

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.SavedRelAt.closureH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedSchedule.SavedRelAt.closureH

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedHistory.fieldBudget_finishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedHistory.fieldBudget_finishing

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedHistory.treeTwinKindNext_savedAdvancingH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedHistory.treeTwinKindNext_savedAdvancingH

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedHistory.savedChallengeNextH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinSavedHistory.savedChallengeNextH
