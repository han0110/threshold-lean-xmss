import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedSchedule

/-!
# The saved check loop's round kinds

The advancing Coin uses its saved caller and actual schedule to construct
the next field exchange. Successful honest Coin outputs and the saved batch
position give one sampled challenge. An honest abort or exhausted sampler
routes to a stopped exchange. The finishing transition remains an explicit
input when joining the two cases of the same saved witness.
-/

set_option linter.unusedSectionVars false
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinSavedKinds
open TreeTwinSavedSchedule
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- An actual field boundary with an inherited honest abort. -/
def StoppedExtendStage {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (p : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E) (live : C.Party → Bool),
    let d := p.data K D rnd δ
    (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧
    a.1.2 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- A stopped field exchange closes without a continuation or coverage premise. -/
theorem treeTwinKindNext_stoppedExtend (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (StoppedExtendStage K D) := by
  intro n δ swaps a b _ _ _ _ _ req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨step, rnd, live, stopped, left, right⟩ := stage
  rw [left, right, ← state]
  apply relTriple_post_mono (treeStages_extendMult_partial_round prims K D A (step.data K D rnd δ)
    live stopped a.1.1 _ b.2 related)
  intro u w h
  obtain ⟨same, hu, hw, caches, _, _⟩ := h
  obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1
    (fun i _ => Or.inl ⟨congrFun hu i, congrFun hw i⟩)
  exact Or.inr ⟨[], δ, fun x hx => by simp at hx, caches, same, done, flags, Or.inl ⟨hu, hw⟩⟩

/-- Port of `TreeTwinLaterKinds.TreeStagesChallengeReduction.coin_round`,
with coverage required only at honest parties. Corrupt Coin outputs are `none`. -/
theorem coin_round_honest (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesChallengeReduction K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i, i ∉ D.1 → ∀ values, values.length = 1 → TreeStagesChallengeCovered K base (p.tag i) (p.hashLabel i) values)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2)
    (base_le : base ≤ a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live 1 coinRnd p.st₁ (p.afterCoin₁ K D))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live 1 coinRnd p.st₂ (p.afterCoin₂ K D))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧ ∃ δ,
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (p.label + 2) δ ∧ TreeSimFutureEmpty (p.label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (p.label + 2) z.2.2 ∧
        ((u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none)) ∨
          ∃ rnd,
            let step := p.step K D (p.sampled K D base coinRnd u.1.2.2)
            let d := step.data K D rnd δ
            let live' := p.nextLive K D base coinRnd u.1.2.2
            u.1.2.1 = treeSimExtendMultPartial K D d.ctx₁ live' d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
            z.1.2.1 = treeSimExtendMultPartial K D d.ctx₂ live' d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
            base ≤ u.2.1.1)) := by
  by_cases active : ∀ i, i ∉ D.1 → live i = true
  · rw [treeStages_coin_partial_live K D live active, treeStages_coin_partial_live K D live active]
    simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    rw [treeSim_coin_round_factor, treeSim_coin_round_factor]
    simp only [treeStages_resumeAll_map, simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D old _ a b related))
    intro r₁ r₂ hr
    rw [hr.1.1]
    have fresh' : TreeSimFutureEmpty (p.label + 1) r₁.2.1.2 := by
      rw [hr.1.2.2.1]
      exact fresh
    have le' : base ≤ r₁.2.1.1 := base_le.trans (treeSim_logged_grows prims D _ a r₁ hr.2.1)
    apply relTriple_bind (treeStages_challenge_extendMult_start prims K D p.T₀ p.pivotParty p.pivot old visible
      p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys p.count p.products₁ p.products₂ p.len₁ p.len₂ p.tag p.hashLabel
      (treeSimCoinOutput K D 1 coinRnd r₂.1.2) (by intro i hi; simp [treeSimCoinOutput, hi])
      (p.label + 1) future (fun i => nextLabel (p.st₁ i)) (fun i => nextLabel (p.st₂ i))
      (by intro i hi; change (p.st₁ i).label + 1 = p.label + 1; rw [p.lab₁ i hi])
      (by intro i hi; change (p.st₂ i).label + 1 = p.label + 1; rw [p.lab₂ i hi])
      (p.afterField₁ K D) (p.afterField₂ K D) base (by
        intro i values ho
        have hi : i ∉ D.1 := by
          intro hc
          simp [treeSimCoinOutput, hc] at ho
        exact covered i hi values (treeStages_coinOutput_length K D 1 coinRnd r₂.1.2 i values ho))
      r₁.2 r₂.2 hr.1.2.1 fresh' le')
    intro u z hu
    obtain ⟨rnd, δ, left, right, caches, vis, zero, fresh₁, fresh₂, le⟩ := hu
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, δ, caches, vis, zero, fresh₁, fresh₂,
      Or.inr ⟨rnd, left, right, le⟩⟩
  · push Not at active
    apply relTriple_post_mono (treeTwin_coin_stopped_round prims K D A old live active 1 coinRnd
      p.st₁ p.st₂ (p.afterCoin₁ K D) (p.afterCoin₂ K D) state a b related)
    intro u z h
    obtain ⟨stateEq, sentEq, left, right, caches, frame₁, frame₂⟩ := h
    refine ⟨stateEq, sentEq, old, caches, visible, future, ?_, ?_, Or.inl ⟨left, right⟩⟩
    · rw [frame₁]
      exact fun x hx => fresh x (by omega)
    · rw [frame₂]
      exact fun x hx => treeSim_futureEmpty_related fresh related.2 x (by omega)


/-- Live recipients at one address use the same sampled challenge, without
any consistency premise on their party-local Coin randomness. -/
theorem sampled_agree (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (base : HashCache C) (coinRnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E)
    (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (address : (p.tag i, p.hashLabel i) = (p.tag j, p.hashLabel j))
    (live_i : p.nextLive K D base coinRnd sent i = true)
    (live_j : p.nextLive K D base coinRnd sent j = true) :
    p.sampled K D base coinRnd sent i = p.sampled K D base coinRnd sent j := by
  cases hoi : treeSimCoinOutput K D 1 coinRnd sent i with
  | none => simp [TreeStagesChallengeReduction.nextLive, treeStagesChallengeLive, hoi] at live_i
  | some a =>
    cases hoj : treeSimCoinOutput K D 1 coinRnd sent j with
    | none => simp [TreeStagesChallengeReduction.nextLive, treeStagesChallengeLive, hoj] at live_j
    | some b =>
      have same := coinOutput_agree K D 1 coinRnd sent hi hj hoi hoj
      obtain ⟨tag, label⟩ := Prod.mk.inj address
      simp only [TreeStagesChallengeReduction.sampled, hoi, hoj, same, tag, label]

section Kinds
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (openings : List (List (List Bit)))
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))

/-- An advancing saved Coin enters the next saved field exchange or an
inherited-abort field exchange, with coverage only at honest addresses. -/
theorem treeTwinKindNext_savedAdvancing
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1))
    (field : TreeTwinExtendChallengeStage K D (SavedRel K circuits settings top tree D parameter openings) ∈ kinds)
    (stopped : StoppedExtendStage K D ∈ kinds) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedAdvancing K circuits settings top tree D parameter openings)) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨step, rnd, sent, coinRnd, ⟨w, saved, adv⟩, visible, future, fresh₁, fresh₂, left, right⟩ := stage
  let coin := step.coinNext K D rnd δ sent
  by_cases live : ∀ i, i ∉ D.1 → coin.live i = true
  · obtain ⟨recipe, close⟩ := saved.closure adv
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
        obtain ⟨w', saved', _, _⟩ := close rnd δ sent live
          (red.sampled K D base coinRnd u.1.2.2) (red.sampled K D base coinRnd u.1.2.2 step.pivotParty) common
        refine Or.inr ⟨[], δ', fun x hx => by simp at hx, caches, same, done, flags,
          Or.inr (Or.inr ⟨_, field, red.step K D (red.sampled K D base coinRnd u.1.2.2), nextRnd,
            red.nextLive K D base coinRnd u.1.2.2, ⟨w', saved'⟩, vis, ?_, ?_, hu, hv⟩)⟩
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
theorem savedChallengeNext
    (advancing : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedAdvancing K circuits settings top tree D parameter openings)))
    (finishing : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedFinishing K circuits settings top tree D parameter openings))) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (SavedRel K circuits settings top tree D parameter openings)) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨step, rnd, sent, coinRnd, saved, rest⟩ := stage
  rcases savedRel_cases saved with ha | hf
  · exact advancing n δ swaps a b reach bound good active salts req ⟨step, rnd, sent, coinRnd, ha, rest⟩
  · exact finishing n δ swaps a b reach bound good active salts req ⟨step, rnd, sent, coinRnd, hf, rest⟩

end Kinds

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedKinds.treeTwinKindNext_stoppedExtend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_stoppedExtend

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedKinds.coin_round_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coin_round_honest

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedKinds.sampled_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sampled_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedKinds.treeTwinKindNext_savedAdvancing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_savedAdvancing

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedKinds.savedChallengeNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms savedChallengeNext

end ThresholdLeanXmssSecurity.TreeTwinSavedKinds
