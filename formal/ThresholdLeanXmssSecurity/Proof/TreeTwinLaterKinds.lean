import ThresholdLeanXmssSecurity.Proof.TreeTwinLater

/-!
# Later kinds of the linked twin execution

A challenge Coin executes its bounded hash sampler before the next field draw.
The successor retains the sampled challenge, actual products and saved check
continuation. Partial activation and sampler exhaustion use the same driver
round as the live case. The linked kind interface records cache coverage and
the saved-program recipe separately.

The pinned and current leanVM proof trees were searched for synchronous
challenge/field transitions. These threshold driver boundaries are specific
to this protocol.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- A sequence of digest swaps fixes every query fixed by its individual
permutations; no inclusion of the entire swapped cache is assumed. -/
theorem treeTwin_swapAll_read (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (q : Query C)
    (fixed : ∀ x ∈ swaps, digestSwap x.1 x.2.1 x.2.2 q = q) :
    treeStagesSwapAll swaps cache q = cache q := by
  induction swaps with
  | nil => rfl
  | cons x xs ih =>
    change relabelHashCache (digestSwap x.1 x.2.1 x.2.2) (treeStagesSwapAll xs cache) q = _
    have same := relabelHashCache_apply (digestSwap x.1 x.2.1 x.2.2) (treeStagesSwapAll xs cache) q
    rw [fixed x (by simp)] at same
    exact same.trans (ih fun y hy => fixed y (by simp [hy]))

theorem treeTwin_swapAll_coinKey (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (tag label : ℕ) (values : List Bit) :
    treeStagesSwapAll swaps cache (.coinKey tag label values) = cache (.coinKey tag label values) :=
  treeTwin_swapAll_read swaps cache _ fun x _ => digestSwap_coinKey x.1 values x.2.1 x.2.2 tag label

theorem treeTwin_swapAll_expand (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (key : HashOutput) (index : ℕ) :
    treeStagesSwapAll swaps cache (.expand key index) = cache (.expand key index) :=
  treeTwin_swapAll_read swaps cache _ fun _ _ => by simp [digestSwap, Equiv.swap_apply_def]

/-- The check's bounded expansion coverage is unchanged by all digest swaps. -/
theorem treeTwin_expansionCovered_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (tag label : ℕ) (values : List E) (count : ℕ) :
    TreeStagesExpansionCovered K (treeStagesSwapAll swaps cache) tag label values count ↔
      TreeStagesExpansionCovered K cache tag label values count := by
  simp only [TreeStagesExpansionCovered, treeTwin_swapAll_coinKey, treeTwin_swapAll_expand]

/-- The challenge sampler's entire bounded query set is unchanged. -/
theorem treeTwin_challengeCovered_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (tag label : ℕ) (values : List E) :
    TreeStagesChallengeCovered K (treeStagesSwapAll swaps cache) tag label values ↔
      TreeStagesChallengeCovered K cache tag label values := by
  simp only [TreeStagesChallengeCovered, treeTwin_swapAll_coinKey, treeTwin_swapAll_expand]

theorem treeTwin_cachedFindChallenge_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (key : HashOutput) (tries index : ℕ) :
    treeStagesCachedFindChallenge K (treeStagesSwapAll swaps cache) key tries index =
      treeStagesCachedFindChallenge K cache key tries index := by
  induction tries generalizing index with
  | zero => rfl
  | succ tries ih =>
    simp only [treeStagesCachedFindChallenge, treeTwin_swapAll_expand, ih]

/-- Cache swaps preserve rejection as well as successful challenge values. -/
theorem treeTwin_cachedChallenge_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (tag label : ℕ) (values : List E) :
    treeStagesCachedChallenge K (treeStagesSwapAll swaps cache) tag label values =
      treeStagesCachedChallenge K cache tag label values := by
  simp only [treeStagesCachedChallenge, treeTwin_swapAll_coinKey, treeTwin_cachedFindChallenge_swapAll]

/-- The challenge sampled from the shared, covered cache after the actual
rushing Coin reply. -/
def TreeStagesChallengeReduction.sampled (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (base : HashCache C) (coinRnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) : C.Party → E :=
  fun i => (treeStagesCachedChallenge K base (p.tag i) (p.hashLabel i)
    ((treeSimCoinOutput K D 1 coinRnd sent i).getD [])).getD 0

def TreeStagesChallengeReduction.nextLive (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (base : HashCache C) (coinRnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) : C.Party → Bool :=
  let out := treeSimCoinOutput K D 1 coinRnd sent
  treeStagesChallengeLive K base p.tag p.hashLabel (fun i => (out i).getD [])
    (fun i => (out i).map fun _ => ())

/-- One driver round from a challenge Coin to the next actual field boundary.
Unlike the two-round reduction law, this retains the intermediate pending
steps required by `TreeTwinKindNext`. -/
theorem TreeStagesChallengeReduction.coin_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesChallengeReduction K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 → TreeStagesChallengeCovered K base (p.tag i) (p.hashLabel i) values)
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
        exact covered i values (treeStages_coinOutput_length K D 1 coinRnd r₂.1.2 i values ho))
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

/-- A saved challenge Coin whose bounded rejection queries are covered by
the incoming cache. `Recipes` describes its actual remaining check code. -/
def TreeTwinReductionCoinStage {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (Recipes : TreeStagesChallengeReduction K D → Prop)
    (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (p : TreeStagesChallengeReduction K D) (live : C.Party → Bool)
    (rnd : C.Party → PrssOutput C E) (base : HashCache C),
    Recipes p ∧
    (∀ i values, values.length = 1 → TreeStagesChallengeCovered K base (p.tag i) (p.hashLabel i) values) ∧
    (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero (p.label + 2) δ ∧
    TreeSimFutureEmpty (p.label + 1) a.2.1.2 ∧ base ≤ a.2.1.1 ∧
    a.1.2 = treeSimCoinPartial K D live 1 rnd p.st₁ (p.afterCoin₁ K D) ∧
    b.1.2 = treeSimCoinPartial K D live 1 rnd p.st₂ (p.afterCoin₂ K D)

/-- A challenge kind advances to the field kind while retaining the recipe
for the sampled products and the entire saved continuation. -/
theorem treeTwinKindNext_reductionCoin (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (Recipes : TreeStagesChallengeReduction K D → Prop)
    (Fields : TreeStagesExtendMultChallenge K D → Prop)
    (recipes : ∀ step, Recipes step → ∀ values, Fields (step.step K D values))
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (field : TreeTwinExtendChallengeStage K D Fields ∈ kinds) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinReductionCoinStage K D Recipes) := by
  intro n δ swaps a b _ _ _ _ _ req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨step, live, rnd, base, recipe, covered, visible, future, fresh, le, left, right⟩ := stage
  rw [left, right, ← state]
  apply relTriple_post_mono (step.coin_round prims K D A δ visible future live rnd base covered
    a.1.1 _ b.2 related fresh le)
  intro u w h
  obtain ⟨same, _, δ', caches, vis, zero, fresh₁, _, ⟨hu, hw⟩ | ⟨nextRnd, hu, hw, _⟩⟩ := h
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1
      (fun i _ => Or.inl ⟨congrFun hu i, congrFun hw i⟩)
    exact Or.inr ⟨[], δ', fun x hx => by simp at hx, caches, same, done, flags, Or.inl ⟨hu, hw⟩⟩
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1 (fun i hi => by
      rw [hu, hw]
      exact treeTwin_sameKind_extendPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
    refine Or.inr ⟨[], δ', fun x hx => by simp at hx, caches, same, done, flags,
      Or.inr (Or.inr ⟨_, field, step.step K D (step.sampled K D base rnd u.1.2.2), nextRnd,
        step.nextLive K D base rnd u.1.2.2, recipes step recipe _, vis, ?_, ?_, hu, hw⟩)⟩
    · simpa only [TreeStagesChallengeReduction.step, Nat.add_assoc] using zero
    · change TreeSimFutureEmpty (step.label + 1 + 1) u.2.1.2
      simpa only [Nat.add_assoc] using fresh₁

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_expansionCovered_swapAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_expansionCovered_swapAll

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_challengeCovered_swapAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_challengeCovered_swapAll

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_cachedChallenge_swapAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_cachedChallenge_swapAll

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesChallengeReduction.coin_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeStagesChallengeReduction.coin_round

/-- info: 'ThresholdLeanXmssSecurity.treeTwinKindNext_reductionCoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_reductionCoin

end ThresholdLeanXmssSecurity
