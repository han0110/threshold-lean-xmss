import ThresholdLeanXmssSecurity.Proof.TreeTwinEntry
import ThresholdLeanXmssSecurity.Proof.TreeTwinLaterKinds

/-!
# Linked check transitions

The state returned by a field exchange determines the next challenge context.
Its saved slice and halving bodies determine the next concrete reduction.
Finite entry padding supplies the challenge cache at reached states, and
digest permutations preserve those entries. All transition obligations use
the same allowed code and the same list of round kinds.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- Recording field shares preserves the batch tag, including the default
state used for an aborted party. -/
theorem treeTwin_extendMult_recorded_tag {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    ((treeSimExtendMultOutputs K D ctx count rnd v st k sent i).getD
      (0, nextLabel (st i))).2.tag = (st i).tag := by
  unfold treeSimExtendMultOutputs treeSimExtendMultReturn
  split_ifs <;> rfl

/-- The reduction context uses the original optional field returns. -/
def TreeStagesExtendMultChallenge.reductionContext (D : C.Coalition)
    (p : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) :
    TreeStagesReductionContext K D :=
  let n := p.coinNext K D rnd δ sent
  { T₀ := p.T₀, pivotParty := p.pivotParty, pivot := p.pivot,
    label := p.label + 1,
    tag := fun i => (n.st₁ i).tag,
    hashLabel := fun i => (n.st₁ i).label,
    ctx₁ := p.ctx₁, ctx₂ := p.ctx₂,
    self₁ := p.self₁, self₂ := p.self₂, keys := p.keys,
    st₁ := n.st₁, st₂ := n.st₂,
    lab₁ := n.lab₁, lab₂ := n.lab₂ }

theorem TreeStagesExtendMultChallenge.coinNext_tag (D : C.Coalition)
    (p : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) (i : C.Party) :
    ((p.coinNext K D rnd δ sent).st₁ i).tag = (p.st₁ i).tag ∧
    ((p.coinNext K D rnd δ sent).st₂ i).tag = (p.st₂ i).tag := by
  constructor <;> apply treeTwin_extendMult_recorded_tag

/-- A deterministic saved body that enters another field exchange and
challenge. It contains no probabilistic transition premise. -/
structure TreeTwinReductionRecipe (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D) where
  count : ℕ
  products₁ : C.Party → Shares C E × RunState C → E → List (Product C E)
  products₂ : C.Party → Shares C E × RunState C → E → List (Product C E)
  len₁ : ∀ i out r, (products₁ i out r).length = count
  len₂ : ∀ i out r, (products₂ i out r).length = count
  body₁ : C.Party → Shares C E × RunState C → E →
    Shares C E × RunState C → E × RunState C → PartyM C E RealSpec TreeOutput
  body₂ : C.Party → Shares C E × RunState C → E →
    Shares C E × RunState C → E × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i out r, p.body₁ i out r =
    ((realCheckGadgets K (p.ctx₁ i)).extendMult (products₁ i out r.1)).run r.2 >>= fun v =>
      (challenge K (realCheckGadgets K (p.ctx₁ i))).run v.2 >>= body₁ i out r.1 v
  program₂ : ∀ i out r, p.body₂ i out r =
    ((realCheckGadgets K (p.ctx₂ i)).extendMult (products₂ i out r.1)).run r.2 >>= fun v =>
      (challenge K (realCheckGadgets K (p.ctx₂ i))).run v.2 >>= body₂ i out r.1 v

/-- Instantiate the next reduction with the actual field reply, retaining
the real and ideal recorded histories separately. -/
def TreeTwinReductionRecipe.reduction (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) : TreeStagesChallengeReduction K D :=
  let n := p.coinNext K D rnd δ sent
  { toTreeStagesReductionContext := p.reductionContext K D rnd δ sent,
    count := recipe.count,
    products₁ := fun i => recipe.products₁ i (n.x₁ i),
    products₂ := fun i => recipe.products₂ i (n.x₂ i),
    len₁ := fun i => recipe.len₁ i (n.x₁ i),
    len₂ := fun i => recipe.len₂ i (n.x₂ i),
    body₁ := fun i => recipe.body₁ i (n.x₁ i),
    body₂ := fun i => recipe.body₂ i (n.x₂ i) }

theorem TreeTwinReductionRecipe.afterCoin₁ (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) :
    (recipe.reduction K D rnd δ sent).afterCoin₁ K D = (p.coinNext K D rnd δ sent).next₁ := by
  funext i values
  change treeStagesChallengeTail K _ _ _ values = treeStagesChallengeTail K _ _ _ values
  congr 1
  funext r
  exact (recipe.program₁ i _ r).symm

theorem TreeTwinReductionRecipe.afterCoin₂ (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag)
    (i : C.Party) (hi : i ∉ D.1) :
    (recipe.reduction K D rnd δ sent).afterCoin₂ K D i = (p.coinNext K D rnd δ sent).next₂ i := by
  let n := p.coinNext K D rnd δ sent
  have tag : (n.st₁ i).tag = (n.st₂ i).tag :=
    (p.coinNext_tag K D rnd δ sent i).1.trans ((tags i hi).trans (p.coinNext_tag K D rnd δ sent i).2.symm)
  have label : (n.st₁ i).label = (n.st₂ i).label := (n.lab₁ i hi).trans (n.lab₂ i hi).symm
  funext values
  change treeStagesChallengeTail K (n.st₁ i).tag (n.st₁ i).label _ values =
    treeStagesChallengeTail K (n.st₂ i).tag (n.st₂ i).label _ values
  rw [tag, label]
  congr 1
  funext r
  exact (recipe.program₂ i _ r).symm

/-- Successive slices give a concrete recipe, including the unchanged
halving, final-check and caller suffix. -/
def TreeTwinReductionRecipe.slice (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (body₁ : p.body₁ = fun i => treeStagesSliceBody K (p.ctx₁ i) (τ₁ i) (count₁ i) j
      (next :: remaining) (v₁ i) (finish₁ i))
    (body₂ : p.body₂ = fun i => treeStagesSliceBody K (p.ctx₂ i) (τ₂ i) (count₂ i) j
      (next :: remaining) (v₂ i) (finish₂ i)) : TreeTwinReductionRecipe K D p where
  count := 2
  products₁ := fun i out r => treeStagesSliceProducts (τ₁ i) (count₁ i) next
    (treeStagesSliceUpdate K (p.ctx₁ i) (τ₁ i) (count₁ i) j (v₁ i) out.1 r)
  products₂ := fun i out r => treeStagesSliceProducts (τ₂ i) (count₂ i) next
    (treeStagesSliceUpdate K (p.ctx₂ i) (τ₂ i) (count₂ i) j (v₂ i) out.1 r)
  len₁ := by intros; rfl
  len₂ := by intros; rfl
  body₁ := fun i out r => treeStagesSliceBody K (p.ctx₁ i) (τ₁ i) (count₁ i) next remaining
    (treeStagesSliceUpdate K (p.ctx₁ i) (τ₁ i) (count₁ i) j (v₁ i) out.1 r) (finish₁ i)
  body₂ := fun i out r => treeStagesSliceBody K (p.ctx₂ i) (τ₂ i) (count₂ i) next remaining
    (treeStagesSliceUpdate K (p.ctx₂ i) (τ₂ i) (count₂ i) j (v₂ i) out.1 r) (finish₂ i)
  program₁ := by intro i out r; rw [body₁]; dsimp only; rw [treeStages_sliceBody_next]; rfl
  program₂ := by intro i out r; rw [body₂]; dsimp only; rw [treeStages_sliceBody_next]; rfl

/-- Successive halvings instantiate the same deterministic recipe. -/
def TreeTwinReductionRecipe.halving (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (width₁ width₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (body₁ : p.body₁ = fun i => treeStagesHalvingBody K (p.ctx₁ i) (width₁ i) j
      (next :: remaining) (v₁ i) (finish₁ i))
    (body₂ : p.body₂ = fun i => treeStagesHalvingBody K (p.ctx₂ i) (width₂ i) j
      (next :: remaining) (v₂ i) (finish₂ i)) : TreeTwinReductionRecipe K D p where
  count := 2
  products₁ := fun i out r => treeStagesHalvingProducts (width₁ i) next
    (treeStagesHalvingUpdate K (p.ctx₁ i) (width₁ i) j (v₁ i) out.1 r)
  products₂ := fun i out r => treeStagesHalvingProducts (width₂ i) next
    (treeStagesHalvingUpdate K (p.ctx₂ i) (width₂ i) j (v₂ i) out.1 r)
  len₁ := by intros; rfl
  len₂ := by intros; rfl
  body₁ := fun i out r => treeStagesHalvingBody K (p.ctx₁ i) (width₁ i) next remaining
    (treeStagesHalvingUpdate K (p.ctx₁ i) (width₁ i) j (v₁ i) out.1 r) (finish₁ i)
  body₂ := fun i out r => treeStagesHalvingBody K (p.ctx₂ i) (width₂ i) next remaining
    (treeStagesHalvingUpdate K (p.ctx₂ i) (width₂ i) j (v₂ i) out.1 r) (finish₂ i)
  program₁ := by intro i out r; rw [body₁]; dsimp only; rw [treeStages_halvingBody_next]; rfl
  program₂ := by intro i out r; rw [body₂]; dsimp only; rw [treeStages_halvingBody_next]; rfl

/-- The saved program of a challenge Coin is the program of its concrete
reduction. Corrupt parties' unused continuations need no equality. -/
theorem TreeTwinReductionRecipe.coin_steps (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinReductionRecipe K D p) (rnd coinRnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) :
    let n := p.coinNext K D rnd δ sent
    let q := recipe.reduction K D rnd δ sent
    treeSimCoinPartial K D n.live n.count coinRnd n.st₁ n.next₁ =
      treeSimCoinPartial K D n.live 1 coinRnd q.st₁ (q.afterCoin₁ K D) ∧
    treeSimCoinPartial K D n.live n.count coinRnd n.st₂ n.next₂ =
      treeSimCoinPartial K D n.live 1 coinRnd q.st₂ (q.afterCoin₂ K D) := by
  dsimp only
  constructor
  · rw [recipe.afterCoin₁ K D rnd δ sent]
    rfl
  · funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCoinPartial, treeSimCoinWaiting, hi]
    · simp only [treeSimCoinPartial, treeSimCoinWaiting, if_neg hi]
      rw [recipe.afterCoin₂ K D rnd δ sent tags i hi]
      rfl

/-- A syntactic recipe family and its actual successor family. -/
def TreeTwinRecipeClosure (D : C.Coalition)
    (Fields : TreeStagesExtendMultChallenge K D → Prop)
    (Reductions : TreeStagesChallengeReduction K D → Prop) : Prop :=
  ∀ p, Fields p →
    (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ recipe : TreeTwinReductionRecipe K D p,
      ∀ rnd δ sent, Reductions (recipe.reduction K D rnd δ sent)

/-- The linked challenge stage embeds into the covered reduction stage
without replacing any stored party program. -/
theorem treeTwin_challengeCoin_reduction {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (Fields : TreeStagesExtendMultChallenge K D → Prop)
    (Reductions : TreeStagesChallengeReduction K D → Prop)
    (recipes : TreeTwinRecipeClosure K D Fields Reductions)
    (base : HashCache C)
    (covered : ∀ p, Fields p → ∀ rnd δ sent i values, values.length = 1 →
      let q := p.reductionContext K D rnd δ sent
      TreeStagesChallengeCovered K base (q.tag i) (q.hashLabel i) values)
    (δ : HiddenAddress C → Bit) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) (le : base ≤ a.2.1.1)
    (stage : TreeTwinChallengeCoinStage K D Fields δ a b) :
    TreeTwinReductionCoinStage K D Reductions δ a b := by
  obtain ⟨p, rnd, sent, coinRnd, field, visible, future, fresh, _, left, right⟩ := stage
  obtain ⟨tags, recipe, reduced⟩ := recipes p field
  obtain ⟨same₁, same₂⟩ := recipe.coin_steps K D rnd coinRnd δ sent tags
  refine ⟨recipe.reduction K D rnd δ sent, (p.coinNext K D rnd δ sent).live, coinRnd,
    base, reduced rnd δ sent, covered p field rnd δ sent, visible, ?_, ?_, le,
    left.trans same₁, right.trans same₂⟩
  · exact fun x hx => future x (by change p.label + 1 + 2 ≤ _ at hx; omega)
  · simpa only [TreeTwinReductionRecipe.reduction, TreeStagesExtendMultChallenge.reductionContext,
      Nat.add_assoc] using fresh

/-- Entry padding covers every indicated challenge at the reached cache,
also after the twin's digest permutations. -/
theorem treeTwin_reached_challengeCovered (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (seeds : C.Term → HashOutput)
    (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ) (r : Unit × HashCache C)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run s.1.1))
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state
      ((r.2, s.1.2), s.2) n a)
    (swaps : List (List Bit × HashOutput × HashOutput))
    (tag label : ℕ) (mem : (tag, label) ∈ tagLabels)
    (values : List E) (length : values.length = 1) :
    TreeStagesChallengeCovered K (treeStagesTwin swaps a.2).1.1 tag label values := by
  apply (treeTwin_challengeCovered_swapAll K swaps a.2.1.1 tag label values).2
  exact (treeTwin_entryPadding_reached prims K circuits settings top tree D A x state s seeds
    tagLabels historyLimit r padding n a reach).challenge tag label mem values length

/-- Exact saved slice code, with its caller and private claim retained. -/
def TreeTwinSliceShape (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (remaining : List ℕ) : Prop :=
  ∃ (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j : ℕ)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput),
    p.body₁ = (fun i => treeStagesSliceBody K (p.ctx₁ i) (τ₁ i) (count₁ i) j remaining (v₁ i) (finish₁ i)) ∧
    p.body₂ = (fun i => treeStagesSliceBody K (p.ctx₂ i) (τ₂ i) (count₂ i) j remaining (v₂ i) (finish₂ i))

/-- Exact saved halving code, with its final check and caller retained. -/
def TreeTwinHalvingShape (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (remaining : List ℕ) : Prop :=
  ∃ (width₁ width₂ : C.Party → ℕ) (j : ℕ)
    (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput),
    p.body₁ = (fun i => treeStagesHalvingBody K (p.ctx₁ i) (width₁ i) j remaining (v₁ i) (finish₁ i)) ∧
    p.body₂ = (fun i => treeStagesHalvingBody K (p.ctx₂ i) (width₂ i) j remaining (v₂ i) (finish₂ i))

def TreeTwinCheckShape (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ remaining, TreeTwinSliceShape K D p remaining ∨ TreeTwinHalvingShape K D p remaining

def TreeTwinInternalCheck (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ next remaining, TreeTwinSliceShape K D p (next :: remaining) ∨
      TreeTwinHalvingShape K D p (next :: remaining)

/-- The challenge following the last slice or the last halving. -/
def TreeTwinCheckExit (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    (TreeTwinSliceShape K D p [] ∨ TreeTwinHalvingShape K D p [])

theorem treeTwin_checkShape_cases (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (shape : TreeTwinCheckShape K D p) :
    TreeTwinInternalCheck K D p ∨ TreeTwinCheckExit K D p := by
  obtain ⟨tags, remaining, body⟩ := shape
  cases remaining with
  | nil => exact Or.inr ⟨tags, body⟩
  | cons next remaining => exact Or.inl ⟨tags, next, remaining, body⟩

/-- Reduction bodies whose sampled successor is the actual slice or
halving form. This property speaks only about deterministic saved code. -/
def TreeTwinCheckReduction (D : C.Coalition) (q : TreeStagesChallengeReduction K D) : Prop :=
  ∀ values, TreeTwinCheckShape K D (q.step K D values)

theorem TreeTwinReductionRecipe.step_tags (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) (values : C.Party → E)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) (i : C.Party) (hi : i ∉ D.1) :
    (((recipe.reduction K D rnd δ sent).step K D values).st₁ i).tag =
      (((recipe.reduction K D rnd δ sent).step K D values).st₂ i).tag :=
  (p.coinNext_tag K D rnd δ sent i).1.trans ((tags i hi).trans (p.coinNext_tag K D rnd δ sent i).2.symm)

/-- Internal slices and halvings are closed under their actual saved
challenge-dependent reductions. -/
theorem treeTwin_internal_recipeClosure (D : C.Coalition) :
    TreeTwinRecipeClosure K D (TreeTwinInternalCheck K D) (TreeTwinCheckReduction K D) := by
  rintro p ⟨tags, next, remaining, slice | halving⟩
  · obtain ⟨τ₁, τ₂, count₁, count₂, j, v₁, v₂, finish₁, finish₂, body₁, body₂⟩ := slice
    let recipe := TreeTwinReductionRecipe.slice K D p τ₁ τ₂ count₁ count₂ j next remaining
      v₁ v₂ finish₁ finish₂ body₁ body₂
    refine ⟨tags, recipe, ?_⟩
    intro rnd δ sent values
    refine ⟨recipe.step_tags K D rnd δ sent values tags, remaining, Or.inl ?_⟩
    let n := p.coinNext K D rnd δ sent
    exact ⟨τ₁, τ₂, count₁, count₂, next,
      (fun i => treeStagesSliceUpdate K (p.ctx₁ i) (τ₁ i) (count₁ i) j (v₁ i) (n.x₁ i).1 (values i)),
      (fun i => treeStagesSliceUpdate K (p.ctx₂ i) (τ₂ i) (count₂ i) j (v₂ i) (n.x₂ i).1 (values i)),
      finish₁, finish₂, rfl, rfl⟩
  · obtain ⟨width₁, width₂, j, v₁, v₂, finish₁, finish₂, body₁, body₂⟩ := halving
    let recipe := TreeTwinReductionRecipe.halving K D p width₁ width₂ j next remaining
      v₁ v₂ finish₁ finish₂ body₁ body₂
    refine ⟨tags, recipe, ?_⟩
    intro rnd δ sent values
    refine ⟨recipe.step_tags K D rnd δ sent values tags, remaining, Or.inr ?_⟩
    let n := p.coinNext K D rnd δ sent
    exact ⟨width₁, width₂, next,
      (fun i => treeStagesHalvingUpdate K (p.ctx₁ i) (width₁ i) j (v₁ i) (n.x₁ i).1 (values i)),
      (fun i => treeStagesHalvingUpdate K (p.ctx₂ i) (width₂ i) j (v₂ i) (n.x₂ i).1 (values i)),
      finish₁, finish₂, rfl, rfl⟩

theorem TreeStagesExtendMultChallenge.reductionContext_address (D : C.Coalition)
    (p : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) (i : C.Party) :
    let q := p.reductionContext K D rnd δ sent
    (q.tag i, q.hashLabel i) = ((p.st₁ i).tag, (p.st₁ i).label + 1) := by
  dsimp only [TreeStagesExtendMultChallenge.reductionContext]
  exact Prod.ext (p.coinNext_tag K D rnd δ sent i).1
    (treeStages_extendMult_recorded_label K D _ _ _ _ _ _ sent i)

/-- The address of each saved challenge lies in the finite entry padding. -/
def TreeTwinCheckTagged (D : C.Coalition) (Saved : TreeStagesExtendMultChallenge K D → Prop)
    (tagLabels : List (ℕ × ℕ)) (p : TreeStagesExtendMultChallenge K D) : Prop :=
  Saved p ∧ ∀ i, ((p.st₁ i).tag, (p.st₁ i).label + 1) ∈ tagLabels

/-- The first field exchange has the slice body used by the fixed kinds. -/
theorem TreeTwinCheckCoinData.firstSlice_shape (D : C.Coalition)
    (p : TreeTwinCheckCoinData K D) (base : HashCache C)
    (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) :
    TreeTwinCheckShape K D (p.firstSlice K D base rnd sent) := by
  refine ⟨tags, (List.range sliceBits).drop 1, Or.inl ?_⟩
  refine ⟨p.expansion K D base rnd sent, p.expansion K D base rnd sent,
    (fun i => ((p.tuples₁ i).map (·.count)).sum),
    (fun i => ((p.tuples₂ i).map (·.count)).sum), 0,
    (fun i => treeStagesCheckInitial K (p.ctx₁ i) (p.tuples₁ i) (p.expansion K D base rnd sent i)),
    (fun i => treeStagesCheckInitial K (p.ctx₂ i) (p.tuples₂ i) (p.expansion K D base rnd sent i)),
    p.finish₁, p.finish₂, ?_, ?_⟩
  · rfl
  · rfl

section FixedKinds

variable (circuits : Circuits) (settings : Settings)
  (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
  (Saved : TreeStagesExtendMultChallenge K D → Prop)
  (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop))

/-- Reached linked challenge states admit saved programs with addresses
inside the chosen padding. All witnesses refer to this one stage relation. -/
def TreeTwinReachedChallengeTags (tagLabels : List (ℕ × ℕ)) : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    treeTwinReq D (treeTwinDataStage K D Allowed kinds) n δ (a.1, treeStagesTwin swaps a.2) b →
    TreeTwinChallengeCoinStage K D Saved δ (a.1, treeStagesTwin swaps a.2) b →
    TreeTwinChallengeCoinStage K D (TreeTwinCheckTagged K D Saved tagLabels) δ (a.1, treeStagesTwin swaps a.2) b

/-- Internal challenge Coins advance through the actual bounded sampler
and field draw. Only the last-slice and last-halving Coins use `exitNext`. -/
theorem treeTwinKindNext_checkCoin (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run p.2.2.1.1))
    (tagged : TreeTwinReachedChallengeTags prims K circuits settings top tree D A parameter seeds pairs z
      p r Allowed Saved kinds tagLabels)
    (shape : ∀ q, Saved q → TreeTwinCheckShape K D q)
    (recipes : TreeTwinRecipeClosure K D (fun q => Saved q ∧ TreeTwinInternalCheck K D q)
      (fun q => ∀ values, Saved (q.step K D values)))
    (field : TreeTwinExtendChallengeStage K D Saved ∈ kinds)
    (exitNext : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D (fun q => Saved q ∧ TreeTwinCheckExit K D q))) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinChallengeCoinStage K D Saved) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨step, rnd, sent, coinRnd, ⟨saved, addresses⟩, visible, future, fresh₁, fresh₂, left, right⟩ :=
    tagged n δ swaps a b reach bound good active salts req stage
  rcases treeTwin_checkShape_cases K D step (shape step saved) with internal | final
  · let Fields := fun q => (Saved q ∧ TreeTwinInternalCheck K D q) ∧
      ∀ i, ((q.st₁ i).tag, (q.st₁ i).label + 1) ∈ tagLabels
    have closed : TreeTwinRecipeClosure K D Fields (fun q => ∀ values, Saved (q.step K D values)) :=
      fun q hq => recipes q hq.1
    have covered : ∀ q, Fields q → ∀ draw shift reply i values, values.length = 1 →
        let ctx := q.reductionContext K D draw shift reply
        TreeStagesChallengeCovered K (treeStagesTwin swaps a.2).1.1 (ctx.tag i) (ctx.hashLabel i) values := by
      intro q hq draw shift reply i values length
      apply treeTwin_reached_challengeCovered prims K circuits settings top tree D A
        (dealtKeys parameter seeds pairs) p.2.1 p.2.2 seeds tagLabels historyLimit r padding n a reach swaps
        _ _ _ values length
      rw [q.reductionContext_address K D draw shift reply i]
      exact hq.2 i
    have reduced := treeTwin_challengeCoin_reduction K D Fields (fun q => ∀ values, Saved (q.step K D values))
      closed (treeStagesTwin swaps a.2).1.1 covered δ (a.1, treeStagesTwin swaps a.2) b le_rfl
      ⟨step, rnd, sent, coinRnd, ⟨⟨saved, internal⟩, addresses⟩, visible, future, fresh₁, fresh₂, left, right⟩
    exact treeTwinKindNext_reductionCoin prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed (fun q => ∀ values, Saved (q.step K D values)) Saved (fun _ h => h) kinds field
      n δ swaps a b reach bound good active salts req reduced
  · exact exitNext n δ swaps a b reach bound good active salts req
      ⟨step, rnd, sent, coinRnd, ⟨saved, final⟩, visible, future, fresh₁, fresh₂, left, right⟩

end FixedKinds

/-- One fixed list for the collector, Rerand, field, challenge and caller
boundaries. The same `Saved` predicate is used on both sides of the check loop. -/
abbrev treeTwinCheckKinds {A : Adversary C E (Keys C) PEmpty PEmpty} (D : C.Coalition)
    (Allowed : TreeTwinCode C E → Prop) (Saved : TreeStagesExtendMultChallenge K D → Prop)
    (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)) :=
  treeTwinLinkedKinds K D Allowed
    (TreeTwinExtendChallengeStage K D Saved :: TreeTwinChallengeCoinStage K D Saved :: others)

/-- Boundary obligations for one allowed-code predicate and one fixed list.
Internal field and challenge transitions are supplied by the check loop. -/
structure TreeTwinLinkedBoundary (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (Saved : TreeStagesExtendMultChallenge K D → Prop)
    (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (tagLabels : List (ℕ × ℕ)) : Prop where
  outputs : TreeTwinAllowedOutputs Allowed
  shape : ∀ q, Saved q → TreeTwinCheckShape K D q
  recipes : TreeTwinRecipeClosure K D (fun q => Saved q ∧ TreeTwinInternalCheck K D q)
    (fun q => ∀ values, Saved (q.step K D values))
  entry : TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
    (treeTwinReq D (treeTwinDataStage K D (fun _ => False) (treeTwinCheckKinds K D Allowed Saved others)))
  rerand : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r
    (fun _ => False) (treeTwinCheckKinds K D Allowed Saved others) (TreeTwinRerandCoinStage K D Allowed)
  tagged : TreeTwinReachedChallengeTags prims K circuits settings top tree D A parameter seeds pairs z p r
    (fun _ => False) Saved (treeTwinCheckKinds K D Allowed Saved others) tagLabels
  exitNext : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r
    (fun _ => False) (treeTwinCheckKinds K D Allowed Saved others)
    (TreeTwinChallengeCoinStage K D (fun q => Saved q ∧ TreeTwinCheckExit K D q))
  next : ∀ Kind ∈ others, TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r
    (fun _ => False) (treeTwinCheckKinds K D Allowed Saved others) Kind

/-- All later transitions follow from the boundary obligations for the
same fixed allowed code, saved programs and list of kinds. -/
theorem TreeTwinLinkedBoundary.next_all (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (Saved : TreeStagesExtendMultChallenge K D → Prop)
    (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run p.2.2.1.1))
    (boundary : TreeTwinLinkedBoundary prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed Saved others tagLabels) :
    ∀ Kind ∈ TreeTwinRerandCoinStage K D Allowed :: TreeTwinExtendChallengeStage K D Saved ::
      TreeTwinChallengeCoinStage K D Saved :: others,
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r
      (fun _ => False) (treeTwinCheckKinds K D Allowed Saved others) Kind := by
  intro Kind mem
  rcases List.mem_cons.1 mem with rfl | mem
  · exact boundary.rerand
  rcases List.mem_cons.1 mem with rfl | mem
  · exact treeTwinKindNext_extendChallenge prims K circuits settings top tree D A parameter seeds pairs z p r
      (fun _ => False) Saved _ (by simp [treeTwinCheckKinds, treeTwinLinkedKinds])
  rcases List.mem_cons.1 mem with rfl | mem
  · exact treeTwinKindNext_checkCoin prims K circuits settings top tree D A parameter seeds pairs z p r
      (fun _ => False) Saved _ tagLabels historyLimit padding boundary.tagged boundary.shape boundary.recipes
      (by simp [treeTwinCheckKinds, treeTwinLinkedKinds]) boundary.exitNext
  · exact boundary.next Kind mem

/-- Simultaneous boundary construction for the original linked target.
The allowed code and complete kind list are chosen once, before the padded
cache is sampled, and shared by entry and every transition obligation. -/
def TreeTwinLinkedBoundaries (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ) (Allowed : TreeTwinCode C E → Prop)
      (Saved : TreeStagesExtendMultChallenge K D → Prop)
      (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
        TreeSimConfig A (HashCache C × HiddenCache C) → Prop)),
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run p.2.2.1.1),
    TreeTwinLinkedBoundary prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed Saved others tagLabels

/-- The simultaneous boundary construction implies the exact original
linked goal, with no separate entry or later-kind existential witness. -/
theorem treeTwinLinkedGoal_of_boundaries (circuits : Circuits) (settings : Settings)
    (boundaries : TreeTwinLinkedBoundaries prims K circuits settings) :
    TreeTwinLinkedGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq small p hp good
  obtain ⟨tagLabels, historyLimit, Allowed, Saved, others, boundary⟩ :=
    boundaries hb top tree D A parameter seeds pairs z Z q hq small p hp good
  refine ⟨treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit, ?_⟩
  intro r hr
  have h := boundary r hr
  exact ⟨Allowed, TreeTwinExtendChallengeStage K D Saved :: TreeTwinChallengeCoinStage K D Saved :: others,
    h.outputs, h.entry, h.next_all prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed Saved others tagLabels historyLimit hr⟩

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinReductionRecipe.coin_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinReductionRecipe.coin_steps

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_challengeCoin_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_challengeCoin_reduction

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_reached_challengeCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_reached_challengeCovered

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_internal_recipeClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_internal_recipeClosure

/-- info: 'ThresholdLeanXmssSecurity.treeTwinKindNext_checkCoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_checkCoin

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinkedBoundary.next_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinLinkedBoundary.next_all

/-- info: 'ThresholdLeanXmssSecurity.treeTwinLinkedGoal_of_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinLinkedGoal_of_boundaries

end ThresholdLeanXmssSecurity
