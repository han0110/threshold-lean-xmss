import ThresholdLeanXmssSecurity.Proof.TreeTwinLinked

/-!
# Saved check callers and the slice-to-halving boundary

Check recipes retain the exact Rerand caller, output shares and contexts.
Their program equalities concern honest parties: corrupt continuations do
not run in a partial Coin. The final slice converts its updated replicated
shares to Shamir shares before entering the actual halving schedule.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- A concrete next field exchange. Only honest continuations are executed
by the partial Coin; the other entries may keep their original defaults. -/
structure TreeTwinHonestReductionRecipe (D : C.Coalition)
    (p : TreeStagesExtendMultChallenge K D) where
  count : ℕ
  products₁ : C.Party → Shares C E × RunState C → E → List (Product C E)
  products₂ : C.Party → Shares C E × RunState C → E → List (Product C E)
  len₁ : ∀ i out r, (products₁ i out r).length = count
  len₂ : ∀ i out r, (products₂ i out r).length = count
  body₁ : C.Party → Shares C E × RunState C → E →
    Shares C E × RunState C → E × RunState C → PartyM C E RealSpec TreeOutput
  body₂ : C.Party → Shares C E × RunState C → E →
    Shares C E × RunState C → E × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → ∀ out r, p.body₁ i out r =
    ((realCheckGadgets K (p.ctx₁ i)).extendMult (products₁ i out r.1)).run r.2 >>= fun v =>
      (challenge K (realCheckGadgets K (p.ctx₁ i))).run v.2 >>= body₁ i out r.1 v
  program₂ : ∀ i, i ∉ D.1 → ∀ out r, p.body₂ i out r =
    ((realCheckGadgets K (p.ctx₂ i)).extendMult (products₂ i out r.1)).run r.2 >>= fun v =>
      (challenge K (realCheckGadgets K (p.ctx₂ i))).run v.2 >>= body₂ i out r.1 v

namespace TreeTwinHonestReductionRecipe

def reduction (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinHonestReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) : TreeStagesChallengeReduction K D :=
  let n := p.coinNext K D rnd δ sent
  { toTreeStagesReductionContext := p.reductionContext K D rnd δ sent
    count := recipe.count
    products₁ := fun i => recipe.products₁ i (n.x₁ i)
    products₂ := fun i => recipe.products₂ i (n.x₂ i)
    len₁ := fun i => recipe.len₁ i (n.x₁ i)
    len₂ := fun i => recipe.len₂ i (n.x₂ i)
    body₁ := fun i => recipe.body₁ i (n.x₁ i)
    body₂ := fun i => recipe.body₂ i (n.x₂ i) }

theorem afterCoin₁ (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinHonestReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) :
    (recipe.reduction K D rnd δ sent).afterCoin₁ K D i = (p.coinNext K D rnd δ sent).next₁ i := by
  funext values
  change treeStagesChallengeTail K _ _ _ values = treeStagesChallengeTail K _ _ _ values
  congr 1
  funext r
  exact (recipe.program₁ i hi _ r).symm

theorem afterCoin₂ (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinHonestReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) (i : C.Party) (hi : i ∉ D.1) :
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
  exact (recipe.program₂ i hi _ r).symm

theorem coin_steps (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinHonestReductionRecipe K D p) (rnd coinRnd : C.Party → PrssOutput C E)
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
  · apply treeTwin_coinPartial_congr
    exact fun i hi => (recipe.afterCoin₁ K D rnd δ sent i hi).symm
  · apply treeTwin_coinPartial_congr
    exact fun i hi => (recipe.afterCoin₂ K D rnd δ sent tags i hi).symm

theorem step_tags (D : C.Coalition) {p : TreeStagesExtendMultChallenge K D}
    (recipe : TreeTwinHonestReductionRecipe K D p) (rnd : C.Party → PrssOutput C E)
    (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) (values : C.Party → E)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) (i : C.Party) (hi : i ∉ D.1) :
    (((recipe.reduction K D rnd δ sent).step K D values).st₁ i).tag =
      (((recipe.reduction K D rnd δ sent).step K D values).st₂ i).tag :=
  (p.coinNext_tag K D rnd δ sent i).1.trans ((tags i hi).trans (p.coinNext_tag K D rnd δ sent i).2.symm)

def slice (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (body₁ : ∀ i, i ∉ D.1 → p.body₁ i = treeStagesSliceBody K (p.ctx₁ i) (τ₁ i) (count₁ i) j
      (next :: remaining) (v₁ i) (finish₁ i))
    (body₂ : ∀ i, i ∉ D.1 → p.body₂ i = treeStagesSliceBody K (p.ctx₂ i) (τ₂ i) (count₂ i) j
      (next :: remaining) (v₂ i) (finish₂ i)) : TreeTwinHonestReductionRecipe K D p where
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
  program₁ := by intro i hi out r; rw [body₁ i hi]; rw [treeStages_sliceBody_next]; rfl
  program₂ := by intro i hi out r; rw [body₂ i hi]; rw [treeStages_sliceBody_next]; rfl

def halving (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (width₁ width₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (body₁ : ∀ i, i ∉ D.1 → p.body₁ i = treeStagesHalvingBody K (p.ctx₁ i) (width₁ i) j
      (next :: remaining) (v₁ i) (finish₁ i))
    (body₂ : ∀ i, i ∉ D.1 → p.body₂ i = treeStagesHalvingBody K (p.ctx₂ i) (width₂ i) j
      (next :: remaining) (v₂ i) (finish₂ i)) : TreeTwinHonestReductionRecipe K D p where
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
  program₁ := by intro i hi out r; rw [body₁ i hi]; rw [treeStages_halvingBody_next]; rfl
  program₂ := by intro i hi out r; rw [body₂ i hi]; rw [treeStages_halvingBody_next]; rfl

end TreeTwinHonestReductionRecipe

/-- The replicated-to-Shamir conversion performed after the last slice. -/
def treeTwinSliceShamir (ctx : Context C) (τ : List E) (count j : ℕ)
    (v : Shares C E × Shares C E × E) (out : Shares C E) (r : E) :
    (ℕ → E) × (ℕ → E) × E :=
  let u := treeStagesSliceUpdate K ctx τ count j v out r
  (conv K ctx u.1, conv K ctx u.2.1, u.2.2)

theorem treeTwin_sliceBody_halving (ctx : Context C) (τ : List E) (count j next : ℕ)
    (remaining : List ℕ) (schedule : List.range (halvings count - sliceBits) = next :: remaining)
    (v : Shares C E × Shares C E × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E × RunState C) :
    treeStagesSliceBody K ctx τ count j [] v finish out r =
      ((realCheckGadgets K ctx).extendMult
        (treeStagesHalvingProducts (sliceWidth count) next (treeTwinSliceShamir K ctx τ count j v out.1 r.1))).run r.2 >>=
        treeStagesAfterHalving K ctx (sliceWidth count) next remaining
          (treeTwinSliceShamir K ctx τ count j v out.1 r.1) finish := by
  rw [treeStagesSliceBody, treeStages_checkFold_nil, schedule, treeStages_halvingFold_cons]
  rfl

/-- The schedule is required only for honest parties, whose saved programs
continue after the Coin. In particular no count is imposed on corrupt tuples. -/
def TreeTwinHonestReductionRecipe.sliceHalving (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (schedule₁ : ∀ i, i ∉ D.1 → List.range (halvings (count₁ i) - sliceBits) = next :: remaining)
    (schedule₂ : ∀ i, i ∉ D.1 → List.range (halvings (count₂ i) - sliceBits) = next :: remaining)
    (v₁ v₂ : C.Party → Shares C E × Shares C E × E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (body₁ : ∀ i, i ∉ D.1 → p.body₁ i = treeStagesSliceBody K (p.ctx₁ i) (τ₁ i) (count₁ i) j [] (v₁ i) (finish₁ i))
    (body₂ : ∀ i, i ∉ D.1 → p.body₂ i = treeStagesSliceBody K (p.ctx₂ i) (τ₂ i) (count₂ i) j [] (v₂ i) (finish₂ i)) :
    TreeTwinHonestReductionRecipe K D p where
  count := 2
  products₁ := fun i out r => treeStagesHalvingProducts (sliceWidth (count₁ i)) next
    (treeTwinSliceShamir K (p.ctx₁ i) (τ₁ i) (count₁ i) j (v₁ i) out.1 r)
  products₂ := fun i out r => treeStagesHalvingProducts (sliceWidth (count₂ i)) next
    (treeTwinSliceShamir K (p.ctx₂ i) (τ₂ i) (count₂ i) j (v₂ i) out.1 r)
  len₁ := by intros; rfl
  len₂ := by intros; rfl
  body₁ := fun i out r => treeStagesHalvingBody K (p.ctx₁ i) (sliceWidth (count₁ i)) next remaining
    (treeTwinSliceShamir K (p.ctx₁ i) (τ₁ i) (count₁ i) j (v₁ i) out.1 r) (finish₁ i)
  body₂ := fun i out r => treeStagesHalvingBody K (p.ctx₂ i) (sliceWidth (count₂ i)) next remaining
    (treeTwinSliceShamir K (p.ctx₂ i) (τ₂ i) (count₂ i) j (v₂ i) out.1 r) (finish₂ i)
  program₁ := by
    intro i hi out r
    rw [body₁ i hi]
    rw [treeTwin_sliceBody_halving K _ _ _ _ _ _ (schedule₁ i hi)]
    rfl
  program₂ := by
    intro i hi out r
    rw [body₂ i hi]
    rw [treeTwin_sliceBody_halving K _ _ _ _ _ _ (schedule₂ i hi)]
    rfl

/-- Closure of honest saved programs under their concrete reductions. -/
def TreeTwinHonestRecipeClosure (D : C.Coalition)
    (Fields : TreeStagesExtendMultChallenge K D → Prop)
    (Reductions : TreeStagesChallengeReduction K D → Prop) : Prop :=
  ∀ p, Fields p →
    (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ recipe : TreeTwinHonestReductionRecipe K D p,
      ∀ rnd δ sent, Reductions (recipe.reduction K D rnd δ sent)

/-- A tagged challenge uses only the finite collection of covered
addresses. Its corrupt continuations require no program equality. -/
theorem treeTwin_honestChallengeCoin_reduction {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (Fields : TreeStagesExtendMultChallenge K D → Prop)
    (Reductions : TreeStagesChallengeReduction K D → Prop)
    (recipes : TreeTwinHonestRecipeClosure K D Fields Reductions)
    (tagLabels : List (ℕ × ℕ)) (base : HashCache C)
    (covered : ∀ tag label, (tag, label) ∈ tagLabels → ∀ values, values.length = 1 →
      TreeStagesChallengeCovered K base tag label values)
    (δ : HiddenAddress C → Bit) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) (le : base ≤ a.2.1.1)
    (stage : TreeTwinChallengeCoinStage K D (TreeTwinCheckTagged K D Fields tagLabels) δ a b) :
    TreeTwinReductionCoinStage K D Reductions δ a b := by
  obtain ⟨p, rnd, sent, coinRnd, ⟨field, addresses⟩, visible, future, fresh, _, left, right⟩ := stage
  obtain ⟨tags, recipe, reduced⟩ := recipes p field
  obtain ⟨same₁, same₂⟩ := recipe.coin_steps K D rnd coinRnd δ sent tags
  refine ⟨recipe.reduction K D rnd δ sent, (p.coinNext K D rnd δ sent).live, coinRnd,
    base, reduced rnd δ sent, ?_, visible, ?_, ?_, le, left.trans same₁, right.trans same₂⟩
  · intro i values length
    apply covered _ _ ?_ values length
    change ((p.reductionContext K D rnd δ sent).tag i,
      (p.reductionContext K D rnd δ sent).hashLabel i) ∈ tagLabels
    rw [p.reductionContext_address K D rnd δ sent i]
    exact addresses i
  · exact fun x hx => future x (by change p.label + 1 + 2 ≤ _ at hx; omega)
  · simpa only [TreeTwinHonestReductionRecipe.reduction, TreeStagesExtendMultChallenge.reductionContext,
      Nat.add_assoc] using fresh

namespace TreeTwinBoundaries

variable (circuits : Circuits) (settings : Settings) (D : C.Coalition)
  (parameter : PublicParameter) (openings : List (List (List Bit)))

abbrev Allowed : TreeTwinCode C E → Prop :=
  TreeTwinEntryAllowed K circuits settings D parameter openings

/-- The caller is an original linked Rerand boundary. Its saved output
shares and batch continuations are retained, together with the batch code. -/
structure Caller where
  peer : TreeSimPeerData K D
  rest : TreeStagesRerandTail K D peer
  allowed : Allowed K circuits settings D parameter openings (treeTwinRerandCode K D rest)
  data : TreeTwinRunData K D peer.ctx₁ peer.ctx₂ rest.p₁ rest.p₂
  link : TreeTwinRerandLink K D rest
  sent : C.Party → Mail C E
  nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0
  nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0

namespace Caller

def checkData (c : Caller K circuits settings D parameter openings) : TreeTwinCheckCoinData K D :=
  c.rest.checkCoinData K D c.peer c.nonzero₁ c.nonzero₂ c.sent c.data

def count₁ (c : Caller K circuits settings D parameter openings) (i : C.Party) : ℕ :=
  (((c.checkData K circuits settings D parameter openings).tuples₁ i).map (·.count)).sum

def count₂ (c : Caller K circuits settings D parameter openings) (i : C.Party) : ℕ :=
  (((c.checkData K circuits settings D parameter openings).tuples₂ i).map (·.count)).sum

theorem counts (c : Caller K circuits settings D parameter openings) (i : C.Party) :
    c.count₁ K circuits settings D parameter openings i = c.count₂ K circuits settings D parameter openings i :=
  (c.checkData K circuits settings D parameter openings).counts i

/-- Saved slices use the tuple counts and final caller of this same
Rerand boundary. The private running claims remain unrestricted. -/
def Slice (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D) (remaining : List ℕ) : Prop :=
  ∃ (τ₁ τ₂ : C.Party → List E) (j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E),
    (∀ i, i ∉ D.1 → p.body₁ i = treeStagesSliceBody K (p.ctx₁ i) (τ₁ i)
      (c.count₁ K circuits settings D parameter openings i) j remaining (v₁ i)
      ((c.checkData K circuits settings D parameter openings).finish₁ i)) ∧
    (∀ i, i ∉ D.1 → p.body₂ i = treeStagesSliceBody K (p.ctx₂ i) (τ₂ i)
      (c.count₂ K circuits settings D parameter openings i) j remaining (v₂ i)
      ((c.checkData K circuits settings D parameter openings).finish₂ i))

def Halving (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D) (remaining : List ℕ) : Prop :=
  ∃ (j : ℕ) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E),
    (∀ i, i ∉ D.1 → p.body₁ i = treeStagesHalvingBody K (p.ctx₁ i)
      (sliceWidth (c.count₁ K circuits settings D parameter openings i)) j remaining (v₁ i)
      ((c.checkData K circuits settings D parameter openings).finish₁ i)) ∧
    (∀ i, i ∉ D.1 → p.body₂ i = treeStagesHalvingBody K (p.ctx₂ i)
      (sliceWidth (c.count₂ K circuits settings D parameter openings i)) j remaining (v₂ i)
      ((c.checkData K circuits settings D parameter openings).finish₂ i))

def Contexts (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D) : Prop :=
  p.ctx₁ = c.peer.ctx₁ ∧ p.ctx₂ = c.peer.ctx₂

end Caller

/-- One fixed family of saved check programs with actual Rerand callers. -/
def Saved (p : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ (c : Caller K circuits settings D parameter openings) (remaining : List ℕ),
      c.Contexts K circuits settings D parameter openings p ∧
      (c.Slice K circuits settings D parameter openings p remaining ∨
        c.Halving K circuits settings D parameter openings p remaining)

/-- The concrete first slice belongs to the saved family, including its
original caller and the actual optional Rerand output shares. -/
theorem Caller.firstSlice_saved (c : Caller K circuits settings D parameter openings)
    (base : HashCache C) (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) :
    Saved K circuits settings D parameter openings
      ((c.checkData K circuits settings D parameter openings).firstSlice K D base rnd sent) := by
  let p := c.checkData K circuits settings D parameter openings
  refine ⟨?_, c, (List.range sliceBits).drop 1, ⟨rfl, rfl⟩, Or.inl ?_⟩
  · exact fun i hi => treeTwin_peer_saved_tag K D c.peer c.sent i hi
  · exact ⟨p.expansion K D base rnd sent, p.expansion K D base rnd sent, 0,
      (fun i => treeStagesCheckInitial K (p.ctx₁ i) (p.tuples₁ i) (p.expansion K D base rnd sent i)),
      (fun i => treeStagesCheckInitial K (p.ctx₂ i) (p.tuples₂ i) (p.expansion K D base rnd sent i)),
      fun _ _ => rfl, fun _ _ => rfl⟩

/-- Every internal slice has a recipe that preserves this same caller. -/
theorem Caller.slice_recipe (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag)
    (contexts : c.Contexts K circuits settings D parameter openings p)
    (next : ℕ) (remaining : List ℕ)
    (shape : c.Slice K circuits settings D parameter openings p (next :: remaining)) :
    ∃ recipe : TreeTwinHonestReductionRecipe K D p, ∀ rnd δ sent values,
      Saved K circuits settings D parameter openings ((recipe.reduction K D rnd δ sent).step K D values) := by
  obtain ⟨τ₁, τ₂, j, v₁, v₂, body₁, body₂⟩ := shape
  let recipe := TreeTwinHonestReductionRecipe.slice K D p τ₁ τ₂
    (c.count₁ K circuits settings D parameter openings) (c.count₂ K circuits settings D parameter openings)
    j next remaining v₁ v₂ (c.checkData K circuits settings D parameter openings).finish₁
    (c.checkData K circuits settings D parameter openings).finish₂ body₁ body₂
  refine ⟨recipe, ?_⟩
  intro rnd δ sent values
  refine ⟨recipe.step_tags K D rnd δ sent values tags, c, remaining, contexts, Or.inl ?_⟩
  let n := p.coinNext K D rnd δ sent
  exact ⟨τ₁, τ₂, next,
    (fun i => treeStagesSliceUpdate K (p.ctx₁ i) (τ₁ i)
      (c.count₁ K circuits settings D parameter openings i) j (v₁ i) (n.x₁ i).1 (values i)),
    (fun i => treeStagesSliceUpdate K (p.ctx₂ i) (τ₂ i)
      (c.count₂ K circuits settings D parameter openings i) j (v₂ i) (n.x₂ i).1 (values i)),
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem Caller.halving_recipe (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag)
    (contexts : c.Contexts K circuits settings D parameter openings p)
    (next : ℕ) (remaining : List ℕ)
    (shape : c.Halving K circuits settings D parameter openings p (next :: remaining)) :
    ∃ recipe : TreeTwinHonestReductionRecipe K D p, ∀ rnd δ sent values,
      Saved K circuits settings D parameter openings ((recipe.reduction K D rnd δ sent).step K D values) := by
  obtain ⟨j, v₁, v₂, body₁, body₂⟩ := shape
  let recipe := TreeTwinHonestReductionRecipe.halving K D p
    (fun i => sliceWidth (c.count₁ K circuits settings D parameter openings i))
    (fun i => sliceWidth (c.count₂ K circuits settings D parameter openings i))
    j next remaining v₁ v₂ (c.checkData K circuits settings D parameter openings).finish₁
    (c.checkData K circuits settings D parameter openings).finish₂ body₁ body₂
  refine ⟨recipe, ?_⟩
  intro rnd δ sent values
  refine ⟨recipe.step_tags K D rnd δ sent values tags, c, remaining, contexts, Or.inr ?_⟩
  let n := p.coinNext K D rnd δ sent
  exact ⟨next,
    (fun i => treeStagesHalvingUpdate K (p.ctx₁ i)
      (sliceWidth (c.count₁ K circuits settings D parameter openings i)) j (v₁ i) (n.x₁ i).1 (values i)),
    (fun i => treeStagesHalvingUpdate K (p.ctx₂ i)
      (sliceWidth (c.count₂ K circuits settings D parameter openings i)) j (v₂ i) (n.x₂ i).1 (values i)),
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- The last slice enters the same caller's first halving whenever the
honest parties have the indicated nonempty schedule. -/
theorem Caller.sliceHalving_recipe (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag)
    (contexts : c.Contexts K circuits settings D parameter openings p)
    (next : ℕ) (remaining : List ℕ)
    (schedule : ∀ i, i ∉ D.1 →
      List.range (halvings (c.count₁ K circuits settings D parameter openings i) - sliceBits) = next :: remaining)
    (shape : c.Slice K circuits settings D parameter openings p []) :
    ∃ recipe : TreeTwinHonestReductionRecipe K D p, ∀ rnd δ sent values,
      Saved K circuits settings D parameter openings ((recipe.reduction K D rnd δ sent).step K D values) := by
  obtain ⟨τ₁, τ₂, j, v₁, v₂, body₁, body₂⟩ := shape
  have schedule₂ : ∀ i, i ∉ D.1 →
      List.range (halvings (c.count₂ K circuits settings D parameter openings i) - sliceBits) = next :: remaining := by
    intro i hi
    rw [← c.counts K circuits settings D parameter openings i]
    exact schedule i hi
  let recipe := TreeTwinHonestReductionRecipe.sliceHalving K D p τ₁ τ₂
    (c.count₁ K circuits settings D parameter openings) (c.count₂ K circuits settings D parameter openings)
    j next remaining schedule schedule₂ v₁ v₂ (c.checkData K circuits settings D parameter openings).finish₁
    (c.checkData K circuits settings D parameter openings).finish₂ body₁ body₂
  refine ⟨recipe, ?_⟩
  intro rnd δ sent values
  refine ⟨recipe.step_tags K D rnd δ sent values tags, c, remaining, contexts, Or.inr ?_⟩
  let n := p.coinNext K D rnd δ sent
  exact ⟨next,
    (fun i => treeTwinSliceShamir K (p.ctx₁ i) (τ₁ i)
      (c.count₁ K circuits settings D parameter openings i) j (v₁ i) (n.x₁ i).1 (values i)),
    (fun i => treeTwinSliceShamir K (p.ctx₂ i) (τ₂ i)
      (c.count₂ K circuits settings D parameter openings i) j (v₂ i) (n.x₂ i).1 (values i)),
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- A saved check with a next field exchange, including the conversion
after the last slice when its honest halving schedule is nonempty. -/
def Advancing (p : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ c : Caller K circuits settings D parameter openings,
      c.Contexts K circuits settings D parameter openings p ∧
      ((∃ next remaining,
          c.Slice K circuits settings D parameter openings p (next :: remaining) ∨
          c.Halving K circuits settings D parameter openings p (next :: remaining)) ∨
        (c.Slice K circuits settings D parameter openings p [] ∧ ∃ next remaining,
          ∀ i, i ∉ D.1 → List.range (halvings (c.count₁ K circuits settings D parameter openings i) - sliceBits) =
            next :: remaining))

theorem advancing_saved (p : TreeStagesExtendMultChallenge K D)
    (h : Advancing K circuits settings D parameter openings p) :
    Saved K circuits settings D parameter openings p := by
  obtain ⟨tags, c, contexts, internal | ⟨last, _⟩⟩ := h
  · obtain ⟨next, remaining, shape⟩ := internal
    exact ⟨tags, c, next :: remaining, contexts, shape⟩
  · exact ⟨tags, c, [], contexts, Or.inl last⟩

theorem advancing_recipe (p : TreeStagesExtendMultChallenge K D)
    (h : Advancing K circuits settings D parameter openings p) :
    (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ recipe : TreeTwinHonestReductionRecipe K D p, ∀ rnd δ sent values,
      Saved K circuits settings D parameter openings ((recipe.reduction K D rnd δ sent).step K D values) := by
  obtain ⟨tags, c, contexts, internal | ⟨last, next, remaining, schedule⟩⟩ := h
  · obtain ⟨next, remaining, slice | halving⟩ := internal
    · exact ⟨tags, c.slice_recipe K circuits settings D parameter openings p tags contexts next remaining slice⟩
    · exact ⟨tags, c.halving_recipe K circuits settings D parameter openings p tags contexts next remaining halving⟩
  · exact ⟨tags, c.sliceHalving_recipe K circuits settings D parameter openings p tags contexts next remaining schedule last⟩

theorem advancing_recipeClosure :
    TreeTwinHonestRecipeClosure K D (Advancing K circuits settings D parameter openings)
      (fun q => ∀ values, Saved K circuits settings D parameter openings (q.step K D values)) :=
  advancing_recipe K circuits settings D parameter openings

/-- The only continuation after these check bodies is the final masked
check followed by the saved output caller. -/
def Finishing (p : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag) ∧
    ∃ c : Caller K circuits settings D parameter openings,
      c.Contexts K circuits settings D parameter openings p ∧
      (c.Halving K circuits settings D parameter openings p [] ∨
        (c.Slice K circuits settings D parameter openings p [] ∧
          ∀ i, i ∉ D.1 → halvings (c.count₁ K circuits settings D parameter openings i) ≤ sliceBits))

/-- A common honest halving schedule separates the actual next field
exchange from the final masked check for this one saved caller. -/
theorem Caller.check_cases (c : Caller K circuits settings D parameter openings)
    (p : TreeStagesExtendMultChallenge K D)
    (tags : ∀ i, i ∉ D.1 → (p.st₁ i).tag = (p.st₂ i).tag)
    (contexts : c.Contexts K circuits settings D parameter openings p)
    (remaining : List ℕ)
    (shape : c.Slice K circuits settings D parameter openings p remaining ∨
      c.Halving K circuits settings D parameter openings p remaining)
    (rounds : ℕ) (schedule : ∀ i, i ∉ D.1 →
      halvings (c.count₁ K circuits settings D parameter openings i) - sliceBits = rounds) :
    Advancing K circuits settings D parameter openings p ∨ Finishing K circuits settings D parameter openings p := by
  cases remaining with
  | cons next remaining => exact Or.inl ⟨tags, c, contexts, Or.inl ⟨next, remaining, shape⟩⟩
  | nil =>
    rcases shape with slice | halving
    · cases h : List.range rounds with
      | nil =>
        have zero : rounds = 0 := by simpa using congrArg List.length h
        refine Or.inr ⟨tags, c, contexts, Or.inr ⟨slice, ?_⟩⟩
        intro i hi
        have bound := schedule i hi
        omega
      | cons next remaining =>
        refine Or.inl ⟨tags, c, contexts, Or.inr ⟨slice, next, remaining, ?_⟩⟩
        intro i hi
        rw [schedule i hi, h]
    · exact Or.inr ⟨tags, c, contexts, Or.inl halving⟩

theorem finishing_programs (p : TreeStagesExtendMultChallenge K D)
    (h : Finishing K circuits settings D parameter openings p) :
    ∃ (c : Caller K circuits settings D parameter openings)
      (claim₁ claim₂ : C.Party → Shares C E × RunState C → E → (ℕ → E) × (ℕ → E) × E),
      c.Contexts K circuits settings D parameter openings p ∧
      (∀ i, i ∉ D.1 → ∀ out r, p.body₁ i out r =
        (finalStep K (p.ctx₁ i) (realCheckGadgets K (p.ctx₁ i)) (claim₁ i out r.1)).run r.2 >>=
          (c.checkData K circuits settings D parameter openings).finish₁ i) ∧
      (∀ i, i ∉ D.1 → ∀ out r, p.body₂ i out r =
        (finalStep K (p.ctx₂ i) (realCheckGadgets K (p.ctx₂ i)) (claim₂ i out r.1)).run r.2 >>=
          (c.checkData K circuits settings D parameter openings).finish₂ i) := by
  obtain ⟨_, c, contexts, halving | ⟨slice, schedule⟩⟩ := h
  · obtain ⟨j, v₁, v₂, body₁, body₂⟩ := halving
    refine ⟨c,
      (fun i out r => treeStagesHalvingUpdate K (p.ctx₁ i)
        (sliceWidth (c.count₁ K circuits settings D parameter openings i)) j (v₁ i) out.1 r),
      (fun i out r => treeStagesHalvingUpdate K (p.ctx₂ i)
        (sliceWidth (c.count₂ K circuits settings D parameter openings i)) j (v₂ i) out.1 r), contexts, ?_, ?_⟩
    · intro i hi out r
      rw [body₁ i hi]
      simp only [treeStagesHalvingBody, treeStagesHalvingFold, List.foldlM_nil, pure_bind]
    · intro i hi out r
      rw [body₂ i hi]
      simp only [treeStagesHalvingBody, treeStagesHalvingFold, List.foldlM_nil, pure_bind]
  · obtain ⟨τ₁, τ₂, j, v₁, v₂, body₁, body₂⟩ := slice
    refine ⟨c,
      (fun i out r => treeTwinSliceShamir K (p.ctx₁ i) (τ₁ i)
        (c.count₁ K circuits settings D parameter openings i) j (v₁ i) out.1 r),
      (fun i out r => treeTwinSliceShamir K (p.ctx₂ i) (τ₂ i)
        (c.count₂ K circuits settings D parameter openings i) j (v₂ i) out.1 r), contexts, ?_, ?_⟩
    · intro i hi out r
      rw [body₁ i hi, treeStagesSliceBody, treeStages_checkFold_nil, Nat.sub_eq_zero_of_le (schedule i hi)]
      simp only [List.range_zero, treeStagesHalvingFold, List.foldlM_nil, pure_bind, treeTwinSliceShamir]
      rfl
    · intro i hi out r
      have bound : halvings (c.count₂ K circuits settings D parameter openings i) ≤ sliceBits := by
        rw [← c.counts K circuits settings D parameter openings i]
        exact schedule i hi
      rw [body₂ i hi, treeStagesSliceBody, treeStages_checkFold_nil, Nat.sub_eq_zero_of_le bound]
      simp only [List.range_zero, treeStagesHalvingFold, List.foldlM_nil, pure_bind, treeTwinSliceShamir]
      rfl

/-- The partial Coin vectors of a tagged advancing check are the vectors
of its covered reduction. Coverage is restricted to the finite address list. -/
theorem challengeCoin_reduction {A : Adversary C E (Keys C) PEmpty PEmpty}
    (tagLabels : List (ℕ × ℕ)) (base : HashCache C)
    (covered : ∀ tag label, (tag, label) ∈ tagLabels → ∀ values, values.length = 1 →
      TreeStagesChallengeCovered K base tag label values)
    (δ : HiddenAddress C → Bit) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) (le : base ≤ a.2.1.1)
    (stage : TreeTwinChallengeCoinStage K D
      (TreeTwinCheckTagged K D (Advancing K circuits settings D parameter openings) tagLabels) δ a b) :
    TreeTwinReductionCoinStage K D
      (fun q => ∀ values, Saved K circuits settings D parameter openings (q.step K D values)) δ a b := by
  exact treeTwin_honestChallengeCoin_reduction K D _ _
    (advancing_recipeClosure K circuits settings D parameter openings) tagLabels base covered δ a b le stage

/-- Reached check Coins use the entry padding for their tagged addresses.
Classification and the final-check transition refer to the same saved family. -/
theorem checkCoin_next (top : TopTree) (tree : Tree)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Other : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (tagLabels : List (ℕ × ℕ)) (historyLimit : ℕ)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (treeTwinEntryPadding K circuits settings seeds tagLabels historyLimit)).run p.2.2.1.1))
    (classified : ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 →
      (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
      treeTwinReq D (treeTwinDataStage K D Other kinds) n δ (a.1, treeStagesTwin swaps a.2) b →
      TreeTwinChallengeCoinStage K D (Saved K circuits settings D parameter openings)
        δ (a.1, treeStagesTwin swaps a.2) b →
      TreeTwinChallengeCoinStage K D (fun q =>
        TreeTwinCheckTagged K D (Saved K circuits settings D parameter openings) tagLabels q ∧
        (Advancing K circuits settings D parameter openings q ∨ Finishing K circuits settings D parameter openings q))
        δ (a.1, treeStagesTwin swaps a.2) b)
    (field : TreeTwinExtendChallengeStage K D (Saved K circuits settings D parameter openings) ∈ kinds)
    (exitNext : TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Other kinds
      (TreeTwinChallengeCoinStage K D (fun q =>
        Saved K circuits settings D parameter openings q ∧ Finishing K circuits settings D parameter openings q))) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Other kinds
      (TreeTwinChallengeCoinStage K D (Saved K circuits settings D parameter openings)) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨step, rnd, sent, coinRnd, ⟨⟨saved, addresses⟩, advance | finish⟩,
    visible, future, fresh₁, fresh₂, left, right⟩ :=
    classified n δ swaps a b reach bound good active salts req stage
  · have covered : ∀ tag label, (tag, label) ∈ tagLabels → ∀ values, values.length = 1 →
        TreeStagesChallengeCovered K (treeStagesTwin swaps a.2).1.1 tag label values := by
      intro tag label mem values length
      exact treeTwin_reached_challengeCovered prims K circuits settings top tree D A
        (dealtKeys parameter seeds pairs) p.2.1 p.2.2 seeds tagLabels historyLimit r padding n a reach swaps
        tag label mem values length
    have reduced := challengeCoin_reduction K circuits settings D parameter openings tagLabels
      (treeStagesTwin swaps a.2).1.1 covered δ (a.1, treeStagesTwin swaps a.2) b le_rfl
      ⟨step, rnd, sent, coinRnd, ⟨advance, addresses⟩, visible, future, fresh₁, fresh₂, left, right⟩
    exact treeTwinKindNext_reductionCoin prims K circuits settings top tree D A parameter seeds pairs z p r
      Other (fun q => ∀ values, Saved K circuits settings D parameter openings (q.step K D values))
      (Saved K circuits settings D parameter openings) (fun _ h => h) kinds field
      n δ swaps a b reach bound good active salts req reduced
  · exact exitNext n δ swaps a b reach bound good active salts req
      ⟨step, rnd, sent, coinRnd, ⟨saved, finish⟩, visible, future, fresh₁, fresh₂, left, right⟩

/-- Rerand's actual partial Coin enters the first field kind with its
concrete caller saved, or propagates an earlier honest abort. -/
theorem Caller.rerand_round_saved (c : Caller K circuits settings D parameter openings)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      let p := c.checkData K circuits settings D parameter openings
      TreeStagesExpansionCovered K base (p.tag i) (p.hashLabel i) values ((p.tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel c.peer.δ a b) (fresh : TreeSimFutureEmpty (c.rest.ρ + 2) a.1.2)
    (future : TreeSimFutureZero (c.rest.ρ + 2) c.peer.δ) (base_le : base ≤ a.1.1)
    (n : ℕ)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (field : TreeTwinExtendChallengeStage K D (Saved K circuits settings D parameter openings) ∈ kinds) :
    let coin := c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂ c.nonzero₁ c.nonzero₂ c.sent
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D coin.live coin.count coinRnd coin.st₁ coin.next₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D coin.live coin.count coinRnd coin.st₂ coin.next₂)).run b)
      (fun u w => ∃ δ, treeTwinReq D
        (treeTwinDataStage K D (Allowed K circuits settings D parameter openings) kinds) n δ
        ((u.1.1, u.1.2.1), u.2) ((w.1.1, w.1.2.1), w.2)) := by
  exact c.rest.checkCoin_round_stage prims K D A c.peer c.nonzero₁ c.nonzero₂ c.sent c.data coinRnd base covered
    state a b related fresh future base_le n (Allowed K circuits settings D parameter openings)
    (Saved K circuits settings D parameter openings) (c.firstSlice_saved K circuits settings D parameter openings base coinRnd)
    kinds field

end TreeTwinBoundaries

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHonestReductionRecipe.coin_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinHonestReductionRecipe.coin_steps

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHonestReductionRecipe.sliceHalving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinHonestReductionRecipe.sliceHalving

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_sliceBody_halving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_sliceBody_halving

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.Caller.firstSlice_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.Caller.firstSlice_saved

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.Caller.slice_recipe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.Caller.slice_recipe

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.Caller.halving_recipe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.Caller.halving_recipe

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.Caller.sliceHalving_recipe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.Caller.sliceHalving_recipe

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.advancing_recipe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.advancing_recipe

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.Caller.check_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.Caller.check_cases

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.finishing_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.finishing_programs

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.challengeCoin_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.challengeCoin_reduction

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.Caller.rerand_round_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.Caller.rerand_round_saved

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_honestChallengeCoin_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_honestChallengeCoin_reduction

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.advancing_recipeClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.advancing_recipeClosure

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBoundaries.checkCoin_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinBoundaries.checkCoin_next

end ThresholdLeanXmssSecurity
