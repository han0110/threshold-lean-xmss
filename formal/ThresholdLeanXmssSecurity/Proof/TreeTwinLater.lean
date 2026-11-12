import ThresholdLeanXmssSecurity.Proof.TreeTwinKinds

/-!
Concrete later rounds of the linked twin execution.

The target is `TreeTwinLinkedGoal`. In particular, arbitrary `Circuits`
can have zero output width: `TreeTwinAllowedOutputs` applies only to its
chosen codes, not to every reachable batch. Zero-output batches require
their own later kinds. The unlinked `TreeTwinScheduleData` and
`TreeTwinTailData` are not used.

The pinned and current leanVM proofs were searched. The saved threshold
tuple metadata and partial Coin boundary below are specific to this protocol.

`checkCoinData_steps` identifies the original Rerand continuation exactly.
`checkCoin_round_stage` moves its partial Coin through the real expansion,
zero test and field draw, or propagates an earlier abort. Its cache coverage
premise is not inferred from `Allowed`: `TreeTwinRunData` only relates counts
between the two runs, not to the finite circuit schedule. The first field
exchange has an unconditional `TreeTwinKindNext` proof, as does a stopped
Coin. The field and challenge stages retain a supplied `Recipes` predicate
unchanged, so further invariants on saved data and callers can be preserved.

The global interface is `TreeTwinLinkedGoal`. It requires a
concrete allowed-code choice and entry padding (including `inner'`), the
actual-reach link supplying finite expansion coverage at RerandCoin, the
zero-output kinds, and closure of the subsequent challenge, digest, opening,
output and batch stages. Same-holder histories and cached later salt reads
are separate global constraints.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- The saved data relation fixes every count and mode in the other run;
it does not identify the count list with a circuit schedule. -/
theorem treeTwinRunData_counts_modes (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (data : TreeTwinRunData K D ctx₁ ctx₂ p₁ p₂) (i : C.Party) (hi : i ∉ D.1) :
    (p₂ i).2.map (·.count) = (p₁ i).2.map (·.count) ∧
      (p₂ i).2.map (·.mode) = (p₁ i).2.map (·.mode) := by
  have length := (data.1 i hi).2
  have entry (k : ℕ) (hk₂ : k < (p₂ i).2.length) (hk₁ : k < (p₁ i).2.length) :
      ((p₂ i).2[k]).count = ((p₁ i).2[k]).count ∧
        ((p₂ i).2[k]).mode = ((p₁ i).2[k]).mode := by
    obtain ⟨dx, dy, h⟩ := data.2.2 k
    have h' := h i hi _ _ (List.getElem?_eq_getElem hk₁) (List.getElem?_eq_getElem hk₂)
    exact ⟨h'.1, h'.2.1⟩
  constructor
  · apply List.ext_getElem (by simpa)
    intro k hk₂ hk₁
    simpa using (entry k (by simpa using hk₂) (by simpa using hk₁)).1
  · apply List.ext_getElem (by simpa)
    intro k hk₂ hk₁
    simpa using (entry k (by simpa using hk₂) (by simpa using hk₁)).2

/-- The real Rerand tuple adds the same output width on both sides,
regardless of the actual saved share values. -/
theorem treeTwinRunData_rerand_counts (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (data : TreeTwinRunData K D ctx₁ ctx₂ p₁ p₂)
    (circs : List Circuit) (v₁ v₂ : C.Party → Shares C Bit) (i : C.Party) (hi : i ∉ D.1) :
    ((treeStagesRerandTuples K circs (p₁ i) (v₁ i)).map (·.count)).sum =
      ((treeStagesRerandTuples K circs (p₂ i) (v₂ i)).map (·.count)).sum := by
  have counts := (treeTwinRunData_counts_modes K D ctx₁ ctx₂ p₁ p₂ data i hi).1
  simp only [treeStagesRerandTuples, List.map_append, List.map_cons, List.map_nil, counts]

/-- A prior honest abort propagates in this actual Coin round. The
adversary is called once with the unchanged view, and no continuation runs. -/
theorem treeTwin_coin_stopped_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (δ : HiddenAddress C → Bit)
    (live : C.Party → Bool) (stopped : ∃ i, i ∉ D.1 ∧ live i ≠ true)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live count rnd st₁ k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live count rnd st₂ k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_coin_partial_factor K D A _ live stopped,
    treeSim_coin_partial_factor K D A _ live stopped]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b related)
  intro u z h
  apply relTriple_pure_pure
  dsimp only
  exact ⟨congrArg Prod.fst h.1, congrArg Prod.snd h.1, rfl, rfl, h.2⟩

/-- The concrete code saved at the first check Coin. Counts agree between
runs; any connection to the batch schedule must be proved separately. -/
structure TreeTwinCheckCoinData (D : C.Coalition) where
  T₀ : C.Term
  pivotParty : C.Party
  pivot : Pivot K D T₀ pivotParty
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  tuples₁ : C.Party → List (Tuple C)
  tuples₂ : C.Party → List (Tuple C)
  counts : ∀ i, ((tuples₁ i).map (·.count)).sum = ((tuples₂ i).map (·.count)).sum
  tag : C.Party → ℕ
  hashLabel : C.Party → ℕ
  label : ℕ
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label
  finish₁ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput
  finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput

def TreeTwinCheckCoinData.next₁ (D : C.Coalition) (p : TreeTwinCheckCoinData K D) :=
  fun i => treeStagesCheckAfterCoin K (p.ctx₁ i) (p.tuples₁ i) (p.tag i) (p.hashLabel i) (p.finish₁ i)

def TreeTwinCheckCoinData.next₂ (D : C.Coalition) (p : TreeTwinCheckCoinData K D) :=
  fun i => treeStagesCheckAfterCoin K (p.ctx₂ i) (p.tuples₂ i) (p.tag i) (p.hashLabel i) (p.finish₂ i)

def TreeTwinCheckCoinData.expansion (D : C.Coalition) (p : TreeTwinCheckCoinData K D)
    (base : HashCache C) (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) :
    C.Party → List E := fun i => treeStagesCachedExpansion K base (p.tag i) (p.hashLabel i)
      ((treeSimCoinOutput K D 1 rnd sent i).getD []) ((p.tuples₁ i).map (·.count)).sum

def TreeTwinCheckCoinData.firstSlice (D : C.Coalition) (p : TreeTwinCheckCoinData K D)
    (base : HashCache C) (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) :
    TreeStagesExtendMultChallenge K D :=
  treeStagesFirstSliceChallenge K D p.T₀ p.pivotParty p.pivot p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys
    p.tuples₁ p.tuples₂ (p.expansion K D base rnd sent) p.label p.st₁ p.st₂ p.lab₁ p.lab₂ p.finish₁ p.finish₂

def TreeTwinCheckCoinData.firstLive (D : C.Coalition) (p : TreeTwinCheckCoinData K D)
    (base : HashCache C) (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) : C.Party → Bool :=
  treeStagesExpansionLive K base p.tag p.hashLabel (fun i => ((p.tuples₁ i).map (·.count)).sum)
    (fun i => (treeSimCoinOutput K D 1 rnd sent i).getD [])
    (fun i => (treeSimCoinOutput K D 1 rnd sent i).map fun _ => ())

/-- One actual round enters the first slice, or propagates an earlier
abort. The code saved in `firstSlice` is the original remaining check.
Cache coverage is an explicit concrete read premise, not a coupling premise. -/
theorem TreeTwinCheckCoinData.round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeTwinCheckCoinData K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old)
    (live : C.Party → Bool) (coinRnd : C.Party → PrssOutput C E)
    (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      TreeStagesExpansionCovered K base (p.tag i) (p.hashLabel i) values ((p.tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2)
    (base_le : base ≤ a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live 1 coinRnd p.st₁ (p.next₁ K D))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live 1 coinRnd p.st₂ (p.next₂ K D))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧ ∃ δ,
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (p.label + 2) δ ∧ TreeSimFutureEmpty (p.label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (p.label + 2) z.2.2 ∧
        ((u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none)) ∨
          ∃ rnd,
            let step := p.firstSlice K D base coinRnd u.1.2.2
            let d := step.data K D rnd δ
            let live' := p.firstLive K D base coinRnd u.1.2.2
            u.1.2.1 = treeSimExtendMultPartial K D d.ctx₁ live' d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
            z.1.2.1 = treeSimExtendMultPartial K D d.ctx₂ live' d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
            base ≤ u.2.1.1)) := by
  by_cases active : ∀ i, i ∉ D.1 → live i = true
  · rw [treeStages_coin_partial_live K D live active, treeStages_coin_partial_live K D live active]
    apply relTriple_post_mono (treeStages_check_coin_firstSlice_round prims K D A p.T₀ p.pivotParty
      p.pivot old visible p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys p.tuples₁ p.tuples₂ p.counts
      p.tag p.hashLabel p.label future coinRnd p.st₁ p.st₂ p.lab₁ p.lab₂ p.finish₁ p.finish₂
      base covered state a b related fresh base_le)
    intro u z h
    obtain ⟨sent, rnd, δ, stateEq, sent₁, sent₂, left, right, caches, vis, zero, fresh₁, fresh₂, le⟩ := h
    refine ⟨stateEq, sent₁.trans sent₂.symm, δ, caches, vis, zero, fresh₁, fresh₂, Or.inr ⟨rnd, ?_⟩⟩
    rw [sent₁]
    exact ⟨left, right, le⟩
  · push Not at active
    apply relTriple_post_mono (treeTwin_coin_stopped_round prims K D A old live active 1 coinRnd
      p.st₁ p.st₂ (p.next₁ K D) (p.next₂ K D) state a b related)
    intro u z h
    obtain ⟨stateEq, sentEq, left, right, caches, frame₁, frame₂⟩ := h
    refine ⟨stateEq, sentEq, old, caches, visible, future, ?_, ?_, Or.inl ⟨left, right⟩⟩
    · rw [frame₁]
      exact fun x hx => fresh x (by omega)
    · rw [frame₂]
      exact fun x hx => treeSim_futureEmpty_related fresh related.2 x (by omega)

/-- The actual optional Rerand returns have the same tag, even when both
certificate values use their inactive fallback. -/
theorem treeTwin_peer_saved_tag (D : C.Coalition) (d : TreeSimPeerData K D)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) :
    ((treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i).getD
      (0, nextLabel (d.st₁ i))).2.tag =
    ((treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i).getD
      (0, nextLabel (d.st₂ i))).2.tag := by
  have h := d.outputs K D sent i
  generalize treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i = x at h ⊢
  generalize treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i = y at h ⊢
  cases h with
  | none => exact (d.states i hi).2.1
  | some h => exact h.2.1.2.1

/-- Extract the actual first-check code from the Rerand boundary. The
inactive corrupt entries are totalized to empty tuples on both sides. -/
def TreeStagesRerandTail.checkCoinData (D : C.Coalition) (d : TreeSimPeerData K D)
    (rest : TreeStagesRerandTail K D d)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (data : TreeTwinRunData K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂) :
    TreeTwinCheckCoinData K D := by
  let n := rest.coinNext K D d rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent
  exact {
    T₀ := d.T₀, pivotParty := d.pivotParty, pivot := d.pivot
    ctx₁ := d.ctx₁, ctx₂ := d.ctx₂, self₁ := d.self₁, self₂ := d.self₂, keys := rest.keys
    tuples₁ := fun i => if i ∈ D.1 then [] else treeStagesRerandTuples K rest.circs (rest.p₁ i) (n.x₁ i).1
    tuples₂ := fun i => if i ∈ D.1 then [] else treeStagesRerandTuples K rest.circs (rest.p₂ i) (n.x₂ i).1
    counts := by
      intro i
      by_cases hi : i ∈ D.1
      · simp only [if_pos hi]
      · simp only [if_neg hi]
        exact treeTwinRunData_rerand_counts K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂ data rest.circs
          (fun i => (n.x₁ i).1) (fun i => (n.x₂ i).1) i hi
    tag := fun i => if i ∈ D.1 then 0 else (n.st₁ i).tag
    hashLabel := fun i => if i ∈ D.1 then 0 else (n.st₁ i).label
    label := n.label, st₁ := n.st₁, st₂ := n.st₂, lab₁ := n.lab₁, lab₂ := n.lab₂
    finish₁ := fun i => treeStagesAfterVerify (rest.gadgets₁ i) rest.circs (n.x₁ i).1 (rest.finish₁ i)
    finish₂ := fun i => treeStagesAfterVerify (rest.gadgets₂ i) rest.circs (n.x₂ i).1 (rest.finish₂ i) }

theorem TreeStagesRerandTail.checkCoinData_programs (D : C.Coalition) (d : TreeSimPeerData K D)
    (rest : TreeStagesRerandTail K D d)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (data : TreeTwinRunData K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂)
    (i : C.Party) (hi : i ∉ D.1) :
    let n := rest.coinNext K D d rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent
    let p := rest.checkCoinData K D d nonzero₁ nonzero₂ sent data
    n.next₁ i = p.next₁ K D i ∧ n.next₂ i = p.next₂ K D i := by
  dsimp only
  constructor
  · simp only [TreeStagesRerandTail.checkCoinData, TreeTwinCheckCoinData.next₁, if_neg hi]
    rfl
  · have tag := treeTwin_peer_saved_tag K D d sent i hi
    have label := (treeStages_peer_recorded_label K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i).trans
      ((congrArg (· + 1) (d.states i hi).1).trans
        (treeStages_peer_recorded_label K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i).symm)
    simp only [TreeStagesRerandTail.checkCoinData, TreeTwinCheckCoinData.next₂, if_neg hi]
    change treeStagesCheckAfterCoin K _ _ _ _ _ = treeStagesCheckAfterCoin K _ _ _ _ _
    dsimp only [TreeStagesRerandTail.coinNext, treeStages_peer_coinNext]
    rw [tag, label]

theorem treeTwin_coinPartial_congr {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k k' : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (equal : ∀ i, i ∉ D.1 → k i = k' i) :
    treeSimCoinPartial K D live count rnd st k = treeSimCoinPartial K D live count rnd st k' := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinPartial, treeSimCoinWaiting, hi]
  · by_cases hl : live i = true
    · simp only [treeSimCoinPartial, if_pos hl, treeSimCoinWaiting, if_neg hi, equal i hi]
    · simp only [treeSimCoinPartial, if_neg hl]

/-- Both concrete partial-step vectors are unchanged by extracting the
first-check data, including stopped and corrupt operators. -/
theorem TreeStagesRerandTail.checkCoinData_steps (D : C.Coalition) (d : TreeSimPeerData K D)
    (rest : TreeStagesRerandTail K D d)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (data : TreeTwinRunData K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂)
    (rnd : C.Party → PrssOutput C E) :
    let n := rest.coinNext K D d rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent
    let p := rest.checkCoinData K D d nonzero₁ nonzero₂ sent data
    treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ =
      treeSimCoinPartial K D n.live 1 rnd p.st₁ (p.next₁ K D) ∧
    treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂ =
      treeSimCoinPartial K D n.live 1 rnd p.st₂ (p.next₂ K D) := by
  dsimp only
  constructor
  · apply treeTwin_coinPartial_congr
    intro i hi
    exact (rest.checkCoinData_programs K D d nonzero₁ nonzero₂ sent data i hi).1
  · apply treeTwin_coinPartial_congr
    intro i hi
    exact (rest.checkCoinData_programs K D d nonzero₁ nonzero₂ sent data i hi).2

/-- An actual Coin boundary containing an honest abort. Its next round is
closed independently of all later check and output code. -/
def TreeTwinStoppedCoinStage {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (_δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (live : C.Party → Bool) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput),
    (∃ i, i ∉ D.1 ∧ live i ≠ true) ∧
    a.1.2 = treeSimCoinPartial K D live count rnd st₁ k₁ ∧
    b.1.2 = treeSimCoinPartial K D live count rnd st₂ k₂

theorem treeTwinKindNext_stoppedCoin (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinStoppedCoinStage K D) := by
  intro n δ swaps a b _ _ _ _ _ req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨live, count, rnd, st₁, st₂, k₁, k₂, stopped, left, right⟩ := stage
  rw [left, right, ← state]
  apply relTriple_post_mono (treeTwin_coin_stopped_round prims K D A δ live stopped count rnd
    st₁ st₂ k₁ k₂ a.1.1 _ b.2 related)
  intro u w h
  obtain ⟨same, _, hu, hw, caches, _, _⟩ := h
  obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1
    (fun i _ => Or.inl ⟨congrFun hu i, congrFun hw i⟩)
  exact Or.inr ⟨[], δ, fun x hx => by simp at hx, caches, same, done, flags, Or.inl ⟨hu, hw⟩⟩

theorem treeTwin_extendPartial_live {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (active : ∀ i, i ∉ D.1 → live i = true)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α) :
    treeSimExtendMultPartial K D ctx live count rnd v st k =
      treeSimExtendMultWaiting K D ctx count rnd v st k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
  · simp [treeSimExtendMultPartial, active i hi]

theorem treeTwin_sameKind_extendPartial {α : Type} (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C) (live : C.Party → Bool) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C E) (v₁ v₂ : C.Party → ℕ → E)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (i : C.Party) (hi : i ∉ D.1) :
    TreeTwinSameKind (treeSimExtendMultPartial K D ctx₁ live count rnd₁ v₁ st₁ k₁ i)
      (treeSimExtendMultPartial K D ctx₂ live count rnd₂ v₂ st₂ k₂ i) := by
  by_cases hl : live i = true
  · exact Or.inr ⟨_, _, _, _, by
      simp only [treeSimExtendMultPartial, if_pos hl, treeSimExtendMultWaiting, if_neg hi]; rfl, by
      simp only [treeSimExtendMultPartial, if_pos hl, treeSimExtendMultWaiting, if_neg hi]; rfl⟩
  · exact Or.inl ⟨by simp [treeSimExtendMultPartial, hl], by simp [treeSimExtendMultPartial, hl]⟩

/-- One actual field-reshare round keeps the saved challenge body and
enters its Coin, including all inherited-abort cases. -/
theorem treeTwin_extendChallenge_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesExtendMultChallenge K D)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (future : TreeSimFutureZero (p.label + 1) δ)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2) :
    let d := p.data K D rnd δ
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧
        TreeSimFutureZero (p.label + 2) δ ∧ TreeSimFutureEmpty (p.label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (p.label + 2) z.2.2 ∧
        ((u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none)) ∨
          ∃ sent coinRnd,
            let n := p.coinNext K D rnd δ sent
            u.1.2.1 = treeSimCoinPartial K D n.live n.count coinRnd n.st₁ n.next₁ ∧
            z.1.2.1 = treeSimCoinPartial K D n.live n.count coinRnd n.st₂ n.next₂)) := by
  dsimp only
  by_cases active : ∀ i, i ∉ D.1 → live i = true
  · rw [treeTwin_extendPartial_live K D _ live active, treeTwin_extendPartial_live K D _ live active]
    apply relTriple_post_mono (treeStages_extendMult_coin_round prims K D A (p.data K D rnd δ)
      p.label 1 visible future p.keys p.lab₁ p.lab₂ (p.next₁ K D) (p.next₂ K D)
      (fun i x => treeStages_challenge_prefix K (p.ctx₁ i) x.2 (p.body₁ i x))
      (fun i x => treeStages_challenge_prefix K (p.ctx₂ i) x.2 (p.body₂ i x))
      state a b related fresh)
    intro u z h
    obtain ⟨sent, coinRnd, same, _, _, left, right, caches, zero, fresh₁, fresh₂⟩ := h
    exact ⟨same, caches, zero, fresh₁, fresh₂, Or.inr ⟨sent, coinRnd, left, right⟩⟩
  · push Not at active
    apply relTriple_post_mono (treeStages_extendMult_partial_round prims K D A (p.data K D rnd δ)
      live active state a b related)
    intro u z h
    obtain ⟨same, left, right, caches, frame₁, frame₂⟩ := h
    refine ⟨same, caches, (fun x hx => future x (by omega)), ?_, ?_, Or.inl ⟨left, right⟩⟩
    · rw [frame₁]; exact fun x hx => fresh x (by omega)
    · rw [frame₂]; exact fun x hx => treeSim_futureEmpty_related fresh related.2 x (by omega)

/-- The allowed recipe retains any required saved-data and caller invariant. -/
def TreeTwinExtendChallengeStage {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (Recipes : TreeStagesExtendMultChallenge K D → Prop) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (p : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E) (live : C.Party → Bool),
    let d := p.data K D rnd δ
    Recipes p ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero (p.label + 1) δ ∧
    TreeSimFutureEmpty (p.label + 1) a.2.1.2 ∧
    a.1.2 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- The same allowed recipe survives the field exchange and Coin draw. -/
def TreeTwinChallengeCoinStage {A : Adversary C E (Keys C) PEmpty PEmpty}
    (D : C.Coalition) (Recipes : TreeStagesExtendMultChallenge K D → Prop) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (p : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E)
    (sent : C.Party → Mail C E) (coinRnd : C.Party → PrssOutput C E),
    let n := p.coinNext K D rnd δ sent
    Recipes p ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero (p.label + 2) δ ∧
    TreeSimFutureEmpty (p.label + 2) a.2.1.2 ∧ TreeSimFutureEmpty (p.label + 2) b.2.2 ∧
    a.1.2 = treeSimCoinPartial K D n.live n.count coinRnd n.st₁ n.next₁ ∧
    b.1.2 = treeSimCoinPartial K D n.live n.count coinRnd n.st₂ n.next₂

/-- The next field is closed for a concrete ExtendMult/challenge boundary.
It ends in an abort or the original saved challenge Coin. -/
theorem treeTwinKindNext_extendChallenge (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) (Allowed : TreeTwinCode C E → Prop)
    (Recipes : TreeStagesExtendMultChallenge K D → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (coin : TreeTwinChallengeCoinStage K D Recipes ∈ kinds) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Allowed kinds
      (TreeTwinExtendChallengeStage K D Recipes) := by
  intro n δ swaps a b _ _ _ _ _ req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨step, rnd, live, recipe, visible, future, fresh, left, right⟩ := stage
  rw [left, right, ← state]
  apply relTriple_post_mono (treeTwin_extendChallenge_round prims K D A step rnd δ visible future live
    a.1.1 _ b.2 related fresh)
  intro u w h
  obtain ⟨same, caches, zero, e₁, e₂, ⟨hu, hw⟩ | ⟨sent, coinRnd, hu, hw⟩⟩ := h
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1
      (fun i _ => Or.inl ⟨congrFun hu i, congrFun hw i⟩)
    exact Or.inr ⟨[], δ, fun x hx => by simp at hx, caches, same, done, flags, Or.inl ⟨hu, hw⟩⟩
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1 (fun i hi => by
      rw [hu, hw]
      exact treeTwin_sameKind_coinPartial K D _ _ _ _ _ _ _ i hi)
    exact Or.inr ⟨[], δ, fun x hx => by simp at hx, caches, same, done, flags,
      Or.inr (Or.inr ⟨_, coin, step, rnd, sent, coinRnd, recipe, visible, zero, e₁, e₂, hu, hw⟩)⟩

/-- The first check Coin enters the concrete later kind, retaining the
entire check continuation. This uses only the displayed cache-read premise. -/
theorem TreeTwinCheckCoinData.round_stage (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeTwinCheckCoinData K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old)
    (live : C.Party → Bool) (coinRnd : C.Party → PrssOutput C E)
    (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      TreeStagesExpansionCovered K base (p.tag i) (p.hashLabel i) values ((p.tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2)
    (base_le : base ≤ a.1.1) (n : ℕ) (Allowed : TreeTwinCode C E → Prop)
    (Recipes : TreeStagesExtendMultChallenge K D → Prop)
    (recipes : ∀ sent, Recipes (p.firstSlice K D base coinRnd sent))
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (field : TreeTwinExtendChallengeStage K D Recipes ∈ kinds) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live 1 coinRnd p.st₁ (p.next₁ K D))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D live 1 coinRnd p.st₂ (p.next₂ K D))).run b)
      (fun u w => ∃ δ, treeTwinReq D (treeTwinDataStage K D Allowed kinds) n δ
        ((u.1.1, u.1.2.1), u.2) ((w.1.1, w.1.2.1), w.2)) := by
  apply relTriple_post_mono (p.round prims K D A old visible future live coinRnd base covered
    state a b related fresh base_le)
  intro u w h
  obtain ⟨same, _, δ, caches, vis, zero, fresh₁, _, ⟨hu, hw⟩ | ⟨rnd, hu, hw, _⟩⟩ := h
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1
      (fun i _ => Or.inl ⟨congrFun hu i, congrFun hw i⟩)
    exact ⟨δ, caches, same, done, flags, Or.inl ⟨hu, hw⟩⟩
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1 (fun i hi => by
      rw [hu, hw]
      exact treeTwin_sameKind_extendPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
    refine ⟨δ, caches, same, done, flags, Or.inr (Or.inr ⟨_, field,
      p.firstSlice K D base coinRnd u.1.2.2, rnd, p.firstLive K D base coinRnd u.1.2.2,
      recipes _, vis, ?_, ?_, hu, hw⟩)⟩
    · simpa only [TreeTwinCheckCoinData.firstSlice, treeStagesFirstSliceChallenge, Nat.add_assoc] using zero
    · simpa only [TreeTwinCheckCoinData.firstSlice, treeStagesFirstSliceChallenge, Nat.add_assoc] using fresh₁

/-- The first-check transition on the exact partial vectors used by
`TreeTwinRerandCoinStage`. No replacement of the saved Rerand output or caller
is made. Establishing `covered` at every reached boundary remains separate. -/
theorem TreeStagesRerandTail.checkCoin_round_stage (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (rest : TreeStagesRerandTail K D d)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (data : TreeTwinRunData K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      let p := rest.checkCoinData K D d nonzero₁ nonzero₂ sent data
      TreeStagesExpansionCovered K base (p.tag i) (p.hashLabel i) values ((p.tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (rest.ρ + 2) a.1.2)
    (future : TreeSimFutureZero (rest.ρ + 2) d.δ) (base_le : base ≤ a.1.1)
    (n : ℕ) (Allowed : TreeTwinCode C E → Prop)
    (Recipes : TreeStagesExtendMultChallenge K D → Prop)
    (recipes : ∀ reply, Recipes ((rest.checkCoinData K D d nonzero₁ nonzero₂ sent data).firstSlice
      K D base coinRnd reply))
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (field : TreeTwinExtendChallengeStage K D Recipes ∈ kinds) :
    let coin := rest.coinNext K D d rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D coin.live coin.count coinRnd coin.st₁ coin.next₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinPartial K D coin.live coin.count coinRnd coin.st₂ coin.next₂)).run b)
      (fun u w => ∃ δ, treeTwinReq D (treeTwinDataStage K D Allowed kinds) n δ
        ((u.1.1, u.1.2.1), u.2) ((w.1.1, w.1.2.1), w.2)) := by
  dsimp only
  obtain ⟨left, right⟩ := rest.checkCoinData_steps K D d nonzero₁ nonzero₂ sent data coinRnd
  rw [left, right]
  apply TreeTwinCheckCoinData.round_stage prims K D A _ d.δ rest.visible _ _ coinRnd base covered
    state a b related _ base_le n Allowed Recipes recipes kinds field
  · change TreeSimFutureZero (rest.ρ + 1 + 2) d.δ
    exact fun x hx => future x (by omega)
  · change TreeSimFutureEmpty (rest.ρ + 1 + 1) a.1.2
    simpa only [Nat.add_assoc] using fresh

/-- info: 'ThresholdLeanXmssSecurity.treeTwinRunData_counts_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinRunData_counts_modes

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCheckCoinData.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeTwinCheckCoinData.round

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesRerandTail.checkCoinData_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeStagesRerandTail.checkCoinData_steps

/-- info: 'ThresholdLeanXmssSecurity.treeTwinKindNext_stoppedCoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_stoppedCoin

/-- info: 'ThresholdLeanXmssSecurity.treeTwinKindNext_extendChallenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_extendChallenge

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesRerandTail.checkCoin_round_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeStagesRerandTail.checkCoin_round_stage

end ThresholdLeanXmssSecurity
