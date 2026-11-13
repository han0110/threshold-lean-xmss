import ThresholdLeanXmssSecurity.Proof.TreeTwinCollectorValue

/-! # Values, layer counts and live history budgets

Tuple value transport ignores resharing modes. Exact layer counts and live bit
history budgets supply the field budget at the actual Rerand exit.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinValueCarry
open TreeTwinValueLink TreeTwinCollectorValue TreeTwinHistoryRecords
open TreeTwinSavedSchedule TreeTwinSavedEntry TreeTwinLinked2 TreeCheckWalkTranscript
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

private theorem tupleAt_congr (p q : List (Tuple C))
    (same : q.map (fun t => (t.x, t.y, t.z, t.count)) =
      p.map (fun t => (t.x, t.y, t.z, t.count)))
    (k : ℕ) (t : Tuple C) (atQ : q[k]? = some t) :
    ∃ u, p[k]? = some u ∧ t.x = u.x ∧ t.y = u.y ∧ t.z = u.z ∧ t.count = u.count := by
  have atP := congrArg (fun ts => ts[k]?) same
  simp only [List.getElem?_map, atQ, Option.map_some] at atP
  cases hu : p[k]? with
  | none => simp [hu] at atP
  | some u =>
    simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at atP
    exact ⟨u, rfl, atP.1, atP.2.1, atP.2.2.1, atP.2.2.2⟩

theorem valueLink_congr (D : C.Coalition)
    (p q : C.Party → MainInput C × List (Tuple C)) (st st' : C.Party → RunState C)
    (wires : ∀ i, i ∉ D.1 → (q i).1 = (p i).1)
    (tuples : ∀ i, i ∉ D.1 → (q i).2.map (fun t => (t.x, t.y, t.z, t.count)) =
      (p i).2.map (fun t => (t.x, t.y, t.z, t.count)))
    (history : ∀ i, i ∉ D.1 → (st' i).history = (st i).history)
    (values : ValueLink D p st) : ValueLink D q st' := by
  intro hist
  have prior : AllHistory D st := by
    intro T i j hi hj heldI heldJ
    rw [← history i hi, ← history j hj]
    exact hist T i j hi hj heldI heldJ
  obtain ⟨wire, tuple⟩ := values prior
  constructor
  · intro T i j hi hj heldI heldJ
    simpa only [wires i hi, wires j hj] using wire T i j hi hj heldI heldJ
  · intro T i j hi hj heldI heldJ k t t' ht ht'
    obtain ⟨u, hu, hx, hy, hz, _⟩ := tupleAt_congr _ _ (tuples i hi) k t ht
    obtain ⟨u', hu', hx', hy', hz', _⟩ := tupleAt_congr _ _ (tuples j hj) k t' ht'
    simpa only [hx, hy, hz, hx', hy', hz'] using tuple T i j hi hj heldI heldJ k u u' hu hu'

theorem tupleShape_congr (D : C.Coalition)
    (p q : C.Party → MainInput C × List (Tuple C))
    (tuples : ∀ i, i ∉ D.1 → (q i).2.map (fun t => (t.x, t.y, t.z, t.count)) =
      (p i).2.map (fun t => (t.x, t.y, t.z, t.count)))
    (shape : TupleShape D p) : TupleShape D q := by
  obtain ⟨counts, hc⟩ := shape
  refine ⟨counts, fun i hi => ?_⟩
  have same := congrArg (List.map (fun t => t.2.2.2)) (tuples i hi)
  simpa only [List.map_map, Function.comp_def, hc i hi] using same

theorem valueLink_nextLabel (D : C.Coalition)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C)
    (values : ValueLink D p st) : ValueLink D p (fun i => nextLabel (st i)) := values

theorem valueLink_peerLayerShares {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i) (jobs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 →
      treeSimPeerOutputs K D ctx (gatesAt jobs layer).length rnd v st k sent i = some (x i))
    (masks : MaskAgree D (gatesAt jobs layer).length rnd)
    (values : ValueLink D p st) (shape : TupleShape D p)
    (mode : C.Party → ReshareMode) :
    ValueLink D (fun i => treeTwinLayerShares K jobs layer (mode i) (p i) (x i).1)
      (fun i => (x i).2) ∧
    TupleShape D (fun i => treeTwinLayerShares K jobs layer (mode i) (p i) (x i).1) := by
  have old := valueLink_peerLayer K D ctx self jobs layer p st rnd v k sent x out masks values shape
  constructor
  · exact valueLink_congr D (fun i => treeTwinLayerShares K jobs layer .peer (p i) (x i).1) _ _ _ (fun _ _ => rfl)
      (fun _ _ => by simp [treeTwinLayerShares]) (fun _ _ => rfl) old.1
  · exact tupleShape_congr D (fun i => treeTwinLayerShares K jobs layer .peer (p i) (x i).1) _ (fun _ _ => by simp [treeTwinLayerShares]) old.2

theorem valueLink_collectorLayerShares (D : C.Coalition) (jobs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent sent' : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 → treeSimCollectorRecorded K (gatesAt jobs layer).length st i
      (colOuts K D (gatesAt jobs layer).length rnd v sent sent' i) = some (x i))
    (masks : MaskAgree D (gatesAt jobs layer).length rnd)
    (values : ValueLink D p st) (shape : TupleShape D p)
    (mode : C.Party → ReshareMode) :
    ValueLink D (fun i => treeTwinLayerShares K jobs layer (mode i) (p i) (x i).1)
      (fun i => (x i).2) ∧
    TupleShape D (fun i => treeTwinLayerShares K jobs layer (mode i) (p i) (x i).1) := by
  have old := valueLink_collectorLayer K D jobs layer p st rnd v sent sent' x out masks values shape
  constructor
  · exact valueLink_congr D (fun i => treeTwinLayerShares K jobs layer .collector (p i) (x i).1) _ _ _ (fun _ _ => rfl)
      (fun _ _ => by simp [treeTwinLayerShares]) (fun _ _ => rfl) old.1
  · exact tupleShape_congr D (fun i => treeTwinLayerShares K jobs layer .collector (p i) (x i).1) _ (fun _ _ => by simp [treeTwinLayerShares]) old.2

/-- The honest tuple counts are exactly the completed layer gate counts. -/
def LayerCounts (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) : Prop :=
  ∀ i, i ∉ D.1 → (p i).2.map (·.count) =
    (List.range layer).map (fun l => (gatesAt circs l).length)

theorem layerCounts_entry (D : C.Coalition) (circs : List Circuit)
    (w : C.Party → MainInput C) : LayerCounts D circs 0 (fun i => (w i, [])) := by
  intro i hi
  rfl

theorem layerCounts_layerShares (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (mode : C.Party → ReshareMode)
    (z : C.Party → Shares C Bit) (counts : LayerCounts D circs layer p) :
    LayerCounts D circs (layer + 1) (fun i => treeTwinLayerShares K circs layer (mode i) (p i) (z i)) := by
  intro i hi
  simp [treeTwinLayerShares, List.range_succ, counts i hi]

theorem tupleShape_of_layerCounts (D : C.Coalition) (circs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (counts : LayerCounts D circs layer p) :
    TupleShape D p := ⟨_, counts⟩

theorem total_of_layerCounts (D : C.Coalition) (circs : List Circuit)
    (p : C.Party → MainInput C × List (Tuple C)) (counts : LayerCounts D circs (depth circs) p) :
    ∀ i, i ∉ D.1 → ((p i).2.map (·.count)).sum + (outputsOf circs).length = tupleCount circs := by
  intro i hi
  exact layerCounts_total circs (p i).2 (counts i hi)

theorem range_drop_succ (n layer next : ℕ) (rest : List ℕ)
    (eq : (List.range n).drop layer = layer :: next :: rest) : next = layer + 1 := by
  have len := congrArg List.length eq
  simp only [List.length_drop, List.length_range, List.length_cons] at len
  have atOne := congrArg (fun xs => xs[1]?) eq
  simpa only [List.getElem?_drop, List.getElem?_range (by omega : layer + 1 < n),
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] using atOne.symm

theorem range_drop_last (n layer : ℕ)
    (eq : (List.range n).drop layer = [layer]) : layer + 1 = n := by
  have len := congrArg List.length eq
  simp only [List.length_drop, List.length_range, List.length_cons, List.length_nil] at len
  omega

/-- Only live honest histories need to be bounded at a partial round. -/
def BitBudget (D : C.Coalition) (live : C.Party → Bool)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C) : Prop :=
  ∀ i, i ∉ D.1 → live i = true → ∀ T,
    ((st i).history T).length ≤ ((p i).2.map (·.count)).sum

theorem bitBudget_empty (D : C.Coalition) (live : C.Party → Bool)
    (w : C.Party → MainInput C) (st : C.Party → RunState C)
    (empty : ∀ i, i ∉ D.1 → live i = true → (st i).history = fun _ => []) :
    BitBudget D live (fun i => (w i, [])) st := by
  intro i hi hl T
  simp [empty i hi hl]

theorem bitBudget_antitone (D : C.Coalition) (live live' : C.Party → Bool)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C)
    (restrict : ∀ i, i ∉ D.1 → live' i = true → live i = true)
    (prev : BitBudget D live p st) : BitBudget D live' p st := by
  intro i hi hl
  exact prev i hi (restrict i hi hl)

theorem bitBudget_peerLayerShares {α : Type} (D : C.Coalition)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (jobs : List Circuit) (layer : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (st : C.Party → RunState C) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (mode : C.Party → ReshareMode)
    (out : ∀ i, i ∉ D.1 → live i = true →
      treeSimPeerOutputs K D ctx (gatesAt jobs layer).length rnd v st k sent i = some (x i))
    (prev : BitBudget D live p st) :
    BitBudget D live (fun i => treeTwinLayerShares K jobs layer (mode i) (p i) (x i).1)
      (fun i => (x i).2) := by
  intro i hi hl T
  have record := peerOutputs_history K D ctx (gatesAt jobs layer).length rnd v st k sent i
    (x i) (out i hi hl)
  have bound := recordPeer_bit_length_le K (ctx i).self (st i).history (x i).1
    (gatesAt jobs layer).length T
  rw [← record] at bound
  have before := prev i hi hl T
  simpa only [treeTwinLayerShares, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] using
    bound.trans (Nat.add_le_add_right before _)

theorem bitBudget_collectorLayerShares (D : C.Coalition) (live : C.Party → Bool)
    (jobs : List Circuit) (layer : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (st : C.Party → RunState C) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent sent' : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (mode : C.Party → ReshareMode)
    (out : ∀ i, i ∉ D.1 → live i = true →
      treeSimCollectorRecorded K (gatesAt jobs layer).length st i
        (colOuts K D (gatesAt jobs layer).length rnd v sent sent' i) = some (x i))
    (prev : BitBudget D live p st) :
    BitBudget D live (fun i => treeTwinLayerShares K jobs layer (mode i) (p i) (x i).1)
      (fun i => (x i).2) := by
  intro i hi hl T
  have record := (collectorRecorded_some K (gatesAt jobs layer).length st i _ (x i)
    (out i hi hl)).2
  have bound := recordMode_length_le K .collector i (st i).history (x i).1
    (gatesAt jobs layer).length T
  rw [← record] at bound
  have before := prev i hi hl T
  simpa only [treeTwinLayerShares, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] using
    bound.trans (Nat.add_le_add_right before _)

theorem fieldBudget_of_sources (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit)))
    (c : Caller K circuits settings top tree D parameter openings)
    (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 → treeSimPeerOutputs K D c.peer.ctx₁ c.peer.count c.peer.rnd₁
      c.peer.v₁ c.peer.st₁ c.peer.k₁ c.sent i = some (x i))
    (budget : BitBudget D (fun _ => true) c.rest.p₁ c.peer.st₁)
    (counts : LayerCounts D c.rest.circs (depth c.rest.circs) c.rest.p₁) :
    FieldBudget circuits settings D (tupleCount c.rest.circs) 0 (fun i => (x i).2) := by
  exact fieldBudget_entry K circuits settings top tree D parameter openings c x out
    (fun i hi => budget i hi rfl) (total_of_layerCounts D c.rest.circs c.rest.p₁ counts)

end ThresholdLeanXmssSecurity.TreeTwinValueCarry


/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_congr

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.tupleShape_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.tupleShape_congr

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_nextLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_nextLabel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_peerLayerShares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_peerLayerShares

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_collectorLayerShares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.valueLink_collectorLayerShares

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.layerCounts_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.layerCounts_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.layerCounts_layerShares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.layerCounts_layerShares

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.tupleShape_of_layerCounts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.tupleShape_of_layerCounts

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.total_of_layerCounts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.total_of_layerCounts

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.range_drop_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.range_drop_succ

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.range_drop_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.range_drop_last

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_empty

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_antitone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_antitone

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_peerLayerShares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_peerLayerShares

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_collectorLayerShares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.bitBudget_collectorLayerShares

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueCarry.fieldBudget_of_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueCarry.fieldBudget_of_sources
