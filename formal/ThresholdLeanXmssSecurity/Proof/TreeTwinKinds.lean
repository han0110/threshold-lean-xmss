import ThresholdLeanXmssSecurity.Proof.TreeTwinOther

/-!
# The round kinds of the twin stages

`TreeTwinOther.lean` reduces `TreeTwinStageCoreGoal3` to `TreeTwinScheduleData`, `TreeTwinTailData`
and `TreeTwinDataGoal`. This file shows that the two data `Prop`s are false under one assumption,
adds the share links, proves the collector rounds and the Rerand round with them, and checks the
histories at `T₀`.

## The histories at `T₀`

Live honest holders of `T₀` hold the same real history at `T₀`. This is a deduction on paper. It
assumes that the honest operators run in lockstep, so that they record with the same count,
mode and label.

* No corrupt operator holds `T₀` (`lackedTerm`, `Ideal.lean:41-44`).
* Only `record` writes a history (`Scheme.lean:471`). It writes the positions that `filler` picks
  (`Scheme.lean:465`), and the pick depends only on the mode, the term and the gate.
* In peer mode the value at `T₀` comes from the one filler of `T₀` (`filled` is injective and
  `filled_held`, `Scheme.lean:113-114`). That filler is honest and sends the same `u` to every holder
  (`Scheme.lean:487-491`). The real ExtendMult of the check is such a peer reshare
  (`Scheme.lean:747-750`).
* The filler records `u g`, and the other holders record `unpack (pack (vector count u)) g`. The
  two agree for `g < count` by the codecs (`Scheme.lean:402-413`). This step is assumed here.
* In collector mode the value at `T₀` is `sum g` of the collector `κ` (`Scheme.lean:514-517`).
  `κ` holds `T₀` (`collector_held`, `Scheme.lean:117`), so it is honest and forwards the same `sum g`
  to every holder (`Scheme.lean:512`).
* Honest mail is delivered as sent (`Scheme.lean:1440`).
* The salt of `T₀` is the PRSS term output of `randBits` (`Scheme.lean:735-736`, `Scheme.lean:752`),
  so all holders use the same salt.

So the digest round needs one swap, with the real and the ideal history of `T₀`. Its kind has two constraints.
No frozen invariant states the equal histories, because `TreeSimRunStateRel` is per operator. So the stage must carry them. Every live holder makes the same digest query
(`Scheme.lean:579`), and only the first one is fresh. The later ones read the cache of the twin
state, which `treeTwin_hiddenDigest_twin` does not cover.

## The two data `Prop`s are false under one assumption

This is a deduction with one unchecked assumption. The successor shares of a live operator are fixed
by its continuation, although `successor`, `next` and `finish` are existential.

* The `z` clause of `TreeTwinRunData` asks for the shift of the honest local products of the saved
  tuples. The collector exit gives the shift `Σ_j (d.v₁ - d.v₂) j` at the count `d.count`
  (`treeStages_collector_exit_values`).
* No field of `TreeStagesCollectorSchedule` and no hypothesis ties `d.v₁`, `d.v₂` and `d.count` to
  `s.p₁`, `s.p₂` and `gatesAt s.circs s.layer`. Also nothing aligns the share lists of different
  honest operators, and nothing makes the two runs record the same mode.
* Let every honest operator have empty saved shares on both sides, so that `TreeTwinRunData` holds.
  Let `d.count = (gatesAt s.circs s.layer).length ≥ 1` and `d.v₂ = d.v₁ + e` with
  `Σ_j e j 0 ≠ 0`, and take `d.rnd₂` from `d.masks`. Let the adversary send the honest messages.
* Then every honest holder of `T₀` is live. At `T₀` and gate `0` its new tuple has
  `z₂ = z₁ + Σ_j e j 0`. The saved tuples ask for the shift `0`, because `mulRep` reads only `self`.

`TreeTwinTailData` fails in the same way. So `treeTwinStageCoreGoal3_of_data` cannot be used. This
file keeps the frozen relation `treeTwinDataStage` with an empty data collector stage, and puts the
linked stages among the kinds.

## The results

`treeTwinRunData_layer` and `treeTwinRunData_exit` show that one collector layer keeps
`TreeTwinRunData` under `TreeTwinLayerLink`. The proof shows that `layerX` and `layerY` keep the held
shift, also past the count. `treeTwin_scheduleLinked_next`, `treeTwin_tailLinked_next` and their
rounds are the frozen collector lemmas with `TreeTwinRunData` and the links kept.

`treeTwin_linkedCollector_round` is the collector round with no hypothesis.
`treeTwinKindNext_linkedCollector` and `treeTwinKindNext_linkedRerand` give the field `next` at the
linked collector stage and at the linked Rerand entry. The Rerand round ends in the done stage or in
`TreeTwinRerandCoinStage`. `treeTwinStageCoreGoal3_of_linked` gives `TreeTwinStageCoreGoal3` from
`TreeTwinLinkedGoal`.

`TreeTwinLinkedGoal` names the rest in exact form. It asks for allowed code that satisfies
`TreeTwinAllowedOutputs`, for the field `entry` with the linked kinds, and for `TreeTwinKindNext` at
`TreeTwinRerandCoinStage` and at each later kind. The later kinds are ExtendMult, the check Coins,
the digest round, both openings, the output and the batch transitions.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The sum of a list with a list of the same length, read at one index. -/
theorem treeTwin_zipWith_getD (l d : List Bit) (length : l.length = d.length) (w : ℕ) :
    (List.zipWith (· + ·) l d)[w]?.getD 0 = l[w]?.getD 0 + d[w]?.getD 0 := by
  rw [List.getElem?_zipWith]
  cases hl : l[w]? <;> cases hd : d[w]? <;> simp_all

/-- `treeTwin_zipWith_getD` summed over a list of wires. -/
theorem treeTwin_zipWith_sum (l d : List Bit) (length : l.length = d.length) (ws : List ℕ) :
    (ws.map fun w => (List.zipWith (· + ·) l d)[w]?.getD 0).sum =
      (ws.map fun w => l[w]?.getD 0).sum + (ws.map fun w => d[w]?.getD 0).sum := by
  simp only [treeTwin_zipWith_getD l d length, List.sum_map_add]

/-- The shift that one affine input of each gate of a layer takes from the saved sharings. -/
def treeTwinLayerShift (circs : List Circuit) (layer : ℕ) (select : Affine × Affine → Affine)
    (differences : ℕ → List Bit) : ℕ → Bit := fun g =>
  match (gatesAt circs layer)[g]? with
  | some (k, ab) => ((select ab).wires.map fun w => (differences k).getD w 0).sum
  | none => 0

/-- An affine input of each gate of a layer keeps the held shift of the saved sharings, also at the
gate indices past the count. -/
theorem treeTwin_layer_shift (D : C.Coalition) (i : C.Party) (circs : List Circuit) (layer : ℕ)
    (select : Affine × Affine → Affine) (publicTerm : C.Term)
    (wires₁ wires₂ : List (C.Term → List Bit)) (differences : ℕ → List Bit)
    (length : wires₂.length = wires₁.length)
    (outside : ∀ k, wires₁.length ≤ k → differences k = [])
    (related : ∀ k w₁ w₂, wires₁[k]? = some w₁ → wires₂[k]? = some w₂ →
      TreeSimHistoryRel D i (differences k) w₁ w₂) :
    (fun T g => match (gatesAt circs layer)[g]? with
      | some (k, ab) => (select ab).share (wires₂.getD k fun _ => []) publicTerm T | none => 0) =
    treeSimHeldShift D i (gatesAt circs layer).length (treeTwinLayerShift circs layer select differences)
      (fun T g => match (gatesAt circs layer)[g]? with
        | some (k, ab) => (select ab).share (wires₁.getD k fun _ => []) publicTerm T | none => 0) := by
  funext T g
  simp only [treeSimHeldShift, treeTwinLayerShift]
  cases hg : (gatesAt circs layer)[g]? with
  | none => simp
  | some gate =>
    obtain ⟨k, ab⟩ := gate
    have glt : g < (gatesAt circs layer).length := (List.getElem?_eq_some_iff.1 hg).1
    simp only [Affine.share, glt, true_and]
    by_cases hk : k < wires₁.length
    · have h₁ : wires₁[k]? = some wires₁[k] := List.getElem?_eq_getElem hk
      have h₂ : wires₂[k]? = some wires₂[k] := List.getElem?_eq_getElem (length ▸ hk)
      have rel := related k _ _ h₁ h₂ T
      simp only [List.getD_eq_getElem?_getD, h₁, h₂, Option.getD_some]
      by_cases held : i ∈ C.holders T ∧ lackedTerm D.1 = some T
      · rw [if_pos held] at rel
        rw [if_pos held, rel.2, treeTwin_zipWith_sum _ _ rel.1]
        abel
      · rw [if_neg held] at rel
        rw [if_neg held, rel, add_zero]
    · have h₁ : wires₁[k]? = none := List.getElem?_eq_none (by omega)
      have h₂ : wires₂[k]? = none := List.getElem?_eq_none (by omega)
      simp only [List.getD_eq_getElem?_getD, h₁, h₂, Option.getD_none, outside k (by omega)]
      simp

/-- The values of one layer that `appendLayer` appends to the saved sharing of job `k`. -/
def treeTwinAppended (circs : List Circuit) (layer k : ℕ) (value : ℕ → Bit) : List Bit :=
  ((gatesAt circs layer).zipIdx.filter (·.1.1 = k)).map fun (_, g) => value g

theorem treeTwin_appendLayer_length (circs : List Circuit) (layer : ℕ)
    (wires : List (C.Term → List Bit)) (z : Shares C Bit) :
    (appendLayer circs layer wires z).length = wires.length := by
  simp [appendLayer]

theorem treeTwin_appendLayer_getElem? (circs : List Circuit) (layer : ℕ)
    (wires : List (C.Term → List Bit)) (z : Shares C Bit) (k : ℕ) :
    (appendLayer circs layer wires z)[k]? =
      wires[k]?.map fun w T => w T ++ treeTwinAppended circs layer k (z T) := by
  simp only [appendLayer, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, zero_add]
  rfl

/-- The saved sharings after a layer keep the history relation, with the appended shift. -/
theorem treeTwin_appendLayer_rel (D : C.Coalition) (i : C.Party) (circs : List Circuit) (layer : ℕ)
    (wires₁ wires₂ : List (C.Term → List Bit)) (differences : ℕ → List Bit)
    (z₁ z₂ : Shares C Bit) (shift : ℕ → Bit)
    (related : ∀ k w₁ w₂, wires₁[k]? = some w₁ → wires₂[k]? = some w₂ →
      TreeSimHistoryRel D i (differences k) w₁ w₂)
    (shifted : z₂ = treeSimHeldShift D i (gatesAt circs layer).length shift z₁) :
    ∀ k w₁ w₂, (appendLayer circs layer wires₁ z₁)[k]? = some w₁ →
      (appendLayer circs layer wires₂ z₂)[k]? = some w₂ →
      TreeSimHistoryRel D i (differences k ++ treeTwinAppended circs layer k shift) w₁ w₂ := by
  intro k w₁ w₂ h₁ h₂
  rw [treeTwin_appendLayer_getElem?] at h₁ h₂
  obtain ⟨v₁, hv₁, rfl⟩ := Option.map_eq_some_iff.1 h₁
  obtain ⟨v₂, hv₂, rfl⟩ := Option.map_eq_some_iff.1 h₂
  have rel := related k v₁ v₂ hv₁ hv₂
  intro T
  have relT := rel T
  have entries : ∀ x ∈ (gatesAt circs layer).zipIdx.filter (·.1.1 = k),
      x.2 < (gatesAt circs layer).length := by
    intro x hx
    have := (List.mem_filter.1 hx).1
    have := (List.mem_zipIdx this).2.1
    omega
  beta_reduce
  by_cases held : i ∈ C.holders T ∧ lackedTerm D.1 = some T
  · rw [if_pos held] at relT ⊢
    refine ⟨by simp [treeTwinAppended, relT.1], ?_⟩
    rw [relT.2, List.zipWith_append relT.1]
    congr 1
    simp only [treeTwinAppended, shifted, treeSimHeldShift, List.zipWith_map, List.zipWith_self]
    refine List.map_congr_left fun x hx => ?_
    simp [held, entries x hx]
  · rw [if_neg held] at relT ⊢
    rw [relT]
    congr 1
    simp only [treeTwinAppended, shifted, treeSimHeldShift]
    refine List.map_congr_left fun x _ => ?_
    rw [if_neg (fun h => held ⟨h.1, h.2.2⟩), add_zero]

/-- The saved shares of one operator after the collector layer `layer` with the result `z`, as
`layerBody` builds them. -/
def treeTwinLayerShares (circs : List Circuit) (layer : ℕ) (mode : ReshareMode)
    (p : List (C.Term → List Bit) × List (Tuple C)) (z : Shares C Bit) :
    List (C.Term → List Bit) × List (Tuple C) :=
  (appendLayer circs layer p.1 z,
    p.2 ++ [⟨layerX K circs layer p.1, layerY K circs layer p.1, z, (gatesAt circs layer).length, mode⟩])

/-- The honest local products of one layer, summed and taken as a difference of the two runs. -/
def treeTwinProductShift (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C) (circs : List Circuit)
    (layer : ℕ) (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)) : ℕ → Bit := fun g =>
  ∑ j ∈ Finset.univ.filter (· ∉ D.1),
    (mulRep K (ctx₁ j) (layerX K circs layer (p₁ j).1) (layerY K circs layer (p₁ j).1) g -
      mulRep K (ctx₂ j) (layerX K circs layer (p₂ j).1) (layerY K circs layer (p₂ j).1) g)

/-- A common length of the honest operators. -/
theorem treeTwin_common_length (D : C.Coalition) (f : C.Party → ℕ)
    (aligned : ∀ i j, i ∉ D.1 → j ∉ D.1 → f i = f j) : ∃ L, ∀ i, i ∉ D.1 → f i = L := by
  by_cases h : ∃ i, i ∉ D.1
  · obtain ⟨i, hi⟩ := h
    exact ⟨f i, fun j hj => aligned j i hj hi⟩
  · exact ⟨0, fun j hj => (h ⟨j, hj⟩).elim⟩

/-- One collector layer keeps `TreeTwinRunData`. The honest share lists are aligned, the two runs
record the same mode, and the results differ by the held shift of the honest local products. -/
theorem treeTwinRunData_layer (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (circs : List Circuit) (layer : ℕ) (mode₁ mode₂ : C.Party → ReshareMode)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)) (z₁ z₂ : C.Party → Shares C Bit)
    (data : TreeTwinRunData K D ctx₁ ctx₂ p₁ p₂)
    (wiresAligned : ∀ i j, i ∉ D.1 → j ∉ D.1 → (p₁ i).1.length = (p₁ j).1.length)
    (tuplesAligned : ∀ i j, i ∉ D.1 → j ∉ D.1 → (p₁ i).2.length = (p₁ j).2.length)
    (modes : ∀ i, i ∉ D.1 → mode₂ i = mode₁ i)
    (shifted : ∀ i, i ∉ D.1 → z₂ i = treeSimHeldShift D i (gatesAt circs layer).length
      (treeTwinProductShift K D ctx₁ ctx₂ circs layer p₁ p₂) (z₁ i)) :
    TreeTwinRunData K D ctx₁ ctx₂ (fun i => treeTwinLayerShares K circs layer (mode₁ i) (p₁ i) (z₁ i))
      (fun i => treeTwinLayerShares K circs layer (mode₂ i) (p₂ i) (z₂ i)) := by
  obtain ⟨lengths, sharings, tuples⟩ := data
  obtain ⟨L, hL⟩ := treeTwin_common_length D (fun i => (p₁ i).1.length) wiresAligned
  obtain ⟨N, hN⟩ := treeTwin_common_length D (fun i => (p₁ i).2.length) tuplesAligned
  choose differences hdifferences using sharings
  let inside : ℕ → List Bit := fun k => if k < L then differences k else []
  have insideRel : ∀ i, i ∉ D.1 → ∀ k w₁ w₂, (p₁ i).1[k]? = some w₁ → (p₂ i).1[k]? = some w₂ →
      TreeSimHistoryRel D i (inside k) w₁ w₂ := by
    intro i hi k w₁ w₂ h₁ h₂
    have hk : k < L := hL i hi ▸ (List.getElem?_eq_some_iff.1 h₁).1
    simp only [inside, if_pos hk]
    exact hdifferences k i hi w₁ w₂ h₁ h₂
  have insideOut : ∀ i, i ∉ D.1 → ∀ k, (p₁ i).1.length ≤ k → inside k = [] := by
    intro i hi k hk
    simp only [inside, if_neg (by rw [← hL i hi]; omega : ¬ k < L)]
  refine ⟨fun i hi => ?_, fun k => ⟨inside k ++ treeTwinAppended circs layer k
    (treeTwinProductShift K D ctx₁ ctx₂ circs layer p₁ p₂), fun i hi w₁ w₂ h₁ h₂ => ?_⟩, fun k => ?_⟩
  · simp [treeTwinLayerShares, treeTwin_appendLayer_length, (lengths i hi).1, (lengths i hi).2]
  · exact treeTwin_appendLayer_rel D i circs layer (p₁ i).1 (p₂ i).1 inside (z₁ i) (z₂ i) _
      (insideRel i hi) (shifted i hi) k w₁ w₂ h₁ h₂
  · have length₂ : ∀ j, j ∉ D.1 → (p₂ j).2.length = N := fun j hj => (lengths j hj).2.trans (hN j hj)
    rcases lt_trichotomy k N with hk | rfl | hk
    · have old₁ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₁ j) (p₁ j) (z₁ j)).2[k]? = (p₁ j).2[k]? :=
        fun j hj => List.getElem?_append_left (by rw [hN j hj]; exact hk)
      have old₂ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₂ j) (p₂ j) (z₂ j)).2[k]? = (p₂ j).2[k]? :=
        fun j hj => List.getElem?_append_left (by rw [length₂ j hj]; exact hk)
      obtain ⟨dx, dy, old⟩ := tuples k
      refine ⟨dx, dy, fun i hi t₁ t₂ h₁ h₂ => ?_⟩
      obtain ⟨count, mode, x, y, z⟩ := old i hi t₁ t₂ ((old₁ i hi).symm.trans h₁) ((old₂ i hi).symm.trans h₂)
      refine ⟨count, mode, x, y, ?_⟩
      rw [z]
      congr 1
      funext g
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [old₁ j (Finset.mem_filter.1 hj).2, old₂ j (Finset.mem_filter.1 hj).2]
    · have new₁ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₁ j) (p₁ j) (z₁ j)).2[k]? =
            some ⟨layerX K circs layer (p₁ j).1, layerY K circs layer (p₁ j).1, z₁ j,
              (gatesAt circs layer).length, mode₁ j⟩ := by
        intro j hj
        simp [treeTwinLayerShares, hN j hj]
      have new₂ : ∀ j, j ∉ D.1 →
          (treeTwinLayerShares K circs layer (mode₂ j) (p₂ j) (z₂ j)).2[k]? =
            some ⟨layerX K circs layer (p₂ j).1, layerY K circs layer (p₂ j).1, z₂ j,
              (gatesAt circs layer).length, mode₂ j⟩ := by
        intro j hj
        simp [treeTwinLayerShares, length₂ j hj]
      refine ⟨treeTwinLayerShift circs layer Prod.fst inside, treeTwinLayerShift circs layer Prod.snd inside,
        fun i hi t₁ t₂ h₁ h₂ => ?_⟩
      rw [new₁ i hi] at h₁
      rw [new₂ i hi] at h₂
      cases h₁
      cases h₂
      refine ⟨rfl, modes i hi, treeTwin_layer_shift D i circs layer Prod.fst K.publicTerm (p₁ i).1 (p₂ i).1
        inside (lengths i hi).1 (insideOut i hi) (insideRel i hi),
        treeTwin_layer_shift D i circs layer Prod.snd K.publicTerm (p₁ i).1 (p₂ i).1
        inside (lengths i hi).1 (insideOut i hi) (insideRel i hi), ?_⟩
      rw [shifted i hi]
      dsimp only
      congr 1
      funext g
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [new₁ j (Finset.mem_filter.1 hj).2, new₂ j (Finset.mem_filter.1 hj).2]
      rfl
    · refine ⟨0, 0, fun i hi t₁ t₂ h₁ h₂ => ?_⟩
      have none : (treeTwinLayerShares K circs layer (mode₁ i) (p₁ i) (z₁ i)).2[k]? = none :=
        List.getElem?_eq_none (by simp [treeTwinLayerShares, hN i hi]; omega)
      rw [none] at h₁
      cases h₁

/-- The links of a collector layer that `TreeTwinRunData` misses. The count and the reshared
values of the layer are those of the saved shares, the two runs record the same mode, and the
honest share lists are aligned. -/
def TreeTwinLayerLink (D : C.Coalition) (d : TreeSimCollectorData K D) (ctx₁ ctx₂ : C.Party → Context C)
    (gadgets₁ gadgets₂ : C.Party → RunGadgets C E RealSpec) (circs : List Circuit) (layer : ℕ)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)) : Prop :=
  d.count = (gatesAt circs layer).length ∧
  (∀ i, i ∉ D.1 → d.v₁ i = mulRep K (ctx₁ i) (layerX K circs layer (p₁ i).1) (layerY K circs layer (p₁ i).1)) ∧
  (∀ i, i ∉ D.1 → d.v₂ i = mulRep K (ctx₂ i) (layerX K circs layer (p₂ i).1) (layerY K circs layer (p₂ i).1)) ∧
  (∀ i, i ∉ D.1 → (gadgets₂ i).mode = (gadgets₁ i).mode) ∧
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (p₁ i).1.length = (p₁ j).1.length) ∧
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (p₁ i).2.length = (p₁ j).2.length)

/-- `TreeTwinLayerLink` at a layer schedule. -/
def TreeTwinScheduleLink (D : C.Coalition) {d : TreeSimCollectorData K D}
    (s : TreeStagesCollectorSchedule K D d) : Prop :=
  TreeTwinLayerLink K D d s.ctx₁ s.ctx₂ s.gadgets₁ s.gadgets₂ s.circs s.layer s.p₁ s.p₂

/-- `TreeTwinLayerLink` at the last collector layer. -/
def TreeTwinTailLink (D : C.Coalition) {d : TreeSimCollectorData K D}
    (tail : TreeStagesCollectorTail K D d) : Prop :=
  TreeTwinLayerLink K D d tail.ctx₁ tail.ctx₂ tail.gadgets₁ tail.gadgets₂ tail.circs tail.layer tail.p₁ tail.p₂

/-- The collector exits keep `TreeTwinRunData` at a linked layer. -/
theorem treeTwinRunData_exit (D : C.Coalition) (d : TreeSimCollectorData K D)
    (ctx₁ ctx₂ : C.Party → Context C) (gadgets₁ gadgets₂ : C.Party → RunGadgets C E RealSpec)
    (circs : List Circuit) (layer : ℕ) (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (data : TreeTwinRunData K D ctx₁ ctx₂ p₁ p₂)
    (link : TreeTwinLayerLink K D d ctx₁ ctx₂ gadgets₁ gadgets₂ circs layer p₁ p₂)
    (x₁ x₂ : C.Party → Shares C Bit × RunState C)
    (exits : ∀ i, i ∉ D.1 → (x₂ i).1 = treeSimHeldShift D i d.count
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g) (x₁ i).1) :
    TreeTwinRunData K D ctx₁ ctx₂
      (fun i => treeTwinLayerShares K circs layer (gadgets₁ i).mode (p₁ i) (x₁ i).1)
      (fun i => treeTwinLayerShares K circs layer (gadgets₂ i).mode (p₂ i) (x₂ i).1) := by
  obtain ⟨count, v₁, v₂, modes, wires, tuples⟩ := link
  refine treeTwinRunData_layer K D ctx₁ ctx₂ circs layer _ _ p₁ p₂ _ _ data wires tuples modes
    fun i hi => ?_
  rw [exits i hi, count]
  congr 1
  funext g
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Pi.sub_apply, Pi.sub_apply, v₁ j (Finset.mem_filter.1 hj).2, v₂ j (Finset.mem_filter.1 hj).2]

/-- `treeTwin_schedule_next` with `TreeTwinRunData` and `TreeTwinScheduleLink` kept. -/
theorem treeTwin_scheduleLinked_next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (nextLayer : ℕ) (remaining : List ℕ)
    (rest_eq : s.rest = nextLayer :: remaining) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (s.ρ + 1) initial) (sent sent' : C.Party → Mail C E)
    (data : TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂) (link : TreeTwinScheduleLink K D s) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeSimCollectorNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = s.ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt s.circs nextLayer).length ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesCollectorSchedule K D (n.data K rnd₁ rnd₂ masks),
          successor.ρ = n.ρ ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining ∧
          treeTwinScheduleCode K D successor = treeTwinScheduleCode K D s ∧
          TreeTwinRunData K D successor.ctx₁ successor.ctx₂ successor.p₁ successor.p₂ ∧
          TreeTwinScheduleLink K D successor := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  let nextP₁ := fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₁ i).mode (s.p₁ i) (x₁ i).1
  let nextP₂ := fun i => treeTwinLayerShares K s.circs s.layer (s.gadgets₂ i).mode (s.p₂ i) (x₂ i).1
  refine ⟨{
    T₀ := d.T₀, lacked := d.lacked, ctx₁ := s.ctx₁, ctx₂ := s.ctx₂
    self₁ := s.self₁, self₂ := s.self₂, keys := s.keys
    ρ := s.ρ + 1, idx := 0, count := (gatesAt s.circs nextLayer).length
    v₁ := fun i => mulRep K (s.ctx₁ i) (layerX K s.circs nextLayer (nextP₁ i).1) (layerY K s.circs nextLayer (nextP₁ i).1)
    v₂ := fun i => mulRep K (s.ctx₂ i) (layerX K s.circs nextLayer (nextP₂ i).1) (layerY K s.circs nextLayer (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (s.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (s.labels i hi)))
    next₁ := fun i => treeStagesAfterLayer K (s.gadgets₁ i) s.circs nextLayer remaining (nextP₁ i) (s.finish₁ i)
    next₂ := fun i => treeStagesAfterLayer K (s.gadgets₂ i) s.circs nextLayer remaining (nextP₂ i) (s.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := s.visible, futureZero := s.zero, futureEmpty := fresh
  }, rfl, rfl, rfl, ?_⟩
  · intro i hi _
    rw [s.program₁ i hi, rest_eq]
    exact treeStages_layers_collector K (s.ctx₁ i) (s.gadgets₁ i) (s.mult₁ i hi)
      s.circs nextLayer remaining (nextP₁ i) (x₁ i).2 (s.finish₁ i)
  · intro i hi _
    rw [s.program₂ i hi, rest_eq]
    exact treeStages_layers_collector K (s.ctx₂ i) (s.gadgets₂ i) (s.mult₂ i hi)
      s.circs nextLayer remaining (nextP₂ i) (x₂ i).2 (s.finish₂ i)
  · intro rnd₁ rnd₂ masks zeroNext
    refine ⟨{
      ctx₁ := s.ctx₁, ctx₂ := s.ctx₂, self₁ := s.self₁, self₂ := s.self₂, keys := s.keys
      gadgets₁ := s.gadgets₁, gadgets₂ := s.gadgets₂, mult₁ := s.mult₁, mult₂ := s.mult₂
      circs := s.circs, layer := nextLayer, rest := remaining
      p₁ := nextP₁, p₂ := nextP₂, finish₁ := s.finish₁, finish₂ := s.finish₂
      program₁ := by intros; rfl
      program₂ := by intros; rfl
      ρ := s.ρ + 1
      labels := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (s.labels i hi))
      visible := ?_, zero := zeroNext
      rerand₁ := s.rerand₁, rerand₂ := s.rerand₂, verify₁ := s.verify₁, verify₂ := s.verify₂
    }, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx
      change (d.δ + treeSimCollectorShift K D d.T₀ (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _) x = 0
      simp only [Pi.add_apply, s.visible x hx, treeSimCollectorShift,
        treeSim_blockShift_visible D (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _ _ x hx, add_zero]
    · exact treeTwinRunData_exit K D d s.ctx₁ s.ctx₂ s.gadgets₁ s.gadgets₂ s.circs s.layer s.p₁ s.p₂
        data link x₁ x₂ fun i hi => (exits i hi).1.1
    · obtain ⟨_, _, _, modes, wires, tuples⟩ := link
      refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, modes, fun i j hi hj => ?_, fun i j hi hj => ?_⟩
      · simpa [nextP₁, treeTwinLayerShares, treeTwin_appendLayer_length] using wires i j hi hj
      · simpa [nextP₁, treeTwinLayerShares] using tuples i j hi hj

/-- The links of a Rerand recipe that `TreeTwinRunData` misses. The reshared values are the owner
sums of the saved outputs, the two runs record the same mode, and the honest share lists are
aligned. -/
def TreeTwinRerandLink (D : C.Coalition) {d : TreeSimPeerData K D} (rest : TreeStagesRerandTail K D d) :
    Prop :=
  (∀ i, i ∉ D.1 → d.v₁ i = ownerSum K (d.ctx₁ i) (outputShares K rest.circs (rest.p₁ i).1)) ∧
  (∀ i, i ∉ D.1 → d.v₂ i = ownerSum K (d.ctx₂ i) (outputShares K rest.circs (rest.p₂ i).1)) ∧
  (∀ i, i ∉ D.1 → (rest.gadgets₂ i).mode = (rest.gadgets₁ i).mode) ∧
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (rest.p₁ i).1.length = (rest.p₁ j).1.length) ∧
  (∀ i j, i ∉ D.1 → j ∉ D.1 → (rest.p₁ i).2.length = (rest.p₁ j).2.length)

/-- `treeTwin_tail_next` with `TreeTwinRunData` and `TreeTwinRerandLink` kept. -/
theorem treeTwin_tailLinked_next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (tail : TreeStagesCollectorTail K D d) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (tail.ρ + 1) initial) (sent sent' : C.Party → Mail C E)
    (data : TreeTwinRunData K D tail.ctx₁ tail.ctx₂ tail.p₁ tail.p₂) (link : TreeTwinTailLink K D tail) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeStagesPeerNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = tail.ρ + 1 ∧ n.count = (outputsOf tail.circs).length ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        ∃ rest : TreeStagesRerandTail K D (n.data K rnd₁ rnd₂ masks), rest.ρ = n.ρ ∧ rest.circs = tail.circs ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail ∧
          TreeTwinRunData K D (n.data K rnd₁ rnd₂ masks).ctx₁ (n.data K rnd₁ rnd₂ masks).ctx₂ rest.p₁ rest.p₂ ∧
          TreeTwinRerandLink K D rest := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let nextP₁ := fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₁ i).mode (tail.p₁ i) (x₁ i).1
  let nextP₂ := fun i => treeTwinLayerShares K tail.circs tail.layer (tail.gadgets₂ i).mode (tail.p₂ i) (x₂ i).1
  refine ⟨{
    T₀ := T₀, pivotParty := pivotParty, pivot := pivot
    ctx₁ := tail.ctx₁, ctx₂ := tail.ctx₂, self₁ := tail.self₁, self₂ := tail.self₂, keys := tail.keys
    ρ := tail.ρ + 1, count := (outputsOf tail.circs).length
    v₁ := fun i => ownerSum K (tail.ctx₁ i) (outputShares K tail.circs (nextP₁ i).1)
    v₂ := fun i => ownerSum K (tail.ctx₂ i) (outputShares K tail.circs (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (tail.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (tail.labels i hi)))
    next₁ := fun i => treeStagesAfterRerand K (tail.gadgets₁ i) tail.circs (nextP₁ i) (tail.finish₁ i)
    next₂ := fun i => treeStagesAfterRerand K (tail.gadgets₂ i) tail.circs (nextP₂ i) (tail.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := tail.visible, futureZero := tail.zero, futureEmpty := fresh
  }, rfl, rfl, ?_⟩
  · intro i hi _
    rw [tail.program₁ i hi]
    exact treeStages_layers_rerand K (tail.ctx₁ i) (tail.gadgets₁ i) (tail.rerand₁ i hi)
      tail.circs (nextP₁ i) (x₁ i).2 (tail.finish₁ i)
  · intro i hi _
    rw [tail.program₂ i hi]
    exact treeStages_layers_rerand K (tail.ctx₂ i) (tail.gadgets₂ i) (tail.rerand₂ i hi)
      tail.circs (nextP₂ i) (x₂ i).2 (tail.finish₂ i)
  · intro rnd₁ rnd₂ masks
    refine ⟨⟨tail.gadgets₁, tail.gadgets₂, tail.circs, rfl, nextP₁, nextP₂, tail.finish₁, tail.finish₂,
      (by intros; rfl), (by intros; rfl), tail.ρ + 1,
      (fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (tail.labels i hi))),
      tail.keys, tail.verify₁, tail.verify₂, ?_⟩, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp only [TreeStagesPeerNext.data, TreeStagesPeerNext.δ, Pi.add_apply, tail.visible x hx,
        treeSimPeerShift, treeSim_blockShift_visible D (tail.ρ + 1) 0 _ _ _ x hx, add_zero]
    · exact treeTwinRunData_exit K D d tail.ctx₁ tail.ctx₂ tail.gadgets₁ tail.gadgets₂ tail.circs tail.layer
        tail.p₁ tail.p₂ data link x₁ x₂ fun i hi => (exits i hi).1.1
    · obtain ⟨_, _, _, modes, wires, tuples⟩ := link
      refine ⟨fun _ _ => rfl, fun _ _ => rfl, modes, fun i j hi hj => ?_, fun i j hi hj => ?_⟩
      · simpa [nextP₁, treeTwinLayerShares, treeTwin_appendLayer_length] using wires i j hi hj
      · simpa [nextP₁, treeTwinLayerShares] using tuples i j hi hj

/-- `treeTwin_schedule_round` with `TreeTwinRunData` and `TreeTwinScheduleLink` kept. -/
theorem treeTwin_scheduleLinked_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d)
    (nextLayer : ℕ) (remaining : List ℕ) (rest_eq : s.rest = nextLayer :: remaining)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2)
    (data : TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂) (link : TreeTwinScheduleLink K D s) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimCollectorData K D) (successor : TreeStagesCollectorSchedule K D next)
          (live : C.Party → Bool),
          successor.ρ = s.ρ + 1 ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining ∧
          treeTwinScheduleCode K D successor = treeTwinScheduleCode K D s ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (successor.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (successor.ρ + 1) z.2.2 ∧
          TreeTwinRunData K D successor.ctx₁ successor.ctx₂ successor.p₁ successor.p₂ ∧
          TreeTwinScheduleLink K D successor ∧
          u.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₂ next.v₂ next.st₂ next.k₂) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, _, after⟩ := treeTwin_scheduleLinked_next K D d s nextLayer remaining rest_eq a.1.2 fresh sent u.1.2 data link
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D A u.1.1 d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨_, _, empty₁, empty₂, zero, rnd₁, rnd₂, masks, steps₁, steps₂, boundary⟩ := h'
  obtain ⟨successor, nextLabel, info⟩ := after rnd₁ rnd₂ masks zero
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, successor, n.live, nextLabel.trans label,
    info.1, info.2.1, info.2.2.1, info.2.2.2.1, boundary.2.1, ?_, ?_, info.2.2.2.2.1,
    info.2.2.2.2.2, steps₁, steps₂⟩
  · simpa only [nextLabel] using empty₁
  · simpa only [nextLabel] using empty₂

/-- `treeTwin_tail_round` with `TreeTwinRunData` and `TreeTwinRerandLink` kept. -/
theorem treeTwin_tailLinked_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2)
    (data : TreeTwinRunData K D tail.ctx₁ tail.ctx₂ tail.p₁ tail.p₂) (link : TreeTwinTailLink K D tail) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
          rest.ρ = tail.ρ + 1 ∧ rest.circs = tail.circs ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (rest.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (rest.ρ + 1) z.2.2 ∧
          TreeSimFutureZero (rest.ρ + 1) next.δ ∧
          TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧ TreeTwinRerandLink K D rest ∧
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂ ∧
          treeTwinRerandCode K D rest = treeTwinTailCode K D tail) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, after⟩ := treeTwin_tailLinked_next K D d tail a.1.2 fresh sent u.1.2 data link
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨caches, empty₁, empty₂, zero, rnd₁, rnd₂, masks, next₁, next₂⟩ := h'
  obtain ⟨rest, restLabel, restCircs, restCode, restData, restLink⟩ := after rnd₁ rnd₂ masks
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, rest, n.live, restLabel.trans label, restCircs, caches, ?_, ?_, ?_, restData,
    restLink, next₁, next₂, restCode⟩
  · simpa only [restLabel] using empty₁
  · simpa only [restLabel] using empty₂
  · simpa only [restLabel, TreeStagesPeerNext.data] using zero

section Stages

variable {A : Adversary C E (Keys C) PEmpty PEmpty}

/-- `TreeTwinDataCollectorStage` with `TreeTwinScheduleLink`. -/
def TreeTwinLinkedCollectorStage (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ d : TreeSimCollectorData K D, ∃ s : TreeStagesCollectorSchedule K D d,
    Allowed (treeTwinScheduleCode K D s) ∧ δ = d.δ ∧ TreeSimFutureEmpty (s.ρ + 1) a.2.1.2 ∧
    TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂ ∧ TreeTwinScheduleLink K D s ∧
    ((∃ live, a.1.2 = treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        b.1.2 = treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∨
      ∃ sent, a.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent ∧
        b.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)

/-- `TreeTwinDataRerandEntry` with `TreeTwinRerandLink`. -/
def TreeTwinLinkedRerandEntry (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
    Allowed (treeTwinRerandCode K D rest) ∧ δ = next.δ ∧ TreeSimFutureEmpty (rest.ρ + 1) a.2.1.2 ∧
    TreeSimFutureEmpty (rest.ρ + 1) b.2.2 ∧ TreeSimFutureZero (rest.ρ + 1) next.δ ∧
    TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧ TreeTwinRerandLink K D rest ∧
    a.1.2 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
    b.1.2 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂

end Stages

/-- One round from the linked collector stage, with no hypothesis. It is
`treeTwin_dataCollector_round` with the linked stages, which are kinds of the stage relation. -/
theorem treeTwin_linkedCollector_round (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Allowed Other : TreeTwinCode C E → Prop)
    (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop))
    (collector : TreeTwinLinkedCollectorStage K D Allowed ∈ kinds)
    (rerand : TreeTwinLinkedRerandEntry K D Allowed ∈ kinds)
    (n : ℕ) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (state : a.1.1 = b.1.1) (related : TreeSimStreamRel δ a.2 b.2)
    (stage : TreeTwinLinkedCollectorStage K D Allowed δ a b) :
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => ∃ δ', treeTwinReq D (treeTwinDataStage K D Other kinds) n δ'
      ((v.1.1, v.1.2.1), v.2) ((w.1.1, w.1.2.1), w.2)) := by
  obtain ⟨d, s, allowed, rfl, fresh, data, link, ⟨live, h₁, h₂⟩ | ⟨sent, h₁, h₂⟩⟩ := stage
  · have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
    simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    rw [h₁, h₂, ← state]
    by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
    · apply relTriple_post_mono (treeSim_collector_partial_mixed prims K D A a.1.1 live stopped d.δ
        d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a.2 b.2 related)
      rintro u z ⟨hs, -, hu, hz, hc, -, -⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i _ => Or.inl
        ⟨congrFun hu i, congrFun hz i⟩)
      exact ⟨d.δ, hc, hs, done, flags, Or.inl ⟨hu, hz⟩⟩
    · have all : ∀ j, j ∉ D.1 → live j = true := fun j hj => by
        by_contra h
        exact stopped ⟨j, hj, h⟩
      rw [treeTwin_collectorPartial_live K D live all, treeTwin_collectorPartial_live K D live all]
      apply relTriple_post_mono (treeSim_collector_first_mixed prims K D A a.1.1 d.δ
        d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a.2 b.2 related)
      rintro u z ⟨hs, -, hu, hz, hc, hl, -⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_collectorAfterFirst K D _ _ _ _ _ _ _ _ _ _ i hi)
      refine ⟨d.δ, hc, hs, done, flags, Or.inr (Or.inr ⟨_, collector,
        d, s, allowed, rfl, ?_, data, link, Or.inr ⟨u.1.2.2, hu, hz⟩⟩)⟩
      change TreeSimFutureEmpty (s.ρ + 1) u.2.1.2
      rw [hl]
      exact fresh
  · rw [h₁, h₂, ← state]
    cases hrest : s.rest with
    | cons nextLayer remaining =>
      apply relTriple_post_mono (treeTwin_scheduleLinked_round prims K D A a.1.1 d s nextLayer remaining
        hrest sent a.2 b.2 related fresh data link)
      rintro u z ⟨hs, -, next, successor, live, -, -, -, -, code, hc, f₁, -, data', link', hu, hz⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_collectorPartial K D _ _ _ _ _ _ _ _ _ _ i hi)
      exact ⟨next.δ, hc, hs, done, flags, Or.inr (Or.inr ⟨_, collector,
        next, successor, code ▸ allowed, rfl, f₁, data', link', Or.inl ⟨live, hu, hz⟩⟩)⟩
    | nil =>
      have tailLink : TreeTwinTailLink K D (s.last K D d hrest) := link
      apply relTriple_post_mono (treeTwin_tailLinked_round prims K D A a.1.1 d (s.last K D d hrest) sent
        a.2 b.2 related fresh data tailLink)
      rintro u z ⟨hs, -, next, rest, live, -, -, hc, f₁, f₂, zero, data', link', hu, hz, code⟩
      obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 z.1.2.1 (fun i hi => by
        rw [hu, hz]
        exact treeTwin_sameKind_peerPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
      exact ⟨next.δ, hc, hs, done, flags, Or.inr (Or.inr ⟨_, rerand,
        next, rest, live, code ▸ allowed, rfl, f₁, f₂, zero, data', link', hu, hz⟩)⟩

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Allowed Other : TreeTwinCode C E → Prop)
  (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop))

/-- The field `next` at the linked collector kind. -/
theorem treeTwinKindNext_linkedCollector (collector : TreeTwinLinkedCollectorStage K D Allowed ∈ kinds)
    (rerand : TreeTwinLinkedRerandEntry K D Allowed ∈ kinds) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Other kinds
      (TreeTwinLinkedCollectorStage K D Allowed) := by
  intro n δ swaps a b _ _ _ _ _ req stage
  obtain ⟨related, state, _, _, _⟩ := req
  apply relTriple_post_mono (treeTwin_linkedCollector_round prims K D A Allowed Other kinds collector
    rerand (n + 1) δ (a.1, treeStagesTwin swaps a.2) b state related stage)
  rintro v w ⟨δ', req'⟩
  exact Or.inr ⟨[], δ', fun x hx => by simp at hx, req'⟩

/-- The field `next` of the stage relation with no data collector stage, from the field at each
kind. -/
theorem treeTwinNext3_of_kinds
    (next : ∀ Kind ∈ kinds, TreeTwinKindNext prims K circuits settings top tree D A parameter seeds
      pairs z p r (fun _ => False) kinds Kind) :
    TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinDataStage K D (fun _ => False) kinds)) := by
  intro n δ swaps a b reach bound good active salts req
  obtain ⟨related, state, _, _, stage⟩ := req
  rcases stage with done | collector | ⟨Kind, mem, rest⟩
  · exact (active fun i _ => by rw [done.1]; trivial).elim
  · obtain ⟨_, _, allowed, _⟩ := collector
    exact allowed.elim
  · exact next Kind mem n δ swaps a b reach bound good active salts
      ⟨related, state, ‹_›, ‹_›, Or.inr (Or.inr ⟨Kind, mem, rest⟩)⟩ rest

end Fields

theorem treeTwin_sameKind_coinPartial {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec α) (i : C.Party) (hi : i ∉ D.1) :
    TreeTwinSameKind (treeSimCoinPartial K D live count rnd st₁ k₁ i)
      (treeSimCoinPartial K D live count rnd st₂ k₂ i) := by
  by_cases hl : live i = true
  · exact Or.inr ⟨_, _, _, _, by
      simp only [treeSimCoinPartial, hl, if_true, treeSimCoinWaiting, hi, if_false, treeSimCoinStep]; rfl, by
      simp only [treeSimCoinPartial, hl, if_true, treeSimCoinWaiting, hi, if_false, treeSimCoinStep]; rfl⟩
  · exact Or.inl ⟨by simp [treeSimCoinPartial, hl], by simp [treeSimCoinPartial, hl]⟩

/-- The allowed code has circuits with outputs, so the check covers at least one tuple bit. -/
def TreeTwinAllowedOutputs (Allowed : TreeTwinCode C E → Prop) : Prop :=
  ∀ code, Allowed code → (outputsOf code.2.2.2.2.1).length ≠ 0

section Stages

variable {A : Adversary C E (Keys C) PEmpty PEmpty}

/-- The first check Coin after the Rerand round, as `TreeStagesRerandTail.coin_boundary_round`
leaves it, with the saved shares and their links. -/
def TreeTwinRerandCoinStage (D : C.Coalition) (Allowed : TreeTwinCode C E → Prop)
    (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (rnd : C.Party → PrssOutput C E),
    Allowed (treeTwinRerandCode K D rest) ∧ δ = next.δ ∧
    TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧ TreeTwinRerandLink K D rest ∧
    TreeSimFutureZero (rest.ρ + 2) next.δ ∧ TreeSimFutureEmpty (rest.ρ + 2) a.2.1.2 ∧
    TreeSimFutureEmpty (rest.ρ + 2) b.2.2 ∧
    a.1.2 = treeSimCoinPartial K D
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).live
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).count rnd
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).st₁
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).next₁ ∧
    b.1.2 = treeSimCoinPartial K D
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).live
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).count rnd
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).st₂
      (rest.coinNext K D next rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent).next₂

end Stages

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Allowed Other : TreeTwinCode C E → Prop)
  (kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop))

/-- The field `next` at the linked Rerand entry. The Rerand round stops every operator or reaches
the first check Coin. -/
theorem treeTwinKindNext_linkedRerand (outputs : TreeTwinAllowedOutputs Allowed)
    (coin : TreeTwinRerandCoinStage K D Allowed ∈ kinds) :
    TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r Other kinds
      (TreeTwinLinkedRerandEntry K D Allowed) := by
  intro n δ swaps a b _ _ _ _ _ req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨next, rest, live, allowed, rfl, f₁, _, zero, data, link, h₁, h₂⟩ := stage
  have nonzero : (outputsOf rest.circs).length ≠ 0 := outputs _ allowed
  have nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0 :=
    fun _ _ => by omega
  have nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0 :=
    fun _ _ => by omega
  change RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run
    (treeStagesTwin swaps a.2)) _ _
  rw [h₁, h₂, ← state]
  apply relTriple_post_mono (rest.coin_boundary_round prims K D A next rest.keys rest.verify₁ rest.verify₂
    nonzero₁ nonzero₂ rest.visible zero live a.1.1 _ b.2 related f₁)
  rintro u w ⟨hs, -, hc, zero', e₁, e₂, ⟨hu, hz⟩ | ⟨sent, rnd, -, -, hu, hz⟩⟩
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1 (fun i _ => Or.inl
      ⟨congrFun hu i, congrFun hz i⟩)
    exact Or.inr ⟨[], next.δ, fun x hx => by simp at hx, hc, hs, done, flags, Or.inl ⟨hu, hz⟩⟩
  · obtain ⟨done, flags⟩ := treeTwin_flags_of_sameKind D u.1.2.1 w.1.2.1 (fun i hi => by
      rw [hu, hz]
      exact treeTwin_sameKind_coinPartial K D _ _ _ _ _ _ _ i hi)
    exact Or.inr ⟨[], next.δ, fun x hx => by simp at hx, hc, hs, done, flags, Or.inr (Or.inr ⟨_, coin,
      next, rest, nonzero₁, nonzero₂, sent, rnd, allowed, rfl, data, link, zero', e₁, e₂, hu, hz⟩)⟩

end Fields

/-- The kinds of the stage relation. The linked collector stage, the linked Rerand entry and the
first check Coin come first, and the other kinds follow. -/
abbrev treeTwinLinkedKinds {A : Adversary C E (Keys C) PEmpty PEmpty} (D : C.Coalition)
    (Allowed : TreeTwinCode C E → Prop)
    (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)) :
    List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop) :=
  TreeTwinLinkedCollectorStage K D Allowed :: TreeTwinLinkedRerandEntry K D Allowed ::
    TreeTwinRerandCoinStage K D Allowed :: others

/-- `TreeTwinDataGoal` with the linked kinds first. The frozen data collector stage is empty. The
goal asks for allowed code with outputs, the field `entry`, and the field `next` at the first check
Coin and at each other kind. -/
def TreeTwinLinkedGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ (Allowed : TreeTwinCode C E → Prop)
      (others : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
        TreeSimConfig A (HashCache C × HiddenCache C) → Prop)),
    TreeTwinAllowedOutputs Allowed ∧
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
      (treeTwinReq D (treeTwinDataStage K D (fun _ => False) (treeTwinLinkedKinds K D Allowed others))) ∧
    ∀ Kind ∈ TreeTwinRerandCoinStage K D Allowed :: others,
      TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r (fun _ => False)
        (treeTwinLinkedKinds K D Allowed others) Kind

/-- `TreeTwinStageCoreGoal3` from `TreeTwinLinkedGoal`, with no hypothesis on the collector rounds
and on the Rerand round. -/
theorem treeTwinStageCoreGoal3_of_linked (goal : TreeTwinLinkedGoal prims K circuits settings) :
    TreeTwinStageCoreGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := goal hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Allowed, others, outputs, entry, next⟩ := hpadding r hr
  refine ⟨_, entry, treeTwinNext3_of_kinds prims K circuits settings top tree D A parameter seeds pairs
    z p r _ fun Kind mem => ?_⟩
  rcases List.mem_cons.1 mem with rfl | mem
  · exact treeTwinKindNext_linkedCollector prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed _ _ (by simp) (by simp)
  rcases List.mem_cons.1 mem with rfl | mem
  · exact treeTwinKindNext_linkedRerand prims K circuits settings top tree D A parameter seeds pairs z p r
      Allowed _ _ outputs (by simp)
  · exact next Kind mem

/-- `TreeSimStagesGoal3` from the lockstep goals and `TreeTwinLinkedGoal`. -/
theorem treeSimStagesGoal3_of_linked
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings)
    (goal : TreeTwinLinkedGoal prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_lockstep prims K circuits settings lockstep draws
    (treeTwinStageCoreGoal3_of_linked prims K circuits settings goal)

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_linkedCollector_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_linkedCollector_round

/-- info: 'ThresholdLeanXmssSecurity.treeTwinKindNext_linkedRerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinKindNext_linkedRerand

/-- info: 'ThresholdLeanXmssSecurity.treeTwinStageCoreGoal3_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinStageCoreGoal3_of_linked

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_linked

end ThresholdLeanXmssSecurity
