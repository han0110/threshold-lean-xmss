import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedEntry
import ThresholdLeanXmssSecurity.Proof.TreeTwinHiddenLayer

/-!
# Hidden-term entry to the saved first slice

The caller retains its actual Rerand source, tuple metadata, and histories.
Only input-affine x/y shifts range over all hidden terms; the reshared z and
claim shifts remain on the original lacked term. Slice shape coefficients
are common to all honest parties without a history-agreement premise.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinHiddenEntry
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinLocalSum TreeTwinHiddenData TreeTwinSavedEntry
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (top : TopTree) (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
  (openings : List (List (List Bit)))

-- Port of TreeTwinLater.checkCoinData and its exact program identities.
def checkCoinData (D : C.Coalition) (d : TreeSimPeerData K D)
    (rest : TreeStagesRerandTail K D d)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (data : HiddenRunData K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂) :
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
        simp only [treeStagesRerandTuples, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        rw [(TreeTwinHiddenLayer.counts_modes K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂ data i hi).1]
    tag := fun i => if i ∈ D.1 then 0 else (n.st₁ i).tag
    hashLabel := fun i => if i ∈ D.1 then 0 else (n.st₁ i).label
    label := n.label, st₁ := n.st₁, st₂ := n.st₂, lab₁ := n.lab₁, lab₂ := n.lab₂
    finish₁ := fun i => treeStagesAfterVerify (rest.gadgets₁ i) rest.circs (n.x₁ i).1 (rest.finish₁ i)
    finish₂ := fun i => treeStagesAfterVerify (rest.gadgets₂ i) rest.circs (n.x₂ i).1 (rest.finish₂ i) }

theorem checkCoinData_programs (D : C.Coalition) (d : TreeSimPeerData K D)
    (rest : TreeStagesRerandTail K D d)
    (nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (data : HiddenRunData K D d.ctx₁ d.ctx₂ rest.p₁ rest.p₂)
    (i : C.Party) (hi : i ∉ D.1) :
    let n := rest.coinNext K D d rest.keys rest.verify₁ rest.verify₂ nonzero₁ nonzero₂ sent
    let p := checkCoinData K D d rest nonzero₁ nonzero₂ sent data
    n.next₁ i = p.next₁ K D i ∧ n.next₂ i = p.next₂ K D i := by
  dsimp only
  constructor
  · simp only [checkCoinData, TreeTwinCheckCoinData.next₁, if_neg hi]
    rfl
  · have tag := treeTwin_peer_saved_tag K D d sent i hi
    have label := (treeStages_peer_recorded_label K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i).trans
      ((congrArg (· + 1) (d.states i hi).1).trans
        (treeStages_peer_recorded_label K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i).symm)
    simp only [checkCoinData, TreeTwinCheckCoinData.next₂, if_neg hi]
    change treeStagesCheckAfterCoin K _ _ _ _ _ = treeStagesCheckAfterCoin K _ _ _ _ _
    dsimp only [TreeStagesRerandTail.coinNext, treeStages_peer_coinNext]
    rw [tag, label]


-- Port of TreeTwinLinked2.Caller; only its saved-data field changes.
structure HiddenCaller where
  peer : TreeSimPeerData K D
  rest : TreeStagesRerandTail K D peer
  batch : BatchLink K circuits settings top tree D parameter openings (treeTwinRerandCode K D rest) peer.st₁
  data : HiddenRunData K D peer.ctx₁ peer.ctx₂ rest.p₁ rest.p₂
  link : TreeTwinRerandLink K D rest
  sent : C.Party → Mail C E
  nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0
  nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0

namespace HiddenCaller

def checkData (c : HiddenCaller K circuits settings top tree D parameter openings) : TreeTwinCheckCoinData K D :=
  TreeTwinHiddenEntry.checkCoinData K D c.peer c.rest c.nonzero₁ c.nonzero₂ c.sent c.data

def count₁ (c : HiddenCaller K circuits settings top tree D parameter openings) (i : C.Party) : ℕ :=
  (((c.checkData K circuits settings top tree D parameter openings).tuples₁ i).map (·.count)).sum

end HiddenCaller

/-- Common per-hidden-term x/y coefficients, with the original single-pivot claim. -/
def HiddenSliceShape (D : C.Coalition) (v₁ v₂ : C.Party → Shares C E × Shares C E × E) : Prop :=
  ∃ (dx dy : C.Term → ℕ → E) (e : E),
    (∀ i, i ∉ D.1 → ∀ T k, (v₂ i).1 T k = (v₁ i).1 T k +
      if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then dx T k else 0) ∧
    (∀ i, i ∉ D.1 → ∀ T k, (v₂ i).2.1 T k = (v₁ i).2.1 T k +
      if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then dy T k else 0) ∧
    (∀ i, i ∉ D.1 → (v₁ i).2.2 - (v₂ i).2.2 = lackedShare K D i e)


/-- Every honest return of this caller's actual preceding Rerand succeeded. -/
def RerandLive (c : HiddenCaller K circuits settings top tree D parameter openings) : Prop :=
  ∀ i, i ∉ D.1 → (c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂
    c.nonzero₁ c.nonzero₂ c.sent).live i = true

variable {K circuits settings top tree D parameter openings}

-- Port of TreeTwinSavedEntry.RerandLive.exit, with the same actual optional outputs.
theorem RerandLive.exit {c : HiddenCaller K circuits settings top tree D parameter openings}
    (h : RerandLive K circuits settings top tree D parameter openings c)
    (i : C.Party) (hi : i ∉ D.1) :
    let n := c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂
      c.nonzero₁ c.nonzero₂ c.sent
    treeSimPeerOutputs K D c.peer.ctx₁ c.peer.count c.peer.rnd₁ c.peer.v₁ c.peer.st₁ c.peer.k₁ c.sent i =
      some (n.x₁ i) ∧
    treeSimPeerOutputs K D c.peer.ctx₂ c.peer.count c.peer.rnd₂ c.peer.v₂ c.peer.st₂ c.peer.k₂ c.sent i =
      some (n.x₂ i) ∧ TreeSimPeerExitRel K D c.peer i (n.x₁ i) (n.x₂ i) := by
  dsimp only
  let n := c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂
    c.nonzero₁ c.nonzero₂ c.sent
  have left := n.shape₁ i
  have right := n.shape₂ i
  have hn : n.live i = true := h i hi
  simp only [if_neg hi, hn, ↓reduceIte] at left right
  refine ⟨left, right, ?_⟩
  have exits := c.peer.outputs K D c.sent i
  rw [left, right] at exits
  cases exits with
  | some rel => exact rel

-- Port of TreeTwinSavedEntry.counts_run₂ using the hidden-data metadata lemma.
theorem counts_run₂ (c : HiddenCaller K circuits settings top tree D parameter openings)
    (i : C.Party) (hi : i ∉ D.1) :
    ((c.checkData K circuits settings top tree D parameter openings).tuples₂ i).map (·.count) =
      ((c.checkData K circuits settings top tree D parameter openings).tuples₁ i).map (·.count) := by
  simp only [HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi,
    treeStagesRerandTuples, List.map_append, List.map_cons, List.map_nil]
  rw [(TreeTwinHiddenLayer.counts_modes K D c.peer.ctx₁ c.peer.ctx₂ c.rest.p₁ c.rest.p₂ c.data i hi).1]

theorem entryCounts_run₂ {c : HiddenCaller K circuits settings top tree D parameter openings}
    (h : EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁) :
    EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₂ := by
  obtain ⟨counts, hc⟩ := h
  exact ⟨counts, fun i hi => (counts_run₂ c i hi).trans (hc i hi)⟩

/-- Common tuple-position shifts; only x/y have term-indexed coefficients. -/
def HiddenTupleShifts (D : C.Coalition) (a b : C.Party → List (Tuple C)) : Prop :=
  ∀ k : ℕ, ∃ (dx dy : C.Term → ℕ → Bit) (dz : ℕ → Bit), ∀ i, i ∉ D.1 → ∀ t u : Tuple C,
    (a i)[k]? = some t → (b i)[k]? = some u →
    u.count = t.count ∧
    u.x = hiddenShift D i t.count dx t.x ∧
    u.y = hiddenShift D i t.count dy t.y ∧
    u.z = treeSimHeldShift D i t.count dz t.z

-- Port of treeTwin_layer_shift (TreeTwinKinds.lean), using outputsOf
-- in place of gatesAt. The affine constant cancels on both sides.
theorem output_shift (D : C.Coalition) (i : C.Party) (circs : List Circuit)
    (wires₁ wires₂ : List (C.Term → List Bit)) (differences : ℕ → C.Term → List Bit)
    (length : wires₂.length = wires₁.length)
    (outside : ∀ k, wires₁.length ≤ k → ∀ T, differences k T = [])
    (related : ∀ k w₁ w₂, wires₁[k]? = some w₁ → wires₂[k]? = some w₂ →
      HiddenWireRel D i (differences k) w₁ w₂) :
    outputShares K circs wires₂ = hiddenShift D i (outputsOf circs).length
      (fun T g => match (outputsOf circs)[g]? with
        | some (k, a) => (a.wires.map fun w => (differences k T).getD w 0).sum
        | none => 0) (outputShares K circs wires₁) := by
  funext T g
  simp only [hiddenShift, outputShares]
  cases hg : (outputsOf circs)[g]? with
  | none => simp
  | some gate =>
    obtain ⟨k, a⟩ := gate
    have glt : g < (outputsOf circs).length := (List.getElem?_eq_some_iff.1 hg).1
    simp only [Affine.share, glt, true_and]
    by_cases hk : k < wires₁.length
    · have h₁ : wires₁[k]? = some wires₁[k] := List.getElem?_eq_getElem hk
      have h₂ : wires₂[k]? = some wires₂[k] := List.getElem?_eq_getElem (length ▸ hk)
      have rel := related k _ _ h₁ h₂ T
      simp only [List.getD_eq_getElem?_getD, h₁, h₂, Option.getD_some]
      by_cases held : i ∈ C.holders T ∧ ¬ KnownTo D.1 T
      · rw [if_pos held] at rel
        rw [if_pos held, rel.2, treeTwin_zipWith_sum _ _ rel.1]
        abel
      · rw [if_neg held] at rel
        rw [if_neg held, rel, add_zero]
    · have h₁ : wires₁[k]? = none := List.getElem?_eq_none (by omega)
      have h₂ : wires₂[k]? = none := List.getElem?_eq_none (by omega)
      simp only [List.getD_eq_getElem?_getD, h₁, h₂, Option.getD_none, outside k (by omega) T]
      simp


theorem caller_output_shift (c : HiddenCaller K circuits settings top tree D parameter openings) :
    ∃ dx : C.Term → ℕ → Bit, ∀ i, i ∉ D.1 → outputShares K c.rest.circs (c.rest.p₂ i).1 =
      hiddenShift D i (outputsOf c.rest.circs).length dx
        (outputShares K c.rest.circs (c.rest.p₁ i).1) := by
  obtain ⟨L, hL⟩ := treeTwin_common_length D (fun i => (c.rest.p₁ i).1.length) c.link.2.2.2.1
  choose differences related using c.data.2.1
  let inside := fun k T => if k < L then differences k T else []
  refine ⟨fun T g => match (outputsOf c.rest.circs)[g]? with
    | some (k, a) => (a.wires.map fun w => (inside k T).getD w 0).sum
    | none => 0, ?_⟩
  intro i hi
  apply output_shift D i _ _ _ inside (c.data.1 i hi).1
  · intro k hk T
    simp only [inside, if_neg (by rw [← hL i hi]; omega : ¬ k < L)]
  · intro k w₁ w₂ h₁ h₂
    have hk : k < L := hL i hi ▸ (List.getElem?_eq_some_iff.1 h₁).1
    simp only [inside, if_pos hk]
    exact related k i hi _ _ h₁ h₂

-- Port of TreeTwinSavedEntry.caller_tupleShifts; the old and output z cases are unchanged.
theorem caller_tupleShifts (c : HiddenCaller K circuits settings top tree D parameter openings)
    (prior : RerandLive K circuits settings top tree D parameter openings c) :
    HiddenTupleShifts D (c.checkData K circuits settings top tree D parameter openings).tuples₁
      (c.checkData K circuits settings top tree D parameter openings).tuples₂ := by
  obtain ⟨N, hN⟩ := treeTwin_common_length D (fun i => (c.rest.p₁ i).2.length) c.link.2.2.2.2
  have hN₂ : ∀ i, i ∉ D.1 → (c.rest.p₂ i).2.length = N :=
    fun i hi => (c.data.1 i hi).2.trans (hN i hi)
  intro k
  rcases lt_trichotomy k N with hk | rfl | hk
  · obtain ⟨dx, dy, old⟩ := c.data.2.2 k
    refine ⟨dx, dy, fun g => ∑ j ∈ univ.filter (· ∉ D.1),
      (((c.rest.p₁ j).2[k]?.map fun t : Tuple C => mulRep K (c.peer.ctx₁ j) t.x t.y g).getD 0 -
       ((c.rest.p₂ j).2[k]?.map fun t : Tuple C => mulRep K (c.peer.ctx₂ j) t.x t.y g).getD 0), ?_⟩
    intro i hi t u ht hu
    simp only [HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi,
      treeStagesRerandTuples] at ht hu
    rw [List.getElem?_append_left (by rw [hN i hi]; exact hk)] at ht
    rw [List.getElem?_append_left (by rw [hN₂ i hi]; exact hk)] at hu
    have h := old i hi t u ht hu
    exact ⟨h.1, h.2.2⟩
  · obtain ⟨dx, hx⟩ := caller_output_shift c
    refine ⟨dx, 0, fun g => ∑ j ∈ univ.filter (· ∉ D.1), (c.peer.v₁ - c.peer.v₂) j g, ?_⟩
    intro i hi t u ht hu
    simp only [HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi,
      treeStagesRerandTuples] at ht hu
    rw [List.getElem?_append_right (by rw [hN i hi]), hN i hi, Nat.sub_self] at ht
    rw [List.getElem?_append_right (by rw [hN₂ i hi]), hN₂ i hi, Nat.sub_self] at hu
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hu
    subst t
    subst u
    refine ⟨rfl, hx i hi, ?_, ?_⟩
    · funext T g
      simp [hiddenShift]
    · have h := (prior.exit i hi).2.2.1
      simpa only [c.rest.count] using h
  · refine ⟨0, 0, 0, ?_⟩
    intro i hi t u ht hu
    have impossible : ((c.checkData K circuits settings top tree D parameter openings).tuples₁ i)[k]? = none := by
      apply List.getElem?_eq_none
      simp only [HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi,
        treeStagesRerandTuples, List.length_append, List.length_singleton, hN i hi]
      omega
    rw [impossible] at ht
    cases ht

/-- Flattening preserves a common shift because the count list is common. -/
theorem lifted_shift {a b : C.Party → List (Tuple C)} (counts : EntryCounts D a)
    (same : ∀ i, i ∉ D.1 → (b i).map (·.count) = (a i).map (·.count))
    (part : Tuple C → Shares C Bit)
    (shift : ∀ m : ℕ, ∃ d : C.Term → ℕ → Bit, ∀ i, i ∉ D.1 → ∀ t u : Tuple C,
      (a i)[m]? = some t → (b i)[m]? = some u → u.count = t.count ∧
        part u = hiddenShift D i t.count d (part t)) :
    ∃ d : C.Term → ℕ → E, ∀ i, i ∉ D.1 → ∀ T k,
      liftedPart (E := E) (b i) part T k = liftedPart (a i) part T k +
        if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then d T k else 0 := by
  obtain ⟨cs, hc⟩ := counts
  choose ds hd using shift
  refine ⟨fun T k => match flatPos cs k with | none => 0 | some (m, g) => algebraMap Bit E (ds m T g), ?_⟩
  intro i hi T k
  rw [liftedPart_flat, liftedPart_flat, same i hi, hc i hi]
  cases hp : flatPos cs k with
  | none => simp [hp]
  | some pos =>
    obtain ⟨m, g⟩ := pos
    obtain ⟨hm, hg⟩ := flatPos_spec cs k m g hp
    have ha : m < (a i).length := by
      have hlen : (a i).length = cs.length := by simpa using congrArg List.length (hc i hi)
      omega
    have hb : m < (b i).length := by
      have hlen : (b i).length = cs.length := by
        simpa using congrArg List.length ((same i hi).trans (hc i hi))
      omega
    have ea := List.getElem?_eq_getElem ha
    have eb := List.getElem?_eq_getElem hb
    have metadata : ((a i)[m]).count = cs.getD m 0 := by
      rw [← hc i hi, List.getD_eq_getElem?_getD, List.getElem?_map, ea]
      rfl
    have hx := (hd m i hi _ _ ea eb).2
    simp only [ea, eb, Option.map_some, Option.getD_some]
    rw [hx]
    simp only [hiddenShift, metadata, hg, true_and, map_add, hp]
    split_ifs <;> simp


theorem tupleShifts_lifted {a b : C.Party → List (Tuple C)}
    (counts : EntryCounts D a)
    (same : ∀ i, i ∉ D.1 → (b i).map (·.count) = (a i).map (·.count))
    (shifts : HiddenTupleShifts D a b) :
    ∃ (dx dy : C.Term → ℕ → E) (dz : ℕ → E), ∀ i, i ∉ D.1 → ∀ T k,
      (liftedPart (E := E) (b i) (·.x) T k = liftedPart (a i) (·.x) T k +
        if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then dx T k else 0) ∧
      (liftedPart (E := E) (b i) (·.y) T k = liftedPart (a i) (·.y) T k +
        if i ∈ C.holders T ∧ ¬ KnownTo D.1 T then dy T k else 0) ∧
      (liftedPart (E := E) (b i) (·.z) T k = liftedPart (a i) (·.z) T k +
        if i ∈ C.holders T ∧ lackedTerm D.1 = some T then dz k else 0) := by
  obtain ⟨dx, hx⟩ := lifted_shift (E := E) counts same (·.x) (by
    intro m
    obtain ⟨x, y, z, h⟩ := shifts m
    exact ⟨x, fun i hi t u ht hu => ⟨(h i hi t u ht hu).1, (h i hi t u ht hu).2.1⟩⟩)
  obtain ⟨dy, hy⟩ := lifted_shift (E := E) counts same (·.y) (by
    intro m
    obtain ⟨x, y, z, h⟩ := shifts m
    exact ⟨y, fun i hi t u ht hu => ⟨(h i hi t u ht hu).1, (h i hi t u ht hu).2.2.1⟩⟩)
  obtain ⟨dz, hz⟩ := TreeTwinSavedEntry.lifted_shift (E := E) counts same (·.z) (by
    intro m
    obtain ⟨x, y, z, h⟩ := shifts m
    exact ⟨z, fun i hi t u ht hu => ⟨(h i hi t u ht hu).1, (h i hi t u ht hu).2.2.2⟩⟩)
  exact ⟨dx, dy, dz, fun i hi T k => ⟨hx i hi T k, hy i hi T k, hz i hi T k⟩⟩

theorem sliceShape_entry (c : HiddenCaller K circuits settings top tree D parameter openings)
    (τ : List E) (prior : RerandLive K circuits settings top tree D parameter openings c)
    (counts : EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁) :
    HiddenSliceShape K D
      (fun i => treeStagesCheckInitial K (c.peer.ctx₁ i)
        ((c.checkData K circuits settings top tree D parameter openings).tuples₁ i) τ)
      (fun i => treeStagesCheckInitial K (c.peer.ctx₂ i)
        ((c.checkData K circuits settings top tree D parameter openings).tuples₂ i) τ) := by
  obtain ⟨dx, dy, dz, shifts⟩ := tupleShifts_lifted (E := E) counts (counts_run₂ c) (caller_tupleShifts c prior)
  obtain ⟨cs, hc⟩ := counts
  have hs₁ : ∀ i, i ∉ D.1 →
      (((c.checkData K circuits settings top tree D parameter openings).tuples₁ i).map (·.count)).sum = cs.sum :=
    fun i hi => congrArg List.sum (hc i hi)
  have hs₂ : ∀ i, i ∉ D.1 →
      (((c.checkData K circuits settings top tree D parameter openings).tuples₂ i).map (·.count)).sum = cs.sum :=
    fun i hi => congrArg List.sum ((counts_run₂ c i hi).trans (hc i hi))
  obtain ⟨e, he⟩ := claim_shift (K := K) τ cs.sum _ _ dz
    (fun i hi T k => (shifts i hi T k).2.2)
  refine ⟨fun T k => wordWeightOf K τ cs.sum k * dx T k, dy, e, ?_, ?_, ?_⟩
  · intro i hi T k
    dsimp only [treeStagesCheckInitial]
    rw [hs₁ i hi, hs₂ i hi, (shifts i hi T k).1]
    split_ifs <;> ring
  · intro i hi T k
    exact (shifts i hi T k).2.1
  · intro i hi
    dsimp only [treeStagesCheckInitial]
    rw [hs₁ i hi, hs₂ i hi, conv_self K _ i (c.peer.self₁ i hi), conv_self K _ i (c.peer.self₂ i hi)]
    exact he i hi


/-- Common tuple metadata transfers copy agreement through the common shifts. -/
theorem HiddenTupleShifts.agree {a b : C.Party → List (Tuple C)}
    (shifts : HiddenTupleShifts D a b) (counts : EntryCounts D a)
    (same : ∀ i, i ∉ D.1 → (b i).map (·.count) = (a i).map (·.count))
    (agree : EntryTuplesAgree D a) : EntryTuplesAgree D b := by
  obtain ⟨cs, hc⟩ := counts
  intro T i j hi hj hiT hjT m u v hu hv
  have hiLen : (b i).length = (a i).length := by simpa using congrArg List.length (same i hi)
  have hjLen : (b j).length = (a j).length := by simpa using congrArg List.length (same j hj)
  have hmi : m < (a i).length := hiLen ▸ (List.getElem?_eq_some_iff.1 hu).1
  have hmj : m < (a j).length := hjLen ▸ (List.getElem?_eq_some_iff.1 hv).1
  have ei := List.getElem?_eq_getElem hmi
  have ej := List.getElem?_eq_getElem hmj
  obtain ⟨dx, dy, dz, h⟩ := shifts m
  obtain ⟨ci, xi, yi, zi⟩ := h i hi _ u ei hu
  obtain ⟨cj, xj, yj, zj⟩ := h j hj _ v ej hv
  have old := agree T i j hi hj hiT hjT m _ _ ei ej
  have cnt : ((a i)[m]).count = ((a j)[m]).count := by
    have e := congrArg (fun xs : List ℕ => xs[m]?) ((hc i hi).trans (hc j hj).symm)
    simpa only [List.getElem?_map, ei, ej, Option.map_some, Option.some.injEq] using e
  refine ⟨?_, ?_, ?_⟩
  · funext g
    simp only [xi, xj, hiddenShift, hiT, hjT, true_and, old.1, cnt]
  · funext g
    simp only [yi, yj, hiddenShift, hiT, hjT, true_and, old.2.1, cnt]
  · funext g
    simp only [zi, zj, treeSimHeldShift, hiT, hjT, true_and, old.2.2, cnt]

theorem copies_known {a b : C.Party → List (Tuple C)} {cs : List ℕ}
    (ha : ∀ i, i ∉ D.1 → (a i).map (·.count) = cs)
    (hb : ∀ i, i ∉ D.1 → (b i).map (·.count) = cs)
    (shift : HiddenTupleShifts D a b) (m : ℕ) (hm : m < cs.length)
    (X Y Z X' Y' Z' : Shares C Bit) (left : Copies D a m X Y Z) (right : Copies D b m X' Y' Z') :
    ∀ T, KnownTo D.1 T → X T = X' T ∧ Y T = Y' T ∧ Z T = Z' T := by
  intro T known
  obtain ⟨i, held, hi⟩ := exists_honest_holder D T
  obtain ⟨t, ht, _⟩ := tuple_exists ha m hm i hi
  obtain ⟨u, hu, _⟩ := tuple_exists hb m hm i hi
  obtain ⟨dx, dy, dz, h⟩ := shift m
  have h := h i hi t u ht hu
  have l := left i hi t ht T held
  have r := right i hi u hu T held
  have hn : lackedTerm D.1 ≠ some T := fun eq => main_lacked_unknown D T eq known
  refine ⟨?_, ?_, ?_⟩
  · rw [← l.1, ← r.1, h.2.1]; funext g; simp [hiddenShift, known]
  · rw [← l.2.1, ← r.2.1, h.2.2.1]; funext g; simp [hiddenShift, known]
  · rw [← l.2.2, ← r.2.2, h.2.2.2]; funext g; simp [treeSimHeldShift, hn]

-- Port of TreeTwinSavedEntry.caller_tuple_residual, reusing its z and global-sum lemmas.
theorem caller_tuple_residual (c : HiddenCaller K circuits settings top tree D parameter openings)
    (prior : RerandLive K circuits settings top tree D parameter openings c)
    (cs : List ℕ)
    (ha : ∀ i, i ∉ D.1 → ((c.checkData K circuits settings top tree D parameter openings).tuples₁ i).map (·.count) = cs)
    (m : ℕ) (hm : m < cs.length) (g : ℕ) (hg : g < cs.getD m 0)
    (X Y Z X' Y' Z' : Shares C Bit)
    (left : Copies D (c.checkData K circuits settings top tree D parameter openings).tuples₁ m X Y Z)
    (right : Copies D (c.checkData K circuits settings top tree D parameter openings).tuples₂ m X' Y' Z') :
    shareValue Z g - shareValue Z' g =
      shareValue X g * shareValue Y g - shareValue X' g * shareValue Y' g := by
  let a := (c.checkData K circuits settings top tree D parameter openings).tuples₁
  let b := (c.checkData K circuits settings top tree D parameter openings).tuples₂
  have hb : ∀ i, i ∉ D.1 → (b i).map (·.count) = cs :=
    fun i hi => (counts_run₂ c i hi).trans (ha i hi)
  have known := copies_known ha hb (caller_tupleShifts c prior) m hm X Y Z X' Y' Z' left right
  obtain ⟨N, hN⟩ := treeTwin_common_length D (fun i => (c.rest.p₁ i).2.length) c.link.2.2.2.2
  have hN₂ : ∀ i, i ∉ D.1 → (c.rest.p₂ i).2.length = N :=
    fun i hi => (c.data.1 i hi).2.trans (hN i hi)
  have cslen : cs.length = N + 1 := by
    have hc := congrArg List.length (ha c.peer.pivotParty c.peer.pivot.honest)
    simpa only [HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg c.peer.pivot.honest,
      treeStagesRerandTuples, List.length_map, List.length_append, List.length_singleton,
      hN _ c.peer.pivot.honest] using hc.symm
  by_cases old : m < N
  · have ea : ∀ i, i ∉ D.1 → (a i)[m]? = (c.rest.p₁ i).2[m]? := by
      intro i hi
      simp only [a, HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi, treeStagesRerandTuples]
      exact List.getElem?_append_left (by rw [hN i hi]; exact old)
    have eb : ∀ i, i ∉ D.1 → (b i)[m]? = (c.rest.p₂ i).2[m]? := by
      intro i hi
      simp only [b, HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi, treeStagesRerandTuples]
      exact List.getElem?_append_left (by rw [hN₂ i hi]; exact old)
    obtain ⟨dx, dy, sh⟩ := c.data.2.2 m
    rw [copies_z_total ha hb m hm g hg X Y Z X' Y' Z' left right _
      (fun i hi t u ht hu => (sh i hi t u ((ea i hi).symm.trans ht)
        ((eb i hi).symm.trans hu)).2.2.2.2)]
    let vx := fun i => (((c.rest.p₁ i).2[m]?).map (·.x)).getD 0
    let vy := fun i => (((c.rest.p₁ i).2[m]?).map (·.y)).getD 0
    let vx' := fun i => (((c.rest.p₂ i).2[m]?).map (·.x)).getD 0
    let vy' := fun i => (((c.rest.p₂ i).2[m]?).map (·.y)).getD 0
    have asSum : (∑ i ∈ univ.filter (· ∉ D.1),
        ((((c.rest.p₁ i).2[m]?).map fun t => mulRep K (c.peer.ctx₁ i) t.x t.y g).getD 0 -
        (((c.rest.p₂ i).2[m]?).map fun t => mulRep K (c.peer.ctx₂ i) t.x t.y g).getD 0)) =
        ∑ i ∈ univ.filter (· ∉ D.1),
          (mulRep K (c.peer.ctx₁ i) (vx i) (vy i) g - mulRep K (c.peer.ctx₂ i) (vx' i) (vy' i) g) := by
      apply sum_congr rfl
      intro i hi
      have hi := (mem_filter.mp hi).2
      obtain ⟨t, ht, _⟩ := tuple_exists ha m hm i hi
      obtain ⟨u, hu, _⟩ := tuple_exists hb m hm i hi
      rw [ea i hi] at ht
      rw [eb i hi] at hu
      simp only [vx, vy, vx', vy', ht, hu, Option.map_some, Option.getD_some]
    rw [asSum]
    apply mulRep_honest_diff c.peer.ctx₁ c.peer.ctx₂ c.peer.self₁ c.peer.self₂ vx vy vx' vy' X Y X' Y' g
    · intro i hi T held
      obtain ⟨t, ht, _⟩ := tuple_exists ha m hm i hi
      obtain ⟨u, hu, _⟩ := tuple_exists hb m hm i hi
      have l := left i hi t ht T held
      have r := right i hi u hu T held
      rw [ea i hi] at ht
      rw [eb i hi] at hu
      simp only [vx, vy, vx', vy', ht, hu, Option.map_some, Option.getD_some]
      exact ⟨congrFun l.1 g, congrFun l.2.1 g, congrFun r.1 g, congrFun r.2.1 g⟩
    · exact fun T hk => ⟨(known T hk).1, (known T hk).2.1⟩
  · have em : m = N := by omega
    subst m
    let n := c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂
      c.nonzero₁ c.nonzero₂ c.sent
    have ea : ∀ i, i ∉ D.1 → (a i)[N]? = some
        ⟨outputShares K c.rest.circs (c.rest.p₁ i).1, one K, (n.x₁ i).1, (outputsOf c.rest.circs).length, .peer⟩ := by
      intro i hi
      simp only [a, HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi, treeStagesRerandTuples]
      rw [List.getElem?_append_right (by rw [hN i hi]), hN i hi, Nat.sub_self]
      rfl
    have eb : ∀ i, i ∉ D.1 → (b i)[N]? = some
        ⟨outputShares K c.rest.circs (c.rest.p₂ i).1, one K, (n.x₂ i).1, (outputsOf c.rest.circs).length, .peer⟩ := by
      intro i hi
      simp only [b, HiddenCaller.checkData, TreeTwinHiddenEntry.checkCoinData, if_neg hi, treeStagesRerandTuples]
      rw [List.getElem?_append_right (by rw [hN₂ i hi]), hN₂ i hi, Nat.sub_self]
      rfl
    have yOne : Y = one K ∧ Y' = one K := by
      constructor
      · funext T g
        obtain ⟨i, held, hi⟩ := exists_honest_holder D T
        exact (congrFun (left i hi _ (ea i hi) T held).2.1 g).symm
      · funext T g
        obtain ⟨i, held, hi⟩ := exists_honest_holder D T
        exact (congrFun (right i hi _ (eb i hi) T held).2.1 g).symm
    rw [yOne.1, yOne.2, shareValue_one, mul_one, mul_one]
    rw [copies_z_total ha hb N hm g hg X Y Z X' Y' Z' left right
      (fun g => ∑ j ∈ univ.filter (· ∉ D.1), (c.peer.v₁ - c.peer.v₂) j g) (by
        intro i hi t u ht hu
        rw [ea i hi] at ht
        rw [eb i hi] at hu
        cases ht
        cases hu
        simpa only [c.rest.count] using (prior.exit i hi).2.2.1)]
    have values : (∑ j ∈ univ.filter (· ∉ D.1), (c.peer.v₁ - c.peer.v₂) j g) =
        ∑ j ∈ univ.filter (· ∉ D.1),
          (ownerSum K (c.peer.ctx₁ j) (outputShares K c.rest.circs (c.rest.p₁ j).1) g -
           ownerSum K (c.peer.ctx₂ j) (outputShares K c.rest.circs (c.rest.p₂ j).1) g) := by
      apply sum_congr rfl
      intro j hj
      simp only [Pi.sub_apply, c.link.1 j (mem_filter.mp hj).2, c.link.2.1 j (mem_filter.mp hj).2]
    rw [values]
    apply ownerSum_honest_diff c.peer.ctx₁ c.peer.ctx₂ c.peer.self₁ c.peer.self₂ _ _ X X' g
    · intro i hi T held
      exact ⟨(left i hi _ (ea i hi) T held).1, (right i hi _ (eb i hi) T held).1⟩
    · exact fun T hk => (known T hk).1


-- Port of TreeTwinSavedEntry.sliceRel_entry using its unchanged initial_rel.
theorem sliceRel_entry [CharP E 2]
    (c : HiddenCaller K circuits settings top tree D parameter openings) (τ : List E)
    (_hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0)
    (total : ∀ i, i ∉ D.1 → c.count₁ K circuits settings top tree D parameter openings i = tupleCount c.rest.circs)
    (prior : RerandLive K circuits settings top tree D parameter openings c)
    (counts : EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁)
    (agree : EntryTuplesAgree D (c.checkData K circuits settings top tree D parameter openings).tuples₁) :
    let a := (c.checkData K circuits settings top tree D parameter openings).tuples₁
    let b := (c.checkData K circuits settings top tree D parameter openings).tuples₂
    SliceRel K D τ (tupleCount c.rest.circs) 0
      (fun i => (treeStagesCheckInitial K (c.peer.ctx₁ i) (a i) τ).1)
      (fun i => (treeStagesCheckInitial K (c.peer.ctx₁ i) (a i) τ).2.1)
      (fun i => (treeStagesCheckInitial K (c.peer.ctx₂ i) (b i) τ).1)
      (fun i => (treeStagesCheckInitial K (c.peer.ctx₂ i) (b i) τ).2.1)
      (fun i => (treeStagesCheckInitial K (c.peer.ctx₁ i) (a i) τ).2.2)
      (fun i => (treeStagesCheckInitial K (c.peer.ctx₂ i) (b i) τ).2.2) := by
  let a := (c.checkData K circuits settings top tree D parameter openings).tuples₁
  let b := (c.checkData K circuits settings top tree D parameter openings).tuples₂
  have shifts := caller_tupleShifts c prior
  have agree₂ := shifts.agree counts (counts_run₂ c) agree
  choose X Y Z left using (fun m => copies_exists counts agree m)
  choose X' Y' Z' right using (fun m => copies_exists (entryCounts_run₂ counts) agree₂ m)
  obtain ⟨cs, ha⟩ := counts
  have hb : ∀ i, i ∉ D.1 → (b i).map (·.count) = cs := fun i hi => (counts_run₂ c i hi).trans (ha i hi)
  apply initial_rel τ (tupleCount c.rest.circs) a b c.peer.ctx₁ c.peer.ctx₂ c.peer.self₁ c.peer.self₂
    (fun i hi => ⟨total i hi, (congrArg List.sum (counts_run₂ c i hi)).trans (total i hi)⟩)
    (flatShares cs X) (flatShares cs Y) (flatShares cs Z)
    (flatShares cs X') (flatShares cs Y') (flatShares cs Z')
  · intro i hi T held
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lifted_of_copies ha (·.x) X (fun m i hi t ht T held => (left m i hi t ht T held).1) i hi T held
    · exact lifted_of_copies ha (·.y) Y (fun m i hi t ht T held => (left m i hi t ht T held).2.1) i hi T held
    · exact lifted_of_copies ha (·.z) Z (fun m i hi t ht T held => (left m i hi t ht T held).2.2) i hi T held
    · exact lifted_of_copies hb (·.x) X' (fun m i hi t ht T held => (right m i hi t ht T held).1) i hi T held
    · exact lifted_of_copies hb (·.y) Y' (fun m i hi t ht T held => (right m i hi t ht T held).2.1) i hi T held
    · exact lifted_of_copies hb (·.z) Z' (fun m i hi t ht T held => (right m i hi t ht T held).2.2) i hi T held
  · intro T hk
    have all : ∀ k, flatShares (E := E) cs X T k = flatShares cs X' T k ∧
        flatShares (E := E) cs Y T k = flatShares cs Y' T k ∧
        flatShares (E := E) cs Z T k = flatShares cs Z' T k := by
      intro k
      cases hp : flatPos cs k with
      | none => simp [flatShares, hp]
      | some pos =>
        obtain ⟨m, g⟩ := pos
        have known := copies_known ha hb shifts m (flatPos_spec cs k m g hp).1
          (X m) (Y m) (Z m) (X' m) (Y' m) (Z' m) (left m) (right m) T hk
        simp [flatShares, hp, known.1, known.2.1, known.2.2]
    exact ⟨funext fun k => (all k).1, funext fun k => (all k).2.1, funext fun k => (all k).2.2⟩
  · intro k
    cases hp : flatPos cs k with
    | none => simp [flatShares, hp, shareValue]
    | some pos =>
      obtain ⟨m, g⟩ := pos
      obtain ⟨hm, hg⟩ := flatPos_spec cs k m g hp
      have residual := caller_tuple_residual c prior cs ha m hm g hg
        (X m) (Y m) (Z m) (X' m) (Y' m) (Z' m) (left m) (right m)
      simpa only [flatShares, hp, shareValue, ← map_sum, ← map_mul, ← map_sub] using congrArg (algebraMap Bit E) residual


/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.checkCoinData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkCoinData

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.checkCoinData_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkCoinData_programs

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.RerandLive.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RerandLive.exit

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.counts_run₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counts_run₂

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.entryCounts_run₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entryCounts_run₂

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.output_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms output_shift

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.caller_output_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms caller_output_shift

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.caller_tupleShifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms caller_tupleShifts

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.lifted_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifted_shift

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.tupleShifts_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tupleShifts_lifted

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.sliceShape_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceShape_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.HiddenTupleShifts.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HiddenTupleShifts.agree

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.copies_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copies_known

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.caller_tuple_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms caller_tuple_residual

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHiddenEntry.sliceRel_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceRel_entry

end ThresholdLeanXmssSecurity.TreeTwinHiddenEntry
