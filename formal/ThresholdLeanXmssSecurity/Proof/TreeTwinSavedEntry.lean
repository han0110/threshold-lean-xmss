import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedSchedule

/-!
# Entry to the saved first slice

The tuple metadata and successful preceding Rerand are explicit. Agreement
of the actual tuple copies follows from the caller's supplied entry link.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinSavedEntry

open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinLocalSum

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (top : TopTree) (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
  (openings : List (List (List Bit)))

/-- One per-tuple count list at every honest party. -/
def EntryCounts (D : C.Coalition) (tuples : C.Party → List (Tuple C)) : Prop :=
  ∃ counts : List ℕ, ∀ i, i ∉ D.1 → (tuples i).map (·.count) = counts

/-- Every honest return of the caller's preceding Rerand succeeded. -/
def RerandLive (c : Caller K circuits settings top tree D parameter openings) : Prop :=
  ∀ i, i ∉ D.1 → (c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂
    c.nonzero₁ c.nonzero₂ c.sent).live i = true

variable {K circuits settings top tree D parameter openings}

theorem RerandLive.exit {c : Caller K circuits settings top tree D parameter openings}
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

theorem counts_run₂ (c : Caller K circuits settings top tree D parameter openings)
    (i : C.Party) (hi : i ∉ D.1) :
    ((c.checkData K circuits settings top tree D parameter openings).tuples₂ i).map (·.count) =
      ((c.checkData K circuits settings top tree D parameter openings).tuples₁ i).map (·.count) := by
  simp only [Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi,
    treeStagesRerandTuples, List.map_append, List.map_cons, List.map_nil]
  rw [(treeTwinRunData_counts_modes K D c.peer.ctx₁ c.peer.ctx₂ c.rest.p₁ c.rest.p₂ c.data i hi).1]

theorem EntryCounts.run₂ {c : Caller K circuits settings top tree D parameter openings}
    (h : EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁) :
    EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₂ := by
  obtain ⟨counts, hc⟩ := h
  exact ⟨counts, fun i hi => (counts_run₂ c i hi).trans (hc i hi)⟩

theorem lifted_common {tuples : C.Party → List (Tuple C)}
    (h : EntryCounts D tuples) (agree : EntryTuplesAgree D tuples)
    (part : Tuple C → Shares C Bit) (hp : part = (·.x) ∨ part = (·.y) ∨ part = (·.z))
    (T : C.Term) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    liftedPart (E := E) (tuples i) part T = liftedPart (tuples j) part T := by
  obtain ⟨counts, hc⟩ := h
  apply liftedPart_congr_flat counts _ _ part T (hc i hi) (hc j hj)
  intro m g hm hg
  have li : (tuples i).length = counts.length := by simpa using congrArg List.length (hc i hi)
  have lj : (tuples j).length = counts.length := by simpa using congrArg List.length (hc j hj)
  have ei := List.getElem?_eq_getElem (show m < (tuples i).length by omega)
  have ej := List.getElem?_eq_getElem (show m < (tuples j).length by omega)
  have a := agree T i j hi hj hiT hjT m _ _ ei ej
  rw [ei, ej]
  rcases hp with rfl | rfl | rfl
  · simp only [Option.map_some, a.1]
  · simp only [Option.map_some, a.2.1]
  · simp only [Option.map_some, a.2.2]

/-- Common bit shifts, indexed by the actual tuple position. -/
def TupleShifts (D : C.Coalition) (a b : C.Party → List (Tuple C)) : Prop :=
  ∀ k : ℕ, ∃ dx dy dz : ℕ → Bit, ∀ i, i ∉ D.1 → ∀ t u : Tuple C,
    (a i)[k]? = some t → (b i)[k]? = some u →
    u.count = t.count ∧
    u.x = treeSimHeldShift D i t.count dx t.x ∧
    u.y = treeSimHeldShift D i t.count dy t.y ∧
    u.z = treeSimHeldShift D i t.count dz t.z

-- Port of treeTwin_layer_shift (TreeTwinKinds.lean), using outputsOf
-- in place of gatesAt. The affine constant cancels on both sides.
theorem output_shift (D : C.Coalition) (i : C.Party) (circs : List Circuit)
    (wires₁ wires₂ : List (C.Term → List Bit)) (differences : ℕ → List Bit)
    (length : wires₂.length = wires₁.length)
    (outside : ∀ k, wires₁.length ≤ k → differences k = [])
    (related : ∀ k w₁ w₂, wires₁[k]? = some w₁ → wires₂[k]? = some w₂ →
      TreeSimHistoryRel D i (differences k) w₁ w₂) :
    outputShares K circs wires₂ = treeSimHeldShift D i (outputsOf circs).length
      (fun g => match (outputsOf circs)[g]? with
        | some (k, a) => (a.wires.map fun w => (differences k).getD w 0).sum
        | none => 0) (outputShares K circs wires₁) := by
  funext T g
  simp only [treeSimHeldShift, outputShares]
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


theorem caller_output_shift (c : Caller K circuits settings top tree D parameter openings) :
    ∃ dx : ℕ → Bit, ∀ i, i ∉ D.1 → outputShares K c.rest.circs (c.rest.p₂ i).1 =
      treeSimHeldShift D i (outputsOf c.rest.circs).length dx
        (outputShares K c.rest.circs (c.rest.p₁ i).1) := by
  obtain ⟨L, hL⟩ := treeTwin_common_length D (fun i => (c.rest.p₁ i).1.length) c.link.2.2.2.1
  choose differences related using c.data.2.1
  let inside := fun k => if k < L then differences k else []
  refine ⟨fun g => match (outputsOf c.rest.circs)[g]? with
    | some (k, a) => (a.wires.map fun w => (inside k).getD w 0).sum
    | none => 0, ?_⟩
  intro i hi
  apply output_shift D i _ _ _ inside (c.data.1 i hi).1
  · intro k hk
    simp only [inside, if_neg (by rw [← hL i hi]; omega : ¬ k < L)]
  · intro k w₁ w₂ h₁ h₂
    have hk : k < L := hL i hi ▸ (List.getElem?_eq_some_iff.1 h₁).1
    simp only [inside, if_pos hk]
    exact related k i hi _ _ h₁ h₂

theorem caller_tupleShifts (c : Caller K circuits settings top tree D parameter openings)
    (prior : RerandLive K circuits settings top tree D parameter openings c) :
    TupleShifts D (c.checkData K circuits settings top tree D parameter openings).tuples₁
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
    simp only [Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi,
      treeStagesRerandTuples] at ht hu
    rw [List.getElem?_append_left (by rw [hN i hi]; exact hk)] at ht
    rw [List.getElem?_append_left (by rw [hN₂ i hi]; exact hk)] at hu
    have h := old i hi t u ht hu
    exact ⟨h.1, h.2.2⟩
  · obtain ⟨dx, hx⟩ := caller_output_shift c
    refine ⟨dx, 0, fun g => ∑ j ∈ univ.filter (· ∉ D.1), (c.peer.v₁ - c.peer.v₂) j g, ?_⟩
    intro i hi t u ht hu
    simp only [Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi,
      treeStagesRerandTuples] at ht hu
    rw [List.getElem?_append_right (by rw [hN i hi]), hN i hi, Nat.sub_self] at ht
    rw [List.getElem?_append_right (by rw [hN₂ i hi]), hN₂ i hi, Nat.sub_self] at hu
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hu
    subst t
    subst u
    refine ⟨rfl, hx i hi, ?_, ?_⟩
    · funext T g
      simp [treeSimHeldShift]
    · have h := (prior.exit i hi).2.2.1
      simpa only [c.rest.count] using h
  · refine ⟨0, 0, 0, ?_⟩
    intro i hi t u ht hu
    have impossible : ((c.checkData K circuits settings top tree D parameter openings).tuples₁ i)[k]? = none := by
      apply List.getElem?_eq_none
      simp only [Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi,
        treeStagesRerandTuples, List.length_append, List.length_singleton, hN i hi]
      omega
    rw [impossible] at ht
    cases ht

/-- Flattening preserves a common shift because the count list is common. -/
theorem lifted_shift {a b : C.Party → List (Tuple C)} (counts : EntryCounts D a)
    (same : ∀ i, i ∉ D.1 → (b i).map (·.count) = (a i).map (·.count))
    (part : Tuple C → Shares C Bit)
    (shift : ∀ m : ℕ, ∃ d : ℕ → Bit, ∀ i, i ∉ D.1 → ∀ t u : Tuple C,
      (a i)[m]? = some t → (b i)[m]? = some u → u.count = t.count ∧
        part u = treeSimHeldShift D i t.count d (part t)) :
    ∃ d : ℕ → E, ∀ i, i ∉ D.1 → ∀ T k,
      liftedPart (E := E) (b i) part T k = liftedPart (a i) part T k +
        if i ∈ C.holders T ∧ lackedTerm D.1 = some T then d k else 0 := by
  obtain ⟨cs, hc⟩ := counts
  choose ds hd using shift
  refine ⟨fun k => match flatPos cs k with | none => 0 | some (m, g) => algebraMap Bit E (ds m g), ?_⟩
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
    simp only [treeSimHeldShift, metadata, hg, true_and, map_add, hp]
    split_ifs <;> simp


theorem tupleShifts_lifted {a b : C.Party → List (Tuple C)}
    (counts : EntryCounts D a)
    (same : ∀ i, i ∉ D.1 → (b i).map (·.count) = (a i).map (·.count))
    (shifts : TupleShifts D a b) :
    ∃ dx dy dz : ℕ → E, ∀ i, i ∉ D.1 → ∀ T k,
      (liftedPart (E := E) (b i) (·.x) T k = liftedPart (a i) (·.x) T k +
        if i ∈ C.holders T ∧ lackedTerm D.1 = some T then dx k else 0) ∧
      (liftedPart (E := E) (b i) (·.y) T k = liftedPart (a i) (·.y) T k +
        if i ∈ C.holders T ∧ lackedTerm D.1 = some T then dy k else 0) ∧
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
  obtain ⟨dz, hz⟩ := lifted_shift (E := E) counts same (·.z) (by
    intro m
    obtain ⟨x, y, z, h⟩ := shifts m
    exact ⟨z, fun i hi t u ht hu => ⟨(h i hi t u ht hu).1, (h i hi t u ht hu).2.2.2⟩⟩)
  exact ⟨dx, dy, dz, fun i hi T k => ⟨hx i hi T k, hy i hi T k, hz i hi T k⟩⟩

/-- A common held shift of the z vector induces one lacked-term claim shift. -/
theorem claim_shift (τ : List E) (count : ℕ) (z₁ z₂ : C.Party → Shares C E) (dz : ℕ → E)
    (shift : ∀ i, i ∉ D.1 → ∀ T k, z₂ i T k = z₁ i T k +
      if i ∈ C.holders T ∧ lackedTerm D.1 = some T then dz k else 0) :
    ∃ e : E, ∀ i, i ∉ D.1 →
      conv K (localContext i) (claimOf K τ count (z₁ i)) 0 -
        conv K (localContext i) (claimOf K τ count (z₂ i)) 0 = lackedShare K D i e := by
  let e := -(∑ k ∈ range (2 ^ sliceBits * sliceWidth count),
    coinProduct τ 0 sliceBits (sliceOf count k) * wordWeightOf K τ count k * dz k)
  refine ⟨e, ?_⟩
  intro i hi
  apply conv_sub_eq
  intro T held
  simp only [claimOf, ← sum_sub_distrib, ← mul_sub]
  simp_rw [shift i hi T]
  simp only [held, true_and]
  by_cases lack : lackedTerm D.1 = some T
  · simp only [lack, ↓reduceIte, sub_add_cancel_left, mul_neg, sum_neg_distrib]
    rfl
  · simp [lack, e]

theorem sliceShape_entry (c : Caller K circuits settings top tree D parameter openings)
    (τ : List E) (prior : RerandLive K circuits settings top tree D parameter openings c)
    (counts : EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁) :
    SliceShape K D
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
  refine ⟨fun k => wordWeightOf K τ cs.sum k * dx k, dy, e, ?_, ?_, ?_⟩
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
theorem TupleShifts.agree {a b : C.Party → List (Tuple C)}
    (shifts : TupleShifts D a b) (counts : EntryCounts D a)
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
    simp only [xi, xj, treeSimHeldShift, hiT, hjT, true_and, old.1, cnt]
  · funext g
    simp only [yi, yj, treeSimHeldShift, hiT, hjT, true_and, old.2.1, cnt]
  · funext g
    simp only [zi, zj, treeSimHeldShift, hiT, hjT, true_and, old.2.2, cnt]

/-- A tuple's global shares agree with its copies on held terms. -/
def Copies (D : C.Coalition) (a : C.Party → List (Tuple C)) (m : ℕ)
    (X Y Z : Shares C Bit) : Prop :=
  ∀ i, i ∉ D.1 → ∀ t : Tuple C, (a i)[m]? = some t → ∀ T, i ∈ C.holders T →
    t.x T = X T ∧ t.y T = Y T ∧ t.z T = Z T

theorem copies_exists {a : C.Party → List (Tuple C)}
    (counts : EntryCounts D a) (agree : EntryTuplesAgree D a) (m : ℕ) :
    ∃ X Y Z : Shares C Bit, Copies D a m X Y Z := by
  choose holder held honest using exists_honest_holder D
  let G := fun (part : Tuple C → Shares C Bit) T g =>
    (((a (holder T))[m]?).map fun t => part t T g).getD 0
  refine ⟨G (·.x), G (·.y), G (·.z), ?_⟩
  obtain ⟨cs, hc⟩ := counts
  intro i hi t ht T hiT
  have hlen : (a (holder T)).length = (a i).length := by
    simpa using congrArg List.length ((hc _ (honest T)).trans (hc i hi).symm)
  have hm : m < (a (holder T)).length := hlen ▸ (List.getElem?_eq_some_iff.1 ht).1
  have eh := List.getElem?_eq_getElem hm
  have aeq := agree T i (holder T) hi (honest T) hiT (held T) m t _ ht eh
  refine ⟨?_, ?_, ?_⟩
  all_goals funext g
  · simpa only [G, eh, Option.map_some, Option.getD_some] using congrFun aeq.1 g
  · simpa only [G, eh, Option.map_some, Option.getD_some] using congrFun aeq.2.1 g
  · simpa only [G, eh, Option.map_some, Option.getD_some] using congrFun aeq.2.2 g

theorem tuple_exists {a : C.Party → List (Tuple C)} {cs : List ℕ}
    (hc : ∀ i, i ∉ D.1 → (a i).map (·.count) = cs)
    (m : ℕ) (hm : m < cs.length) (i : C.Party) (hi : i ∉ D.1) :
    ∃ t : Tuple C, (a i)[m]? = some t ∧ t.count = cs.getD m 0 := by
  have hlen : (a i).length = cs.length := by simpa using congrArg List.length (hc i hi)
  have hmi : m < (a i).length := by omega
  refine ⟨(a i)[m], List.getElem?_eq_getElem hmi, ?_⟩
  rw [← hc i hi, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hmi]
  rfl

/-- Known terms are unchanged between the two global tuple sharings. -/
theorem copies_known {a b : C.Party → List (Tuple C)} {cs : List ℕ}
    (ha : ∀ i, i ∉ D.1 → (a i).map (·.count) = cs)
    (hb : ∀ i, i ∉ D.1 → (b i).map (·.count) = cs)
    (shift : TupleShifts D a b) (m : ℕ) (hm : m < cs.length)
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
  · rw [← l.1, ← r.1, h.2.1]; funext g; simp [treeSimHeldShift, hn]
  · rw [← l.2.1, ← r.2.1, h.2.2.1]; funext g; simp [treeSimHeldShift, hn]
  · rw [← l.2.2, ← r.2.2, h.2.2.2]; funext g; simp [treeSimHeldShift, hn]

/-- The global value difference of a common bit shift is that shift. -/
theorem held_shift_total (g : ℕ) (Z Z' : Shares C Bit) (d : Bit)
    (shift : ∀ T, Z' T g = Z T g + if lackedTerm D.1 = some T then d else 0) :
    shareValue Z g - shareValue Z' g = d := by
  obtain ⟨T₀, lack, _⟩ := lackedTerm_spec D
  simp only [shareValue, ← sum_sub_distrib, shift]
  have hterm : ∀ T, Z T g - (Z T g + if lackedTerm D.1 = some T then d else 0) =
      if T = T₀ then d else 0 := by
    intro T
    simp only [lack, Option.some.injEq, eq_comm (a := T₀)]
    split_ifs <;> simp [CharTwo.neg_eq]
  simp only [hterm]
  simp


theorem mulRep_honest_diff (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (x y x' y' : C.Party → Shares C Bit) (X Y X' Y' : Shares C Bit) (g : ℕ)
    (copies : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
      x i T g = X T g ∧ y i T g = Y T g ∧ x' i T g = X' T g ∧ y' i T g = Y' T g)
    (known : ∀ T, KnownTo D.1 T → X T = X' T ∧ Y T = Y' T) :
    (∑ i ∈ univ.filter (· ∉ D.1),
      (mulRep K (ctx₁ i) (x i) (y i) g - mulRep K (ctx₂ i) (x' i) (y' i) g)) =
      shareValue X g * shareValue Y g - shareValue X' g * shareValue Y' g := by
  have eqs : ∀ i, i ∉ D.1 →
      mulRep K (ctx₁ i) (x i) (y i) g = mulRep K (localContext i) X Y g ∧
      mulRep K (ctx₂ i) (x' i) (y' i) g = mulRep K (localContext i) X' Y' g := by
    intro i hi
    constructor
    · simp only [mulRep, self₁ i hi, localContext]
      apply sum_congr rfl
      intro AB hAB
      obtain ⟨hA, hB⟩ := K.pairs_held i AB hAB
      rw [(copies i hi AB.1 hA).1, (copies i hi AB.2 hB).2.1]
    · simp only [mulRep, self₂ i hi, localContext]
      apply sum_congr rfl
      intro AB hAB
      obtain ⟨hA, hB⟩ := K.pairs_held i AB hAB
      rw [(copies i hi AB.1 hA).2.2.1, (copies i hi AB.2 hB).2.2.2]
  have sums : (∑ i ∈ univ.filter (· ∉ D.1),
      (mulRep K (ctx₁ i) (x i) (y i) g - mulRep K (ctx₂ i) (x' i) (y' i) g)) =
      (∑ i ∈ univ.filter (· ∉ D.1),
        (mulRep K (localContext i) X Y g - mulRep K (localContext i) X' Y' g)) := by
    apply sum_congr rfl
    intro i hi
    rw [(eqs i (mem_filter.mp hi).2).1, (eqs i (mem_filter.mp hi).2).2]
  rw [sums, sum_sub_distrib, honest_sum_sub D]
  · rw [mulRep_views_sum K (fun _ => X) (fun _ => Y) X Y g
      (fun _ _ _ => rfl) (fun _ _ _ => rfl),
      mulRep_views_sum K (fun _ => X') (fun _ => Y') X' Y' g
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)]
  · intro i hi
    unfold mulRep
    apply sum_congr rfl
    intro AB hAB
    obtain ⟨hA, hB⟩ := K.pairs_held i AB hAB
    rw [(known AB.1 ⟨i, hi, hA⟩).1, (known AB.2 ⟨i, hi, hB⟩).2]

theorem ownerSum_honest_diff (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (x x' : C.Party → Shares C Bit) (X X' : Shares C Bit) (g : ℕ)
    (copies : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → x i T = X T ∧ x' i T = X' T)
    (known : ∀ T, KnownTo D.1 T → X T = X' T) :
    (∑ i ∈ univ.filter (· ∉ D.1),
      (ownerSum K (ctx₁ i) (x i) g - ownerSum K (ctx₂ i) (x' i) g)) =
      shareValue X g - shareValue X' g := by
  have eqs : ∀ i, i ∉ D.1 →
      ownerSum K (ctx₁ i) (x i) g = ownerSum K (localContext i) X g ∧
      ownerSum K (ctx₂ i) (x' i) g = ownerSum K (localContext i) X' g := by
    intro i hi
    constructor
    · simp only [ownerSum, self₁ i hi, localContext]
      apply sum_congr rfl
      intro T hT
      have held : i ∈ C.holders T := (by simpa only [localContext] using (mem_filter.mp hT).2 : K.owner T = i) ▸ K.owner_held T
      rw [(copies i hi T held).1]
    · simp only [ownerSum, self₂ i hi, localContext]
      apply sum_congr rfl
      intro T hT
      have held : i ∈ C.holders T := (by simpa only [localContext] using (mem_filter.mp hT).2 : K.owner T = i) ▸ K.owner_held T
      rw [(copies i hi T held).2]
  have sums : (∑ i ∈ univ.filter (· ∉ D.1),
      (ownerSum K (ctx₁ i) (x i) g - ownerSum K (ctx₂ i) (x' i) g)) =
      (∑ i ∈ univ.filter (· ∉ D.1),
        (ownerSum K (localContext i) X g - ownerSum K (localContext i) X' g)) := by
    apply sum_congr rfl
    intro i hi
    rw [(eqs i (mem_filter.mp hi).2).1, (eqs i (mem_filter.mp hi).2).2]
  rw [sums, sum_sub_distrib, honest_sum_sub D]
  · rw [sum_ownerSum K (fun _ => X) X (fun _ _ _ => rfl),
      sum_ownerSum K (fun _ => X') X' (fun _ _ _ => rfl)]
  · intro i hi
    unfold ownerSum
    apply sum_congr rfl
    intro T hT
    have held : i ∈ C.holders T := (by simpa only [localContext] using (mem_filter.mp hT).2 : K.owner T = i) ▸ K.owner_held T
    rw [known T ⟨i, hi, held⟩]

theorem copies_z_total {a b : C.Party → List (Tuple C)} {cs : List ℕ}
    (ha : ∀ i, i ∉ D.1 → (a i).map (·.count) = cs)
    (hb : ∀ i, i ∉ D.1 → (b i).map (·.count) = cs)
    (m : ℕ) (hm : m < cs.length) (g : ℕ) (hg : g < cs.getD m 0)
    (X Y Z X' Y' Z' : Shares C Bit) (left : Copies D a m X Y Z) (right : Copies D b m X' Y' Z')
    (d : ℕ → Bit)
    (shift : ∀ i, i ∉ D.1 → ∀ t u : Tuple C,
      (a i)[m]? = some t → (b i)[m]? = some u → u.z = treeSimHeldShift D i t.count d t.z) :
    shareValue Z g - shareValue Z' g = d g := by
  apply held_shift_total (D := D) g Z Z' (d g)
  intro T
  obtain ⟨i, held, hi⟩ := exists_honest_holder D T
  obtain ⟨t, ht, hcount⟩ := tuple_exists ha m hm i hi
  obtain ⟨u, hu, _⟩ := tuple_exists hb m hm i hi
  rw [← (left i hi t ht T held).2.2, ← (right i hi u hu T held).2.2, shift i hi t u ht hu]
  simp only [treeSimHeldShift, held, hcount, hg, true_and]

/-- Each actual tuple has the same residual in the two global sharings. -/
theorem caller_tuple_residual (c : Caller K circuits settings top tree D parameter openings)
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
    simpa only [Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg c.peer.pivot.honest,
      treeStagesRerandTuples, List.length_map, List.length_append, List.length_singleton,
      hN _ c.peer.pivot.honest] using hc.symm
  by_cases old : m < N
  · have ea : ∀ i, i ∉ D.1 → (a i)[m]? = (c.rest.p₁ i).2[m]? := by
      intro i hi
      simp only [a, Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi, treeStagesRerandTuples]
      exact List.getElem?_append_left (by rw [hN i hi]; exact old)
    have eb : ∀ i, i ∉ D.1 → (b i)[m]? = (c.rest.p₂ i).2[m]? := by
      intro i hi
      simp only [b, Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi, treeStagesRerandTuples]
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
      simp only [a, Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi, treeStagesRerandTuples]
      rw [List.getElem?_append_right (by rw [hN i hi]), hN i hi, Nat.sub_self]
      rfl
    have eb : ∀ i, i ∉ D.1 → (b i)[N]? = some
        ⟨outputShares K c.rest.circs (c.rest.p₂ i).1, one K, (n.x₂ i).1, (outputsOf c.rest.circs).length, .peer⟩ := by
      intro i hi
      simp only [b, Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi, treeStagesRerandTuples]
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


/-- Concatenate the global bit shares with the same metadata as the copies. -/
def flatShares (cs : List ℕ) (V : ℕ → Shares C Bit) : Shares C E := fun T k =>
  match flatPos cs k with
  | none => 0
  | some (m, g) => algebraMap Bit E (V m T g)

theorem lifted_of_copies {a : C.Party → List (Tuple C)} {cs : List ℕ}
    (counts : ∀ i, i ∉ D.1 → (a i).map (·.count) = cs)
    (part : Tuple C → Shares C Bit) (V : ℕ → Shares C Bit)
    (copies : ∀ m i, i ∉ D.1 → ∀ t : Tuple C, (a i)[m]? = some t →
      ∀ T, i ∈ C.holders T → part t T = V m T)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (held : i ∈ C.holders T) :
    liftedPart (E := E) (a i) part T = flatShares (E := E) cs V T := by
  funext k
  rw [liftedPart_flat, counts i hi]
  cases hp : flatPos cs k with
  | none => simp [flatShares, hp]
  | some pos =>
    obtain ⟨m, g⟩ := pos
    obtain ⟨hm, _⟩ := flatPos_spec cs k m g hp
    obtain ⟨t, ht, _⟩ := tuple_exists counts m hm i hi
    simp only [flatShares, hp, ht, Option.map_some, Option.getD_some, copies m i hi t ht T held]

-- The finite weighted-sum calculation of CheckFinish.checkInitSlice,
-- factored from its particular canonical dummy tuple construction.
theorem initial_rel (τ : List E) (count : ℕ) (a b : C.Party → List (Tuple C))
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (total : ∀ i, i ∉ D.1 → ((a i).map (·.count)).sum = count ∧ ((b i).map (·.count)).sum = count)
    (X Y Z X' Y' Z' : Shares C E)
    (copies : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
      liftedPart (a i) (·.x) T = X T ∧ liftedPart (a i) (·.y) T = Y T ∧
      liftedPart (a i) (·.z) T = Z T ∧ liftedPart (b i) (·.x) T = X' T ∧
      liftedPart (b i) (·.y) T = Y' T ∧ liftedPart (b i) (·.z) T = Z' T)
    (known : ∀ T, KnownTo D.1 T → X T = X' T ∧ Y T = Y' T ∧ Z T = Z' T)
    (residual : ∀ k, shareValue Z k - shareValue Z' k =
      shareValue X k * shareValue Y k - shareValue X' k * shareValue Y' k) :
    SliceRel K D τ count 0
      (fun i => (treeStagesCheckInitial K (ctx₁ i) (a i) τ).1)
      (fun i => (treeStagesCheckInitial K (ctx₁ i) (a i) τ).2.1)
      (fun i => (treeStagesCheckInitial K (ctx₂ i) (b i) τ).1)
      (fun i => (treeStagesCheckInitial K (ctx₂ i) (b i) τ).2.1)
      (fun i => (treeStagesCheckInitial K (ctx₁ i) (a i) τ).2.2)
      (fun i => (treeStagesCheckInitial K (ctx₂ i) (b i) τ).2.2) := by
  refine ⟨fun T k => wordWeightOf K τ count k * X T k, Y,
    fun T k => wordWeightOf K τ count k * X' T k, Y',
    fun T => claimOf K τ count Z T 0 - claimOf K τ count Z' T 0, ?_, ?_, ?_, ?_⟩
  · intro i hi T held
    have h := copies i hi T held
    dsimp only [treeStagesCheckInitial]
    rw [(total i hi).1, (total i hi).2, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro T hk
    have h := known T hk
    exact ⟨by dsimp only; rw [h.1], h.2.1, by simp only [claimOf, h.2.2, sub_self]⟩
  · intro i hi
    dsimp only [treeStagesCheckInitial]
    rw [(total i hi).1, (total i hi).2, conv_self K _ i (self₁ i hi), conv_self K _ i (self₂ i hi)]
    have e1 : conv K (localContext i) (claimOf K τ count (liftedPart (a i) (·.z))) 0 =
        conv K (localContext i) (claimOf K τ count Z) 0 :=
      conv_congr i _ _ 0 fun T held => by simp only [claimOf, (copies i hi T held).2.2.1]
    have e2 : conv K (localContext i) (claimOf K τ count (liftedPart (b i) (·.z))) 0 =
        conv K (localContext i) (claimOf K τ count Z') 0 :=
      conv_congr i _ _ 0 fun T held => by simp only [claimOf, (copies i hi T held).2.2.2.2.2]
    rw [e1, e2, conv_sub_const]
  · have hlen : sliceLen count 0 = 2 ^ sliceBits * sliceWidth count := by simp [sliceLen, mul_comm]
    have hs : ∑ T, (claimOf K τ count Z T 0 - claimOf K τ count Z' T 0) =
        ∑ k ∈ range (2 ^ sliceBits * sliceWidth count),
          coinProduct τ 0 sliceBits (sliceOf count k) * wordWeightOf K τ count k *
            (shareValue Z k - shareValue Z' k) := by
      simp only [claimOf, shareValue, ← sum_sub_distrib, mul_sub, mul_sum]
      rw [sum_comm]
    rw [hs, hlen]
    apply sum_congr rfl
    intro k _
    have hw (V : Shares C E) : shareValue (fun T k => wordWeightOf K τ count k * V T k) k =
        wordWeightOf K τ count k * shareValue V k := by simp only [shareValue, mul_sum]
    rw [hw X, hw X', residual k]
    simp only [sliceWeight, Nat.sub_zero, sliceOf]
    ring

theorem sliceRel_entry [CharP E 2]
    (c : Caller K circuits settings top tree D parameter openings) (τ : List E)
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
  choose X' Y' Z' right using (fun m => copies_exists counts.run₂ agree₂ m)
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
      simpa only [flatShares, hp, shareValue, ← map_sum, ← map_mul, ← map_sub] using
        congrArg (algebraMap Bit E) residual


theorem firstSlice_expansion (c : Caller K circuits settings top tree D parameter openings)
    (base : HashCache C) (coinRnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E)
    (pos : Position circuits settings tree D parameter c.rest.circs (depth c.rest.circs + 1)
      (c.checkData K circuits settings top tree D parameter openings).st₁)
    (total : ∀ i, i ∉ D.1 → c.count₁ K circuits settings top tree D parameter openings i = tupleCount c.rest.circs)
    (live : ∀ i, i ∉ D.1 → (c.checkData K circuits settings top tree D parameter openings).firstLive K D base coinRnd sent i = true) :
    ∃ τ : List E, (∀ i, i ∉ D.1 →
      (c.checkData K circuits settings top tree D parameter openings).expansion K D base coinRnd sent i = τ) ∧
      ∀ b < sliceBits, τ.getD b 0 ≠ 0 := by
  let p := c.checkData K circuits settings top tree D parameter openings
  let i₀ := c.peer.pivotParty
  have hi₀ : i₀ ∉ D.1 := c.peer.pivot.honest
  let τ := p.expansion K D base coinRnd sent i₀
  refine ⟨τ, ?_, ?_⟩
  · intro i hi
    obtain ⟨enc, k, _, _, _, hp⟩ := pos
    have tags : p.tag i = p.tag i₀ := by
      change (if i ∈ D.1 then 0 else (p.st₁ i).tag) =
        (if i₀ ∈ D.1 then 0 else (p.st₁ i₀).tag)
      rw [if_neg hi, if_neg hi₀, (hp i hi).1, (hp i₀ hi₀).1]
    have labels : p.hashLabel i = p.hashLabel i₀ := by
      change (if i ∈ D.1 then 0 else (p.st₁ i).label) =
        (if i₀ ∈ D.1 then 0 else (p.st₁ i₀).label)
      rw [if_neg hi, if_neg hi₀, (hp i hi).2, (hp i₀ hi₀).2]
    have li := live i hi
    have l₀ := live i₀ hi₀
    cases oi : treeSimCoinOutput K D 1 coinRnd sent i with
    | none => simp [TreeTwinCheckCoinData.firstLive, treeStagesExpansionLive, oi] at li
    | some a =>
      cases o₀ : treeSimCoinOutput K D 1 coinRnd sent i₀ with
      | none => simp [TreeTwinCheckCoinData.firstLive, treeStagesExpansionLive, o₀] at l₀
      | some b =>
        have same := coinOutput_agree K D 1 coinRnd sent hi hi₀ oi o₀
        change p.expansion K D base coinRnd sent i = p.expansion K D base coinRnd sent i₀
        have countEq : ((p.tuples₁ i).map (·.count)).sum = ((p.tuples₁ i₀).map (·.count)).sum :=
          (total i hi).trans (total i₀ hi₀).symm
        simp only [TreeTwinCheckCoinData.expansion, oi, o₀, Option.getD_some,
          same, tags, labels, countEq]
  · have hl := live i₀ hi₀
    simp only [TreeTwinCheckCoinData.firstLive, treeStagesExpansionLive, Bool.and_eq_true,
      decide_eq_true_eq] at hl
    exact hl.2

set_option maxRecDepth 4000 in
/-- The first saved slice keeps the actual caller. Its value relation uses
only the supplied entry link, common metadata and successful Rerand. -/
theorem savedRel_firstSlice
    (c : Caller K circuits settings top tree D parameter openings)
    (base : HashCache C) (coinRnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E)
    (pos : Position circuits settings tree D parameter c.rest.circs (depth c.rest.circs + 1)
      (c.checkData K circuits settings top tree D parameter openings).st₁)
    (total : ∀ i, i ∉ D.1 → c.count₁ K circuits settings top tree D parameter openings i = tupleCount c.rest.circs)
    (hist₁ : CommonHistory D (fun _ => true) (c.checkData K circuits settings top tree D parameter openings).st₁)
    (hist₂ : CommonHistory D (fun _ => true) (c.checkData K circuits settings top tree D parameter openings).st₂)
    (prior : RerandLive K circuits settings top tree D parameter openings c)
    (live : ∀ i, i ∉ D.1 → (c.checkData K circuits settings top tree D parameter openings).firstLive K D base coinRnd sent i = true)
    (counts : EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁)
    (link : EntryLink c) :
    ∃ w, SavedRelAt K circuits settings top tree D parameter openings
      ((c.checkData K circuits settings top tree D parameter openings).firstSlice K D base coinRnd sent) w ∧
      w.caller = c ∧ w.phase.index = 0 := by
  letI : CharP E 2 := charP_two
  let p := c.checkData K circuits settings top tree D parameter openings
  let q := p.firstSlice K D base coinRnd sent
  obtain ⟨τ, common, nz⟩ := firstSlice_expansion c base coinRnd sent pos total live
  let v₁ := fun i => treeStagesCheckInitial K (c.peer.ctx₁ i) (p.tuples₁ i) τ
  let v₂ := fun i => treeStagesCheckInitial K (c.peer.ctx₂ i) (p.tuples₂ i) τ
  let φ : SavedPhase C E := .slice τ 0 v₁ v₂
  let w : SavedWitness K circuits settings top tree D parameter openings := ⟨c, φ⟩
  have bound : φ.Bound (tupleCount c.rest.circs) := by change 0 < sliceBits; decide
  have nonzero : tupleCount c.rest.circs ≠ 0 := by
    rw [← total c.peer.pivotParty c.peer.pivot.honest]
    simpa [Caller.count₁, Caller.checkData, TreeStagesRerandTail.checkCoinData,
      treeStagesRerandTuples, c.peer.pivot.honest] using c.nonzero₁ c.peer.pivotParty c.peer.pivot.honest
  refine ⟨w, ?_, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, total, bound, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact treeTwin_peer_saved_tag K D c.peer c.sent i hi
  · have hpos := position_shift circuits settings tree D parameter c.rest.circs
      (depth c.rest.circs + 1) 1 p.st₁ q.st₁ pos
      (fun _ _ => rfl) (fun _ _ => rfl) (by
        intro jobs eq
        have h := savedOffset_le circuits parameter jobs (φ := φ)
          (c := tupleCount c.rest.circs) (congrArg tupleCount eq) nonzero bound
        simpa only [← eq, savedOffset, φ, SavedPhase.index, mul_zero, add_zero, Nat.add_assoc] using h)
    simpa only [w, φ, savedOffset, SavedPhase.index, mul_zero, add_zero, Nat.add_assoc] using hpos
  · exact hist₁
  · exact hist₂
  · change (∀ b < sliceBits, τ.getD b 0 ≠ 0) ∧ _
    refine ⟨nz, ?_, ?_, ?_, ?_, sliceShape_entry c τ prior counts, ?_⟩
    · intro i hi
      change treeStagesSliceBody K (p.ctx₁ i) (p.expansion K D base coinRnd sent i)
        ((p.tuples₁ i).map (·.count)).sum 0 ((List.range sliceBits).drop 1)
        (treeStagesCheckInitial K (p.ctx₁ i) (p.tuples₁ i) (p.expansion K D base coinRnd sent i)) (p.finish₁ i) = _
      rw [common i hi]
      rfl
    · intro i hi
      change treeStagesSliceBody K (p.ctx₂ i) (p.expansion K D base coinRnd sent i)
        ((p.tuples₂ i).map (·.count)).sum 0 ((List.range sliceBits).drop 1)
        (treeStagesCheckInitial K (p.ctx₂ i) (p.tuples₂ i) (p.expansion K D base coinRnd sent i)) (p.finish₂ i) = _
      rw [common i hi, ← p.counts i]
      rfl
    · intro i hi
      change treeStagesSliceProducts (p.expansion K D base coinRnd sent i)
        ((p.tuples₁ i).map (·.count)).sum 0
        (treeStagesCheckInitial K (p.ctx₁ i) (p.tuples₁ i) (p.expansion K D base coinRnd sent i)) = _
      rw [common i hi]
      change treeStagesSliceProducts τ (c.count₁ K circuits settings top tree D parameter openings i) 0 (v₁ i) = _
      rw [total i hi]
    · intro i hi
      change treeStagesSliceProducts (p.expansion K D base coinRnd sent i)
        ((p.tuples₂ i).map (·.count)).sum 0
        (treeStagesCheckInitial K (p.ctx₂ i) (p.tuples₂ i) (p.expansion K D base coinRnd sent i)) = _
      rw [common i hi, ← p.counts i]
      change treeStagesSliceProducts τ (c.count₁ K circuits settings top tree D parameter openings i) 0 (v₂ i) = _
      rw [total i hi]
    · intro history
      exact sliceRel_entry c τ nz total prior counts (link history)

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedEntry.RerandLive.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RerandLive.exit

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedEntry.sliceShape_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceShape_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedEntry.caller_tuple_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms caller_tuple_residual

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedEntry.sliceRel_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceRel_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSavedEntry.savedRel_firstSlice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms savedRel_firstSlice


end ThresholdLeanXmssSecurity.TreeTwinSavedEntry
