import ThresholdLeanXmssSecurity.Proof.TreeTwinHistoryRecords
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkTranscript
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkConsistent

/-! # Tuple values retained by actual bit records -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinValueLink
open TreeTwinSavedSchedule TreeTwinSavedEntry TreeCheckWalkConsistent TreeCheckWalkTranscript
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

def recordBlock (mode : ReshareMode) (T : C.Term) (z : Shares C Bit) (count : ℕ) : List Bit :=
  ((List.range count).filter fun g => (filler K mode T g).isSome).map (z T)

theorem recordPeer_bit_eq (i : C.Party) (h : C.Term → List Bit) (z : Shares C Bit) (count : ℕ) :
    recordPeer K bitCodec i h z count = recordMode K .peer i h z count := rfl

theorem recordMode_eq_append (mode : ReshareMode) (i : C.Party) (h : C.Term → List Bit)
    (z : Shares C Bit) (count : ℕ) (T : C.Term) (held : i ∈ C.holders T) :
    recordMode K mode i h z count T = h T ++ recordBlock K mode T z count := by
  simp [recordMode, recordBlock, held, bitCodec, Function.comp_def, ← List.map_eq_flatMap]

theorem recordBlock_length (mode : ReshareMode) (T : C.Term) (z : Shares C Bit) (count : ℕ) :
    (recordBlock K mode T z count).length =
      ((List.range count).filter fun g => (filler K mode T g).isSome).length := by
  simp [recordBlock]

theorem filled_eq_of_block (mode : ReshareMode) (T : C.Term) (z z' : Shares C Bit) (count g : ℕ)
    (same : recordBlock K mode T z count = recordBlock K mode T z' count)
    (hg : g < count) (filled : (filler K mode T g).isSome) : z T g = z' T g := by
  exact List.map_inj_left.mp same g (List.mem_filter.mpr ⟨List.mem_range.mpr hg, filled⟩)

/-- Equal completed records retain equal prefixes and every recorded product. -/
theorem allHistory_of_records (D : C.Coalition) (mode : ReshareMode) (count : ℕ)
    (st st' : C.Party → RunState C) (z : C.Party → Shares C Bit)
    (records : ∀ i, i ∉ D.1 → (st' i).history = recordMode K mode i (st i).history (z i) count)
    (hist : AllHistory D st') :
    AllHistory D st ∧ ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      ∀ g < count, (filler K mode T g).isSome → z i T g = z j T g := by
  have blocks (T : C.Term) (i : C.Party) (hi : i ∉ D.1) (held : i ∈ C.holders T) :
      (st' i).history T = (st i).history T ++ recordBlock K mode T (z i) count := by
    rw [records i hi, recordMode_eq_append K mode i _ _ count T held]
  have prior : AllHistory D st := allHistory_of_append D st st'
    (fun T => ((List.range count).filter fun g => (filler K mode T g).isSome).length)
    (fun T i hi held => ⟨_, recordBlock_length K mode T (z i) count, blocks T i hi held⟩) hist
  refine ⟨prior, ?_⟩
  intro T i j hi hj heldI heldJ g hg filled
  have same := hist T i j hi hj heldI heldJ
  rw [blocks T i hi heldI, blocks T j hj heldJ, prior T i j hi hj heldI heldJ] at same
  exact filled_eq_of_block K mode T (z i) (z j) count g (List.append_cancel_left same) hg filled

def WireAgree (D : C.Coalition) (w : C.Party → MainInput C) : Prop :=
  ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    wiresAt T (w i) = wiresAt T (w j)

/-- The tuple count list is shared by all honest callers. -/
def TupleShape (D : C.Coalition) (p : C.Party → MainInput C × List (Tuple C)) : Prop :=
  EntryCounts D (fun i => (p i).2)

def ValueLink (D : C.Coalition) (p : C.Party → MainInput C × List (Tuple C))
    (st : C.Party → RunState C) : Prop :=
  AllHistory D st → WireAgree D (fun i => (p i).1) ∧ EntryTuplesAgree D (fun i => (p i).2)

theorem valueLink_entry (D : C.Coalition) (w : C.Party → MainInput C)
    (st : C.Party → RunState C) (agree : WireAgree D w) :
    ValueLink D (fun i => (w i, [])) st := by
  intro _
  refine ⟨agree, ?_⟩
  intro T i j hi hj heldI heldJ k t t' ht
  simp at ht

theorem tupleShape_entry (D : C.Coalition) (w : C.Party → MainInput C) :
    TupleShape D (fun i => (w i, [])) := ⟨[], fun _ _ => rfl⟩

theorem zAgree_full (D : C.Coalition) (mode : ReshareMode) (count : ℕ)
    (z : C.Party → Shares C Bit) (unfilled : ZAgree K D mode count z)
    (filled : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      ∀ g < count, (filler K mode T g).isSome → z i T g = z j T g)
    (outside : ∀ i, i ∉ D.1 → ∀ T g, count ≤ g → z i T g = 0) :
    ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      z i T = z j T := by
  intro T i j hi hj heldI heldJ
  funext g
  by_cases hg : g < count
  · by_cases hf : (filler K mode T g).isSome
    · exact filled T i j hi hj heldI heldJ g hg hf
    · apply unfilled T i j heldI heldJ hi hj g hg
      rintro ⟨k, _, hk⟩
      simp [hk] at hf
  · rw [outside i hi T g (by omega), outside j hj T g (by omega)]

theorem appendLayer_wireAgree (D : C.Coalition) (jobs : List Circuit) (layer : ℕ)
    (w : C.Party → MainInput C) (z : C.Party → Shares C Bit) (agree : WireAgree D w)
    (products : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      z i T = z j T) : WireAgree D (fun i => appendLayer jobs layer (w i) (z i)) := by
  intro T i j hi hj heldI heldJ
  exact TreeCheckWalkConsistent.appendLayer_congr jobs layer T (agree T i j hi hj heldI heldJ)
    (fun g _ => congrFun (products T i j hi hj heldI heldJ) g)

theorem peerOutputs_value {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1)
    (x : Shares C Bit × RunState C)
    (out : treeSimPeerOutputs K D ctx count rnd v st k sent i = some x) :
    x.1 = reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2 (v i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) bitCodec (rnd j).1 (rnd j).2 (v j) count i) := by
  simp only [treeSimPeerOutputs, if_neg hi, treeSimPeerReturn] at out
  split_ifs at out
  cases out
  apply congrArg (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2 (v i) count)
  funext j
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj]
  · simp [hj, treeSimPeerWaiting, treeSimPeerStep, Step.delivered]

/-- Actual successful peer outputs give full product agreement when their records agree. -/
theorem peerOutputs_agree {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 → treeSimPeerOutputs K D ctx count rnd v st k sent i = some (x i))
    (masks : MaskAgree D count rnd) (hist : AllHistory D (fun i => (x i).2)) :
    AllHistory D st ∧ ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (x i).1 T = (x j).1 T := by
  have recorded : ∀ i, i ∉ D.1 → (x i).2.history =
      recordMode K .peer i (st i).history (x i).1 count := by
    intro i hi
    rw [TreeTwinHistoryRecords.peerOutputs_history K D ctx count rnd v st k sent i (x i) (out i hi),
      self i hi, recordPeer_bit_eq]
  have records := allHistory_of_records K D .peer count st (fun i => (x i).2)
    (fun i => (x i).1) recorded hist
  refine ⟨records.1, zAgree_full K D .peer count (fun i => (x i).1) ?_ records.2 ?_⟩
  · intro T i j heldI heldJ hi hj g hg unfilled
    change (x i).1 T g = (x j).1 T g
    rw [peerOutputs_value K D ctx count rnd v st k sent i hi (x i) (out i hi),
      peerOutputs_value K D ctx count rnd v st k sent j hj (x j) (out j hj)]
    exact peer_agree K D ctx self rnd v count sent masks T i j heldI heldJ hi hj g hg unfilled
  · intro i hi T g hg
    rw [peerOutputs_value K D ctx count rnd v st k sent i hi (x i) (out i hi),
      treeSim_reshareZ_value K D ctx self rnd v count sent i hi T g]
    simp [hg]

theorem entryCounts_append (D : C.Coalition) (tuples : C.Party → List (Tuple C))
    (shape : EntryCounts D tuples) (x y z : C.Party → Shares C Bit)
    (count : ℕ) (mode : ReshareMode) :
    EntryCounts D (fun i => tuples i ++ [⟨x i, y i, z i, count, mode⟩]) := by
  obtain ⟨counts, hc⟩ := shape
  refine ⟨counts ++ [count], ?_⟩
  intro i hi
  simp [hc i hi]

theorem entryTuplesAgree_append (D : C.Coalition) (tuples : C.Party → List (Tuple C))
    (shape : EntryCounts D tuples) (agree : EntryTuplesAgree D tuples)
    (x y z : C.Party → Shares C Bit) (count : ℕ) (mode : ReshareMode)
    (new : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      x i T = x j T ∧ y i T = y j T ∧ z i T = z j T) :
    EntryTuplesAgree D (fun i => tuples i ++ [⟨x i, y i, z i, count, mode⟩]) := by
  obtain ⟨counts, hc⟩ := shape
  have length (i : C.Party) (hi : i ∉ D.1) : (tuples i).length = counts.length := by
    simpa using congrArg List.length (hc i hi)
  intro T i j hi hj heldI heldJ k t t' ht ht'
  by_cases hk : k < counts.length
  · rw [List.getElem?_append_left (by rw [length i hi]; exact hk)] at ht
    rw [List.getElem?_append_left (by rw [length j hj]; exact hk)] at ht'
    exact agree T i j hi hj heldI heldJ k t t' ht ht'
  · rw [List.getElem?_append_right (by rw [length i hi]; omega), length i hi] at ht
    rw [List.getElem?_append_right (by rw [length j hj]; omega), length j hj] at ht'
    cases he : k - counts.length with
    | zero =>
        simp only [he, List.getElem?_cons_zero, Option.some.injEq] at ht ht'
        subst t
        subst t'
        exact new T i j hi hj heldI heldJ
    | succ n => simp [he] at ht

theorem valueLink_peerLayer {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i) (jobs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 →
      treeSimPeerOutputs K D ctx (gatesAt jobs layer).length rnd v st k sent i = some (x i))
    (masks : MaskAgree D (gatesAt jobs layer).length rnd)
    (values : ValueLink D p st) (shape : TupleShape D p) :
    let p' := fun i => (appendLayer jobs layer (p i).1 (x i).1,
      (p i).2 ++ [⟨layerX K jobs layer (p i).1, layerY K jobs layer (p i).1,
        (x i).1, (gatesAt jobs layer).length, .peer⟩])
    ValueLink D p' (fun i => (x i).2) ∧ TupleShape D p' := by
  dsimp only
  refine ⟨?_, entryCounts_append D _ shape _ _ _ _ _⟩
  intro hist
  have outputs := peerOutputs_agree K D ctx self _ rnd v st k sent x out masks hist
  have old := values outputs.1
  refine ⟨appendLayer_wireAgree D jobs layer _ _ old.1 outputs.2,
    entryTuplesAgree_append D _ shape old.2 _ _ _ _ _ ?_⟩
  intro T i j hi hj heldI heldJ
  exact ⟨TreeCheckWalkConsistent.layerX_congr K jobs layer T (old.1 T i j hi hj heldI heldJ),
    TreeCheckWalkConsistent.layerY_congr K jobs layer T (old.1 T i j hi hj heldI heldJ),
    outputs.2 T i j hi hj heldI heldJ⟩

/-- The actual Rerand records and the caller's incoming value link supply the original entry link. -/
theorem entryLink_of_rerand (circuits : Circuits) (settings : Settings) (top : TopTree)
    (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit)))
    (c : TreeTwinLinked2.Caller K circuits settings top tree D parameter openings)
    (live : RerandLive K circuits settings top tree D parameter openings c)
    (values : ValueLink D c.rest.p₁ c.peer.st₁) (shape : TupleShape D c.rest.p₁)
    (masks : MaskAgree D c.peer.count c.peer.rnd₁) :
    EntryLink c ∧
      EntryCounts D (c.checkData K circuits settings top tree D parameter openings).tuples₁ := by
  let n := c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂
    c.nonzero₁ c.nonzero₂ c.sent
  have out : ∀ i, i ∉ D.1 →
      treeSimPeerOutputs K D c.peer.ctx₁ c.peer.count c.peer.rnd₁ c.peer.v₁
        c.peer.st₁ c.peer.k₁ c.sent i = some (n.x₁ i) := fun i hi => (live.exit i hi).1
  constructor
  · intro hist
    have current : AllHistory D (fun i => (n.x₁ i).2) := by
      exact hist
    have outputs := peerOutputs_agree K D c.peer.ctx₁ c.peer.self₁ c.peer.count
      c.peer.rnd₁ c.peer.v₁ c.peer.st₁ c.peer.k₁ c.sent n.x₁ out masks current
    have old := values outputs.1
    have added : EntryTuplesAgree D (fun i => treeStagesRerandTuples K c.rest.circs (c.rest.p₁ i) (n.x₁ i).1) := by
      apply entryTuplesAgree_append D _ shape old.2
      intro T i j hi hj heldI heldJ
      exact ⟨TreeCheckWalkConsistent.outputShares_congr K c.rest.circs T (old.1 T i j hi hj heldI heldJ),
        rfl, outputs.2 T i j hi hj heldI heldJ⟩
    intro T i j hi hj heldI heldJ k t t' ht ht'
    apply added T i j hi hj heldI heldJ k t t'
    · simpa only [TreeTwinLinked2.Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi] using ht
    · simpa only [TreeTwinLinked2.Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hj] using ht'
  · obtain ⟨counts, hc⟩ := shape
    refine ⟨counts ++ [(outputsOf c.rest.circs).length], ?_⟩
    intro i hi
    simp only [TreeTwinLinked2.Caller.checkData, TreeStagesRerandTail.checkCoinData, if_neg hi,
      treeStagesRerandTuples, List.map_append, List.map_cons, List.map_nil, hc i hi]

end ThresholdLeanXmssSecurity.TreeTwinValueLink

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.allHistory_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.allHistory_of_records

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.zAgree_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.zAgree_full

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.peerOutputs_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.peerOutputs_value

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.peerOutputs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.peerOutputs_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.entryTuplesAgree_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.entryTuplesAgree_append

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.valueLink_peerLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.valueLink_peerLayer

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinValueLink.entryLink_of_rerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinValueLink.entryLink_of_rerand
