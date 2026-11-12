import ThresholdLeanXmssSecurity.Proof.TreeTwinGuessStart

/-! # Retaining a saved-witness predicate through the finishing round -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss Finset
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinGuessCarry
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinSavedKinds TreeTwinSegment
open TreeTwinPrefill TreeTwinPassPrefill TreeTwinFinishPass TreeTwinLocalSum TreeTwinGuessStart
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

section Stages
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (openings : List (List (List Bit)))
    (P : TreeStagesExtendMultChallenge K D →
      SavedWitness K circuits settings top tree D parameter openings → Prop)

/-- A live finishing Coin with a predicate on its own saved witness. -/
def FinishingCoinLiveP (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (q : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E)
    (sent : C.Party → Mail C E) (coinRnd : C.Party → PrssOutput C E),
    (∃ w, SavedRelAt K circuits settings top tree D parameter openings q w ∧
      w.phase.Finishing (tupleCount w.caller.rest.circs) ∧ P q w) ∧
    (∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) ∧
    (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
    TreeSimFutureZero (q.label + 2) δ ∧
    TreeSimFutureEmpty (q.label + 2) a.2.1.2 ∧ TreeSimFutureEmpty (q.label + 2) b.2.2 ∧
    a.1.2 = treeSimCoinPartial K D (q.coinNext K D rnd δ sent).live
      (q.coinNext K D rnd δ sent).count coinRnd (q.coinNext K D rnd δ sent).st₁
      (q.coinNext K D rnd δ sent).next₁ ∧
    b.1.2 = treeSimCoinPartial K D (q.coinNext K D rnd δ sent).live
      (q.coinNext K D rnd δ sent).count coinRnd (q.coinNext K D rnd δ sent).st₂
      (q.coinNext K D rnd δ sent).next₂

/-- The field output retains the predicate on precisely the incoming saved witness. -/
def GuessFieldPlusP (ĉ : E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (q : TreeStagesExtendMultChallenge K D)
    (w : SavedWitness K circuits settings top tree D parameter openings)
    (rnd : C.Party → PrssOutput C E) (δp : HiddenAddress C → Bit)
    (sent : C.Party → Mail C E) (s : E) (j : ℕ)
    (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E)
    (f : FinalData K circuits settings top tree D parameter openings)
    (d : TreeSimExtendMultData K D) (offset : ℕ),
    let n := q.coinNext K D rnd δp sent
    let tag := (q.st₁ q.pivotParty).tag
    SavedRelAt K circuits settings top tree D parameter openings q w ∧ P q w ∧
    w.phase = .halving j v₁ v₂ ∧ w.phase.Finishing (tupleCount w.caller.rest.circs) ∧
    (∀ i, i ∉ D.1 → n.live i = true) ∧ f.caller = w.caller ∧
    (∀ i, i ∉ D.1 →
      f.claim₁ i = treeStagesHalvingUpdate K (q.ctx₁ i)
        (sliceWidth (tupleCount w.caller.rest.circs)) j (v₁ i) (n.x₁ i).1 s ∧
      f.claim₂ i = treeStagesHalvingUpdate K (q.ctx₂ i)
        (sliceWidth (tupleCount w.caller.rest.circs)) j (v₂ i) (n.x₂ i).1 s) ∧
    (∀ i, i ∉ D.1 → d.st₁ i = nextLabel (nextLabel (n.st₁ i)) ∧
      d.st₂ i = nextLabel (nextLabel (n.st₂ i))) ∧
    TreeStagesChallengeCovered K a.2.1.1 tag (q.label + 5) [ĉ] ∧
    GuessFieldAt K circuits settings top tree D A parameter openings
      (challengeAt K a.2.1.1 tag (q.label + 5) ĉ) δ a b f d offset (q.label + 3)

/-- Dropping the retained predicate gives the frozen live-Coin form. -/
theorem finishingCoinLiveP_forget (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : FinishingCoinLiveP K circuits settings top tree D A parameter openings P δ a b) :
    FinishingCoinLive K circuits settings top tree D A parameter openings δ a b := by
  obtain ⟨q, rnd, sent, coinRnd, ⟨w, saved, finish, _⟩, rest⟩ := h
  exact ⟨q, rnd, sent, coinRnd, ⟨w, saved, finish⟩, rest⟩

/-- Dropping the predicate keeps every field of the original saved output. -/
theorem guessFieldPlusP_forget (ĉ : E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : GuessFieldPlusP K circuits settings top tree D A parameter openings P ĉ δ a b) :
    GuessFieldPlus K circuits settings top tree D A parameter openings ĉ δ a b := by
  obtain ⟨q, w, rnd, δp, sent, s, j, v₁, v₂, f, d, offset, saved, _, rest⟩ := h
  exact ⟨q, w, rnd, δp, sent, s, j, v₁, v₂, f, d, offset, saved, rest⟩

/-- The finishing alternatives retain the original saved-witness predicate. -/
def Round1EndP (ĉ : E) := treeTwinReq D (fun _ δ a b =>
  TreeTwinDoneStage a b ∨ StoppedFieldStage K D δ a b ∨
    GuessFieldPlusP K circuits settings top tree D A parameter openings P ĉ δ a b)

/-- The strengthened postcondition implies the frozen finishing postcondition. -/
theorem round1EndP_forget (ĉ : E) (n : ℕ) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : Round1EndP K circuits settings top tree D A parameter openings P ĉ n δ a b) :
    Round1End K circuits settings top tree D A parameter openings ĉ n δ a b := by
  obtain ⟨related, state, done, outputs, stage⟩ := h
  refine ⟨related, state, done, outputs, ?_⟩
  rcases stage with stopped | stopped | live
  · exact Or.inl stopped
  · exact Or.inr (Or.inl stopped)
  · exact Or.inr (Or.inr (guessFieldPlusP_forget K circuits settings top tree D A
      parameter openings P ĉ δ a b live))

end Stages

/-- The actual finishing round carries any predicate on its retained q and w.
Port of TreeTwinGuessStart.finishingRound: the coupling and its helper calls are
unchanged; the stage premise is arbitrary and the same witness carries P. -/
theorem finishingRoundP (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C)
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1))
    (P : TreeStagesExtendMultChallenge K D →
      SavedWitness K circuits settings top tree D parameter p.1.2 → Prop)
    (Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (ĉ : E) : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a → n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    treeTwinReq D Stage n δ (a.1, treeStagesTwin swaps a.2) b →
    FinishingCoinLiveP K circuits settings top tree D A parameter p.1.2 P δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
      (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
        ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
          Round1EndP K circuits settings top tree D A parameter p.1.2 P ĉ (n + 1) δ'
            ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2)) := by
  intro round δ swaps a b reach bound good active salts req stage
  obtain ⟨related, state, _, _, _⟩ := req
  obtain ⟨q, rnd, sent, coinRnd, ⟨w, saved, finish, carried⟩, allLive, visibleOld, future,
    fresh₁, fresh₂, left, right⟩ := stage
  let n := q.coinNext K D rnd δ sent
  obtain ⟨j, v₁, v₂, phase, last⟩ := saved.finishing_halving finish
  have source := saved.state
  simp only [SavedState, phase] at source
  obtain ⟨body₁, body₂, products₁, products₂, shape, rel⟩ := source
  have suffix : halvSuffix (tupleCount w.caller.rest.circs) j = [] := by
    simpa only [phase, SavedPhase.Finishing] using finish
  let width := sliceWidth (tupleCount w.caller.rest.circs)
  let finish₁ := (w.caller.checkData K circuits settings top tree D parameter p.1.2).finish₁
  let finish₂ := (w.caller.checkData K circuits settings top tree D parameter p.1.2).finish₂
  let tag := fun i => (n.st₁ i).tag
  let hashLabel := fun i => (n.st₁ i).label
  let k₁ := fun i => treeStagesChallengeTail K (tag i) (hashLabel i)
    (treeStagesHalvingBody K (q.ctx₁ i) width j [] (v₁ i) (finish₁ i) (n.x₁ i))
  let k₂ := fun i => treeStagesChallengeTail K (tag i) (hashLabel i)
    (treeStagesHalvingBody K (q.ctx₂ i) width j [] (v₂ i) (finish₂ i) (n.x₂ i))
  have tags (i : C.Party) (hi : i ∉ D.1) : (n.st₂ i).tag = (n.st₁ i).tag :=
    (q.coinNext_tag K D rnd δ sent i).2.trans
      ((saved.tags i hi).symm.trans (q.coinNext_tag K D rnd δ sent i).1.symm)
  have labels (i : C.Party) (hi : i ∉ D.1) : (n.st₂ i).label = (n.st₁ i).label :=
    (n.lab₂ i hi).trans (n.lab₁ i hi).symm
  have next₁ (i : C.Party) (hi : i ∉ D.1) : n.next₁ i = k₁ i := by
    change treeStagesChallengeTail K (n.st₁ i).tag (n.st₁ i).label (q.body₁ i (n.x₁ i)) = _
    rw [body₁ i hi, saved.counts i hi, suffix]
  have next₂ (i : C.Party) (hi : i ∉ D.1) : n.next₂ i = k₂ i := by
    change treeStagesChallengeTail K (n.st₂ i).tag (n.st₂ i).label (q.body₂ i (n.x₂ i)) = _
    rw [body₂ i hi, saved.counts i hi, suffix, tags i hi, labels i hi]
  have coins₁ : treeSimCoinWaiting K D n.count coinRnd n.st₁ n.next₁ =
      treeSimCoinWaiting K D 1 coinRnd n.st₁ k₁ := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCoinWaiting, hi]
    · simp only [treeSimCoinWaiting, if_neg hi, next₁ i hi]
      rfl
  have coins₂ : treeSimCoinWaiting K D n.count coinRnd n.st₂ n.next₂ =
      treeSimCoinWaiting K D 1 coinRnd n.st₂ k₂ := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCoinWaiting, hi]
    · simp only [treeSimCoinWaiting, if_neg hi, next₂ i hi]
      rfl
  rw [left, right, treeStages_coin_partial_live K D n.live allLive,
    treeStages_coin_partial_live K D n.live allLive, coins₁, coins₂, ← state]
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_coin_round_factor, treeSim_coin_round_factor]
  simp only [treeStages_resumeAll_map, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeSim_local_streamRel_fixed prims D δ _ (treeStagesTwin swaps a.2) b.2 related))
  intro r₁ r₂ hr
  rw [hr.1.1]
  let base := (treeStagesTwin swaps a.2).1.1
  let out := treeSimCoinOutput K D 1 coinRnd r₂.1.2
  let live := treeStagesChallengeLive K base tag hashLabel (fun i => (out i).getD [])
    (fun i => (out i).map fun _ => ())
  let sampled := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) ((out i).getD [])).getD 0
  have base_le : base ≤ r₁.2.1.1 := treeSim_logged_grows prims D _ _ r₁ hr.2.1
  have fresh₁' : TreeSimFutureEmpty (q.label + 2) r₁.2.1.2 := by
    rw [hr.1.2.2.1]
    exact fresh₁
  have fresh₂' : TreeSimFutureEmpty (q.label + 2) r₂.2.2 := by
    rw [hr.1.2.2.2]
    exact fresh₂
  have corrupt (i : C.Party) (hi : i ∈ D.1) : out i = none := by simp [out, treeSimCoinOutput, hi]
  have honest (i : C.Party) (values : List E) (ho : out i = some values) : i ∉ D.1 :=
    fun hi => by rw [corrupt i hi] at ho; cases ho
  have covered (i : C.Party) (values : List E) (ho : out i = some values) :
      TreeStagesChallengeCovered K base (tag i) (hashLabel i) values := by
    exact treeTwin_reached_challengeCovered prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) p.2.1 p.2.2 seeds
      (tagLabels circuits settings tree parameter) (historyLimit circuits settings) r padding round a reach swaps
      _ _ (saved.address rnd δ sent i (honest i values ho)).2 values
      (treeStages_coinOutput_length K D 1 coinRnd r₂.1.2 i values ho)
  have finalCovered : TreeStagesChallengeCovered K base (q.st₁ q.pivotParty).tag (q.label + 5) [ĉ] :=
    finalAddress_covered prims K circuits settings top tree D A parameter seeds pairs p r padding
      q w saved finish round a reach swaps ĉ
  let guess := challengeAt K base (q.st₁ q.pivotParty).tag (q.label + 5) ĉ
  let s := sampled q.pivotParty
  have shifted := saved.outputShift rnd δ sent allLive
  have shifted' := shifted.congr_products K D q.ctx₁ q.ctx₂ _ _ _ _ _ _ products₁ products₂
  have shape' := halvFold_shape K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ width j v₁ v₂ _ _ shifted' s shape
  obtain ⟨eA, eB, e, shapeA, shapeB, shapeD⟩ := shape'
  let δ₀ := if ∀ i, i ∉ D.1 → live i = true then finalMaskDelta q.T₀ guess (eA 0) (eB 0) else 0
  have visible₀ : ∀ name, ¬ Hidden D name → δ₀ name = 0 := by
    dsimp only [δ₀]
    split
    · exact finalMaskDelta_visible D q.T₀ q.pivot.lacked guess (eA 0) (eB 0)
    · simp
  let blocks := finishingBlocks D q.ctx₁ live
  let qs := finishingKeys D q.ctx₁ live r₁.2.1.1
  have hiddenB : ∀ x ∈ blocks, Hidden D x.1 := by
    intro x hx
    obtain ⟨i, T, _, _, hidden, rfl⟩ := (finishingBlocks_mem D q.ctx₁ live x).mp hx
    exact hidden
  have freshQ : ∀ x ∈ qs, r₁.2.1.1 x = none := by
    intro x hx
    obtain ⟨i, T, _, _, _, empty, rfl⟩ := (finishingKeys_mem D q.ctx₁ live _ x).mp hx
    exact empty
  have lab₁ (i : C.Party) (hi : i ∉ D.1) : (nextLabel (n.st₁ i)).label = q.label + 2 := by
    change (n.st₁ i).label + 1 = _
    rw [n.lab₁ i hi]
    rfl
  have lab₂ (i : C.Party) (hi : i ∉ D.1) : (nextLabel (n.st₂ i)).label = q.label + 2 := by
    change (n.st₂ i).label + 1 = _
    rw [n.lab₂ i hi]
    rfl
  refine relTriple_bind (R := fun u v => ∃ δ',
    Round1EndP K circuits settings top tree D A parameter p.1.2 P ĉ (round + 1) δ'
      ((r₂.1.1, u.1), u.2) ((r₂.1.1, v.1), v.2)) ?_ (by
    intro u v huv
    obtain ⟨δ', result⟩ := huv
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨[], δ', fun x hx => by simp at hx, result⟩))
  apply prefill_pass_coupling prims K D (q.label + 2) 1 2 δ₀ blocks
    (Finset.nodup_toList _) hiddenB qs (Finset.nodup_toList _)
    (by
      intro x hx
      obtain ⟨i, T, _, _, _, _, rfl⟩ := (finishingKeys_mem D q.ctx₁ live _ x).mp hx
      rintro ⟨_, eq, _⟩
      cases eq)
    _ _ r₁.2 r₂.2 hr.1.2.1.1
    (fun x hx g => fresh₁' _ le_rfl) (fun x hx g => fresh₂' _ le_rfl) freshQ
    (by
      intro u hu
      exact finishing_prefill_reads prims K D (q.label + 2) q.ctx₁ q.ctx₁ width j v₁ finish₁ n.x₁
        (fun i => nextLabel (n.st₁ i)) tag hashLabel out base r₁.2 u base_le covered
        (fun i values ho => ⟨rfl, rfl, lab₁ i (honest i values ho)⟩) hu)
    (by
      intro u hu
      have reads := finishing_prefill_reads_stream prims K D (q.label + 2) q.ctx₂ q.ctx₁ width j v₂ finish₂ n.x₂
        (fun i => nextLabel (n.st₂ i)) tag hashLabel out base r₂.2 u
        (by rw [← hr.1.2.1.1]; exact base_le) covered
        (fun i values ho => ⟨(q.self₂ i (honest i values ho)).trans (q.self₁ i (honest i values ho)).symm,
          (q.keys i (honest i values ho)).symm, lab₂ i (honest i values ho)⟩) hu
      simpa only [qs, hr.1.2.1.1] using reads)
  intro h c₁ c₂ filled
  let f : FinalData K circuits settings top tree D parameter p.1.2 := {
    caller := w.caller
    claim₁ := fun i => treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 (sampled i)
    claim₂ := fun i => treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 (sampled i)
    w₁ := fun i => predictedTerms prims K D h c₁ (q.ctx₁ i) (q.label + 2) 1 2
    w₂ := fun i => predictedTerms prims K D h c₂ (q.ctx₁ i) (q.label + 2) 1 2 }
  let fv₁ := fun i => contextProductValues K (q.ctx₁ i) (finalProducts K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i))
  let fv₂ := fun i => contextProductValues K (q.ctx₂ i) (finalProducts K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i))
  let dt := termShift K D q.T₀ q.pivotParty (fv₁ - fv₂) (0 : C.Term → Fin 2 → E)
  let dp := pairShift q.pivotParty (pairDelta K D q.T₀ q.pivotParty (fv₁ - fv₂) (0 : C.Term → Fin 2 → E))
  let δ₁ := treeStagesMaskDelta D 2 dt dp
  have prefilledLe : r₁.2.1.1 ≤ h := prefilled_hash_le K D (q.label + 2) 1 2 δ₀ blocks qs
    _ _ _ _ _ _ filled freshQ
  have prefilledRel : PassRel K D (q.label + 2) δ₀ δ₁ r₁.2.1.2 r₂.2.2 h c₁ c₂
      ((h, c₁), r₁.2.2) (h, c₂) := by
    refine ⟨⟨rfl, ?_⟩, le_rfl, le_rfl, le_rfl⟩
    exact prefilled_twoField K D (q.label + 2) 1 2 (q.label + 2 + 1) 0 2 δ₀ δ₁ blocks qs
      r₁.2.1.1 h r₁.2.1.2 r₂.2.2 c₁ c₂ filled hiddenB (by omega) fresh₁' fresh₂' (by omega)
  have reads (i : C.Party) (values : List E) (ch : E) (ho : out i = some values)
      (hs : treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some ch) :=
    finishing_prefilled_terms K D (q.label + 2) δ₀ q.ctx₁ live r₁.2.1.1 h r₁.2.1.2 r₂.2.2 c₁ c₂
      filled i ((finishing_live_iff K base tag hashLabel out i).mpr ⟨values, ch, ho, hs⟩)
  apply relTriple_post_mono (finishing_prefilled_pass prims K D (q.label + 2) δ₀ δ₁ r₁.2.1.2 r₂.2.2
    h c₁ c₂ visible₀ (treeStagesMaskDelta_visible D 2 dt dp) q.ctx₁ q.ctx₂ q.self₁ q.self₂ q.keys
    width j v₁ v₂ finish₁ finish₂ n.x₁ n.x₂ (fun i => nextLabel (n.st₁ i))
    (fun i => nextLabel (n.st₂ i)) lab₁ lab₂ tag hashLabel out corrupt base
    (base_le.trans prefilledLe) covered
    (fun i values ch ho hs T ht hh g => ((reads i values ch ho hs).1 T ht hh g).1)
    (fun i values ch ho hs T ht hh g => ((reads i values ch ho hs).1 T ht hh g).2)
    (fun i values ch ho hs => (reads i values ch ho hs).2)
    ((h, c₁), r₁.2.2) (h, c₂) prefilledRel)
  intro u v result
  obtain ⟨⟨fieldRnd, step₁, step₂⟩, masks, caches⟩ := result
  let δ' := twoFieldCacheDelta D (q.label + 2) 1 2 (q.label + 2 + 1) 0 2 δ u.2.1.2 v.2.2
  let d := treeStagesExtendMultData K D q.T₀ q.pivotParty q.pivot δ' 2 q.ctx₁ q.ctx₂ q.self₁ q.self₂
    fieldRnd fv₁ fv₂ (fun i => nextLabel (nextLabel (n.st₁ i))) (fun i => nextLabel (nextLabel (n.st₂ i)))
    (fun i => finalAfterField K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i) (finish₁ i))
    (fun i => finalAfterField K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i) (finish₂ i))
  have steps₁ : u.1 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ := step₁
  have steps₂ : v.1 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ := by
    rw [step₂]
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
    · have shift := treeStages_prssFieldShift_mask D (q.ctx₁ i)
        (by simpa only [q.self₁ i hi] using hi) 2 dt dp
      rw [q.self₁ i hi] at shift
      simp only [d, treeStagesExtendMultData, treeSimExtendMultPartial, treeSimExtendMultWaiting, if_neg hi]
      split
      · rw [shift]
      · rfl
  have stream : TreeSimStreamRel δ' u.2 v.2 :=
    ⟨caches.1.1, twoFieldCaches_related K D _ _ _ _ _ _ δ₀ δ₁ δ _ _ _ _ caches.1.2 hr.1.2.1.2⟩
  have frames : Frames D A (q.label + 4) δ' ((r₂.1.1, u.1), u.2) ((r₂.1.1, v.1), v.2) := by
    refine ⟨twoFieldCacheDelta_visible D _ _ _ _ _ _ δ _ _ visibleOld,
      twoFieldCacheDelta_future D _ _ _ _ _ _ _ δ _ _ (by omega) (by omega)
        (fun x hx => future x (by omega)), ?_⟩
    exact twoFieldCaches_future K D _ _ _ _ _ _ _ δ₀ δ₁ _ _ _ _ caches.1.2 (by omega) (by omega)
      (fun x hx => fresh₁' x (by omega)) (fun x hx => fresh₂' x (by omega))
  have flags := treeTwin_flags_of_sameKind D u.1 v.1 (fun i hi => by
    rw [steps₁, steps₂]
    exact treeTwin_sameKind_extendPartial K D _ _ _ _ _ _ _ _ _ _ _ _ i hi)
  refine ⟨δ', stream, rfl, flags.1, flags.2, ?_⟩
  by_cases full : ∀ i, i ∉ D.1 → live i = true
  · have sampled_eq (i : C.Party) (hi : i ∉ D.1) : sampled i = s := by
      obtain ⟨values, ch, oi, ci⟩ := (finishing_live_iff K base tag hashLabel out i).mp (full i hi)
      obtain ⟨values', ch', op, cp⟩ := (finishing_live_iff K base tag hashLabel out q.pivotParty).mp
        (full q.pivotParty q.pivot.honest)
      have vals := coinOutput_agree K D 1 coinRnd r₂.1.2 hi q.pivot.honest oi op
      have addr : (tag i, hashLabel i) = (tag q.pivotParty, hashLabel q.pivotParty) :=
        (saved.address rnd δ sent i hi).1.trans
          (saved.address rnd δ sent q.pivotParty q.pivot.honest).1.symm
      obtain ⟨tags', labels'⟩ := Prod.mk.inj addr
      simp only [sampled, s, oi, op, Option.getD_some, vals, tags', labels']
    have claim₁ (i : C.Party) (hi : i ∉ D.1) : f.claim₁ i =
        treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 s := by
      change treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 (sampled i) = _
      rw [sampled_eq i hi]
    have claim₂ (i : C.Party) (hi : i ∉ D.1) : f.claim₂ i =
        treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 s := by
      change treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 (sampled i) = _
      rw [sampled_eq i hi]
    have hist₁ : CommonHistory D (fun _ => true) n.st₁ := by
      exact commonHistory_extendMult K D q.ctx₁ q.self₁ q.count rnd (fun i => contextProductValues K (q.ctx₁ i) (q.products₁ i)) q.st₁ (q.k₁ K D) sent n.x₁
        (fun i hi => by
          have hl : n.live i = true := allLive i hi
          simpa only [if_neg hi, hl, ↓reduceIte] using n.shape₁ i) saved.history₁
    have hist₂ : CommonHistory D (fun _ => true) n.st₂ := by
      exact commonHistory_extendMult K D q.ctx₂ q.self₂ q.count (q.data K D rnd δ).rnd₂ (fun i => contextProductValues K (q.ctx₂ i) (q.products₂ i)) q.st₂
        (q.k₂ K D) sent n.x₂
        (fun i hi => by
          have hl : n.live i = true := allLive i hi
          simpa only [if_neg hi, hl, ↓reduceIte] using n.shape₂ i) saved.history₂
    have leFinal : base ≤ u.2.1.1 := base_le.trans (prefilledLe.trans caches.2.1)
    refine Or.inr (Or.inr ⟨q, w, rnd, δ, sent, s, j, v₁, v₂, f, d,
      savedOffset w.caller.rest.circs w.phase + 3, saved, carried, phase, finish, allLive, rfl,
      (fun i hi => ⟨claim₁ i hi, claim₂ i hi⟩), (fun _ _ => ⟨rfl, rfl⟩),
      treeStages_challengeCovered_mono K leFinal _ _ _ finalCovered, ?_⟩)
    refine ⟨saved.ctx₁, saved.ctx₂, rfl, ?_, ?_, rfl, rfl,
      finishing_offset saved finish rnd δ sent allLive, ?_, hist₁, hist₂,
      frames, rfl, ?_, steps₁.trans (extendMultPartial_allLive K D _ _ _ _ _ _ _ full),
      steps₂.trans (extendMultPartial_allLive K D _ _ _ _ _ _ _ full)⟩
    · change fv₁ = fun i => contextProductValues K (q.ctx₁ i)
        (f.products₁ K circuits settings top tree D parameter p.1.2 i)
      unfold FinalData.products₁
      change fv₁ = fun i => contextProductValues K (q.ctx₁ i)
        (finalProducts K (w.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i))
      rw [← saved.ctx₁]
    · change fv₂ = fun i => contextProductValues K (q.ctx₂ i)
        (f.products₂ K circuits settings top tree D parameter p.1.2 i)
      unfold FinalData.products₂
      change fv₂ = fun i => contextProductValues K (q.ctx₂ i)
        (finalProducts K (w.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i))
      rw [← saved.ctx₂]
    · intro i hi
      exact ⟨(tags i hi).symm, by change (n.st₁ i).label + 1 + 1 = q.label + 3; rw [n.lab₁ i hi]; rfl,
        by change (n.st₂ i).label + 1 + 1 = q.label + 3; rw [n.lab₂ i hi]; rfl⟩
    · intro allHist rr hrr i hi o₁ o₂ ho k hk
      have guessEq : guess = some rr := by
        change challengeAt K base (q.st₁ q.pivotParty).tag (q.label + 5) ĉ = some rr
        rw [challengeAt_mono K leFinal _ _ _ finalCovered]
        exact hrr
      have rrne := challengeAt_some K base (q.st₁ q.pivotParty).tag (q.label + 5) ĉ rr guessEq
      have nonzero : 1 + rr ≠ 0 := by
        letI : CharP E 2 := charTwo
        intro eq
        apply rrne.2
        have h2 : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
        linear_combination eq - h2
      let c₁' := fun i => treeStagesHalvingUpdate K (q.ctx₁ i) width j (v₁ i) (n.x₁ i).1 s
      let c₂' := fun i => treeStagesHalvingUpdate K (q.ctx₂ i) width j (v₂ i) (n.x₂ i).1 s
      have relation : HalvRel K D 1 (fun i => (c₁' i).1) (fun i => (c₁' i).2.1)
          (fun i => (c₂' i).1) (fun i => (c₂' i).2.1) (fun i => (c₁' i).2.2) (fun i => (c₂' i).2.2) := by
        letI : CharP E 2 := charTwo
        have h := halvFold_rel K D q.ctx₁ q.ctx₂ q.self₁ q.self₂ width j v₁ v₂ _ _ shifted' s
          (rel (finishing_history_before rnd δ sent allLive allHist))
        rw [Function.iterate_succ_apply', saved.finishing_length finish j v₁ v₂ phase] at h
        exact h
      have maskEq (j : C.Party) (hj : j ∉ D.1) :
          f.w₂ j = f.w₁ j + (treeStagesPrssFieldShift (q.ctx₁ j) 2
            (finalMaskDelta q.T₀ (some rr) (eA 0) (eB 0))).1 := by
        have m := masks j (full j hj)
        simpa only [δ₀, if_pos full, guessEq] using m
      have ma (j : C.Party) (hj : j ∉ D.1) : conv K (q.ctx₂ j) (f.w₂ j) 0 =
          conv K (q.ctx₁ j) (f.w₁ j) 0 + rr / (1 + rr) * ((c₁' j).1 0 - (c₂' j).1 0) := by
        rw [conv_self K _ j (q.self₂ j hj), ← conv_self K (q.ctx₁ j) j (q.self₁ j hj), maskEq j hj]
        rw [(finalMaskDelta_conv K D q.T₀ q.pivot.lacked (q.ctx₁ j) j (q.self₁ j hj)
          rr (eA 0) (eB 0) (f.w₁ j)).1, shapeA j hj 0]
      have mb (j : C.Party) (hj : j ∉ D.1) : conv K (q.ctx₂ j) (f.w₂ j) 1 =
          conv K (q.ctx₁ j) (f.w₁ j) 1 + rr / (1 + rr) * ((c₁' j).2.1 0 - (c₂' j).2.1 0) := by
        rw [conv_self K _ j (q.self₂ j hj), ← conv_self K (q.ctx₁ j) j (q.self₁ j hj), maskEq j hj]
        rw [(finalMaskDelta_conv K D q.T₀ q.pivot.lacked (q.ctx₁ j) j (q.self₁ j hj)
          rr (eA 0) (eB 0) (f.w₁ j)).2, shapeB j hj 0]
      let out₁ := fun _ : C.Party => o₁
      let out₂ := fun j => treeSimFieldHeldShift D j 2
        (fun g => ∑ l ∈ univ.filter (· ∉ D.1), (fv₁ l g - fv₂ l g)) o₁
      have output : OutputShift K D q.ctx₁ q.ctx₂
          (fun i => finalProducts K (q.ctx₁ i) (c₁' i) (f.w₁ i))
          (fun i => finalProducts K (q.ctx₂ i) (c₂' i) (f.w₂ i)) out₁ out₂ := by
        apply OutputShift.congr_products K D q.ctx₁ q.ctx₂
          (fun i => finalProducts K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i))
          (fun i => finalProducts K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i)) _ _ out₁ out₂
          (fun _ _ => rfl)
        · intro j hj
          rw [claim₁ j hj]
        · intro j hj
          rw [claim₂ j hj]
      have eq := guess_conjunct K D q.T₀ q.pivot.lacked q.ctx₁ q.ctx₂ q.self₁ q.self₂
        c₁' c₂' f.w₁ f.w₂ rr e nonzero relation shapeD ma mb out₁ out₂ output i hi k hk
      change finalVector K (q.ctx₁ i) (f.claim₁ i) (f.w₁ i) o₁ rr k =
        finalVector K (q.ctx₂ i) (f.claim₂ i) (f.w₂ i) o₂ rr k
      rw [claim₁ i hi, claim₂ i hi, ho]
      exact eq
  · push Not at full
    exact Or.inr (Or.inl ⟨d, live, full, rfl, steps₁, steps₂⟩)

end ThresholdLeanXmssSecurity.TreeTwinGuessCarry

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessCarry.finishingCoinLiveP_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinGuessCarry.finishingCoinLiveP_forget

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessCarry.guessFieldPlusP_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinGuessCarry.guessFieldPlusP_forget

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessCarry.round1EndP_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinGuessCarry.round1EndP_forget

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinGuessCarry.finishingRoundP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinGuessCarry.finishingRoundP
