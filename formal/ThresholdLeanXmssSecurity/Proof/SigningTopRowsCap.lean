import ThresholdLeanXmssSecurity.Proof.SigningTopRows
import ThresholdLeanXmssSecurity.Proof.SigningCappedExpect

/-!
# The cap of the unopened top target

This module puts `unopenedTopTarget` (`SigningTopRows`) into the one input-side target of the
uncharged lane, so that `TopRow` and `AbsentRow` share the cap `q / 2^128` of `InputHitRow`.

## The release of a top key

* A `.tree b` call that returns a tree has resolved the bottom ceremony of
  `b` on the cache (`tree_release_resolves`). Stored trees retain their counted construction
  witnesses; the handler answers `none` when its memoized result has no bottom tree
  (`flagged_tree_answer`, `Ideal.lean`, `tsigOracles`).
* `releaseOracles` adds a ghost bit that a `.tree b` call with a returned tree sets.
  `releaseFinalRun_forget` shows that the bit changes no real call.
* When `TopUnopened` holds on the final cache, the bit is false (`exposedRun_unreleased`). So no
  call of the run, before or after a candidate, released the top signature of `b`. `.round2` returns
  bottom values only, and `TopTree` holds only the chain ends (`SigningTopRows`). So a hybrid
  of the coupling never has to reveal the target values. Lean checks only the release bit.

## One target, one charge

* `laneChainTarget` merges `partialChainTarget` and `unopenedTopTarget`. Both give the honest top
  value of the forged top key at a position, so they agree where both are set
  (`partial_unopened_agree`).
* So the lane target has one value for each hidden key. `hiddenCandidate` gives at most one
  candidate for each call, and each call is charged at most once.
* A hit on the lane target is a hit on one of the two parts (`hiddenInputHit_lane_iff`).
* The three rows of `UnchargedRow` are one row, `LaneInputRow` (`probEvent_unchargedRow_le`). The
  assembly uses it in place of `InputHitRow` (`unchargedRow_add_le`), with no sum over the rows.

## The cap

`unchargedRow_le_of_coupling` gives `q / 2^128` for `UnchargedRow` through
`SigningCappedExpectProof.probEvent_le_of_capped_expect`. Its one premise is `LaneInputCoupling`,
the coupling of `LaneInputRow` into the capped hybrid. Like
`GuardedFlagCoupling` and `InputCachedLaneCap`, it is an explicit coupling hypothesis. In the hybrid, the hidden top chain values of
`b` are secrets that the hybrid reveals only at a `.tree b` call that returns a tree, and the setup
walks of these chains take pending answers. This cap spends the whole `q / 2^128`, so it is not
summed with another row. A row on the same capped hybrid goes through `unchargedRow_add_le`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningTopRowsCapProof

open LeanXmss ThresholdLeanXmss SigningOpeningProof SigningUnchargedLoggedProof SigningAssemblyProof
  SigningTopRowsProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

set_option maxRecDepth 100000 in
/-- The `.tree b` handler reads or builds its memoized bottom tree, and preserves the returned state. -/
theorem flagged_tree_answer (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (s : TsigState C × Bool) :
    ∃ k, (SigningCoreProof.flaggedOracles x (SigningHitProof.actualDealt x top) (.inr (.tree b))).run s =
        (bottomOnce (SigningHitProof.actualDealt x top) b).run s.1 >>= k ∧
      ∀ st, k (none, st) = pure (none, st, s.2) := by
  refine ⟨?k, ?eq, ?none⟩
  case eq =>
    simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, tsigOracles,
      StateT.run_bind, map_bind]
    rfl
  case none =>
    intro st
    rfl

/-- A larger cache keeps a resolved bottom ceremony, so `TopUnopened` passes to a smaller cache. -/
theorem topUnopened_anti (x : SigningSecurityProof.Keys3 C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    {cache larger : HashCache C} (hle : cache ≤ larger) (h : TopUnopened x larger top b) :
    TopUnopened x cache top b :=
  fun ⟨tree, hres⟩ => h ⟨tree, hres.mono hle⟩

set_option maxRecDepth 100000 in
/-- A `.tree b` call that returns a tree leaves its bottom ceremony resolved on the cache. -/
theorem tree_release_resolves (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (s : TsigState C × Bool) (initial : HashCache C × ℕ)
    (r : (Option (BottomTree × Digest) × TsigState C × Bool) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((SigningCoreProof.flaggedOracles x (SigningHitProof.actualDealt x top) (.inr (.tree b))).run s)).run
        initial))
    (hstored : SigningGuessProof.StoredTreeRuns prims x top initial.1 s.1)
    (hsome : r.1.1.isSome) : ¬TopUnopened x r.2.1 top b := by
  obtain ⟨k, hk, hnone⟩ := flagged_tree_answer x top b s
  rw [hk] at hr
  obtain ⟨call, hc, htail⟩ := SigningCacheProof.run_bind_support prims _ _ initial r hr
  cases hb : call.1.1 with
  | none =>
    have he : call.1 = (none, call.1.2) := Prod.ext hb rfl
    rw [he, hnone] at htail
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at htail
    subst r
    simp at hsome
  | some tree =>
    obtain ⟨start, built, hbuilt, hout, hle⟩ := SigningSelectionProof.bottomOnce_tree_runs
      prims x top b s.1 initial hstored call hc tree hb
    rw [← SigningHitProof.hashEmbed_referenceTree] at hbuilt
    have hres := SigningHitProof.run_hashEmbed_resolves prims _ start built hbuilt
    intro hun
    exact hun ⟨tree, hout ▸ hres.mono
      (hle.trans (SigningCacheProof.countRun_grows prims _ _ r htail))⟩

/-- The ghost bit of a tree release. A `.tree b` call that returns a tree sets it. -/
def treeReleased (b : Fin (2 ^ layerHeight)) :
    (t : (LocalSpec C + TsigSpec C).Domain) → (LocalSpec C + TsigSpec C).Range t → Bool
  | .inr (.tree b'), a => decide (b' = b) && a.isSome
  | _, _ => false

/-- `flaggedOracles` with the ghost bit of a release of tree `b`. All real calls are unchanged. -/
def releaseOracles (x : SigningSecurityProof.Keys3 C) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT ((TsigState C × Bool) × Bool) (OracleComp (WorldSpec C))) :=
  fun t => StateT.mk fun p =>
    (fun z => (z.1, (z.2, p.2 || treeReleased b t z.1))) <$>
      (SigningCoreProof.flaggedOracles x (SigningHitProof.actualDealt x top) t).run p.1

theorem releaseRun_forget {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : TsigState C × Bool) (released : Bool) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (releaseOracles x top b) oa).run (s, released) =
      (simulateQ (SigningCoreProof.flaggedOracles x (SigningHitProof.actualDealt x top)) oa).run s :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun t s released => by simp [releaseOracles, Functor.map_map]) oa s released

set_option maxRecDepth 100000 in
theorem releaseOracles_storedTreeRuns (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (t : (LocalSpec C + TsigSpec C).Domain)
    (p : (TsigState C × Bool) × Bool) (initial : HashCache C × ℕ)
    (hinv : SigningGuessProof.StoredTreeRuns prims x top initial.1 p.1.1)
    (r : ((LocalSpec C + TsigSpec C).Range t × ((TsigState C × Bool) × Bool)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((releaseOracles x top b t).run p)).run initial)) :
    SigningGuessProof.StoredTreeRuns prims x top r.2.1 r.1.2.1.1 := by
  simp only [releaseOracles, StateT.run_mk, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  apply SigningSelectionProof.gameOracles_storedTreeRuns prims x top t p.1.1 initial hinv
    ((v.1.1, v.1.2.1), v.2)
  rw [← SigningCoreProof.flaggedOracles_forget x _ t p.1.1 p.1.2,
    simulateQ_map, StateT.run_map, support_map]
  exact ⟨v, hv, rfl⟩

set_option maxRecDepth 100000 in
/-- One call keeps the release certificate. A set bit gives a resolved bottom ceremony. -/
theorem releaseOracles_resolves (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (t : (LocalSpec C + TsigSpec C).Domain)
    (p : (TsigState C × Bool) × Bool) (initial : HashCache C × ℕ)
    (hstored : SigningGuessProof.StoredTreeRuns prims x top initial.1 p.1.1)
    (hp : p.2 = true → ¬TopUnopened x initial.1 top b)
    (r : ((LocalSpec C + TsigSpec C).Range t × ((TsigState C × Bool) × Bool)) × (HashCache C × ℕ))
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((releaseOracles x top b t).run p)).run initial)) :
    r.1.2.2 = true → ¬TopUnopened x r.2.1 top b := by
  simp only [releaseOracles, StateT.run_mk, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  simp only [Bool.or_eq_true]
  rintro (hprevious | hrelease)
  · exact fun h => hp hprevious
      (topUnopened_anti x top b (SigningCacheProof.countRun_grows prims _ _ v hv) h)
  · rcases t with t | (i | b' | _ | _)
    · simp [treeReleased] at hrelease
    · simp [treeReleased] at hrelease
    · simp only [treeReleased, Bool.and_eq_true, decide_eq_true_eq] at hrelease
      obtain ⟨rfl, hsome⟩ := hrelease
      exact tree_release_resolves prims x top b' p.1 initial v hv hstored hsome
    · simp [treeReleased] at hrelease
    · simp [treeReleased] at hrelease

set_option maxRecDepth 100000 in
/-- The release certificate holds through an adaptive adversary. -/
theorem releaseRun_resolves {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ (p : (TsigState C × Bool) × Bool) (initial : HashCache C × ℕ),
      SigningGuessProof.StoredTreeRuns prims x top initial.1 p.1.1 →
      (p.2 = true → ¬TopUnopened x initial.1 top b) →
      ∀ r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((simulateQ (releaseOracles x top b) oa).run p)).run initial),
        r.1.2.2 = true → ¬TopUnopened x r.2.1 top b := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro p initial hstored hp r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hp
  | query_bind t k ih =>
    intro p initial hstored hp r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    exact ih v.1.1 v.1.2 v.2
      (releaseOracles_storedTreeRuns prims x top b t p initial hstored v hv)
      (releaseOracles_resolves prims x top b t p initial hstored hp v hv) r hr

/-- `finalRun` with the ghost bit of a release of tree `b`. -/
def releaseFinalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    OracleComp (WorldSpec C) (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × Bool) := do
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top
    | pure (((false, false), none), false)
  let r ← (simulateQ (releaseOracles x top b) (A ⟨top.root, x.1⟩ top)).run
    ((SigningCoreProof.tsigInit, false), false)
  (fun w => (((w.1, r.2.1.2), some (top, w.2.1, w.2.2)), r.2.2)) <$>
    SigningCoreProof.tsigFinish (SigningHitProof.actualDealt x top) (r.1, r.2.1.1)

set_option maxRecDepth 100000 in
theorem releaseFinalRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    Prod.fst <$> releaseFinalRun A x b = SigningDescentProof.finalRun A x := by
  unfold releaseFinalRun SigningDescentProof.finalRun
  rw [map_bind]
  apply bind_congr
  intro output
  rcases output with _ | (top | bottom)
  · simp
  · simp only [map_bind, Functor.map_map]
    erw [← releaseRun_forget x top b (A ⟨top.root, x.1⟩ top) (SigningCoreProof.tsigInit, false) false,
      bind_map_left]
  · simp

set_option maxRecDepth 100000 in
open SigningCacheProof in
/-- A set release bit leaves the bottom ceremony of `b` resolved on the final cache, after the
verification and the freshness check. -/
theorem releaseFinalRun_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) (initial : HashCache C × ℕ)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × Bool) × (HashCache C × ℕ))
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (releaseFinalRun A x b)).run initial))
    (hrelease : r.1.2 = true) :
    ∃ top state forgery, r.1.1.2 = some (top, state, forgery) ∧ ¬TopUnopened x r.2.1 top b := by
  unfold releaseFinalRun at hr
  obtain ⟨p, hp, hr⟩ := run_bind_support prims _ _ initial r hr
  rcases hp1 : p.1 with _ | (top | bottom)
  · rw [hp1] at hr
    simp at hr
    subst hr
    cases hrelease
  swap
  · rw [hp1] at hr
    simp at hr
    subst hr
    cases hrelease
  rw [hp1] at hr
  obtain ⟨q, hq, hr⟩ := run_bind_support prims _ _ p.2 r hr
  have hresolved := releaseRun_resolves prims x top b (A ⟨top.root, x.1⟩ top)
    ((SigningCoreProof.tsigInit, false), false) p.2
    (by simp [SigningGuessProof.StoredTreeRuns, SigningCoreProof.tsigInit]) (by simp) q hq
  have hgrow := countRun_grows prims _ _ r hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact ⟨top, w.1.2.1, w.1.2.2, rfl, fun h => hresolved hrelease (topUnopened_anti x top b hgrow h)⟩

set_option maxRecDepth 100000 in
/-- At an outcome of `exposedRun` where the bottom ceremony of `b` is unopened on
the final cache, no `.tree b` call of the run returned a tree. So the game never released the top
signature of `b`, and the top chain values of `b` below the end stayed hidden for the whole run. -/
theorem exposedRun_unreleased (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningCostProof.Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.2 = some (top, state, forgery))
    (b : Fin (2 ^ layerHeight)) (hopen : TopUnopened x r.2.1 top b) :
    ∃ v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (releaseFinalRun A x b)).run
        ((∅ : HashCache C), 0)),
      (v.1.1, v.2) = r ∧ v.1.2 = false := by
  unfold SigningDescentProof.exposedRun at hr
  rw [← releaseFinalRun_forget A x b, simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨v, hv, hvr⟩ := hr
  refine ⟨v, hv, hvr, ?_⟩
  cases hb : v.1.2
  · rfl
  obtain ⟨top', state', forgery', hm', hres⟩ := releaseFinalRun_resolves prims A x b _ v hv hb
  have hv1 : v.1.1.2 = r.1.2 := by rw [← hvr]
  rw [hv1, hm] at hm'
  cases hm'
  exact (hres (by rw [show v.2 = r.2 by rw [← hvr]]; exact hopen)).elim

/-! ## One target for the input side -/

/-- Two chain targets in one. The first target wins where both are set. -/
def mergeTarget (first second : HiddenKey → Option Digest) : HiddenKey → Option Digest :=
  fun key => (first key).or (second key)

/-- A hit on a merged target is a hit on one of its parts. -/
theorem hiddenInputHit_of_merge (x : SigningSecurityProof.Keys3 C) (first second : HiddenKey → Option Digest)
    (r : SigningGuessLinkProof.LoggedOutcome C) (h : HiddenInputHit x (mergeTarget first second) r) :
    HiddenInputHit x first r ∨ HiddenInputHit x second r := by
  obtain ⟨c, hc, ht⟩ := h
  rcases c with ⟨key, d⟩
  cases key with
  | opening lay e => exact Or.inl ⟨_, hc, ht⟩
  | bottomChain e l p =>
    simp only [hiddenTarget, mergeTarget] at ht
    cases hf : first (.bottomChain e l p) with
    | none => rw [hf, Option.none_or] at ht; exact Or.inr ⟨_, hc, ht⟩
    | some v => rw [hf, Option.some_or] at ht; exact Or.inl ⟨_, hc, hf.trans ht⟩
  | topChain b l p =>
    simp only [hiddenTarget, mergeTarget] at ht
    cases hf : first (.topChain b l p) with
    | none => rw [hf, Option.none_or] at ht; exact Or.inr ⟨_, hc, ht⟩
    | some v => rw [hf, Option.some_or] at ht; exact Or.inl ⟨_, hc, hf.trans ht⟩

/-- A hit on the first part is a hit on the merged target. -/
theorem hiddenInputHit_merge_left (x : SigningSecurityProof.Keys3 C) (first second : HiddenKey → Option Digest)
    (r : SigningGuessLinkProof.LoggedOutcome C) (h : HiddenInputHit x first r) :
    HiddenInputHit x (mergeTarget first second) r := by
  obtain ⟨c, hc, ht⟩ := h
  refine ⟨c, hc, ?_⟩
  rcases c with ⟨key, d⟩
  cases key with
  | opening lay e => exact ht
  | bottomChain e l p =>
    simp only [hiddenTarget, mergeTarget] at ht ⊢
    rw [ht, Option.some_or]
  | topChain b l p =>
    simp only [hiddenTarget, mergeTarget] at ht ⊢
    rw [ht, Option.some_or]

/-- A hit on the second part is a hit on the merged target, when the two parts agree where both
are set. -/
theorem hiddenInputHit_merge_right (x : SigningSecurityProof.Keys3 C) (first second : HiddenKey → Option Digest)
    (hagree : ∀ key d d', first key = some d → second key = some d' → d = d')
    (r : SigningGuessLinkProof.LoggedOutcome C) (h : HiddenInputHit x second r) :
    HiddenInputHit x (mergeTarget first second) r := by
  obtain ⟨c, hc, ht⟩ := h
  refine ⟨c, hc, ?_⟩
  rcases c with ⟨key, d⟩
  cases key with
  | opening lay e => exact ht
  | bottomChain e l p =>
    simp only [hiddenTarget, mergeTarget] at ht ⊢
    cases hf : first (.bottomChain e l p) with
    | none => rw [Option.none_or]; exact ht
    | some v => rw [Option.some_or, hagree _ _ _ hf ht]
  | topChain b l p =>
    simp only [hiddenTarget, mergeTarget] at ht ⊢
    cases hf : first (.topChain b l p) with
    | none => rw [Option.none_or]; exact ht
    | some v => rw [Option.some_or, hagree _ _ _ hf ht]

/-- The partial chain target and the unopened target agree where both are set. Both give the honest
top chain value of the forged top key at the same position. So the merged target has one value
for each hidden key, and a call is charged at most once. -/
theorem partial_unopened_agree (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (key : HiddenKey) (d d' : Digest)
    (h : SigningGuardedFlagProof.partialChainTarget prims x r key = some d)
    (h' : unopenedTopTarget prims x r key = some d') : d = d' := by
  unfold SigningGuardedFlagProof.partialChainTarget at h
  split_ifs at h
  unfold SigningGuessLinkProof.chainTarget at h
  unfold unopenedTopTarget at h'
  rcases hm : r.1.1.2 with _ | ⟨top, state, forgery⟩
  · simp [hm] at h'
  simp only [hm] at h h'
  cases key with
  | opening lay e => simp at h'
  | bottomChain e l p => simp at h'
  | topChain b l p =>
    simp only at h h'
    split_ifs at h h'
    exact Option.some.inj (h.symm.trans h')

/-- The input-side target of the uncharged lane. It is the partial chain target, and the unopened
top target where the partial one is unset. -/
def laneChainTarget (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C) :
    HiddenKey → Option Digest :=
  mergeTarget (SigningGuardedFlagProof.partialChainTarget prims x r) (unopenedTopTarget prims x r)

/-- The input-side row on the lane target. -/
def LaneInputRow (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  Win w ∧ ¬Charged prims x w ∧ HiddenInputHit x (laneChainTarget prims x (w.1, w.2.1)) (w.1, w.2.1)

/-- The lane target splits into its two parts. -/
theorem hiddenInputHit_lane_iff (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C) :
    HiddenInputHit x (laneChainTarget prims x r) r ↔
      HiddenInputHit x (SigningGuardedFlagProof.partialChainTarget prims x r) r ∨
        HiddenInputHit x (unopenedTopTarget prims x r) r :=
  ⟨hiddenInputHit_of_merge x _ _ r, fun h => h.elim (hiddenInputHit_merge_left x _ _ r)
    (hiddenInputHit_merge_right x _ _ (partial_unopened_agree prims x r) r)⟩

set_option maxRecDepth 100000 in
/-- Each row of the uncharged lane is the one input-side row on the lane target. -/
theorem laneInputRow_of_unchargedRow (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (w : JointOutcome C) (hw : w ∈ support (jointRun prims A x)) (hrow : UnchargedRow prims x w) :
    LaneInputRow prims x w := by
  rcases hrow with ⟨hwin, hc, hhit⟩ | htop | habsent
  · exact ⟨hwin, hc, (hiddenInputHit_lane_iff prims x _).mpr (Or.inl hhit)⟩
  · exact ⟨htop.1, htop.2.1, (hiddenInputHit_lane_iff prims x _).mpr
      (Or.inr (topRow_hit prims A x w hw htop))⟩
  · exact ⟨habsent.1, habsent.2.1, (hiddenInputHit_lane_iff prims x _).mpr
      (Or.inr (absentRow_hit prims A x w hw habsent))⟩

set_option maxRecDepth 100000 in
/-- The three rows of the uncharged lane cost no more than the one input-side row. -/
theorem probEvent_unchargedRow_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[UnchargedRow prims x | jointRun prims A x] ≤ Pr[LaneInputRow prims x | jointRun prims A x] :=
  probEvent_mono fun w hw h => laneInputRow_of_unchargedRow prims A x w hw h

set_option maxRecDepth 100000 in
/-- A bound on the one input-side row and another term is a bound on the three rows and that term. -/
theorem unchargedRow_add_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (P bound : ℝ≥0∞)
    (h : Pr[LaneInputRow prims x | jointRun prims A x] + P ≤ bound) :
    Pr[UnchargedRow prims x | jointRun prims A x] + P ≤ bound :=
  (add_le_add (probEvent_unchargedRow_le prims A x) le_rfl).trans h

/-! ## The cap -/

open SigningCappedExpectProof in
/-- The coupling of the input-side row on the lane target into one capped hybrid. It is the
`hcouple` premise of `SigningCappedExpectProof.probEvent_le_of_capped_expect`, with its other
premises. The secrets of the hybrid are the openings and the hidden chain values. A top chain value
of `b` is revealed only at a `.tree b` call that returns a tree (`exposedRun_unreleased`). -/
def LaneInputCoupling : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    ∃ (κ σ β K : Type) (spec : OracleSpec κ) (_ : Fintype K) (_ : DecidableEq K)
      (_ : SampleableType (K → Digest)) (impl : QueryImpl spec (StateT σ ProbComp))
      (inputSide p : κ → Prop) (keyOf : κ → K) (point : κ → Digest)
      (Inv : σ × ℕ → Prop) (f : σ × ℕ → ℝ≥0∞) (E : σ × ℕ → Prop)
      (oa : OracleComp (spec + RevealSpec K Digest) β) (σ₀ : σ),
      (∀ t st, Inv st → ∀ y ∈ support ((countImpl impl p t).run st), Inv y.2) ∧
      (∀ t st, Inv st →
        ∑' y, Pr[= y | (countImpl impl p t).run st] * f y.2 ≤
          f st + if cappedCall p q t st ∧ ¬inputSide t then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) ∧
      (∀ st, E st → 1 ≤ f st) ∧ Inv (σ₀, 0) ∧ f (σ₀, 0) = 0 ∧
      Pr[LaneInputRow prims x | jointRun prims A x] ≤
        Pr[fun r => r.2.2.2 = true ∨ E r.2.1 | $ᵗ (K → Digest) >>= fun s =>
          (simulateQ (cappedHybrid impl inputSide p keyOf point q s) oa).run
            ((σ₀, 0), fun _ => none, false)]

set_option maxRecDepth 100000 in
open SigningCappedExpectProof in
/-- The three rows of the uncharged lane, `InputHitRow`, `TopRow` and `AbsentRow`, share the one cap
`q / 2^128` of the lane target. -/
theorem unchargedRow_le_of_coupling (hcouple : LaneInputCoupling (C := C) prims) (A : TsigAdversary C)
    (q : ℕ) (x : SigningSecurityProof.Keys3 C) (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr[UnchargedRow prims x | jointRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  obtain ⟨κ, σ, β, K, spec, _, _, _, impl, inputSide, p, keyOf, point, Inv, f, E, oa, σ₀,
    hinv, hstep, hE, hσ₀, hf₀, hlane⟩ := hcouple A q x hx hkeys hq hsmall
  exact (probEvent_unchargedRow_le prims A x).trans
    (probEvent_le_of_capped_expect impl inputSide p (jointRun prims A x) (LaneInputRow prims x) keyOf
      point q Inv f hinv hstep E hE oa σ₀ hσ₀ hf₀ hlane)

end SigningTopRowsCapProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsCapProof.exposedRun_unreleased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningTopRowsCapProof.exposedRun_unreleased

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsCapProof.tree_release_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningTopRowsCapProof.tree_release_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsCapProof.hiddenInputHit_lane_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningTopRowsCapProof.hiddenInputHit_lane_iff

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsCapProof.unchargedRow_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningTopRowsCapProof.unchargedRow_add_le

/-- info: 'ThresholdLeanXmssSecurity.SigningTopRowsCapProof.unchargedRow_le_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningTopRowsCapProof.unchargedRow_le_of_coupling
