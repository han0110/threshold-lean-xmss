import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame

/-! # The release at a tree request of the O1 coupling

- `sourceReturnTreeX_eq` splits the release into `returnOpeningX` and one `returnChainX` for each
  top chain.
- `returnOpening_sync` states that the release of the top opening keeps the relation inside a handler.
- `returnChain_sync` states the same for the release of one top chain.
- `returnTree_sync` states that the full release keeps the relation and returns the real stored tree.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open SigningCompilerSyncChain SigningCompilerSyncSuffix
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The release of the opening of the top key of a returned tree. -/
def returnOpeningX (P : PublicParameter) (bi : XmssSecurity.TopIndex) : SourceMX C Digest := do
  let opening ← sourceRevealX (.opening topLayer (topKey bi))
  let ok ← liftM (completeQ (C := C) (.randomizer topLayer (topKey bi)) opening)
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  let pending := (← get).allocated.filter fun p => p.key = .opening topLayer (topKey bi)
  let _ ← pending.mapM (sourcePlantX P)
  pure opening

/-- The release of one top chain of a returned tree, from the digit of its top codeword. -/
def returnChainX (P : PublicParameter) (bi : XmssSecurity.TopIndex) (tree : DeferredBottomTree)
    (l : ChainIndex) : SourceMX C Digest := do
  let start := tree.topSignature.encoding l
  let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
  let _ ← keys.mapM fun p => sourceRevealX (.topChain bi l p)
  if start.val = 0 then
    let value ← sourceRevealX (.topChain bi l ⟨0, by decide⟩)
    let ok ← liftM (completeQ (C := C) (.chain topLayer (topKey bi) l (digit 0)) value)
    modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  let _ ← keys.mapM fun p => sourcePlantX P (.top bi l p)
  sourceRevealDigestX (tree.topSignature.chainValue l)

/-- The release at a tree request is the release of the opening and then of each top chain. -/
theorem sourceReturnTreeX_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (bi : XmssSecurity.TopIndex) (tree : DeferredBottomTree) :
    sourceReturnTreeX P seeds bi tree = (do
      let opening ← returnOpeningX P bi
      let values ← Concrete.sequenceFin fun l => returnChainX P bi tree l
      pure (⟨tree.cpk, tree.commitment, tree.root,
        ⟨tree.topSignature.randomness, values, tree.topSignature.path⟩⟩, opening)) := by
  simp only [sourceReturnTreeX, returnOpeningX, returnChainX, bind_assoc, pure_bind]

/-- The completion of the top chain start in the release of a top chain. It runs only at digit 0. -/
def topStartX (bi : XmssSecurity.TopIndex) (tree : DeferredBottomTree) (l : ChainIndex) :
    SourceMX C Unit :=
  if (tree.topSignature.encoding l).val = 0 then do
    let value ← sourceRevealX (.topChain bi l ⟨0, by decide⟩)
    let ok ← liftM (completeQ (C := C) (.chain topLayer (topKey bi) l (digit 0)) value)
    modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  else pure ()

/-- The release of one top chain is the reveals, the completion of the start, the plants and the
read of the chain value. -/
theorem returnChainX_eq (P : PublicParameter) (bi : XmssSecurity.TopIndex)
    (tree : DeferredBottomTree) (l : ChainIndex) :
    returnChainX (C := C) P bi tree l =
      ((List.finRange 3).filter fun p : XmssSecurity.ChainStep =>
          (tree.topSignature.encoding l).val ≤ p.val).mapM
          (fun p => sourceRevealX (.topChain bi l p)) >>= fun _ =>
        topStartX bi tree l >>= fun _ =>
          ((List.finRange 3).filter fun p : XmssSecurity.ChainStep =>
              (tree.topSignature.encoding l).val ≤ p.val).mapM
              (fun p => sourcePlantX P (.top bi l p)) >>= fun _ =>
            sourceRevealDigestX (tree.topSignature.chainValue l) := by
  unfold returnChainX topStartX
  refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
  split <;> simp only [bind_assoc, pure_bind] <;> rfl

/-! ## The keys of a tree request -/

/-- The keys that the release at the tree request of `bi` reveals. These are the top opening and
the top chain keys at or above the digit of the top codeword. -/
def TreeKey (bi : XmssSecurity.TopIndex) (tree : DeferredBottomTree) (k : HiddenKey) : Prop :=
  k = .opening topLayer (topKey bi) ∨
    ∃ (l : ChainIndex) (p : XmssSecurity.ChainStep), k = .topChain bi l p ∧ (tree.topSignature.encoding l).val ≤ p.val

theorem treeKey_opening {bi : XmssSecurity.TopIndex} {tree : DeferredBottomTree} {lay : Layer}
    {e : KeyIndex} (h : TreeKey bi tree (.opening lay e)) : lay = topLayer ∧ e = topKey bi := by
  rcases h with h | ⟨l, p, h, _⟩
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem treeKey_bottomChain {bi : XmssSecurity.TopIndex} {tree : DeferredBottomTree}
    {e : XmssSecurity.LeafIndex} {l : ChainIndex} {p : XmssSecurity.ChainStep} :
    ¬TreeKey bi tree (.bottomChain e l p) := by
  rintro (h | ⟨_, _, h, _⟩) <;> cases h

theorem treeKey_topChain {bi bj : XmssSecurity.TopIndex} {tree : DeferredBottomTree}
    {l : ChainIndex} {p : XmssSecurity.ChainStep} (h : TreeKey bi tree (.topChain bj l p)) :
    bj = bi ∧ (tree.topSignature.encoding l).val ≤ p.val := by
  rcases h with h | ⟨l', p', h, hle⟩
  · cases h
  · cases h; exact ⟨rfl, hle⟩

/-- Only a top pending point has a top chain key. -/
theorem pendingKey_topChain (p : PendingInput) (bi : XmssSecurity.TopIndex) (l : ChainIndex)
    (d : XmssSecurity.ChainStep) (h : p.key = .topChain bi l d) : p = .top bi l d := by
  cases p <;> simp_all [PendingInput.key]

/-- The effect of a release step of a tree request on the compiler side. The step reveals only keys
of the tree request and keeps the cache relation at the fixed visible cache. -/
structure TreeFrame (x : Keys3 C) (s : HiddenKey → Digest) (bi : XmssSecurity.TopIndex)
    (tree : DeferredBottomTree) (visible : HashCache C) (b b' : SourceState C × CompState C) : Prop
    extends ReleaseFrame x b b' where
  kept : ∀ k, b.1.revealed k ≠ none → b'.1.revealed k = b.1.revealed k
  new : ∀ k, b.1.revealed k = none → b'.1.revealed k ≠ none → TreeKey bi tree k
  reveal : RevealRelation s b'.1 b'.2.1.1
  agreement : CacheRelation x.1 x.2.1 s (dataOf x b'.2) visible
  released : ReleasedPending x.1 s b'.1 (dataOf x b'.2)
  bad : b'.2.2.bad = none

/-- Outside the keys of the tree request the reveal map does not change. -/
theorem TreeFrame.revealed_eq {x : Keys3 C} {s : HiddenKey → Digest} {bi : XmssSecurity.TopIndex}
    {tree : DeferredBottomTree} {visible : HashCache C} {b b' : SourceState C × CompState C}
    (h : TreeFrame x s bi tree visible b b') (k : HiddenKey) (hk : ¬TreeKey bi tree k) :
    b'.1.revealed k = b.1.revealed k := by
  by_cases hold : b.1.revealed k = none
  · rw [hold]
    by_contra hne
    exact hk (h.new k hold hne)
  · exact h.kept k hold

/-- A key that the step leaves unrevealed was unrevealed before. -/
theorem TreeFrame.revealed_none {x : Keys3 C} {s : HiddenKey → Digest} {bi : XmssSecurity.TopIndex}
    {tree : DeferredBottomTree} {visible : HashCache C} {b b' : SourceState C × CompState C}
    (h : TreeFrame x s bi tree visible b b') (k : HiddenKey) (hk : b'.1.revealed k = none) :
    b.1.revealed k = none := by
  by_contra hne
  rw [h.kept k hne] at hk
  exact hne hk

/-- The release steps compose. -/
theorem TreeFrame.trans {x : Keys3 C} {s : HiddenKey → Digest} {bi : XmssSecurity.TopIndex}
    {tree : DeferredBottomTree} {visible : HashCache C} {b b' b'' : SourceState C × CompState C}
    (h : TreeFrame x s bi tree visible b b') (h' : TreeFrame x s bi tree visible b' b'') :
    TreeFrame x s bi tree visible b b'' where
  toReleaseFrame := h.toReleaseFrame.trans h'.toReleaseFrame
  kept k hk := (h'.kept k (by rw [h.kept k hk]; exact hk)).trans (h.kept k hk)
  new k hk hk'' := by
    by_cases hm : b'.1.revealed k = none
    · exact h'.new k hm hk''
    · exact h.new k hk hm
  reveal := h'.reveal
  agreement := h'.agreement
  released := h'.released
  bad := h'.bad

section TreeRequest
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A release step of a tree request keeps the relation inside a handler. The timing view names the
tree, so the new reveals meet the timing clauses. -/
theorem syncIn_of_treeFrame (top : TopTree) (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight))
    (tree : DeferredBottomTree) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (src' : SourceState C) (st' : CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htree : b.1.base.trees bi = some (some tree)) (hexposed : bi ∈ cTime.2.1)
    (h : TreeFrame x s bi tree (visibleOf a) (b.1.base, b.2) (src', st'))
    (hF : Frame x rest st'.1.1 ∧ ShareG (gOf s pads u) st'.2) (hd : DoneCached st'.2)
    (hpads : PadsFixed x pads st') :
    SyncIn prims x s pads u rest noise top cCore cTime a (⟨src', b.1.starts⟩, st') := by
  obtain ⟨⟨⟨hf, hc⟩, hcount⟩, hx, htop, -⟩ := hs
  have hsig : src'.signing = b.1.base.signing := h.signing
  have htrees : src'.trees = b.1.base.trees := h.trees
  have hcand : src'.candidates = b.1.base.candidates := h.candidates
  have hpend : (dataOf x st').pending = (dataOf x b.2).pending := h.pending
  have hvirt : (dataOf x st').virtual = (dataOf x b.2).virtual := h.virtual
  have hcache : (dataOf x b.2).cache ≤ (dataOf x st').cache := h.cache
  have heq : ∀ k, ¬TreeKey bi tree k → src'.revealed k = b.1.base.revealed k := h.revealed_eq
  have hnone : ∀ k, src'.revealed k = none → b.1.base.revealed k = none := h.revealed_none
  have hkept : ∀ k, b.1.base.revealed k ≠ none → src'.revealed k ≠ none := by
    intro k hk
    rw [h.kept k hk]
    exact hk
  refine ⟨⟨⟨?_, h.agreement⟩, hcount.trans h.count.symm⟩, ?_, ?_, hpads⟩
  · refine {
      corrupt := ?_, bound := ?_, released := ?_, exposed := ?_, candidates := ?_, flag := ?_
      reveal := h.reveal, releasedPending := h.released, opening := ?_
      pendingValid := hF.1.2.2, allocated := ?_, virtualSeen := ?_, compilerBound := ?_
      trace := ?_, bad := h.bad, share := hF.2, restAgree := hF.1.1, restFree := hF.1.2.1
      realPrivate := hf.realPrivate, frontier := ?_, candidatesPaid := ?_, doneCached := hd }
    · rw [hsig]; exact hf.corrupt
    · rw [hsig]; exact hf.bound
    · rw [hsig]; exact hf.released
    · exact h.exposed.trans hf.exposed
    · exact hcand.trans hf.candidates
    · exact h.hiddenFlag.trans hf.flag
    · refine ⟨hf.opening.actualValue, ?_⟩
      intro e he T
      have hk : ¬TreeKey bi tree (.opening bottomLayer e) := fun hk =>
        XmssSecurity.Bridge.topLayer_ne_bottom (treeKey_opening hk).1.symm
      rw [heq _ hk] at he
      obtain ⟨value, hv⟩ := hf.opening.released e he T
      exact ⟨value, hcache hv⟩
    · intro p hp
      rw [h.allocated]
      exact hf.allocated p (hpend ▸ hp)
    · intro T p hp
      exact hf.virtualSeen T p (hvirt ▸ hp)
    · exact h.bound.trans (hsig ▸ hf.compilerBound)
    · exact hf.trace.trans h.trace.symm
    · intro edge hp
      rw [hpend] at hp
      by_cases hk : TreeKey bi tree (chainPending edge).key
      · rcases hk with hk | ⟨l, p, hk, _⟩
        · rcases edge with ⟨l, key | bj, p⟩ <;> simp [chainPending, PendingInput.key] at hk
        · have he := pendingKey_topChain _ _ _ _ hk
          exact absurd (he ▸ hp) (htop.topRows bi l p)
      · rw [heq _ hk]
        exact hf.frontier edge hp
    · intro c hc hs
      rw [hcand] at hc
      exact hkept _ (hf.candidatesPaid c hc hs)
  · have hr := hx.rest
    refine ⟨?_, hx.prfSeen, ?_⟩
    · exact
        { hr with
          treeRows := fun bj hbj k l d => by
            have hrows := hr.treeRows bj (htrees ▸ hbj) k l d
            exact ⟨fun T => hvirt ▸ hrows.1 T, hpend ▸ hrows.2⟩
          storedTrees := fun bj => by
            rw [htrees]
            exact hr.storedTrees bj
          storedTopDigit := fun bj t ht => hr.storedTopDigit bj t (htrees ▸ ht)
          startsTreed := fun e l hl => by
            rw [htrees]
            exact hr.startsTreed e l hl
          boundTreeRevealed := fun e hb ht =>
            hkept _ (hr.boundTreeRevealed e (hsig ▸ hb) (htrees ▸ ht))
          revealedReleased := fun lay e hk => by
            by_cases hold : b.1.base.revealed (.opening lay e) = none
            · obtain ⟨hl, he⟩ := treeKey_opening (h.new _ hold hk)
              subst hl he
              exact Or.inr ⟨rfl, bi, hexposed, rfl⟩
            · exact hr.revealedReleased lay e hold
          revealedCovered := fun e l p hk => by
            rw [heq _ treeKey_bottomChain] at hk
            exact hr.revealedCovered e l p hk
          revealedTop := fun bj l p hk => by
            by_cases hold : b.1.base.revealed (.topChain bj l p) = none
            · obtain ⟨hb, hle⟩ := treeKey_topChain (h.new _ hold hk)
              subst hb
              exact ⟨hexposed, tree, htrees ▸ htree, hle⟩
            · rw [htrees]
              exact hr.revealedTop bj l p hold
          candidatesPaid := fun c hc hs => hkept _ (hr.candidatesPaid c (hcand ▸ hc) hs)
          openingFresh := fun c hc => hr.openingFresh c (hcand ▸ hc)
          noEarlyGuess := fun e message hk => hr.noEarlyGuess e message (hnone _ hk)
          guessFree := fun p hk hp => hr.guessFree p (hnone _ hk) (hpend ▸ hp)
          treeTerms := fun bj hbj => by
            obtain ⟨h1, h2⟩ := hr.treeTerms bj (htrees ▸ hbj)
            exact ⟨fun k T => hvirt ▸ h1 k T, fun T => hvirt ▸ h2 T⟩
          treeStarts := fun bj t ht T l => hvirt ▸ hr.treeStarts bj t (htrees ▸ ht) T l
          treeValues := fun bj t ht => hr.treeValues bj t (htrees ▸ ht)
          bottomSeen := fun hfl => by cases hfl }
    · intro hfl T e l d ho hv
      rcases hx.bottomSeen hfl T e l d ho hv with h1 | h1
      · exact Or.inl h1
      · exact Or.inr fun d' => hpend ▸ h1 d'
  · exact ⟨fun bj l d => hpend ▸ htop.topRows bj l d, htop.topRun⟩

/-- The post of a release step of a tree request. The real state does not move. -/
def ReleasePostIn (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C) {α : Type} (value : α → Prop)
    (r : (α × SourceState C) × CompState C) : Prop :=
  Stop r.2 ∨
    (value r.1.1 ∧
      SyncIn prims x s pads u rest noise top cCore cTime a (⟨r.1.2, b.1.starts⟩, r.2) ∧
      r.1.2.signing = b.1.base.signing ∧ r.1.2.trees = b.1.base.trees ∧
      r.1.2.exposed = b.1.base.exposed ∧ r.1.2.candidates = b.1.base.candidates ∧
      r.2.1.2 = false)

theorem safe_returnOpeningX (P : PublicParameter) (bi : XmssSecurity.TopIndex) :
    Safe (returnOpeningX (C := C) P bi) := by
  unfold returnOpeningX
  exact (safe_sourceRevealX _).bind fun _ =>
    (safe_complete _ _ (constrained_top_randomizer bi)).bind fun _ =>
      (Safe.modify _).bind fun _ => Safe.get.bind fun _ =>
        (Safe.mapM _ _ fun p _ => safe_sourcePlantX P p).bind fun _ => Safe.pure _

/-- A release step of a tree request that does not stop gives the post, when its compiler effect is
a `TreeFrame`. -/
theorem releasePostIn_of_treeFrame {α : Type} (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (top : TopTree) (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight))
    (tree : DeferredBottomTree) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htree : b.1.base.trees bi = some (some tree)) (hexposed : bi ∈ cTime.2.1)
    (hmark : b.2.1.2 = false) (oa : SourceMX C α) (hsafe : Safe oa) (value : α → Prop)
    (r : (α × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) oa b.1.base b.2))
    (h : Stop r.2 ∨ (value r.1.1 ∧
      TreeFrame x s bi tree (visibleOf a) (b.1.base, b.2) (r.1.2, r.2))) :
    ReleasePostIn prims x s pads u rest noise top cCore cTime a b value r := by
  rcases h with hstop | ⟨hv, hframe⟩
  · exact Or.inl hstop
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  have hi := TprfSecurityProof.slotInput_injective hinj (not_not.mp (not_or.mp hkeys).2)
  have hf := hs.1.1.1
  have hF := safe_frame capTag x hi q s pads (tauOf s pads) (gOf s pads u) noise rest oa hsafe
    b.1.base b.2 ⟨⟨hf.restAgree, hf.restFree, hf.pendingValid⟩, hf.share⟩ r hr
  have hd := simulate_doneCached capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
    (oa.run b.1.base) b.2 hf.doneCached r hr
  have hpads := backend_padsFixed x q s pads u rest noise (oa.run b.1.base) b.2 hs.2.2.2 r hr
  refine Or.inr ⟨hv, syncIn_of_treeFrame prims x s pads u rest noise top cCore cTime bi tree a b
    r.1.2 r.2 hs htree hexposed hframe hF hd hpads, hframe.signing, hframe.trees, hframe.exposed,
    hframe.candidates, hframe.mark.trans hmark⟩

/-- The compiler effect of the release of the top opening. It is the port of `releaseOpening_post`
to the top randomizer point, with the visible row of the point given. -/
theorem returnOpening_frame (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (bi : Fin (2 ^ layerHeight)) (tree : DeferredBottomTree) (a : RealState C)
    (src : SourceState C) (st : CompState C)
    (hf : SyncFields x s pads noise (gOf s pads u) rest a (src, st))
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf a)) (hmark : st.1.2 = false)
    (hrow : ∀ T, visibleOf a (.prf (x.2.1 T) (.randomizer topLayer (topKey bi))) =
      some (gOf s pads u (T, ⟨.randomizer topLayer (topKey bi), constrained_top_randomizer bi⟩)))
    (r : (Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) (returnOpeningX x.1 bi) src st)) :
    Stop r.2 ∨ (r.1.1 = s (.opening topLayer (topKey bi)) ∧
      TreeFrame x s bi tree (visibleOf a) (src, st) (r.1.2, r.2)) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  let k := HiddenKey.opening topLayer (topKey bi)
  let p : CPoint := ⟨.randomizer topLayer (topKey bi), constrained_top_randomizer bi⟩
  simp only [returnOpeningX, runX_bind, runX_get, pure_bind, runX_modify, runX_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨revealed, hrrev, completed, hrcomp, planted, hrplant, rfl⟩ := hr
  have hR := sourceRevealX_sync capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
    k src st hf.reveal hf.restFree revealed hrrev
  have heq : revealed = ((s k, { src with revealed := Function.update src.revealed k (some (s k)) }),
      (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), st.2)) :=
    Prod.ext (Prod.ext hR.1 hR.2.2.1) hR.2.2.2
  subst revealed
  rw [runX_complete capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p] at hrcomp
  simp only [support_map] at hrcomp
  obtain ⟨a', ha', rfl⟩ := hrcomp
  have hcomp := completion_cache_sync_at x hinj s (tauOf s pads) (gOf s pads u) st.1.1 st.2
    (visibleOf a) p hc hf.share hf.doneCached hrow (s k) (capTag
      ((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2)) a' ha'
  have hbad := eager_complete_null (tauOf s pads) (gOf s pads u) st.2 hf.bad p (s k) st.1.1.2.2 a' (by
    change a' ∈ support ((SigningShareLazy.eagerImpl C.terms (tauOf s pads) (gOf s pads u)
      (.complete p (s k) (st.1.2, st.1.1.2.2))).run st.2) at ha'
    rw [hmark] at ha'
    exact ha')
  let srcC : SourceState C := { src with
    revealed := Function.update src.revealed k (some (s k))
    consistent := src.consistent && a'.1 }
  let stC : CompState C :=
    (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), a'.2)
  have hplants := sourcePlantsX_sync capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
    (src.allocated.filter (fun pending => pending.key = k)) srcC stC (visibleOf a) (by
      intro pending hmem
      have hkey : pending.key = k := of_decide_eq_true (List.mem_filter.mp hmem).2
      refine ⟨key_opening_next pending topLayer (topKey bi) hkey, ?_⟩
      change Function.update src.revealed k (some (s k)) pending.key = some (s pending.key)
      rw [hkey, Function.update_self]) (by exact hf.pendingValid) hf.restFree (by exact hcomp.1)
      planted hrplant
  have hsrc : planted.1.2 = srcC := hplants.1
  have hstate : planted.2 = cacheState stC planted.2.1.1.1.1.data.cache := hplants.2.1
  have hpend : (dataOf x planted.2).pending = (dataOf x st).pending := by
    rw [hstate]; rfl
  have hgrow : (dataOf x st).cache ≤ (dataOf x planted.2).cache :=
    hcomp.2.trans hplants.2.2.2.1
  have hrev : planted.1.2.revealed = Function.update src.revealed k (some (s k)) := by
    rw [hsrc]
  rcases hbad with hbad | hbad
  swap
  · left; left
    rw [hstate]
    exact hbad
  right
  refine ⟨rfl, ?_⟩
  refine {
    toReleaseFrame := ?_
    kept := ?_
    new := ?_
    reveal := ?_
    agreement := hplants.2.2.1
    released := ?_
    bad := ?_ }
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hpend, ?_, hgrow, ?_, ?_, ?_, ?_⟩
    any_goals (change planted.1.2.signing = _; rw [hsrc])
    any_goals (change planted.1.2.trees = _; rw [hsrc])
    any_goals (change planted.1.2.exposed = _; rw [hsrc])
    any_goals (change planted.1.2.allocated = _; rw [hsrc])
    any_goals (change planted.1.2.candidates = _; rw [hsrc])
    any_goals (change planted.1.2.hiddenFlag = _; rw [hsrc])
    all_goals (rw [hstate]; try rfl)
  · intro key hkey
    change planted.1.2.revealed key = src.revealed key
    rw [hrev]
    by_cases he : key = k
    · subst key
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hkey
      rw [hv, hf.reveal.2 k v hv, Function.update_self]
    · exact Function.update_of_ne he _ _
  · intro key hkey hnew
    change planted.1.2.revealed key ≠ none at hnew
    rw [hrev] at hnew
    by_cases he : key = k
    · exact Or.inl he
    · rw [Function.update_of_ne he] at hnew
      exact absurd hkey hnew
  · change RevealRelation s planted.1.2 planted.2.1.1
    rw [hsrc, hstate]
    exact hR.2.1
  · intro pending value hvalue hreleased
    rw [hpend] at hvalue
    by_cases he : pending.key = k
    · apply hplants.2.2.2.2.2 pending ?_ value hvalue
      exact List.mem_filter.mpr ⟨hf.allocated pending (by rw [hvalue]; exact Option.some_ne_none _),
        by simpa only [decide_eq_true_eq] using he⟩
    · have hold : src.revealed pending.key ≠ none := by
        change planted.1.2.revealed pending.key ≠ none at hreleased
        rw [hrev, Function.update_of_ne he] at hreleased
        exact hreleased
      exact hgrow (hf.releasedPending pending value hvalue hold)
  · change planted.2.2.bad = none
    rw [hstate]
    exact hbad

/-- The release of the top opening of a stored successful tree. The timing view names the tree. -/
theorem returnOpening_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (tree : DeferredBottomTree)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htree : b.1.base.trees bi = some (some tree)) (hexposed : bi ∈ cTime.2.1)
    (hmark : b.2.1.2 = false)
    (r : (Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (returnOpeningX x.1 bi) b.1.base b.2)) :
    ReleasePostIn prims x s pads u rest noise top cCore cTime a b
      (fun v => v = s (.opening topLayer (topKey bi))) r := by
  have hf := hs.1.1.1
  have hrow := chainRow_of_virtual x hkeys s pads noise (gOf s pads u) rest (withCarried a cCore)
    (b.1.base, b.2) hf ⟨_, constrained_top_randomizer bi⟩
    (hs.2.1.rest.treeTerms bi (by rw [htree]; exact Option.some_ne_none _)).2
  exact releasePostIn_of_treeFrame prims x q s pads u rest noise hkeys top cCore cTime bi tree a b
    hs htree hexposed hmark _ (safe_returnOpeningX x.1 bi) _ r hr
    (returnOpening_frame x q s pads u rest noise hkeys bi tree (withCarried a cCore) b.1.base b.2
      hf hs.1.1.2 hmark hrow r hr)

/-- A list of reveals changes only the two reveal maps. Each listed key is revealed at its secret,
and each other key keeps its entry. -/
theorem revealsX_post {α : Type} (f : α → HiddenKey) (ps : List α) (src : SourceState C)
    (st : CompState C) (hrev : RevealRelation s src st.1.1)
    (hfree : RestFree x.2.1 st.1.1.1.1.data.cache)
    (r : (List Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (ps.mapM fun p => sourceRevealX (f p)) src st)) :
    r.1.2 = { src with revealed := r.1.2.revealed } ∧
      r.2 = (((st.1.1.1, r.2.1.1.2.1, st.1.1.2.2), st.1.2), st.2) ∧
      RevealRelation s r.1.2 r.2.1.1 ∧
      (∀ k, (∀ p ∈ ps, k ≠ f p) → r.1.2.revealed k = src.revealed k) ∧
      (∀ p ∈ ps, r.1.2.revealed (f p) = some (s (f p))) := by
  induction ps generalizing src st r with
  | nil =>
    simp only [List.mapM_nil, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, rfl, hrev, fun _ _ => rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons p ps ih =>
    simp only [List.mapM_cons, runX_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, b, hb, hr⟩ := hr
    rw [runX_pure, mem_support_pure_iff] at hr
    subst r
    have hR := sourceRevealX_sync capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
      (f p) src st hrev hfree a ha
    have heq : a = ((s (f p),
        { src with revealed := Function.update src.revealed (f p) (some (s (f p))) }),
        (((st.1.1.1, Function.update st.1.1.2.1 (f p) (some (s (f p))), st.1.1.2.2), st.1.2),
          st.2)) :=
      Prod.ext (Prod.ext hR.1 hR.2.2.1) hR.2.2.2
    subst a
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih _ _ hR.2.1 hfree b hb
    refine ⟨?_, ?_, h3, ?_, ?_⟩
    · conv_lhs => rw [h1]
    · conv_lhs => rw [h2]
    · intro k hk
      rw [h4 k (fun p' hp' => hk p' (List.mem_cons_of_mem _ hp'))]
      exact Function.update_of_ne (hk p (List.mem_cons_self ..)) _ _
    · intro p' hp'
      rcases List.mem_cons.mp hp' with he | hp'
      · subst p'
        by_cases hm : ∃ p'' ∈ ps, f p = f p''
        · obtain ⟨p'', hp'', he⟩ := hm
          rw [he]
          exact h5 p'' hp''
        · rw [h4 (f p) (fun p'' hp'' he => hm ⟨p'', hp'', he⟩)]
          exact Function.update_self ..
      · exact h5 p' hp'

/-- A later top chain key is in the suffix of its chain. -/
theorem top_next_suffix (bi : XmssSecurity.TopIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep)
    (k : HiddenKey) (hk : (PendingInput.top bi l d).next = some k) :
    ∃ next : XmssSecurity.ChainStep, d.val < next.val ∧ k = .topChain bi l next := by
  simp only [PendingInput.next] at hk
  split at hk
  · rename_i hnext
    exact ⟨⟨d.val + 1, hnext⟩, by change d.val < d.val + 1; omega, (Option.some.inj hk).symm⟩
  · cases hk

/-- A revealed key is read again with no backend call. -/
theorem runX_sourceRevealX_revealed (k : HiddenKey) (v : Digest) (src : SourceState C)
    (st : CompState C) (hk : src.revealed k = some v) :
    runX (compBackend x q s pads u rest noise) (sourceRevealX k) src st = pure ((v, src), st) := by
  simp [runX, sourceRevealX, hk, StateT.run_bind, StateT.run_get, StateT.run_pure]

/-- The effect of a completion with no new reveal. -/
structure CompletePost (x : Keys3 C) (s : HiddenKey → Digest) (g : C.Term × CPoint → HashOutput)
    (visible : HashCache C) (b b' : SourceState C × CompState C) : Prop
    extends ReleaseFrame x b b' where
  revealed : b'.1.revealed = b.1.revealed
  reveal : RevealRelation s b'.1 b'.2.1.1
  agreement : CacheRelation x.1 x.2.1 s (dataOf x b'.2) visible
  restFree : RestFree x.2.1 b'.2.1.1.1.1.data.cache
  share : ShareG g b'.2.2
  doneCached : DoneCached b'.2.2
  bad : b'.2.2.bad = none

/-- The completion of the top chain start keeps the cache relation at the fixed visible cache, or
stops. The start key is revealed before. -/
theorem topStartX_post (hinj : Function.Injective x.2.1) (bi : Fin (2 ^ layerHeight))
    (tree : DeferredBottomTree) (l : ChainIndex) (a : RealState C) (src : SourceState C)
    (st : CompState C) (hrev : RevealRelation s src st.1.1)
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf a))
    (hfree : RestFree x.2.1 st.1.1.1.1.data.cache) (hg : ShareG (gOf s pads u) st.2)
    (hd : DoneCached st.2) (hb : st.2.bad = none) (hm : st.1.2 = false)
    (hk : (tree.topSignature.encoding l).val = 0 →
      src.revealed (.topChain bi l ⟨0, by decide⟩) = some (s (.topChain bi l ⟨0, by decide⟩)))
    (hrow : ∀ T, visibleOf a (.prf (x.2.1 T) (.chain topLayer (topKey bi) l (digit 0))) =
      some (gOf s pads u (T, ⟨.chain topLayer (topKey bi) l (digit 0), constrained_top_chain bi l⟩)))
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) (topStartX bi tree l) src st)) :
    Stop r.2 ∨ CompletePost x s (gOf s pads u) (visibleOf a) (src, st) (r.1.2, r.2) := by
  unfold topStartX at hr
  split at hr
  · rename_i h0
    let k := HiddenKey.topChain bi l ⟨0, by decide⟩
    let p : CPoint := ⟨.chain topLayer (topKey bi) l (digit 0), constrained_top_chain bi l⟩
    simp only [runX_bind, mem_support_bind_iff] at hr
    obtain ⟨revealed, hrrev, completed, hrcomp, hr⟩ := hr
    rw [runX_sourceRevealX_revealed x q s pads u rest noise k _ src st (hk h0),
      mem_support_pure_iff] at hrrev
    subst revealed
    rw [runX_complete capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p] at hrcomp
    simp only [support_map] at hrcomp
    obtain ⟨a', ha', rfl⟩ := hrcomp
    rw [runX_modify, mem_support_pure_iff] at hr
    subst r
    have hcomp := completion_cache_sync_at x hinj s (tauOf s pads) (gOf s pads u) st.1.1 st.2
      (visibleOf a) p hc hg hd hrow (s k) (capTag st.1) a' ha'
    have hbad := eager_complete_null (tauOf s pads) (gOf s pads u) st.2 hb p (s k) st.1.1.2.2 a' (by
      change a' ∈ support ((SigningShareLazy.eagerImpl C.terms (tauOf s pads) (gOf s pads u)
        (.complete p (s k) (st.1.2, st.1.1.2.2))).run st.2) at ha'
      rw [hm] at ha'
      exact ha')
    rcases hbad with hbad | hbad
    · exact Or.inr {
        toReleaseFrame := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcomp.2, rfl, rfl, rfl, rfl⟩
        revealed := rfl
        reveal := hrev
        agreement := hcomp.1
        restFree := hfree
        share := eagerImpl_shareG _ _ _ st.2 hg a' ha'
        doneCached := eagerImpl_doneCached _ _ st.2 hd _ a' ha'
        bad := hbad }
    · exact Or.inl (Or.inl hbad)
  · rw [runX_pure, mem_support_pure_iff] at hr
    subst r
    exact Or.inr ⟨ReleaseFrame.refl x _, rfl, hrev, hc, hfree, hg, hd, hb⟩

/-- The compiler effect of the release of one top chain. It is the port of `releaseSuffix_post` to a
top chain, with the visible row of the chain start given. -/
theorem returnChain_frame (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (bi : Fin (2 ^ layerHeight)) (tree : DeferredBottomTree) (l : ChainIndex) (a : RealState C)
    (src : SourceState C) (st : CompState C)
    (hf : SyncFields x s pads noise (gOf s pads u) rest a (src, st))
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) (visibleOf a)) (hmark : st.1.2 = false)
    (hrow : ∀ T, visibleOf a (.prf (x.2.1 T) (.chain topLayer (topKey bi) l (digit 0))) =
      some (gOf s pads u (T, ⟨.chain topLayer (topKey bi) l (digit 0), constrained_top_chain bi l⟩)))
    (hvalue : (∀ h : (tree.topSignature.encoding l).val < 3, tree.topSignature.chainValue l =
        .secret (.topChain bi l ⟨(tree.topSignature.encoding l).val, h⟩)) ∧
      ((tree.topSignature.encoding l).val = 3 → ∃ w, tree.topSignature.chainValue l = .known w))
    (r : (Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (returnChainX x.1 bi tree l) src st)) :
    Stop r.2 ∨ (r.1.1 = (tree.topSignature.chainValue l).interpret s ∧
      TreeFrame x s bi tree (visibleOf a) (src, st) (r.1.2, r.2)) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  let start := tree.topSignature.encoding l
  let keys := (List.finRange 3).filter fun p : XmssSecurity.ChainStep => start.val ≤ p.val
  have hmem (d : XmssSecurity.ChainStep) : d ∈ keys ↔ start.val ≤ d.val := by simp [keys]
  rw [returnChainX_eq] at hr
  simp only [runX_bind, mem_support_bind_iff] at hr
  obtain ⟨revealed, hrrev, completed, hrcomp, planted, hrplant, hr⟩ := hr
  obtain ⟨hR1, hR2, hR3, hR4, hR5⟩ := revealsX_post x q s pads u rest noise
    (fun p => HiddenKey.topChain bi l p) keys src st hf.reveal hf.restFree revealed hrrev
  have hpend1 : (dataOf x revealed.2).pending = (dataOf x st).pending := by rw [hR2]; rfl
  have rf1 : ReleaseFrame x (src, st) (revealed.1.2, revealed.2) := by
    refine ⟨(congrArg SourceState.signing hR1 :), (congrArg SourceState.trees hR1 :),
      (congrArg SourceState.exposed hR1 :), (congrArg SourceState.allocated hR1 :),
      (congrArg SourceState.candidates hR1 :), (congrArg SourceState.hiddenFlag hR1 :), hpend1, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    all_goals (rw [hR2]; try rfl)
  rcases topStartX_post x q s pads u rest noise hinj bi tree l a revealed.1.2 revealed.2 hR3
    (by rw [hR2]; exact hc) (by rw [hR2]; exact hf.restFree) (by rw [hR2]; exact hf.share)
    (by rw [hR2]; exact hf.doneCached) (by rw [hR2]; exact hf.bad) (by rw [hR2]; exact hmark)
    (fun h0 => hR5 ⟨0, by decide⟩ ((hmem _).mpr (by change start.val ≤ 0; omega)))
    hrow completed hrcomp with hstop | hcp
  · left
    have h1 := runX_stop x q s pads (tauOf s pads) (gOf s pads u) noise rest _ completed.1.2
      completed.2 hstop planted hrplant
    exact runX_stop x q s pads (tauOf s pads) (gOf s pads u) noise rest _ planted.1.2
      planted.2 h1 r hr
  have hrev2 : completed.1.2.revealed = revealed.1.2.revealed := hcp.revealed
  have hpending : PendingValid (dataOf x completed.2) := by
    intro p value hp
    rw [hcp.pending, hpend1] at hp
    exact hf.pendingValid p value hp
  have hplants := sourcePlantsX_sync_next capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
    (keys.map fun d => PendingInput.top bi l d) completed.1.2 completed.2 (visibleOf a)
    (by
      intro p hp
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
      rw [hrev2]
      constructor
      · intro key hk
        obtain ⟨next, hnext, rfl⟩ := top_next_suffix bi l d key hk
        apply hR5 next
        apply (hmem next).mpr
        have hstart := (hmem d).mp hd
        omega
      · exact hR5 d hd)
    hpending hcp.restFree hcp.agreement planted (by
      simpa only [List.mapM_map, Function.comp_def] using hrplant)
  have rf3 : ReleaseFrame x (completed.1.2, completed.2) (planted.1.2, planted.2) := by
    refine ⟨congrArg SourceState.signing hplants.1, congrArg SourceState.trees hplants.1,
      congrArg SourceState.exposed hplants.1, congrArg SourceState.allocated hplants.1,
      congrArg SourceState.candidates hplants.1, congrArg SourceState.hiddenFlag hplants.1,
      ?_, ?_, hplants.2.2.2.1, ?_, ?_, ?_, ?_⟩
    all_goals (rw [hplants.2.1] <;> rfl)
  have rf := (rf1.trans hcp.toReleaseFrame).trans rf3
  have hrevF : planted.1.2.revealed = revealed.1.2.revealed := by
    rw [hplants.1]; exact hrev2
  have hframe : TreeFrame x s bi tree (visibleOf a) (src, st) (planted.1.2, planted.2) := by
    refine {
      toReleaseFrame := rf
      kept := ?_
      new := ?_
      reveal := ?_
      agreement := hplants.2.2.1
      released := ?_
      bad := ?_ }
    · intro k hk
      change planted.1.2.revealed k = src.revealed k
      rw [hrevF]
      by_cases hn : ∃ d ∈ keys, k = .topChain bi l d
      · obtain ⟨d, hd, rfl⟩ := hn
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hk
        rw [hR5 d hd, hv, hf.reveal.2 _ v hv]
      · exact hR4 k (fun d hd he => hn ⟨d, hd, he⟩)
    · intro k hk hnew
      change planted.1.2.revealed k ≠ none at hnew
      rw [hrevF] at hnew
      by_cases hn : ∃ d ∈ keys, k = .topChain bi l d
      · obtain ⟨d, hd, rfl⟩ := hn
        exact Or.inr ⟨l, d, rfl, (hmem d).mp hd⟩
      · rw [hR4 k (fun d hd he => hn ⟨d, hd, he⟩)] at hnew
        exact absurd hk hnew
    · have hbackend : planted.2.1.1.2.1 = completed.2.1.1.2.1 := by rw [hplants.2.1]; rfl
      exact hcp.reveal.frame (by rw [hplants.1]) hbackend
    · intro p value hv hrel
      change planted.1.2.revealed p.key ≠ none at hrel
      by_cases hn : ∃ d ∈ keys, p.key = .topChain bi l d
      · obtain ⟨d, hd, hkey⟩ := hn
        have he := pendingKey_topChain p bi l d hkey
        subst p
        exact hplants.2.2.2.2.2 (.top bi l d) (List.mem_map.mpr ⟨d, hd, rfl⟩) value
          (rf3.pending ▸ hv)
      · have hold : src.revealed p.key ≠ none := by
          rw [hrevF, hR4 p.key (fun d hd he => hn ⟨d, hd, he⟩)] at hrel
          exact hrel
        exact rf.cache (hf.releasedPending p value (rf.pending ▸ hv) hold)
    · change planted.2.2.bad = none
      rw [hplants.2.1]
      exact hcp.bad
  right
  by_cases h3 : (tree.topSignature.encoding l).val < 3
  · have hkrev : planted.1.2.revealed (.topChain bi l ⟨start.val, h3⟩) =
        some (s (.topChain bi l ⟨start.val, h3⟩)) := by
      rw [hrevF]
      exact hR5 _ ((hmem _).mpr le_rfl)
    rw [hvalue.1 h3] at hr ⊢
    simp only [sourceRevealDigestX] at hr
    rw [runX_sourceRevealX_revealed x q s pads u rest noise _ _ planted.1.2 planted.2 hkrev,
      mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, hframe⟩
  · obtain ⟨w, hw⟩ := hvalue.2 (by have := start.isLt; change start.val < 4 at this; omega)
    rw [hw] at hr ⊢
    simp only [sourceRevealDigestX, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, hframe⟩

theorem safe_returnChainX (P : PublicParameter) (bi : XmssSecurity.TopIndex)
    (tree : DeferredBottomTree) (l : ChainIndex) : Safe (returnChainX (C := C) P bi tree l) := by
  have hstart : Safe (topStartX (C := C) bi tree l) := by
    unfold topStartX
    split
    · exact (safe_sourceRevealX _).bind fun _ =>
        (safe_complete _ _ (constrained_top_chain bi l)).bind fun _ => Safe.modify _
    · exact Safe.pure _
  rw [returnChainX_eq]
  exact (Safe.mapM _ _ fun p _ => safe_sourceRevealX _).bind fun _ => hstart.bind fun _ =>
    (Safe.mapM _ _ fun p _ => safe_sourcePlantX P _).bind fun _ => safe_sourceRevealDigestX _

/-- The release of one top chain of a stored successful tree. It returns the chain value of the
top signature in the clear. -/
theorem returnChain_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (tree : DeferredBottomTree)
    (l : ChainIndex) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htree : b.1.base.trees bi = some (some tree)) (hexposed : bi ∈ cTime.2.1)
    (hmark : b.2.1.2 = false)
    (r : (Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (returnChainX x.1 bi tree l) b.1.base b.2)) :
    ReleasePostIn prims x s pads u rest noise top cCore cTime a b
      (fun v => v = (tree.topSignature.chainValue l).interpret s) r := by
  have hf := hs.1.1.1
  have hrow := chainRow_of_virtual x hkeys s pads noise (gOf s pads u) rest (withCarried a cCore)
    (b.1.base, b.2) hf ⟨_, constrained_top_chain bi l⟩
    (fun T => hs.2.1.rest.treeStarts bi tree htree T l)
  exact releasePostIn_of_treeFrame prims x q s pads u rest noise hkeys top cCore cTime bi tree a b
    hs htree hexposed hmark _ (safe_returnChainX x.1 bi tree l) _ r hr
    (returnChain_frame x q s pads u rest noise hkeys bi tree l (withCarried a cCore) b.1.base b.2
      hf hs.1.1.2 hmark hrow (hs.2.1.rest.treeValues bi tree htree l) r hr)

/-- The releases of several top chains, in order, keep the relation and return the chain values of
the top signature. -/
theorem chains_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (tree : DeferredBottomTree) (a : RealState C)
    (hexposed : bi ∈ cTime.2.1) (n : ℕ) (g : Fin n → ChainIndex) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htree : b.1.base.trees bi = some (some tree)) (hmark : b.2.1.2 = false)
    (r : ((Fin n → Digest) × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (Concrete.sequenceFin fun i => returnChainX x.1 bi tree (g i)) b.1.base b.2)) :
    ReleasePostIn prims x s pads u rest noise top cCore cTime a b
      (fun v => ∀ i, v i = (tree.topSignature.chainValue (g i)).interpret s) r := by
  induction n generalizing b with
  | zero =>
    simp only [Concrete.sequenceFin, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact Or.inr ⟨fun i => i.elim0, hs, rfl, rfl, rfl, rfl, hmark⟩
  | succ n ih =>
    simp only [Concrete.sequenceFin, runX_bind, mem_support_bind_iff] at hr
    obtain ⟨r1, hr1, r2, hr2, hr⟩ := hr
    rw [runX_pure, mem_support_pure_iff] at hr
    subst r
    rcases returnChain_sync prims x q s pads u rest noise hkeys top cCore cTime bi tree (g 0) a b hs
      htree hexposed hmark r1 hr1 with hstop | ⟨hv1, hs1, hsig1, htrees1, hexp1, hcand1, hmark1⟩
    · exact Or.inl (runX_stop x q s pads (tauOf s pads) (gOf s pads u) noise rest _ r1.1.2 r1.2
        hstop r2 hr2)
    rcases ih (fun i => g i.succ) (⟨r1.1.2, b.1.starts⟩, r1.2) hs1 (htrees1 ▸ htree) hmark1 r2 hr2
      with hstop | ⟨hv2, hs2, hsig2, htrees2, hexp2, hcand2, hmark2⟩
    · exact Or.inl hstop
    refine Or.inr ⟨?_, hs2, hsig2.trans hsig1, htrees2.trans htrees1, hexp2.trans hexp1,
      hcand2.trans hcand1, hmark2⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hv1
    | succ j => exact hv2 j

/-- The release at a tree request. It returns the real tree with no patch and the opening. -/
theorem returnTree_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (tree : DeferredBottomTree)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htree : b.1.base.trees bi = some (some tree)) (hexposed : bi ∈ cTime.2.1)
    (hmark : b.2.1.2 = false)
    (r : ((BottomTree × Digest) × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceReturnTreeX x.1 x.2.1 bi tree) b.1.base b.2)) :
    ReleasePostIn prims x s pads u rest noise top cCore cTime a b
      (fun v => patchTree bi v.1 = interpretTree s bi tree ∧
        v.2 = s (.opening topLayer (topKey bi))) r := by
  rw [sourceReturnTreeX_eq] at hr
  simp only [runX_bind, mem_support_bind_iff] at hr
  obtain ⟨r1, hr1, r2, hr2, hr⟩ := hr
  rw [runX_pure, mem_support_pure_iff] at hr
  subst r
  rcases returnOpening_sync prims x q s pads u rest noise hkeys top cCore cTime bi tree a b hs htree
    hexposed hmark r1 hr1 with hstop | ⟨hv1, hs1, hsig1, htrees1, hexp1, hcand1, hmark1⟩
  · exact Or.inl (runX_stop x q s pads (tauOf s pads) (gOf s pads u) noise rest _ r1.1.2 r1.2
      hstop r2 hr2)
  rcases chains_sync prims x q s pads u rest noise hkeys top cCore cTime bi tree a hexposed _
    (fun l => l) (⟨r1.1.2, b.1.starts⟩, r1.2) hs1 (htrees1 ▸ htree) hmark1 r2 hr2
    with hstop | ⟨hv2, hs2, hsig2, htrees2, hexp2, hcand2, hmark2⟩
  · exact Or.inl hstop
  refine Or.inr ⟨⟨?_, hv1⟩, hs2, hsig2.trans hsig1, htrees2.trans htrees1, hexp2.trans hexp1,
    hcand2.trans hcand1, hmark2⟩
  have hvalues : r2.1.1 = fun l => (tree.topSignature.chainValue l).interpret s := funext hv2
  simp only [patchTree, interpretTree, hvalues]

end TreeRequest

end ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.sourceReturnTreeX_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.sourceReturnTreeX_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnChainX_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnChainX_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.treeKey_opening' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.treeKey_opening

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.treeKey_bottomChain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.treeKey_bottomChain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.treeKey_topChain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.treeKey_topChain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.pendingKey_topChain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.pendingKey_topChain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.TreeFrame.revealed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.TreeFrame.revealed_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.TreeFrame.revealed_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.TreeFrame.revealed_none

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.TreeFrame.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.TreeFrame.trans

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.syncIn_of_treeFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.syncIn_of_treeFrame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.safe_returnOpeningX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.safe_returnOpeningX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.releasePostIn_of_treeFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.releasePostIn_of_treeFrame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnOpening_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnOpening_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnOpening_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnOpening_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.revealsX_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.revealsX_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.top_next_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.top_next_suffix

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.runX_sourceRevealX_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.runX_sourceRevealX_revealed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.topStartX_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.topStartX_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnChain_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnChain_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.safe_returnChainX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.safe_returnChainX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnChain_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnChain_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.chains_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.chains_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnTree_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeRequest.returnTree_sync
