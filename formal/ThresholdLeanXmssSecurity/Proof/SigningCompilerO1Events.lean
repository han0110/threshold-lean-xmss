import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Sync
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Canonical

/-! # The final events of the O1 coupling

At the end of two runs that did not stop, the real event of `CompilerCouplingO1` gives the good
event of the compiler outcome. No logged input hits its target, the stale bit is clear, and the
lane 2 event passes to the compiler state.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Events
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Canonical
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

/-- A bottom chain input, a top chain input and a top digest input are outside the trial
inputs. So the log cache and the visible cache agree at them. -/
theorem outsideTrials_chain (P : PublicParameter) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (v : Digest)
    (bi : XmssSecurity.TopIndex) (payload : XmssSecurity.Digest × XmssSecurity.Randomness) :
    SigningPartnerCompareProof.OutsideTrials P
        (.hash (XmssSecurity.Concrete.CacheView.chainInput P e l p v) : Query C) ∧
      SigningPartnerCompareProof.OutsideTrials P
        (.hash (XmssSecurity.Concrete.CacheView.topChainInput P bi l p v) : Query C) ∧
      SigningPartnerCompareProof.OutsideTrials P
        (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput P bi payload) : Query C) := by
  refine ⟨⟨SigningCacheLogProof.tracked_hash _, fun e' payload' h => ?_⟩,
    ⟨SigningCacheLogProof.tracked_hash _, fun e' payload' h => ?_⟩,
    ⟨SigningCacheLogProof.tracked_hash _, fun e' payload' h => ?_⟩⟩
  · have h' := Query.hash.inj h
    rw [SigningGuessLinkProof.chainInput_eq_bridge] at h'
    have hb := byte23_chain P bottomLayer e p (Concrete.chainPayload l v)
    rw [h', byte23_msg] at hb
    exact hb rfl
  · have h' := Query.hash.inj h
    rw [SigningGuessLinkProof.topChainInput_eq_bridge] at h'
    have hb := byte23_chain P topLayer (topKey bi) p (Concrete.chainPayload l v)
    rw [h', byte23_msg] at hb
    exact hb rfl
  · have h' := Query.hash.inj h
    have hm := XmssSecurity.Bridge.topMessage_input P bi payload.1 payload.2
    unfold XmssSecurity.Concrete.CacheView.topEncodingInput at h'
    rw [← hm] at h'
    have hf := congrArg (fun f => f.hi.toNat) (tweakableInput_injective h').1
    norm_num [hashDomainFields, tweakFields, layerHi, topLayer, bottomLayer] at hf

/-- An `Option` traversal that succeeds has an output at each element. -/
theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ a ∈ l, (f a).isSome
  | [], _, _, a, ha => absurd ha List.not_mem_nil
  | b :: l, ys, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hb : f b with
    | none => simp [hb] at h
    | some w =>
      cases hl : l.mapM f with
      | none => simp [hb, hl] at h
      | some zs =>
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [hb]
        · exact mapM_isSome f l zs hl a ha

/-- An `Option` traversal that succeeds is the map of a function that each output matches. -/
theorem mapM_eq_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α) (ys : List β), (∀ a ∈ l, ∀ b, f a = some b → b = g a) →
      l.mapM f = some ys → ys = l.map g
  | [], ys, _, h => by
    simp only [List.mapM_nil] at h
    exact (Option.some.inj h).symm
  | b :: l, ys, hf, h => by
    rw [List.mapM_cons] at h
    cases hb : f b with
    | none => simp [hb] at h
    | some w =>
      cases hl : l.mapM f with
      | none => simp [hb, hl] at h
      | some zs =>
        simp only [hb, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        rw [← h, List.map_cons, hf b List.mem_cons_self w hb,
          mapM_eq_map f g l zs (fun a ha => hf a (List.mem_cons_of_mem b ha)) hl]

/-- A left fold of the exclusive or is the start value with the right fold. -/
theorem foldl_xor_eq (a : Digest) :
    ∀ l : List Digest, l.foldl (· ^^^ ·) a = a ^^^ l.foldr (· ^^^ ·) 0
  | [] => by simp
  | b :: l => by
    rw [List.foldl_cons, foldl_xor_eq (a ^^^ b) l, List.foldr_cons, BitVec.xor_assoc]

/-- A walk of three steps from `σ 0`, where each step maps `σ j` to `σ (j + 1)`, ends at `σ p`. -/
theorem walk_chain (step : ℕ → Digest → Digest) (σ : XmssSecurity.ChainStep → Digest)
    (hstep : ∀ (j : XmssSecurity.ChainStep) (hj : j.val + 1 < 3),
      step j.val (σ j) = σ ⟨j.val + 1, hj⟩)
    (p : XmssSecurity.ChainStep) :
    XmssSecurity.Wots.walk step 0 p.val (σ ⟨0, by decide⟩) = σ p := by
  obtain ⟨p, hp⟩ := p
  rcases p with _ | _ | _ | p
  · rfl
  · exact hstep ⟨0, by decide⟩ (by decide)
  · change step (0 + 1) (step (0 + 0) (σ ⟨0, by decide⟩)) = _
    rw [show step (0 + 0) (σ ⟨0, by decide⟩) = σ ⟨1, by decide⟩ from
      hstep ⟨0, by decide⟩ (by decide)]
    exact hstep ⟨1, by decide⟩ (by decide)
  · exact absurd hp (by change ¬(_ < 3); omega)

/-- A pending bottom chain edge maps its secret to the next secret on a cache that agrees with
the visible cache outside the trial inputs. -/
theorem bottom_cell (s : HiddenKey → Digest) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (data : DeferredState C) (vis log : HashCache C) (hcache : CacheRelation P seeds s data vis)
    (hvalid : PendingValid data)
    (hout : ∀ q, SigningPartnerCompareProof.OutsideTrials P q → vis q = log q)
    (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (j : XmssSecurity.ChainStep)
    (hj : j.val + 1 < 3) (hp : data.pending (.bottom e l j) ≠ none) :
    SigningDescentProof.bottomStep log P e l j.val (s (.bottomChain e l j)) =
      s (.bottomChain e l ⟨j.val + 1, hj⟩) := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
  have hvis := hcache.pending _ v hv
  have hlog : log (.hash (XmssSecurity.Concrete.CacheView.chainInput P e l j (s (.bottomChain e l j)))) =
      some (v.interpret s) :=
    (hout _ (outsideTrials_chain P e l j _ ⟨0, by decide⟩ (0, 0)).1).symm.trans hvis
  have htr := pending_truncate_next data hvalid _ v hv (.bottomChain e l ⟨j.val + 1, hj⟩)
    (by simp only [PendingInput.next, dif_pos hj]) s
  unfold SigningDescentProof.bottomStep XmssSecurity.Concrete.CacheView.chainStep
  rw [dif_pos j.isLt]
  unfold XmssSecurity.Concrete.CacheView.digestAt
  have hth : SigningDescentProof.thView log (XmssSecurity.Concrete.CacheView.chainInput P e l
      ⟨j.val, j.isLt⟩ (s (.bottomChain e l j))) = some (v.interpret s) := hlog
  rw [hth]
  exact htr

/-- A pending top chain edge maps its secret to the next secret on a cache that agrees with the
visible cache outside the trial inputs. -/
theorem top_cell (s : HiddenKey → Digest) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (data : DeferredState C) (vis log : HashCache C) (hcache : CacheRelation P seeds s data vis)
    (hvalid : PendingValid data)
    (hout : ∀ q, SigningPartnerCompareProof.OutsideTrials P q → vis q = log q)
    (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (j : XmssSecurity.ChainStep)
    (hj : j.val + 1 < 3) (hp : data.pending (.top (XmssSecurity.topKeyOf e) l j) ≠ none) :
    SigningDescentProof.topStep log P e l j.val (s (.topChain (XmssSecurity.topKeyOf e) l j)) =
      s (.topChain (XmssSecurity.topKeyOf e) l ⟨j.val + 1, hj⟩) := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
  have hvis := hcache.pending _ v hv
  have hlog : log (.hash (XmssSecurity.Concrete.CacheView.topChainInput P (XmssSecurity.topKeyOf e) l j
      (s (.topChain (XmssSecurity.topKeyOf e) l j)))) = some (v.interpret s) :=
    (hout _ (outsideTrials_chain P e l j _ (XmssSecurity.topKeyOf e) (0, 0)).2.1).symm.trans hvis
  have htr := pending_truncate_next data hvalid _ v hv
    (.topChain (XmssSecurity.topKeyOf e) l ⟨j.val + 1, hj⟩) (by simp only [PendingInput.next, dif_pos hj]) s
  unfold SigningDescentProof.topStep XmssSecurity.Concrete.CacheView.topChainStep
  rw [dif_pos j.isLt]
  unfold XmssSecurity.Concrete.CacheView.digestAt
  have hth : SigningDescentProof.thView log (XmssSecurity.Concrete.CacheView.topChainInput P
      (XmssSecurity.topKeyOf e) l ⟨j.val, j.isLt⟩ (s (.topChain (XmssSecurity.topKeyOf e) l j))) =
      some (v.interpret s) := hlog
  rw [hth]
  exact htr

section Targets
variable (prims : Primitives) (x : Keys3 C)

/-- A bottom chain target is the honest walk from the cached chain start at the key of the
forgery, and the chain start is cached. -/
theorem partialBottom_value (r : SigningGuessLinkProof.LoggedOutcome C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep)
    (v : Digest)
    (hv : SigningGuardedFlagProof.partialChainTarget prims x r (.bottomChain e l p) = some v) :
    SigningGuardedFlagProof.StartsCached x r.2.1 bottomLayer e l ∧
      e = forgery.signature.leafIndex ∧
      v = SigningDescentProof.honestValue (SigningDescentProof.bottomStep r.2.1 x.1 e)
        (fun l => D prims (SigningCacheProof.answersOf r.2.1)
          (prfValue x.2.1 (.chain bottomLayer e l (digit 0)))) l p.val := by
  unfold SigningGuardedFlagProof.partialChainTarget at hv
  by_cases hs : SigningGuardedFlagProof.KeyStartsCached x r.2.1 (.bottomChain e l p)
  · rw [if_pos hs] at hv
    simp only [SigningGuessLinkProof.chainTarget, hm] at hv
    split_ifs at hv with hc
    obtain ⟨he, -⟩ := hc
    subst he
    exact ⟨hs, rfl, (Option.some.inj hv).symm⟩
  · rw [if_neg hs] at hv
    cases hv

/-- A partial top chain target is the honest walk from the cached chain start at the top key of
the forgery, and the chain start is cached. -/
theorem partialTop_value (r : SigningGuessLinkProof.LoggedOutcome C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep)
    (v : Digest)
    (hv : SigningGuardedFlagProof.partialChainTarget prims x r (.topChain b l p) = some v) :
    SigningGuardedFlagProof.StartsCached x r.2.1 topLayer (topKey b) l ∧
      b = XmssSecurity.topKeyOf forgery.signature.leafIndex ∧
      v = SigningDescentProof.honestValue
        (SigningDescentProof.topStep r.2.1 x.1 forgery.signature.leafIndex)
        (fun l => D prims (SigningCacheProof.answersOf r.2.1)
          (prfValue x.2.1 (.chain topLayer (topKey b) l (digit 0)))) l p.val := by
  unfold SigningGuardedFlagProof.partialChainTarget at hv
  by_cases hs : SigningGuardedFlagProof.KeyStartsCached x r.2.1 (.topChain b l p)
  · rw [if_pos hs] at hv
    simp only [SigningGuessLinkProof.chainTarget, hm] at hv
    split_ifs at hv with hc
    obtain ⟨he, -⟩ := hc
    subst he
    exact ⟨hs, rfl, (Option.some.inj hv).symm⟩
  · rw [if_neg hs] at hv
    cases hv

/-- An unopened top target is the honest walk from the cached chain start at the top key of the
forgery, and the chain start is cached. -/
theorem unopenedTop_value (r : SigningGuessLinkProof.LoggedOutcome C) (top : TopTree)
    (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep)
    (v : Digest)
    (hv : SigningTopRowsProof.unopenedTopTarget prims x r (.topChain b l p) = some v) :
    SigningGuardedFlagProof.StartsCached x r.2.1 topLayer (topKey b) l ∧
      b = XmssSecurity.topKeyOf forgery.signature.leafIndex ∧
      v = SigningDescentProof.honestValue
        (SigningDescentProof.topStep r.2.1 x.1 forgery.signature.leafIndex)
        (fun l => D prims (SigningCacheProof.answersOf r.2.1)
          (prfValue x.2.1 (.chain topLayer (topKey b) l (digit 0)))) l p.val := by
  simp only [SigningTopRowsProof.unopenedTopTarget, hm] at hv
  split_ifs at hv with hc
  obtain ⟨he, -, hs⟩ := hc
  subst he
  exact ⟨hs, rfl, (Option.some.inj hv).symm⟩

set_option maxRecDepth 100000 in
/-- The setup run below a cache gives the top tree on the answers of the cache. -/
theorem topRun_D (top : TopTree) (cache : HashCache C) (h : TopRun prims x top cache) :
    D prims (SigningCacheProof.answersOf cache)
      (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) = some (.top top) := by
  obtain ⟨start, result, hr, h1, hle⟩ := h
  have hval := SigningCacheProof.run_liftFree prims _ start result hr
    (SigningCacheProof.answersOf cache) (SigningCacheProof.agrees_answersOf hle)
  rw [← hval, h1]

set_option maxRecDepth 100000 in
/-- The setup run below a cache gives the top facts on the answers of the cache. -/
theorem topFacts_of_topRun (top : TopTree) (cache : HashCache C) (h : TopRun prims x top cache) :
    TopFacts prims (SigningCacheProof.answersOf cache) x.2.1 x.1 top := by
  obtain ⟨generated, hgen, hchain, hroot⟩ :=
    D_refTop (prims := prims) (h := SigningCacheProof.answersOf cache) x.1 x.2.1 emptyTop
  have heq : generated = top :=
    TreeOutput.top.inj (Option.some.inj (hgen.symm.trans (topRun_D prims x top cache h)))
  subst heq
  exact ⟨hchain, hroot⟩

end Targets

section Final
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The lane 2 event passes to the compiler state. -/
theorem final_ghost (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c)
    (hghost : SigningLaneUnionProof.GhostAt x z.1)
    (hq : (SigningLaneUnionProof.observed z.1).2.1 ≤ q) :
    compilerEvent x.1 q (SigningCompilerShareTables.finish x.2.1 c).1.2.1 := by
  obtain ⟨vlog, win, -, ⟨⟨hfields, hcache⟩, hcount⟩, -, rev, -, hextra⟩ := hf
  have hview := hcache.keptView
  have htrace := hfields.trace
  have hstale := hextra.staleFree
  refine ⟨?_, ?_, ?_⟩
  · change c.2.1.1.1.1.trace.2 = false
    rw [← htrace]
    exact hstale
  · have hv : compilerView (SigningCompilerShareTables.finish x.2.1 c).1.2.1.1 =
        SigningLaneUnionProof.traceView z.1.2 := by
      unfold compilerView SigningLaneUnionProof.traceView
      refine Prod.ext ?_ ?_
      · exact hview.symm
      · exact (congrArg Prod.fst htrace).symm
    unfold SigningLaneUnionProof.GhostAt SigningLane2Proof.ghostEvent at hghost
    unfold SigningLane2Proof.ghostEvent
    rw [hv]
    exact hghost
  · change c.2.1.1.1.2 ≤ q
    rw [← hcount]
    exact hq

/-- At a constrained randomizer point, an opening value that a cache below the visible cache
gives is the secret. -/
theorem cachedOpening_constrained (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (priv vis cache : HashCache C) (h : RealPrivate x s pads noise (gOf s pads u) rest priv vis)
    (hle : cache ≤ vis) (lay : Layer) (e : KeyIndex) (hc : Constrained (.randomizer lay e))
    (v : Digest) (hv : cachedOpening x cache (lay, e) = some v) :
    v = s (.opening lay e) := by
  let cp : CPoint := ⟨.randomizer lay e, hc⟩
  unfold cachedOpening at hv
  obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp hv
  have hmap := mapM_eq_map _ (fun T => truncateHash (gOf s pads u (T, cp))) C.terms ys
    (fun T _ b hb => by
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hb
      have hw' := realPrivate_slotValue x hkeys s pads noise _ rest priv vis h
        (.inl (T, .randomizer lay e)) w (hle hw)
      rw [realTable_constrained _ rest T cp] at hw'
      rw [hw']) hys
  subst hmap
  rw [foldl_xor_eq, List.foldr_map]
  refine (BitVec.zero_xor (x := _)).trans ?_
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.fiberTable_sum C.terms terms_nodup mem_terms
    (SigningCompilerShare.NoFalse.tau s pads) _
    (SigningShareLazy.good_init _ _ (Or.inl (List.ne_nil_of_mem (mem_terms T)))) u cp

/-- No opening candidate hits its target. -/
theorem final_no_opening_hit (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c) (hstop : ¬Stop c.2)
    (hflag : SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z.1))
    (cand : HiddenKey × Digest) (hc : cand ∈ z.1.1.2) (lay : Layer) (e : KeyIndex)
    (hk : cand.1 = .opening lay e) :
    cachedOpening x (loggedOf z.1).2.1 (lay, e) ≠ some cand.2 := by
  obtain ⟨vlog, win, hz, ⟨⟨hfields, -⟩, -⟩, -, rev, -, hextra⟩ := hf
  have hcand : cand ∈ c.1.2.base.candidates := by
    have h2 : z.1.1.2 = (realEnd z).1.2.2.2 ++ vlog := congrArg Prod.snd hz
    rw [hfields.candidates]
    change cand ∈ (realEnd z).1.2.2.2 ++ vlog
    rw [← h2]
    exact hc
  have hfresh := hextra.openingFresh cand hcand lay e hk
  have hle : (loggedOf z.1).2.1 ≤ visibleOf (realEnd z) := hextra.logAgreement.1
  intro hhit
  by_cases hcon : Constrained (.randomizer lay e)
  · apply hfresh
    rw [hk]
    exact cachedOpening_constrained x s pads u rest noise hkeys _ _ _ hfields.realPrivate hle
      lay e hcon cand.2 hhit
  · have hrf : realFlag (realEnd z) = false := by
      have h1 := congrArg (fun w => w.1.1.2) hz
      exact h1.symm.trans hflag
    obtain ⟨T, hT⟩ := exists_lacked_term _ hextra.corruptBound
    have hnone : visibleOf (realEnd z) (.prf (x.2.1 T) (.randomizer lay e)) = none := by
      by_contra hne
      rcases hextra.prfSeen hrf T _ hne with h | h
      · exact hT h
      · exact hcon h
    unfold cachedOpening at hhit
    obtain ⟨ys, hys, -⟩ := Option.map_eq_some_iff.mp hhit
    have hT' := mapM_isSome _ C.terms ys hys T (mem_terms T)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hT'
    obtain ⟨w', hw', -⟩ := Option.map_eq_some_iff.mp hw
    have := hle hw'
    rw [hnone] at this
    cases this

/-- With every term cached below the visible cache, the threshold PRF value at a constrained
point is its fixed target. -/
theorem prfValue_constrained (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (priv vis cache : HashCache C) (h : RealPrivate x s pads noise (gOf s pads u) rest priv vis)
    (hle : cache ≤ vis) (cp : CPoint)
    (hc : ∀ T ∈ C.terms, (cache (.prf (x.2.1 T) cp.val)).isSome) :
    D prims (SigningCacheProof.answersOf cache) (prfValue x.2.1 cp.val) = tauOf s pads cp := by
  rw [prfValue, D_bind, D_mapM, D_pure]
  simp only [prf, D_map, D_hashQuery]
  have hmap : (C.terms.map fun T => truncateHash (SigningCacheProof.answersOf cache (.prf (x.2.1 T) cp.val))) =
      C.terms.map fun T => truncateHash (gOf s pads u (T, cp)) := by
    refine List.map_congr_left fun T hT => ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hc T hT)
    have hw' := realPrivate_slotValue x hkeys s pads noise _ rest priv vis h
      (.inl (T, cp.val)) w (hle hw)
    rw [realTable_constrained _ rest T cp] at hw'
    simp only [SigningCacheProof.answersOf, hw, Option.getD_some, hw']
  rw [hmap, foldl_xor_eq, List.foldr_map]
  refine (BitVec.zero_xor (x := _)).trans ?_
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.fiberTable_sum C.terms terms_nodup mem_terms
    (SigningCompilerShare.NoFalse.tau s pads) _
    (SigningShareLazy.good_init _ _ (Or.inl (List.ne_nil_of_mem (mem_terms T)))) u cp

set_option maxRecDepth 100000 in
/-- No top chain candidate hits one of its two targets. -/
theorem final_no_top_hit (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c) (hstop : ¬Stop c.2)
    (hflag : SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z.1))
    (cand : HiddenKey × Digest) (hc : cand ∈ z.1.1.2) (bi : XmssSecurity.TopIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (hk : cand.1 = .topChain bi l p) :
    SigningGuardedFlagProof.partialChainTarget prims x (loggedOf z.1) cand.1 ≠ some cand.2 ∧
      SigningTopRowsProof.unopenedTopTarget prims x (loggedOf z.1) cand.1 ≠ some cand.2 := by
  obtain ⟨vlog, win, hz, ⟨⟨hfields, hcache⟩, -⟩, htopo, rev, -, hextra⟩ := hf
  have hm : (loggedOf z.1).1.1.2 = some (c.1.1.2.1, realSigning (realEnd z), c.1.1.2.2) :=
    congrArg (fun w => w.1.2) hz
  have hcand : cand ∈ c.1.2.base.candidates := by
    have h2 : z.1.1.2 = (realEnd z).1.2.2.2 ++ vlog := congrArg Prod.snd hz
    rw [hfields.candidates]
    change cand ∈ (realEnd z).1.2.2.2 ++ vlog
    rw [← h2]
    exact hc
  have hle : (loggedOf z.1).2.1 ≤ visibleOf (realEnd z) := hextra.logAgreement.1
  have hout : ∀ q, SigningPartnerCompareProof.OutsideTrials x.1 q →
      visibleOf (realEnd z) q = (loggedOf z.1).2.1 q := hextra.logAgreement.2
  have core : ∀ v : Digest,
      SigningGuardedFlagProof.StartsCached x (loggedOf z.1).2.1 topLayer (topKey bi) l →
      bi = XmssSecurity.topKeyOf c.1.1.2.2.signature.leafIndex →
      v = SigningDescentProof.honestValue
        (SigningDescentProof.topStep (loggedOf z.1).2.1 x.1 c.1.1.2.2.signature.leafIndex)
        (fun l => D prims (SigningCacheProof.answersOf (loggedOf z.1).2.1)
          (prfValue x.2.1 (.chain topLayer (topKey bi) l (digit 0)))) l p.val →
      v = cand.2 →
      SigningGuessLinkProof.chainTarget prims x (loggedOf z.1) (.topChain bi l p) = none ∧
        SigningTopRowsProof.unopenedTopTarget prims x (loggedOf z.1) (.topChain bi l p) = none := by
    intro v hsc hb hval hv
    subst hv hb
    have hstart : D prims (SigningCacheProof.answersOf (loggedOf z.1).2.1)
        (prfValue x.2.1 (.chain topLayer (topKey (XmssSecurity.topKeyOf c.1.1.2.2.signature.leafIndex)) l
          (digit 0))) = s (.topChain (XmssSecurity.topKeyOf c.1.1.2.2.signature.leafIndex) l ⟨0, by decide⟩) := by
      refine (prfValue_constrained prims x s pads u rest noise hkeys _ _ _ hfields.realPrivate hle
        ⟨_, constrained_top_chain _ l⟩ hsc).trans ?_
      exact SigningCompilerShare.NoFalse.tau_top_start s pads _ l
    have hvs : cand.2 = s cand.1 := by
      rw [hval, hk]
      unfold SigningDescentProof.honestValue
      exact (congrArg (XmssSecurity.Wots.walk _ 0 p.val) hstart).trans
        (walk_chain _ (fun j => s (.topChain (XmssSecurity.topKeyOf c.1.1.2.2.signature.leafIndex) l j))
          (fun j hj => top_cell s x.1 x.2.1 (dataOf x c.2) _ _ hcache hfields.pendingValid hout _ l j hj
            (htopo.topRows _ l j)) p)
    have hpaid := hextra.candidatesPaid cand hcand hvs
    rw [hk] at hpaid
    obtain ⟨-, dtree, hdtree, hdigit⟩ := hextra.revealedTop _ l p hpaid
    have htrees : (realSigning (realEnd z)).trees (treeOf c.1.1.2.2.signature.leafIndex) =
        some (some (interpretTree s (treeOf c.1.1.2.2.signature.leafIndex) dtree)) := by
      have h1 := hextra.storedTrees (treeOf c.1.1.2.2.signature.leafIndex)
      change _ = (c.1.2.base.trees (XmssSecurity.topKeyOf c.1.1.2.2.signature.leafIndex)).map _ at h1
      rw [hdtree] at h1
      exact h1
    obtain ⟨start, result, hrun, h1, hlog⟩ := hextra.storedRuns _ _ htrees
    rw [← SigningHitProof.hashEmbed_referenceTree] at hrun
    have hres := (SigningHitProof.run_hashEmbed_resolves prims _ start result hrun).mono hlog
    rw [h1] at hres
    exact top_covered_not_target prims x (loggedOf z.1) c.1.1.2.1 (realSigning (realEnd z)) c.1.1.2.2 hm
      (topRun_D prims x _ _ htopo.topRun) _ hres dtree.topSignature.encoding
      (hextra.storedTopDigit _ dtree hdtree).2 l p hdigit
  refine ⟨fun hhit => ?_, fun hhit => ?_⟩
  · rw [hk] at hhit
    obtain ⟨hsc, hb, hval⟩ := partialTop_value prims x _ _ _ _ hm bi l p cand.2 hhit
    have hnone := (core cand.2 hsc hb hval rfl).1
    unfold SigningGuardedFlagProof.partialChainTarget at hhit
    rw [if_pos (show SigningGuardedFlagProof.KeyStartsCached x _ (.topChain bi l p) from hsc),
      hnone] at hhit
    cases hhit
  · rw [hk] at hhit
    obtain ⟨hsc, hb, hval⟩ := unopenedTop_value prims x _ _ _ _ hm bi l p cand.2 hhit
    rw [(core cand.2 hsc hb hval rfl).2] at hhit
    cases hhit

set_option maxRecDepth 100000 in
/-- No bottom chain candidate hits its target. This lemma uses the gate. -/
theorem final_no_bottom_hit (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c) (hstop : ¬Stop c.2)
    (hflag : SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z.1))
    (hnc : SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z.1))
    (cand : HiddenKey × Digest) (hc : cand ∈ z.1.1.2) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (hk : cand.1 = .bottomChain e l p) :
    SigningGuardedFlagProof.partialChainTarget prims x (loggedOf z.1) cand.1 ≠ some cand.2 := by
  obtain ⟨vlog, win, hz, ⟨⟨hfields, hcache⟩, -⟩, htopo, rev, -, hextra⟩ := hf
  have hm : (loggedOf z.1).1.1.2 = some (c.1.1.2.1, realSigning (realEnd z), c.1.1.2.2) :=
    congrArg (fun w => w.1.2) hz
  have hcand : cand ∈ c.1.2.base.candidates := by
    have h2 : z.1.1.2 = (realEnd z).1.2.2.2 ++ vlog := congrArg Prod.snd hz
    rw [hfields.candidates]
    change cand ∈ (realEnd z).1.2.2.2 ++ vlog
    rw [← h2]
    exact hc
  have hrf : realFlag (realEnd z) = false := by
    have h1 : z.1.1.1.1.2 = realFlag (realEnd z) := congrArg (fun w => w.1.1.2) hz
    exact h1.symm.trans hflag
  have hle : (loggedOf z.1).2.1 ≤ visibleOf (realEnd z) := hextra.logAgreement.1
  have hout : ∀ q, SigningPartnerCompareProof.OutsideTrials x.1 q →
      visibleOf (realEnd z) q = (loggedOf z.1).2.1 q := hextra.logAgreement.2
  intro hhit
  rw [hk] at hhit
  obtain ⟨hsc, he, hval⟩ := partialBottom_value prims x _ _ _ _ hm e l p cand.2 hhit
  obtain ⟨T, hT⟩ := exists_lacked_term _ hextra.corruptBound
  have hTvis : visibleOf (realEnd z)
      (.prf (x.2.1 T) (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit ⟨0, by decide⟩))) ≠
      none := by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hsc T (mem_terms T))
    have hw' := hle hw
    change visibleOf (realEnd z) (.prf (x.2.1 T) (.chain bottomLayer e l (digit 0))) ≠ none
    rw [hw']
    exact Option.some_ne_none w
  have hrows := (hextra.bottomSeen hrf T e l ⟨0, by decide⟩ hTvis).resolve_left hT
  have hstart : D prims (SigningCacheProof.answersOf (loggedOf z.1).2.1)
      (prfValue x.2.1 (.chain bottomLayer e l (digit 0))) = s (.bottomChain e l ⟨0, by decide⟩) := by
    have h0 := prfValue_constrained prims x s pads u rest noise hkeys _ _ _ hfields.realPrivate hle
      ⟨.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit ⟨0, by decide⟩),
        constrained_bottom_chain e l _ (by decide)⟩ hsc
    refine h0.trans ?_
    change SigningCompilerShare.NoFalse.tau s pads _ = _
    rw [SigningCompilerShare.NoFalse.tau_bottom_chain]
    simp
  have hvs : cand.2 = s cand.1 := by
    rw [hval, hk]
    unfold SigningDescentProof.honestValue
    exact (congrArg (XmssSecurity.Wots.walk _ 0 p.val) hstart).trans
      (walk_chain _ (fun j => s (.bottomChain e l j))
        (fun j hj => bottom_cell s x.1 x.2.1 (dataOf x c.2) _ _ hcache hfields.pendingValid hout e l j hj
          (hrows j)) p)
  have hpaid := hextra.candidatesPaid cand hcand hvs
  rw [hk] at hpaid
  have hcov := hextra.revealedCovered e l p hpaid
  subst he
  have hnone := covered_not_target prims x (loggedOf z.1) c.1.1.2.1 (realSigning (realEnd z)) c.1.1.2.2 hm
    (topFacts_of_topRun prims x _ _ htopo.topRun) (fun h => hnc (Or.inr (Or.inl h)))
    (c.1.2.starts c.1.1.2.2.signature.leafIndex)
    (fun l d hd => hextra.startsTraced _ l d hd) l p hcov
  unfold SigningGuardedFlagProof.partialChainTarget at hhit
  rw [if_pos (show SigningGuardedFlagProof.KeyStartsCached x _ (.bottomChain _ l p) from hsc),
    hnone] at hhit
  cases hhit

set_option maxRecDepth 100000 in
/-- No input-side hit at the end. -/
theorem final_no_input_hit (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c) (hstop : ¬Stop c.2)
    (hflag : SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z.1))
    (hnc : SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z.1)) :
    ¬SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z.1) := by
  rintro (⟨⟨key, v⟩, hc, ht⟩ | ⟨⟨key, v⟩, hc, ht⟩)
  · cases key with
    | opening lay e =>
      exact final_no_opening_hit prims x s pads u rest noise hkeys z c hf hstop hflag _ hc lay e rfl ht
    | bottomChain e l p =>
      exact final_no_bottom_hit prims x s pads u rest noise hkeys z c hf hstop hflag hnc _ hc e l p rfl ht
    | topChain b l p =>
      exact (final_no_top_hit prims x s pads u rest noise hkeys z c hf hstop hflag _ hc b l p rfl).1 ht
  · cases key with
    | opening lay e =>
      exact final_no_opening_hit prims x s pads u rest noise hkeys z c hf hstop hflag _ hc lay e rfl ht
    | bottomChain e l p =>
      obtain ⟨vlog, win, hz, -⟩ := hf
      have hm : (SigningLaneUnionProof.observed z.1).1.1.2 =
          some (c.1.1.2.1, realSigning (realEnd z), c.1.1.2.2) := congrArg (fun w => w.1.2) hz
      simp only [SigningTopRowsProof.unopenedTopTarget, hm] at ht
      cases ht
    | topChain b l p =>
      exact (final_no_top_hit prims x s pads u rest noise hkeys z c hf hstop hflag _ hc b l p rfl).2 ht

/-- The real event gives the good compiler event at two runs that did not stop. -/
theorem final_event (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c) (hstop : ¬Stop c.2)
    (hE : RealEvent prims x z.1) (hq : (SigningLaneUnionProof.observed z.1).2.1 ≤ q) :
    CompGood x q (SigningCompilerShareTables.finish x.2.1 c).1 := by
  obtain ⟨hflag, hnc, hev⟩ := hE
  have hf0 := hf
  obtain ⟨vlog, win, hz, ⟨⟨hfields, -⟩, -⟩, -, rev, -, hextra⟩ := hf
  refine ⟨?_, Or.inr ?_⟩
  · change c.1.2.base.hiddenFlag = false
    rw [hfields.flag]
    have h1 : z.1.1.1.1.2 = realFlag (realEnd z) := congrArg (fun w => w.1.1.2) hz
    exact h1.symm.trans hflag
  · rcases hev with hhit | hstale | hghost
    · exact absurd hhit (final_no_input_hit prims x s pads u rest noise hkeys z c hf0 hstop hflag hnc)
    · exact absurd (hstale.symm.trans hextra.staleFree) Bool.noConfusion
    · exact final_ghost prims x q s pads u rest noise z c hf0 hghost hq

end Final

end ThresholdLeanXmssSecurity.SigningCompilerO1Events

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.outsideTrials_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.outsideTrials_chain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_ghost

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_opening_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_opening_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_top_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_top_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_bottom_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_bottom_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_input_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_no_input_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Events.final_event
