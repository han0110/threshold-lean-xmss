import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRows

/-! # Bottom suffix release against a fixed real table

The actual two-loop suffix release either reaches a persistent stopping event or
preserves synchronization with the fixed real state. Only the requested suffix
is revealed; all source control fields and compiler counters remain unchanged.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncChain SigningCompilerSyncRows XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Control fields shared by completion and planting frames. -/
structure ReleaseFrame (x : Keys3 C) (b b' : SourceState C × CompState C) : Prop where
  signing : b'.1.signing = b.1.signing
  trees : b'.1.trees = b.1.trees
  exposed : b'.1.exposed = b.1.exposed
  allocated : b'.1.allocated = b.1.allocated
  candidates : b'.1.candidates = b.1.candidates
  hiddenFlag : b'.1.hiddenFlag = b.1.hiddenFlag
  pending : (dataOf x b'.2).pending = (dataOf x b.2).pending
  virtual : (dataOf x b'.2).virtual = (dataOf x b.2).virtual
  cache : (dataOf x b.2).cache ≤ (dataOf x b'.2).cache
  count : b'.2.1.1.1.2 = b.2.1.1.1.2
  trace : b'.2.1.1.1.1.trace = b.2.1.1.1.1.trace
  bound : b'.2.1.1.1.1.bound = b.2.1.1.1.1.bound
  mark : b'.2.1.2 = b.2.1.2

/-- All bookkeeping and revealed-coordinate effects of the canonical suffix. -/
structure SuffixFrame (x : Keys3 C) (s : HiddenKey → Digest) (e : KeyIndex)
    (l : ChainIndex) (start : Digit) (b b' : SourceState C × CompState C) : Prop
    extends ReleaseFrame x b b' where
  revealed : ∀ k, (∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
    k ≠ .bottomChain e l d) → b'.1.revealed k = b.1.revealed k
  suffix : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
    b'.1.revealed (.bottomChain e l d) = some (s (.bottomChain e l d))

theorem ReleaseFrame.refl (x : Keys3 C) (b : SourceState C × CompState C) :
    ReleaseFrame x b b := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, rfl, rfl, rfl, rfl⟩

theorem ReleaseFrame.trans {x : Keys3 C} {a b c : SourceState C × CompState C}
    (h : ReleaseFrame x a b) (j : ReleaseFrame x b c) : ReleaseFrame x a c :=
  ⟨j.signing.trans h.signing, j.trees.trans h.trees, j.exposed.trans h.exposed,
    j.allocated.trans h.allocated, j.candidates.trans h.candidates,
    j.hiddenFlag.trans h.hiddenFlag, j.pending.trans h.pending, j.virtual.trans h.virtual,
    h.cache.trans j.cache, j.count.trans h.count, j.trace.trans h.trace,
    j.bound.trans h.bound, j.mark.trans h.mark⟩

/-- Persistent Stop lifted through an arbitrary X-source continuation. -/
theorem runX_stop {α : Type} (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : SourceMX C α) (src : SourceState C) (st : CompState C) (h : Stop st)
    (r : (α × SourceState C) × CompState C)
    (hr : r ∈ support (runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      oa src st)) : Stop r.2 :=
  simulateQ_sticky _ Stop (backendT_stop x.1 x.2.1 x.2.2 q s pads τ g noise rest)
    (oa.run src) st h r hr

/-- The actual reveal-pad-complete body, factored out of the source list. -/
def bottomCompletionX (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep) : SourceMX C Unit := do
  let value ← sourceRevealX (.bottomChain e l d)
  let offset ← if d.val = 0 then pure (0 : Digest) else
    (show SourceMX C Digest from liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (chainStepDigit d)))))
  let ok ← liftM (completeQ (C := C) (.chain bottomLayer e l (chainStepDigit d)) (value ^^^ offset))
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }

theorem sourceReleaseBottomSuffixX_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    sourceReleaseBottomSuffixX P seeds e l start = (do
      let keys := (List.finRange 3).filter fun d => start.val ≤ d.val
      let _ ← keys.mapM (bottomCompletionX (C := C) e l)
      let _ ← keys.mapM fun d => sourcePlantX P (.bottom e l d)
      pure ()) := rfl

/-- The first loop has not yet planted its newly revealed pending inputs. -/
structure CompletionPost (x : Keys3 C) (s : HiddenKey → Digest)
    (g : C.Term × CPoint → HashOutput) (visible : HashCache C)
    (e : KeyIndex) (l : ChainIndex) (positions : List XmssSecurity.ChainStep)
    (b b' : SourceState C × CompState C) : Prop extends ReleaseFrame x b b' where
  reveal : RevealRelation s b'.1 b'.2.1.1
  agreement : CacheRelation x.1 x.2.1 s (dataOf x b'.2) visible
  restFree : RestFree x.2.1 b'.2.1.1.1.1.data.cache
  share : ShareG g b'.2.2
  doneCached : DoneCached b'.2.2
  bad : b'.2.2.bad = none
  outside : ∀ k, (∀ d ∈ positions, k ≠ .bottomChain e l d) → b'.1.revealed k = b.1.revealed k
  allRevealed : ∀ d ∈ positions, b'.1.revealed (.bottomChain e l d) = some (s (.bottomChain e l d))

/-- Updating the pad map changes no other compiler component. -/
def padState (st : CompState C) (pads : Point → Option Digest) : CompState C :=
  (((({ st.1.1.1.1 with data := { st.1.1.1.1.data with pads := pads } }, st.1.1.1.2),
    st.1.1.2), st.1.2), st.2)

theorem runX_pad (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (p : Point) (src : SourceState C) (st : CompState C)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (liftM (deferredQueryX (C := C) (.pad p))) src st =
    pure (((padStep pads p st.1.1).1, src), ((padStep pads p st.1.1).2, st.1.2), st.2) := by
  simp [runX, deferredQueryX]
  rw [backendT_pad capTag x q s pads τ g noise rest p st hf]
  rfl

theorem offset_frame (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep)
    (src : SourceState C) (st : CompState C)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (r : (Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (if d.val = 0 then pure (0 : Digest) else
        liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (chainStepDigit d))))) src st)) :
    r.1.2 = src ∧ r.2 = padState st r.2.1.1.1.1.data.pads := by
  split at hr
  · rw [runX_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, rfl⟩
  · rw [runX_pad x q s pads τ g noise rest _ src st hf, mem_support_pure_iff] at hr
    subst r
    cases hp : st.1.1.1.1.data.pads (.chain bottomLayer e l (chainStepDigit d)) <;>
      simp only [padStep, hp] <;> exact ⟨trivial, rfl⟩

theorem bottomCompletionX_eq (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep) :
    bottomCompletionX (C := C) e l d =
      (sourceRevealX (.bottomChain e l d) >>= fun value =>
        (if d.val = 0 then pure (0 : Digest) else
          (show SourceMX C Digest from liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (chainStepDigit d)))))) >>=
          fun offset => liftM (completeQ (C := C) (.chain bottomLayer e l (chainStepDigit d)) (value ^^^ offset)) >>=
            fun ok => modify fun st => { st with consistent := st.consistent && ok }) := by
  unfold bottomCompletionX
  congr 1
  funext value
  split <;> rfl

/-- One actual completion preserves its fixed-visible cache relation or stops. -/
theorem bottomCompletion_post (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (visible : HashCache C) (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep)
    (src : SourceState C) (st : CompState C)
    (hrev : RevealRelation s src st.1.1)
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) visible)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) (hg : ShareG g st.2)
    (hd : DoneCached st.2) (hb : st.2.bad = none) (hm : st.1.2 = false)
    (hrow : ∀ T, visible (.prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) =
      some (g (T, ⟨.chain bottomLayer e l (chainStepDigit d),
        constrained_bottom_chain e l _ d.isLt⟩)))
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (bottomCompletionX e l d) src st)) :
    Stop r.2 ∨ CompletionPost x s g visible e l [d] (src, st) (r.1.2, r.2) := by
  let k := HiddenKey.bottomChain e l d
  let p : CPoint := ⟨.chain bottomLayer e l (chainStepDigit d), constrained_bottom_chain e l _ d.isLt⟩
  rw [bottomCompletionX_eq] at hr
  simp only [runX_bind, mem_support_bind_iff] at hr
  obtain ⟨revealed, hrrev, offset, hroff, completed, hrcomp, hr⟩ := hr
  have hR := sourceRevealX_sync capTag x q s pads τ g noise rest k src st hrev hf revealed hrrev
  have heq : revealed = ((s k, { src with revealed := Function.update src.revealed k (some (s k)) }),
      (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), st.2)) :=
    Prod.ext (Prod.ext hR.1 hR.2.2.1) hR.2.2.2
  subst revealed
  have hO := offset_frame x q s pads τ g noise rest e l d
    { src with revealed := Function.update src.revealed k (some (s k)) }
    (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), st.2)
    hf offset hroff
  rcases offset with ⟨⟨off, osrc⟩, ost⟩
  obtain ⟨hosrc, host⟩ := hO
  dsimp only at hosrc host
  subst osrc
  generalize hpads : ost.1.1.1.1.data.pads = newPads at host
  subst ost
  rw [runX_complete capTag x q s pads τ g noise rest p] at hrcomp
  simp only [support_map] at hrcomp
  obtain ⟨a, ha, rfl⟩ := hrcomp
  simp only [runX_modify, mem_support_pure_iff] at hr
  subst r
  have hcomp := completion_cache_sync_at x hinj s τ g
    (padState (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2), st.1.2), st.2)
      newPads).1.1 st.2 visible p ⟨hc.1, hc.2⟩ hg hd hrow (s k ^^^ off)
      (capTag ((padState (((st.1.1.1, Function.update st.1.1.2.1 k (some (s k)), st.1.1.2.2),
        st.1.2), st.2) newPads).1)) a ha
  have hbad := eager_complete_null τ g st.2 hb p (s k ^^^ off) st.1.1.2.2 a (by
    change a ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.complete p (s k ^^^ off) (st.1.2, st.1.1.2.2))).run st.2) at ha
    rw [hm] at ha
    exact ha)
  rcases hbad with hbad | hbad
  · apply Or.inr
    refine {
      toReleaseFrame := ?_
      reveal := ?_
      agreement := hcomp.1
      restFree := hf
      share := eagerImpl_shareG τ g _ st.2 hg a ha
      doneCached := eagerImpl_doneCached τ g st.2 hd _ a ha
      bad := hbad
      outside := ?_
      allRevealed := ?_ }
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcomp.2, rfl, rfl, rfl, rfl⟩
    · exact hR.2.1.frame rfl rfl
    · intro key hkey
      exact Function.update_of_ne (hkey d (List.mem_singleton_self _)) _ _
    · intro pos hpos
      have he : pos = d := List.mem_singleton.mp hpos
      subst pos
      exact Function.update_self ..
  · exact Or.inl (Or.inl hbad)

/-- Finite completion retains the exact reveal set and all unaffected fields. -/
theorem completions_post (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (visible : HashCache C) (e : KeyIndex) (l : ChainIndex) (positions : List XmssSecurity.ChainStep)
    (src : SourceState C) (st : CompState C)
    (hrev : RevealRelation s src st.1.1)
    (hc : CacheRelation x.1 x.2.1 s (dataOf x st) visible)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) (hg : ShareG g st.2)
    (hd : DoneCached st.2) (hb : st.2.bad = none) (hm : st.1.2 = false)
    (hrows : ∀ d ∈ positions, ∀ T,
      visible (.prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) =
        some (g (T, ⟨.chain bottomLayer e l (chainStepDigit d), constrained_bottom_chain e l _ d.isLt⟩)))
    (r : (List Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (positions.mapM (bottomCompletionX e l)) src st)) :
    Stop r.2 ∨ CompletionPost x s g visible e l positions (src, st) (r.1.2, r.2) := by
  induction positions generalizing src st r with
  | nil =>
      simp only [List.mapM_nil, runX_pure, mem_support_pure_iff] at hr
      subst r
      exact Or.inr ⟨ReleaseFrame.refl x _, hrev, hc, hf, hg, hd, hb,
        fun _ _ => rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons d positions ih =>
      simp only [List.mapM_cons, runX_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, b, hb', hr⟩ := hr
      rw [runX_pure, mem_support_pure_iff] at hr
      subst r
      rcases bottomCompletion_post x hinj q s pads τ g noise rest visible e l d src st
        hrev hc hf hg hd hb hm (hrows d (List.mem_cons_self ..)) a ha with hs | hh
      · exact Or.inl (runX_stop x q s pads τ g noise rest _ a.1.2 a.2 hs b hb')
      · rcases ih a.1.2 a.2 hh.reveal hh.agreement hh.restFree hh.share hh.doneCached
          hh.bad (hh.mark.trans hm) (fun j hj => hrows j (List.mem_cons_of_mem _ hj)) b hb' with hs | ht
        · exact Or.inl hs
        · apply Or.inr
          refine ⟨hh.toReleaseFrame.trans ht.toReleaseFrame, ht.reveal, ht.agreement,
            ht.restFree, ht.share, ht.doneCached, ht.bad, ?_, ?_⟩
          · intro k hk
            exact (ht.outside k (fun j hj => hk j (List.mem_cons_of_mem _ hj))).trans
              (hh.outside k (fun j hj => hk j (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hj)))))
          · intro j hj
            rcases List.mem_cons.mp hj with he | hj
            · subst j
              by_cases hdmem : d ∈ positions
              · exact ht.allRevealed d hdmem
              · rw [ht.outside (.bottomChain e l d) (by
                  intro pos hp he
                  have heq : d = pos := (HiddenKey.bottomChain.inj he).2.2
                  exact hdmem (heq ▸ hp))]
                exact hh.allRevealed d (List.mem_singleton_self _)
            · exact ht.allRevealed j hj

/-- Successful suffix postconditions before restoring the complete synchronization record. -/
structure SuffixPost (x : Keys3 C) (s : HiddenKey → Digest) (visible : HashCache C)
    (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (b b' : SourceState C × CompState C) : Prop extends SuffixFrame x s e l start b b' where
  reveal : RevealRelation s b'.1 b'.2.1.1
  agreement : CacheRelation x.1 x.2.1 s (dataOf x b'.2) visible
  released : ReleasedPending x.1 s b'.1 (dataOf x b'.2)
  bad : b'.2.2.bad = none

/-- A bottom pending's next secret lies later in its own chain. -/
theorem bottom_next_suffix (e : KeyIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep)
    (k : HiddenKey) (hk : (PendingInput.bottom e l d).next = some k) :
    ∃ next : XmssSecurity.ChainStep, d.val < next.val ∧ k = .bottomChain e l next := by
  simp only [PendingInput.next] at hk
  split at hk
  · rename_i hnext
    exact ⟨⟨d.val + 1, hnext⟩, by change d.val < d.val + 1; omega, (Option.some.inj hk).symm⟩
  · cases hk

/-- Both actual loops establish the complete suffix frame and planted-cache facts. -/
theorem releaseSuffix_post (x : Keys3 C)
    (hkeys : ¬ TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise g rest a (src, st)) (hmark : st.1.2 = false)
    (hrows : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
      (∀ T, (T, .chain bottomLayer e l (chainStepDigit d)) ∈ (dataOf x st).virtual) ∧
      (dataOf x st).pending (.bottom e l d) ≠ none)
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceReleaseBottomSuffixX x.1 x.2.1 e l start) src st)) :
    Stop r.2 ∨ SuffixPost x s (visibleOf a) e l start (src, st) (r.1.2, r.2) := by
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  let positions := (List.finRange 3).filter fun d => start.val ≤ d.val
  have hmem (d : XmssSecurity.ChainStep) : d ∈ positions ↔ start.val ≤ d.val := by simp [positions]
  rw [sourceReleaseBottomSuffixX_eq] at hr
  simp only [runX_bind, mem_support_bind_iff] at hr
  obtain ⟨completed, hcompleted, planted, hplanted, hr⟩ := hr
  rw [runX_pure, mem_support_pure_iff] at hr
  subst r
  rcases completions_post x hinj q s pads τ g noise rest (visibleOf a) e l positions src st
    hs.1.1.reveal hs.1.2 hs.1.1.restFree hs.1.1.share hs.1.1.doneCached hs.1.1.bad hmark
    (fun d hd => chainRow_of_virtual x hkeys s pads noise g rest a (src, st) hs.1.1
      ⟨.chain bottomLayer e l (chainStepDigit d), constrained_bottom_chain e l _ d.isLt⟩
      (hrows d ((hmem d).mp hd)).1) completed hcompleted with hstop | hc
  · exact Or.inl (runX_stop x q s pads τ g noise rest _ completed.1.2 completed.2 hstop planted hplanted)
  · have hpending : PendingValid (dataOf x completed.2) := by
      intro p value hp
      rw [hc.pending] at hp
      exact hs.1.1.pendingValid p value hp
    have hp := sourcePlantsX_sync_next capTag x q s pads τ g noise rest
      (positions.map fun d => PendingInput.bottom e l d) completed.1.2 completed.2 (visibleOf a)
      (by
        intro p hp
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
        constructor
        · intro key hk
          obtain ⟨next, hnext, rfl⟩ := bottom_next_suffix e l d key hk
          apply hc.allRevealed next
          apply (hmem next).mpr
          have hstart := (hmem d).mp hd
          omega
        · exact hc.allRevealed d hd)
      hpending hc.restFree hc.agreement planted (by
        simpa only [List.mapM_map, Function.comp_def] using hplanted)
    have hpf : ReleaseFrame x (completed.1.2, completed.2) (planted.1.2, planted.2) := by
      refine ⟨congrArg SourceState.signing hp.1, congrArg SourceState.trees hp.1,
        congrArg SourceState.exposed hp.1, congrArg SourceState.allocated hp.1,
        congrArg SourceState.candidates hp.1, congrArg SourceState.hiddenFlag hp.1,
        ?_, ?_, hp.2.2.2.1, ?_, ?_, ?_, ?_⟩
      all_goals (rw [hp.2.1] <;> rfl)
    have hframe := hc.toReleaseFrame.trans hpf
    apply Or.inr
    refine {
      toSuffixFrame := ⟨hframe, ?_, ?_⟩
      reveal := ?_
      agreement := hp.2.2.1
      released := ?_
      bad := ?_ }
    · intro key hk
      rw [hp.1]
      exact hc.outside key (fun d hd => hk d ((hmem d).mp hd))
    · intro d hd
      rw [hp.1]
      exact hc.allRevealed d ((hmem d).mpr hd)
    · have hsrc := congrArg SourceState.revealed hp.1
      have hbackend : planted.2.1.1.2.1 = completed.2.1.1.2.1 := by rw [hp.2.1]; rfl
      exact hc.reveal.frame hsrc hbackend
    · intro p value hv hrev
      by_cases hn : ∃ d ∈ positions, p.key = .bottomChain e l d
      · obtain ⟨d, hd, hkey⟩ := hn
        have he := pendingKey_bottomChain p e l d hkey
        subst p
        exact hp.2.2.2.2.2 (.bottom e l d) (List.mem_map.mpr ⟨d, hd, rfl⟩) value
          (hpf.pending ▸ hv)
      · have hold : src.revealed p.key ≠ none := by
          rw [hp.1, hc.outside p.key (fun d hd he => hn ⟨d, hd, he⟩)] at hrev
          exact hrev
        exact hframe.cache (hs.1.1.releasedPending p value (hframe.pending ▸ hv) hold)
    · rw [hp.2.1]
      exact hc.bad

/-- Port of ReleasePost.syncFields for the bottom-chain suffix reveal set. -/
theorem SuffixPost.syncFields (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (a : RealState C) (src src' : SourceState C) (st st' : CompState C)
    (hs : SyncFields x s pads noise g rest a (src, st))
    (h : SuffixPost x s (visibleOf a) e l start (src, st) (src', st'))
    (hrows : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
      (dataOf x st).pending (.bottom e l d) ≠ none)
    (hf : Frame x rest st'.1.1 ∧ ShareG g st'.2) (hd : DoneCached st'.2) :
    SyncFields x s pads noise g rest a (src', st') := by
  refine {
    corrupt := ?_, bound := ?_, released := ?_, exposed := ?_, candidates := ?_, flag := ?_
    reveal := h.reveal, releasedPending := h.released, opening := ?_
    pendingValid := hf.1.2.2, allocated := ?_, virtualSeen := ?_, compilerBound := ?_
    trace := ?_, bad := h.bad, share := hf.2, restAgree := hf.1.1, restFree := hf.1.2.1
    realPrivate := hs.realPrivate, frontier := ?_, candidatesPaid := ?_, doneCached := hd }
  · rw [h.signing]; exact hs.corrupt
  · rw [h.signing]; exact hs.bound
  · rw [h.signing]; exact hs.released
  · rw [h.exposed]; exact hs.exposed
  · rw [h.candidates]; exact hs.candidates
  · rw [h.hiddenFlag]; exact hs.flag
  · refine ⟨hs.opening.actualValue, ?_⟩
    intro other ho T
    have ho' : src.revealed (.opening bottomLayer other) ≠ none := by
      rw [h.revealed (.opening bottomLayer other) (by intro d hd he; cases he)] at ho
      exact ho
    obtain ⟨value, hv⟩ := hs.opening.released other ho' T
    exact ⟨value, h.cache hv⟩
  · intro p hp
    rw [h.allocated]
    exact hs.allocated p (h.pending ▸ hp)
  · intro T p hp
    exact hs.virtualSeen T p (h.virtual ▸ hp)
  · rw [h.bound, h.signing]
    exact hs.compilerBound
  · exact hs.trace.trans h.trace.symm
  · intro edge hp
    by_cases hn : ∃ d : XmssSecurity.ChainStep, start.val ≤ d.val ∧
        (chainPending edge).key = .bottomChain e l d
    · obtain ⟨d, hd, hkey⟩ := hn
      have he := pendingKey_bottomChain (chainPending edge) e l d hkey
      have hnone : (dataOf x st).pending (.bottom e l d) = none := by
        rw [h.pending, he] at hp
        exact hp
      exact (hrows d hd hnone).elim
    · rw [h.revealed (chainPending edge).key (fun d hd he => hn ⟨d, hd, he⟩)]
      exact hs.frontier edge (h.pending ▸ hp)
  · intro candidate hc he
    rw [h.candidates] at hc
    by_cases hn : ∃ d : XmssSecurity.ChainStep, start.val ≤ d.val ∧ candidate.1 = .bottomChain e l d
    · obtain ⟨d, hd, hk⟩ := hn
      rw [hk, h.suffix d hd]
      exact Option.some_ne_none _
    · rw [h.revealed candidate.1 (fun d hd hk => hn ⟨d, hd, hk⟩)]
      exact hs.candidatesPaid candidate hc he

/-- The actual suffix release synchronizes with the fixed real state or stops. -/
theorem releaseSuffix_sync (x : Keys3 C)
    (hkeys : ¬ TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise g rest a (src, st)) (hmark : st.1.2 = false)
    (hrows : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
      (∀ T, (T, .chain bottomLayer e l (chainStepDigit d)) ∈ (dataOf x st).virtual) ∧
      (dataOf x st).pending (.bottom e l d) ≠ none)
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceReleaseBottomSuffixX x.1 x.2.1 e l start) src st)) :
    Stop r.2 ∨ (SyncCore x s pads noise g rest a (r.1.2, r.2) ∧
      SuffixFrame x s e l start (src, st) (r.1.2, r.2)) := by
  rcases releaseSuffix_post x hkeys q s pads τ g noise rest e l start a src st hs hmark hrows r hr
    with hstop | hp
  · exact Or.inl hstop
  · have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
    have hi := TprfSecurityProof.slotInput_injective hinj (not_not.mp (not_or.mp hkeys).2)
    have hf := safe_frame capTag x hi q s pads τ g noise rest
      (sourceReleaseBottomSuffixX x.1 x.2.1 e l start)
      (safe_sourceReleaseBottomSuffixX x.1 x.2.1 e l start) src st
      ⟨⟨hs.1.1.restAgree, hs.1.1.restFree, hs.1.1.pendingValid⟩, hs.1.1.share⟩ r hr
    have hd := simulate_doneCached capTag x q s pads τ g noise rest
      ((sourceReleaseBottomSuffixX x.1 x.2.1 e l start).run src) st hs.1.1.doneCached r hr
    exact Or.inr ⟨⟨⟨hp.syncFields x s pads noise g rest e l start a src r.1.2 st r.2
      hs.1.1 (fun d hd => (hrows d hd).2) hf hd, hp.agreement⟩,
      hs.2.trans hp.count.symm⟩, hp.toSuffixFrame⟩

end ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.ReleaseFrame.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.ReleaseFrame.refl

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.ReleaseFrame.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.ReleaseFrame.trans

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.runX_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.runX_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.sourceReleaseBottomSuffixX_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.sourceReleaseBottomSuffixX_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.runX_pad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.runX_pad

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.offset_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.offset_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.bottomCompletionX_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.bottomCompletionX_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.bottomCompletion_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.bottomCompletion_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.completions_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.completions_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.bottom_next_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.bottom_next_suffix

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.releaseSuffix_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.releaseSuffix_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.SuffixPost.syncFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.SuffixPost.syncFields

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.releaseSuffix_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncSuffix.releaseSuffix_sync
