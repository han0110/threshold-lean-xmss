import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackPure
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackRun

/-! # The tree release of the O1 source at a fixed coalition state

The completion of a tree release point succeeds and keeps the slack `ReleaseSlackO1`. The reveal
and completion prefix returns the hidden value that it completes. The optional start completion,
the release of one top chain and the full tree release keep the invariant `BaseInvariant`, and
the tree release leaves its top opening point cached.

The reveal of a stored signature value keeps the linked invariant. The release of a bottom suffix
keeps the signing state, and its start point is cached after the release.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackPure
open SigningCompilerO1SlackRun
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Steps
variable (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

theorem completePrf_top_slackO1 (hinj : Function.Injective seeds) (b : XmssSecurity.TopIndex)
    (kind : Option ChainIndex) (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (completePrf seeds (topReleasePoint b kind) (s (topReleaseKey b kind))))
      source backend)) :
    r.1.1 = true ∧ ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (topReleasePoint b kind) (s (topReleaseKey b kind)) := by
  have hd := completePrf_done_or_missing P seeds hinj q s _ _ source backend
    (ReleaseSlackO1.top_admissible hs b kind) r hr
  have hf := completePrf_frame P seeds q s _ _ source backend r hr
  have hdata := congrArg (fun b : CappedCompilerState C => b.1.1.data) hf.2.1
  have hvirtual := congrArg DeferredState.virtual hdata
  have hpads := congrArg DeferredState.pads hdata
  exact ⟨hd.1, ReleaseSlackO1.complete_top hs b kind hf.2.2.2 hvirtual hpads
    (fun _ he => hf.1 ▸ he) hd.2, hd.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem sourceTopCompletion_slackO1 (hinj : Function.Injective seeds)
    (b : XmssSecurity.TopIndex) (kind : Option ChainIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (hrev : RevealRelation s source backend)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceTopCompletion seeds b kind) source backend)) :
    r.1.1 = s (topReleaseKey b kind) ∧
      ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      RevealRelation s r.1.2 r.2 ∧
      PointDone seeds r.2.1.1.data (topReleasePoint b kind) (s (topReleaseKey b kind)) := by
  simp only [sourceTopCompletion, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, completed, hcompleted, modified, hmodified, hr⟩ := hr
  have hrevealed := sourceReveal_correct P seeds q s (topReleaseKey b kind)
    source backend hrev revealed hreveal
  have hslack := SigningCompilerO1Release.sourceReveal_slack P seeds q s sig starts
    (topReleaseKey b kind) source backend hs
    (by intro e he; cases kind <;> simp [topReleaseKey, topLayer, bottomLayer] at he)
    revealed hreveal
  rw [hrevealed.1] at hcompleted
  have hc := completePrf_top_slackO1 P seeds q s sig starts hinj b kind revealed.1.2 revealed.2
    hslack completed hcompleted
  have hf := completePrf_frame P seeds q s _ _ revealed.1.2 revealed.2 completed hcompleted
  have hsource := congrArg SourceState.revealed hf.1
  have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) hf.2.1
  have hfinal := hrevealed.2.1.frame hsource hbackend
  rw [runSource_modify, mem_support_pure_iff] at hmodified
  subst modified
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  exact ⟨hrevealed.1, ReleaseSlackO1.frame hc.2.1 (fun _ _ => rfl) rfl rfl (fun _ he => he),
    hfinal, hc.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem sourceTopStartCompletion_base (hinj : Function.Injective seeds)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (start : Digit)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (sourceTopStartCompletion seeds b l start) source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 := by
  have hv' := runSource_pendingValid P seeds q s _ source backend h.2.2 r hr
  by_cases hp : start.val = 0
  · simp only [sourceTopStartCompletion, hp, ↓reduceIte, runSource_bind,
      mem_support_bind_iff, runSource_pure, mem_support_pure_iff] at hr
    obtain ⟨completed, hcompleted, rfl⟩ := hr
    have hc := sourceTopCompletion_slackO1 P seeds q s sig starts hinj b (some l) source backend
      h.1 h.2.1 completed hcompleted
    exact ⟨hc.2.1, hc.2.2.1, hv'⟩
  · simp only [sourceTopStartCompletion, hp, ↓reduceIte, runSource_pure,
      mem_support_pure_iff] at hr
    subst r
    exact h

set_option backward.isDefEq.respectTransparency false in
theorem sourceReturnedChain_base (hinj : Function.Injective seeds)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) (l : ChainIndex)
    (hvalue : NoBottomOpening (tree.topSignature.chainValue l))
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReturnedChain P seeds b tree l)
      source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 := by
  simp only [sourceReturnedChain, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, completed, hcompleted, planted, hplanted, hr⟩ := hr
  have hi : BaseInvariant seeds s sig starts revealed.1.2 revealed.2 := by
    apply runSource_mapM_inv P seeds q s (fun pos => sourceReveal (.topChain b l pos))
      (BaseInvariant seeds s sig starts) _ ?_ source backend h revealed hreveal
    intro pos _ st backend hb a ha
    exact ⟨SigningCompilerO1Release.sourceReveal_slack P seeds q s sig starts _ st backend hb.1
        (by intro e he; cases he) a ha,
      (sourceReveal_correct P seeds q s _ st backend hb.2.1 a ha).2.1,
      runSource_pendingValid P seeds q s _ st backend hb.2.2 a ha⟩
  have hc := sourceTopStartCompletion_base P seeds q s sig starts hinj b l
    (tree.topSignature.encoding l) revealed.1.2 revealed.2 hi completed hcompleted
  have hp : BaseInvariant seeds s sig starts planted.1.2 planted.2 := by
    apply runSource_mapM_inv P seeds q s (fun pos => sourcePlant P (.top b l pos))
      (BaseInvariant seeds s sig starts) _ ?_ completed.1.2 completed.2 hc planted hplanted
    intro pos _ st backend hb a ha
    exact sourcePlant_invariant P seeds q s sig starts (.top b l pos) st backend hb
      (by intro e he; cases he) a ha
  exact ⟨SigningCompilerO1Release.sourceRevealDigest_slack P seeds q s sig starts _
      planted.1.2 planted.2 hp.1 (fun e he => (hvalue e he).elim) r hr,
    (sourceRevealDigest_correct P seeds q s _ planted.1.2 planted.2 hp.2.1 r hr).2.1,
    runSource_pendingValid P seeds q s _ planted.1.2 planted.2 hp.2.2 r hr⟩

set_option backward.isDefEq.respectTransparency false in
/-- The tree release keeps the invariant and leaves its top opening point cached. -/
theorem sourceReturnTree_base (hinj : Function.Injective seeds)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree)
    (hshape : ∀ l, NoBottomOpening (tree.topSignature.chainValue l))
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (r : ((BottomTree × Digest) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReturnTree P seeds b tree) source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 ∧
      PrfPointCached seeds r.2.1.1.data (.randomizer topLayer (topKey b)) := by
  rw [sourceReturnTree_eq] at hr
  simp only [runSource_bind, runSource_get, pure_bind, mem_support_bind_iff] at hr
  obtain ⟨opening, hopening, planted, hplanted, values, hvalues, hr⟩ := hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  have ho := sourceTopCompletion_slackO1 P seeds q s sig starts hinj b none source backend
    h.1 h.2.1 opening hopening
  have hv' := runSource_pendingValid P seeds q s _ source backend h.2.2 opening hopening
  have hp : BaseInvariant seeds s sig starts planted.1.2 planted.2 := by
    apply runSource_mapM_inv P seeds q s (sourcePlant P) (BaseInvariant seeds s sig starts) _
      ?_ opening.1.2 opening.2 ⟨ho.2.1, ho.2.2.1, hv'⟩ planted hplanted
    intro p hmem st backend hb a ha
    have hkey : p.key = .opening topLayer (topKey b) :=
      of_decide_eq_true (List.mem_filter.mp hmem).2
    apply sourcePlant_invariant P seeds q s sig starts p st backend hb ?_ a ha
    intro e he
    have hx := hkey.symm.trans he
    simp [topLayer, bottomLayer] at hx
  have hcached : PrfPointCached seeds opening.2.1.1.data (.randomizer topLayer (topKey b)) :=
    fun T => Option.ne_none_iff_exists'.mpr (ho.2.2.2.1 T)
  refine ⟨runSource_sequenceFin_inv P seeds q s (BaseInvariant seeds s sig starts) numChains
    (sourceReturnedChain P seeds b tree)
    (fun l st backend hb a ha => sourceReturnedChain_base P seeds q s sig starts hinj b tree l
      (hshape l) st backend hb a ha) planted.1.2 planted.2 hp values hvalues, ?_⟩
  exact (hcached.mono (runSource_cache_le P seeds q s _ opening.1.2 opening.2 planted hplanted)).mono
    (runSource_cache_le P seeds q s _ planted.1.2 planted.2 values hvalues)

theorem sourceRevealDigest_linked (value : DeferredDigest) (hv : NoBottomOpening value) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts)
      (sourceRevealDigest value) := by
  apply linked_of_signing P seeds q s sig starts _
    ((sourceControl_sourceRevealDigest value).comp Prod.fst)
  intro source backend h r hr
  exact ⟨SigningCompilerO1Release.sourceRevealDigest_slack P seeds q s sig starts value source
      backend h.2.1 (fun e he => (hv e he).elim) r hr,
    sourceReveals_sourceRevealDigest P seeds q s value source backend h.2.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2.2 r hr⟩

/-- The suffix release makes its start point readable. -/
theorem sourceReleaseBottomSuffix_readO1 (hinj : Function.Injective seeds)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) (hstart : start.val < 3)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : LinkedInvariant seeds s sig starts source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseBottomSuffix P seeds e l start)
      source backend)) :
    ReadInvariantO1 seeds s sig starts (.chain bottomLayer e l start) r.1.2 r.2 := by
  have hb := sourceReleaseBottomSuffix_base P seeds hinj q s sig starts e l start source backend
    h.2 r hr
  have hsig : r.1.2.signing = source.signing :=
    ((sourceControl_sourceReleaseBottomSuffix P seeds e l start).comp Prod.fst).run
      P seeds q s source backend r hr
  refine ⟨⟨(congrArg TsigState.bound hsig).trans h.1, hb.1⟩, Or.inl ?_⟩
  have hd := hb.2 ⟨start.val, hstart⟩ (Nat.le_refl _)
  exact fun T => Option.ne_none_iff_exists'.mpr (hd.2.1 T)

end Steps

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.completePrf_top_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.completePrf_top_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceTopCompletion_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceTopCompletion_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceTopStartCompletion_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceTopStartCompletion_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceReturnedChain_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceReturnedChain_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceReturnTree_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceReturnTree_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceRevealDigest_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceRevealDigest_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceReleaseBottomSuffix_readO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackTree.sourceReleaseBottomSuffix_readO1
