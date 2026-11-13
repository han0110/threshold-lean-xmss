import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackBuild
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackTree

/-! # Handlers of the base source at the signing state of the source

A local call of the forger with no hidden-key hit keeps the invariant `BaseInvariant` at the
signing state of the source, and so does the local branch of the oracle when the hidden flag is
down at its end. The opening release after a new binding keeps the invariant at the bound signing
state and completes the bottom randomizer of the key. Round 1 and the tree request keep the
invariant at the signing state of the source. The honest-signature tail keeps `LinkedInvariant`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackPure
open SigningCompilerO1SlackSteps SigningCompilerO1SlackRun SigningCompilerO1SlackRead
open SigningCompilerO1SlackBuild SigningCompilerO1SlackTree
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section BaseHandlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

/-- A step that keeps the signing state, and that keeps the linked invariant at the signing state of
its start, keeps the invariant at the signing state of the source. -/
theorem base_of_linked {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : SourceM C α) (source : SourceState C) (backend : CappedCompilerState C)
    (hc : SourceKeeps (SourceState.signing (C := C)) oa)
    (hp : ∀ r : (α × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s oa source backend) →
        LinkedInvariant seeds s source.signing starts r.1.2 r.2)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s oa source backend)) :
    BaseInvariant seeds s r.1.2.signing starts r.1.2 r.2 := by
  rw [hc.run P seeds q s source backend r hr]
  exact (hp r hr).2

set_option backward.isDefEq.respectTransparency false in
/-- A local call of the forger with no hidden-key hit keeps the invariant. -/
theorem sourceLocal_stable (hinj : Function.Injective x.2.1) (t : (LocalSpec C).Domain)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant x.2.1 s source.signing starts source backend)
    (hh : SigningCoreProof.hiddenHit x source.signing.corrupt t = false)
    (r : (LocalSpec C t × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceLocal prims x t) source backend)) :
    BaseInvariant x.2.1 s r.1.2.signing starts r.1.2 r.2 := by
  apply base_of_linked q s starts x.1 x.2.1 _ source backend
    ((sourceControl_sourceLocal prims x t).comp Prod.fst) ?_ r hr
  intro r hr
  cases t with
  | inl n =>
      exact sourceUniform_linked x.1 x.2.1 q s source.signing starts n source backend
        ⟨rfl, h⟩ r hr
  | inr t =>
      cases t with
      | inl query =>
          exact sourceHash_allowed x.1 x.2.1 q s source.signing starts hinj query source
            backend ⟨rfl, h⟩ (ReadAllowedO1.of_source
              (sourceReadAllowed_of_no_hiddenHit x source backend.1.1.data query hh) rfl
              (Finset.Subset.refl _)) r hr
      | inr inp =>
          exact SourcePreserves.bind (sourceHash_linked x.1 x.2.1 q s source.signing starts hinj
            (.streamKey inp.2.1) (fun _ _ he => by cases he)) _ (fun _ => SourcePreserves.pure _)
            source backend ⟨rfl, h⟩ r hr

set_option backward.isDefEq.respectTransparency false in
/-- The local branch of the oracle with the flag down at its end keeps the invariant. -/
theorem sourceOracles_local_stable (hinj : Function.Injective x.2.1) (top : TopTree)
    (t : (LocalSpec C).Domain) (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant x.2.1 s source.signing starts source backend)
    (r : (LocalSpec C t × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceOracles prims x top (.inl t))
      source backend))
    (hflag : r.1.2.hiddenFlag = false) :
    BaseInvariant x.2.1 s r.1.2.signing starts r.1.2 r.2 := by
  have hlocal := sourceOracles_local_hiddenFlag prims x top q s t source backend r hr
  have hh : SigningCoreProof.hiddenHit x source.signing.corrupt t = false := by
    rw [hflag] at hlocal
    exact (Bool.or_eq_false_iff.mp hlocal.symm).2
  simp only [sourceOracles, runSource_bind, runSource_get, mem_support_bind_iff,
    mem_support_pure_iff] at hr
  obtain ⟨_, rfl, a, ha, b, hb, hr⟩ := hr
  have hi := sourceLocal_stable prims x q s starts hinj t source backend h hh a ha
  rw [runSource_modify, mem_support_pure_iff] at hb
  subst b
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  exact ReleaseInvariantO1.source_frame hi rfl rfl

set_option backward.isDefEq.respectTransparency false in
/-- The opening release after a new binding keeps the invariant at the bound signing state and
completes the bottom randomizer of the key. -/
theorem sourceReleaseOpening_after_bindO1 (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (e : KeyIndex) (message : Message)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s source.signing starts source backend)
    (hfree : source.signing.bound e = none ∨ source.signing.bound e = some message)
    (hrel : SigningGuessProof.ReleasedBound source.signing)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseOpening P seeds e)
      { source with signing :=
        { source.signing with bound := Function.update source.signing.bound e (some message) } }
      backend)) :
    BaseInvariant seeds s
        { source.signing with bound := Function.update source.signing.bound e (some message) }
        starts r.1.2 r.2 ∧
      PointDone seeds r.2.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) := by
  have hrev : RevealRelation s
      { source with signing :=
        { source.signing with bound := Function.update source.signing.bound e (some message) } }
      backend := h.2.1
  have hs := SigningCompilerO1Release.ReleaseSlackO1.frame
    (source' := { source with signing :=
      { source.signing with bound := Function.update source.signing.bound e (some message) } })
    (SigningCompilerO1SlackPure.ReleaseSlackO1.bind_filtered h.1 e message hfree hrel)
    (fun _ _ => rfl) rfl rfl (fun _ he => he)
  have hp := sourceReleaseOpening_slack_frameO1 P seeds q s _ starts hinj e _ backend _ hs
    (fun _ _ => rfl) (by
      intro f hfe T
      simp only [Finset.mem_filter]
      refine ⟨fun hm => ⟨hm, ?_⟩, And.left⟩
      intro he
      exact hfe (Point.randomizer.inj he).2) rfl h.2.2 hrev r hr
  exact ⟨⟨hp.1, sourceReveals_sourceReleaseOpening P seeds q s e _ backend hrev r hr,
    runSource_pendingValid P seeds q s _ _ backend h.2.2 r hr⟩, hp.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Round 1 keeps the invariant at the signing state of the source. -/
theorem sourceRound1_stable (hinj : Function.Injective x.2.1) (top : TopTree)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant x.2.1 s source.signing starts source backend)
    (hrel : SigningGuessProof.ReleasedBound source.signing)
    (r : (TsigSpec C (.round1 i J e message) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s
      (sourceTsig prims x top (.round1 i J e message)) source backend)) :
    BaseInvariant x.2.1 s r.1.2.signing starts r.1.2 r.2 := by
  let bound : TsigState C :=
    { source.signing with bound := Function.update source.signing.bound e (some message) }
  have part (source' : SourceState C) (backend' : CappedCompilerState C)
      (h' : ReadInvariantO1 x.2.1 s bound starts (.randomizer bottomLayer e) source' backend')
      (hsig : source'.signing = bound)
      (hr' : r ∈ support (runSource x.1 x.2.1 q s
        (some <$> sourcePart prims x i J (.randomizer bottomLayer e) message) source' backend')) :
      BaseInvariant x.2.1 s r.1.2.signing starts r.1.2 r.2 := by
    have hk := ((sourceControl_sourcePart prims x i J (.randomizer bottomLayer e) message).comp
      Prod.fst).map some
    have hs : r.1.2.signing = source'.signing := hk.run x.1 x.2.1 q s source' backend' r hr'
    rw [hs, hsig]
    exact ((SourcePreserves.map (sourcePart_readO1 prims x q s bound starts hinj i J
      (.randomizer bottomLayer e) message) some) source' backend' h' r hr').1.2
  simp only [sourceTsig, runSource_bind, runSource_get, pure_bind] at hr
  split at hr
  · rw [runSource_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  · rename_i hguard
    have hfree : source.signing.bound e = none ∨ source.signing.bound e = some message := by
      rcases hbe : source.signing.bound e with _ | m
      · exact Or.inl rfl
      · have hm : ¬breaksOneMessagePerKey source.signing e message = true :=
          fun hc => hguard (Or.inr (Or.inr hc))
        simp only [breaksOneMessagePerKey, hbe, Option.any_some, decide_eq_true_eq,
          not_not] at hm
        exact Or.inr (congrArg some hm)
    simp only [runSource_bind, runSource_modify, runSource_bindKey, runSource_snapshot,
      runSource_get, pure_bind] at hr
    let assigned : SourceState C := { source with signing := bound }
    let boundBackend : CappedCompilerState C :=
      (({ backend.1.1 with bound := (if backend.1.1.bound e = none then
        Function.update backend.1.1.bound e (some message) else backend.1.1.bound) },
        backend.1.2), backend.2)
    have hbase : BaseInvariant x.2.1 s source.signing starts source boundBackend := h
    split at hr
    · rw [runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨released, hreleased, hr⟩ := hr
      have hp := sourceReleaseOpening_after_bindO1 q s starts x.1 x.2.1 hinj e message source
        boundBackend hbase hfree hrel released (by with_reducible exact hreleased)
      have hsig : released.1.2.signing = bound :=
        ((sourceControl_sourceReleaseOpening x.1 x.2.1 e).comp Prod.fst).run x.1 x.2.1 q s
          assigned boundBackend released hreleased
      exact part released.1.2 released.2 ⟨⟨by rw [hsig], hp.1⟩, hp.2.readable⟩ hsig hr
    · rename_i hready
      have hs : ReleaseSlackO1 x.2.1 s bound ⟨assigned, starts⟩ boundBackend.1.1.data :=
        SigningCompilerO1Release.ReleaseSlackO1.frame
          (SigningCompilerO1SlackPure.ReleaseSlackO1.bind_unready h.1 e message hfree hrel hready)
          (fun _ _ => rfl) rfl rfl (fun _ he => he)
      exact part assigned boundBackend
        ⟨⟨rfl, hs, h.2⟩, Or.inr ⟨e, rfl, by simp [assigned, bound]⟩⟩ rfl hr

set_option backward.isDefEq.respectTransparency false in
/-- The tree request keeps the invariant at the signing state of the source. -/
theorem sourceTree_stable (hinj : Function.Injective x.2.1) (top : TopTree)
    (b : XmssSecurity.TopIndex) (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant x.2.1 s source.signing starts source backend)
    (hshape : StoredTopShape source)
    (r : (TsigSpec C (.tree b) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceTsig prims x top (.tree b))
      source backend)) :
    BaseInvariant x.2.1 s r.1.2.signing starts r.1.2 r.2 := by
  simp only [sourceTsig, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨built, hbuilt, hr⟩ := hr
  have hb := sourceBottomOnce_linked x.1 x.2.1 q s source.signing starts hinj top b source
    backend ⟨rfl, h⟩ built hbuilt
  have hsb : built.1.2.signing = source.signing :=
    (sourceSigning_sourceBottomOnce x.1 x.2.1 top b).run x.1 x.2.1 q s source backend built hbuilt
  cases ht : built.1.1 with
  | none =>
      simp only [ht, runSource_pure, mem_support_pure_iff] at hr
      subst r
      rw [hsb]
      exact hb.2
  | some tree =>
      have shape := sourceBottomOnce_noBottomOpening x.1 x.2.1 q s top b source backend h.2.2
        hshape built hbuilt tree ht
      simp only [ht, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨returned, hreturned, opened, hopened, hr⟩ := hr
      have ret := sourceReturnTree_base x.1 x.2.1 q s source.signing starts hinj b tree shape
        built.1.2 built.2 hb.2 returned hreturned
      have hsr : returned.1.2.signing = built.1.2.signing :=
        ((sourceControl_sourceReturnTree x.1 x.2.1 b tree).comp Prod.fst).run x.1 x.2.1 q s
          built.1.2 built.2 returned hreturned
      have hso : opened.1.2.signing = returned.1.2.signing :=
        ((sourceControl_sourceRoProgram prims x.1 x.2.1 _).comp Prod.fst).run x.1 x.2.1 q s
          returned.1.2 returned.2 opened hopened
      have ho := sourcePrfValue_readO1 x.1 x.2.1 q s source.signing starts prims hinj
        (.randomizer topLayer (topKey b)) returned.1.2 returned.2
        ⟨⟨by rw [hsr, hsb], ret.1⟩, Or.inl ret.2⟩ opened hopened
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      change BaseInvariant x.2.1 s opened.1.2.signing starts opened.1.2 opened.2
      rw [hso, hsr, hsb]
      exact ho.1.2

/-- A suffix release and the full PRF read at its start point keep the linked invariant. -/
theorem sourcePrfValue_after_QO1 (hinj : Function.Injective x.2.1) (e : KeyIndex) (l : ChainIndex)
    (pos : Digit) (hpos : pos.val < 3) :
    SourcePreserves x.1 x.2.1 q s (LinkedInvariant x.2.1 s sig starts) (do
      sourceReleaseBottomSuffix x.1 x.2.1 e l pos
      sourceRoProgram prims x.1 x.2.1 (prfValue x.2.1 (.chain bottomLayer e l pos))) := by
  intro source backend h r hr
  rw [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨released, hreleased, hr⟩ := hr
  have hp := sourceReleaseBottomSuffix_readO1 x.1 x.2.1 q s sig starts hinj e l pos hpos source
    backend h released hreleased
  exact (sourcePrfValue_readO1 x.1 x.2.1 q s sig starts prims hinj (.chain bottomLayer e l pos)
    released.1.2 released.2 hp r hr).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The honest-signature tail keeps the linked invariant. -/
theorem sourceHonestSignature_linked (hinj : Function.Injective x.2.1) (top : TopTree)
    (e : KeyIndex) (message : Message) :
    SourcePreserves x.1 x.2.1 q s (LinkedInvariant x.2.1 s sig starts)
      (sourceHonestSignature prims x top e message) := by
  intro source backend h r hr
  simp only [sourceHonestSignature, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨built, hbuilt, hr⟩ := hr
  have hb := sourceBottomTree_linked x.1 x.2.1 q s sig starts hinj top (treeOf e) source backend
    h built hbuilt
  cases ht : built.1.1 with
  | none =>
      simp only [ht, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hb
  | some tree =>
      have shape := sourceBottomTree_noBottomOpening x.1 x.2.1 q s top (treeOf e) source backend
        h.2.2.2 built hbuilt tree ht
      simp only [ht, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨released, hreleased, opening, hopening, found, hfound, hr⟩ := hr
      have hp := sourceReleaseOpening_slackO1 x.1 x.2.1 q s sig starts hinj e built.1.2 built.2
        hb.2.1 hb.2.2.2 hb.2.2.1 released hreleased
      have hsig : released.1.2.signing = built.1.2.signing :=
        ((sourceControl_sourceReleaseOpening x.1 x.2.1 e).comp Prod.fst).run x.1 x.2.1 q s
          built.1.2 built.2 released hreleased
      have hi : ReadInvariantO1 x.2.1 s sig starts (.randomizer bottomLayer e) released.1.2
          released.2 :=
        ⟨⟨by rw [hsig]; exact hb.1, hp.1,
          sourceReveals_sourceReleaseOpening x.1 x.2.1 q s e built.1.2 built.2 hb.2.2.1 released
            hreleased,
          runSource_pendingValid x.1 x.2.1 q s _ built.1.2 built.2 hb.2.2.2 released hreleased⟩,
          hp.2.readable⟩
      have ho := sourcePrfValue_readO1 x.1 x.2.1 q s sig starts prims hinj
        (.randomizer bottomLayer e) released.1.2 released.2 hi opening hopening
      have hf := sourceCodeword_linked x.1 x.2.1 q s sig starts prims hinj (tree.commitment e) e
        message opening.1.1 opening.1.2 opening.2 ho.1 found hfound
      cases hfound : found.1.1 with
      | none =>
          simp only [hfound, runSource_pure, mem_support_pure_iff] at hr
          subst r
          exact hf
      | some result =>
          rcases result with ⟨randomness, encoding⟩
          simp only [hfound, runSource_bind, mem_support_bind_iff] at hr
          obtain ⟨values, hvalues, path, hpath, topValues, htop, hr⟩ := hr
          have hvaluesInv : LinkedInvariant x.2.1 s sig starts values.1.2 values.2 := by
            apply (SourcePreserves.sequenceFin (P := x.1) (seeds := x.2.1) (q := q) (s := s)
              numChains _ (fun l => ?_)) found.1.2 found.2 hf values hvalues
            split
            · exact SourcePreserves.pure _
            · rename_i hpos
              have hlt : (encoding l).val < 3 := by
                have hbound := (encoding l).isLt
                change (encoding l).val < 4 at hbound
                omega
              simpa only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def] using
                (sourcePrfValue_after_QO1 prims x q s sig starts hinj e l (encoding l) hlt).map
                  (fun value => if (encoding l).val = 0 then value else
                    (if (encoding l).val = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^
                      value)
          have hpathInv := sourceHashProgram_linked x.1 x.2.1 q s sig starts hinj _ values.1.2
            values.2 hvaluesInv path hpath
          have htopInv := SourcePreserves.sequenceFin (P := x.1) (seeds := x.2.1) (q := q)
            (s := s) numChains (fun l => sourceRevealDigest (tree.topSignature.chainValue l))
            (fun l => sourceRevealDigest_linked x.1 x.2.1 q s sig starts _ (shape l))
            path.1.2 path.2 hpathInv topValues htop
          rw [runSource_pure, mem_support_pure_iff] at hr
          subst r
          exact htopInv

end BaseHandlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.base_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.base_of_linked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceLocal_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceLocal_stable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceOracles_local_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceOracles_local_stable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceReleaseOpening_after_bindO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceReleaseOpening_after_bindO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceRound1_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceRound1_stable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceTree_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceTree_stable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourcePrfValue_after_QO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourcePrfValue_after_QO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceHonestSignature_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackBase.sourceHonestSignature_linked
