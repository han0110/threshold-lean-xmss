import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackBase
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackCorrupt
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackRound2
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackControl

/-! # The guarded invariant of the O1 source

Each signing request keeps the invariant at the signing state of the source. A step of the base
source that keeps the signing state, the stored trees and the hidden flag, and that keeps the linked
invariant, keeps `GuardedReleaseInvariantS`. The setup, one call of the verification and the
honest-signature tail are such steps. Each oracle call and the complete O1 game keep
`GuardedReleaseInvariantS`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackRun
open SigningCompilerO1SlackRead SigningCompilerO1SlackBuild SigningCompilerO1SlackBase
open SigningCompilerO1SlackCorrupt SigningCompilerO1SlackRound2 SigningCompilerO1SlackControl
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

set_option backward.isDefEq.respectTransparency false in
/-- Each signing request keeps the invariant at the signing state of the source. -/
theorem sourceTsigO1_stable (hinj : Function.Injective x.2.1) (top : TopTree) (t : TsigQuery C)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s src.base.signing src backend)
    (hrel : SigningGuessProof.ReleasedBound src.base.signing)
    (hshape : StoredTopShape src.base)
    (r : (TsigSpec C t × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s (sourceTsigO1 prims x top t) src backend)) :
    ReleaseInvariantO1 x.2.1 s r.1.2.base.signing r.1.2 r.2 := by
  cases t with
  | corrupt i => exact sourceCorruptO1_stable prims x q s hinj top i src backend h r hr
  | tree b =>
      simp only [sourceTsigO1, map_eq_bind_pure_comp, runSourceO1_bind, mem_support_bind_iff,
        runSourceO1_liftBase] at hr
      obtain ⟨a, ha, hr⟩ := hr
      obtain ⟨a', ha', ha⟩ := ha
      rw [Function.comp_apply, mem_support_pure_iff] at ha
      subst a
      rw [Function.comp_apply, runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      exact sourceTree_stable prims x q s src.starts hinj top b src.base backend h hshape a' ha'
  | round1 i J e message =>
      simp only [sourceTsigO1, runSourceO1_liftBase, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact sourceRound1_stable prims x q s src.starts hinj top i J e message src.base backend h
        hrel a ha
  | round2 i J e message parts =>
      exact sourceRound2O1_stable prims x q s hinj top i J e message parts src backend h r hr

/-- A step of the base source that keeps the signing state, the stored trees, the hidden flag and
the linked invariant keeps the guarded invariant of the O1 source. -/
theorem liftBase_guardedS {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : SourceM C α)
    (hc : SourceKeeps (fun st : SourceState C => (st.signing, st.trees, st.hiddenFlag)) oa)
    (hi : ∀ sig starts, SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) oa) :
    SourcePreservesO1 P seeds q s (GuardedReleaseInvariantS seeds s) (liftBase oa) := by
  refine SourcePreservesO1.liftBase fun starts source backend h r hr => ?_
  have hk := hc.run P seeds q s source backend r hr
  have hsig : r.1.2.signing = source.signing := congrArg Prod.fst hk
  have htrees : r.1.2.trees = source.trees := congrArg (fun c => c.2.1) hk
  have hflag : r.1.2.hiddenFlag = source.hiddenFlag := congrArg (fun c => c.2.2) hk
  refine ⟨⟨runSource_pendingValid P seeds q s oa source backend h.1.1 r hr, ?_, fun hf => ?_⟩, ?_⟩
  · intro b tree ht
    change r.1.2.trees b = some (some tree) at ht
    rw [htrees] at ht
    exact h.1.2.1 b tree ht
  · change BaseInvariant seeds s r.1.2.signing starts r.1.2 r.2
    rw [hsig]
    exact (hi source.signing starts source backend
      ⟨rfl, h.1.2.2 (hflag.symm.trans hf)⟩ r hr).2
  · change SigningGuessProof.ReleasedBound r.1.2.signing
    rw [hsig]
    exact h.2

/-- The setup keeps the guarded invariant. -/
theorem setupO1_guardedS (hinj : Function.Injective x.2.1) :
    SourcePreservesO1 x.1 x.2.1 q s (GuardedReleaseInvariantS x.2.1 s)
      (liftBase (sourceTopTree x.1 x.2.1)) :=
  liftBase_guardedS q s x.1 x.2.1 _
    ((sourceControl_sourceTopTree x.1 x.2.1).comp fun c => (c.1, c.2.1, c.2.2.1))
    (fun sig starts => sourceTopTree_linked x.1 x.2.1 q s sig starts hinj)

/-- One call of the verification keeps the guarded invariant. -/
theorem verifyO1_guardedS (hinj : Function.Injective x.2.1) (st : SourceState C)
    (input : HashInput) :
    SourcePreservesO1 x.1 x.2.1 q s (GuardedReleaseInvariantS x.2.1 s)
      (liftBase (do
        let value ← sourceHash x.1 x.2.1 (.hash input)
        modify fun (state : SourceState C) => { state with candidates :=
          state.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
        pure value : SourceM C HashOutput)) := by
  refine liftBase_guardedS q s x.1 x.2.1 _ ?_ fun sig starts => ?_
  · refine SourceKeeps.bind ((sourceControl_sourceHash x.1 x.2.1 (.hash input)).comp
      fun c => (c.1, c.2.1, c.2.2.1)) _ fun value => ?_
    refine SourceKeeps.bind (SourceKeeps.modify _ ?_) _ fun _ => SourceKeeps.pure value
    exact fun _ => rfl
  · refine (sourceHash_linked x.1 x.2.1 q s sig starts hinj (.hash input)
      (fun _ _ he => by cases he)).bind _ fun value => ?_
    refine SourcePreserves.bind (sourceModify_linked x.1 x.2.1 q s sig starts _ ?_ ?_) _
      fun _ => SourcePreserves.pure value
    · exact fun _ => rfl
    · exact fun _ => rfl

/-- The honest-signature tail keeps the guarded invariant. -/
theorem honestO1_guardedS (hinj : Function.Injective x.2.1) (top : TopTree) (e : KeyIndex)
    (message : Message) :
    SourcePreservesO1 x.1 x.2.1 q s (GuardedReleaseInvariantS x.2.1 s)
      (liftBase (sourceHonestSignature prims x top e message)) :=
  liftBase_guardedS q s x.1 x.2.1 _
    ((sourceControl_sourceHonestSignature prims x top e message).comp
      fun c => (c.1, c.2.1, c.2.2.1))
    (fun sig starts => sourceHonestSignature_linked prims x q s sig starts hinj top e message)

set_option backward.isDefEq.respectTransparency false in
/-- Each oracle call of the O1 source keeps the guarded invariant. -/
theorem sourceOraclesO1_guardedS (hinj : Function.Injective x.2.1) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) :
    SourcePreservesO1 x.1 x.2.1 q s (GuardedReleaseInvariantS x.2.1 s)
      (sourceOraclesO1 prims x top t) := by
  cases t with
  | inl t =>
      refine SourcePreservesO1.liftBase fun starts source backend h r hr => ?_
      have hk : SourceKeeps (fun st : SourceState C => (st.signing, st.trees))
          (sourceOracles prims x top (.inl t)) := by
        refine SourceKeeps.get.bind _ fun current => ?_
        refine ((sourceControl_sourceLocal prims x t).comp fun c => (c.1, c.2.1)).bind _
          fun value => ?_
        refine SourceKeeps.bind (SourceKeeps.modify _ ?_) _ fun _ => SourceKeeps.pure value
        exact fun _ => rfl
      have hkr := hk.run x.1 x.2.1 q s source backend r hr
      have hsig : r.1.2.signing = source.signing := congrArg Prod.fst hkr
      have htrees : r.1.2.trees = source.trees := congrArg Prod.snd hkr
      have hlocal := sourceOracles_local_hiddenFlag prims x top q s t source backend r hr
      refine ⟨⟨runSource_pendingValid x.1 x.2.1 q s _ source backend h.1.1 r hr, ?_,
        fun hf => ?_⟩, ?_⟩
      · intro b tree ht
        change r.1.2.trees b = some (some tree) at ht
        rw [htrees] at ht
        exact h.1.2.1 b tree ht
      · have hsf : source.hiddenFlag = false :=
          (Bool.or_eq_false_iff.mp (hlocal.symm.trans hf)).1
        exact sourceOracles_local_stable prims x q s starts hinj top t source backend
          (h.1.2.2 hsf) r hr hf
      · change SigningGuessProof.ReleasedBound r.1.2.signing
        rw [hsig]
        exact h.2
  | inr t =>
      intro src backend h r hr
      simp only [sourceOraclesO1, runSourceO1_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, b, hb, hr⟩ := hr
      have control := sourceTsigO1_control prims x q s top src.base.hiddenFlag t src backend
        ⟨h.1.1, h.1.2.1, rfl, h.2⟩ a ha
      rw [runSourceO1_modify, mem_support_pure_iff] at hb
      subst b
      rw [runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨⟨control.1, control.2.1, fun hf => ?_⟩, control.2.2.2⟩
      have hi := sourceTsigO1_stable prims x q s hinj top t src backend
        (h.1.2.2 (control.2.2.1.symm.trans hf)) h.2 h.1.2.1 a ha
      exact ReleaseInvariantO1.source_frame hi rfl rfl

set_option maxRecDepth 100000 in
/-- The complete O1 game keeps the guarded invariant. -/
theorem sourceGameO1_guardedS (A : TsigAdversary C) (hinj : Function.Injective x.2.1) :
    SourcePreservesO1 x.1 x.2.1 q s (GuardedReleaseInvariantS x.2.1 s)
      (sourceGameO1 prims A x) := by
  unfold sourceGameO1
  refine SourcePreservesO1.bind (setupO1_guardedS x q s hinj) _ fun top => ?_
  refine SourcePreservesO1.bind (SourcePreservesO1.simulateQ _
    (sourceOraclesO1_guardedS prims x q s hinj top) _) _ fun forgery => ?_
  refine SourcePreservesO1.bind SourcePreservesO1.get _ fun current => ?_
  refine SourcePreservesO1.bind (SourcePreservesO1.simulateQ _
    (fun input => verifyO1_guardedS x q s hinj current.base input) _) _ fun verified => ?_
  dsimp only
  split
  · exact SourcePreservesO1.bind (SourcePreservesO1.pure _) _ fun _ => SourcePreservesO1.pure _
  · exact SourcePreservesO1.bind (honestO1_guardedS prims x q s hinj top _ _) _
      fun _ => SourcePreservesO1.bind (SourcePreservesO1.pure _) _
        fun _ => SourcePreservesO1.pure _

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.sourceTsigO1_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.sourceTsigO1_stable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.liftBase_guardedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.liftBase_guardedS

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.setupO1_guardedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.setupO1_guardedS

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.verifyO1_guardedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.verifyO1_guardedS

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.honestO1_guardedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.honestO1_guardedS

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.sourceOraclesO1_guardedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.sourceOraclesO1_guardedS

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.sourceGameO1_guardedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackGuarded.sourceGameO1_guardedS
