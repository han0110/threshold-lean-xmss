import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackRun

/-! # Control fields of the O1 source

`ControlAt flag st` is `ControlInvariantO1 flag` with the signing state `st`. A lifted step that
keeps the control fields of the base source, the tree build, the key sweep and the callback of
round 2 keep it.

Round 1 of the base source keeps each release record at its bound message, because its guard
gives a free key or the same message. The tree request of the base source keeps the signing state.

Each signing request of the O1 source keeps `ControlInvariantO1 flag`. The final update of round 2
adds the record of the signer at a bound key, and the update of corruption changes only the
corrupt set.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackRun
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

/-! ## Handlers of the base source -/

section BaseHandlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

/-- Round 1 of the base source keeps each release record at its bound message. -/
theorem sourceRound1_releasedBound (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex)
    (message : Message) (source : SourceState C) (backend : CappedCompilerState C)
    (h : SigningGuessProof.ReleasedBound source.signing)
    (r : (TsigSpec C (.round1 i J e message) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s
      (sourceTsig prims x top (.round1 i J e message)) source backend)) :
    SigningGuessProof.ReleasedBound r.1.2.signing := by
  unfold sourceTsig at hr
  rw [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  rw [runSource_get, mem_support_pure_iff] at ha
  subst a
  dsimp only at hr
  split at hr
  · rw [runSource_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  · rename_i hguard
    rw [runSource_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, hr⟩ := hr
    rw [runSource_modify, mem_support_pure_iff] at ha
    subst a
    have hk := SourceKeeps.run (field := SourceState.signing) ?_ x.1 x.2.1 q s _ _ r hr
    · rw [hk]
      apply releasedBound_bind source.signing e message h
      rcases hbe : source.signing.bound e with _ | m
      · exact Or.inl rfl
      · have hm : ¬breaksOneMessagePerKey source.signing e message = true :=
          fun hc => hguard (Or.inr (Or.inr hc))
        simp only [breaksOneMessagePerKey, hbe, Option.any_some, decide_eq_true_eq,
          not_not] at hm
        exact Or.inr (congrArg some hm)
    · have part := (sourceControl_sourcePart prims x i J (.randomizer bottomLayer e) message).comp
        Prod.fst
      refine (SourceKeeps.lift _).bind _ fun _ => ?_
      refine (SourceKeeps.lift _).bind _ fun _ => ?_
      refine SourceKeeps.get.bind _ fun _ => ?_
      split
      · exact ((sourceControl_sourceReleaseOpening x.1 x.2.1 e).comp Prod.fst).bind _
          fun _ => part.map some
      · exact (SourceKeeps.pure _).bind _ fun _ => part.map some

/-- The tree request of the base source keeps the signing state. -/
theorem sourceSigning_tree (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourceKeeps (SourceState.signing (C := C)) (sourceTsig prims x top (.tree b)) := by
  unfold sourceTsig
  refine (sourceSigning_sourceBottomOnce x.1 x.2.1 top b).bind _ fun built => ?_
  cases built with
  | none => exact SourceKeeps.pure none
  | some tree =>
      refine ((sourceControl_sourceReturnTree x.1 x.2.1 b tree).comp Prod.fst).bind _
        fun returned => ?_
      exact ((sourceControl_sourceRoProgram prims x.1 x.2.1 _).comp Prod.fst).bind _
        (fun _ => SourceKeeps.pure _)

end BaseHandlers

/-! ## Handlers of the O1 source -/

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

/-- The control fields of the O1 source with a fixed signing state. The body of a signing request
keeps this invariant up to its last update of the signing state. -/
def ControlAt (flag : Bool) (st : TsigState C) (src : SourceStateO1 C)
    (backend : CappedCompilerState C) : Prop :=
  ControlInvariantO1 flag src backend ∧ src.base.signing = st

/-- A new state with the control fields of the old state and valid pending answers keeps
`ControlAt`. -/
theorem ControlAt.of_control {flag : Bool} {st : TsigState C} {src src' : SourceStateO1 C}
    {backend backend' : CappedCompilerState C} (h : ControlAt flag st src backend)
    (hc : sourceControl src'.base = sourceControl src.base)
    (hv : PendingValid backend'.1.1.data) : ControlAt flag st src' backend' := by
  have hsig : src'.base.signing = src.base.signing := congrArg Prod.fst hc
  refine ⟨⟨hv, h.1.2.1.of_control hc, (congrArg (fun c => c.2.2.1) hc).trans h.1.2.2.1, ?_⟩,
    hsig.trans h.2⟩
  rw [hsig]
  exact h.1.2.2.2

/-- A step that keeps `ControlAt` at each signing state keeps `ControlInvariantO1` and each property
of the signing state. -/
theorem ControlAt.keeps {α : Type} {P : PublicParameter} {seeds : C.Term → HashOutput}
    {flag : Bool} {oa : SourceMO1 C α}
    (h : ∀ st, SourcePreservesO1 P seeds q s (ControlAt flag st) oa) (Q : TsigState C → Prop) :
    SourcePreservesO1 P seeds q s
      (fun src backend => ControlInvariantO1 flag src backend ∧ Q src.base.signing) oa := by
  intro src backend hs r hr
  have hh := h src.base.signing src backend ⟨hs.1, rfl⟩ r hr
  exact ⟨hh.1, hh.2 ▸ hs.2⟩

/-- A step of the base source that keeps its control fields keeps the control fields of the O1
source and the signing state. -/
theorem liftBase_controlAt {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (flag : Bool) (st : TsigState C) (oa : SourceM C α) (hc : SourceKeeps sourceControl oa) :
    SourcePreservesO1 P seeds q s (ControlAt flag st) (liftBase oa) := by
  refine SourcePreservesO1.liftBase fun starts source backend h r hr => ?_
  exact ControlAt.of_control (src' := ⟨r.1.2, starts⟩) h (hc.run P seeds q s source backend r hr)
    (runSource_pendingValid P seeds q s oa source backend h.1.1 r hr)

theorem sourceBottomOnce_controlAt (P : PublicParameter) (seeds : C.Term → HashOutput)
    (flag : Bool) (st : TsigState C) (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourcePreservesO1 P seeds q s (ControlAt flag st)
      (liftBase (sourceBottomOnce P seeds top b)) := by
  refine SourcePreservesO1.liftBase fun starts source backend h r hr => ?_
  have hb := sourceBottomOnce_controlInvariant P seeds q s flag top b source backend
    ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩ r hr
  have hsig := (sourceSigning_sourceBottomOnce P seeds top b).run P seeds q s source backend r hr
  refine ⟨⟨hb.1, hb.2.1, hb.2.2, ?_⟩, hsig.trans h.2⟩
  change SigningGuessProof.ReleasedBound r.1.2.signing
  rw [hsig]
  exact h.1.2.2.2

theorem sourceReleaseKey_controlAt (P : PublicParameter) (seeds : C.Term → HashOutput)
    (flag : Bool) (st : TsigState C) (e : KeyIndex) :
    SourcePreservesO1 P seeds q s (ControlAt flag st) (sourceReleaseKey P seeds e) := by
  intro src backend h r hr
  exact ControlAt.of_control h (sourceReleaseKey_control q s P seeds e src backend r hr).1
    (runSourceO1_pendingValid q s P seeds _ src backend h.1.1 r hr)

/-- The release of the covered suffix of one chain keeps `ControlAt`. -/
theorem sourceReleaseCovered_controlAt (P : PublicParameter) (seeds : C.Term → HashOutput)
    (flag : Bool) (st : TsigState C) (e : KeyIndex) (l : ChainIndex) :
    SourcePreservesO1 P seeds q s (ControlAt flag st) (sourceReleaseCovered P seeds e l) := by
  unfold sourceReleaseCovered
  refine SourcePreservesO1.bind SourcePreservesO1.get _ fun current => ?_
  split
  · exact liftBase_controlAt q s P seeds flag st _
      (sourceControl_sourceReleaseBottomSuffix P seeds e l _)
  · exact SourcePreservesO1.pure ()

theorem round2Callback_controlAt (flag : Bool) (st : TsigState C) (i : C.Party) (J : C.Quorum)
    (message : Message) (atThreshold : Bool) (p : Point) :
    SourcePreservesO1 x.1 x.2.1 q s (ControlAt flag st)
      (round2Callback prims x i J message atThreshold p) := by
  have part := liftBase_controlAt q s x.1 x.2.1 flag st _
    (sourceControl_sourcePart prims x i J p message)
  unfold round2Callback
  dsimp only
  split
  · unfold recordStart
    refine SourcePreservesO1.bind (SourcePreservesO1.modify _ ?_) _ fun _ => ?_
    · exact fun _ _ h => h
    split
    · exact SourcePreservesO1.bind (sourceReleaseCovered_controlAt q s x.1 x.2.1 flag st _ _) _
        fun _ => part
    · exact SourcePreservesO1.bind (SourcePreservesO1.pure _) _ fun _ => part
  · exact SourcePreservesO1.bind (SourcePreservesO1.pure _) _ fun _ => part

/-- Each signing request keeps the control fields. -/
theorem sourceTsigO1_control (top : TopTree) (flag : Bool) (t : TsigQuery C) :
    SourcePreservesO1 x.1 x.2.1 q s (ControlInvariantO1 flag) (sourceTsigO1 prims x top t) := by
  cases t with
  | corrupt i =>
      intro src backend h r hr
      unfold sourceTsigO1 at hr
      rw [runSourceO1_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, hr⟩ := hr
      rw [runSourceO1_get, mem_support_pure_iff] at ha
      subst a
      dsimp only at hr
      split at hr
      · rw [runSourceO1_pure, mem_support_pure_iff] at hr
        subst r
        exact h
      · rw [runSourceO1_bind, mem_support_bind_iff] at hr
        obtain ⟨a, ha, hr⟩ := hr
        rw [runSourceO1_modify, mem_support_pure_iff] at ha
        subst a
        refine (ControlAt.keeps q s (fun st => ?_) (fun _ => True) _ _ ?_ r hr).1
        · exact SourcePreservesO1.bind (SourcePreservesO1.mapM _ _
            fun e _ => sourceReleaseKey_controlAt q s x.1 x.2.1 flag st e) _
            fun _ => SourcePreservesO1.pure _
        · exact ⟨⟨h.1, h.2.1, h.2.2.1, releasedBound_corrupt _ _ h.2.2.2⟩, trivial⟩
  | tree b =>
      unfold sourceTsigO1
      refine SourcePreservesO1.map ?_ _
      refine SourcePreservesO1.liftBase fun starts source backend h r hr => ?_
      have hc := sourceTsig_controlInvariant prims x top q s flag (.tree b) source backend
        ⟨h.1, h.2.1, h.2.2.1⟩ r hr
      have hsig := (sourceSigning_tree prims x top b).run x.1 x.2.1 q s source backend r hr
      refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
      change SigningGuessProof.ReleasedBound r.1.2.signing
      rw [hsig]
      exact h.2.2.2
  | round1 i J e message =>
      unfold sourceTsigO1
      refine SourcePreservesO1.liftBase fun starts source backend h r hr => ?_
      have hc := sourceTsig_controlInvariant prims x top q s flag (.round1 i J e message) source
        backend ⟨h.1, h.2.1, h.2.2.1⟩ r hr
      exact ⟨hc.1, hc.2.1, hc.2.2,
        sourceRound1_releasedBound prims x q s top i J e message source backend h.2.2.2 r hr⟩
  | round2 i J e message parts =>
      rw [sourceRound2O1_eq]
      intro src backend h r hr
      rw [runSourceO1_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, hr⟩ := hr
      rw [runSourceO1_get, mem_support_pure_iff] at ha
      subst a
      dsimp only at hr
      split at hr
      · rw [runSourceO1_pure, mem_support_pure_iff] at hr
        subst r
        exact h
      · rename_i hguard
        have hb : src.base.signing.bound e = some message := by
          by_contra hn
          exact hguard (Or.inr (Or.inr hn))
        have keep {α : Type} {oa : SourceMO1 C α}
            (hc : ∀ st, SourcePreservesO1 x.1 x.2.1 q s (ControlAt flag st) oa) :=
          ControlAt.keeps q s hc (fun sig => sig.bound e = some message)
        refine (?_ : SourcePreservesO1 x.1 x.2.1 q s (fun src backend =>
          ControlInvariantO1 flag src backend ∧ src.base.signing.bound e = some message) _)
          src backend ⟨h, hb⟩ r hr |>.1
        refine SourcePreservesO1.bind
          (keep fun st => sourceBottomOnce_controlAt q s x.1 x.2.1 flag st top (treeOf e)) _
          fun built => ?_
        rcases built with _ | tree
        · exact SourcePreservesO1.pure none
        refine SourcePreservesO1.bind (keep fun st => liftBase_controlAt q s x.1 x.2.1 flag st _
          (sourceControl_sourcePart prims x i J _ message)) _ fun own => ?_
        refine SourcePreservesO1.bind ?_ _ fun values => ?_
        · unfold signRound2With
          refine SourcePreservesO1.bind (keep fun st => liftBase_controlAt q s x.1 x.2.1 flag st _
            (sourceControl_sourceRoProgram prims x.1 x.2.1 _)) _ fun answer => ?_
          rcases answer with _ | ⟨randomness, encoding⟩
          · exact SourcePreservesO1.pure none
          refine SourcePreservesO1.bind (SourcePreservesO1.sequenceFin _ _ fun l => ?_) _
            fun _ => SourcePreservesO1.pure _
          split
          · exact SourcePreservesO1.map
              (keep fun st => round2Callback_controlAt prims x q s flag st i J message _ _) some
          · exact SourcePreservesO1.pure none
        rcases values with _ | values
        · exact SourcePreservesO1.pure none
        dsimp only
        split
        · refine SourcePreservesO1.bind
            (keep fun st => sourceReleaseKey_controlAt q s x.1 x.2.1 flag st e) _ fun _ => ?_
          refine SourcePreservesO1.bind (SourcePreservesO1.modify _ ?_) _
            fun _ => SourcePreservesO1.pure _
          intro current backend hc
          exact ⟨⟨hc.1.1, hc.1.2.1, hc.1.2.2.1,
            releasedBound_withRecord _ e message i hc.1.2.2.2 hc.2⟩, hc.2⟩
        · refine SourcePreservesO1.bind (SourcePreservesO1.pure ()) _ fun _ => ?_
          refine SourcePreservesO1.bind (SourcePreservesO1.modify _ ?_) _
            fun _ => SourcePreservesO1.pure _
          intro current backend hc
          exact ⟨⟨hc.1.1, hc.1.2.1, hc.1.2.2.1,
            releasedBound_withRecord _ e message i hc.1.2.2.2 hc.2⟩, hc.2⟩

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceRound1_releasedBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceRound1_releasedBound

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceSigning_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceSigning_tree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.ControlAt.of_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.ControlAt.of_control

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.ControlAt.keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.ControlAt.keeps

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.liftBase_controlAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.liftBase_controlAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceBottomOnce_controlAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceBottomOnce_controlAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceReleaseKey_controlAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceReleaseKey_controlAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceReleaseCovered_controlAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceReleaseCovered_controlAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.round2Callback_controlAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.round2Callback_controlAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceTsigO1_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackControl.sourceTsigO1_control
