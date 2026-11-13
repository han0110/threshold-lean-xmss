import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackBuild

/-! # Round 2 of the O1 source

The build, the own part and the codeword search run at the signing state `st` from before the
call. A failed build or a failed search returns with the invariant at `st`.

Below the threshold, the coalition state moves to `withRecord st e message i` after a successful
search. Each callback records its digit and reads only the held terms of the signer.

At the threshold, each callback records its digit, completes the covered positions of its chain and
reads the complete point at `st`. The key sweep completes each covered position of the key, and then
the coalition state moves to `withRecord st e message i`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack
open SigningCompilerO1SlackRun SigningCompilerO1SlackRead SigningCompilerO1SlackBuild
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem chainStepDigit_mk (d : Digit) (hd : d.val < 3) : chainStepDigit ⟨d.val, hd⟩ = d :=
  Fin.ext rfl

/-- A lifted step that keeps the linked invariant at `sig` and the signing state keeps the
invariant at `sig` and the signing state `st`, when `st` has the bound map of `sig`. -/
theorem linked_liftBase {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (sig st : TsigState C) (hbound : st.bound = sig.bound)
    {oa : SourceM C α}
    (h : ∀ starts, SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) oa)
    (hk : SourceKeeps (SourceState.signing (C := C)) oa) :
    SourcePreservesO1 P seeds q s
      (fun src backend => ReleaseInvariantO1 seeds s sig src backend ∧ src.base.signing = st)
      (liftBase oa) := by
  refine SourcePreservesO1.liftBase fun starts source backend hs r hr => ?_
  have hsig := hk.run P seeds q s source backend r hr
  exact ⟨(h starts source backend ⟨by rw [hs.2, hbound], hs.1⟩ r hr).2, hsig.trans hs.2⟩

/-- A release of the covered positions of one chain keeps the control fields of the base state and
the recorded digits. -/
theorem sourceReleaseCovered_control (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (e : KeyIndex) (l : ChainIndex) (src : SourceStateO1 C)
    (backend : CappedCompilerState C) (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s (sourceReleaseCovered P seeds e l) src backend)) :
    sourceControl r.1.2.base = sourceControl src.base ∧ r.1.2.starts = src.starts := by
  have hcov : SourcePreservesO1 P seeds q s
      (fun (current : SourceStateO1 C) (_ : CappedCompilerState C) =>
        sourceControl current.base = sourceControl src.base ∧ current.starts = src.starts)
      (sourceReleaseCovered P seeds e l) := by
    unfold sourceReleaseCovered
    refine SourcePreservesO1.bind SourcePreservesO1.get _ fun current => ?_
    split
    · refine SourcePreservesO1.liftBase fun starts source b h a ha => ?_
      exact ⟨((sourceControl_sourceReleaseBottomSuffix P seeds e l _).run P seeds q s
        source b a ha).trans h.1, h.2⟩
    · exact SourcePreservesO1.pure ()
  exact hcov src backend ⟨rfl, rfl⟩ r hr

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

/-- The record of a digit and the release of its chain keep the invariant and the control fields.
After them, the point of the digit is complete. -/
theorem recordThenCover_point (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (sig : TsigState C) (e : KeyIndex) (l : ChainIndex)
    (d : Digit) (hd : d.val < 3) (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s
      (recordStart e l d >>= fun _ => sourceReleaseCovered P seeds e l) src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧
      sourceControl r.1.2.base = sourceControl src.base ∧
      BottomDone seeds s r.2.1.1.data e l ⟨d.val, hd⟩ := by
  have hh := recordThenCover_slack P seeds hinj q s sig e l d src backend h r hr
  have hr' := hr
  simp only [runSourceO1_bind, recordStart, runSourceO1_modify, pure_bind] at hr'
  have hc := sourceReleaseCovered_control P seeds q s e l _ backend r hr'
  refine ⟨hh.1, hc.1, hh.2 ⟨d.val, hd⟩ ⟨d, ?_, le_rfl⟩⟩
  rw [hc.2]
  simp

/-- The callback of round 2 below the threshold. The coalition state holds the record of the
signer, and the base state holds the signing state from before the call. -/
theorem round2_callback_below (hinj : Function.Injective x.2.1) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (l : ChainIndex)
    (d : Digit) (hd : d.val < 3) (hb : st.bound e = some message)
    (hlt : (signersAt (withRecord st e message i) e message).card < C.t)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s (withRecord st e message i) src backend)
    (hst : src.base.signing = st)
    (r : (Digest × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s
      (round2Callback prims x i J message false (.chain bottomLayer e l d)) src backend)) :
    ReleaseInvariantO1 x.2.1 s (withRecord st e message i) r.1.2 r.2 ∧
      r.1.2.base.signing = st := by
  rw [round2Callback_below] at hr
  simp only [runSourceO1_bind, recordStart, runSourceO1_modify, pure_bind, runSourceO1_liftBase,
    support_map, Set.mem_image] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  have hheld : HeldReadable (withRecord st e message i)
      (Function.update src.starts e (Function.update (src.starts e) l (insert d (src.starts e l))))
      i (.chain bottomLayer e l d) :=
    ⟨e, l, ⟨d.val, hd⟩, message, by rw [chainStepDigit_mk], by simp [chainStepDigit_mk], hb,
      mem_signersAt_withRecord st e message i⟩
  have hinv : ReleaseInvariantO1 x.2.1 s (withRecord st e message i)
      ⟨src.base, Function.update src.starts e
        (Function.update (src.starts e) l (insert d (src.starts e l)))⟩ backend :=
    ⟨ReleaseSlackO1.record_below h.1 e l d message hb hlt, h.2.1, h.2.2⟩
  have hpart := sourcePart_held prims x q s (withRecord st e message i) _ hinj i J
    (.chain bottomLayer e l d) message hheld src.base backend ⟨by rw [hst], hinv⟩ a ha
  have hsig := congrArg Prod.fst
    ((sourceControl_sourcePart prims x i J (.chain bottomLayer e l d) message).run x.1 x.2.1 q s
      src.base backend a ha)
  exact ⟨hpart.2, hsig.trans hst⟩

/-- The callback of round 2 at the threshold. The coalition state is the signing state from before
the call. -/
theorem round2_callback_at (hinj : Function.Injective x.2.1) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (l : ChainIndex)
    (d : Digit) (hd : d.val < 3)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s st src backend) (hst : src.base.signing = st)
    (r : (Digest × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s
      (round2Callback prims x i J message true (.chain bottomLayer e l d)) src backend)) :
    ReleaseInvariantO1 x.2.1 s st r.1.2 r.2 ∧ r.1.2.base.signing = st := by
  rw [round2Callback_at] at hr
  simp only [runSourceO1_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, b, hb, hr⟩ := hr
  have hcover := recordThenCover_point q s x.1 x.2.1 hinj st e l d hd src backend h b
    (by rw [runSourceO1_bind, mem_support_bind_iff]; exact ⟨a, ha, hb⟩)
  have hsigb : b.1.2.base.signing = st := (congrArg Prod.fst hcover.2.1).trans hst
  rw [runSourceO1_liftBase, support_map] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  have hread : PointReadable x.2.1 b.1.2.base b.2.1.1.data (.chain bottomLayer e l d) := by
    refine Or.inl fun T => ?_
    obtain ⟨value, hv⟩ := hcover.2.2.2.1 T
    rw [chainStepDigit_mk] at hv
    rw [hv]
    exact Option.some_ne_none value
  have hpart := sourcePart_readO1 prims x q s st b.1.2.starts hinj i J (.chain bottomLayer e l d)
    message b.1.2.base b.2 ⟨⟨by rw [hsigb], hcover.1⟩, hread⟩ c hc
  have hsig := congrArg Prod.fst
    ((sourceControl_sourcePart prims x i J (.chain bottomLayer e l d) message).run x.1 x.2.1 q s
      b.1.2.base b.2 c hc)
  exact ⟨hpart.1.2, hsig.trans hsigb⟩

/-- The codeword search and the chain parts of round 2 below the threshold. A failed search keeps
the invariant at the signing state from before the call. A success gives the invariant at the state
with the record of the signer. -/
theorem round2_values_below (hinj : Function.Injective x.2.1) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (commitment : Digest) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (hb : st.bound e = some message)
    (hlt : (signersAt (withRecord st e message i) e message).card < C.t)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s st src backend) (hst : src.base.signing = st)
    (r : (Option (ChainIndex → Option Digest) × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s
      (signRound2With (fun oa => liftBase (sourceRoProgram prims x.1 x.2.1 oa))
        (round2Callback prims x i J message false) x.1 J commitment e message parts)
      src backend)) :
    r.1.2.base.signing = st ∧
      ReleaseInvariantO1 x.2.1 s
        (if r.1.1.isSome then withRecord st e message i else st) r.1.2 r.2 := by
  unfold signRound2With at hr
  rw [runSourceO1_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  have hcode := linked_liftBase x.1 x.2.1 q s st st rfl
    (fun starts => sourceCodeword_linked x.1 x.2.1 q s st starts prims hinj commitment e message _)
    ((sourceControl_sourceRoProgram prims x.1 x.2.1 _).comp Prod.fst) src backend ⟨h, hst⟩ a ha
  rcases a with ⟨⟨_ | ⟨randomness, encoding⟩, mid⟩, midBackend⟩
  · simp only [runSourceO1_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨hcode.2, by simpa using hcode.1⟩
  · simp only [runSourceO1_bind, mem_support_bind_iff] at hr
    obtain ⟨b, hb', hr⟩ := hr
    rw [runSourceO1_pure, mem_support_pure_iff] at hr
    subst r
    have loop : SourcePreservesO1 x.1 x.2.1 q s
        (fun src backend => ReleaseInvariantO1 x.2.1 s (withRecord st e message i) src backend ∧
          src.base.signing = st)
        (Concrete.sequenceFin fun l =>
          if (encoding l).val < chainLength - 1 then
            some <$> round2Callback prims x i J message false (.chain bottomLayer e l (encoding l))
          else pure none) := by
      refine SourcePreservesO1.sequenceFin _ _ fun l => ?_
      split
      · rename_i hpos
        exact SourcePreservesO1.map (fun src backend hs r hr => round2_callback_below prims x q s
          hinj st i J e message l (encoding l) hpos hb hlt src backend hs.1 hs.2 r hr) some
      · exact SourcePreservesO1.pure none
    have hl := loop mid midBackend
      ⟨⟨ReleaseSlackO1.promote_below hcode.1.1 e message i hlt, hcode.1.2.1, hcode.1.2.2⟩,
        hcode.2⟩ b hb'
    exact ⟨hl.2, by simpa using hl.1⟩

/-- The codeword search and the chain parts of round 2 at the threshold keep the invariant at the
signing state from before the call. -/
theorem round2_values_at (hinj : Function.Injective x.2.1) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (commitment : Digest) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s st src backend) (hst : src.base.signing = st)
    (r : (Option (ChainIndex → Option Digest) × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s
      (signRound2With (fun oa => liftBase (sourceRoProgram prims x.1 x.2.1 oa))
        (round2Callback prims x i J message true) x.1 J commitment e message parts)
      src backend)) :
    ReleaseInvariantO1 x.2.1 s st r.1.2 r.2 ∧ r.1.2.base.signing = st := by
  have key : SourcePreservesO1 x.1 x.2.1 q s
      (fun src backend => ReleaseInvariantO1 x.2.1 s st src backend ∧ src.base.signing = st)
      (signRound2With (fun oa => liftBase (sourceRoProgram prims x.1 x.2.1 oa))
        (round2Callback prims x i J message true) x.1 J commitment e message parts) := by
    unfold signRound2With
    refine SourcePreservesO1.bind (linked_liftBase x.1 x.2.1 q s st st rfl
      (fun starts => sourceCodeword_linked x.1 x.2.1 q s st starts prims hinj commitment e
        message _)
      ((sourceControl_sourceRoProgram prims x.1 x.2.1 _).comp Prod.fst)) _ fun answer => ?_
    cases answer with
    | none => exact SourcePreservesO1.pure none
    | some answer =>
        rcases answer with ⟨randomness, encoding⟩
        refine SourcePreservesO1.bind (SourcePreservesO1.sequenceFin _ _ fun l => ?_) _
          fun _ => SourcePreservesO1.pure _
        split
        · rename_i hpos
          exact SourcePreservesO1.map (fun src backend hs r hr => round2_callback_at prims x q s
            hinj st i J e message l (encoding l) hpos src backend hs.1 hs.2 r hr) some
        · exact SourcePreservesO1.pure none
  exact key src backend ⟨h, hst⟩ r hr

/-- Round 2 keeps the invariant at the signing state of the source. -/
theorem sourceRound2O1_stable (hinj : Function.Injective x.2.1) (top : TopTree)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s src.base.signing src backend)
    (r : (TsigSpec C (.round2 i J e message parts) × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s
      (sourceTsigO1 prims x top (.round2 i J e message parts)) src backend)) :
    ReleaseInvariantO1 x.2.1 s r.1.2.base.signing r.1.2 r.2 := by
  rw [sourceRound2O1_eq] at hr
  simp only [runSourceO1_bind, runSourceO1_get, pure_bind] at hr
  split at hr
  · rw [runSourceO1_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  · rename_i hguard
    have hbound : src.base.signing.bound e = some message := by tauto
    rw [runSourceO1_bind, mem_support_bind_iff] at hr
    obtain ⟨built, hbuilt, hr⟩ := hr
    have hb := linked_liftBase x.1 x.2.1 q s src.base.signing src.base.signing rfl
      (fun starts => sourceBottomOnce_linked x.1 x.2.1 q s src.base.signing starts hinj top
        (treeOf e))
      (sourceSigning_sourceBottomOnce x.1 x.2.1 top (treeOf e)) src backend ⟨h, rfl⟩ built hbuilt
    cases ht : built.1.1 with
    | none =>
        simp only [ht, runSourceO1_pure, mem_support_pure_iff] at hr
        subst r
        rw [hb.2]
        exact hb.1
    | some tree =>
        simp only [ht, runSourceO1_bind, mem_support_bind_iff] at hr
        obtain ⟨own, hown, values, hvalues, hr⟩ := hr
        rw [runSourceO1_liftBase, support_map] at hown
        obtain ⟨own, hown, rfl⟩ := hown
        have hread : PointReadable x.2.1 built.1.2.base built.2.1.1.data
            (.randomizer bottomLayer e) :=
          Or.inr ⟨e, rfl, by rw [hb.2, hbound]; exact Option.some_ne_none _⟩
        have ho := sourcePart_readO1 prims x q s src.base.signing built.1.2.starts hinj i J
          (.randomizer bottomLayer e) message built.1.2.base built.2 ⟨⟨by rw [hb.2], hb.1⟩, hread⟩
          own hown
        have hos : own.1.2.signing = src.base.signing := (congrArg Prod.fst
          ((sourceControl_sourcePart prims x i J (.randomizer bottomLayer e) message).run x.1
            x.2.1 q s built.1.2.base built.2 own hown)).trans hb.2
        by_cases hth : C.t ≤ (signersAt (withRecord src.base.signing e message i) e message).card
        · have hrt : roundTwoReleased src.base.signing e message i = true := by
            simpa [roundTwoReleased] using hth
          rw [hrt] at hvalues hr
          have hv := round2_values_at prims x q s hinj src.base.signing i J (tree.commitment e) e
            message (Function.update parts i own.1.1) _ own.2 ho.1.2 hos values hvalues
          cases hvv : values.1.1 with
          | none =>
              simp only [hvv, runSourceO1_pure, mem_support_pure_iff] at hr
              subst r
              rw [hv.2]
              exact hv.1
          | some chainValues =>
              simp only [hvv, ↓reduceIte, runSourceO1_bind, mem_support_bind_iff] at hr
              obtain ⟨swept, hswept, hr⟩ := hr
              simp only [runSourceO1_modify, runSourceO1_pure, mem_support_pure_iff] at hr
              obtain ⟨_, rfl, rfl⟩ := hr
              have hk := sourceReleaseKey_slack x.1 x.2.1 hinj q s src.base.signing e values.1.2
                values.2 hv.1 swept hswept
              have hkc := sourceReleaseKey_control q s x.1 x.2.1 e values.1.2 values.2 swept hswept
              have hsig : swept.1.2.base.signing = src.base.signing :=
                (congrArg Prod.fst hkc.1).trans hv.2
              refine ReleaseInvariantO1.source_frame (src := swept.1.2) ?_ rfl rfl
              rw [hsig]
              exact ⟨ReleaseSlackO1.promote_covered hk.1.1 e message i hk.2, hk.1.2.1, hk.1.2.2⟩
        · have hrt : roundTwoReleased src.base.signing e message i = false := by
            simpa [roundTwoReleased] using hth
          rw [hrt] at hvalues hr
          have hv := round2_values_below prims x q s hinj src.base.signing i J (tree.commitment e)
            e message (Function.update parts i own.1.1) hbound (not_le.mp hth) _ own.2 ho.1.2 hos
            values hvalues
          cases hvv : values.1.1 with
          | none =>
              simp only [hvv, runSourceO1_pure, mem_support_pure_iff] at hr
              subst r
              rw [hv.1]
              simpa [hvv] using hv.2
          | some chainValues =>
              simp only [hvv, Bool.false_eq_true, ↓reduceIte, runSourceO1_bind, runSourceO1_modify,
                runSourceO1_pure, pure_bind, mem_support_pure_iff] at hr
              subst r
              refine ReleaseInvariantO1.source_frame (src := values.1.2) ?_ rfl rfl
              rw [hv.1]
              simpa [hvv] using hv.2

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.chainStepDigit_mk' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.chainStepDigit_mk

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.linked_liftBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.linked_liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.sourceReleaseCovered_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.sourceReleaseCovered_control

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.recordThenCover_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.recordThenCover_point

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_callback_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_callback_below

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_callback_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_callback_at

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_values_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_values_below

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_values_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.round2_values_at

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.sourceRound2O1_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRound2.sourceRound2O1_stable
