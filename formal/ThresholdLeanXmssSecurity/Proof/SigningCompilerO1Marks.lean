import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareMarks
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Share

/-! # Marks and tags of the O1 source

A quiet segment of the O1 source asks no mark and keeps the hidden flag. Each signing request of
the O1 source is quiet. Each oracle call of the O1 source starts with the mark of its final flag.
`shareRunO1_tagTrue` states that a first share failure with a true tag gives a final hidden flag
that is up.

The lemmas are the lemmas of `SigningCompilerShare.Marks` for the O1 program. The flag is
`st.base.hiddenFlag`. The lift `liftBaseX` keeps a quiet segment of the base source quiet. The
answer of a tree request goes through `patchTree`. This map makes no query and sets no mark.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Marks
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof SigningCompilerShare
open SigningCompilerO1SourceProof SigningCompilerO1Share
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
attribute [local irreducible] sourceProgramX sourceProgram sourceGameX sourceGame
attribute [local irreducible] sourceProgramO1X sourceGameO1X

/-- A segment of the O1 source that asks no mark and keeps the hidden flag. -/
def QuietO1 {α : Type} (oa : SourceMXO1 C α) : Prop :=
  ∀ st, Queries Marks.NoMark (oa.run st) ∧
    ∀ r ∈ support (oa.run st), r.2.base.hiddenFlag = st.base.hiddenFlag

namespace QuietO1
variable {α β : Type}

theorem pure (a : α) : QuietO1 (C := C) (Pure.pure a) := by
  intro st
  refine ⟨Queries.pure _, ?_⟩
  intro r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  rfl

theorem get : QuietO1 (get : SourceMXO1 C (SourceStateO1 C)) := by
  intro st
  refine ⟨Queries.pure _, ?_⟩
  intro r hr
  simp only [StateT.run_get, mem_support_pure_iff] at hr
  subst r
  rfl

theorem modify (f : SourceStateO1 C → SourceStateO1 C)
    (hf : ∀ st, (f st).base.hiddenFlag = st.base.hiddenFlag) :
    QuietO1 (modify f : SourceMXO1 C Unit) := by
  intro st
  refine ⟨Queries.pure _, ?_⟩
  intro r hr
  have h : r = ((), f st) := by simpa only [StateT.run_modify, mem_support_pure_iff] using hr
  simpa only [h] using hf st

theorem bind {oa : SourceMXO1 C α} {f : α → SourceMXO1 C β}
    (h : QuietO1 oa) (hf : ∀ a, QuietO1 (f a)) : QuietO1 (oa >>= f) := by
  intro st
  refine ⟨(h st).1.bind (fun z => (hf z.1 z.2).1), ?_⟩
  intro r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact ((hf a.1 a.2).2 r hr).trans ((h st).2 a ha)

theorem map (f : α → β) {oa : SourceMXO1 C α} (h : QuietO1 oa) : QuietO1 (f <$> oa) := by
  simpa only [bind_pure_comp] using h.bind (fun a => pure (f a))

theorem mapM (xs : List α) (f : α → SourceMXO1 C β)
    (h : ∀ a ∈ xs, QuietO1 (f a)) : QuietO1 (xs.mapM f) := by
  induction xs with
  | nil => exact pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      exact (h a (List.mem_cons_self ..)).bind fun b =>
        (ih fun a ha => h a (List.mem_cons_of_mem _ ha)).bind fun bs => pure (b :: bs)

theorem sequenceFin {n : ℕ} (f : Fin n → SourceMXO1 C α) (h : ∀ a, QuietO1 (f a)) :
    QuietO1 (Concrete.sequenceFin f) := by
  induction n with
  | zero => exact pure _
  | succ n ih =>
      exact (h 0).bind fun a => (ih _ fun i => h i.succ).bind fun as => pure _

theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMXO1 C)) (oa : OracleComp spec α)
    (h : ∀ t, QuietO1 (impl t)) : QuietO1 (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (C := C) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (h t).bind ih

/-- A quiet segment of the base source is a quiet segment of the O1 source. -/
theorem liftBaseX {oa : SourceMX C α} (h : Marks.Quiet oa) : QuietO1 (liftBaseX oa) := by
  intro st
  have hq := h st.base
  refine ⟨hq.1.map _, ?_⟩
  intro r hr
  change r ∈ support ((fun r => (r.1, { st with base := r.2 })) <$> oa.run st.base) at hr
  obtain ⟨a, ha, rfl⟩ := mem_support_map_peel _ _ hr
  exact hq.2 a ha

end QuietO1

attribute [local irreducible] Queries QuietO1

theorem QuietO1.at {α : Type} {oa : SourceMXO1 C α} (h : QuietO1 oa) (st : SourceStateO1 C) :
    Queries Marks.NoMark (oa.run st) ∧
      ∀ r ∈ support (oa.run st), r.2.base.hiddenFlag = st.base.hiddenFlag := by
  unfold QuietO1 at h
  exact h st

local macro "quiet_step" : tactic => `(tactic|
  first
    | with_reducible exact QuietO1.pure _
    | with_reducible exact QuietO1.get
    | (with_reducible refine QuietO1.modify _ ?_; intro st; rfl)
    | with_reducible apply QuietO1.liftBaseX
    | (with_reducible refine QuietO1.bind ?_ (fun a => ?_))
    | with_reducible apply QuietO1.map
    | (with_reducible apply QuietO1.mapM; intro a ha)
    | (with_reducible apply QuietO1.sequenceFin; intro a)
    | assumption
    | split
    | (dsimp only; split))

theorem quiet_recordStartX (e : KeyIndex) (l : ChainIndex) (pos : Digit) :
    QuietO1 (recordStartX (C := C) e l pos) :=
  QuietO1.modify _ fun _ => rfl

theorem quiet_sourceReleaseCoveredX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : QuietO1 (sourceReleaseCoveredX P seeds e l) := by
  unfold sourceReleaseCoveredX
  repeat' first | with_reducible apply Marks.quiet_sourceReleaseBottomSuffixX | quiet_step

theorem quiet_sourceReleaseKeyX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : QuietO1 (sourceReleaseKeyX P seeds e) := by
  unfold sourceReleaseKeyX
  repeat' first | with_reducible apply quiet_sourceReleaseCoveredX | quiet_step

/-- Each signing request of the O1 source asks no mark and keeps the hidden flag. -/
theorem quiet_sourceTsigO1X (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (t : TsigQuery C) : QuietO1 (sourceTsigO1X prims x top t) := by
  cases t <;> unfold sourceTsigO1X
  all_goals repeat' first
    | with_reducible apply Marks.quiet_sourceTsigX
    | with_reducible apply Marks.quiet_sourceBottomOnceX
    | with_reducible apply Marks.quiet_sourcePartX
    | with_reducible apply Marks.quiet_sourceRoProgramX
    | with_reducible apply quiet_recordStartX
    | with_reducible apply quiet_sourceReleaseCoveredX
    | with_reducible apply quiet_sourceReleaseKeyX
    | (unfold signRound2With)
    | quiet_step

/-- The rest of an oracle call of the O1 source after its first mark. -/
def callRestO1 (prims : Primitives) (x : Keys3 C) (top : TopTree) (st : SourceStateO1 C) :
    (t : (LocalSpec C + TsigSpec C).Domain) → SourceMXO1 C ((LocalSpec C + TsigSpec C) t)
  | .inl t => SigningCompilerO1SourceProof.liftBaseX (Marks.callRest prims x top st.base (.inl t))
  | .inr t => do
      let value ← sourceTsigO1X prims x top t
      modify fun (s : SourceStateO1 C) =>
        { s with base := { s.base with exposed := releasedTrees s.base.exposed t } }
      pure value

/-- Each oracle call of the O1 source starts with the mark of its final flag. -/
theorem sourceOraclesO1X_marked (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (st : SourceStateO1 C) (t : (LocalSpec C + TsigSpec C).Domain) :
    (sourceOraclesO1X prims x top t).run st =
      markQ (Marks.callMark x st.base t) >>= fun _ => (callRestO1 prims x top st t).run st := by
  cases t with
  | inl t =>
      change (SigningCompilerO1SourceProof.liftBaseX (sourceOraclesX prims x top (.inl t))).run st = _
      simp only [SigningCompilerO1SourceProof.liftBaseX, callRestO1, StateT.run_mk,
        Marks.sourceOraclesX_marked, map_bind]
  | inr t =>
      simp only [sourceOraclesO1X, StateT.run_bind, StateT.run_get, pure_bind, Marks.callMark,
        callRestO1]
      rfl

theorem callRestO1_noMark (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (st : SourceStateO1 C) (t : (LocalSpec C + TsigSpec C).Domain) :
    Queries Marks.NoMark ((callRestO1 prims x top st t).run st) := by
  cases t with
  | inl t =>
      change Queries Marks.NoMark ((fun r => (r.1, { st with base := r.2 })) <$>
        (Marks.callRest prims x top st.base (.inl t)).run st.base)
      exact (Marks.callRest_noMark prims x top st.base (.inl t)).map _
  | inr t =>
      simp only [callRestO1, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
      exact ((quiet_sourceTsigO1X prims x top t).at st).1.bind fun z => Queries.pure _

theorem callRestO1_flag (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (st : SourceStateO1 C) (t : (LocalSpec C + TsigSpec C).Domain)
    (r : (LocalSpec C + TsigSpec C) t × SourceStateO1 C)
    (hr : r ∈ support ((callRestO1 prims x top st t).run st)) :
    r.2.base.hiddenFlag = Marks.callMark x st.base t := by
  cases t with
  | inl t =>
      change r ∈ support ((fun r => (r.1, { st with base := r.2 })) <$>
        (Marks.callRest prims x top st.base (.inl t)).run st.base) at hr
      obtain ⟨a, ha, rfl⟩ := mem_support_map_peel _ _ hr
      exact Marks.callRest_flag prims x top st.base (.inl t) a ha
  | inr t =>
      simp only [callRestO1, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      exact ((quiet_sourceTsigO1X prims x top t).at st).2 z hz

/-- At each boundary of a segment the mark is the hidden flag, the flag only rises, and each stored
tag is below the flag. -/
def TagSafeO1 {α : Type}
    (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : SourceMXO1 C α) : Prop :=
  ∀ (st : SourceStateO1 C) (bm : CappedCompilerState C × Bool) (sh : ShareState C),
    bm.2 = st.base.hiddenFlag → Marks.TagLe st.base.hiddenFlag sh →
    ∀ z ∈ support (Marks.jointRun H P seeds q s pads (oa.run st) bm sh),
      z.1.2.2 = z.1.1.2.base.hiddenFlag ∧ st.base.hiddenFlag ≤ z.1.1.2.base.hiddenFlag ∧
        Marks.TagLe z.1.1.2.base.hiddenFlag z.2

namespace TagSafeO1
variable {α β : Type}
variable {H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp)}
variable {P : PublicParameter} {seeds : C.Term → HashOutput} {q : ℕ}
variable {s : HiddenKey → Digest} {pads : Point → Digest}

theorem pure (a : α) : TagSafeO1 H P seeds q s pads (Pure.pure a) := by
  intro st bm sh he ht z hz
  simp only [StateT.run_pure, Marks.jointRun, simulateQ_pure, mem_support_pure_iff] at hz
  subst z
  exact ⟨he, le_rfl, ht⟩

theorem bind {oa : SourceMXO1 C α} {f : α → SourceMXO1 C β}
    (h : TagSafeO1 H P seeds q s pads oa) (hf : ∀ a, TagSafeO1 H P seeds q s pads (f a)) :
    TagSafeO1 H P seeds q s pads (oa >>= f) := by
  intro st bm sh he ht z hz
  rw [StateT.run_bind, Marks.jointRun_bind] at hz
  simp only [mem_support_bind_iff] at hz
  obtain ⟨mid, hm, hz⟩ := hz
  have hi := h st bm sh he ht mid hm
  have hj := hf mid.1.1.1 mid.1.1.2 mid.1.2 mid.2 hi.1 hi.2.2 z hz
  exact ⟨hj.1, hi.2.1.trans hj.2.1, hj.2.2⟩

theorem map (f : α → β) {oa : SourceMXO1 C α} (h : TagSafeO1 H P seeds q s pads oa) :
    TagSafeO1 H P seeds q s pads (f <$> oa) := by
  simpa only [bind_pure_comp] using h.bind (fun a => pure (f a))

theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMXO1 C)) (oa : OracleComp spec α)
    (h : ∀ t, TagSafeO1 H P seeds q s pads (impl t)) :
    TagSafeO1 H P seeds q s pads (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (H := H) (P := P) (seeds := seeds) (q := q) (s := s) (pads := pads) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (h t).bind ih

theorem get_mark (f : SourceStateO1 C → SourceMXO1 C α)
    (hf : ∀ st, TagSafeO1 H P seeds q s pads (f st)) :
    TagSafeO1 H P seeds q s pads (do
      let st ← get
      let _ ← liftM (markQ (C := C) st.base.hiddenFlag)
      f st) := by
  intro st bm sh he ht z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  change z ∈ support (Marks.jointRun H P seeds q s pads
    (markQ st.base.hiddenFlag >>= fun _ => (f st).run st) bm sh) at hz
  rw [Marks.jointRun_bind, Marks.joint_mark] at hz
  simp only [pure_bind] at hz
  exact hf st st (bm.1, st.base.hiddenFlag) sh rfl ht z hz

end TagSafeO1

theorem QuietO1.tagSafe {α : Type} {oa : SourceMXO1 C α} (h : QuietO1 oa)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput) :
    TagSafeO1 (Marks.handler τ draw finish) P seeds q s pads oa := by
  intro st bm sh he ht z hz
  have hq := h.at st
  have hj := Marks.joint_noMark P seeds q s pads τ draw finish (oa.run st) hq.1
    bm sh (by simpa only [he] using ht) z hz
  have hf := hq.2 z.1.1 hj.2.2
  exact ⟨hj.1.trans (he.trans hf.symm), by simp only [hf]; exact le_rfl,
    by simpa only [hf, he] using hj.2.1⟩

theorem sourceOraclesO1X_tagSafe (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (t : (LocalSpec C + TsigSpec C).Domain) :
    TagSafeO1 (Marks.handler τ draw finish) x.1 x.2.1 q s pads
      (sourceOraclesO1X prims x top t) := by
  intro st bm sh he ht z hz
  rw [sourceOraclesO1X_marked, Marks.jointRun_bind, Marks.joint_mark] at hz
  simp only [pure_bind] at hz
  have hmono := Marks.flag_le_callMark x st.base t
  have hj := Marks.joint_noMark x.1 x.2.1 q s pads τ draw finish
    ((callRestO1 prims x top st t).run st) (callRestO1_noMark prims x top st t)
    (bm.1, Marks.callMark x st.base t) sh (ht.mono hmono) z hz
  have hf := callRestO1_flag prims x top st t z.1.1 hj.2.2
  exact ⟨hj.1.trans hf.symm, by simpa only [hf] using hmono,
    by simpa only [hf] using hj.2.1⟩

attribute [local irreducible] TagSafeO1

theorem sourceGameO1X_tagSafe (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput) :
    TagSafeO1 (Marks.handler τ draw finish) x.1 x.2.1 q s pads (sourceGameO1X prims A x) := by
  unfold sourceGameO1X
  apply TagSafeO1.get_mark
  intro initial
  apply TagSafeO1.bind ((QuietO1.liftBaseX (Marks.quiet_sourceTopTreeX x.1 x.2.1)).tagSafe
    x.1 x.2.1 q s pads τ draw finish)
  intro top
  apply TagSafeO1.bind (TagSafeO1.simulate _ _
    (sourceOraclesO1X_tagSafe prims x top q s pads τ draw finish))
  intro forgery
  apply TagSafeO1.get_mark
  intro st
  apply TagSafeO1.bind
    ((QuietO1.simulate _ _ fun input => QuietO1.liftBaseX
      (Marks.quiet_verify x.1 x.2.1 st.base input)).tagSafe x.1 x.2.1 q s pads τ draw finish)
  intro verified
  split <;> simp only [pure_bind]
  · exact TagSafeO1.pure _
  · exact ((QuietO1.liftBaseX (Marks.quiet_sourceHonestSignatureX prims x top _ _)).tagSafe
      x.1 x.2.1 q s pads τ draw finish).bind fun _ => TagSafeO1.pure _

/-- A first share failure with a true tag gives a final hidden flag that is up. -/
theorem shareRunO1_tagTrue (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (z : CompilerOutcomeO1 C × ShareState C)
    (hz : z ∈ support ((simulateQ (Marks.handler τ draw finish)
      (shareRunTagO1 prims A x q s pads Prod.snd)).run SigningShareLazy.init))
    (k : SigningShareLazy.Kind) (l : Bool) (hbad : z.2.bad = some (true, k, l)) :
    z.1.1.2.base.hiddenFlag = true := by
  change z ∈ support ((simulateQ (Marks.handler τ draw finish) (do
      let result ← (simulateQ (shareBackend x.1 x.2.1 q s pads)
        (sourceProgramO1X prims A x)).run (((compilerInit, 0), fun _ => none, false), false)
      let view ← shareQuery (C := C) .view
      pure (result.1, merged x.2.1 result.2.1 view.1))).run SigningShareLazy.init) at hz
  simp only [simulateQ_bind, StateT.run_bind, Marks.handler_view, pure_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := sourceGameO1X_tagSafe prims A x q s pads τ draw finish
  unfold TagSafeO1 at hs
  have hi : Marks.TagLe (sourceInitO1 (C := C)).base.hiddenFlag
      (SigningShareLazy.init (κ := C.Term) (ι := CPoint) (B := SigningShareLazy.ImplBad Bool)) := by
    intro b k l hb
    simp [SigningShareLazy.init] at hb
  have result := hs sourceInitO1 (((compilerInit, 0), fun _ => none, false), false)
    SigningShareLazy.init rfl hi r (by simpa only [Marks.jointRun, sourceProgramO1X] using hr)
  have hb := result.2.2 true k l hbad
  exact Bool.le_iff_imp.mp hb rfl

end ThresholdLeanXmssSecurity.SigningCompilerO1Marks

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Marks.quiet_sourceTsigO1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Marks.quiet_sourceTsigO1X

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Marks.sourceOraclesO1X_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Marks.sourceOraclesO1X_marked

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Marks.sourceGameO1X_tagSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Marks.sourceGameO1X_tagSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Marks.shareRunO1_tagTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Marks.shareRunO1_tagTrue
