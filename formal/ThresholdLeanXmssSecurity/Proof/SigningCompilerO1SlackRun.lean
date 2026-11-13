import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Slack

/-! # Runs of the O1 source

`SourcePreservesO1` states that each supported run of the O1 source over the capped backend keeps
a joint invariant. The combinators of this file give it for `pure`, `get`, `modify`, `bind`, `map`,
`mapM`, `sequenceFin`, `simulateQ` and a lifted step of the base source.

Each run keeps the valid pending answers. A step that keeps the signing state keeps the link of
the bound maps. A release sweep of one key keeps the control fields of the base state and the
recorded digits.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Steps
variable (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

/-- A step that keeps the signing state of the source keeps the link of the bound maps. -/
theorem linked_of_signing {α : Type} (oa : SourceM C α)
    (hc : SourceKeeps (SourceState.signing (C := C)) oa)
    (hi : ∀ source backend, LinkedInvariant seeds s sig starts source backend →
      ∀ r : (α × SourceState C) × CappedCompilerState C,
        r ∈ support (runSource P seeds q s oa source backend) →
          BaseInvariant seeds s sig starts r.1.2 r.2) :
    SourcePreserves P seeds q s (LinkedInvariant seeds s sig starts) oa := by
  intro source backend h r hr
  refine ⟨?_, hi source backend h r hr⟩
  rw [hc.run P seeds q s source backend r hr]
  exact h.1

end Steps

namespace SourcePreservesO1
variable {P : PublicParameter} {seeds : C.Term → HashOutput} {q : ℕ} {s : HiddenKey → Digest}
  {I : SourceStateO1 C → CappedCompilerState C → Prop}

theorem pure {α : Type} (value : α) : SourcePreservesO1 P seeds q s I (Pure.pure value) := by
  intro src backend hs r hr
  rw [runSourceO1_pure, mem_support_pure_iff] at hr
  subst r
  exact hs

theorem get : SourcePreservesO1 P seeds q s I (get : SourceMO1 C (SourceStateO1 C)) := by
  intro src backend hs r hr
  rw [runSourceO1_get, mem_support_pure_iff] at hr
  subst r
  exact hs

theorem modify (f : SourceStateO1 C → SourceStateO1 C)
    (hf : ∀ src backend, I src backend → I (f src) backend) :
    SourcePreservesO1 P seeds q s I (modify f : SourceMO1 C Unit) := by
  intro src backend hs r hr
  rw [runSourceO1_modify, mem_support_pure_iff] at hr
  subst r
  exact hf src backend hs

theorem bind {α β : Type} {oa : SourceMO1 C α} (h : SourcePreservesO1 P seeds q s I oa)
    (next : α → SourceMO1 C β) (hn : ∀ value, SourcePreservesO1 P seeds q s I (next value)) :
    SourcePreservesO1 P seeds q s I (oa >>= next) := by
  intro src backend hs r hr
  rw [runSourceO1_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact hn a.1.1 a.1.2 a.2 (h src backend hs a ha) r hr

theorem map {α β : Type} {oa : SourceMO1 C α} (h : SourcePreservesO1 P seeds q s I oa)
    (f : α → β) : SourcePreservesO1 P seeds q s I (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact SourcePreservesO1.bind h _ fun value => SourcePreservesO1.pure (f value)

theorem mapM {α β : Type} (items : List α) (oa : α → SourceMO1 C β)
    (h : ∀ a ∈ items, SourcePreservesO1 P seeds q s I (oa a)) :
    SourcePreservesO1 P seeds q s I (items.mapM oa) := by
  induction items with
  | nil => exact SourcePreservesO1.pure []
  | cons a items ih =>
      rw [List.mapM_cons]
      refine SourcePreservesO1.bind (h a (List.mem_cons_self ..)) _ fun head => ?_
      refine SourcePreservesO1.bind (ih fun b hb => h b (List.mem_cons_of_mem _ hb)) _ fun tail => ?_
      exact SourcePreservesO1.pure _

theorem sequenceFin {α : Type} (n : ℕ) (oa : Fin n → SourceMO1 C α)
    (h : ∀ i, SourcePreservesO1 P seeds q s I (oa i)) :
    SourcePreservesO1 P seeds q s I (Concrete.sequenceFin oa) := by
  induction n with
  | zero => exact SourcePreservesO1.pure _
  | succ n ih =>
      simp only [Concrete.sequenceFin]
      refine SourcePreservesO1.bind (h 0) _ fun head => ?_
      refine SourcePreservesO1.bind (ih (fun i => oa i.succ) fun i => h i.succ) _ fun tail => ?_
      exact SourcePreservesO1.pure _

theorem simulateQ {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (SourceMO1 C))
    (step : ∀ t, SourcePreservesO1 P seeds q s I (impl t)) (oa : OracleComp spec α) :
    SourcePreservesO1 P seeds q s I (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using SourcePreservesO1.pure (I := I) value
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact SourcePreservesO1.bind (step t) _ ih

/-- A step of the base source keeps an invariant of the O1 source when it keeps the invariant for
each fixed map of recorded digits. -/
theorem liftBase {α : Type} {oa : SourceM C α}
    (h : ∀ starts, SourcePreserves P seeds q s (fun source backend => I ⟨source, starts⟩ backend) oa) :
    SourcePreservesO1 P seeds q s I (liftBase oa) := by
  intro src backend hs r hr
  rw [runSourceO1_liftBase, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact h src.starts src.base backend hs a ha

end SourcePreservesO1

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

/-- Each run of the O1 source keeps the valid pending answers. -/
theorem runSourceO1_pendingValid {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : SourceMO1 C α) (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data) (r : (α × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s oa src backend)) :
    PendingValid r.2.1.1.data :=
  simulateQ_sticky _ (fun st : CappedCompilerState C => PendingValid st.1.1.data)
    (cappedCompiler_pendingValid_step P seeds q s) (oa.run src) backend hv r hr

/-- A release sweep of one key keeps the control fields of the base state and the recorded
digits. -/
theorem sourceReleaseKey_control (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s (sourceReleaseKey P seeds e) src backend)) :
    sourceControl r.1.2.base = sourceControl src.base ∧ r.1.2.starts = src.starts := by
  have hkey : SourcePreservesO1 P seeds q s
      (fun (current : SourceStateO1 C) (_ : CappedCompilerState C) =>
        sourceControl current.base = sourceControl src.base ∧ current.starts = src.starts)
      (sourceReleaseKey P seeds e) := by
    unfold sourceReleaseKey
    refine SourcePreservesO1.bind (SourcePreservesO1.mapM _ _ fun l _ => ?_) _
      fun _ => SourcePreservesO1.pure ()
    unfold sourceReleaseCovered
    refine SourcePreservesO1.bind SourcePreservesO1.get _ fun current => ?_
    split
    · refine SourcePreservesO1.liftBase fun starts source b h a ha => ?_
      exact ⟨((sourceControl_sourceReleaseBottomSuffix P seeds e l _).run P seeds q s
        source b a ha).trans h.1, h.2⟩
    · exact SourcePreservesO1.pure ()
  exact hkey src backend ⟨rfl, rfl⟩ r hr

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.linked_of_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.linked_of_signing

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.mapM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.sequenceFin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.simulateQ

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.liftBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.SourcePreservesO1.liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.runSourceO1_pendingValid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.runSourceO1_pendingValid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.sourceReleaseKey_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackRun.sourceReleaseKey_control
