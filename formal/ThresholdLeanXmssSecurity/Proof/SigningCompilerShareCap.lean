import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTag
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareNoFalse

/-!
# Cap-tagged first-bad transport for the signing compiler

The paired tag records the source hidden flag and backend cap at the first
share failure. The cap event before that failure transfers from the eager
fiber table to the fixed-pad compiler.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShareCap
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag

-- The following frozen-law port is SigningCompilerShareTable:26–124 with
-- the already generic SigningShareLazy tag specialized to Bool × Bool.
variable {C : Committee}

def capTag (st : CappedCompilerState C × Bool) : Bool × Bool := (st.2, st.1.2.2)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev FrozenStateC (C : Committee) :=
  SigningShareLazy.ShareState C.Term CPoint (SigningShareLazy.FrozenBad (Bool × Bool))

def eagerHandlerC (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    QueryImpl (RunSpecT C (Bool × Bool)) (StateT (ShareStateT C (Bool × Bool)) ProbComp) :=
  SigningShareLazy.unifImpl (ShareStateT C (Bool × Bool)) +
    SigningShareLazy.eagerImpl (Tag := Bool × Bool) C.terms τ g

@[simp] theorem erase_init :
    SigningShareLazy.erase (SigningShareLazy.init : ShareStateT C (Bool × Bool)) =
      (SigningShareLazy.init : FrozenStateC C) := rfl

private theorem ordinary_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((ordinary P seeds q s pads t).run st)) : st.2.2 ≤ r.2.2.2 := by
  have sticky (h : st.2.2 = true) : r.2.2.2 = true := by
    cases t with
    | inr k => exact cappedCompiler_flag_sticky P seeds q s (.inr k) st h r hr
    | inl t =>
      cases t with
      | pad p =>
        simp only [ordinary, StateT.run, mem_support_pure_iff] at hr
        subst r
        cases hp : st.1.1.data.pads p <;> simpa only [padStep, hp] using h
      | _ => exact cappedCompiler_flag_sticky P seeds q s _ st h r hr
  cases h : st.2.2 with
  | false => simp
  | true => simp [sticky h]

def capOnly (st : CappedCompilerState C × Bool) : Bool := st.1.2.2

section CapSupport
attribute [local irreducible] hashTail

/-- Every backend query tags with the starting cap and never lowers that cap.
This is the cap analogue of Marks.backend_noMark, without a NoMark restriction. -/
theorem backend_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : (SpecX C).Domain) (bm : CappedCompilerState C × Bool) :
    Queries (Marks.TagIs (capOnly bm)) ((shareBackendTag capOnly P seeds q s pads t).run bm) ∧
      ∀ r ∈ support ((shareBackendTag capOnly P seeds q s pads t).run bm),
        capOnly bm ≤ capOnly r.2 := by
  have ho (t : DeferredQuery C ⊕ HiddenKey) :
      Queries (Marks.TagIs (capOnly bm)) ((ordinaryStepTag (Tag := Bool) P seeds q s pads t).run bm) ∧
        ∀ r ∈ support ((ordinaryStepTag (Tag := Bool) P seeds q s pads t).run bm), capOnly bm ≤ capOnly r.2 := by
    constructor
    · exact (Marks.queries_share (capOnly bm) .view trivial).bind fun view =>
        (Marks.queries_uniform _ (capOnly bm)).bind fun result => Queries.pure _
    · intro r hr
      simp only [ordinaryStepTag, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨view, _, result, hs, rfl⟩ := hr
      exact ordinary_cap P seeds q s pads t (merged seeds bm.1 view.1) result
        (mem_support_of_mem_support_liftComp (RunSpec C) _ _ hs)
  have hread (T : C.Term) (p : CPoint) :
      Queries (Marks.TagIs (capOnly bm)) ((readStepTag capOnly P seeds T p).run bm) ∧
        ∀ r ∈ support ((readStepTag capOnly P seeds T p).run bm), capOnly bm ≤ capOnly r.2 := by
    constructor
    · dsimp only [readStepTag, StateT.run]
      refine (Marks.queries_share (C := C) (capOnly bm) .view trivial).bind ?_
      intro view
      refine (Marks.queries_share (C := C) (capOnly bm) (.read T p (capOnly bm)) rfl).bind ?_
      intro value
      refine (Marks.queries_share (C := C) (capOnly bm) .view trivial).bind ?_
      intro view'
      refine (Marks.queries_uniform (C := C)
        (hashTail P seeds (key seeds (T, p)) (merged seeds bm.1 view.1) value
          (merge seeds bm.1.1.1.data.cache view'.1)) (capOnly bm)).bind ?_
      intro result
      exact Queries.pure _
    · intro r hr
      simp only [readStepTag, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨view, _, value, _, view', _, result, hs, rfl⟩ := hr
      have hs := mem_support_of_mem_support_liftComp (RunSpec C)
        (hashTail P seeds (key seeds (T, p)) (merged seeds bm.1 view.1) value
          (merge seeds bm.1.1.1.data.cache view'.1)) result hs
      simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hs
      obtain ⟨prefetched, _, rfl⟩ := hs
      exact le_rfl
  cases t with
  | inl t =>
    cases t with
    | inl t =>
      cases t with
      | inr k => exact ho (.inr k)
      | inl t =>
        cases t with
        | hash query =>
          simp only [shareBackendTag]
          cases hr : route seeds query with
          | none => exact ho _
          | some z => exact hread z.1 z.2
        | _ => exact ho _
    | inr mark =>
      refine ⟨Queries.pure _, ?_⟩
      intro r hr
      simp only [shareBackendTag, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact le_rfl
  | inr t =>
    rcases t with ⟨p, target⟩
    by_cases hp : Constrained p
    · simp only [shareBackendTag, hp, dite_true, StateT.run]
      refine ⟨(Marks.queries_share (capOnly bm) (.complete ⟨p, hp⟩ target (capOnly bm)) rfl).bind
        (fun _ => Queries.pure _), ?_⟩
      intro r hr
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      exact le_rfl
    · simp only [shareBackendTag, hp, dite_false, StateT.run]
      refine ⟨Queries.pure _, ?_⟩
      intro r hr
      simp only [mem_support_pure_iff] at hr
      subst r
      exact le_rfl


def capJointRun {α : Type} (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : OracleComp (SpecX C) α)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) :=
  (simulateQ H ((simulateQ (shareBackendTag capOnly P seeds q s pads) oa).run bm)).run sh

/-- Recorded cap tags lie below the current cap throughout any source program. -/
theorem capJoint_tagLe {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (oa : OracleComp (SpecX C) α) (bm : CappedCompilerState C × Bool) (sh : ShareState C)
    (h : Marks.TagLe (capOnly bm) sh)
    (z : (α × (CappedCompilerState C × Bool)) × ShareState C)
    (hz : z ∈ support (capJointRun (Marks.handler τ draw finish) P seeds q s pads oa bm sh)) :
    Marks.TagLe (capOnly z.1.2) z.2 := by
  induction oa using OracleComp.inductionOn generalizing bm sh with
  | pure a =>
    simp only [capJointRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact h
  | query_bind t next ih =>
    simp only [capJointRun, simulateQ_bind, StateT.run_bind,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      mem_support_bind_iff] at hz
    obtain ⟨mid, hm, hz⟩ := hz
    have hs := backend_cap P seeds q s pads t bm
    have he := hs.2 mid.1 (Marks.mem_support_of_simulate_run _ _ _ hm)
    have ht := Marks.simulate_tagLe τ draw finish (capOnly bm) _ hs.1 sh h mid hm
    exact ih mid.1.1 mid.1.2 mid.2 (ht.mono he) hz

end CapSupport


def BadCap (bad : Option (SigningShareLazy.FrozenBad (Bool × Bool))) : Prop :=
  ∃ m k, bad = some ((m, true), k)

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.capJoint_tagLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capJoint_tagLe

end ThresholdLeanXmssSecurity.SigningCompilerShareCap
