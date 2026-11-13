import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Tables

/-! # The share runs of the O1 source

This file defines the lazy, the eager and the table runs of the O1 source with the flag tag. The
runs with the cap tag are `lazyRunCO1` and `tableRunCO1`. `projectO1` forgets the cap part of the
tag, and it maps each run with the cap tag to the same run with the flag tag.

`nonbad_lawO1` and `nonbad_lawCO1` compare the lazy run with the table run. Each event of the full
outcome before the first share failure has the same probability in the two runs. `firstbad_lawO1`
and `firstbad_lawCO1` state the same for the tag and the kind of the first share failure.
`erased_bad_lawCO1` states that the erased first failure has the same law in the two runs.

The proofs follow `SigningCompilerShare.Table` and `SigningCompilerShareCap`. They treat the share
run as an opaque program.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Runs
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareCap
open SigningCompilerO1SourceProof SigningCompilerO1Share SigningCompilerO1Tables
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

section FlagRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The O1 source with lazy shares and the flag tag. -/
def lazyRunO1 (τ : CPoint → Digest) : ProbComp (CompilerOutcomeO1 C × ShareState C) :=
  (simulateQ (lazyHandler τ) (shareRunTagO1 prims A x q s pads Prod.snd)).run SigningShareLazy.init

/-- The O1 source with an eager share table and the flag tag. -/
def eagerRunO1 (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    ProbComp (CompilerOutcomeO1 C × ShareState C) :=
  (simulateQ (Table.eagerHandler τ g) (shareRunTagO1 prims A x q s pads Prod.snd)).run
    SigningShareLazy.init

/-- The O1 source with the fiber table of a uniform table and the flag tag. -/
def tableRunO1 (τ : CPoint → Digest) : ProbComp (CompilerOutcomeO1 C × ShareState C) := do
  let u ← $ᵗ (C.Term × CPoint → HashOutput)
  eagerRunO1 prims A x q s pads τ
    (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : Table.FrozenState C) u)

end FlagRuns

section CapRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- Forget the cap part of the tag of the first share failure. -/
def projectO1 (z : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) :
    CompilerOutcomeO1 C × ShareState C := Prod.map id (mapBad Prod.fst) z

/-- The cap is set before any share failure, or at the first failure. -/
def CapEarlyO1 (z : CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) : Prop :=
  (z.2.bad = none ∧ z.1.2.2.2 = true) ∨ ∃ m k l, z.2.bad = some ((m, true), k, l)

end CapRuns

/-- The initial frozen state with the flag tag is good. This lemma is a port of the private
`SigningCompilerShare.Table.initial_good`. -/
private theorem initial_good (τ : CPoint → Digest) :
    SigningShareLazy.Good C.terms τ (SigningShareLazy.init : Table.FrozenState C) := by
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.good_init C.terms τ (Or.inl (List.ne_nil_of_mem (mem_terms T)))

/-- The initial frozen state with the cap tag is good. This lemma is a port of the private
`SigningCompilerShareCap.initial_good`. -/
private theorem initial_goodC (τ : CPoint → Digest) :
    SigningShareLazy.Good C.terms τ (SigningShareLazy.init : FrozenStateC C) := by
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.good_init C.terms τ (Or.inl (List.ne_nil_of_mem (mem_terms T)))

/-- The lazy frozen run with the flag tag has the law of the fiber table run. This lemma is a port
of the private `SigningCompilerShare.Table.frozen_law`. -/
private theorem frozen_law (τ : CPoint → Digest) {α : Type}
    (oa : OracleComp (RunSpec C) α) :
    𝒟[(simulateQ (SigningShareLazy.unifImpl (Table.FrozenState C) +
      SigningShareLazy.lazyFrozen (Tag := Bool) C.terms τ) oa).run SigningShareLazy.init] =
    𝒟[do let u ← $ᵗ (C.Term × CPoint → HashOutput)
         (simulateQ (SigningShareLazy.unifImpl (Table.FrozenState C) +
           SigningShareLazy.eagerFrozen (Tag := Bool) C.terms τ
             (SigningShareLazy.fiberTable C.terms τ
               (SigningShareLazy.init : Table.FrozenState C) u))
           oa).run SigningShareLazy.init] :=
  SigningShareLazy.lazyFrozen_eq_eagerFrozen C.terms terms_nodup mem_terms τ oa
    SigningShareLazy.init (initial_good τ)

/-- The lazy frozen run with the cap tag has the law of the fiber table run. This lemma is a port
of the private `SigningCompilerShareCap.frozen_law`. -/
private theorem frozen_lawC (τ : CPoint → Digest) {α : Type}
    (oa : OracleComp (RunSpecT C (Bool × Bool)) α) :
    𝒟[(simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
      SigningShareLazy.lazyFrozen (Tag := Bool × Bool) C.terms τ) oa).run SigningShareLazy.init] =
    𝒟[do let u ← $ᵗ (C.Term × CPoint → HashOutput)
         (simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
           SigningShareLazy.eagerFrozen (Tag := Bool × Bool) C.terms τ
             (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u))
           oa).run SigningShareLazy.init] :=
  SigningShareLazy.lazyFrozen_eq_eagerFrozen C.terms terms_nodup mem_terms τ oa
    SigningShareLazy.init (initial_goodC τ)

attribute [local irreducible] sourceProgramO1X sourceProgramO1 sourceGameO1X sourceGameO1

section CapRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The lazy run with the cap tag maps to the lazy run with the flag tag. -/
theorem lazyRunCO1_project (τ : CPoint → Digest) :
    projectO1 <$> lazyRunCO1 prims A x q s pads τ = lazyRunO1 prims A x q s pads τ := by
  have h := lazyRun_retag (C := C) (Tag := Bool × Bool) Prod.fst τ
    (shareRunTagO1 prims A x q s pads capTag) SigningShareLazy.init
  rw [← shareRunTagO1_retag] at h
  exact h.symm

/-- The eager run with the cap tag maps to the eager run with the flag tag. -/
theorem eagerRunCO1_project (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    projectO1 <$> eagerRunCO1 prims A x q s pads τ g = eagerRunO1 prims A x q s pads τ g := by
  have h := eagerRun_retag (C := C) (Tag := Bool × Bool) Prod.fst τ g
    (shareRunTagO1 prims A x q s pads capTag) SigningShareLazy.init
  rw [← shareRunTagO1_retag] at h
  exact h.symm

/-- The table run with the cap tag maps to the table run with the flag tag. -/
theorem tableRunCO1_project (τ : CPoint → Digest) :
    projectO1 <$> tableRunCO1 prims A x q s pads τ = tableRunO1 prims A x q s pads τ := by
  simp only [tableRunCO1, tableRunO1, map_bind]
  congr 1
  funext u
  exact eagerRunCO1_project prims A x q s pads τ _

end CapRuns

section FlagRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The pad run is the lazy share run with the flag tag. -/
theorem compilerRunPadsO1_eq_lazyO1 (hinj : Function.Injective x.2.1) (τ : CPoint → Digest) :
    compilerRunPadsO1 prims A x q s pads = Prod.fst <$> lazyRunO1 prims A x q s pads τ := by
  rw [compilerRunPadsO1_eq_lazy prims A x q s pads hinj τ, ← lazyRunCO1_project, Functor.map_map]
  rfl

/-- This lemma compares the lazy run with the table run, both with the flag tag. Each event of the
full outcome before the first share failure has the same probability. -/
theorem nonbad_lawO1 (τ : CPoint → Digest)
    (G : CompilerOutcomeO1 C × Table.FrozenState C → Prop) :
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      lazyRunO1 prims A x q s pads τ] =
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      tableRunO1 prims A x q s pads τ] := by
  unfold lazyRunO1 lazyHandler
  rw [SigningShareLazy.lazyImpl_frozen_nonbad, Table.erase_init]
  trans Pr[fun z => G z ∧ z.2.bad = none | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (Table.FrozenState C) +
      SigningShareLazy.eagerFrozen (Tag := Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : Table.FrozenState C) u))
      (shareRunTagO1 prims A x q s pads Prod.snd)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_law τ _)
  · unfold tableRunO1
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_nonbad C.terms τ _
      (shareRunTagO1 prims A x q s pads Prod.snd) SigningShareLazy.init G).symm

/-- This lemma compares the lazy run with the table run, both with the flag tag. The tag and the
kind of the first share failure have the same probability. -/
theorem firstbad_lawO1 (τ : CPoint → Digest) (r : SigningShareLazy.FrozenBad Bool) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      lazyRunO1 prims A x q s pads τ] =
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      tableRunO1 prims A x q s pads τ] := by
  unfold lazyRunO1 lazyHandler
  rw [SigningShareLazy.lazyImpl_frozen_firstbad, Table.erase_init]
  trans Pr[fun z => z.2.bad = some r | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (Table.FrozenState C) +
      SigningShareLazy.eagerFrozen (Tag := Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : Table.FrozenState C) u))
      (shareRunTagO1 prims A x q s pads Prod.snd)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_law τ _)
  · unfold tableRunO1
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_firstbad C.terms τ _
      (shareRunTagO1 prims A x q s pads Prod.snd) SigningShareLazy.init r).symm

end FlagRuns

section CapRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- This lemma compares the lazy run with the table run, both with the cap tag. Each event of the
full outcome before the first share failure has the same probability. -/
theorem nonbad_lawCO1 (τ : CPoint → Digest)
    (G : CompilerOutcomeO1 C × FrozenStateC C → Prop) :
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      lazyRunCO1 prims A x q s pads τ] =
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      tableRunCO1 prims A x q s pads τ] := by
  unfold lazyRunCO1 lazyHandlerTag
  rw [SigningShareLazy.lazyImpl_frozen_nonbad, erase_init]
  trans Pr[fun z => G z ∧ z.2.bad = none | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
      SigningShareLazy.eagerFrozen (Tag := Bool × Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u))
      (shareRunTagO1 prims A x q s pads capTag)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_lawC τ _)
  · unfold tableRunCO1
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_nonbad C.terms τ _
      (shareRunTagO1 prims A x q s pads capTag) SigningShareLazy.init G).symm

/-- This lemma compares the lazy run with the table run, both with the cap tag. The tag and the
kind of the first share failure have the same probability. -/
theorem firstbad_lawCO1 (τ : CPoint → Digest) (r : SigningShareLazy.FrozenBad (Bool × Bool)) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      lazyRunCO1 prims A x q s pads τ] =
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      tableRunCO1 prims A x q s pads τ] := by
  unfold lazyRunCO1 lazyHandlerTag
  rw [SigningShareLazy.lazyImpl_frozen_firstbad, erase_init]
  trans Pr[fun z => z.2.bad = some r | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
      SigningShareLazy.eagerFrozen (Tag := Bool × Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u))
      (shareRunTagO1 prims A x q s pads capTag)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_lawC τ _)
  · unfold tableRunCO1
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_firstbad C.terms τ _
      (shareRunTagO1 prims A x q s pads capTag) SigningShareLazy.init r).symm

/-- The erased first share failure has the same law in the lazy run and in the table run with the
cap tag. -/
theorem erased_bad_lawCO1 (τ : CPoint → Digest) :
    𝒟[(fun z => (SigningShareLazy.erase z.2).bad) <$> lazyRunCO1 prims A x q s pads τ] =
      𝒟[(fun z => (SigningShareLazy.erase z.2).bad) <$> tableRunCO1 prims A x q s pads τ] := by
  apply evalDist_ext
  intro bad
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  cases bad with
  | none =>
    simpa [SigningShareLazy.erase, Function.comp_def] using
      nonbad_lawCO1 prims A x q s pads τ (fun _ => True)
  | some r => exact firstbad_lawCO1 prims A x q s pads τ r

end CapRuns

end ThresholdLeanXmssSecurity.SigningCompilerO1Runs

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.lazyRunCO1_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.lazyRunCO1_project

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.eagerRunCO1_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.eagerRunCO1_project

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.tableRunCO1_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.tableRunCO1_project

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.compilerRunPadsO1_eq_lazyO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.compilerRunPadsO1_eq_lazyO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.nonbad_lawO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.nonbad_lawO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.firstbad_lawO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.firstbad_lawO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.nonbad_lawCO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.nonbad_lawCO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.firstbad_lawCO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.firstbad_lawCO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Runs.erased_bad_lawCO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Runs.erased_bad_lawCO1
