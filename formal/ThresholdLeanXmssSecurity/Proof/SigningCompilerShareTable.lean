import ThresholdLeanXmssSecurity.Proof.SigningCompilerShare

/-!
# The signing compiler's eager fiber table

The lazy and eager share interpreters have the same full outcome law before
bad, and the same first-bad tag and kind. Only the lucky bit is erased.
The target function is arbitrary. The laws specialize the frozen-state
coupling and implementation erasure laws of `SigningShareLazy`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningCompilerShare.Table

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof

variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev FrozenState (C : Committee) :=
  SigningShareLazy.ShareState C.Term CPoint (SigningShareLazy.FrozenBad Bool)

def lazyRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) : ProbComp (CompilerOutcome C × ShareState C) :=
  (simulateQ (lazyHandler τ) (shareRun prims A x q s pads)).run SigningShareLazy.init

def eagerHandler (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp) :=
  SigningShareLazy.unifImpl (ShareState C) +
    SigningShareLazy.eagerImpl (Tag := Bool) C.terms τ g

def eagerRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    ProbComp (CompilerOutcome C × ShareState C) :=
  (simulateQ (eagerHandler τ g) (shareRun prims A x q s pads)).run SigningShareLazy.init

def tableRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) : ProbComp (CompilerOutcome C × ShareState C) := do
  let u ← $ᵗ (C.Term × CPoint → HashOutput)
  eagerRun prims A x q s pads τ
    (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenState C) u)

@[simp] theorem erase_init :
    SigningShareLazy.erase (SigningShareLazy.init : ShareState C) =
      (SigningShareLazy.init : FrozenState C) := rfl

private theorem initial_good (τ : CPoint → Digest) :
    SigningShareLazy.Good C.terms τ (SigningShareLazy.init : FrozenState C) := by
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.good_init C.terms τ (Or.inl (List.ne_nil_of_mem (mem_terms T)))

private theorem frozen_law (τ : CPoint → Digest) {α : Type}
    (oa : OracleComp (RunSpec C) α) :
    𝒟[(simulateQ (SigningShareLazy.unifImpl (FrozenState C) +
      SigningShareLazy.lazyFrozen (Tag := Bool) C.terms τ) oa).run SigningShareLazy.init] =
    𝒟[do let u ← $ᵗ (C.Term × CPoint → HashOutput)
         (simulateQ (SigningShareLazy.unifImpl (FrozenState C) +
           SigningShareLazy.eagerFrozen (Tag := Bool) C.terms τ
             (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenState C) u))
           oa).run SigningShareLazy.init] :=
  SigningShareLazy.lazyFrozen_eq_eagerFrozen C.terms terms_nodup mem_terms τ oa
    SigningShareLazy.init (initial_good τ)

/-- Equality of every full-outcome event before the first bad occurrence. -/
theorem nonbad_law (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (G : CompilerOutcome C × FrozenState C → Prop) :
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      lazyRun prims A x q s pads τ] =
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      tableRun prims A x q s pads τ] := by
  unfold lazyRun lazyHandler
  rw [SigningShareLazy.lazyImpl_frozen_nonbad, erase_init]
  trans Pr[fun z => G z ∧ z.2.bad = none | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (FrozenState C) +
      SigningShareLazy.eagerFrozen (Tag := Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenState C) u))
      (shareRun prims A x q s pads)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_law τ _)
  · unfold tableRun
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_nonbad C.terms τ _
      (shareRun prims A x q s pads) SigningShareLazy.init G).symm

/-- The first-bad law retains its tag and kind and forgets only lucky. -/
theorem firstbad_law (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (r : SigningShareLazy.FrozenBad Bool) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      lazyRun prims A x q s pads τ] =
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      tableRun prims A x q s pads τ] := by
  unfold lazyRun lazyHandler
  rw [SigningShareLazy.lazyImpl_frozen_firstbad, erase_init]
  trans Pr[fun z => z.2.bad = some r | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (FrozenState C) +
      SigningShareLazy.eagerFrozen (Tag := Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenState C) u))
      (shareRun prims A x q s pads)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_law τ _)
  · unfold tableRun
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_firstbad C.terms τ _
      (shareRun prims A x q s pads) SigningShareLazy.init r).symm

end ThresholdLeanXmssSecurity.SigningCompilerShare.Table

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Table.nonbad_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Table.nonbad_law

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Table.firstbad_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Table.firstbad_law
