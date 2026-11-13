import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareCap
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Source

/-! # The share run of the O1 source

`compilerRunPadsO1_eq_lazy` states that the O1 source with fixed hidden labels and eager private
pads is equal, as a program, to the first component of the O1 source over the lazy share backend
with the cap tag.
The proof follows `SigningCompilerShare.compilerRunPads_eq_shareRun`. The tag drops by the retag
lemmas of `SigningCompilerShareTag`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Share
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareCap
open SigningCompilerO1SourceProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

section Share
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The O1 source over the share backend, with the complete compiler outcome. -/
def shareRunTagO1 {Tag : Type} (tagOf : CappedCompilerState C × Bool → Tag) :
    OracleComp (RunSpecT C Tag) (CompilerOutcomeO1 C) := do
  let result ← (simulateQ (shareBackendTag tagOf x.1 x.2.1 q s pads)
    (sourceProgramO1X prims A x)).run (((compilerInit, 0), fun _ => none, false), false)
  let view ← shareQueryTag (C := C) .view
  pure (result.1, merged x.2.1 result.2.1 view.1)

/-- The O1 source with lazy shares and the cap tag. -/
def lazyRunCO1 (τ : CPoint → Digest) :
    ProbComp (CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) :=
  (simulateQ (lazyHandlerTag τ) (shareRunTagO1 prims A x q s pads capTag)).run SigningShareLazy.init

/-- The O1 source with fixed hidden labels and eager private pads. -/
def compilerRunPadsO1 : ProbComp (CompilerOutcomeO1 C) :=
  compilerProgramPads x.1 x.2.1 q s pads (sourceProgramO1 prims A x)
    ((compilerInit, 0), fun _ => none, false)

end Share

attribute [local irreducible] sourceProgramO1X sourceProgramO1 sourceGameO1X sourceGameO1

/-- A tag map after the tag of the backend is a retag of the run. -/
theorem shareRunTagO1_retag {Tag Tag' : Type} (f : Tag → Tag')
    (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    shareRunTagO1 prims A x q s pads (f ∘ tagOf) =
      simulateQ (retag f) (shareRunTagO1 prims A x q s pads tagOf) := by
  simp only [shareRunTagO1, simulateQ_bind, simulateQ_pure, retag_view]
  rw [simulateQ_StateT_compose _ _ _ (shareBackendTag_retag f tagOf x.1 x.2.1 q s pads)]
  rfl

/-- The lazy run of the untagged O1 share run is the share program of the O1 source. -/
theorem shareRunO1_final (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) :
    Prod.fst <$> (simulateQ (lazyHandler τ) (shareRunTagO1 prims A x q s pads Prod.snd)).run
      (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) =
      projectResult x.2.1 <$> runShareProgram x.1 x.2.1 q s pads τ
        (sourceProgramO1X prims A x) (((compilerInit, 0), fun _ => none, false), false)
        (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
  change Prod.fst <$> (simulateQ (lazyHandler τ) (do
      let result ← (simulateQ (shareBackend x.1 x.2.1 q s pads)
        (sourceProgramO1X prims A x)).run (((compilerInit, 0), fun _ => none, false), false)
      let view ← shareQuery (C := C) .view
      pure (result.1, merged x.2.1 result.2.1 view.1))).run
        (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) = _
  simp only [runShareProgram, simulateQ_bind, StateT.run_bind, lazy_view_run, map_pure,
    bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

section Share
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The pad run is the lazy share run. It is `compilerRunPads_eq_shareRun` for the O1 source. -/
theorem compilerRunPadsO1_eq_lazy (hinj : Function.Injective x.2.1) (τ : CPoint → Digest) :
    compilerRunPadsO1 prims A x q s pads = Prod.fst <$> lazyRunCO1 prims A x q s pads τ := by
  have htag := lazyRun_retag (C := C) (Tag := Bool × Bool) Prod.fst τ
    (shareRunTagO1 prims A x q s pads capTag) SigningShareLazy.init
  rw [← shareRunTagO1_retag] at htag
  have hsnd : (Prod.fst ∘ capTag : CappedCompilerState C × Bool → Bool) = Prod.snd := rfl
  rw [hsnd] at htag
  have hfst : Prod.fst <$> lazyRunCO1 prims A x q s pads τ =
      Prod.fst <$> (simulateQ (lazyHandler τ) (shareRunTagO1 prims A x q s pads Prod.snd)).run
        (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
    change _ = Prod.fst <$> (simulateQ (lazyHandlerTag τ)
      (shareRunTagO1 prims A x q s pads Prod.snd)).run
        (mapBad (Tag := Bool × Bool) Prod.fst SigningShareLazy.init)
    rw [htag, Functor.map_map]
    rfl
  rw [hfst, shareRunO1_final, compilerRunPadsO1, sourceProgramO1_eq_expand,
    compilerProgramPads_ordinary]
  have hi : Inv x.2.1 (((compilerInit, 0), fun _ => none, false), false)
      (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
    constructor
    · intro query z hz
      rfl
    · simp [DoneCached, SigningShareLazy.init]
  simpa only [merged_init] using program_eq_of_steps x.1 x.2.1 q s pads τ
    (step_law x.1 x.2.1 hinj q s pads τ) (sourceProgramO1X prims A x)
    (sourceProgramO1X_allowed prims A x) _ _ hi

end Share

end ThresholdLeanXmssSecurity.SigningCompilerO1Share

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Share.compilerRunPadsO1_eq_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Share.compilerRunPadsO1_eq_lazy
