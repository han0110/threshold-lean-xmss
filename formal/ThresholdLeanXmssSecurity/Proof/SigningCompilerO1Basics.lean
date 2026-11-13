import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Source
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRelease

/-! # Enumeration and base-state laws for the threshold-guarded compiler

Threshold crossings occur among the recorded keys. The first stored digit is
minimal. The base-state lens preserves monadic sequencing and the complete X
runner outcome. Eager private pads preserve the complete O1 run distribution.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Basics
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1SourceProof SigningCompilerShare SigningCompilerShareTables
open SigningCompilerSyncRelease
variable {C : Committee}
attribute [local instance] Classical.propDecidable

theorem crossed_mem (old new : TsigState C) (e : KeyIndex) (m : Message)
    (hbound : new.bound e = some m) (hcard : new.corrupt.card ≤ C.t - 1)
    (hold : (signersAt old e m).card < C.t) (hnew : C.t ≤ (signersAt new e m).card) :
    e ∈ crossedKeys old new := by
  have he : e ∈ new.released.map (·.1) := by
    by_contra hn
    have hf : (new.released.filter fun r => r.1 = e ∧ r.2.1 = m) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro r hr
      have hr' := List.mem_filter.mp hr
      exact hn (List.mem_map.mpr ⟨r, hr'.1, (of_decide_eq_true hr'.2).1⟩)
    have hs : signersAt new e m = new.corrupt := by
      unfold signersAt
      rw [hf]
      simp
    rw [hs] at hnew
    have := C.one_le_t
    omega
  simpa [crossedKeys, hbound, hold, hnew] using he

theorem firstStart_spec (S : Finset Digit) (d : Digit) (h : firstStart S = some d) :
    d ∈ S ∧ ∀ d' ∈ S, d.val ≤ d'.val := by
  have hh := List.find?_eq_some_iff_getElem.mp h
  rcases hh with ⟨hd, i, hi, hid, hbefore⟩
  refine ⟨of_decide_eq_true hd, ?_⟩
  intro d' hd'
  have hie : i = d.val := by simpa using congrArg Fin.val hid
  by_contra hn
  have hlt : d'.val < i := by omega
  have hb := hbefore d'.val hlt
  have hget : (List.finRange chainLength)[d'.val]'(by simp) = d' := by
    apply Fin.ext
    simp
  rw [hget] at hb
  have hb' : d' ∉ S := by simpa using hb
  exact hb' hd'

theorem firstStart_none_iff (S : Finset Digit) : firstStart S = none ↔ S = ∅ := by
  simp [firstStart, List.find?_eq_none, Finset.eq_empty_iff_forall_notMem]

theorem liftBase_pure {α : Type} (a : α) :
    liftBase (pure a : SourceM C α) = pure a := by
  funext st
  simp [liftBase, StateT.run_pure]

theorem liftBase_bind {α β : Type} (oa : SourceM C α) (f : α → SourceM C β) :
    liftBase (oa >>= f) = (liftBase oa >>= fun a => liftBase (f a)) := by
  funext st
  change (liftBase (oa >>= f)).run st = (liftBase oa >>= fun a => liftBase (f a)).run st
  simp [liftBase, StateT.run_bind, map_bind, bind_map_left]

theorem compilerRunO1_eq_padTable (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) :
    𝒟[compilerRunO1 prims A x q] = 𝒟[do
      let s ← $ᵗ (HiddenKey → Digest)
      let pads ← $ᵗ (Point → Digest)
      compilerProgramPads x.1 x.2.1 q s pads (sourceProgramO1 prims A x)
        ((compilerInit, 0), fun _ => none, false)] := by
  unfold compilerRunO1
  apply evalDist_bind_congr
  intro s _
  exact cappedCompiler_eq_padTable x.1 x.2.1 q s (sourceProgramO1 prims A x)
    ((compilerInit, 0), fun _ => none, false)

def runXO1 {Tag α : Type}
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (oa : SourceMXO1 C α) (src : SourceStateO1 C) (st : FullState C Tag) :
    ProbComp ((α × SourceStateO1 C) × FullState C Tag) :=
  (simulateQ backend (oa.run src)).run st

theorem runXO1_liftBaseX {Tag α : Type}
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (oa : SourceMX C α) (src : SourceStateO1 C) (st : FullState C Tag) :
    runXO1 backend (liftBaseX oa) src st =
      (fun r => ((r.1.1, { src with base := r.1.2 }), r.2)) <$> runX backend oa src.base st := by
  simp [runXO1, liftBaseX, runX, simulateQ_map, StateT.run_map]

end ThresholdLeanXmssSecurity.SigningCompilerO1Basics

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.crossed_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.crossed_mem

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.firstStart_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.firstStart_spec

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.firstStart_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.firstStart_none_iff

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.liftBase_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.liftBase_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.liftBase_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.liftBase_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.compilerRunO1_eq_padTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.compilerRunO1_eq_padTable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Basics.runXO1_liftBaseX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Basics.runXO1_liftBaseX
