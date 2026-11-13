import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame

/-! # The complete runs of the O1 coupling

`simulateQ_run_fuse` states that a simulation over a simulation is the fused simulation, with the
final state pair in the order of the two runs. `realRunRaw_fused` states that the raw real run is
the joint game over the fused real world and the fused forger oracles, with the carried state read
from the fused state. `forger_sync` states that the forger phase of both sides keeps the boundary
relation with the fixed pads until a stop, from the contract of each oracle call.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Run
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

/-- A simulation over a simulation is the fused simulation. The final states come back as a pair
in the order of the two runs. -/
theorem simulateQ_run_fuse {ι κ : Type} {spec : OracleSpec ι} {mid : OracleSpec κ}
    {σ₁ σ₂ α : Type} (inner : QueryImpl spec (StateT σ₁ (OracleComp mid)))
    (outer : QueryImpl mid (StateT σ₂ ProbComp)) (oa : OracleComp spec α) (s : σ₁) (c : σ₂) :
    (simulateQ outer ((simulateQ inner oa).run s)).run c =
      (fun w => ((w.1, w.2.1), w.2.2)) <$>
        (simulateQ (SigningCompilerUntil.fuse inner outer) oa).run (s, c) := by
  rw [← simulateQ_fuse, Functor.map_map]
  exact (id_map _).symm

section Run
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The raw real run is the joint game over the fused real world. -/
theorem realRunRaw_fused (A : TsigAdversary C) :
    realRunRaw prims A x s pads (gOf s pads u) rest noise =
      (fun z => ((z.1, z.2.1), z.2.2)) <$>
        (SigningJointEagerProof.jointGameWith A x
          (SigningCompilerUntil.fuse (rawTraceWorld prims x) (realImpl x (gOf s pads u) rest))
          (fun dealt => SigningCompilerUntil.fuse
            (rawTraceFlatWith prims x (openingOracles x dealt)) (realImpl x (gOf s pads u) rest))
          (StateT.mk fun st => pure (st.1.2, st))).run (realInit x s pads noise) := by
  unfold realRunRaw rawTraceProgram rawTraceGame SigningJointEagerProof.jointGameWith realInit
  rw [← QueryImpl.simulateQ_compose]
  change (simulateQ (realImpl x (gOf s pads u) rest) _).run _ = _
  simp only [StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind, simulateQ_run_fuse,
    bind_map_left]
  refine bind_congr fun ⟨r, st, c⟩ => ?_
  rcases r with _ | (top | tree)
  · simp
  · simp only [StateT.run_bind, simulateQ_bind, map_bind, simulateQ_run_fuse, bind_map_left]
    refine bind_congr fun ⟨a, st', c'⟩ => ?_
    simp only [StateT.run_mk, simulateQ_pure, StateT.run_pure, pure_bind, map_pure]
  · simp

/-- The forger phase of both sides, from the contract of each oracle call. -/
theorem forger_sync (top : TopTree)
    (hstep : ∀ t, StepO1' prims x q s pads u rest noise top t) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : RealStop q a ∨ Stop b.2 ∨
      (SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)) :
    RelTriple ((simulateQ (realOracles prims x s pads u rest top) oa).run a)
      ((simulateQ (compOracles prims x q s pads u rest noise top) oa).run b)
      (Until (RealStop q) CompStop (fun a b =>
        SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)) :=
  relTriple_simulateQ_until _ _ (RealStop q) CompStop _
    (fun t st h r hr => realStop_adv prims x _ _ rest q t st h r hr)
    (fun t st h r hr => fuse_stop _ _
      (fun t' st' h' r' hr' => backendT_stop _ _ _ q s pads _ _ noise rest t' st' h' r' hr')
      t st h r hr)
    (fun t a b hs ha hb => hstep t a b hs ha hb) oa a b hs

end Run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Run.simulateQ_run_fuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_run_fuse

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Run.realRunRaw_fused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRunRaw_fused

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Run.forger_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forger_sync

end ThresholdLeanXmssSecurity.SigningCompilerO1Run
