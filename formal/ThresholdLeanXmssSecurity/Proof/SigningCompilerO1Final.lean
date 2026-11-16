import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Coupled
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Events
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Runs
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealLog

/-! # The real event over fixed tables

- `realRun_mem_traceRun` states that each outcome of the real run over fixed tables is an outcome
  of the trace run.
- `realRun_flag` states that the flag of the result of the real run is the flag of its final state.
- `real_le_table` bounds the real event with a count of at most `q` by the good compiler event, an
  early cap with the flag up, or a share failure with a false tag. It applies `run_coupled`.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Final
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Tail SigningCompilerO1Events SigningCompilerO1Runs SigningCompilerO1Tables
variable {C : Committee}
attribute [local instance] Classical.propDecidable

section Share
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

set_option linter.constructorNameAsVariable false in
/-- Each outcome of the real run over fixed tables is an outcome of the trace run. -/
theorem realRun_mem_traceRun (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (r : SigningLaneUnionProof.TraceOutcome C)
    (hr : r ∈ support (realRun prims A x s pads (gOf s pads u) rest noise)) :
    r ∈ support (SigningLaneUnionProof.traceRun prims A x) := by
  rw [OracleComp.support_eq_of_evalDistEq (traceRun_eq_realRun prims A x hkeys),
    mem_support_bind_iff]
  refine ⟨s, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨pads, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨u, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨rest, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨noise, by simp, ?_⟩
  with_reducible exact hr

set_option maxRecDepth 100000 in
/-- The flag of the result of the real run over fixed tables is the flag of its final state. -/
theorem realRun_flag (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (r : SigningLaneUnionProof.TraceOutcome C)
    (hr : r ∈ support (realRun prims A x s pads (gOf s pads u) rest noise)) :
    r.1.1.1.2 = r.2.2.1.2 :=
  SigningCompilerO1RealLog.traceRun_flag prims x A r
    (realRun_mem_traceRun prims A x s pads hkeys u rest noise r hr)

set_option maxRecDepth 100000 in
/-- For fixed tables, the real event with a count of at most `q` costs at most the good compiler
event, an early cap with the flag up, or a share failure with a false tag. -/
theorem real_le_table (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) :
    Pr{let z ←
        realRun prims A x s pads (gOf s pads u) rest noise}[RealEvent prims x z ∧ (SigningLaneUnionProof.observed z).2.1 ≤ q] ≤
      Pr{let z ←
        eagerRunTagTO1 prims A x q s pads (NoFalse.tau s pads) (gOf s pads u) noise rest}[CompGood x q z.1 ∨ (z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z) ∨ NullBad z.2] := by
  have hreal : realRun prims A x s pads (gOf s pads u) rest noise =
      Prod.fst <$> realRunRaw prims A x s pads (gOf s pads u) rest noise := rfl
  have hcomp : eagerRunTagTO1 prims A x q s pads (NoFalse.tau s pads) (gOf s pads u) noise rest =
      SigningCompilerShareTables.finish x.2.1 <$>
        (simulateQ (compBackend x q s pads u rest noise) (sourceProgramO1X prims A x)).run
          SigningCompilerShareTables.initial := rfl
  calc _ = Pr{let z ← realRun prims A x s pads (gOf s pads u) rest noise}[(RealEvent prims x z ∧ (SigningLaneUnionProof.observed z).2.1 ≤ q) ∧
          z.1.1.1.2 = z.2.2.1.2] :=
        prEvent_congr_of_support _ _ _ (fun z hz =>
          ⟨fun h => ⟨h, realRun_flag prims A x s pads hkeys u rest noise z hz⟩, And.left⟩)
    _ ≤ _ := by
      rw [hreal, hcomp, prEvent_map, prEvent_map]
      refine prEvent_le_of_relTriple
        (SigningCompilerO1Coupled.run_coupled prims x q s pads u rest noise A hkeys) ?_
      rintro z c hrel ⟨⟨hE, hq⟩, hfl⟩
      by_cases hstop : Stop c.2
      · rcases hstop with hnull | ⟨hcap, hbad⟩
        · exact Or.inr (Or.inr hnull)
        · cases hh : c.1.2.base.hiddenFlag
          · exact Or.inl ⟨hh, Or.inl hcap⟩
          · refine Or.inr (Or.inl ⟨hh, ?_⟩)
            rcases hbad with hb | hb
            · exact Or.inl ⟨hb, hcap⟩
            · exact Or.inr hb
      · rcases hrel with hstopReal | hstopComp | ⟨source, wrapper, hf⟩
        · rcases hstopReal with hflag | hcount
          · have h1 : (false : Bool) = true :=
              (hE.1 : z.1.1.1.1.2 = false).symm.trans (hfl.trans hflag)
            exact absurd h1 (by decide)
          · exact absurd hq (not_le.mpr hcount)
        · exact absurd hstopComp hstop
        · exact Or.inl ((compGood_withReveal x q c source wrapper).mp
            (final_event prims x q s pads u rest noise hkeys z _ hf hstop hE hq))

end Share

end ThresholdLeanXmssSecurity.SigningCompilerO1Final

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Final.realRun_mem_traceRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Final.realRun_mem_traceRun

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Final.realRun_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Final.realRun_flag

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Final.real_le_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Final.real_le_table
