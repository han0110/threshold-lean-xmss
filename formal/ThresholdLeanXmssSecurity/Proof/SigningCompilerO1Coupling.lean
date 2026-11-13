import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Events
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Cap
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Guarded
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealLog
import ThresholdLeanXmssSecurity.Proof.SigningCompilerPotential
import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Final
import ThresholdLeanXmssSecurity.Proof.HiddenCore

/-! # The O1 compiler coupling for each cap

`compilerCouplingAny` couples the real trace run and the O1 compiler run for each cap `q`. The real
run over sampled tables costs at most the eager table run for fixed tables. The table run splits on
the hidden-key flag. With the flag down, its good event is the good event of the pad run. With the
flag up, its early cap costs at most the cap of the pad run. A share failure with a false tag has
probability zero.

`compilerCouplingO1_of_any` gives `CompilerCouplingO1`, and `hiddenCoreAt` gives `HiddenCoreAt` from
it. `signingSecurityClosed` is the signing claim.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Coupling
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Tables SigningCompilerO1Runs
open SigningCompilerO1Share SigningCompilerO1Guarded SigningCompilerO1Cap
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable


/-- The event of the compiler run that the coupling gives. With the hidden-key flag down it is the
cap flag or the lane 2 event. With the flag up it is the cap flag alone. -/
def GuardedCompilerEvent (x : Keys3 C) (q : ℕ) (r : CompilerOutcomeO1 C) : Prop :=
  (r.1.2.base.hiddenFlag = false ∧ (r.2.2.2 = true ∨ compilerEvent x.1 q r.2.1)) ∨
    (r.1.2.base.hiddenFlag = true ∧ r.2.2.2 = true)

/-- The O1 coupling for each cap `q`, with the count in the event and with no budget premise. -/
def CompilerCouplingAny (prims : Primitives) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    Pr[fun z => (SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
      SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
      (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
        SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z)) ∧
      (SigningLaneUnionProof.observed z).2.1 ≤ q |
      SigningLaneUnionProof.traceRun prims A x] ≤
        Pr[GuardedCompilerEvent x q | compilerRunO1 prims A x q]

/-- A pointwise bound of two continuations bounds the two binds. -/
private theorem probEvent_bind_le_bind {α β γ : Type} (oa : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (P : β → Prop) (Q : γ → Prop) (h : ∀ a, Pr[P | f a] ≤ Pr[Q | g a]) :
    Pr[P | oa >>= f] ≤ Pr[Q | oa >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

/-- Disjoint events add exactly. This lemma is a port of the private
`SigningCompilerShareCap.probEvent_or_eq`. -/
private theorem probEvent_or_eq {α : Type} (oa : ProbComp α) (P Q : α → Prop)
    (disjoint : ∀ z, P z → Q z → False) :
    Pr[fun z => P z ∨ Q z | oa] = Pr[P | oa] + Pr[Q | oa] := by
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro z
  by_cases hp : P z <;> by_cases hq : Q z <;> simp_all

/-- For fixed hidden labels and pads, the right event of `real_le_table` over the table run costs at
most the guarded event of the pad run. -/
theorem tableRunCO1_le_guarded (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (hinj : Function.Injective x.2.1) :
    Pr[fun z => CompGood x q z.1 ∨ (z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z) ∨ NullBad z.2 |
        tableRunCO1 prims A x q s pads (NoFalse.tau s pads)] ≤
      Pr[GuardedCompilerEvent x q | compilerRunPadsO1 prims A x q s pads] := by
  let t := tableRunCO1 prims A x q s pads (NoFalse.tau s pads)
  let p := compilerRunPadsO1 prims A x q s pads
  let E : CompilerOutcomeO1 C → Prop := fun o => o.2.2.2 = true ∨ compilerEvent x.1 q o.2.1
  have hgood : Pr[fun z => CompGood x q z.1 | t] =
      Pr[fun o => E o ∧ o.1.2.base.hiddenFlag = false | p] := by
    rw [compilerRunPadsO1_hidden_eq_table prims A x q s pads hinj E]
    exact probEvent_ext fun z _ => And.comm
  have hnull : Pr[fun z => NullBad z.2 | t] = 0 :=
    tableRunCO1_falseTag_zero prims A x q s pads hinj
  have hguard : Pr[GuardedCompilerEvent x q | p] =
      Pr[fun o => E o ∧ o.1.2.base.hiddenFlag = false | p] +
        Pr[fun o => o.1.2.base.hiddenFlag = true ∧ o.2.2.2 = true | p] := by
    rw [← probEvent_or_eq]
    · exact probEvent_ext fun o _ => by
        simp only [GuardedCompilerEvent, E, and_comm]
    · intro o h1 h2
      rw [h1.2] at h2
      exact Bool.false_ne_true h2.1
  calc _ ≤ Pr[fun z => CompGood x q z.1 | t] +
        Pr[fun z => (z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z) ∨ NullBad z.2 | t] :=
          probEvent_or_le _ _ _
    _ ≤ Pr[fun z => CompGood x q z.1 | t] +
        (Pr[fun z => z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z | t] +
          Pr[fun z => NullBad z.2 | t]) := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := by
      rw [hgood, hnull, add_zero, hguard]
      exact add_le_add le_rfl (tableRunCO1_capEarly_le prims A x q s pads hinj)

/-- The O1 coupling for each cap. -/
theorem compilerCouplingAny (prims : Primitives) : CompilerCouplingAny (C := C) prims := by
  intro A q x _ hkeys
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (traceRun_eq_realRun prims A x hkeys),
    probEvent_congr' (fun _ _ => Iff.rfl) (compilerRunO1_eq_padTable prims A x q)]
  refine probEvent_bind_le_bind _ _ _ _ _ fun s => ?_
  refine probEvent_bind_le_bind _ _ _ _ _ fun pads => ?_
  refine le_trans ?_ (tableRunCO1_le_guarded prims A x q s pads hinj)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (tableRunCO1_eq_tables prims A x q s pads hkeys _)]
  refine probEvent_bind_le_bind _ _ _ _ _ fun u => ?_
  refine le_of_le_of_eq ?_ (probEvent_bind_bind_swap ($ᵗ (RestSlot C → HashOutput))
    ($ᵗ (ChainNoiseIndex → HashOutput)) (fun rest noise =>
      eagerRunTagTO1 prims A x q s pads (NoFalse.tau s pads) (gOf s pads u) noise rest) _)
  refine probEvent_bind_le_bind _ _ _ _ _ fun rest => ?_
  refine probEvent_bind_le_bind _ _ _ _ _ fun noise => ?_
  exact SigningCompilerO1Final.real_le_table prims A x q s pads hkeys u rest noise

set_option maxRecDepth 100000 in
/-- The present open input follows from the form for each cap. -/
theorem compilerCouplingO1_of_any (prims : Primitives) (h : CompilerCouplingAny (C := C) prims) :
    CompilerCouplingO1 (C := C) prims := by
  intro A q x hx hkeys hq _
  refine le_trans (probEvent_mono fun z hz hE => ?_)
    ((h A q x hx hkeys).trans (probEvent_mono fun r _ hr => ?_))
  · exact ⟨hE, SigningLaneUnionProof.traceRun_count_le prims A q x hq z hz⟩
  · rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
    · exact hr
    · exact Or.inl hr

/-- For fixed distinct keys, a win without the flag costs at most `signingHashError q`. -/
theorem hiddenCoreAt (prims : Primitives) (C : Committee) : SigningCoreProof.HiddenCoreAt prims C :=
  SigningLaneFinal.hiddenCoreAt_of_laneTraceCap prims
    (laneTraceCap_of_compilerO1 prims (SigningCompilerPotential.compilerPotentialStep prims)
      (compilerCouplingO1_of_any prims (compilerCouplingAny prims)))

end ThresholdLeanXmssSecurity.SigningCompilerO1Coupling

namespace ThresholdLeanXmssSecurity

/-- The signing claim, with no open input. -/
theorem signingSecurityClosed (prims : Primitives) (C : Committee) :
    SigningSecurityStatement prims C :=
  signingSecurityFull prims C (SigningCompilerO1Coupling.hiddenCoreAt prims C)

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.tableRunCO1_le_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.tableRunCO1_le_guarded

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.compilerCouplingAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.compilerCouplingAny

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.compilerCouplingO1_of_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.compilerCouplingO1_of_any

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.hiddenCoreAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Coupling.hiddenCoreAt

/-- info: 'ThresholdLeanXmssSecurity.signingSecurityClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.signingSecurityClosed
