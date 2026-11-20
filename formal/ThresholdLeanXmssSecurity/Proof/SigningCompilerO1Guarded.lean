import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1NoFalse

/-! # The pad run and the table run of the O1 source with the flag down

The table run has no first share failure with a false tag, because the first failure has the same
law in the lazy run and in the table run. A first failure with a true tag gives a final hidden flag
that is up. So a run with the flag down has no share failure.

With the flag down, the pad run and the table run give each event of the full outcome the same
probability. The statement holds for the table run with the flag tag and for the table run with the
cap tag. No first share failure of the table run with the cap tag has a false flag part.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Guarded
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareCap
open SigningCompilerO1SourceProof SigningCompilerO1Share SigningCompilerO1Tables
open SigningCompilerO1Marks SigningCompilerO1Runs SigningCompilerO1NoFalse
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] sourceProgramO1X sourceProgramO1 sourceGameO1X sourceGameO1

/-- An outcome with the flag down, no failure with a false tag, and a flag up after each failure with
a true tag has no share failure. -/
private theorem noBad_of_tagsO1 (z : CompilerOutcomeO1 C × ShareState C)
    (hfalse : ∀ k, (SigningShareLazy.erase z.2).bad ≠ some (false, k))
    (htrue : ∀ k l, z.2.bad = some (true, k, l) → z.1.1.2.base.hiddenFlag = true)
    (hf : z.1.1.2.base.hiddenFlag = false) : z.2.bad = none := by
  cases hb : z.2.bad with
  | none => rfl
  | some r =>
      rcases r with ⟨g, k, l⟩
      cases g with
      | false =>
          exact (hfalse k (by simp only [SigningShareLazy.erase, hb, Option.map_some])).elim
      | true =>
          have ht := htrue k l hb
          simp only [hf, Bool.false_eq_true] at ht

section FlagRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The table run has no first share failure with a false tag. -/
theorem tableRunO1_falseBad_zero (hinj : Function.Injective x.2.1) (k : SigningShareLazy.Kind) :
    Pr{let z ←
      tableRunO1 prims A x q s pads (NoFalse.tau s pads)}[(SigningShareLazy.erase z.2).bad = some (false, k)] = 0 := by
  rw [← firstbad_lawO1]
  exact lazyRunO1_falseBad_zero prims A x q s pads hinj k

/-- A first share failure of the table run with a true tag gives a final hidden flag that is up. -/
theorem tableRunO1_tagTrue (τ : CPoint → Digest) (z : CompilerOutcomeO1 C × ShareState C)
    (hz : z ∈ support (tableRunO1 prims A x q s pads τ))
    (k : SigningShareLazy.Kind) (l : Bool) (hb : z.2.bad = some (true, k, l)) :
    z.1.1.2.base.hiddenFlag = true := by
  simp only [tableRunO1, mem_support_bind_iff] at hz
  obtain ⟨u, _, hz⟩ := hz
  let g := SigningShareLazy.fiberTable C.terms τ
    (SigningShareLazy.init : Table.FrozenState C) u
  exact shareRunO1_tagTrue prims A x q s pads τ (fun y => pure (g y))
    (fun b p _ _ => pure (g (b, p))) z hz k l hb

/-- A lazy outcome with the flag down has no share failure. -/
theorem lazyRunO1_hidden_nonbad (hinj : Function.Injective x.2.1)
    (z : CompilerOutcomeO1 C × ShareState C)
    (hz : z ∈ support (lazyRunO1 prims A x q s pads (NoFalse.tau s pads)))
    (hf : z.1.1.2.base.hiddenFlag = false) : z.2.bad = none := by
  apply noBad_of_tagsO1 z ?_ ?_ hf
  · intro k
    exact ((OracleComp.prEvent_eq_zero_iff _ _).mp
      (lazyRunO1_falseBad_zero prims A x q s pads hinj k)) z hz
  · intro k l hb
    exact shareRunO1_tagTrue prims A x q s pads (NoFalse.tau s pads)
      (fun _ => $ᵗ SigningShareLazy.HashOutput) Witness.lazyFinish z hz k l hb

/-- A table outcome with the flag down has no share failure. -/
theorem tableRunO1_hidden_nonbad (hinj : Function.Injective x.2.1)
    (z : CompilerOutcomeO1 C × ShareState C)
    (hz : z ∈ support (tableRunO1 prims A x q s pads (NoFalse.tau s pads)))
    (hf : z.1.1.2.base.hiddenFlag = false) : z.2.bad = none := by
  apply noBad_of_tagsO1 z ?_ ?_ hf
  · intro k
    exact ((OracleComp.prEvent_eq_zero_iff _ _).mp
      (tableRunO1_falseBad_zero prims A x q s pads hinj k)) z hz
  · exact tableRunO1_tagTrue prims A x q s pads (NoFalse.tau s pads) z hz

/-- With the flag down, the pad run and the table run with the flag tag give each event the same
probability. -/
theorem compilerRunPadsO1_hidden_eq_tableO1 (hinj : Function.Injective x.2.1)
    (E : CompilerOutcomeO1 C → Prop) :
    Pr{let o ← compilerRunPadsO1 prims A x q s pads}[E o ∧ o.1.2.base.hiddenFlag = false] =
      Pr{let z ←
        tableRunO1 prims A x q s pads (NoFalse.tau s pads)}[E z.1 ∧ z.1.1.2.base.hiddenFlag = false] := by
  let G : CompilerOutcomeO1 C × Table.FrozenState C → Prop :=
    fun w => E w.1 ∧ w.1.1.2.base.hiddenFlag = false
  have hl :
      Pr{let z ←
        lazyRunO1 prims A x q s pads (NoFalse.tau s pads)}[E z.1 ∧ z.1.1.2.base.hiddenFlag = false] =
      Pr{let z ←
        lazyRunO1 prims A x q s pads (NoFalse.tau s pads)}[G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none] := by
    refine prEvent_congr_of_support _ _ _ ?_
    intro z hz
    exact ⟨fun h => ⟨h, lazyRunO1_hidden_nonbad prims A x q s pads hinj z hz h.2⟩, And.left⟩
  have ht :
      Pr{let z ←
        tableRunO1 prims A x q s pads (NoFalse.tau s pads)}[G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none] =
      Pr{let z ←
        tableRunO1 prims A x q s pads (NoFalse.tau s pads)}[E z.1 ∧ z.1.1.2.base.hiddenFlag = false] := by
    refine prEvent_congr_of_support _ _ _ ?_
    intro z hz
    exact ⟨And.left, fun h => ⟨h, tableRunO1_hidden_nonbad prims A x q s pads hinj z hz h.2⟩⟩
  rw [compilerRunPadsO1_eq_lazyO1 prims A x q s pads hinj (NoFalse.tau s pads), prEvent_map]
  change Pr{let z ←
    lazyRunO1 prims A x q s pads (NoFalse.tau s pads)}[E z.1 ∧ z.1.1.2.base.hiddenFlag = false] = _
  rw [hl, nonbad_lawO1, ht]

end FlagRuns

section CapRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- With the flag down, the pad run and the table run give each event the same probability. -/
theorem compilerRunPadsO1_hidden_eq_table (hinj : Function.Injective x.2.1)
    (E : CompilerOutcomeO1 C → Prop) :
    Pr{let o ← compilerRunPadsO1 prims A x q s pads}[E o ∧ o.1.2.base.hiddenFlag = false] =
      Pr{let z ←
        tableRunCO1 prims A x q s pads (NoFalse.tau s pads)}[E z.1 ∧ z.1.1.2.base.hiddenFlag = false] := by
  rw [compilerRunPadsO1_hidden_eq_tableO1 prims A x q s pads hinj E,
    ← tableRunCO1_project, prEvent_map]
  rfl

/-- No share failure of the table run has a false tag. -/
theorem tableRunCO1_falseTag_zero (hinj : Function.Injective x.2.1) :
    Pr{let z ←
      tableRunCO1 prims A x q s pads (NoFalse.tau s pads)}[∃ c k l, z.2.bad = some ((false, c), k, l)] = 0 := by
  apply (OracleComp.prEvent_eq_zero_iff _ _).mpr
  intro z hz hbad
  obtain ⟨c, k, l, hbad⟩ := hbad
  have hz' : projectO1 z ∈ support (tableRunO1 prims A x q s pads (NoFalse.tau s pads)) := by
    rw [← tableRunCO1_project, support_map]
    exact Set.mem_image_of_mem _ hz
  apply ((OracleComp.prEvent_eq_zero_iff _ _).mp (tableRunO1_falseBad_zero prims A x q s pads hinj k))
    (projectO1 z) hz'
  simp only [projectO1, Prod.map, mapBad, SigningShareLazy.erase, hbad, Option.map_some]

end CapRuns

end ThresholdLeanXmssSecurity.SigningCompilerO1Guarded

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunO1_falseBad_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunO1_falseBad_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunO1_tagTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunO1_tagTrue

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.lazyRunO1_hidden_nonbad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.lazyRunO1_hidden_nonbad

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunO1_hidden_nonbad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunO1_hidden_nonbad

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.compilerRunPadsO1_hidden_eq_tableO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.compilerRunPadsO1_hidden_eq_tableO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.compilerRunPadsO1_hidden_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.compilerRunPadsO1_hidden_eq_table

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunCO1_falseTag_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Guarded.tableRunCO1_falseTag_zero
