import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareNoFalse

/-! # Guarded full-outcome equality for the constrained share table

The fixed-pad compiler and the eager constrained table have the same law on
events where the original source hidden flag is false. The full compiler
outcome, including the source state, backend, trace and query count, is retained.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShare.Guarded
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The eager interpreter exposes its complete compiler outcome. -/
def compilerRunTable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (g : C.Term × CPoint → HashOutput) : ProbComp (CompilerOutcome C) :=
  Prod.fst <$> Table.eagerRun prims A x q s pads (NoFalse.tau s pads) g

theorem eagerHandler_eq_handler (τ : CPoint → SigningShareLazy.Digest)
    (g : C.Term × CPoint → SigningShareLazy.HashOutput) :
    Table.eagerHandler τ g = Marks.handler τ (fun y => pure (g y))
      (fun b p _ _ => pure (g (b, p))) := rfl

/-- The frozen first-bad law transfers false-tag exclusion without lucky. -/
theorem tableRun_falseBad_zero (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (k : SigningShareLazy.Kind) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some (false, k) |
      Table.tableRun prims A x q s pads (NoFalse.tau s pads)] = 0 := by
  rw [← Table.firstbad_law]
  exact NoFalse.lazyRun_falseBad_zero prims A x hinj q s pads k

private theorem noBad_of_tags (z : CompilerOutcome C × ShareState C)
    (hfalse : ∀ k, (SigningShareLazy.erase z.2).bad ≠ some (false, k))
    (htrue : ∀ k l, z.2.bad = some (true, k, l) → z.1.1.2.hiddenFlag = true)
    (hf : z.1.1.2.hiddenFlag = false) : z.2.bad = none := by
  cases hb : z.2.bad with
  | none => rfl
  | some r =>
      rcases r with ⟨g, k, l⟩
      cases g with
      | false => exact (hfalse k (by simp only [SigningShareLazy.erase, hb, Option.map_some])).elim
      | true => have ht := htrue k l hb; simp only [hf, Bool.false_eq_true] at ht

/-- A lazy outcome with the original hidden flag down has no first bad. -/
theorem lazyRun_hidden_nonbad (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (z : CompilerOutcome C × ShareState C)
    (hz : z ∈ support (Table.lazyRun prims A x q s pads (NoFalse.tau s pads)))
    (hf : z.1.1.2.hiddenFlag = false) : z.2.bad = none := by
  apply noBad_of_tags z ?_ ?_ hf
  · intro k
    exact (probEvent_eq_zero_iff.mp
      (NoFalse.lazyRun_falseBad_zero prims A x hinj q s pads k)) z hz
  · intro k l hb
    exact Marks.shareRun_tagTrue prims A x q s pads (NoFalse.tau s pads)
      (fun _ => $ᵗ SigningShareLazy.HashOutput) Witness.lazyFinish z hz k l hb

/-- Every supported eager-table true tag entails the original final hidden flag. -/
theorem tableRun_tagTrue (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) (z : CompilerOutcome C × ShareState C)
    (hz : z ∈ support (Table.tableRun prims A x q s pads τ))
    (k : SigningShareLazy.Kind) (l : Bool) (hb : z.2.bad = some (true, k, l)) :
    z.1.1.2.hiddenFlag = true := by
  simp only [Table.tableRun, mem_support_bind_iff] at hz
  obtain ⟨u, _, hz⟩ := hz
  let g := SigningShareLazy.fiberTable C.terms τ
    (SigningShareLazy.init : Table.FrozenState C) u
  exact Marks.shareRun_tagTrue prims A x q s pads τ (fun y => pure (g y))
    (fun b p _ _ => pure (g (b, p))) z hz k l hb

/-- A supported eager-table outcome with the original flag down has no first bad. -/
theorem tableRun_hidden_nonbad (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (z : CompilerOutcome C × ShareState C)
    (hz : z ∈ support (Table.tableRun prims A x q s pads (NoFalse.tau s pads)))
    (hf : z.1.1.2.hiddenFlag = false) : z.2.bad = none := by
  apply noBad_of_tags z ?_ ?_ hf
  · intro k
    exact (probEvent_eq_zero_iff.mp (tableRun_falseBad_zero prims A x hinj q s pads k)) z hz
  · exact tableRun_tagTrue prims A x q s pads (NoFalse.tau s pads) z hz

/-- The exact guarded joint law of the original fixed-pad compiler and its fiber table. -/
theorem compilerRunPads_hidden_eq_table (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hinj : Function.Injective x.2.1) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (E : CompilerOutcome C → Prop) :
    Pr[fun o => E o ∧ o.1.2.hiddenFlag = false | compilerRunPads prims A x q s pads] =
    Pr[fun o => E o ∧ o.1.2.hiddenFlag = false | do
      let u ← $ᵗ (C.Term × CPoint → HashOutput)
      compilerRunTable prims A x q s pads
        (SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads)
          (SigningShareLazy.init : Table.FrozenState C) u)] := by
  let G : CompilerOutcome C × Table.FrozenState C → Prop :=
    fun w => E w.1 ∧ w.1.1.2.hiddenFlag = false
  have hl :
      Pr[fun z => E z.1 ∧ z.1.1.2.hiddenFlag = false |
        Table.lazyRun prims A x q s pads (NoFalse.tau s pads)] =
      Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
        Table.lazyRun prims A x q s pads (NoFalse.tau s pads)] := by
    apply probEvent_congr' ?_ rfl
    intro z hz
    exact ⟨fun h => ⟨h, lazyRun_hidden_nonbad prims A x hinj q s pads z hz h.2⟩, And.left⟩
  have ht :
      Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
        Table.tableRun prims A x q s pads (NoFalse.tau s pads)] =
      Pr[fun z => E z.1 ∧ z.1.1.2.hiddenFlag = false |
        Table.tableRun prims A x q s pads (NoFalse.tau s pads)] := by
    apply probEvent_congr' ?_ rfl
    intro z hz
    exact ⟨And.left, fun h => ⟨h, tableRun_hidden_nonbad prims A x hinj q s pads z hz h.2⟩⟩
  rw [compilerRunPads_eq_shareRun prims A x hinj q s pads (NoFalse.tau s pads),
    probEvent_map]
  change Pr[fun z => E z.1 ∧ z.1.1.2.hiddenFlag = false |
    Table.lazyRun prims A x q s pads (NoFalse.tau s pads)] = _
  rw [hl, Table.nonbad_law, ht]
  simp only [Table.tableRun, compilerRunTable, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]

end ThresholdLeanXmssSecurity.SigningCompilerShare.Guarded

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Guarded.tableRun_hidden_nonbad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Guarded.tableRun_hidden_nonbad

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Guarded.compilerRunPads_hidden_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Guarded.compilerRunPads_hidden_eq_table
