import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareCap
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareGuarded

/-!
# The cap-tagged table run and the guarded table

`tableRunC_fst` shows that the cap tag does not change the outcome of the eager compiler with the table
of `Guarded.compilerRunTable`. `tableRunC_falseTag_zero` shows that a false hidden flag at the first
share failure has probability zero.

These declarations are in the namespace `SigningCompilerShareCap`. They use
`SigningCompilerShareGuarded`, and `SigningCompilerShareCap` does not import this module.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShareCap
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag

variable {C : Committee}

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The cap tag leaves the full eager compiler outcome unchanged. -/
theorem tableRunC_fst (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    𝒟[Prod.fst <$> tableRunC prims A x q s pads (NoFalse.tau s pads)] =
      𝒟[do let u ← $ᵗ (C.Term × CPoint → HashOutput)
           Guarded.compilerRunTable prims A x q s pads
             (SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads)
               (SigningShareLazy.init : Table.FrozenState C) u)] := by
  have h := congrArg (fun oa => Prod.fst <$> oa)
    (tableRunC_project prims A x q s pads (NoFalse.tau s pads))
  simp only [Functor.map_map, project, Prod.map, id_eq] at h
  rw [h]
  simp only [Table.tableRun, Guarded.compilerRunTable, map_bind]

/-- False hidden flags at the first share failure have zero mass. -/
theorem tableRunC_falseTag_zero (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    Pr[fun z => ∃ c k l, z.2.bad = some ((false, c), k, l) |
      tableRunC prims A x q s pads (NoFalse.tau s pads)] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro z hz hbad
  obtain ⟨c, k, l, hbad⟩ := hbad
  have hz' : project z ∈ support (Table.tableRun prims A x q s pads (NoFalse.tau s pads)) := by
    rw [← tableRunC_project, support_map]
    exact Set.mem_image_of_mem _ hz
  apply (probEvent_eq_zero_iff.mp (Guarded.tableRun_falseBad_zero prims A x hinj q s pads k))
    (project z) hz'
  simp only [project, Prod.map, mapBad, SigningShareLazy.erase, hbad, Option.map_some]

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.tableRunC_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRunC_fst

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.tableRunC_falseTag_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRunC_falseTag_zero

end ThresholdLeanXmssSecurity.SigningCompilerShareCap
