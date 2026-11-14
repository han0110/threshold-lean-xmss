import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Share
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTables

/-! # Private tables for the eager share run of the O1 source

`tableRunCO1_eq_tables` states that the eager fiber run of the O1 source has the same law as the
run that samples the noise table and the free slot table in advance. The proof follows
`SigningCompilerSyncStop.tableRunC_eq_tables` and
`SigningCompilerShareTables.eagerRunTag_eq_tables`.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Tables
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerO1SourceProof SigningCompilerO1Share
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false

section Share
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The O1 source with an eager share table and the cap tag. -/
def eagerRunCO1 (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    ProbComp (CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) :=
  (simulateQ (eagerHandlerC τ g) (shareRunTagO1 prims A x q s pads capTag)).run SigningShareLazy.init

/-- The O1 source with the fiber table of a uniform table. -/
def tableRunCO1 (τ : CPoint → Digest) :
    ProbComp (CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) := do
  let u ← $ᵗ (C.Term × CPoint → HashOutput)
  eagerRunCO1 prims A x q s pads τ
    (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u)

/-- The O1 source over the eager backend with all tables fixed. -/
def eagerRunTagTO1 (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput) :
    ProbComp (CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) :=
  SigningCompilerShareTables.finish x.2.1 <$>
    (simulateQ (shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceProgramO1X prims A x)).run SigningCompilerShareTables.initial

end Share

attribute [local irreducible] sourceProgramO1X sourceProgramO1 sourceGameO1X sourceGameO1

/-- The O1 source over the raw backend, which asks the private oracle for noise and free slots. -/
def rawProgramO1 (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    OracleComp (PrivateSpec C) (CompilerOutcomeO1 C × ShareStateT C (Bool × Bool)) :=
  finish x.2.1 <$> (simulateQ (backendRaw capTag x.1 x.2.1 x.2.2 q s pads τ g)
    (sourceProgramO1X prims A x)).run initial

theorem eagerRunCO1_fused (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    eagerRunCO1 prims A x q s pads τ g =
      finish x.2.1 <$> (simulateQ (eagerBackend capTag x.1 x.2.1 q s pads τ g)
        (sourceProgramO1X prims A x)).run initial := by
  change (simulateQ (eagerHandlerTag τ g) (shareRunTagO1 prims A x q s pads capTag)).run
    SigningShareLazy.init = _
  rw [eagerBackend, ← SigningCompilerUntil.simulateQ_fuse]
  simp only [shareRunTagO1, initial, simulateQ_bind, StateT.run_bind, eager_view,
    bind_pure_comp, finish, Functor.map_map, simulateQ_map, StateT.run_map, map_pure]

theorem eagerRunCO1_raw (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    eagerRunCO1 prims A x q s pads τ g =
      Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (rawProgramO1 prims A x q s pads τ g)).run ∅ := by
  rw [eagerRunCO1_fused]
  have h := programRaw_eq capTag x.1 x.2.1 x.2.2 hi q s pads τ g
    (sourceProgramO1X prims A x) initial ∅ ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [← h]
  simp only [rawProgramO1, simulateQ_map, StateT.run_map, Functor.map_map]

theorem eagerRunTagTO1_raw (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput) :
    eagerRunTagTO1 prims A x q s pads τ g noise rest =
      simulateQ (resolvePrivateTable (Sum.elim noise rest))
        (rawProgramO1 prims A x q s pads τ g) := by
  simp only [eagerRunTagTO1, rawProgramO1, simulateQ_map]
  rw [simulateQ_StateT_compose _ _ _ (fun _ _ => rfl)]
  rfl

/-- Reuse the pinned independent-uniform-pair law under an arbitrary continuation. This lemma is a
port of the private `SigningCompilerShareTables.uniform_pair`. -/
private theorem uniform_pair {α β γ : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] (next : α → β → ProbComp γ) :
    (do let a ← $ᵗ α; let b ← $ᵗ β; next a b) =ᵈ
      (($ᵗ (α × β)) >>= fun z => next z.1 z.2) := by
  have h := (XmssSecurity.evalDist_independent_uniform_pair (α := α) (β := β)).bind_left
    (fun z => next z.1 z.2)
  simpa only [bind_assoc, pure_bind] using h

/-- For a fixed share table, independent noise and free slot tables keep the law of the run. -/
theorem eagerRunCO1_eq_tables (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    eagerRunCO1 prims A x q s pads τ g =ᵈ
      (do
           let noise ← $ᵗ (ChainNoiseIndex → HashOutput)
           let rest ← $ᵗ (RestSlot C → HashOutput)
           eagerRunTagTO1 prims A x q s pads τ g noise rest) := by
  have hi : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2) := by
    simp only [TprfSecurityProof.KeyCollision, not_or, not_not] at hkeys
    exact TprfSecurityProof.slotInput_injective hkeys.1 hkeys.2
  simp only [eagerRunTagTO1_raw]
  rw [eagerRunCO1_raw prims A x hi]
  refine (privateRo_eq_table _ _).trans ?_
  simp only [tableExtending_empty]
  let e := Equiv.sumArrowEquivProdArrow ChainNoiseIndex (RestSlot C) HashOutput
  have hu := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (α := TableIndex C → HashOutput) e.bijective
  have hm := hu.bind_left (fun z =>
    simulateQ (resolvePrivateTable (e.symm z)) (rawProgramO1 prims A x q s pads τ g))
  simp only [bind_map_left, Equiv.symm_apply_apply] at hm
  refine hm.trans ?_
  refine EvalDistEq.trans ?_ (uniform_pair (fun noise rest =>
    simulateQ (resolvePrivateTable (Sum.elim noise rest)) (rawProgramO1 prims A x q s pads τ g))).symm
  exact EvalDistEq.of_eq rfl

section Share
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- The table run samples the noise table and the free slots. -/
theorem tableRunCO1_eq_tables (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (τ : CPoint → Digest) :
    tableRunCO1 prims A x q s pads τ =ᵈ
      (do
           let u ← $ᵗ (C.Term × CPoint → HashOutput)
           let noise ← $ᵗ (ChainNoiseIndex → HashOutput)
           let rest ← $ᵗ (RestSlot C → HashOutput)
           eagerRunTagTO1 prims A x q s pads τ
             (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u)
             noise rest) := by
  unfold tableRunCO1
  refine EvalDistEq.bind_right _ fun u => ?_
  exact eagerRunCO1_eq_tables prims A x hkeys q s pads τ _

end Share

end ThresholdLeanXmssSecurity.SigningCompilerO1Tables

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tables.tableRunCO1_eq_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tables.tableRunCO1_eq_tables
