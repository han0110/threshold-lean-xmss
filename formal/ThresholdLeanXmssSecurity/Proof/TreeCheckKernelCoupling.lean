import ThresholdLeanXmssSecurity.Proof.TreeSim

/-!
# Coupling lemmas on supports

This module holds two lemmas on `RelTriple` couplings. `relTriple_support_left` adds a property of
the left support to a coupling. `relTriple_of_support` gives a coupling from a relation that holds
on all pairs of the two supports. It also holds `Final`, the relation of the final states of a real
and a hybrid execution. The round lemmas of the signing compiler (`SigningCompilerO1Round2`,
`SigningCompilerO1Tail`) use `relTriple_of_support`.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Glue

set_option linter.unusedSectionVars false

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    {P : α → Prop} (h : RelTriple oa ob R) (hp : ∀ a ∈ support oa, P a) :
    RelTriple oa ob (fun a b => R a b ∧ P a) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, ?_⟩
  filter_upwards [hc, ae_mem_support_prod c] with z hz hmem
  exact ⟨hz, hp z.1 hmem.1⟩

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_of_support {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    (h : ∀ a ∈ support oa, ∀ b ∈ support ob, R a b) : RelTriple oa ob R := by
  have left := relTriple_support_left (relTriple_true oa ob) (P := fun a => a ∈ support oa)
    (fun a ha => ha)
  have right := relTriple_symm (relTriple_support_left (relTriple_symm left)
    (P := fun b => b ∈ support ob) (fun b hb => hb))
  exact relTriple_post_mono right fun a b hab => h a hab.1.2 b hab.2

end Glue

section SetupPairs

variable (prims : Primitives) (D : C.Coalition)


end SetupPairs

section Kernel

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
  (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- Every honest operator still running in the real execution accepts in the
hybrid one, whose hash cache is part of the real one. -/
def Final {β σ : Type} (x : (A.State × (C.Party → Step C E RealSpec β)) × HashCache C)
    (y : (σ × (C.Party → Option Unit)) × HashCache C) : Prop :=
  ∀ i, i ∉ D.1 → x.1.2 i ≠ .done none → y.2 ≤ x.2 ∧ y.1.2 i = some ()

end Kernel

section Phases

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

end Phases

end ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_support
