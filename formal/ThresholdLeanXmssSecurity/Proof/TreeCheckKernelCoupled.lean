import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoupling

/-!
# The coupled relation of the check kernel

`adapter` is the GS20 check adversary of the fixed family. `Coupled n n' ℓ P Q` says that the real
programs `P` and the hybrid programs `Q` of `adapter` couple with `Final`. `hashPrefix_support` gives
the shape of each outcome of `hashPrefix`. The module doc of `TreeCheckKernelCoupling` describes the
relation.

These declarations are in the namespace `TreeCheckKernelCoupling`. They use `TreeCheckWalkRecipe` and
`CheckCore`, and `TreeCheckKernelCoupling` does not import these modules.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

open TreeCheckWalkCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Phases

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hashPrefix_support {X : Type} (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (xs : C.Party → Option X) (hx : xs ∈ support (hashPrefix D W)) :
    ∀ i, (i ∈ D.1 → xs i = none) ∧ (i ∉ D.1 → (xs i).isSome) := by
  intro i
  have h := mem_support_sequenceFin_oc _ xs hx i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, support_pure, Set.mem_singleton_iff] at h
    exact ⟨fun _ => h, fun h' => (h' hi).elim⟩
  · simp only [if_neg hi, support_map, Set.mem_image] at h
    obtain ⟨x, _, hx⟩ := h
    exact ⟨fun h' => (hi h').elim, fun _ => by rw [← hx]; rfl⟩

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

variable (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)

/-- The family's GS20 check adversary. -/
abbrev adapter : CheckAdversary C E (List (Tuple C)) :=
  TreeCheckWalkRecipe.checkAdversary prims K D A x prss cache0 label0

/-- From every start with the real hash cache equal to the hybrid one, extending
the checkpoint cache, and no hidden draw at the label `ℓ` or later, the real
programs `P` and the hybrid programs `Q` couple with `Final`. -/
def Coupled {β : Type} (n n' ℓ : ℕ) (P : C.Party → PartyM C E RealSpec β)
    (Q : C.Party → PartyM C E (CheckSpec C E) Unit) : Prop :=
  ∀ (stA : A.State) (h : HashCache C) (c : HiddenCache C), cache0 ≤ h → TreeSimFutureEmpty ℓ c →
    RelTriple (realRun prims D A n stA P (h, c))
      (hybRun prims K D (adapter prims K D A x prss cache0 label0) n' ((stA, ℓ) : A.State × ℕ) Q h)
      (Final D A)

end Phases

end ThresholdLeanXmssSecurity.TreeCheckKernelCoupling
