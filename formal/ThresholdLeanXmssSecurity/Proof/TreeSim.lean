import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Coupling

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-!
# The draw order of a list

This module holds one lemma on the draw order of a list. `treeSim_sequenceFin_mapM` states that
`sequenceFin` and the list traversal of the protocol draw in the same order. The signing proof
uses it.
-/

/-- `sequenceFin` and the protocol's list traversal use the same draw order. -/
theorem treeSim_sequenceFin_mapM {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : ℕ} (f : Fin n → m α) :
    List.ofFn <$> OverPermutation.sequenceFin f = (List.finRange n).mapM f := by
  induction n with
  | zero => simp [OverPermutation.sequenceFin, List.finRange]
  | succ n ih =>
    simp only [OverPermutation.sequenceFin, List.finRange_succ, List.mapM_cons, List.mapM_map,
      map_bind, map_pure, List.ofFn_succ]
    rw [← ih]
    simp only [bind_map_left, pure_bind]
    rfl

end ThresholdLeanXmssSecurity
