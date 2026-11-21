import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsShift
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.SeedTable.IdealCoupling

/-!
# The shift of the seed of a hidden term

The module has three general lemmas on lists and on `mapM` (`getD_zipWith_idxOf`,
`length_of_mem_support_mapM`, `mapM_map_zipWith`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare (hiddenInput holdersList)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The shift on the local oracles -/

/-! ## The list of the term seeds -/

theorem mapM_map_zipWith {ι : Type} {spec : OracleSpec ι} {α β : Type} (h : α → β → β)
    (f : α → OracleComp spec β) : ∀ l : List α,
    l.mapM (fun x => h x <$> f x) = (fun r => List.zipWith h l r) <$> l.mapM f
  | [] => by simp
  | x :: xs => by
    simp only [List.mapM_cons, map_bind, bind_map_left, mapM_map_zipWith h f xs, map_pure]
    refine bind_congr fun a => ?_
    simp [List.zipWith_cons_cons]

theorem length_of_mem_support_mapM {ι : Type} {spec : OracleSpec ι} {α β : Type} (f : α → OracleComp spec β) :
    ∀ (l : List α) (r : List β), r ∈ support (l.mapM f) → r.length = l.length
  | [], r, hr => by simpa using hr
  | x :: xs, r, hr => by
    simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨a, -, bs, hbs, rfl⟩ := hr
    simp [length_of_mem_support_mapM f xs bs hbs]

theorem getD_zipWith_idxOf {α β : Type} [BEq α] [LawfulBEq α] (h : α → β → β) (l : List α) (r : List β) (d : β)
    (hr : r.length = l.length) (x : α) (hx : x ∈ l) :
    (List.zipWith h l r).getD (l.idxOf x) d = h x (r.getD (l.idxOf x) d) := by
  have hi := List.idxOf_lt_length_of_mem hx
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith,
    List.getElem_idxOf]

/-! ## The rounds -/

/-! ## The program -/

/-! ## The statement -/

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

