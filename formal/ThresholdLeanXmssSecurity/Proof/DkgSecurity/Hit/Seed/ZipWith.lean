import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsShift

/-!
# Lemmas on `List.zipWith` and `mapM`

`mapM_map_zipWith` moves a map of each answer of `mapM` to a `List.zipWith` on the list of the answers.
`length_of_mem_support_mapM` states that each result of `mapM` has the length of its list.
`getD_zipWith_idxOf` and `getD_zipWith_parties` read one entry of a `List.zipWith`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

variable {C : Committee}

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

theorem getD_zipWith_parties (h : C.Party → HashOutput → HashOutput) (r : List HashOutput)
    (hr : r.length = C.parties.length) (j : C.Party) :
    (List.zipWith h C.parties r).getD j.val 0 = h j (r.getD j.val 0) := by
  have hj : j.val < C.parties.length := by simp [Committee.parties]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
  congr 1
  simp [Committee.parties]

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
