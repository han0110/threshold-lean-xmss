import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Counts
import Mathlib.Data.Sym.Card

/-!
# The count of the shifts that the list run names

* `logged_seedGenList` bounds the counted calls of `seedGenList`. So the log of the list run has at
  most `q` cells (`listRun_log_le`).
* `cellNamed D parts seed q` is the set of the shifts that one cell `q` of the log names. A PRF cell
  names at most one shift for each hidden term. A shared key cell names at most one shift for each
  unordered pair of distinct operators, by the first hidden term that they share.
* `listNamed_subset` puts the named shifts of a run in the union of `cellNamed` over its log, and
  `listCount` proves `ListCount`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The log of the list run -/

section Log

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation of the list program makes the calls of the `setupRounds` rounds of the
adversary. -/
theorem logged_seedGenList (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    IsQueryBoundP (seedGenList D net state early parameter dealt parts adj) Logged (setupRounds * step) :=
  logged_seedGenShape D net step hround state early parameter dealt parts (commitDraws D parts)
    (noLogged_commitDrawsAt D (commitAddress parts)) _ _ _

omit [Fintype E] [DecidableEq E] in
/-- The log of the list run with the budget `q` has at most `q` cells. -/
theorem listRun_log_le (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    ∀ r ∈ support (listRun prims K circuits settings runLimit D A), r.2.2.2.length ≤ q := by
  intro r hr
  simp only [listRun, listRunWith, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨x, hx, seed, -, z, hz, rfl⟩ := hr
  have bound := logged_prefix_suffixOf K circuits settings runLimit D A q bounded
    (fun x => seedGenList D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2 fun _ _ keys => keys)
    (fun step hround x => logged_seedGenList D A.net step hround _ _ _ _ _ _)
  exact log_prefix_suffix prims D A _ q bound (fun y => compWorld prims D y.2.2 (id seed))
    (fun y => compWorld_log prims D y.2.2 (id seed)) x hx z hz

end Log

/-! ## The shifts that one cell names -/

section Cells

variable (D : C.Coalition) (parts : C.Party → Parts C)

/-- The key of a PRF cell. -/
def prfKey : Query C → HashOutput
  | .prf key _ => key
  | _ => 0

/-- The list of a shared key cell. -/
def sharedList : Query C → List HashOutput
  | .sharedKeys _ L => L
  | _ => []

/-- The shift that a shared key cell `q` names for the pair `i`, `j`, by the first hidden term that
they share. -/
def pairShift (seed : C.Term → HashOutput) (q : Query C) (i j : C.Party) : HashOutput :=
  match (sharedTerms i j).find? (fun T => ¬ KnownTo D.1 T) with
  | some T => (sharedList q).getD ((sharedTerms i j).idxOf T) 0 ^^^ heldSeed D parts seed T
  | none => 0

theorem pairShift_comm (seed : C.Term → HashOutput) (q : Query C) (i j : C.Party) :
    pairShift D parts seed q i j = pairShift D parts seed q j i := by
  unfold pairShift
  rw [sharedTerms_comm i j]

/-- The shifts that the cell `q` names. -/
def cellNamed (seed : C.Term → HashOutput) (q : Query C) : Finset HashOutput :=
  (hiddenTerms D).image (fun T => seed T ^^^ prfKey q) ∪
    ((Finset.univ : Finset C.Party).offDiag.image Sym2.mk.uncurry).image
      (Sym2.lift ⟨pairShift D parts seed q, pairShift_comm D parts seed q⟩)

theorem card_cellNamed (seed : C.Term → HashOutput) (q : Query C) :
    (cellNamed D parts seed q).card ≤ (hiddenTerms D).card + C.n.choose 2 := by
  unfold cellNamed
  refine (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le (Finset.card_image_le.trans ?_))
  rw [Sym2.card_image_offDiag, Finset.card_univ, Fintype.card_fin]

/-- The seed that a holder of a hidden term derives moves with the common shift. -/
theorem heldSeed_shiftHidden (δ : HashOutput) (seed : C.Term → HashOutput) {T : C.Term} (hT : ¬ KnownTo D.1 T) :
    heldSeed D parts (shiftHidden D δ seed) T = heldSeed D parts seed T ^^^ δ := by
  unfold heldSeed
  cases h : hiddenTermOf D parts (hiddenInput parts T) with
  | none =>
    unfold hiddenTermOf at h
    rw [dite_eq_left ⟨T, hT, rfl⟩] at h
    cases h
  | some T' =>
    simp only [shiftHidden, (hiddenTermOf_some D parts h).1, ↓reduceIte]

theorem xor_cancel_left (a b : HashOutput) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Each named shift of a run is named by one cell of its log. -/
theorem listNamed_subset (seed : C.Term → HashOutput) (w : LogState C) :
    listNamed D (parts, seed, w) ⊆ w.2.toFinset.biUnion (cellNamed D parts seed) := by
  intro δ hδ
  simp only [listNamed, Finset.mem_filter, Finset.mem_univ, true_and] at hδ
  rw [Finset.mem_biUnion]
  rcases hδ with ⟨q, hq, T, x, hT, rfl⟩ | ⟨q, hq, L, i, j, T, -, -, hij, hf, rfl, hL⟩
  · refine ⟨_, List.mem_toFinset.2 hq, Finset.mem_union_left _ (Finset.mem_image.2 ⟨T, ?_, ?_⟩)⟩
    · simp [hiddenTerms, hT]
    · simp only [prfKey, shiftHidden, hT, ↓reduceIte]
      exact xor_cancel_left _ _
  · have hT : ¬ KnownTo D.1 T := by
      have h2 := List.find?_some hf
      simpa using h2
    refine ⟨_, List.mem_toFinset.2 hq, Finset.mem_union_right _ (Finset.mem_image.2
      ⟨Sym2.mk i j, Finset.mem_image.2 ⟨(i, j), ?_, rfl⟩, ?_⟩)⟩
    · simp [Finset.mem_offDiag, hij]
    · simp only [Sym2.lift_mk, pairShift, hf, sharedList]
      rw [hL, heldSeed_shiftHidden D parts δ seed hT, BitVec.xor_comm (heldSeed D parts seed T) δ, BitVec.xor_assoc,
        BitVec.xor_self, BitVec.xor_zero]

end Cells

/-! ## The count -/

section Count

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
theorem listCount : ListCount prims K circuits settings runLimit := by
  intro D A q bounded r hr
  have hlog := listRun_log_le prims K circuits settings runLimit D A q bounded r hr
  obtain ⟨parts, seed, w⟩ := r
  refine (Finset.card_le_card (listNamed_subset D parts seed w)).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ fun c _ => card_cellNamed D parts seed c).trans ?_
  rw [smul_eq_mul]
  exact Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans hlog)

end Count

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listCount
