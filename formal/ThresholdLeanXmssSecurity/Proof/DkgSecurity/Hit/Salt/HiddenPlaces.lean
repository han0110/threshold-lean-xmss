import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Cache
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Merge

/-!
# The full hidden places

`Full hidden` states that each place of a term with a cell at the position 0 of the stream index 2
has all 256 cells. Then each hidden salt is a full hidden salt (`hiddenSalts_subset_full`).
`loggedWorld_hiddenOnly` states that a call of `loggedWorld` changes the hidden table only at the cell
of a free call of `PRG` under a hidden name, and `readCell` is one such read.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (HonestP)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-- Each place of a term with a cell at the position 0 of the stream index 2 has all 256 cells. -/
def Full (hidden : HiddenCache C) : Prop :=
  ∀ (T : C.Term) (key : HashOutput) (ρ : ℕ), hidden ((.term T, key), ρ, 2, 0) ≠ none →
    ∀ position < 256, hidden ((.term T, key), ρ, 2, position) ≠ none

theorem full_empty : Full (∅ : HiddenCache C) := fun _ _ _ h => absurd rfl h

theorem hiddenSalts_subset_full (D : C.Coalition) {hidden : HiddenCache C} (h : Full hidden) :
    hiddenSalts D hidden ⊆ fullHiddenSalts D hidden := by
  rintro salt ⟨T, key, ρ, hT, hne, rfl⟩
  exact ⟨T, key, ρ, hT, h T key ρ hne, rfl⟩

variable (prims : Primitives) (D : C.Coalition)

/-- A call of `loggedWorld` changes the hidden table only at the cell of a free call of `PRG` under a
hidden name. -/
theorem loggedWorld_hiddenOnly (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w), ∀ d, z.2.1.2 d ≠ w.1.2 d →
      ∃ x, t = .inr (.inr (.inr x)) ∧ Hidden D x.1 ∧ d = ((x.1, x.2.1), x.2.2) := by
  intro z hz d hd
  obtain ⟨x, rfl, hdx⟩ := loggedWorld_hidden prims D t w z hz d hd
  refine ⟨x, rfl, ?_, hdx⟩
  by_contra hx
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  simp only [streamWorld, ite_eq_right hx, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', -, rfl⟩ := hr
  exact hd rfl

/-- One read of `PRG`. -/
def readCell (x : PrgInput C) : OracleComp (RoSpec C) Bit := query (spec := RoSpec C) (.inr x)

/-- A read of `PRG` on the free copy is a free call of `PRG`. -/
theorem free_liftComp_readCell_bind {α : Type} (x : PrgInput C) (k : Bit → OracleComp (RoSpec C) α) :
    free (liftComp (readCell x >>= k) (LocalSpec C)) =
      (liftM ((WorldSpec C).query (.inr (.inr (.inr x)))) : OracleComp (WorldSpec C) _) >>= fun u =>
        free (liftComp (k u) (LocalSpec C)) := by
  rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
  rfl

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.loggedWorld_hiddenOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.loggedWorld_hiddenOnly
