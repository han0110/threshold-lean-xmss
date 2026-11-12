import ThresholdLeanXmssSecurity.Proof.LifetimePathCount

/-!
# Stream-key separation from a complete setup path budget

The failure of `KeysApart` is bounded by an early cached hidden input,
colliding sampled parts, or a collision during key derivation. Only the
early-cache estimate consumes the setup path budget.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeKeysApartPath

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The key-separation estimate under one counted bound on `setupEarly`. -/
theorem prob_notKeysApart_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Q : ℕ)
    (hQ : IsQueryBoundP (setupEarly D A (A.start (corruptInputs D x) z)) Counted Q) :
    Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)] ≤
      (Q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 +
        ((Fintype.card (C.Party × C.Party × C.Term × C.Term) +
          Fintype.card (C.Party × C.Party × C.Party × C.Party) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (revealPairs C : ℝ≥0∞) / 2 ^ 256 := by
  rw [worldRun_setupPrefix, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_add _ _ _
    (fun r => EarlyCached D r ∨ PartsCollide D (fun i => (r.1.1 i).1))
    ((revealPairs C : ℝ≥0∞) / 2 ^ 256) fun r _ hb => ?_).trans ?_
  · push Not at hb
    exact prob_setupReveal_le prims D r.1 r.2 hb.1 hb.2
  · gcongr
    refine (probEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · exact LifetimePathCount.earlyCached_le prims D A _ Q hQ
    · exact prob_setupEarly_partsCollide_le prims D A _

/-- info: 'ThresholdLeanXmssSecurity.LifetimeKeysApartPath.prob_notKeysApart_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prob_notKeysApart_le

end ThresholdLeanXmssSecurity.LifetimeKeysApartPath
