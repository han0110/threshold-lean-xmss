import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Accepts
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Move

/-!
# `TableHop` from the rest after the move of the dealer

`DealerFirstForger` states that `dealerFirstGame` wins at most as often as `forgerWorldGame`, for a
positive run limit. Both games sample the keys of the dealer and compute its top tree first.
`tableHop_of_dealerFirstForger` gives `TableHop` from it. At the run limit 0 `dealtGame` never wins.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- At the run limit 0 `dealtGame` never wins. -/
theorem streamAccepts_dealtGame_zero (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    streamAccepts prims D (dealtGame K circuits settings 0 m D A) = 0 := by
  have hf : List.find? (fun _ : C.Party => false) C.parties = none := by simp [List.find?_eq_none]
  have e : dealtGame K circuits settings 0 m D A = (fun _ => false) <$> (worldSeedGen D A.net >>= fun r =>
      voteRound worldRoles D A.net r.1 fun i => ((r.2.2.2.2 i).map fun _ => r.2.2.2.1 i).map seedVote) := by
    unfold dealtGame dealtRun secRest
    simp only [map_bind]
    refine bind_congr fun r => ?_
    simp only [StateT.run'_eq, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, pure_bind,
      bind_assoc, map_bind]
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun v => ?_
    simp [secRuns, secSigning, topHolder, startState, votedStart, hf]
  rw [e]
  unfold streamAccepts
  rw [ENNReal.toReal_eq_zero_iff]
  left
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_
  rw [simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp

/-- `dealerFirstGame` wins at most as often as `forgerWorldGame`, for a positive run limit. -/
def DealerFirstForger : Prop :=
  0 < runLimit → ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (dealerFirstGame K circuits settings runLimit D A) ≤
      streamAccepts prims D (forgerWorldGame K circuits settings runLimit D A)

/-- `DealerFirst` from `DealerFirstForger`. -/
theorem dealerFirst_of_forger (h : DealerFirstForger prims K circuits settings runLimit) :
    DealerFirst prims K circuits settings runLimit := fun D A => by
  rcases Nat.eq_zero_or_pos runLimit with h0 | hrun
  · subst h0
    rw [streamAccepts_dealtGame_zero]
    exact ENNReal.toReal_nonneg
  · rw [dealerFirst_eq K circuits settings runLimit prims hrun D A]
    exact h hrun D A

/-- `TableHop` from `DealerFirstForger`. -/
theorem tableHop_of_dealerFirstForger (h : DealerFirstForger prims K circuits settings runLimit) :
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
      streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) ≤
        accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) :=
  tableHop_of_dealerFirst prims K circuits settings runLimit (dealerFirst_of_forger prims K circuits settings runLimit h)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop_of_dealerFirstForger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop_of_dealerFirstForger
