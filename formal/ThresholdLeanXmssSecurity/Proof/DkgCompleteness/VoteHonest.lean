import ThresholdLeanXmssSecurity.Proof.Check
import ThresholdLeanXmssSecurity.Proof.SeedGen
import ThresholdLeanXmssSecurity.Proof.Vote

/-!
# The vote of an honest run

With no corrupt operator and the honest adversary, `voteRound` is a local computation on the free
copy (`voteRound_honestNet`). `localVote` is that computation. Each operator with an input makes one
call of `H`, and each other operator sends `abort`.

`run'_localVote_const` is the vote on one input at each operator. The calls of `H` are one call on
one input, so all votes are equal. The decision is `true` exactly when the input exists. A later
computation that reads no result of the vote has the same output as with no vote, because a call of
`H` whose answer nothing reads changes no output (lazy sampling, `evalDist_run'_prepend`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCompletenessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The vote of one honest operator on its input, as a computation of `H`. -/
def voteMessage : Option (Query C) → OracleComp (RoSpec C) (Msg E)
  | some q => (fun h => Msg.hashes [h]) <$> hashQuery q
  | none => pure Msg.abort

/-- The vote round with no corrupt operator and the honest adversary, as a local computation. -/
def localVote (input : C.Party → Option (Query C)) : OracleComp (LocalSpec C) Bool :=
  (fun honest : C.Party → Msg E => decision (fun j => some (honest j))) <$>
    OverPermutation.sequenceFin fun j => liftComp (voteMessage (input j)) (LocalSpec C)

/-- The vote round with no corrupt operator and the honest adversary is `localVote` on the free
copy. -/
theorem voteRound_honestNet (state : (honestNet (C := C) (E := E)).State) (input : C.Party → Option (Query C)) :
    voteRound worldRoles noCoalition honestNet state input = (fun ok => (state, ok)) <$> free (localVote (E := E) input) := by
  unfold voteRound localVote
  simp only [free, simulateQ_map, simulateQ_sequenceFin]
  simp [worldRoles, honestNet, honestAdversary, counted, noCoalition, map_eq_bind_pure_comp]
  congr 1
  · congr 1
    funext j
    cases input j <;> simp [voteMessage, free, map_eq_bind_pure_comp]

/-- The decision on one vote at each operator. -/
theorem decision_const (v : Msg E) : decision (fun _ : C.Party => some v) = decide (v ≠ Msg.abort) := by
  have j : C.Party := ⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩
  unfold decision
  refine decide_eq_decide.2 ⟨fun ⟨w, hw, hall⟩ => ?_, fun hv => ⟨v, hv, fun _ => rfl⟩⟩
  rw [Option.some.inj (hall j)]
  exact hw

/-- `sameRun_sequenceFin_const` for each positive count. -/
theorem sameRun_sequenceFin_const_pos (prims : Primitives) {β : Type} (oa : OracleComp (RoSpec C) β) :
    ∀ {n : ℕ}, 0 < n → SameRun prims (OverPermutation.sequenceFin fun _ : Fin n => liftComp oa (LocalSpec C))
      (liftComp oa (LocalSpec C) >>= fun b => pure fun _ => b)
  | n + 1, _ => sameRun_sequenceFin_const prims oa n

/-- The vote on one input `x` at each operator, followed by a continuation `k`. The output is the
output of `k` on `x.isSome`, from each cache. -/
theorem run'_localVote_const (prims : Primitives) (x : Option (Query C)) {α : Type}
    (k : Bool → OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (localVote (E := E) (fun _ => x) >>= k)).run' s =ᵈ
      (simulateQ (localAnswer prims) (k x.isSome)).run' s := by
  have hn : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  have hsame := (sameRun_sequenceFin_const_pos prims (voteMessage (C := C) (E := E) x) hn).bind
    fun honest => SameRun.refl prims (k (decision fun j => some (honest j)))
  have hrun : (simulateQ (localAnswer prims) (localVote (E := E) (fun _ => x) >>= k)).run' s =ᵈ
      (simulateQ (localAnswer prims) (liftComp (voteMessage (C := C) (E := E) x) (LocalSpec C) >>= fun b =>
        k (decision fun _ : C.Party => some b))).run' s := by
    have h := (hsame s).map Prod.fst
    simp only [bind_assoc, pure_bind] at h
    rw [StateT.run'_eq, StateT.run'_eq, localVote, bind_map_left]
    exact h
  refine hrun.trans ?_
  cases x with
  | none => simp [voteMessage, decision_const]
  | some q =>
    simp only [voteMessage, liftComp_map, bind_map_left, decision_const, ne_eq, reduceCtorEq, not_false_eq_true,
      decide_true, Option.isSome_some]
    exact evalDist_run'_prepend prims _ _ s

end ThresholdLeanXmssSecurity.DkgCompletenessProof
