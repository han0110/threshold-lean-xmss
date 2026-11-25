import ThresholdLeanXmssSecurity.Proof.SigningSelection
import ThresholdLeanXmssSecurity.Proof.Vote

/-!
# The vote round has no split

`voteRound_split` states that the outputs after `voteRound` have no split on each outcome, for each
roles in a monad of oracle calls. `voteRound_split_run` states the same for each stateful answer of
the oracles. Both come from `split_committed`, because an honest operator with no output sends
`abort` in `voteRound`. `voteRound_isQueryBoundP` bounds the calls of the vote round under
`worldRoles` by the calls of one round of the adversary, when no honest vote is a counted call.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.Vote

variable {C : Committee} {E : Type}

open SigningSelectionProof (noCall_iff noCall_pure noCall_sequenceFin)

attribute [local instance] Classical.propDecidable

/-- The outputs after the vote have no split, on each outcome of `voteRound`. -/
theorem voteRound_split {ι α : Type} {spec : OracleSpec ι} (Ro : Roles C (OracleComp spec)) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (outputs : C.Party → Option α)
    (vote : α → Query C) :
    ∀ z ∈ support (voteRound Ro D net state fun i => (outputs i).map vote), split D (committed z.2 outputs) = false := by
  intro z hz
  simp only [voteRound, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨honest, hhonest, sent, -, rfl⟩ := hz
  refine split_committed D honest sent.2 outputs fun i _ hnone => ?_
  have hi := mem_support_sequenceFin_oc _ honest hhonest i
  simp only [hnone, Option.map_none, support_pure, Set.mem_singleton_iff] at hi
  exact hi

/-- The outputs after the vote have no split, on each outcome of `voteRound` under a stateful answer
of the oracles. -/
theorem voteRound_split_run {ι α σ : Type} {spec : OracleSpec ι} (Ro : Roles C (OracleComp spec))
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (outputs : C.Party → Option α)
    (vote : α → Query C) (impl : QueryImpl spec (StateT σ ProbComp)) (w : σ) :
    ∀ z ∈ support ((simulateQ impl (voteRound Ro D net state fun i => (outputs i).map vote)).run w),
      split D (committed z.1.2 outputs) = false := fun z hz =>
  voteRound_split Ro D net state outputs vote z.1 (mem_support_of_mem_support_simulateQ_run impl _ w hz)

/-- A computation of the adversary under `worldRoles` makes the calls of `p` of its own calls. -/
theorem adversary_isQueryBoundP {β : Type} (p : (WorldSpec C).Domain → Prop) (oa : OracleComp (LocalSpec C) β)
    (n : ℕ) (h : IsQueryBoundP oa (fun t => p (.inl (.inl t))) n) : IsQueryBoundP (worldRoles.adversary oa) p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- The vote round under `worldRoles` makes at most `step` calls of `p`, when each round of the
adversary makes at most `step` own calls of `p` and the hash call of no honest vote is a call of `p`. -/
theorem voteRound_isQueryBoundP (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (input : C.Party → Option (Query C)) (p : (WorldSpec C).Domain → Prop) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) (fun t => p (.inl (.inl t))) step)
    (hhonest : ∀ j q, input j = some q → ¬ p (.inr (.inr (.inl q)))) :
    IsQueryBoundP (voteRound worldRoles D net state input) p step := by
  unfold voteRound
  refine (isQueryBoundP_bind (n := 0) ?_ fun _ _ =>
    (isQueryBoundP_bind (m := 0) (adversary_isQueryBoundP p _ _ (hround _ _)) fun r _ => by
      obtain ⟨_, _⟩ := r; trivial).mono (Nat.add_zero _).le).mono (Nat.zero_add _).le
  rw [← noCall_iff]
  refine noCall_sequenceFin _ _ fun j => ?_
  split
  · rename_i q hq
    split_ifs
    · exact noCall_pure _ _
    · rw [noCall_iff]
      simp only [worldRoles, free, simulateQ_map, isQueryBoundP_map_iff]
      change IsQueryBoundP (liftM ((WorldSpec C).query (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) _) p 0
      rw [isQueryBoundP_query_iff]
      exact fun h => absurd h (hhonest j q hq)
  · exact noCall_pure _ _

end ThresholdLeanXmssSecurity.Vote
