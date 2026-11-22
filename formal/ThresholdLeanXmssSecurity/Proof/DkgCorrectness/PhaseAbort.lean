import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Basics
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Route

/-!
# The abort of an honest operator before a round

`phase_dead_noOutput` states that an honest operator that aborts at once makes each honest operator
end a phase with no output, when each honest program starts with a round. `bottomRest_noOutput` gives
this for the rest of a bottom tree after the cut, with an honest operator that has no head result.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## An abort before a round -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem startsWithRound_failure {α : Type} : StartsWithRound (failure : PartyM C E RealSpec α) := by
  intro step hs
  rw [advance_run_failure, support_pure, Set.mem_singleton_iff] at hs
  exact Or.inl hs

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The PRSS setup starts with a round, the exchange of its commitments. -/
theorem startsWithRound_prssSetup (i : C.Party) : StartsWithRound (prssSetup i : PartyM C E RealSpec (PrssKeys C)) := by
  unfold prssSetup
  refine startsWithRound_localStep_bind _ _ fun own => ?_
  unfold prssSetupWith
  refine startsWithRound_bind _ _ ?_
  unfold commitRevealEcho
  exact startsWithRound_oracleStep_bind _ _ fun _ => startsWithRound_exchange_bind _ _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A phase in which one honest operator is not alive and each honest program starts with a round
gives no honest output, for each adversary and each world. -/
theorem phase_dead_noOutput {α : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ)
    (st : net.State) (prog : C.Party → PartyM C E RealSpec α) (i₀ : C.Party) (hi₀ : i₀ ∉ D.1)
    (hdead : prog i₀ = failure) (hround : ∀ i, i ∉ D.1 → StartsWithRound (prog i)) (w : StreamState C)
    (z : (net.State × (C.Party → Option α)) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executePhase worldRoles D net noFunctionality fuel st prog)).run w)) :
    ∀ i, i ∉ D.1 → z.1.2 i = none := by
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  have hsteps : ∀ k, k ∉ D.1 → a.1 k ∈ support (advance (prog k).run) := by
    intro k
    unfold startSteps at ha
    refine sequenceFin_streamWorld prims D (fun k v _ => k ∉ D.1 → v ∈ support (advance (prog k).run)) _
      (fun _ _ _ _ h _ => h) (fun k w' u hu hk => ?_) w a ha k
    simp only [hk, ↓reduceIte] at hu
    refine mem_support_advance_of_handler (streamWorld prims D) (prog k) w' u.1 ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨u, hu, rfl⟩
  have h₀ : a.1 i₀ = .done none := by
    have h := hsteps i₀ hi₀
    rw [hdead, advance_run_failure, support_pure, Set.mem_singleton_iff] at h
    exact h
  intro i hi
  exact executeRounds_cut_noOutput (streamWorld prims D) D net noFunctionality fuel st a.1 prog ⟨i₀, hi₀, h₀⟩
    (fun j hj => Or.inr ⟨hround j hj, hsteps j hj⟩) a.2 z hz i (hsteps i hi) (hround i hi)

omit [Fintype E] [DecidableEq E] in
/-- The rest of a bottom tree at one operator starts with a round, the first exchange of the second
PRSS setup, or it aborts at once. -/
theorem startsWithRound_bottomTail (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (x : HeadResult) : StartsWithRound (CheckTiming.bottomTail K circuits settings i operator b x) := by
  rcases hk : operator.keys with _ | keys
  · simp only [CheckTiming.bottomTail, hk]
    exact startsWithRound_failure
  · rcases ht : operator.top with _ | top
    · simp only [CheckTiming.bottomTail, hk, ht]
      exact startsWithRound_failure
    · obtain ⟨k, hk'⟩ := CheckTiming.bottomTail_prssSetup K circuits settings i operator b keys top hk ht x
      rw [hk']
      exact startsWithRound_bind _ _ (startsWithRound_prssSetup i)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- An honest operator with no head result leaves no honest output of the rest of a bottom tree. Each
living operator meets the abort frame in the first exchange of its second PRSS setup. This is `CutDead` up to the line of the monitor. -/
theorem bottomRest_noOutput (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (st : net.State) (heads : C.Party → Option HeadResult) (m : ℕ)
    (w : StreamState C) (i₀ : C.Party) (hi₀ : i₀ ∉ D.1) (hnone : heads i₀ = none)
    (r : (net.State × (C.Party → Option TreeOutput)) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality m st fun i =>
      (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (s.operators i) b))).run w)) :
    ∀ i, i ∉ D.1 → r.1.2 i = none := by
  refine phase_dead_noOutput prims D net m st _ i₀ hi₀ (by simp [hnone]) (fun i _ => ?_) w r hr
  cases heads i with
  | none => exact startsWithRound_failure
  | some x => exact startsWithRound_bottomTail K circuits settings i (s.operators i) b x

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.phase_dead_noOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.phase_dead_noOutput

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.bottomRest_noOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.bottomRest_noOutput
