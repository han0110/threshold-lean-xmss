import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningReach
import ThresholdLeanXmssSecurity.Proof.PhaseSplit

/-!
# The split of a ghost phase on the real network

`executePhaseR_bind_world` splits a run of the ghost executor at the end of a timed phase. It is
`WorldSplit.executePhase_bind_world` for programs with a record. A program is `p i >>= g i`, where
each honest `p i` gives a result after exactly `a` rounds or aborts, and `g i` keeps the record of an
abort. Under each handler whose free local answers commute, the run has the law of a run of `a`
rounds on `p` and then a run of `b` rounds on `g i` of the result and the record of each operator.
The proof follows the proof of `WorldSplit.executePhase_bind_world` step by step.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace GhostSplit

open WorldSplit RecordedOpening

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## Ghost steps with a continuation -/

section Continue

variable {C : Committee} {E : Type} {α β ρ : Type}

/-- A recorded program that gives a result after exactly `n` rounds, or aborts. -/
abbrev TimedR (n : ℕ) (p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)) : Prop :=
  TimedLog (fun x : Option α × ρ => x.1 = none) (fun x => x.1.isSome) n p

/-- Continue a ghost step with `g`, without running past its next round. -/
def continueStepR (g : Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) :
    RStep C E RealSpec α ρ → OracleComp (LocalSpec C) (RStep C E RealSpec β ρ)
  | .done out record => advanceR (g (out, record))
  | .wait outbox resume => pure (.wait outbox fun inbox => resume inbox >>= g)
  | .call input resume => pure (.call input fun r => resume r >>= g)

/-- Advancing a sequence first advances its prefix and then continues the step. -/
theorem advanceR_bind (p : OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (g : Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) :
    advanceR (p >>= g) = advanceR p >>= continueStepR g := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    rw [pure_bind]
    change advanceR (g x) = pure (RStep.done x.1 x.2) >>= continueStepR g
    rw [pure_bind]
    rfl
  | query_bind q f ih =>
    rcases q with (q | mail) | input
    · rw [bind_assoc]
      change (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (f r >>= g)) =
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (f r)) >>= continueStepR g
      rw [bind_assoc]
      exact bind_congr ih
    · rw [bind_assoc]
      change pure (RStep.wait mail fun inbox => f inbox >>= g) = pure (RStep.wait mail f) >>= continueStepR g
      rw [pure_bind]
      rfl
    · rw [bind_assoc]
      change pure (RStep.call input fun r => f r >>= g) = pure (RStep.call input f) >>= continueStepR g
      rw [pure_bind]
      rfl

/-- The ghost step with the continuation `g` attached. A step that is done stays done, so the lemmas
use it only for a step with no output. -/
def attachStepR (g : Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) :
    RStep C E RealSpec α ρ → RStep C E RealSpec β ρ
  | .done _ record => .done none record
  | .wait outbox resume => .wait outbox fun inbox => resume inbox >>= g
  | .call input resume => .call input fun r => resume r >>= g

variable (g : Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ))

theorem continueStepR_attach (hg : ∀ record, g (none, record) = pure (none, record))
    (step : RStep C E RealSpec α ρ) (h : step.output = none) :
    continueStepR g step = pure (attachStepR g step) := by
  cases step with
  | done out record =>
    change out = none at h
    subst h
    change advanceR (g (none, record)) = _
    rw [hg]
    rfl
  | wait outbox resume => rfl
  | call input resume => rfl

theorem attachStepR_outbox (step : RStep C E RealSpec α ρ) : (attachStepR g step).outbox = step.outbox := by
  cases step <;> rfl

theorem attachStepR_callInput (step : RStep C E RealSpec α ρ) :
    (attachStepR g step).callInput = step.callInput := by
  cases step <;> rfl

theorem attachStepR_isDone (step : RStep C E RealSpec α ρ) : (attachStepR g step).isDone ↔ step.isDone := by
  cases step <;> exact Iff.rfl

theorem attachStepR_delivered (step : RStep C E RealSpec α ρ) (h : step.output = none) :
    (attachStepR g step).delivered = step.delivered := by
  cases step with
  | done out record =>
    change out = none at h
    subst h
    rfl
  | wait outbox resume => rfl
  | call input resume => rfl

end Continue

/-! ## Timed ghost steps -/

section Timed

variable {C : Committee} {E : Type} {α ρ : Type}

/-- A stopped recorded program that needs exactly `n` more rounds, unless it aborts. -/
def StepTimedR (n : ℕ) : RStep C E RealSpec α ρ → Prop
  | .done none _ => True
  | .done (some _) _ => n = 0
  | .wait _ resume => ∃ m, n = m + 1 ∧ ∀ inbox, TimedR m (resume inbox)
  | .call _ _ => False

theorem StepTimedR.output_none {n : ℕ} {step : RStep C E RealSpec α ρ} (h : StepTimedR (n + 1) step) :
    step.output = none := by
  cases step with
  | done out record =>
    cases out with
    | none => rfl
    | some a => exact absurd h (Nat.succ_ne_zero n)
  | wait outbox resume => rfl
  | call input resume => rfl

theorem StepTimedR.isDone {step : RStep C E RealSpec α ρ} (h : StepTimedR 0 step) : step.isDone := by
  cases step with
  | done out record => trivial
  | wait outbox resume =>
    obtain ⟨m, hm, -⟩ := h
    exact absurd hm.symm (Nat.succ_ne_zero m)
  | call input resume => exact h.elim

/-- The local steps of a timed recorded program stop at a timed step. -/
theorem timedR_advanceR {n : ℕ} {p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)} (h : TimedR n p) :
    ∀ s ∈ support (advanceR p), StepTimedR n s := by
  induction h with
  | stop n x hx =>
    intro s hs
    change s ∈ support (pure (RStep.done x.1 x.2) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    rw [hx]
    trivial
  | done x hx =>
    intro s hs
    change s ∈ support (pure (RStep.done x.1 x.2) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hx
    rw [ha]
    rfl
  | queryLocal n q k _ ih =>
    intro s hs
    change s ∈ support (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (k r)) at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨r, -, hr⟩ := hs
    exact ih r s hr
  | round n out k h _ =>
    intro s hs
    change s ∈ support (pure (RStep.wait out k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨n, rfl, h⟩

end Timed

/-! ## The rounds of a timed ghost phase -/

section Rounds

variable {C : Committee} {E : Type} {Ia L R α ρ : Type}
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty PEmpty L R) (blank : ρ)

theorem stepRoundR_noCall (steps : C.Party → RStep C E RealSpec α ρ) :
    ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
  rintro ⟨⟨i, -, hi⟩, -⟩
  cases hs : steps i with
  | done out record => rw [hs] at hi; exact absurd hi (by simp [RStep.callInput])
  | wait outbox resume => rw [hs] at hi; exact absurd hi (by simp [RStep.callInput])
  | call input resume => exact input.elim

/-- A round of the ghost executor takes one round from each timed honest step. -/
theorem stepRoundR_timed (n : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (hD : ∀ i ∈ D.1, steps i = .done none blank) (ht : ∀ i ∉ D.1, StepTimedR (n + 1) (steps i)) :
    ∀ r ∈ support (stepRoundR worldRoles D A F blank st steps),
      (∀ i ∈ D.1, r.2.1 i = .done none blank) ∧ ∀ i ∉ D.1, StepTimedR n (r.2.1 i) := by
  intro r hr
  unfold stepRoundR at hr
  simp only [stepRoundR_noCall D steps, ↓reduceIte] at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨⟨st', sent⟩, -, hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨steps', hsteps', hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hj := Fuel.mem_support_sequenceFin _ steps' hsteps' i
    rw [hD i hi] at hj
    simpa using hj
  · have hj := Fuel.mem_support_sequenceFin _ steps' hsteps' i
    have hti := ht i hi
    show StepTimedR n (steps' i)
    revert hj hti
    cases steps i with
    | done out record =>
      intro hj hti
      rw [support_pure, Set.mem_singleton_iff] at hj
      rw [hj]
      cases out with
      | none => trivial
      | some a => exact absurd hti (Nat.succ_ne_zero n)
    | wait outbox resume =>
      intro hj hti
      simp only [hi, ↓reduceIte] at hj
      obtain ⟨m, hm, hk⟩ := hti
      obtain rfl : n = m := by omega
      exact timedR_advanceR (hk _) _ (Fuel.mem_support_honest _ _ hj)
    | call input resume => exact input.elim

/-- The rounds of a timed ghost phase end with each honest step done. -/
theorem executeRoundsR_timed : ∀ (n : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ),
    (∀ i ∈ D.1, steps i = .done none blank) → (∀ i ∉ D.1, StepTimedR n (steps i)) →
    ∀ r ∈ support (executeRoundsR worldRoles D A F blank n st steps),
      (∀ i ∈ D.1, r.2 i = .done none blank) ∧ ∀ i ∉ D.1, (r.2 i).isDone
  | 0, st, steps, hD, ht => by
    intro r hr
    simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hD, fun i hi => (ht i hi).isDone⟩
  | n + 1, st, steps, hD, ht => by
    intro r hr
    simp only [executeRoundsR] at hr
    split_ifs at hr with hd
    · rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hD, hd⟩
    · rw [mem_support_bind_iff] at hr
      obtain ⟨q, hq, hr⟩ := hr
      obtain ⟨hD', ht'⟩ := stepRoundR_timed D A F blank n st steps hD ht q hq
      exact executeRoundsR_timed n q.1 q.2.1 hD' ht' r hr

/-- Rounds from honest steps that are all done return them. -/
theorem executeRoundsR_allDone (fuel : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (h : ∀ i, i ∉ D.1 → (steps i).isDone) :
    executeRoundsR worldRoles D A F blank fuel st steps = pure (st, steps) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [executeRoundsR, ite_eq_left h]

/-- The first steps of a timed ghost phase. -/
theorem startStepsR_timed (a : ℕ) (p : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (hp : ∀ i ∉ D.1, TimedR a (p i)) :
    ∀ s0 ∈ support (startStepsR worldRoles D blank p),
      (∀ i ∈ D.1, s0 i = .done none blank) ∧ ∀ i ∉ D.1, StepTimedR a (s0 i) := by
  intro s0 hs0
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h := Fuel.mem_support_sequenceFin _ s0 hs0 i
    simpa [hi] using h
  · have h := Fuel.mem_support_sequenceFin _ s0 hs0 i
    simp only [hi, ↓reduceIte] at h
    exact timedR_advanceR (hp i hi) _ (Fuel.mem_support_honest _ _ h)

end Rounds

/-! ## Two ghost phases in sequence on the network -/

section Compose

variable {C : Committee} {E : Type} {Ia L R α β ρ : Type} {σ : Type}
  {impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)}
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty PEmpty L R) (blank : ρ)
  (g : C.Party → Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ))

theorem free_continueStepR_done_none (hg : ∀ i record, g i (none, record) = pure (none, record)) (j : C.Party)
    (record : ρ) : free (continueStepR (g j) (RStep.done none record)) = pure (RStep.done none record) := by
  change free (advanceR (g j (none, record))) = _
  rw [hg]
  rfl

/-- `WorldSplit.stepRound_attach_world` for the ghost executor. -/
theorem stepRoundR_attach_world (himpl : FreeCommute impl) (hg : ∀ i record, g i (none, record) = pure (none, record))
    (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ) (hp : ∀ i, (steps i).output = none) :
    WorldRun impl (stepRoundR worldRoles D A F blank st (fun i => attachStepR (g i) (steps i)))
      (stepRoundR worldRoles D A F blank st steps >>= fun r =>
        OverPermutation.sequenceFin (fun j => free (continueStepR (g j) (r.2.1 j))) >>= fun next =>
          pure (r.1, next, r.2.2)) := by
  have hdel : ∀ t, (attachStepR (g t) (steps t)).delivered = (steps t).delivered :=
    fun t => attachStepR_delivered _ _ (hp t)
  have hno := stepRoundR_noCall D (fun i => attachStepR (g i) (steps i))
  have hno' := stepRoundR_noCall D steps
  unfold stepRoundR
  rw [ite_eq_right hno, ite_eq_right hno']
  simp only [attachStepR_outbox, hdel, bind_assoc, pure_bind]
  refine WorldRun.bind_right impl _ fun r => ?_
  refine worldRun_sequenceFin_bind himpl _ _ (fun j s => free (continueStepR (g j) s)) (fun j => ?_)
    (fun j => ?_) (fun j s => isFree_free _) (fun steps' => pure (r.1, steps', r.2))
  · cases hs : steps j with
    | done out record =>
      have ho := hp j
      rw [hs] at ho
      change out = none at ho
      subst ho
      simp only [attachStepR, pure_bind]
      exact (free_continueStepR_done_none g hg j record).symm
    | wait out resume =>
      by_cases hj : j ∈ D.1
      · simp only [attachStepR, hj, ↓reduceIte, pure_bind]
        exact (free_continueStepR_done_none g hg j blank).symm
      · simp only [attachStepR, hj, ↓reduceIte, worldRoles]
        rw [advanceR_bind, free_bind]
    | call input resume => exact input.elim
  · cases hs : steps j with
    | done out record => exact isFree_pure _
    | wait out resume =>
      by_cases hj : j ∈ D.1
      · simp only [hj, ↓reduceIte]
        exact isFree_pure _
      · simp only [hj, ↓reduceIte, worldRoles]
        exact isFree_free _
    | call input resume => exact input.elim

/-- One round of a timed ghost phase with the next phase attached. -/
theorem executeRoundsR_attach_step_world (himpl : FreeCommute impl)
    (hg : ∀ i record, g i (none, record) = pure (none, record)) (b n : ℕ) (st : A.State)
    (steps : C.Party → RStep C E RealSpec α ρ)
    (hD : ∀ i ∈ D.1, steps i = .done none blank) (ht : ∀ i ∉ D.1, StepTimedR (n + 1) (steps i))
    (hrest : ∀ q ∈ support (stepRoundR worldRoles D A F blank st steps),
      WorldRun impl
        (OverPermutation.sequenceFin (fun j => free (continueStepR (g j) (q.2.1 j))) >>= fun next =>
          executeRoundsR worldRoles D A F blank (n + b) q.1 next)
        (executeRoundsR worldRoles D A F blank n q.1 q.2.1 >>= fun r =>
          OverPermutation.sequenceFin (fun i => free (continueStepR (g i) (r.2 i))) >>=
            executeRoundsR worldRoles D A F blank b r.1)) :
    WorldRun impl (executeRoundsR worldRoles D A F blank (n + 1 + b) st (fun i => attachStepR (g i) (steps i)))
      (executeRoundsR worldRoles D A F blank (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => free (continueStepR (g i) (r.2 i))) >>=
          executeRoundsR worldRoles D A F blank b r.1) := by
  have hp : ∀ i, (steps i).output = none := fun i => by
    by_cases hi : i ∈ D.1
    · rw [hD i hi]
      rfl
    · exact (ht i hi).output_none
  have hattach : (fun i => free (continueStepR (g i) (steps i))) = fun i => pure (attachStepR (g i) (steps i)) :=
    funext fun i => by rw [continueStepR_attach (g i) (hg i) _ (hp i), free_pure]
  rw [show n + 1 + b = (n + b) + 1 by omega, executeRoundsR, executeRoundsR]
  by_cases hd : ∀ i, i ∉ D.1 → (steps i).isDone
  · have hd' : ∀ i, i ∉ D.1 → (attachStepR (g i) (steps i)).isDone := fun i hi => (attachStepR_isDone _ _).2 (hd i hi)
    rw [ite_eq_left hd', ite_eq_left hd, pure_bind]
    apply WorldRun.of_eq
    rw [hattach, sequenceFin_pure, pure_bind, executeRoundsR_allDone D A F blank b st _ hd']
  · have hd' : ¬ ∀ i, i ∉ D.1 → (attachStepR (g i) (steps i)).isDone := fun h =>
      hd fun i hi => (attachStepR_isDone _ _).1 (h i hi)
    rw [ite_eq_right hd', ite_eq_right hd]
    refine ((stepRoundR_attach_world D A F blank g himpl hg st steps hp).bind fun q => WorldRun.refl impl _).trans ?_
    simp only [bind_assoc, pure_bind]
    exact WorldRun.bind_support impl _ fun q hq => hrest q hq

/-- The rounds of a timed ghost phase with the next phase attached. -/
theorem executeRoundsR_attach_world (himpl : FreeCommute impl)
    (hg : ∀ i record, g i (none, record) = pure (none, record)) (b : ℕ) :
    ∀ (n : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ),
    (∀ i ∈ D.1, steps i = .done none blank) → (∀ i ∉ D.1, StepTimedR (n + 1) (steps i)) →
    WorldRun impl (executeRoundsR worldRoles D A F blank (n + 1 + b) st (fun i => attachStepR (g i) (steps i)))
      (executeRoundsR worldRoles D A F blank (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => free (continueStepR (g i) (r.2 i))) >>=
          executeRoundsR worldRoles D A F blank b r.1) := by
  intro n
  induction n with
  | zero =>
    intro st steps hD ht
    refine executeRoundsR_attach_step_world D A F blank g himpl hg b 0 st steps hD ht fun q _ => ?_
    simp only [executeRoundsR, pure_bind, Nat.zero_add]
    exact WorldRun.refl impl _
  | succ m ih =>
    intro st steps hD ht
    refine executeRoundsR_attach_step_world D A F blank g himpl hg b (m + 1) st steps hD ht fun q hq => ?_
    obtain ⟨hD', ht'⟩ := stepRoundR_timed D A F blank (m + 1) st steps hD ht q hq
    have hp' : ∀ i, (q.2.1 i).output = none := fun i => by
      by_cases hi : i ∈ D.1
      · rw [hD' i hi]
        rfl
      · exact (ht' i hi).output_none
    have hattach : (fun i => free (continueStepR (g i) (q.2.1 i))) = fun i => pure (attachStepR (g i) (q.2.1 i)) :=
      funext fun i => by rw [continueStepR_attach (g i) (hg i) _ (hp' i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact ih q.1 q.2.1 hD' ht'

/-- The split of a ghost phase on the network, in distribution. Under each handler whose free local
answers commute, a ghost run of the programs `p i >>= g i`, where each honest `p i` gives a result
after exactly `a` rounds or aborts and `g i` keeps the record of an abort, has the law of a ghost run
of `a` rounds on `p` and then a ghost run of `b` rounds on `g i` of the result and the record of each
operator. The law is on the steps with their records, the state of the adversary and the end state of
the handler. -/
theorem executePhaseR_bind_world (himpl : FreeCommute impl)
    (hg : ∀ i record, g i (none, record) = pure (none, record)) (a b : ℕ) (st : A.State)
    (p : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (hp : ∀ i ∉ D.1, TimedR a (p i)) :
    WorldRun impl (executePhaseR worldRoles D A F blank (a + b) st (fun i => p i >>= g i))
      (executePhaseR worldRoles D A F blank a st p >>= fun r =>
        executePhaseR worldRoles D A F blank b r.1 fun i => g i ((r.2 i).output, (r.2 i).record blank)) := by
  unfold executePhaseR
  have hstart : WorldRun impl
      (startStepsR worldRoles D blank (fun i => p i >>= g i) >>= executeRoundsR worldRoles D A F blank (a + b) st)
      (startStepsR worldRoles D blank p >>= fun s0 =>
        OverPermutation.sequenceFin (fun j => free (continueStepR (g j) (s0 j))) >>=
          executeRoundsR worldRoles D A F blank (a + b) st) := by
    unfold startStepsR
    refine worldRun_sequenceFin_bind himpl _ _ (fun j s => free (continueStepR (g j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFree_free _) _
    · by_cases hj : j ∈ D.1
      · simp only [hj, ↓reduceIte, pure_bind]
        exact (free_continueStepR_done_none g hg j blank).symm
      · simp only [hj, ↓reduceIte, worldRoles]
        rw [advanceR_bind, free_bind]
    · by_cases hj : j ∈ D.1
      · simp only [hj, ↓reduceIte]
        exact isFree_pure _
      · simp only [hj, ↓reduceIte, worldRoles]
        exact isFree_free _
  refine hstart.trans ?_
  simp only [bind_assoc]
  refine WorldRun.bind_support impl _ fun s0 hs0 => ?_
  obtain ⟨hD0, ht0⟩ := startStepsR_timed D blank a p hp s0 hs0
  have hfin : WorldRun impl
      (executeRoundsR worldRoles D A F blank a st s0 >>= fun q =>
        OverPermutation.sequenceFin (fun i => free (continueStepR (g i) (q.2 i))) >>=
          executeRoundsR worldRoles D A F blank b q.1)
      (executeRoundsR worldRoles D A F blank a st s0 >>= fun r =>
        startStepsR worldRoles D blank (fun i => g i ((r.2 i).output, (r.2 i).record blank)) >>=
          executeRoundsR worldRoles D A F blank b r.1) := by
    refine WorldRun.bind_support impl _ fun q hq => WorldRun.of_eq ?_
    obtain ⟨hDq, hdq⟩ := executeRoundsR_timed D A F blank a st s0 hD0 ht0 q hq
    congr 1
    unfold startStepsR
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · rw [ite_eq_left hi, hDq i hi]
      exact free_continueStepR_done_none g hg i blank
    · rw [ite_eq_right hi]
      have hdi := hdq i hi
      cases hs : q.2 i with
      | done out record =>
        show _ = worldRoles.honest (advanceR (g i ((q.2 i).output, (q.2 i).record blank)))
        rw [hs]
        rfl
      | wait outbox resume => rw [hs] at hdi; exact hdi.elim
      | call input resume => exact input.elim
  refine WorldRun.trans ?_ hfin
  cases a with
  | zero =>
    simp only [executeRoundsR, pure_bind, Nat.zero_add]
    exact WorldRun.refl impl _
  | succ n =>
    have hp0 : ∀ i, (s0 i).output = none := fun i => by
      by_cases hi : i ∈ D.1
      · rw [hD0 i hi]
        rfl
      · exact (ht0 i hi).output_none
    have hattach : (fun i => free (continueStepR (g i) (s0 i))) = fun i => pure (attachStepR (g i) (s0 i)) :=
      funext fun i => by rw [continueStepR_attach (g i) (hg i) _ (hp0 i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact executeRoundsR_attach_world D A F blank g himpl hg b n st s0 hD0 ht0

end Compose

end GhostSplit

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostSplit.executePhaseR_bind_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostSplit.executePhaseR_bind_world
