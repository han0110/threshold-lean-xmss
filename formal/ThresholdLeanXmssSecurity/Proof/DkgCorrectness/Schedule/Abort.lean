import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningReach

/-!
# A short phase and the abort before a check

`shortFuel` proves `ShortFuel`. Each honest program of one ceremony takes exactly `ceremonyRounds`
rounds, so a phase with fewer rounds ends with no honest output (`executePhase_support_short`).

`ceremonyAbort` proves `CeremonyAbort`. The ghost executor moves the honest operators in lock step
to the exchange of `OpenRep` of batch `k` (`executePhaseR_wait`). At that round each honest
operator waits there, or it aborted before. An honest output needs an opening of batch `k` with no
abort frame in its mail, so no honest operator aborted before, and each honest record after that
round holds the start of check `k`. With enough rounds each honest operator ends the phase
(`executePhaseR_done`), so its record is not blank. With too few rounds `ShortFuel` gives no output.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

open LiveRounds RecordedOpening

/-! ## A phase with fewer rounds than its programs -/

section Short

variable {C : Committee} {E : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- A phase of fewer rounds than the exact rounds of the honest programs gives no honest output. -/
theorem executePhase_support_short {α : Type} (a fuel : ℕ) (hlt : fuel < a) (st : net.State)
    (program : C.Party → PartyM C E RealSpec α) (hp : ∀ i ∉ D.1, Timed a (program i).run) :
    ∀ z ∈ support (executePhase worldRoles D net noFunctionality fuel st program), ∀ i, i ∉ D.1 → z.2 i = none := by
  intro z hz
  unfold executePhase at hz
  simp only [support_bind, Set.mem_iUnion] at hz
  obtain ⟨s0, hs0, hz⟩ := hz
  obtain ⟨hD, ht⟩ := WorldSplit.startSteps_timed_world D a program hp s0 hs0
  obtain ⟨n, rfl⟩ : ∃ n, a = fuel + n + 1 := ⟨a - fuel - 1, by omega⟩
  exact executeRounds_short D net n fuel st s0 hD ht z hz

end Short

/-! ## `ShortFuel` -/

section Fuel

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The program of one ceremony at an operator with keys takes exactly `ceremonyRounds` rounds
under the parameter of its keys. -/
theorem timed_ceremonyProgram_exact (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hk : c.keys i = some keys) :
    Timed (CheckTiming.ceremonyRounds circuits settings keys.parameter c.jobs)
      (ceremonyProgram K circuits settings i c).run := by
  simp only [ceremonyProgram, hk]
  rw [← Nat.add_zero (CheckTiming.ceremonyRounds _ _ _ _)]
  refine (CheckTiming.runTimed_ceremonyRun_exact K circuits settings i keys c.jobs c.counters).bind fun p => ?_
  rcases p with ⟨_ | outputs, st⟩
  · exact timed_failure 0
  · exact timed_pure _

omit [Fintype E] [DecidableEq E] in
theorem mem_support_phase {α : Type} (D : C.Coalition) (oa : OracleComp (WorldSpec C) α) (world : StreamState C)
    (r : α × StreamState C) (hr : r ∈ support ((simulateQ (streamWorld prims D) oa).run world)) : r.1 ∈ support oa :=
  support_simulateQ_run'_subset (streamWorld prims D) oa world (by rw [StateT.run'_eq, support_map]; exact ⟨r, hr, rfl⟩)

/-- A phase of one ceremony with fewer rounds than `ceremonyRounds` under the parameter of the game,
from consistent keys, gives no honest output. An honest operator with no keys stops each honest
operator in the first round of the PRSS setup (`ceremonyDead`). Otherwise each honest program takes
exactly `ceremonyRounds` rounds. -/
theorem ceremonyPhase_short (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (hlt : rounds < CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs)
    (r : (net.State × (C.Party → Option CeremonyResult)) × StreamState C)
    (hr : r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world)) :
    ∀ i, i ∉ D.1 → r.1.2 i = none := by
  intro i hi
  by_cases hdead : ∃ j, j ∉ D.1 ∧ c.keys j = none
  · exact ceremonyDead prims K circuits settings D net rounds c world r hr hdead i hi
  push Not at hdead
  refine executePhase_support_short D net _ rounds hlt c.adversary _ (fun j hj => ?_) r.1
    (mem_support_phase prims D _ world r hr) i hi
  obtain ⟨keys, hk⟩ := Option.ne_none_iff_exists'.1 (hdead j hj)
  rw [← parameter_eq_gameParameter D c.keys hseeds j hj keys hk]
  exact timed_ceremonyProgram_exact K circuits settings j c keys hk

/-- `ceremonyPhase_short` gives `ShortFuel`. -/
theorem shortFuel : ShortFuel prims K circuits settings :=
  fun D net rounds _ c world hready hlt r hr =>
    ceremonyPhase_short prims K circuits settings D net rounds c world hready.1 hlt r hr

end Fuel

/-! ## The lock step of the ghost executor up to a wait -/

section Lockstep

variable {C : Committee} {E : Type} {Ia L Rs O α ρ : Type}

/-- The local steps of a program that reaches its wait of depth `n` stop at a step that reaches it. -/
theorem reach_advanceR {P : Option α × ρ → Prop}
    {Q : Mail C E → (Mail C E → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ)) → Prop} {n : ℕ}
    {p : OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ)} (h : Reach P Q n p) :
    ∀ s ∈ support (advanceR p), StepReach P Q n s := by
  induction h with
  | early n x hx =>
    intro s hs
    change s ∈ support (pure (RStep.done x.1 x.2) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact hx
  | queryLocal n q k _ ih =>
    intro s hs
    change s ∈ support (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (k r)) at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨r, -, hr⟩ := hs
    exact ih r s hr
  | here out k h =>
    intro s hs
    change s ∈ support (pure (RStep.wait out k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact h
  | round n out k h _ =>
    intro s hs
    change s ∈ support (pure (RStep.wait out k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact h

variable (D : C.Coalition) (net : Adversary C E Ia L Rs) (F : Functionality C PEmpty O L Rs) (blank : ρ)
  (P : C.Party → Option α × ρ → Prop)
  (Q : C.Party → Mail C E → (Mail C E → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ)) → Prop)

/-- The outputs of the next step of an honest step are outputs of the rest of its program. -/
theorem stepOutputs_stepNext (step : RStep C E (CallSpec PEmpty O) α ρ) (inbox : Mail C E) :
    ∀ s ∈ support (stepNext blank step inbox), stepOutputs s ⊆ support (nextR blank step inbox) := by
  intro s hs
  cases step with
  | done out record =>
    rw [stepNext, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, nextR, support_pure]
    rfl
  | wait outbox resume => exact stepOutputs_advanceR _ s hs
  | call input resume => exact input.elim

theorem nextR_subset (step : RStep C E (CallSpec PEmpty O) α ρ) (inbox : Mail C E) :
    support (nextR blank step inbox) ⊆ stepOutputs step := by
  cases step with
  | done out record =>
    intro x hx
    rw [nextR, support_pure] at hx
    exact hx
  | wait outbox resume => exact Set.subset_iUnion (fun inbox => support (resume inbox)) inbox
  | call input resume => exact input.elim

/-- The rounds of the ghost executor keep the outputs of each honest step among the outputs of the
honest step of the start. -/
theorem executeRoundsR_stepOutputs :
    ∀ (fuel : ℕ) (state : net.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ),
      ∀ z ∈ support (executeRoundsR worldRoles D net F blank fuel state steps), ∀ i, i ∉ D.1 →
        stepOutputs (z.2 i) ⊆ stepOutputs (steps i)
  | 0, state, steps, z, hz, i, hi => by
    simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | fuel + 1, state, steps, z, hz, i, hi => by
    unfold executeRoundsR at hz
    split_ifs at hz
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_rfl
    · rw [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      exact (executeRoundsR_stepOutputs fuel r.1 r.2.1 z hz i hi).trans
        ((stepOutputs_stepNext blank (steps i) _ _ (stepRoundR_next D net F blank state steps r hr i hi)).trans
          (nextR_subset blank (steps i) _))

/-- A round of the ghost executor takes each honest step from depth `n + 1` to depth `n`. -/
theorem stepRoundR_reach (n : ℕ) (state : net.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ)
    (h : ∀ i, i ∉ D.1 → StepReach (P i) (Q i) (n + 1) (steps i)) :
    ∀ r ∈ support (stepRoundR worldRoles D net F blank state steps), ∀ i, i ∉ D.1 →
      StepReach (P i) (Q i) n (r.2.1 i) := by
  intro r hr i hi
  have hn := stepRoundR_next D net F blank state steps r hr i hi
  have hs := h i hi
  revert hn hs
  cases steps i with
  | done out record =>
    intro hn hs
    rw [stepNext, support_pure, Set.mem_singleton_iff] at hn
    rw [hn]
    exact hs
  | wait outbox resume =>
    intro hn hs
    exact reach_advanceR (hs _) _ hn
  | call input resume => exact input.elim

theorem stepReach_done {m : ℕ} {i : C.Party} {step : RStep C E (CallSpec PEmpty O) α ρ}
    (h : StepReach (P i) (Q i) m step) (hd : step.isDone) : P i (step.output, step.record blank) := by
  cases step with
  | done out record => exact h
  | wait outbox resume => exact hd.elim
  | call input resume => exact hd.elim

/-- The lock step of the ghost executor up to a wait. From honest steps at depth `n`, at the end each
honest step that is done has a leaf in `P`, or there is a round where each honest step is done with a
leaf in `P` or waits at depth `0`, and the outputs of each final honest step are outputs of the rest
of its program on the mail of that round. -/
theorem executeRoundsR_wait :
    ∀ (n fuel : ℕ) (state : net.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ),
      (∀ i, i ∉ D.1 → StepReach (P i) (Q i) n (steps i)) →
      ∀ z ∈ support (executeRoundsR worldRoles D net F blank fuel state steps),
        (∀ i, i ∉ D.1 → (z.2 i).isDone → P i ((z.2 i).output, (z.2 i).record blank)) ∨
        ∃ (steps₀ : C.Party → RStep C E (CallSpec PEmpty O) α ρ) (sent : C.Party → C.Party → Option (Msg E)),
          (∀ i, i ∉ D.1 → StepReach (P i) (Q i) 0 (steps₀ i)) ∧
          ∀ i, i ∉ D.1 → stepOutputs (z.2 i) ⊆ support (nextR blank (steps₀ i) (LiveRounds.roundInbox D steps₀ sent i)) := by
  intro n
  induction n with
  | zero =>
    intro fuel state steps h z hz
    rcases fuel with _ | fuel
    · simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl fun i hi hd => stepReach_done blank P Q (h i hi) hd
    unfold executeRoundsR at hz
    split_ifs at hz with hall
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl fun i hi hd => stepReach_done blank P Q (h i hi) hd
    rw [mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    refine Or.inr ⟨steps, r.2.2, h, fun i hi => ?_⟩
    exact (executeRoundsR_stepOutputs D net F blank fuel r.1 r.2.1 z hz i hi).trans
      (stepOutputs_stepNext blank (steps i) _ _ (stepRoundR_next D net F blank state steps r hr i hi))
  | succ n ih =>
    intro fuel state steps h z hz
    rcases fuel with _ | fuel
    · simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl fun i hi hd => stepReach_done blank P Q (h i hi) hd
    unfold executeRoundsR at hz
    split_ifs at hz with hall
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl fun i hi hd => stepReach_done blank P Q (h i hi) hd
    rw [mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    exact ih fuel r.1 r.2.1 (stepRoundR_reach D net F blank P Q n state steps h r hr) z hz

/-- `executeRoundsR_wait` from the start of a ghost phase, with programs that reach their wait of
depth `n`. -/
theorem executePhaseR_wait (n fuel : ℕ) (state : net.State)
    (program : C.Party → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ))
    (h : ∀ i, i ∉ D.1 → Reach (P i) (Q i) n (program i)) :
    ∀ z ∈ support (executePhaseR worldRoles D net F blank fuel state program),
      (∀ i, i ∉ D.1 → (z.2 i).isDone → P i ((z.2 i).output, (z.2 i).record blank)) ∨
      ∃ (steps₀ : C.Party → RStep C E (CallSpec PEmpty O) α ρ) (sent : C.Party → C.Party → Option (Msg E)),
        (∀ i, i ∉ D.1 → StepReach (P i) (Q i) 0 (steps₀ i)) ∧
        ∀ i, i ∉ D.1 → stepOutputs (z.2 i) ⊆ support (nextR blank (steps₀ i) (LiveRounds.roundInbox D steps₀ sent i)) := by
  intro z hz
  unfold executePhaseR at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨steps, hsteps, hz⟩ := hz
  refine executeRoundsR_wait D net F blank P Q n fuel state steps (fun i hi => ?_) z hz
  have hj := Fuel.mem_support_sequenceFin _ steps hsteps i
  simp only [hi, ↓reduceIte] at hj
  exact reach_advanceR (h i hi) _ (Fuel.mem_support_honest _ _ hj)

end Lockstep

/-! ## The lock step of one ceremony -/

section Started

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem fst_recCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Prod.fst <$> (recCeremony K circuits settings i c).run.run = (ceremonyProgram K circuits settings i c).run := by
  rw [← dropRec_recCeremony]
  rfl

/-- The lock step of one ceremony from consistent keys at each honest operator. With an honest
output at the end of the ghost run, each honest operator recorded the start of check `k`. -/
theorem started_of_output (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (hkeys : ∀ i, i ∉ D.1 → (c.keys i).isSome)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world))
    (hout : ∃ i, i ∉ D.1 ∧ (ω.1.2 i).output.isSome) (k : ℕ) (hk : k < (chunks settings.batchSize c.jobs).length) :
    StartedAt D k ω.1.2 := by
  obtain ⟨j, hj, hjout⟩ := hout
  have hparam : ∀ i, i ∉ D.1 → ∃ keys, c.keys i = some keys ∧ keys.parameter = gameParameter D c.keys := by
    intro i hi
    obtain ⟨keys, hk'⟩ := Option.isSome_iff_exists.1 (hkeys i hi)
    exact ⟨keys, hk', parameter_eq_gameParameter D c.keys hseeds i hi keys hk'⟩
  by_cases hfuel : rounds < CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs
  · have hr : ((ω.1.1, ceremonyOutputs ω.1.2), ω.2) ∈
        support ((ceremonyPhase prims K circuits settings D net rounds c).run world) := by
      rw [ghostCeremony_erase, support_map]
      exact ⟨ω, hω, rfl⟩
    have hnone := ceremonyPhase_short prims K circuits settings D net rounds c world hseeds hfuel _ hr j hj
    change (ω.1.2 j).output = none at hnone
    rw [hnone] at hjout
    exact absurd hjout (by simp)
  have hω1 : ω.1 ∈ support (executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds c.adversary
      fun i => (recCeremony K circuits settings i c).run.run) :=
    mem_support_phase prims D _ world ω hω
  have hdone := Fuel.executePhaseR_done D net noFunctionality ([] : Record C E) rounds _ (not_lt.1 hfuel)
    c.adversary _ (fun i hi => by
      obtain ⟨keys, hk', hp⟩ := hparam i hi
      rw [fst_recCeremony, ← hp]
      exact Fuel.Within.of_timed (timed_ceremonyProgram_exact K circuits settings i c keys hk')) ω.1 hω1
  have hreach : ∀ i, i ∉ D.1 → Reach (Stop k) (WaitAt K i k)
      (setupRounds + ((((chunks settings.batchSize c.jobs).take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits (gameParameter D c.keys) ·.kind))).sum +
        (CheckTiming.exactBatchRounds settings.mode
          (((chunks settings.batchSize c.jobs)[k]).map (circuits (gameParameter D c.keys) ·.kind)) - 1)))
      (recCeremony K circuits settings i c).run.run := by
    intro i hi
    obtain ⟨keys, hk', hp⟩ := hparam i hi
    simp only [recCeremony, hk']
    rw [← hp]
    exact reach_recBind_left K _ (reach_recRun K circuits settings i keys c.jobs k hk c.counters)
  rcases executePhaseR_wait D net noFunctionality ([] : Record C E) (fun _ => Stop k) (fun i => WaitAt K i k) _
    rounds c.adversary _ hreach ω.1 hω1 with hleft | ⟨steps₀, sent, hsteps₀, hpath⟩
  · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hjout
    have h := (hleft j hj (hdone j hj)).1
    rw [ho] at h
    cases h
  · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hjout
    have hjdone := hdone j hj
    have hxj : ((ω.1.2 j).output, (ω.1.2 j).record []) ∈ stepOutputs (ω.1.2 j) := by
      cases hs : ω.1.2 j with
      | done out record => exact rfl
      | wait outbox resume => rw [hs] at hjdone; exact hjdone.elim
      | call input resume => exact input.elim
    have hxj' := hpath j hj hxj
    rw [ho] at hxj'
    have hno : ∀ c, LiveRounds.roundInbox D steps₀ sent j c ≠ some .abort := by
      have hsj := hsteps₀ j hj
      revert hxj' hsj
      cases steps₀ j with
      | done out record =>
        intro hx hsj
        rw [nextR, support_pure, Set.mem_singleton_iff] at hx
        have h := hsj.1
        simp only [Prod.mk.injEq] at hx
        rw [← hx.1] at h
        cases h
      | wait outbox resume =>
        intro hx hsj
        obtain ⟨b, digests, -, hw⟩ := hsj
        obtain ⟨-, hopen, hinbox⟩ := hw _ _ hx
        exact (hinbox _ _ (List.getElem?_eq_getElem (hopen (by simp)))).2
      | call input resume => exact fun _ hsj => hsj.elim
    intro i hi
    have hsi := hsteps₀ i hi
    have hidone := hdone i hi
    have hxi : ((ω.1.2 i).output, (ω.1.2 i).record []) ∈ stepOutputs (ω.1.2 i) := by
      cases hs : ω.1.2 i with
      | done out record => exact rfl
      | wait outbox resume => rw [hs] at hidone; exact hidone.elim
      | call input resume => exact input.elim
    have hxi' := hpath i hi hxi
    unfold ceremonyRecord
    cases hs₀ : steps₀ i with
    | done out record =>
      rw [hs₀] at hsi
      refine absurd ?_ (hno i)
      simp only [LiveRounds.roundInbox, hi, ↓reduceIte, hs₀]
      rw [show out = none from (hsi : Stop k (out, record)).1]
      rfl
    | wait outbox resume =>
      rw [hs₀] at hsi hxi'
      obtain ⟨b, digests, -, hw⟩ := hsi
      rw [(hw _ _ hxi').1]
      rfl
    | call input resume => exact input.elim

/-- `started_of_output` gives `CeremonyStarted`. It uses no premise on the hash cache and no premise
on the batch size. -/
theorem ceremonyStarted : CeremonyStarted prims K circuits settings :=
  fun _ D net rounds c world _ hseeds hkeys ω hω _ hout k hk =>
    started_of_output prims K circuits settings D net rounds c world hseeds hkeys ω hω hout k hk

/-- The proof of `CeremonyAbort`. An honest operator with no keys stops each honest operator in the
first round of the PRSS setup (`ceremonyDead`). Otherwise an honest output gives the start of check
`k` at each honest operator (`started_of_output`). -/
theorem ceremonyAbort : CeremonyAbort prims K circuits settings := by
  intro D net rounds ℓ c world hready ω hω _ k hk hmissing i hi
  by_cases hdead : ∃ j, j ∉ D.1 ∧ c.keys j = none
  · have hr : ((ω.1.1, ceremonyOutputs ω.1.2), ω.2) ∈
        support ((ceremonyPhase prims K circuits settings D net rounds c).run world) := by
      rw [ghostCeremony_erase, support_map]
      exact ⟨ω, hω, rfl⟩
    exact ceremonyDead prims K circuits settings D net rounds c world _ hr hdead i hi
  push Not at hdead
  by_contra hout
  exact hmissing (started_of_output prims K circuits settings D net rounds c world hready.1
    (fun j hj => Option.isSome_iff_ne_none.2 (hdead j hj)) ω hω ⟨i, hi, Option.isSome_iff_ne_none.2 hout⟩ k hk)

end Started

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.shortFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.shortFuel

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyStarted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyStarted

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyAbort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyAbort
