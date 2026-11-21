import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Setup

/-!
# The parameter of the seed generation in each world

`seedParameterAgree_any` is `SetupParameter.seedParameterAgree` for each implementation of the world
oracles. The argument reads only the steps of the honest operators and the echo check, so each answer
of a local query is possible.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

open SetupParameter (commitStep revealStep echoStep keysOf)

variable {C : Committee} {E : Type}

section Steps

attribute [local instance] Set.monad

/-- Each answer of each local query. -/
def anyAnswer : QueryImpl (LocalSpec C) Set := fun _ => Set.univ

/-- The next step of an honest operator in a round with the inbox `inbox`, with each answer of the
local queries. -/
def StepAny {α : Type} (inbox : Mail C E) : Step C E RealSpec α → Step C E RealSpec α → Prop
  | .wait _ resume, next => next ∈ simulateQ (anyAnswer (C := C)) (advance (resume inbox))
  | .done out, next => next = .done out
  | .call _ _, next => next = .done none

theorem start_any (i : C.Party) (step : Step C E RealSpec (Keys C))
    (h : step ∈ simulateQ (anyAnswer (C := C)) (advance (seedGen i : PartyM C E RealSpec (Keys C)).run)) :
    ∃ own commitments, step = commitStep i own commitments := by
  rw [SetupParameter.advance_seedGen] at h
  simp only [simulateQ_bind, simulateQ_pure] at h
  obtain ⟨own, -, h⟩ := SetupAgree.mem_setBind.1 h
  obtain ⟨commitments, -, h⟩ := SetupAgree.mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  exact ⟨own, commitments, h⟩

theorem commit_any (inbox : Mail C E) (i : C.Party) (own : Parts C) (commitments : List HashOutput)
    (next : Step C E RealSpec (Keys C)) (h : StepAny inbox (commitStep i own commitments) next) :
    next = .done none ∨ next = revealStep i own inbox := by
  change next ∈ simulateQ anyAnswer (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · right
    rw [advance_exchange_bind, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    exact h

theorem reveal_any (inbox : Mail C E) (i : C.Party) (own : Parts C) (committed : Mail C E)
    (next : Step C E RealSpec (Keys C)) (h : StepAny inbox (revealStep i own committed) next) :
    next = .done none ∨ ∃ keys shared, next = echoStep i keys shared := by
  change next ∈ simulateQ anyAnswer (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · rw [advance_setupRest] at h
    simp only [simulateQ_bind] at h
    obtain ⟨opens, -, h⟩ := SetupAgree.mem_setBind.1 h
    split_ifs at h
    · right
      simp only [simulateQ_bind, simulateQ_pure] at h
      obtain ⟨keys, -, h⟩ := SetupAgree.mem_setBind.1 h
      obtain ⟨shared, -, h⟩ := SetupAgree.mem_setBind.1 h
      rw [Set.pure_def, Set.mem_singleton_iff] at h
      exact ⟨keys, shared, h⟩
    · left
      simpa [Set.pure_def] using h

theorem echo_any (inbox : Mail C E) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (next : Step C E RealSpec (Keys C)) (h : StepAny inbox (echoStep i keys shared) next)
    (K : Keys C) (hout : next.output = some K) :
    echoCheck .seedGen i keys shared inbox ∧ K = keysOf keys := by
  change next ∈ simulateQ anyAnswer (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with ha
  · simp only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    subst h
    cases hout
  · rw [advance_require_bind] at h
    split_ifs at h with hc
    · simp only [advance_run_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      simp only [Step.output, Option.some.injEq] at hout
      exact ⟨hc, hout.symm⟩
    · simp only [simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      cases hout

theorem dead_any {α : Type} (a b : Step C E RealSpec α) (m : Mail C E) (ha : a = .done none)
    (hb : StepAny m a b) : b = .done none := by
  subst ha
  exact hb

/-- The steps of one operator through the three rounds of a seed generation that ends with an
output. -/
theorem trace_any (k : C.Party) (step0 step1 step2 step3 : Step C E RealSpec (Keys C))
    (inbox1 inbox2 inbox3 : Mail C E) (h0 : ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepAny inbox1 step0 step1) (h2 : StepAny inbox2 step1 step2) (h3 : StepAny inbox3 step2 step3)
    (K : Keys C) (hout : step3.output = some K) :
    ∃ keys shared, step2 = echoStep k keys shared ∧ echoCheck .seedGen k keys shared inbox3 ∧ K = keysOf keys := by
  obtain ⟨own, commitments, rfl⟩ := h0
  rcases commit_any inbox1 k own commitments step1 h1 with h1' | rfl
  · have := dead_any _ _ _ (dead_any _ _ _ h1' h2) h3
    subst this
    cases hout
  rcases reveal_any inbox2 k own inbox1 step2 h2 with h2' | ⟨keys, shared, rfl⟩
  · have := dead_any _ _ _ h2' h3
    subst this
    cases hout
  obtain ⟨hcheck, rfl⟩ := echo_any inbox3 k keys shared step3 h3 K hout
  exact ⟨keys, shared, rfl, hcheck, rfl⟩

theorem output_none_one_any (k : C.Party) (step0 step1 : Step C E RealSpec (Keys C)) (inbox1 : Mail C E)
    (h0 : ∃ own commitments, step0 = commitStep k own commitments) (h1 : StepAny inbox1 step0 step1) :
    step1.output = none := by
  obtain ⟨own, commitments, rfl⟩ := h0
  rcases commit_any inbox1 k own commitments step1 h1 with rfl | rfl <;> rfl

theorem output_none_two_any (k : C.Party) (step0 step1 step2 : Step C E RealSpec (Keys C))
    (inbox1 inbox2 : Mail C E) (h0 : ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepAny inbox1 step0 step1) (h2 : StepAny inbox2 step1 step2) : step2.output = none := by
  obtain ⟨own, commitments, rfl⟩ := h0
  rcases commit_any inbox1 k own commitments step1 h1 with rfl | rfl
  · rw [show step2 = .done none from h2]
    rfl
  · rcases reveal_any inbox2 k own inbox1 step2 h2 with rfl | ⟨keys, shared, rfl⟩ <;> rfl

end Steps

section Network

attribute [local instance] Set.monad

variable {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition)

/-- The result of a local computation in each world is a result with some answers of its queries. -/
theorem free_any {β : Type} (oa : OracleComp (LocalSpec C) β) :
    ∀ w z, z ∈ support ((simulateQ impl (free oa)).run w) → z.1 ∈ simulateQ (anyAnswer (C := C)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro w z hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | query_bind t k ih =>
    intro w z hz
    simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, -, hz⟩ := hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact Set.mem_iUnion₂.2 ⟨y.1, trivial, ih y.1 y.2 z hz⟩

/-- Each computation of a sequence gives a value with a property. Then the sequence gives each value
with the property. -/
theorem sequenceFin_any {β : Type} :
    ∀ {n : ℕ} (Q : Fin n → β → Prop) (f : Fin n → OracleComp (WorldSpec C) β),
      (∀ i s y, y ∈ support ((simulateQ impl (f i)).run s) → Q i y.1) →
      ∀ s z, z ∈ support ((simulateQ impl (OverPermutation.sequenceFin f)).run s) → ∀ i, Q i (z.1 i)
  | 0, _, _, _, _, _, _, i => i.elim0
  | n + 1, Q, f, hf, s, z, hz, i => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    cases i using Fin.cases with
    | zero => exact hf 0 s y hy
    | succ i => exact sequenceFin_any (fun i => Q i.succ) (fun i => f i.succ) (fun i => hf i.succ) y.2 w hw i

/-- A round of the honest operators in each world. Each honest operator reads the messages of the
other honest operators as they deliver them, and it takes its next step with some answers. -/
theorem stepRound_any {α : Type} (A : Adversary C E Unit PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : σ)
    (y : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × σ)
    (hy : y ∈ support ((simulateQ impl (stepRound worldRoles D A noFunctionality st steps)).run w)) :
    ∀ j, j ∉ D.1 → StepAny (roundInbox D y.1.2.2 steps j) (steps j) (y.1.2.1 j) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRound at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, -, v, hv, rfl⟩ := hy
  refine sequenceFin_any impl (fun j next => j ∉ D.1 → StepAny (roundInbox D a.1.2 steps j) (steps j) next) _
    (fun j w' u hu hj => ?_) a.2 v hv
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    rfl
  · simp only [hsj, hj, ↓reduceIte] at hu
    exact free_any impl _ w' u hu
  · exact input.elim

theorem executeRounds_succ_any {α : Type} (A : Adversary C E Unit PEmpty PEmpty) (n : ℕ) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : σ) (y : (A.State × (C.Party → Option α)) × σ)
    (hy : y ∈ support ((simulateQ impl (executeRounds worldRoles D A noFunctionality (n + 1) st steps)).run w)) :
    y.1.2 = (fun k => (steps k).output) ∨
      ∃ q ∈ support ((simulateQ impl (stepRound worldRoles D A noFunctionality st steps)).run w),
        y ∈ support ((simulateQ impl (executeRounds worldRoles D A noFunctionality n q.1.1 q.1.2.1)).run q.2) := by
  rw [executeRounds] at hy
  split_ifs at hy
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Or.inl rfl
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨q, hq, hy⟩ := hy
    exact Or.inr ⟨q, hq, hy⟩

theorem executeRounds_zero_any {α : Type} (A : Adversary C E Unit PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : σ) (y : (A.State × (C.Party → Option α)) × σ)
    (hy : y ∈ support ((simulateQ impl (executeRounds worldRoles D A noFunctionality 0 st steps)).run w)) :
    y.1.2 = (fun k => (steps k).output) := by
  simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
  subst hy
  rfl

/-- The first steps of a seed generation. An honest operator waits at its commit round. -/
theorem startSteps_any (w : σ) (a : (C.Party → Step C E RealSpec (Keys C)) × σ)
    (ha : a ∈ support ((simulateQ impl (startSteps worldRoles D
      (fun i => (seedGen i : PartyM C E RealSpec (Keys C))))).run w)) :
    ∀ k, k ∉ D.1 → ∃ own commitments, a.1 k = commitStep k own commitments := by
  unfold startSteps at ha
  refine sequenceFin_any impl (fun k v => k ∉ D.1 → ∃ own commitments, v = commitStep k own commitments)
    _ (fun k w' u hu hk => ?_) w a ha
  simp only [hk, ↓reduceIte, worldRoles] at hu
  exact start_any k u.1 (free_any impl _ w' u hu)

/-- The seed generation on the network in each world from each state of the adversary. Two honest
operators with an output hold the same parameter. -/
theorem seedParameterAgree_any (net : Adversary C E Unit PEmpty PEmpty) (st : net.State) (w : σ)
    (y : (net.State × (C.Party → Option (Keys C))) × σ)
    (hy : y ∈ support ((simulateQ impl (executePhase worldRoles D net noFunctionality setupRounds st
      (fun i => (seedGen i : PartyM C E RealSpec (Keys C))))).run w))
    (i j : C.Party) (Ki Kj : Keys C) (hi : i ∉ D.1) (hj : j ∉ D.1) (hKi : y.1.2 i = some Ki)
    (hKj : y.1.2 j = some Kj) : Ki.parameter = Kj.parameter := by
  by_cases hij : i = j
  · subst hij
    rw [hKi] at hKj
    rw [Option.some.inj hKj]
  unfold executePhase at hy
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨a0, ha0, hy⟩ := hy
  have h0 := startSteps_any impl D w a0 ha0
  rcases executeRounds_succ_any impl D net 2 st a0.1 a0.2 y hy with hout | ⟨q1, hq1, hy⟩
  · exfalso
    obtain ⟨own, commitments, h⟩ := h0 i hi
    simp [hout, h, Step.output, commitStep] at hKi
  have hn1 := stepRound_any impl D net st a0.1 a0.2 q1 hq1
  rcases executeRounds_succ_any impl D net 1 q1.1.1 q1.1.2.1 q1.2 y hy with hout | ⟨q2, hq2, hy⟩
  · exfalso
    simp [hout, output_none_one_any i _ _ _ (h0 i hi) (hn1 i hi)] at hKi
  have hn2 := stepRound_any impl D net q1.1.1 q1.1.2.1 q1.2 q2 hq2
  rcases executeRounds_succ_any impl D net 0 q2.1.1 q2.1.2.1 q2.2 y hy with hout | ⟨q3, hq3, hy⟩
  · exfalso
    simp [hout, output_none_two_any i _ _ _ _ _ (h0 i hi) (hn1 i hi) (hn2 i hi)] at hKi
  have hn3 := stepRound_any impl D net q2.1.1 q2.1.2.1 q2.2 q3 hq3
  have hout := executeRounds_zero_any impl D net q3.1.1 q3.1.2.1 q3.2 y hy
  have htrace : ∀ k, k ∉ D.1 → ∀ K, y.1.2 k = some K →
      ∃ keys shared, q2.1.2.1 k = echoStep k keys shared ∧
        echoCheck .seedGen k keys shared (roundInbox D q3.1.2.2 q2.1.2.1 k) ∧ K = keysOf keys := by
    intro k hk K hK
    rw [hout] at hK
    exact trace_any k _ _ _ _ _ _ _ (h0 k hk) (hn1 k hk) (hn2 k hk) (hn3 k hk) K hK
  obtain ⟨keys, shared, -, hcheck, rfl⟩ := htrace i hi Ki hKi
  obtain ⟨keys', shared', he', -, rfl⟩ := htrace j hj Kj hKj
  have hpar := SetupParameter.parameter_of_echo i j hij keys keys' shared shared' _
    (by simp [roundInbox, hj, he', echoStep]) hcheck
  exact congrArg truncateHash hpar

end Network

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.seedParameterAgree_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.seedParameterAgree_any
