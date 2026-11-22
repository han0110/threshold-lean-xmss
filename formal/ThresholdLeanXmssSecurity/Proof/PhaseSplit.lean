import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.PhaseQuiet

/-!
# The split of a phase on the real network

`WorldSplit.executePhase_bind_world` splits a run of `worldRoles` at the end of a timed phase. The
split holds in distribution under each handler whose free local answers commute (`FreeCommute`). The
split changes the order of the local work of the honest operators at the boundary, and it never moves
a step of the adversary. It is `executePhase_bind` of `Proof/CeremonyHybrid/Phase.lean` for the
network roles. `WorldSplit.streamWorld_freeCommute` states that the free local answers of
`streamWorld` commute, and `WorldSplit.executePhase_split` is the split under `streamWorld`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

/-- The state of `streamWorld`, namely the hash cache and the cache of the hidden streams. -/
abbrev StreamState (C : Committee) := HashCache C × HiddenCache C

namespace WorldSplit

attribute [local instance] Classical.propDecidable

/-! ## Runs with the same law -/

section Run

variable {C : Committee} {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))

/-- Two computations on the world oracles that give, under `impl` from each state, the same
distribution of the result and the end state. -/
def WorldRun {α : Type} (oa ob : OracleComp (WorldSpec C) α) : Prop :=
  ∀ s, (simulateQ impl oa).run s =ᵈ (simulateQ impl ob).run s

/-- The free local answers of `impl` commute in pairs. -/
def FreeCommute : Prop := ∀ t t' : (LocalSpec C).Domain, Commutes (impl (.inr t)) (impl (.inr t'))

/-- A computation on the free copy. -/
def IsFree {β : Type} (x : OracleComp (WorldSpec C) β) : Prop := ∃ oa : OracleComp (LocalSpec C) β, x = free oa

theorem WorldRun.refl {α : Type} (oa : OracleComp (WorldSpec C) α) : WorldRun impl oa oa := fun _ => .rfl

theorem WorldRun.bind_right {α β : Type} (oa : OracleComp (WorldSpec C) α)
    {f g : α → OracleComp (WorldSpec C) β} (hfg : ∀ a, WorldRun impl (f a) (g a)) :
    WorldRun impl (oa >>= f) (oa >>= g) := fun s => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact EvalDistEq.bind_right _ fun p => hfg p.1 p.2

theorem WorldRun.bind_support {α β : Type} (oa : OracleComp (WorldSpec C) α)
    {f g : α → OracleComp (WorldSpec C) β} (h : ∀ a ∈ support oa, WorldRun impl (f a) (g a)) :
    WorldRun impl (oa >>= f) (oa >>= g) := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => h z.1 ?_ z.2
  have hsub := support_simulateQ_run'_subset impl oa s
  apply hsub
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

variable {impl}

theorem WorldRun.trans {α : Type} {oa ob oc : OracleComp (WorldSpec C) α} (h : WorldRun impl oa ob)
    (h' : WorldRun impl ob oc) : WorldRun impl oa oc := fun s => (h s).trans (h' s)

theorem WorldRun.bind {α β : Type} {oa ob : OracleComp (WorldSpec C) α} {f g : α → OracleComp (WorldSpec C) β}
    (h : WorldRun impl oa ob) (hfg : ∀ a, WorldRun impl (f a) (g a)) : WorldRun impl (oa >>= f) (ob >>= g) :=
  fun s => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact (h s).bind fun p => hfg p.1 p.2

theorem WorldRun.of_eq {α : Type} {oa ob : OracleComp (WorldSpec C) α} (h : oa = ob) : WorldRun impl oa ob :=
  h ▸ WorldRun.refl impl oa

/-- A run of a free computation is a run with the free answers of the handler. -/
theorem simulateQ_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ impl (free oa) = simulateQ (fun t => impl (.inr t)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [free]
  | query_bind t k ih =>
    simp only [free] at ih ⊢
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rw [simulateQ_HasQuery_query]
    exact bind_congr fun x => ih x

theorem isFree_free {β : Type} (oa : OracleComp (LocalSpec C) β) : IsFree (free oa) := ⟨oa, rfl⟩

theorem isFree_pure {β : Type} (b : β) : IsFree (pure b : OracleComp (WorldSpec C) β) :=
  ⟨pure b, (free_pure b).symm⟩

theorem isFree_sequenceFin {β : Type} {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) β) (h : ∀ i, IsFree (f i)) :
    IsFree (OverPermutation.sequenceFin f) := by
  choose g hg using h
  exact ⟨OverPermutation.sequenceFin g, by rw [free_sequenceFin, ← funext hg]⟩

/-- Lazy sampling. Two free computations commute in distribution. -/
theorem worldRun_swap (himpl : FreeCommute impl) {α β γ : Type} {x : OracleComp (WorldSpec C) α}
    {y : OracleComp (WorldSpec C) β} (hx : IsFree x) (hy : IsFree y) (k : α → β → OracleComp (WorldSpec C) γ) :
    WorldRun impl (do let a ← x; let b ← y; k a b) (do let b ← y; let a ← x; k a b) := by
  obtain ⟨oa, rfl⟩ := hx
  obtain ⟨ob, rfl⟩ := hy
  intro s
  simp only [simulateQ_bind, simulateQ_free]
  exact (commutes_simulateQ (fun t => impl (.inr t)) himpl oa ob).bind _ s

/-- The free steps of `n` operators reorder in distribution, each with its own continuation. -/
theorem worldRun_sequenceFin_dep (himpl : FreeCommute impl) {β₁ β₂ γ : Type} :
    ∀ {n : ℕ} (A : Fin n → OracleComp (WorldSpec C) β₁) (B : Fin n → β₁ → OracleComp (WorldSpec C) β₂)
      (m : Fin n → β₁ → β₂ → γ), (∀ j, IsFree (A j)) → (∀ j u, IsFree (B j u)) →
    WorldRun impl (OverPermutation.sequenceFin fun j => do let u ← A j; let v ← B j u; pure (m j u v))
      (do
        let x ← OverPermutation.sequenceFin A
        let y ← OverPermutation.sequenceFin fun j => B j (x j)
        pure fun j => m j (x j) (y j))
  | 0, A, B, m, _, _ => by
      simp only [OverPermutation.sequenceFin, pure_bind]
      have : (fun j : Fin 0 => m j (Fin.elim0 j) (Fin.elim0 j)) = Fin.elim0 := funext fun j => j.elim0
      rw [this]
      exact WorldRun.refl impl _
  | n + 1, A, B, m, hA, hB => by
      simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
      refine WorldRun.bind_right impl (A 0) fun u => ?_
      refine (WorldRun.bind_right impl (B 0 u) fun v =>
        (worldRun_sequenceFin_dep himpl (fun i : Fin n => A i.succ) (fun i => B i.succ)
          (fun i => m i.succ) (fun i => hA i.succ) (fun i => hB i.succ)).bind fun t =>
            WorldRun.refl impl _).trans ?_
      simp only [bind_assoc, pure_bind]
      refine (worldRun_swap himpl (hB 0 u) (isFree_sequenceFin _ fun i => hA i.succ) _).trans ?_
      refine WorldRun.bind_right impl _ fun x => ?_
      simp only [Fin.cases_zero, Fin.cases_succ]
      refine WorldRun.bind_right impl _ fun v => WorldRun.bind_right impl _ fun y => ?_
      have : (Fin.cases (m 0 u v) fun j => m j.succ (x j) (y j) : Fin (n + 1) → γ) =
          fun j => m j (Fin.cases u x j) (Fin.cases v y j) := by
        funext j
        cases j using Fin.cases <;> rfl
      rw [this]
      exact WorldRun.refl impl _

/-- The free work of the operators and then the free work of their continuations, in the order of the
operators or in two passes. -/
theorem worldRun_sequenceFin_bind (himpl : FreeCommute impl) {β₁ β₂ γ : Type} {n : ℕ}
    (X : Fin n → OracleComp (WorldSpec C) β₂) (U : Fin n → OracleComp (WorldSpec C) β₁)
    (V : Fin n → β₁ → OracleComp (WorldSpec C) β₂) (h : ∀ j, X j = U j >>= V j) (hU : ∀ j, IsFree (U j))
    (hV : ∀ j u, IsFree (V j u)) (f : (Fin n → β₂) → OracleComp (WorldSpec C) γ) :
    WorldRun impl (OverPermutation.sequenceFin X >>= f)
      (OverPermutation.sequenceFin U >>= fun x => OverPermutation.sequenceFin (fun j => V j (x j)) >>= f) := by
  have hX : X = fun j => U j >>= fun u => V j u >>= fun v => pure ((fun _ _ v => v) j u v) := by
    funext j
    simp only [h j, bind_pure]
  have key := worldRun_sequenceFin_dep himpl U V (fun _ _ v => v) hU hV
  rw [← hX] at key
  have := key.bind fun y => WorldRun.refl impl (f y)
  simpa only [bind_assoc, pure_bind] using this

end Run

/-! ## The timed steps of a run on the network -/

section Timed

variable {C : Committee} {E : Type} {I O L R Ia α β : Type}
variable (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- `stepRound_timed` for `worldRoles`. -/
theorem stepRound_timed_world (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimed (n + 1) (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A F st steps),
      (∀ i ∈ D.1, r.2.1 i = .done none) ∧ ∀ i ∉ D.1, StepTimed n (r.2.1 i) := by
  intro r hr
  unfold stepRound at hr
  split_ifs at hr with hc
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨fo, -, steps', hs', rfl⟩ := hr
    have hmem := mem_support_sequenceFin_oc _ _ hs'
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h := hmem i
      rw [hD i hi] at h
      simpa using h
    · have h := hmem i
      have hti := ht i hi
      change StepTimed n (steps' i)
      cases hs : steps i with
      | done out =>
        rw [hs] at h hti
        simp only [support_pure, Set.mem_singleton_iff] at h
        rw [h]
        cases out with
        | none => trivial
        | some a => exact absurd hti (Nat.succ_ne_zero n)
      | wait out resume =>
        have := hc.2 i hi
        simp [hs, Step.callInput, Step.isDone] at this
      | call input resume =>
        rw [hs] at h hti
        obtain ⟨m, hm, htm⟩ := hti
        obtain rfl : n = m := by omega
        simp only [hi, ↓reduceIte, worldRoles] at h
        exact timed_advance (htm _) _ (support_free_subset _ h)
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨fo, -, steps', hs', rfl⟩ := hr
    have hmem := mem_support_sequenceFin_oc _ _ hs'
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h := hmem i
      rw [hD i hi] at h
      simpa using h
    · have h := hmem i
      have hti := ht i hi
      change StepTimed n (steps' i)
      cases hs : steps i with
      | done out =>
        rw [hs] at h hti
        simp only [support_pure, Set.mem_singleton_iff] at h
        rw [h]
        cases out with
        | none => trivial
        | some a => exact absurd hti (Nat.succ_ne_zero n)
      | wait out resume =>
        rw [hs] at h hti
        obtain ⟨m, hm, htm⟩ := hti
        obtain rfl : n = m := by omega
        simp only [hi, ↓reduceIte, worldRoles] at h
        exact timed_advance (htm _) _ (support_free_subset _ h)
      | call input resume =>
        rw [hs] at h
        simp only [support_pure, Set.mem_singleton_iff] at h
        rw [h]
        trivial

/-- `executeSteps_timed` for `worldRoles`. -/
theorem executeSteps_timed_world : ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimed n (steps i)) →
    ∀ r ∈ support (executeSteps worldRoles D A F n st steps),
      (∀ i ∈ D.1, r.2 i = .done none) ∧ ∀ i ∉ D.1, (r.2 i).isDone
  | 0, st, steps, hD, ht => by
    intro r hr
    simp only [executeSteps, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hD, fun i hi => (ht i hi).isDone⟩
  | n + 1, st, steps, hD, ht => by
    intro r hr
    simp only [executeSteps] at hr
    split_ifs at hr with hd
    · rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hD, hd⟩
    · simp only [support_bind, Set.mem_iUnion] at hr
      obtain ⟨q, hq, hr⟩ := hr
      obtain ⟨hD', ht'⟩ := stepRound_timed_world D A F n st steps hD ht q hq
      exact executeSteps_timed_world n q.1 q.2.1 hD' ht' r hr

/-- `startSteps_timed` for `worldRoles`. -/
theorem startSteps_timed_world (a : ℕ) (p : C.Party → PartyM C E (CallSpec I O) α)
    (hp : ∀ i ∉ D.1, Timed a (p i).run) :
    ∀ s0 ∈ support (startSteps worldRoles D p),
      (∀ i ∈ D.1, s0 i = .done none) ∧ ∀ i ∉ D.1, StepTimed a (s0 i) := by
  intro s0 hs0
  have hmem := mem_support_sequenceFin_oc _ _ hs0
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h := hmem i
    simpa [hi] using h
  · have h := hmem i
    simp only [hi, ↓reduceIte, worldRoles] at h
    exact timed_advance (hp i hi) _ (support_free_subset _ h)

end Timed

/-! ## Two phases in sequence on the network -/

section Compose

variable {C : Committee} {E : Type} {I O L R Ia α β : Type} {σ : Type}
  {impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)}
variable (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- `stepRound_attach` for `worldRoles`. One step with the next phase attached is the step, and then
the first free work of the next phase at each operator that finished, in distribution. -/
theorem stepRound_attach_world (himpl : FreeCommute impl) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) (k : C.Party → α → PartyM C E (CallSpec I O) β)
    (hp : ∀ i, (steps i).output = none) :
    WorldRun impl (stepRound worldRoles D A F st (fun i => attachStep (k i) (steps i)))
      (stepRound worldRoles D A F st steps >>= fun r =>
        OverPermutation.sequenceFin (fun j => free (continueStep (k j) (r.2.1 j))) >>= fun next =>
          pure (r.1, next, r.2.2)) := by
  have hdel : ∀ t, (attachStep (k t) (steps t)).delivered = (steps t).delivered :=
    fun t => attachStep_delivered _ _ (hp t)
  unfold stepRound
  simp only [attachStep_callInput, attachStep_isDone]
  split_ifs with hc
  · simp only [bind_assoc, pure_bind]
    refine WorldRun.bind_right impl _ fun r => ?_
    refine worldRun_sequenceFin_bind himpl _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFree_free _) (fun steps' => pure (r.1, steps', fun _ _ => none))
    · cases hs : steps j with
      | done out =>
        have ho := hp j
        rw [hs] at ho
        cases ho
        simp only [attachStep, pure_bind, continueStep, free_pure]
      | wait out resume => simp only [attachStep, pure_bind, continueStep, free_pure]
      | call input resume =>
        by_cases hj : j ∈ D.1
        · simp only [attachStep, hj, ↓reduceIte, pure_bind, continueStep, free_pure]
        · simp only [attachStep, hj, ↓reduceIte, worldRoles]
          rw [advance_bind (OptionT.mk (resume (r.2 j))) (k j), free_bind]
          rfl
    · cases hs : steps j with
      | done out => exact isFree_pure _
      | wait out resume => exact isFree_pure _
      | call input resume =>
        by_cases hj : j ∈ D.1
        · simp only [hj, ↓reduceIte]
          exact isFree_pure _
        · simp only [hj, ↓reduceIte, worldRoles]
          exact isFree_free _
  · simp only [attachStep_outbox, hdel, bind_assoc, pure_bind]
    refine WorldRun.bind_right impl _ fun r => ?_
    refine worldRun_sequenceFin_bind himpl _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFree_free _) (fun steps' => pure (r.1, steps', r.2))
    · cases hs : steps j with
      | done out =>
        have ho := hp j
        rw [hs] at ho
        cases ho
        simp only [attachStep, pure_bind, continueStep, free_pure]
      | wait out resume =>
        by_cases hj : j ∈ D.1
        · simp only [attachStep, hj, ↓reduceIte, pure_bind, continueStep, free_pure]
        · simp only [attachStep, hj, ↓reduceIte, worldRoles]
          rw [advance_bind (OptionT.mk (resume _)) (k j), free_bind]
          rfl
      | call input resume => simp only [attachStep, pure_bind, continueStep, free_pure]
    · cases hs : steps j with
      | done out => exact isFree_pure _
      | wait out resume =>
        by_cases hj : j ∈ D.1
        · simp only [hj, ↓reduceIte]
          exact isFree_pure _
        · simp only [hj, ↓reduceIte, worldRoles]
          exact isFree_free _
      | call input resume => exact isFree_pure _

/-- `executeRounds_attach_step` for `worldRoles`. -/
theorem executeRounds_attach_step_world (himpl : FreeCommute impl) (b : ℕ)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (n : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimed (n + 1) (steps i))
    (hrest : ∀ q ∈ support (stepRound worldRoles D A F st steps),
      WorldRun impl
        (OverPermutation.sequenceFin (fun j => free (continueStep (k j) (q.2.1 j))) >>= fun next =>
          executeRounds worldRoles D A F (n + b) q.1 next)
        (executeSteps worldRoles D A F n q.1 q.2.1 >>= fun r =>
          OverPermutation.sequenceFin (fun i => free (continueStep (k i) (r.2 i))) >>= fun next =>
            executeRounds worldRoles D A F b r.1 next)) :
    WorldRun impl (executeRounds worldRoles D A F (n + 1 + b) st (fun i => attachStep (k i) (steps i)))
      (executeSteps worldRoles D A F (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => free (continueStep (k i) (r.2 i))) >>= fun next =>
          executeRounds worldRoles D A F b r.1 next) := by
  have hp := output_none_of_timed D hD ht
  have hattach : (fun i => free (continueStep (k i) (steps i))) = fun i => pure (attachStep (k i) (steps i)) :=
    funext fun i => by rw [continueStep_attach _ _ (hp i), free_pure]
  rw [show n + 1 + b = (n + b) + 1 by omega, executeRounds, executeSteps]
  simp only [attachStep_isDone]
  split_ifs with hd
  · apply WorldRun.of_eq
    rw [pure_bind, hattach, sequenceFin_pure, pure_bind]
    refine (executeRounds_allDone D A F worldRoles b st _ fun i => ?_).symm
    by_cases hi : i ∈ D.1
    · rw [hD i hi]
      trivial
    · exact (attachStep_isDone _ _).2 (hd i hi)
  · refine ((stepRound_attach_world D A F himpl st steps k hp).bind fun q => WorldRun.refl impl _).trans ?_
    simp only [bind_assoc, pure_bind]
    exact WorldRun.bind_support impl _ fun q hq => hrest q hq

/-- `executeRounds_attach` for `worldRoles`. -/
theorem executeRounds_attach_world (himpl : FreeCommute impl) (b : ℕ)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) :
    ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimed (n + 1) (steps i)) →
    WorldRun impl (executeRounds worldRoles D A F (n + 1 + b) st (fun i => attachStep (k i) (steps i)))
      (executeSteps worldRoles D A F (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => free (continueStep (k i) (r.2 i))) >>= fun next =>
          executeRounds worldRoles D A F b r.1 next) := by
  intro n
  induction n with
  | zero =>
    intro st steps hD ht
    refine executeRounds_attach_step_world D A F himpl b k 0 st steps hD ht fun q _ => ?_
    simp only [executeSteps, pure_bind, Nat.zero_add]
    exact WorldRun.refl impl _
  | succ m ih =>
    intro st steps hD ht
    refine executeRounds_attach_step_world D A F himpl b k (m + 1) st steps hD ht fun q hq => ?_
    obtain ⟨hD', ht'⟩ := stepRound_timed_world D A F (m + 1) st steps hD ht q hq
    have hattach : (fun i => free (continueStep (k i) (q.2.1 i))) =
        fun i => pure (attachStep (k i) (q.2.1 i)) :=
      funext fun i => by rw [continueStep_attach _ _ (output_none_of_timed D hD' ht' i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact ih q.1 q.2.1 hD' ht'

/-- Two phases in sequence on the network, in distribution (GS20, Section 3.1). Under each handler
whose free local answers commute, a run of the programs `p i >>= k i`, where each honest `p i` takes
exactly `a` rounds or calls, has the law of a run of the programs `p i` and then a run of the programs
`k i` on the outputs. The law is on the outputs, the state of the adversary and the end state of the
handler. An operator with no output of the first phase does not start the second phase. -/
theorem executePhase_bind_world (himpl : FreeCommute impl) (a b : ℕ) (st : A.State)
    (p : C.Party → PartyM C E (CallSpec I O) α) (k : C.Party → α → PartyM C E (CallSpec I O) β)
    (hp : ∀ i ∉ D.1, Timed a (p i).run) :
    WorldRun impl (executePhase worldRoles D A F (a + b) st (fun i => p i >>= k i))
      (executePhase worldRoles D A F a st p >>= fun r =>
        executePhase worldRoles D A F b r.1 (fun i => (r.2 i).elim failure (k i))) := by
  unfold executePhase
  have hstart : WorldRun impl
      (startSteps worldRoles D (fun i => p i >>= k i) >>= executeRounds worldRoles D A F (a + b) st)
      (startSteps worldRoles D p >>= fun s0 =>
        OverPermutation.sequenceFin (fun j => free (continueStep (k j) (s0 j))) >>=
          executeRounds worldRoles D A F (a + b) st) := by
    unfold startSteps
    refine worldRun_sequenceFin_bind himpl _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFree_free _) _
    · by_cases hj : j ∈ D.1
      · simp only [hj, ↓reduceIte, pure_bind, continueStep, free_pure]
      · simp only [hj, ↓reduceIte, worldRoles]
        rw [advance_bind (p j) (k j), free_bind]
    · by_cases hj : j ∈ D.1
      · simp only [hj, ↓reduceIte]
        exact isFree_pure _
      · simp only [hj, ↓reduceIte, worldRoles]
        exact isFree_free _
  refine hstart.trans ?_
  simp only [bind_assoc]
  refine WorldRun.bind_support impl _ fun s0 hs0 => ?_
  obtain ⟨hD0, ht0⟩ := startSteps_timed_world D a p hp s0 hs0
  have hfin : WorldRun impl
      (executeSteps worldRoles D A F a st s0 >>= fun q =>
        OverPermutation.sequenceFin (fun i => free (continueStep (k i) (q.2 i))) >>= fun next =>
          executeRounds worldRoles D A F b q.1 next)
      (executeRounds worldRoles D A F a st s0 >>= fun r =>
        startSteps worldRoles D (fun i => (r.2 i).elim failure (k i)) >>=
          executeRounds worldRoles D A F b r.1) := by
    rw [executeRounds_eq_executeSteps, bind_map_left]
    refine WorldRun.bind_support impl _ fun q hq => ?_
    obtain ⟨hDq, hdq⟩ := executeSteps_timed_world D A F a st s0 hD0 ht0 q hq
    exact WorldRun.of_eq (congrArg (· >>= executeRounds worldRoles D A F b q.1)
      (startSteps_elim_of_honest_pure D worldRoles free_pure q.2 k hDq hdq).symm)
  refine WorldRun.trans ?_ hfin
  cases a with
  | zero =>
    simp only [executeSteps, pure_bind, Nat.zero_add]
    exact WorldRun.refl impl _
  | succ n =>
    have hattach : (fun i => free (continueStep (k i) (s0 i))) = fun i => pure (attachStep (k i) (s0 i)) :=
      funext fun i => by rw [continueStep_attach _ _ (output_none_of_timed D hD0 ht0 i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact executeRounds_attach_world D A F himpl b k n st s0 hD0 ht0

end Compose

/-! ## The free answers of `streamWorld` commute -/

section Stream

variable {C : Committee}

/-- A handler of the hidden cache on the second component. -/
def onHidden {α : Type} (m : StateT (HiddenCache C) ProbComp α) :
    StateT (HashCache C × HiddenCache C) ProbComp α :=
  StateT.mk fun st => (fun r => (r.1, (st.1, r.2))) <$> m.run st.2

theorem pair_onHash {α β γ : Type} (x : StateT (HashCache C) ProbComp α) (y : StateT (HashCache C) ProbComp β)
    (f : α → β → γ) (s : HashCache C × HiddenCache C) :
    (do let a ← onHash x; let b ← onHash y; pure (f a b)).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (do let a ← x; let b ← y; pure (f a b)).run s.1 := by
  simp [onHash, StateT.run_bind, map_bind]

theorem pair_onHidden {α β γ : Type} (x : StateT (HiddenCache C) ProbComp α)
    (y : StateT (HiddenCache C) ProbComp β) (f : α → β → γ) (s : HashCache C × HiddenCache C) :
    (do let a ← onHidden x; let b ← onHidden y; pure (f a b)).run s =
      (fun r => (r.1, (s.1, r.2))) <$> (do let a ← x; let b ← y; pure (f a b)).run s.2 := by
  simp [onHidden, StateT.run_bind, map_bind]

theorem commutes_onHash {α β : Type} {x : StateT (HashCache C) ProbComp α} {y : StateT (HashCache C) ProbComp β}
    (h : Commutes x y) : Commutes (onHash x) (onHash y) := fun s => by
  rw [pair_onHash x y Prod.mk s, pair_onHash y x (fun b a => (a, b)) s]
  exact (h s.1).map _

theorem commutes_onHidden {α β : Type} {x : StateT (HiddenCache C) ProbComp α}
    {y : StateT (HiddenCache C) ProbComp β} (h : Commutes x y) : Commutes (onHidden x) (onHidden y) := fun s => by
  rw [pair_onHidden x y Prod.mk s, pair_onHidden y x (fun b a => (a, b)) s]
  exact (h s.2).map _

/-- A step on the hash cache and a step on the hidden cache commute. -/
theorem commutes_onHash_onHidden {α β : Type} (x : StateT (HashCache C) ProbComp α)
    (y : StateT (HiddenCache C) ProbComp β) : Commutes (onHash x) (onHidden y) := fun s => by
  simp only [onHash, onHidden, StateT.run_bind, StateT.run_mk, StateT.run_pure, bind_map_left]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- A free step of `streamWorld` is an atom on the hash cache, or a map of one query of the random
function on the hidden cache. -/
def StreamAtom {α : Type} (m : StateT (HashCache C × HiddenCache C) ProbComp α) : Prop :=
  (∃ m', IsAtom m' ∧ m = onHash m') ∨
    ∃ (q : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) (f : Bit → α),
      m = onHidden (f <$> ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle q))

theorem commutes_of_streamAtom {α β : Type} {x : StateT (HashCache C × HiddenCache C) ProbComp α}
    {y : StateT (HashCache C × HiddenCache C) ProbComp β} (hx : StreamAtom x) (hy : StreamAtom y) :
    Commutes x y := by
  rcases hx with ⟨x', hx', rfl⟩ | ⟨q, f, rfl⟩ <;> rcases hy with ⟨y', hy', rfl⟩ | ⟨q', g, rfl⟩
  · exact commutes_onHash (commutes_of_isAtom hx' hy')
  · exact commutes_onHash_onHidden _ _
  · exact (commutes_onHash_onHidden _ _).symm
  · exact commutes_onHidden (((commutes_randomOracle_randomOracle q q').map_left f).map_right g)

variable (prims : Primitives) (D : C.Coalition)

theorem streamAtom_free (t : (LocalSpec C).Domain) : StreamAtom (streamWorld prims D (.inr t)) := by
  rcases t with n | q | x
  · exact Or.inl ⟨_, isAtom_localAnswer prims _, rfl⟩
  · exact Or.inl ⟨_, isAtom_localAnswer prims _, rfl⟩
  · by_cases hx : Hidden D x.1
    · refine Or.inr ⟨((x.1, x.2.1), x.2.2), id, ?_⟩
      simp only [streamWorld, hx, ↓reduceIte, id_map]
      rfl
    · refine Or.inl ⟨_, isAtom_localAnswer prims (.inr (.inr x)), ?_⟩
      simp only [streamWorld, hx, ↓reduceIte]

/-- The free local answers of `streamWorld` commute in pairs. -/
theorem streamWorld_freeCommute : FreeCommute (streamWorld prims D) := fun t t' =>
  commutes_of_streamAtom (streamAtom_free prims D t) (streamAtom_free prims D t')

/-- The split of a phase on the real network under `streamWorld`. From each state of the adversary and
each world, a run of the programs `p i >>= f i`, where each honest `p i` takes exactly `a` rounds, has
the law of the run of `a` rounds on `p` and then the run of `b` rounds on the continuations. The law
is on the outputs, the state of the adversary and both caches. -/
theorem executePhase_split {E Ia α β : Type} (net : Adversary C E Ia PEmpty PEmpty) (a b : ℕ) (st : net.State)
    (p : C.Party → PartyM C E RealSpec α) (f : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i ∉ D.1, Timed a (p i).run) (w : StreamState C) :
    (simulateQ (streamWorld prims D)
        (executePhase worldRoles D net noFunctionality (a + b) st (fun i => p i >>= f i))).run w =ᵈ
      (simulateQ (streamWorld prims D)
        (executePhase worldRoles D net noFunctionality a st p >>= fun r =>
          executePhase worldRoles D net noFunctionality b r.1 (fun i => (r.2 i).elim failure (f i)))).run w :=
  executePhase_bind_world D net noFunctionality (streamWorld_freeCommute prims D) a b st p f hp w

end Stream

end WorldSplit

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.streamWorld_freeCommute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.streamWorld_freeCommute

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.executePhase_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit.executePhase_split
