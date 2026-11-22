import ThresholdLeanXmssSecurity.Proof.PhaseSplit

/-!
# The split of a phase on the real network with a restricted commutation

`executePhase_bind_worldQ` is `WorldSplit.executePhase_bind_world` under a weaker premise. The free answers
of a call of the class `Q` commute with each free answer, and the first free work of each continuation
makes only calls of `Q`. The split moves only that work, past the local work of the other operators.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

open WorldSplit

attribute [local instance] Classical.propDecidable

section Run

variable {C : Committee} {σ : Type} {impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)}
  {Q : (LocalSpec C).Domain → Prop}

/-- A computation on the free copy with calls of `Q` only. -/
def IsFreeQ (Q : (LocalSpec C).Domain → Prop) {β : Type} (x : OracleComp (WorldSpec C) β) : Prop :=
  ∃ oa : OracleComp (LocalSpec C) β, x = free oa ∧ AllQueriesSatisfy oa Q

/-- Two simulations commute when each call of the first is in `Q` and each call of `Q` commutes with each
call. -/
theorem commutes_simulateQ_Q {κ : Type} {spec : OracleSpec κ} (I : QueryImpl spec (StateT σ ProbComp))
    (P : κ → Prop) (hI : ∀ t t', P t → Commutes (I t) (I t')) {α β : Type} (oa : OracleComp spec α)
    (hoa : AllQueriesSatisfy oa P) (ob : OracleComp spec β) : Commutes (simulateQ I oa) (simulateQ I ob) := by
  have hquery : ∀ t, P t → ∀ {β : Type} (ob : OracleComp spec β), Commutes (I t) (simulateQ I ob) := by
    intro t ht β ob
    induction ob using OracleComp.inductionOn with
    | pure b => rw [simulateQ_pure]; exact commutes_pure (I t) b
    | query_bind t' k ih =>
        rw [simulateQ_bind, simulateQ_query]
        exact ((hI t t' ht).map_right _).bind_right ih
  induction oa using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact (commutes_pure (simulateQ I ob) a).symm
  | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      rw [simulateQ_bind, simulateQ_query]
      exact ((hquery t hoa.1 ob).map_left _).bind_left fun u => ih u (hoa.2 u)

/-- Lazy sampling. A free computation of `Q` calls commutes with a free computation. -/
theorem worldRun_swapQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t'))) {α β γ : Type}
    {x : OracleComp (WorldSpec C) α} {y : OracleComp (WorldSpec C) β} (hx : IsFreeQ Q x) (hy : IsFree y)
    (k : α → β → OracleComp (WorldSpec C) γ) :
    WorldRun impl (do let a ← x; let b ← y; k a b) (do let b ← y; let a ← x; k a b) := by
  obtain ⟨oa, rfl, hoa⟩ := hx
  obtain ⟨ob, rfl⟩ := hy
  intro s
  simp only [simulateQ_bind, WorldSplit.simulateQ_free (impl := impl)]
  exact (commutes_simulateQ_Q (fun t => impl (.inr t)) Q himpl oa hoa ob).bind _ s

/-- The free steps of `n` operators reorder in distribution, each with its own continuation of `Q`
calls. -/
theorem worldRun_sequenceFin_depQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t')))
    {β₁ β₂ γ : Type} :
    ∀ {n : ℕ} (A : Fin n → OracleComp (WorldSpec C) β₁) (B : Fin n → β₁ → OracleComp (WorldSpec C) β₂)
      (m : Fin n → β₁ → β₂ → γ), (∀ j, IsFree (A j)) → (∀ j u, IsFreeQ Q (B j u)) →
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
        (worldRun_sequenceFin_depQ himpl (fun i : Fin n => A i.succ) (fun i => B i.succ)
          (fun i => m i.succ) (fun i => hA i.succ) (fun i => hB i.succ)).bind fun t =>
            WorldRun.refl impl _).trans ?_
      simp only [bind_assoc, pure_bind]
      refine (worldRun_swapQ himpl (hB 0 u) (isFree_sequenceFin _ fun i => hA i.succ) _).trans ?_
      refine WorldRun.bind_right impl _ fun x => ?_
      simp only [Fin.cases_zero, Fin.cases_succ]
      refine WorldRun.bind_right impl _ fun v => WorldRun.bind_right impl _ fun y => ?_
      have : (Fin.cases (m 0 u v) fun j => m j.succ (x j) (y j) : Fin (n + 1) → γ) =
          fun j => m j (Fin.cases u x j) (Fin.cases v y j) := by
        funext j
        cases j using Fin.cases <;> rfl
      rw [this]
      exact WorldRun.refl impl _

/-- The free work of the operators and then the free work of their continuations of `Q` calls, in the
order of the operators or in two passes. -/
theorem worldRun_sequenceFin_bindQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t')))
    {β₁ β₂ γ : Type} {n : ℕ}
    (X : Fin n → OracleComp (WorldSpec C) β₂) (U : Fin n → OracleComp (WorldSpec C) β₁)
    (V : Fin n → β₁ → OracleComp (WorldSpec C) β₂) (h : ∀ j, X j = U j >>= V j) (hU : ∀ j, IsFree (U j))
    (hV : ∀ j u, IsFreeQ Q (V j u)) (f : (Fin n → β₂) → OracleComp (WorldSpec C) γ) :
    WorldRun impl (OverPermutation.sequenceFin X >>= f)
      (OverPermutation.sequenceFin U >>= fun x => OverPermutation.sequenceFin (fun j => V j (x j)) >>= f) := by
  have hX : X = fun j => U j >>= fun u => V j u >>= fun v => pure ((fun _ _ v => v) j u v) := by
    funext j
    simp only [h j, bind_pure]
  have key := worldRun_sequenceFin_depQ himpl U V (fun _ _ v => v) hU hV
  rw [← hX] at key
  have := key.bind fun y => WorldRun.refl impl (f y)
  simpa only [bind_assoc, pure_bind] using this

end Run

section Compose

variable {C : Committee} {E : Type} {I O L R Ia α β : Type} {σ : Type}
  {impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)} {Q : (LocalSpec C).Domain → Prop}
variable (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- The first free work of a continuation makes only calls of `Q`. -/
theorem isFreeQ_continueStep (k : α → PartyM C E (CallSpec I O) β)
    (hk : ∀ a, AllQueriesSatisfy (advance (k a).run) Q) (s : Step C E (CallSpec I O) α) :
    IsFreeQ Q (free (continueStep k s)) := by
  refine ⟨_, rfl, ?_⟩
  cases s with
  | done out =>
    cases out with
    | none => exact allQueriesSatisfy_pure _ _
    | some a => exact hk a
  | wait out resume => exact allQueriesSatisfy_pure _ _
  | call input resume => exact allQueriesSatisfy_pure _ _

/-- `stepRound_attach_world` with the restricted commutation. -/
theorem stepRound_attach_worldQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t')))
    (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α) (k : C.Party → α → PartyM C E (CallSpec I O) β)
    (hk : ∀ i a, AllQueriesSatisfy (advance (k i a).run) Q) (hp : ∀ i, (steps i).output = none) :
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
    refine worldRun_sequenceFin_bindQ himpl _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFreeQ_continueStep (k j) (hk j) s) (fun steps' => pure (r.1, steps', fun _ _ => none))
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
    refine worldRun_sequenceFin_bindQ himpl _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFreeQ_continueStep (k j) (hk j) s) (fun steps' => pure (r.1, steps', r.2))
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

/-- `executeRounds_attach_step_world` with the restricted commutation. -/
theorem executeRounds_attach_step_worldQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t')))
    (b : ℕ) (k : C.Party → α → PartyM C E (CallSpec I O) β) (hk : ∀ i a, AllQueriesSatisfy (advance (k i a).run) Q)
    (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
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
  · refine ((stepRound_attach_worldQ D A F himpl st steps k hk hp).bind fun q => WorldRun.refl impl _).trans ?_
    simp only [bind_assoc, pure_bind]
    exact WorldRun.bind_support impl _ fun q hq => hrest q hq

/-- `executeRounds_attach_world` with the restricted commutation. -/
theorem executeRounds_attach_worldQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t')))
    (b : ℕ) (k : C.Party → α → PartyM C E (CallSpec I O) β) (hk : ∀ i a, AllQueriesSatisfy (advance (k i a).run) Q) :
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
    refine executeRounds_attach_step_worldQ D A F himpl b k hk 0 st steps hD ht fun q _ => ?_
    simp only [executeSteps, pure_bind, Nat.zero_add]
    exact WorldRun.refl impl _
  | succ m ih =>
    intro st steps hD ht
    refine executeRounds_attach_step_worldQ D A F himpl b k hk (m + 1) st steps hD ht fun q hq => ?_
    obtain ⟨hD', ht'⟩ := stepRound_timed_world D A F (m + 1) st steps hD ht q hq
    have hattach : (fun i => free (continueStep (k i) (q.2.1 i))) =
        fun i => pure (attachStep (k i) (q.2.1 i)) :=
      funext fun i => by rw [continueStep_attach _ _ (output_none_of_timed D hD' ht' i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact ih q.1 q.2.1 hD' ht'

/-- Two phases in sequence on the network, in distribution, under the restricted commutation. The first
free work of each continuation makes only calls of `Q`, and each such call commutes with each free
call. -/
theorem executePhase_bind_worldQ (himpl : ∀ t t', Q t → Commutes (impl (.inr t)) (impl (.inr t')))
    (a b : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α) (k : C.Party → α → PartyM C E (CallSpec I O) β)
    (hk : ∀ i x, AllQueriesSatisfy (advance (k i x).run) Q) (hp : ∀ i ∉ D.1, Timed a (p i).run) :
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
    refine worldRun_sequenceFin_bindQ himpl _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_)
      (fun j => ?_) (fun j s => isFreeQ_continueStep (k j) (hk j) s) _
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
    exact executeRounds_attach_worldQ D A F himpl b k hk n st s0 hD0 ht0

end Compose

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.executePhase_bind_worldQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.executePhase_bind_worldQ
