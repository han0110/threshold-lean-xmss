import ThresholdLeanXmssSecurity.Proof.MainStages
import ThresholdLeanXmssSecurity.Proof.StreamWorld

/-!
# Two phases in sequence

The honest programs of GS20 are synchronous (GS20, Section 3.1). Each program takes a public number
of rounds and calls. So a run of the programs `p i >>= k i` is a run of the programs `p i`, and then
a run of the programs `k i` on the outputs. An operator that aborts in the first phase does not start
the second phase.

* `Timed n p` states that the program `p` takes exactly `n` rounds or calls on each path that does
  not abort.
* `executePhase_bind` splits a run at the end of a timed phase. The split holds in distribution from
  every cache (`SameRun`), because the local work at the boundary changes its order.
* `executePhase_partial` is the run after a partial abort. If an honest operator did not start, each
  other honest operator stops at its first call, and the adversary gets no step.

Each lemma holds for every hybrid model, every adversary and every coalition.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Timed programs -/

section Timed

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- A program that takes exactly `n` rounds or calls on each path that does not abort. -/
inductive Timed {α : Type} : ℕ → OracleComp (PartySpec C E G) (Option α) → Prop
  | abort (n : ℕ) : Timed n (pure none)
  | done (a : α) : Timed 0 (pure (some a))
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, Timed n (k r)) : Timed n (.liftBind (.inl (.inl q)) k)
  | round (n : ℕ) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, Timed n (k r)) : Timed (n + 1) (.liftBind (.inl (.inr out)) k)
  | call (n : ℕ) (input : ι) (k : G input → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, Timed n (k r)) : Timed (n + 1) (.liftBind (.inr input) k)

/-- A stopped program that needs exactly `n` more rounds or calls, unless it aborts. -/
def StepTimed {α : Type} (n : ℕ) : Step C E G α → Prop
  | .done none => True
  | .done (some _) => n = 0
  | .wait _ resume => ∃ m, n = m + 1 ∧ ∀ inbox, Timed m (resume inbox)
  | .call _ resume => ∃ m, n = m + 1 ∧ ∀ r, Timed m (resume r)

/-- The local steps of a timed program stop at a timed step. -/
theorem timed_advance {α : Type} {n : ℕ} {p : OracleComp (PartySpec C E G) (Option α)} (h : Timed n p) :
    ∀ step ∈ support (advance p), StepTimed n step := by
  induction h with
  | abort n =>
    intro step hs
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    trivial
  | done a =>
    intro step hs
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    rfl
  | queryLocal n q k _ ih =>
    intro step hs
    change step ∈ support (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)) at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨r, -, hr⟩ := hs
    exact ih r step hr
  | round n out k h _ =>
    intro step hs
    change step ∈ support (pure (Step.wait out k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨n, rfl, h⟩
  | call n input k h _ =>
    intro step hs
    change step ∈ support (pure (Step.call input k) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨n, rfl, h⟩

/-- The number of rounds and calls of a sequence is the sum of the two numbers. -/
theorem Timed.bind {α β : Type} {m n : ℕ} {p : PartyM C E G α} {k : α → PartyM C E G β}
    (hp : Timed m p.run) (hk : ∀ a, Timed n (k a).run) : Timed (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change Timed (m + n) (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | abort m => simpa only [pure_bind, Option.elim_none] using Timed.abort (α := β) (m + n)
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hk a
  | queryLocal m q f _ ih => exact Timed.queryLocal (m + n) q _ ih
  | round m out f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Timed.round (m + n) out _ ih
  | call m input f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Timed.call (m + n) input _ ih

theorem timed_pure {α : Type} (a : α) : Timed 0 (pure a : PartyM C E G α).run := Timed.done a

theorem timed_failure {α : Type} (n : ℕ) : Timed n (failure : PartyM C E G α).run := Timed.abort n

/-- A map of the result takes no round. -/
theorem Timed.map {α β : Type} {n : ℕ} {p : PartyM C E G α} (f : α → β) (hp : Timed n p.run) :
    Timed n (f <$> p).run := by
  have h := hp.bind (k := fun a => (Pure.pure (f a) : PartyM C E G β)) fun a => timed_pure (f a)
  rw [Nat.add_zero] at h
  rw [map_eq_bind_pure_comp]
  exact h

/-- Local work takes no round. -/
theorem Timed.localStep_bind {α β : Type} (n : ℕ) (oa : OracleComp (LocalSpec C) α)
    (k : α → PartyM C E G β) (hk : ∀ a, Timed n (k a).run) : Timed n (localStep oa >>= k).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_assoc, pure_bind,
    Option.elim_some]
  change Timed n (liftComp oa (PartySpec C E G) >>= fun a => (k a).run)
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [liftComp_pure, pure_bind] using hk a
  | query_bind q f ih =>
    simp only [liftComp_bind, liftComp_query, bind_assoc]
    have hq : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (PartySpec C E G) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inl (.inl q))) := by
      rw [← liftM_query_local]
      rfl
    rw [hq]
    exact Timed.queryLocal n q _ ih

/-- A computation of `H` takes no round. -/
theorem Timed.oracleStep_bind {α β : Type} (n : ℕ) (oa : OracleComp (RoSpec C) α)
    (k : α → PartyM C E G β) (hk : ∀ a, Timed n (k a).run) : Timed n (oracleStep oa >>= k).run :=
  Timed.localStep_bind n _ k hk

/-- An exchange takes one round. An abort frame ends the program. -/
theorem Timed.exchange_bind {α : Type} (n : ℕ) (out : Mail C E) (k : Mail C E → PartyM C E G α)
    (hk : ∀ inbox, Timed n (k inbox).run) : Timed (n + 1) (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inl (.inr out))) >>= exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  refine Timed.round n out _ fun inbox => ?_
  change Timed n (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact Timed.abort n
  · exact hk inbox

/-- A call takes one step. -/
theorem Timed.call_bind {α : Type} (n : ℕ) (input : ι) (k : G input → PartyM C E G α)
    (hk : ∀ r, Timed n (k r).run) : Timed (n + 1) (ThresholdLeanXmss.call input >>= k).run := by
  have he : (ThresholdLeanXmss.call (C := C) (E := E) (G := G) input >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inr input)) >>= fun r => (k r).run := by
    simp [ThresholdLeanXmss.call, OptionT.run_bind, OptionT.lift]
  rw [he]
  exact Timed.call n input _ hk

/-- A check takes no round. -/
theorem Timed.require_bind {α : Type} (n : ℕ) (c : Prop) (k : Unit → PartyM C E G α)
    (hk : c → Timed n (k ()).run) : Timed n (require c >>= k).run := by
  unfold require
  split_ifs with h
  · simpa only [pure_bind] using hk h
  · rw [failure_bind]
    exact Timed.abort n

end Timed

/-! ## A stopped program with the next phase -/

section Attach

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type}

/-- Attach the next phase to a stopped program. An operator that is done stays aborted, so the
lemmas use it only for a step with no output. -/
def attachStep (k : α → PartyM C E G β) : Step C E G α → Step C E G β
  | .done _ => .done none
  | .wait out resume => .wait out fun inbox => (OptionT.mk (resume inbox) >>= k).run
  | .call input resume => .call input fun r => (OptionT.mk (resume r) >>= k).run

theorem continueStep_attach (k : α → PartyM C E G β) (step : Step C E G α) (hp : step.output = none) :
    continueStep k step = pure (attachStep k step) := by
  cases step with
  | done out => cases out <;> simp_all [Step.output, continueStep, attachStep]
  | wait out resume => rfl
  | call input resume => rfl

theorem attachStep_outbox (k : α → PartyM C E G β) (step : Step C E G α) :
    (attachStep k step).outbox = step.outbox := by cases step <;> rfl

theorem attachStep_callInput (k : α → PartyM C E G β) (step : Step C E G α) :
    (attachStep k step).callInput = step.callInput := by cases step <;> rfl

theorem attachStep_isDone (k : α → PartyM C E G β) (step : Step C E G α) :
    (attachStep k step).isDone ↔ step.isDone := by cases step <;> rfl

theorem attachStep_delivered (k : α → PartyM C E G β) (step : Step C E G α) (hp : step.output = none) :
    (attachStep k step).delivered = step.delivered := by
  cases step with
  | done out => cases out <;> simp_all [Step.output, Step.delivered, attachStep]
  | wait out resume => rfl
  | call input resume => rfl

/-- A timed step with rounds to go has no output. -/
theorem StepTimed.output_none {n : ℕ} {step : Step C E G α} (h : StepTimed (n + 1) step) :
    step.output = none := by
  cases step with
  | done out =>
    cases out with
    | none => rfl
    | some a => exact absurd h (Nat.succ_ne_zero n)
  | wait out resume => rfl
  | call input resume => rfl

/-- A timed step with no round to go is done. -/
theorem StepTimed.isDone {step : Step C E G α} (h : StepTimed 0 step) : step.isDone := by
  cases step with
  | done out => trivial
  | wait out resume => obtain ⟨m, hm, -⟩ := h; exact absurd hm.symm (Nat.succ_ne_zero m)
  | call input resume => obtain ⟨m, hm, -⟩ := h; exact absurd hm.symm (Nat.succ_ne_zero m)

end Attach

/-! ## One step of the network with the next phase -/

section Compose

variable {C : Committee} {E : Type} {I O L R Ia α β : Type}
variable (prims : Primitives) (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- Runs that agree on each possible result of a common prefix are the same run. -/
theorem SameRun.bind_support {γ δ : Type} (oa : OracleComp (LocalSpec C) γ)
    {f g : γ → OracleComp (LocalSpec C) δ} (h : ∀ a ∈ support oa, SameRun prims (f a) (g a)) :
    SameRun prims (oa >>= f) (oa >>= g) := by
  intro s
  simp only [simulateQ_bind, StateT.run_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => h z.1 ?_ z.2
  have hsub := support_simulateQ_run'_subset (localAnswer (C := C) prims) oa s
  apply hsub
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

/-- The local work of the operators and then the work of their continuations, in the order of the
operators or in two passes. -/
theorem sameRun_sequenceFin_bind {β₁ β₂ γ : Type} {n : ℕ} (X : Fin n → OracleComp (LocalSpec C) β₂)
    (U : Fin n → OracleComp (LocalSpec C) β₁) (V : Fin n → β₁ → OracleComp (LocalSpec C) β₂)
    (h : ∀ j, X j = U j >>= V j) (f : (Fin n → β₂) → OracleComp (LocalSpec C) γ) :
    SameRun prims (OverPermutation.sequenceFin X >>= f)
      (OverPermutation.sequenceFin U >>= fun x => OverPermutation.sequenceFin (fun j => V j (x j)) >>= f) := by
  have hX : X = fun j => U j >>= fun u => V j u >>= fun v => pure ((fun _ _ v => v) j u v) := by
    funext j
    simp only [h j, bind_pure]
  have key := sameRun_sequenceFin_dep prims U V (fun _ _ v => v)
  rw [← hX] at key
  have := key.bind fun y => SameRun.refl prims (f y)
  simpa only [bind_assoc, pure_bind] using this

/-- One step with the next phase attached is the step, and then the first local work of the next
phase at each operator that finished. The two orders of the local work agree in distribution. -/
theorem stepRound_attach (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (hp : ∀ i, (steps i).output = none) :
    SameRun prims (stepRound localRoles D A F st (fun i => attachStep (k i) (steps i)))
      (stepRound localRoles D A F st steps >>= fun r =>
        OverPermutation.sequenceFin (fun j => continueStep (k j) (r.2.1 j)) >>= fun next =>
          pure (r.1, next, r.2.2)) := by
  have hdel : ∀ t, (attachStep (k t) (steps t)).delivered = (steps t).delivered :=
    fun t => attachStep_delivered _ _ (hp t)
  unfold stepRound
  simp only [attachStep_callInput, attachStep_isDone]
  split_ifs with hc
  · simp only [bind_assoc, pure_bind]
    refine SameRun.bind_right _ fun r => ?_
    refine sameRun_sequenceFin_bind prims _ _ (fun j => continueStep (k j)) (fun j => ?_)
      (fun steps' => pure (r.1, steps', fun _ _ => none))
    cases hs : steps j with
    | done out =>
      have ho := hp j
      rw [hs] at ho
      cases ho
      rfl
    | wait out resume => rfl
    | call input resume =>
      by_cases hj : j ∈ D.1
      · simp only [attachStep, hj, ↓reduceIte, pure_bind]
        rfl
      · simp only [attachStep, hj, ↓reduceIte, localRoles]
        exact advance_bind (OptionT.mk (resume (r.2 j))) (k j)
  · simp only [attachStep_outbox, hdel, bind_assoc, pure_bind]
    refine SameRun.bind_right _ fun r => ?_
    refine sameRun_sequenceFin_bind prims _ _ (fun j => continueStep (k j)) (fun j => ?_)
      (fun steps' => pure (r.1, steps', r.2))
    cases hs : steps j with
    | done out =>
      have ho := hp j
      rw [hs] at ho
      cases ho
      rfl
    | wait out resume =>
      by_cases hj : j ∈ D.1
      · simp only [attachStep, hj, ↓reduceIte, pure_bind]
        rfl
      · simp only [attachStep, hj, ↓reduceIte, localRoles]
        exact advance_bind (OptionT.mk (resume _)) (k j)
    | call input resume => rfl

theorem mem_support_sequenceFin_local {γ : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) γ) (x : Fin n → γ),
      x ∈ support (OverPermutation.sequenceFin f) → ∀ i, x i ∈ support (f i) :=
  fun f x hx => mem_support_sequenceFin_oc f x hx

/-- One step of timed steps gives timed steps with one round less. An operator that calls out of turn
aborts, and a corrupt operator stays aborted. -/
theorem stepRound_timed (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimed (n + 1) (steps i)) :
    ∀ r ∈ support (stepRound localRoles D A F st steps),
      (∀ i ∈ D.1, r.2.1 i = .done none) ∧ ∀ i ∉ D.1, StepTimed n (r.2.1 i) := by
  intro r hr
  unfold stepRound at hr
  split_ifs at hr with hc
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨fo, -, steps', hs', rfl⟩ := hr
    have hmem := mem_support_sequenceFin_local _ _ hs'
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
        simp only [hi, ↓reduceIte, localRoles] at h
        exact timed_advance (htm _) _ h
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨fo, -, steps', hs', rfl⟩ := hr
    have hmem := mem_support_sequenceFin_local _ _ hs'
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
        simp only [hi, ↓reduceIte, localRoles] at h
        exact timed_advance (htm _) _ h
      | call input resume =>
        rw [hs] at h
        simp only [support_pure, Set.mem_singleton_iff] at h
        rw [h]
        trivial

/-- A timed phase ends with every honest operator done. -/
theorem executeSteps_timed : ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimed n (steps i)) →
    ∀ r ∈ support (executeSteps localRoles D A F n st steps),
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
      obtain ⟨hD', ht'⟩ := stepRound_timed D A F n st steps hD ht q hq
      exact executeSteps_timed n q.1 q.2.1 hD' ht' r hr

/-- The first steps of timed programs are timed, and a corrupt operator does not run. -/
theorem startSteps_timed (a : ℕ) (p : C.Party → PartyM C E (CallSpec I O) α)
    (hp : ∀ i ∉ D.1, Timed a (p i).run) :
    ∀ s0 ∈ support (startSteps localRoles D p),
      (∀ i ∈ D.1, s0 i = .done none) ∧ ∀ i ∉ D.1, StepTimed a (s0 i) := by
  intro s0 hs0
  have hmem := mem_support_sequenceFin_local _ _ hs0
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h := hmem i
    simpa [hi] using h
  · have h := hmem i
    simp only [hi, ↓reduceIte, localRoles] at h
    exact timed_advance (hp i hi) _ h

/-- The first steps of the next phase, from the last steps of a phase that is over, for each pair of
roles whose honest role keeps `pure`. -/
theorem startSteps_elim_of_honest_pure {m : Type → Type} [Monad m] (Ro : Roles C m)
    (hRo : ∀ {γ : Type} (c : γ), Ro.honest (pure c) = pure c) (fin : C.Party → Step C E (CallSpec I O) α)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (hD : ∀ i ∈ D.1, fin i = .done none)
    (hd : ∀ i ∉ D.1, (fin i).isDone) :
    startSteps Ro D (fun i => ((fin i).output).elim failure (k i)) =
      OverPermutation.sequenceFin fun i => Ro.honest (continueStep (k i) (fin i)) := by
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [hi, ↓reduceIte, hD i hi]
    exact (hRo _).symm
  · simp only [hi, ↓reduceIte]
    cases hs : fin i with
    | done out => cases out <;> rfl
    | wait out resume => exact absurd (hd i hi) (by simp [hs, Step.isDone])
    | call input resume => exact absurd (hd i hi) (by simp [hs, Step.isDone])

/-- The first steps of the next phase, from the last steps of a phase that is over. -/
theorem startSteps_elim (fin : C.Party → Step C E (CallSpec I O) α)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (hD : ∀ i ∈ D.1, fin i = .done none)
    (hd : ∀ i ∉ D.1, (fin i).isDone) :
    startSteps localRoles D (fun i => ((fin i).output).elim failure (k i)) =
      OverPermutation.sequenceFin fun i => continueStep (k i) (fin i) :=
  startSteps_elim_of_honest_pure D localRoles (fun _ => rfl) fin k hD hd

/-- The honest operators that still run have no output, and a corrupt operator has none. -/
theorem output_none_of_timed {n : ℕ} {steps : C.Party → Step C E (CallSpec I O) α}
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimed (n + 1) (steps i)) :
    ∀ i, (steps i).output = none := fun i => by
  by_cases hi : i ∈ D.1
  · rw [hD i hi]
    rfl
  · exact (ht i hi).output_none

/-- One step of a timed phase with the next phase attached. `hrest` is the claim for the rest of the
phase, from each possible result of the step. -/
theorem executeRounds_attach_step (b : ℕ) (k : C.Party → α → PartyM C E (CallSpec I O) β) (n : ℕ)
    (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimed (n + 1) (steps i))
    (hrest : ∀ q ∈ support (stepRound localRoles D A F st steps),
      SameRun prims
        (OverPermutation.sequenceFin (fun j => continueStep (k j) (q.2.1 j)) >>= fun next =>
          executeRounds localRoles D A F (n + b) q.1 next)
        (executeSteps localRoles D A F n q.1 q.2.1 >>= fun r =>
          OverPermutation.sequenceFin (fun i => continueStep (k i) (r.2 i)) >>= fun next =>
            executeRounds localRoles D A F b r.1 next)) :
    SameRun prims (executeRounds localRoles D A F (n + 1 + b) st (fun i => attachStep (k i) (steps i)))
      (executeSteps localRoles D A F (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => continueStep (k i) (r.2 i)) >>= fun next =>
          executeRounds localRoles D A F b r.1 next) := by
  have hp := output_none_of_timed D hD ht
  have hattach : (fun i => continueStep (k i) (steps i)) = fun i => pure (attachStep (k i) (steps i)) :=
    funext fun i => continueStep_attach _ _ (hp i)
  rw [show n + 1 + b = (n + b) + 1 by omega, executeRounds, executeSteps]
  simp only [attachStep_isDone]
  split_ifs with hd
  · apply SameRun.of_eq
    rw [pure_bind, hattach, sequenceFin_pure, pure_bind]
    refine (stages_executeRounds_allDone D A F b st _ fun i => ?_).symm
    by_cases hi : i ∈ D.1
    · rw [hD i hi]
      trivial
    · exact (attachStep_isDone _ _).2 (hd i hi)
  · refine ((stepRound_attach prims D A F st steps k hp).bind fun q => SameRun.refl prims _).trans ?_
    simp only [bind_assoc, pure_bind]
    exact SameRun.bind_support prims _ fun q hq => hrest q hq

/-- A timed phase with the next phase attached runs as the phase, then the first local work of the
next phase, then the rounds of the next phase. -/
theorem executeRounds_attach (b : ℕ) (k : C.Party → α → PartyM C E (CallSpec I O) β) :
    ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimed (n + 1) (steps i)) →
    SameRun prims (executeRounds localRoles D A F (n + 1 + b) st (fun i => attachStep (k i) (steps i)))
      (executeSteps localRoles D A F (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => continueStep (k i) (r.2 i)) >>= fun next =>
          executeRounds localRoles D A F b r.1 next) := by
  intro n
  induction n with
  | zero =>
    intro st steps hD ht
    refine executeRounds_attach_step prims D A F b k 0 st steps hD ht fun q _ => ?_
    simp only [executeSteps, pure_bind, Nat.zero_add]
    exact SameRun.refl prims _
  | succ m ih =>
    intro st steps hD ht
    refine executeRounds_attach_step prims D A F b k (m + 1) st steps hD ht fun q hq => ?_
    obtain ⟨hD', ht'⟩ := stepRound_timed D A F (m + 1) st steps hD ht q hq
    have hattach : (fun i => continueStep (k i) (q.2.1 i)) = fun i => pure (attachStep (k i) (q.2.1 i)) :=
      funext fun i => continueStep_attach _ _ (output_none_of_timed D hD' ht' i)
    rw [hattach, sequenceFin_pure, pure_bind]
    exact ih q.1 q.2.1 hD' ht'

/-- Two phases in sequence (GS20, Section 3.1). A run of the programs `p i >>= k i`, where each
`p i` takes exactly `a` rounds or calls, is a run of the programs `p i` and then a run of the
programs `k i` on the outputs. An operator with no output of the first phase does not start the
second phase. -/
theorem executePhase_bind (a b : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (hp : ∀ i ∉ D.1, Timed a (p i).run) :
    SameRun prims (executePhase localRoles D A F (a + b) st (fun i => p i >>= k i))
      (executePhase localRoles D A F a st p >>= fun r =>
        executePhase localRoles D A F b r.1 (fun i => (r.2 i).elim failure (k i))) := by
  unfold executePhase
  have hstart : SameRun prims
      (startSteps localRoles D (fun i => p i >>= k i) >>= executeRounds localRoles D A F (a + b) st)
      (startSteps localRoles D p >>= fun s0 =>
        OverPermutation.sequenceFin (fun j => continueStep (k j) (s0 j)) >>=
          executeRounds localRoles D A F (a + b) st) := by
    unfold startSteps
    refine sameRun_sequenceFin_bind prims _ _ (fun j => continueStep (k j)) (fun j => ?_) _
    by_cases hj : j ∈ D.1
    · simp only [hj, ↓reduceIte, pure_bind]
      rfl
    · simp only [hj, ↓reduceIte, localRoles]
      exact advance_bind (p j) (k j)
  refine hstart.trans ?_
  simp only [bind_assoc]
  refine SameRun.bind_support prims _ fun s0 hs0 => ?_
  obtain ⟨hD0, ht0⟩ := startSteps_timed D a p hp s0 hs0
  have hfin : SameRun prims
      (executeSteps localRoles D A F a st s0 >>= fun q =>
        OverPermutation.sequenceFin (fun i => continueStep (k i) (q.2 i)) >>= fun next =>
          executeRounds localRoles D A F b q.1 next)
      (executeRounds localRoles D A F a st s0 >>= fun r =>
        startSteps localRoles D (fun i => (r.2 i).elim failure (k i)) >>=
          executeRounds localRoles D A F b r.1) := by
    rw [executeRounds_eq_executeSteps, bind_map_left]
    refine SameRun.bind_support prims _ fun q hq => ?_
    obtain ⟨hDq, hdq⟩ := executeSteps_timed D A F a st s0 hD0 ht0 q hq
    exact SameRun.of_eq (by rw [startSteps_elim D q.2 k hDq hdq])
  refine SameRun.trans ?_ hfin
  cases a with
  | zero =>
    simp only [executeSteps, pure_bind, Nat.zero_add]
    exact SameRun.refl prims _
  | succ n =>
    have hattach : (fun i => continueStep (k i) (s0 i)) = fun i => pure (attachStep (k i) (s0 i)) :=
      funext fun i => continueStep_attach _ _ (output_none_of_timed D hD0 ht0 i)
    rw [hattach, sequenceFin_pure, pure_bind]
    exact executeRounds_attach prims D A F b k n st s0 hD0 ht0

/-- The run after a partial abort. An honest operator does not start. Each other honest operator
does its local work and stops at a call, or aborts. Then the functionality does not run, every
operator aborts, and the adversary gets no step. -/
theorem executePhase_partial (fuel : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α)
    (hdead : ∃ i ∉ D.1, p i = failure)
    (hcall : ∀ i ∉ D.1, ∀ step ∈ support (advance (p i).run), step = .done none ∨
      ∃ input resume, step = .call input resume ∧ advance (resume none) = pure (.done none)) :
    SameRun prims (executePhase localRoles D A F fuel st p)
      (startSteps localRoles D p >>= fun _ => pure (st, fun _ => none)) := by
  unfold executePhase
  refine SameRun.bind_support prims _ fun s0 hs0 => SameRun.of_eq ?_
  have hmem := mem_support_sequenceFin_local _ _ hs0
  obtain ⟨i₀, hi₀, hfail⟩ := hdead
  refine stages_executeRounds_abort D A F fuel st s0 (fun i hi => ?_) (fun i hi => ?_) ⟨i₀, hi₀, ?_⟩
  · have h := hmem i
    simpa [hi] using h
  · have h := hmem i
    simp only [hi, ↓reduceIte, localRoles] at h
    exact hcall i hi _ h
  · have h := hmem i₀
    simp only [hi₀, ↓reduceIte, localRoles, hfail] at h
    rw [advance_run_failure, support_pure, Set.mem_singleton_iff] at h
    exact h

/-- A run depends only on the programs of the honest operators. -/
theorem executePhase_congr (fuel : ℕ) (st : A.State) (p p' : C.Party → PartyM C E (CallSpec I O) α)
    (h : ∀ i, i ∉ D.1 → p i = p' i) :
    executePhase localRoles D A F fuel st p = executePhase localRoles D A F fuel st p' := by
  unfold executePhase startSteps
  congr 2
  funext i
  by_cases hi : i ∈ D.1
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte, h i hi]

/-- The honest operators compute values of `H` and then run. The run is the computation of all values
and then the run on the values. A corrupt operator computes no value, and `d` stands for its value. -/
theorem executePhase_oracleStep_bind {γ : Type} (d : γ) (fuel : ℕ) (st : A.State)
    (q : C.Party → OracleComp (RoSpec C) γ) (prog : C.Party → γ → PartyM C E (CallSpec I O) α) :
    SameRun prims (executePhase localRoles D A F fuel st (fun i => oracleStep (q i) >>= prog i))
      (liftComp (OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure d else q i) (LocalSpec C) >>=
        fun w => executePhase localRoles D A F fuel st (fun i => prog i (w i))) := by
  have hl : liftComp (OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure d else q i) (LocalSpec C) =
      OverPermutation.sequenceFin fun i =>
        liftComp (if i ∈ D.1 then pure d else q i) (LocalSpec C) := simulateQ_sequenceFin _ _
  unfold executePhase startSteps
  rw [hl]
  refine sameRun_sequenceFin_bind prims _ _
    (fun i w => if i ∈ D.1 then pure (Step.done none) else localRoles.honest (advance (prog i w).run))
    (fun i => ?_) _
  by_cases hi : i ∈ D.1
  · simp only [hi, ↓reduceIte, liftComp_pure, pure_bind]
  · simp only [hi, ↓reduceIte, localRoles]
    exact advance_oracleStep_bind (q i) (prog i)

end Compose

end ThresholdLeanXmssSecurity
