import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Phase

/-!
# Two phases in sequence, as an equation of programs

`executePhase_bind` (`Proof/CeremonyHybrid/Phase.lean`) splits a run at the end of a timed phase in
distribution. It changes the order of the local work at the boundary of the two phases.

When each first program makes no local query after its last round, no local work changes its
order. Then the two runs are equal as programs of `OracleComp (WorldSpec C)`, and so they are equal
under each handler.

* `TimedQuiet n p` is `Timed n p` with no local query at the count `0`.
* `timedQuiet_setupKeys` states that a setup is `TimedQuiet setupRounds`. After the echo round,
  `commitRevealEcho` has only `require` and `pure`.
* `executePhase_bind_eq` is the split of a run for `worldRoles`, as an equation. The lemmas before it
  follow the lemmas of `executePhase_bind`, with `worldRoles`, `TimedQuiet` and `=`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Quiet

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- A program that takes exactly `n` rounds or calls on each path that does not abort, and that makes
no local query after its last round or call. -/
inductive TimedQuiet {α : Type} : ℕ → OracleComp (PartySpec C E G) (Option α) → Prop
  | abort (n : ℕ) : TimedQuiet n (pure none)
  | done (a : α) : TimedQuiet 0 (pure (some a))
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, TimedQuiet (n + 1) (k r)) : TimedQuiet (n + 1) (.liftBind (.inl (.inl q)) k)
  | round (n : ℕ) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, TimedQuiet n (k r)) : TimedQuiet (n + 1) (.liftBind (.inl (.inr out)) k)
  | call (n : ℕ) (input : ι) (k : G input → OracleComp (PartySpec C E G) (Option α))
      (h : ∀ r, TimedQuiet n (k r)) : TimedQuiet (n + 1) (.liftBind (.inr input) k)

/-- A quiet program is timed. -/
theorem TimedQuiet.timed {α : Type} {n : ℕ} {p : OracleComp (PartySpec C E G) (Option α)}
    (h : TimedQuiet n p) : Timed n p := by
  induction h with
  | abort n => exact Timed.abort n
  | done a => exact Timed.done a
  | queryLocal n q k _ ih => exact Timed.queryLocal (n + 1) q k ih
  | round n out k _ ih => exact Timed.round n out k ih
  | call n input k _ ih => exact Timed.call n input k ih

/-- A quiet program with no round to go is `pure`. -/
theorem TimedQuiet.eq_pure {α : Type} {p : OracleComp (PartySpec C E G) (Option α)}
    (h : TimedQuiet 0 p) : ∃ out, p = pure out := by
  cases h with
  | abort => exact ⟨none, rfl⟩
  | done a => exact ⟨some a, rfl⟩

/-- The local steps of a quiet program with no round to go make no query. -/
theorem TimedQuiet.advance_eq_pure {α : Type} {p : OracleComp (PartySpec C E G) (Option α)}
    (h : TimedQuiet 0 p) : ∃ out, advance p = pure (.done out) := by
  obtain ⟨out, rfl⟩ := h.eq_pure
  exact ⟨out, advance_pure out⟩

/-- The number of rounds and calls of a sequence is the sum of the two numbers. -/
theorem TimedQuiet.bind {α β : Type} {m n : ℕ} {p : PartyM C E G α} {k : α → PartyM C E G β}
    (hp : TimedQuiet m p.run) (hk : ∀ a, TimedQuiet n (k a).run) : TimedQuiet (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TimedQuiet (m + n) (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | abort m => simpa only [pure_bind, Option.elim_none] using TimedQuiet.abort (α := β) (m + n)
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hk a
  | queryLocal m q f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact TimedQuiet.queryLocal (m + n) q _ fun r => by
      have := ih r
      rwa [Nat.add_right_comm m 1 n] at this
  | round m out f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact TimedQuiet.round (m + n) out _ ih
  | call m input f _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact TimedQuiet.call (m + n) input _ ih

theorem timedQuiet_pure {α : Type} (a : α) : TimedQuiet 0 (pure a : PartyM C E G α).run := TimedQuiet.done a

/-- Local work before a round takes no round. -/
theorem TimedQuiet.localStep_bind {α β : Type} (n : ℕ) (oa : OracleComp (LocalSpec C) α)
    (k : α → PartyM C E G β) (hk : ∀ a, TimedQuiet (n + 1) (k a).run) :
    TimedQuiet (n + 1) (localStep oa >>= k).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_assoc, pure_bind,
    Option.elim_some]
  change TimedQuiet (n + 1) (liftComp oa (PartySpec C E G) >>= fun a => (k a).run)
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
    exact TimedQuiet.queryLocal n q _ ih

/-- A computation of `H` before a round takes no round. -/
theorem TimedQuiet.oracleStep_bind {α β : Type} (n : ℕ) (oa : OracleComp (RoSpec C) α)
    (k : α → PartyM C E G β) (hk : ∀ a, TimedQuiet (n + 1) (k a).run) :
    TimedQuiet (n + 1) (oracleStep oa >>= k).run :=
  TimedQuiet.localStep_bind n _ k hk

/-- An exchange takes one round. An abort frame ends the program. -/
theorem TimedQuiet.exchange_bind {α : Type} (n : ℕ) (out : Mail C E) (k : Mail C E → PartyM C E G α)
    (hk : ∀ inbox, TimedQuiet n (k inbox).run) : TimedQuiet (n + 1) (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inl (.inr out))) >>= exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  refine TimedQuiet.round n out _ fun inbox => ?_
  change TimedQuiet n (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact TimedQuiet.abort n
  · exact hk inbox

/-- A check takes no round and makes no query. -/
theorem TimedQuiet.require_bind {α : Type} (n : ℕ) (c : Prop) (k : Unit → PartyM C E G α)
    (hk : c → TimedQuiet n (k ()).run) : TimedQuiet n (require c >>= k).run := by
  unfold require
  split_ifs with h
  · simpa only [pure_bind] using hk h
  · rw [failure_bind]
    exact TimedQuiet.abort n

end Quiet

section Setup

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- The setup with commit, reveal and echo makes no local query after the echo round. -/
theorem timedQuiet_commitRevealEcho (phase : Phase) (i : C.Party) (own : Parts C) :
    TimedQuiet 3 (commitRevealEcho (E := E) (G := G) phase i own).run := by
  unfold commitRevealEcho
  refine TimedQuiet.oracleStep_bind 2 _ _ fun commitments => ?_
  refine TimedQuiet.exchange_bind 2 _ _ fun committed => ?_
  refine TimedQuiet.exchange_bind 1 _ _ fun revealed => ?_
  refine TimedQuiet.oracleStep_bind 0 _ _ fun opens => ?_
  refine TimedQuiet.require_bind 1 _ _ fun _ => ?_
  refine TimedQuiet.oracleStep_bind 0 _ _ fun keys => ?_
  refine TimedQuiet.oracleStep_bind 0 _ _ fun shared => ?_
  refine TimedQuiet.exchange_bind 0 _ _ fun received => ?_
  exact TimedQuiet.require_bind 0 _ _ fun _ => timedQuiet_pure _

/-- A setup of `phase` takes `setupRounds` rounds and makes no local query after the last one. -/
theorem timedQuiet_setupKeys (phase : Phase) (i : C.Party) :
    TimedQuiet setupRounds (setupKeys (E := E) phase i).run := by
  unfold setupKeys setupWith
  refine TimedQuiet.localStep_bind 2 _ _ fun own => ?_
  exact (timedQuiet_commitRevealEcho (E := E) (G := RealSpec) phase i own).bind (n := 0)
    (k := fun keys => (pure (keysOf keys) : PartyM C E RealSpec (Keys C))) fun keys => timedQuiet_pure _

end Setup

/-! ## Supports and the order of local work -/

section Support

variable {C : Committee}

/-- A computation on the free copy has the results of the computation. -/
theorem support_free_subset {α : Type} (oa : OracleComp (LocalSpec C) α) : support (free oa) ⊆ support oa :=
  support_simulateQ_subset _ oa

/-- The work of the operators and then the work of their continuations, in the order of the
operators or in two passes. The two programs are equal when each continuation is `pure` on the
results of its operator, or when the work of each operator is `pure`. -/
theorem sequenceFin_bind_swap {κ β₁ β₂ : Type} {spec : OracleSpec κ} :
    ∀ {n : ℕ} (U : Fin n → OracleComp spec β₁) (V : Fin n → β₁ → OracleComp spec β₂),
      ((∀ j, ∀ u ∈ support (U j), ∃ v, V j u = pure v) ∨ ∀ j, ∃ u, U j = pure u) →
      OverPermutation.sequenceFin (fun j => U j >>= V j) =
        OverPermutation.sequenceFin U >>= fun x => OverPermutation.sequenceFin fun j => V j (x j)
  | 0, U, V, _ => by
    simp only [OverPermutation.sequenceFin, pure_bind]
  | n + 1, U, V, h => by
    have ih := sequenceFin_bind_swap (fun j : Fin n => U j.succ) (fun j => V j.succ)
      (h.imp (fun h j => h j.succ) fun h j => h j.succ)
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind, ih]
    rcases h with h | h
    · refine bind_congr_of_forall_mem_support (U 0) fun u hu => ?_
      obtain ⟨v, hv⟩ := h 0 u hu
      simp only [Fin.cases_zero, Fin.cases_succ, hv, pure_bind]
    · obtain ⟨u, hu⟩ := h 0
      simp only [hu, pure_bind]
      have hpure : ∀ {m : ℕ} (W : Fin m → OracleComp spec β₁), (∀ j, ∃ w, W j = pure w) →
          ∃ w, OverPermutation.sequenceFin W = pure w := fun W hW => by
        choose w hw using hW
        exact ⟨w, by rw [funext hw]; exact sequenceFin_pure w⟩
      obtain ⟨w, hw⟩ := hpure (fun j : Fin n => U j.succ) fun j => h j.succ
      simp only [hw, pure_bind, Fin.cases_zero, Fin.cases_succ]

/-- `sequenceFin_bind_swap` with a continuation, in the form of `sameRun_sequenceFin_bind`. -/
theorem sequenceFin_bind_attach {κ β₁ β₂ γ : Type} {spec : OracleSpec κ} {n : ℕ}
    (X : Fin n → OracleComp spec β₂) (U : Fin n → OracleComp spec β₁) (V : Fin n → β₁ → OracleComp spec β₂)
    (h : ∀ j, X j = U j >>= V j)
    (hswap : (∀ j, ∀ u ∈ support (U j), ∃ v, V j u = pure v) ∨ ∀ j, ∃ u, U j = pure u)
    (f : (Fin n → β₂) → OracleComp spec γ) :
    OverPermutation.sequenceFin X >>= f =
      OverPermutation.sequenceFin U >>= fun x => OverPermutation.sequenceFin (fun j => V j (x j)) >>= f := by
  rw [funext h, sequenceFin_bind_swap U V hswap, bind_assoc]

end Support

/-! ## Quiet steps -/

section Step

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- A stopped program that needs exactly `n` more rounds or calls, unless it aborts, and that makes
no local query after the last one. -/
def StepTimedQuiet {α : Type} (n : ℕ) : Step C E G α → Prop
  | .done none => True
  | .done (some _) => n = 0
  | .wait _ resume => ∃ m, n = m + 1 ∧ ∀ inbox, TimedQuiet m (resume inbox)
  | .call _ resume => ∃ m, n = m + 1 ∧ ∀ r, TimedQuiet m (resume r)

theorem StepTimedQuiet.stepTimed {α : Type} {n : ℕ} {step : Step C E G α} (h : StepTimedQuiet n step) :
    StepTimed n step := by
  cases step with
  | done out => cases out <;> exact h
  | wait out resume => obtain ⟨m, hm, hr⟩ := h; exact ⟨m, hm, fun inbox => (hr inbox).timed⟩
  | call input resume => obtain ⟨m, hm, hr⟩ := h; exact ⟨m, hm, fun r => (hr r).timed⟩

/-- The local steps of a quiet program stop at a quiet step. -/
theorem timedQuiet_advance {α : Type} {n : ℕ} {p : OracleComp (PartySpec C E G) (Option α)}
    (h : TimedQuiet n p) : ∀ step ∈ support (advance p), StepTimedQuiet n step := by
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

end Step

/-! ## One step of the network with the next phase -/

section Compose

variable {C : Committee} {E : Type} {I O L R Ia α β : Type}
variable (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- The honest operators that still run have no output, and a corrupt operator has none. -/
theorem output_none_of_timedQuiet {n : ℕ} {steps : C.Party → Step C E (CallSpec I O) α}
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimedQuiet (n + 1) (steps i)) :
    ∀ i, (steps i).output = none :=
  output_none_of_timed D hD fun i hi => (ht i hi).stepTimed

/-- The continuation of a step with no output makes no query. -/
theorem free_continueStep_of_output_none (k : α → PartyM C E (CallSpec I O) β) (step : Step C E (CallSpec I O) α)
    (hp : step.output = none) : ∃ v, free (continueStep k step) = pure v :=
  ⟨attachStep k step, by rw [continueStep_attach k step hp, free_pure]⟩

/-- The local work of a quiet step in its last round makes no query. -/
theorem free_advance_of_timedQuiet_zero {p : OracleComp (PartySpec C E (CallSpec I O)) (Option α)}
    (h : TimedQuiet 0 p) : ∃ u, free (advance p) = pure u := by
  obtain ⟨out, ho⟩ := h.advance_eq_pure
  exact ⟨.done out, by rw [ho, free_pure]⟩

/-- One step with the next phase attached is the step, and then the first local work of the next
phase at each operator that finished. The two programs are equal. Before the last round, no operator
finishes, so the attached work is `pure`. In the last round, the step of each operator is `pure`. -/
theorem stepRound_attach_eq (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (hD : ∀ i ∈ D.1, steps i = .done none)
    (ht : ∀ i ∉ D.1, StepTimedQuiet (n + 1) (steps i)) :
    stepRound worldRoles D A F st (fun i => attachStep (k i) (steps i)) =
      stepRound worldRoles D A F st steps >>= fun r =>
        OverPermutation.sequenceFin (fun j => free (continueStep (k j) (r.2.1 j))) >>= fun next =>
          pure (r.1, next, r.2.2) := by
  have hp := output_none_of_timedQuiet D hD ht
  have hdel : ∀ t, (attachStep (k t) (steps t)).delivered = (steps t).delivered :=
    fun t => attachStep_delivered _ _ (hp t)
  have hstep : ∀ j, ∀ u, u = steps j → ∃ v, free (continueStep (k j) u) = pure v := fun j u hu =>
    free_continueStep_of_output_none (k j) u (hu ▸ hp j)
  have hnone : ∀ j : C.Party, ∃ v, free (continueStep (k j) (.done none)) = pure v := fun j =>
    free_continueStep_of_output_none (k j) (.done none) rfl
  unfold stepRound
  simp only [attachStep_callInput, attachStep_isDone]
  split_ifs with hc
  · simp only [bind_assoc, pure_bind]
    refine bind_congr fun r => ?_
    refine sequenceFin_bind_attach _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_) ?_
      (fun steps' => pure (r.1, steps', fun _ _ => none))
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
    · cases n with
      | zero =>
        refine Or.inr fun j => ?_
        cases hs : steps j with
        | done out => exact ⟨_, rfl⟩
        | wait out resume => exact ⟨_, rfl⟩
        | call input resume =>
          by_cases hj : j ∈ D.1
          · exact ⟨.done none, by simp only [hj, ↓reduceIte]⟩
          · have h := ht j hj
            rw [hs] at h
            obtain ⟨m, hm, hr⟩ := h
            obtain rfl : m = 0 := by omega
            obtain ⟨u, hu⟩ := free_advance_of_timedQuiet_zero (hr (r.2 j))
            exact ⟨u, by simp only [hj, ↓reduceIte, worldRoles, hu]⟩
      | succ n =>
        refine Or.inl fun j u hu => ?_
        cases hs : steps j with
        | done out =>
          rw [hs, support_pure, Set.mem_singleton_iff] at hu
          exact hstep j u (hu.trans hs.symm)
        | wait out resume =>
          rw [hs, support_pure, Set.mem_singleton_iff] at hu
          exact hstep j u (hu.trans hs.symm)
        | call input resume =>
          rw [hs] at hu
          by_cases hj : j ∈ D.1
          · simp only [hj, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hu
            exact hu ▸ hnone j
          · simp only [hj, ↓reduceIte, worldRoles] at hu
            have h := ht j hj
            rw [hs] at h
            obtain ⟨m, hm, hr⟩ := h
            obtain rfl : m = n + 1 := by omega
            exact free_continueStep_of_output_none (k j) u
              ((timedQuiet_advance (hr (r.2 j)) u (support_free_subset _ hu)).stepTimed.output_none)
  · simp only [attachStep_outbox, hdel, bind_assoc, pure_bind]
    refine bind_congr fun r => ?_
    refine sequenceFin_bind_attach _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_) ?_
      (fun steps' => pure (r.1, steps', r.2))
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
    · cases n with
      | zero =>
        refine Or.inr fun j => ?_
        cases hs : steps j with
        | done out => exact ⟨_, rfl⟩
        | wait out resume =>
          by_cases hj : j ∈ D.1
          · exact ⟨.done none, by simp only [hj, ↓reduceIte]⟩
          · have h := ht j hj
            rw [hs] at h
            obtain ⟨m, hm, hr⟩ := h
            obtain rfl : m = 0 := by omega
            obtain ⟨u, hu⟩ := free_advance_of_timedQuiet_zero (hr fun k' =>
              if k' ∈ D.1 then r.2 k' j else (steps k').delivered j)
            exact ⟨u, by simp only [hj, ↓reduceIte, worldRoles, hu]⟩
        | call input resume => exact ⟨_, rfl⟩
      | succ n =>
        refine Or.inl fun j u hu => ?_
        cases hs : steps j with
        | done out =>
          rw [hs, support_pure, Set.mem_singleton_iff] at hu
          exact hstep j u (hu.trans hs.symm)
        | wait out resume =>
          rw [hs] at hu
          by_cases hj : j ∈ D.1
          · simp only [hj, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hu
            exact hu ▸ hnone j
          · simp only [hj, ↓reduceIte, worldRoles] at hu
            have h := ht j hj
            rw [hs] at h
            obtain ⟨m, hm, hr⟩ := h
            obtain rfl : m = n + 1 := by omega
            exact free_continueStep_of_output_none (k j) u
              ((timedQuiet_advance (hr _) u (support_free_subset _ hu)).stepTimed.output_none)
        | call input resume =>
          rw [hs, support_pure, Set.mem_singleton_iff] at hu
          exact hu ▸ hnone j

/-! ## The timed steps of a run -/

/-- `stepRound_timed` for `worldRoles` and quiet steps. -/
theorem stepRound_timedQuiet (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimedQuiet (n + 1) (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A F st steps),
      (∀ i ∈ D.1, r.2.1 i = .done none) ∧ ∀ i ∉ D.1, StepTimedQuiet n (r.2.1 i) := by
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
      change StepTimedQuiet n (steps' i)
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
        exact timedQuiet_advance (htm _) _ (support_free_subset _ h)
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨fo, -, steps', hs', rfl⟩ := hr
    have hmem := mem_support_sequenceFin_oc _ _ hs'
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h := hmem i
      rw [hD i hi] at h
      simpa using h
    · have h := hmem i
      have hti := ht i hi
      change StepTimedQuiet n (steps' i)
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
        exact timedQuiet_advance (htm _) _ (support_free_subset _ h)
      | call input resume =>
        rw [hs] at h
        simp only [support_pure, Set.mem_singleton_iff] at h
        rw [h]
        trivial

/-- `executeSteps_timed` for `worldRoles` and quiet steps. -/
theorem executeSteps_timedQuiet : ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimedQuiet n (steps i)) →
    ∀ r ∈ support (executeSteps worldRoles D A F n st steps),
      (∀ i ∈ D.1, r.2 i = .done none) ∧ ∀ i ∉ D.1, (r.2 i).isDone
  | 0, st, steps, hD, ht => by
    intro r hr
    simp only [executeSteps, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hD, fun i hi => (ht i hi).stepTimed.isDone⟩
  | n + 1, st, steps, hD, ht => by
    intro r hr
    simp only [executeSteps] at hr
    split_ifs at hr with hd
    · rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hD, hd⟩
    · simp only [support_bind, Set.mem_iUnion] at hr
      obtain ⟨q, hq, hr⟩ := hr
      obtain ⟨hD', ht'⟩ := stepRound_timedQuiet D A F n st steps hD ht q hq
      exact executeSteps_timedQuiet n q.1 q.2.1 hD' ht' r hr

/-- `startSteps_timed` for `worldRoles` and quiet programs. -/
theorem startSteps_timedQuiet (a : ℕ) (p : C.Party → PartyM C E (CallSpec I O) α)
    (hp : ∀ i ∉ D.1, TimedQuiet a (p i).run) :
    ∀ s0 ∈ support (startSteps worldRoles D p),
      (∀ i ∈ D.1, s0 i = .done none) ∧ ∀ i ∉ D.1, StepTimedQuiet a (s0 i) := by
  intro s0 hs0
  have hmem := mem_support_sequenceFin_oc _ _ hs0
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h := hmem i
    simpa [hi] using h
  · have h := hmem i
    simp only [hi, ↓reduceIte, worldRoles] at h
    exact timedQuiet_advance (hp i hi) _ (support_free_subset _ h)

/-! ## Two phases in sequence -/

/-- `executeRounds_attach_step` as an equation, for `worldRoles` and quiet steps. -/
theorem executeRounds_attach_step_eq (b : ℕ) (k : C.Party → α → PartyM C E (CallSpec I O) β) (n : ℕ)
    (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none) (ht : ∀ i ∉ D.1, StepTimedQuiet (n + 1) (steps i))
    (hrest : ∀ q ∈ support (stepRound worldRoles D A F st steps),
      (OverPermutation.sequenceFin (fun j => free (continueStep (k j) (q.2.1 j))) >>= fun next =>
          executeRounds worldRoles D A F (n + b) q.1 next) =
        (executeSteps worldRoles D A F n q.1 q.2.1 >>= fun r =>
          OverPermutation.sequenceFin (fun i => free (continueStep (k i) (r.2 i))) >>= fun next =>
            executeRounds worldRoles D A F b r.1 next)) :
    executeRounds worldRoles D A F (n + 1 + b) st (fun i => attachStep (k i) (steps i)) =
      executeSteps worldRoles D A F (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => free (continueStep (k i) (r.2 i))) >>= fun next =>
          executeRounds worldRoles D A F b r.1 next := by
  have hp := output_none_of_timedQuiet D hD ht
  have hattach : (fun i => free (continueStep (k i) (steps i))) = fun i => pure (attachStep (k i) (steps i)) :=
    funext fun i => by rw [continueStep_attach _ _ (hp i), free_pure]
  rw [show n + 1 + b = (n + b) + 1 by omega, executeRounds, executeSteps]
  simp only [attachStep_isDone]
  split_ifs with hd
  · rw [pure_bind, hattach, sequenceFin_pure, pure_bind]
    refine (executeRounds_allDone D A F worldRoles b st _ fun i => ?_).symm
    by_cases hi : i ∈ D.1
    · rw [hD i hi]
      trivial
    · exact (attachStep_isDone _ _).2 (hd i hi)
  · rw [stepRound_attach_eq D A F n st steps k hD ht]
    simp only [bind_assoc, pure_bind]
    exact bind_congr_of_forall_mem_support _ fun q hq => hrest q hq

/-- `executeRounds_attach` as an equation, for `worldRoles` and quiet steps. -/
theorem executeRounds_attach_eq (b : ℕ) (k : C.Party → α → PartyM C E (CallSpec I O) β) :
    ∀ (n : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
    (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimedQuiet (n + 1) (steps i)) →
    executeRounds worldRoles D A F (n + 1 + b) st (fun i => attachStep (k i) (steps i)) =
      executeSteps worldRoles D A F (n + 1) st steps >>= fun r =>
        OverPermutation.sequenceFin (fun i => free (continueStep (k i) (r.2 i))) >>= fun next =>
          executeRounds worldRoles D A F b r.1 next := by
  intro n
  induction n with
  | zero =>
    intro st steps hD ht
    refine executeRounds_attach_step_eq D A F b k 0 st steps hD ht fun q _ => ?_
    simp only [executeSteps, pure_bind, Nat.zero_add]
  | succ m ih =>
    intro st steps hD ht
    refine executeRounds_attach_step_eq D A F b k (m + 1) st steps hD ht fun q hq => ?_
    obtain ⟨hD', ht'⟩ := stepRound_timedQuiet D A F (m + 1) st steps hD ht q hq
    have hattach : (fun i => free (continueStep (k i) (q.2.1 i))) =
        fun i => pure (attachStep (k i) (q.2.1 i)) :=
      funext fun i => by rw [continueStep_attach _ _ (output_none_of_timedQuiet D hD' ht' i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact ih q.1 q.2.1 hD' ht'

/-- Two phases in sequence, as an equation of programs (GS20, Section 3.1). A run of the programs
`p i >>= k i`, where each `p i` takes exactly `a` rounds or calls and makes no local query after the
last one, is a run of the programs `p i` and then a run of the programs `k i` on the outputs. The
equation holds under each handler of `WorldSpec C`. -/
theorem executePhase_bind_eq (a b : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α)
    (k : C.Party → α → PartyM C E (CallSpec I O) β) (hp : ∀ i ∉ D.1, TimedQuiet a (p i).run) :
    executePhase worldRoles D A F (a + b) st (fun i => p i >>= k i) =
      executePhase worldRoles D A F a st p >>= fun r =>
        executePhase worldRoles D A F b r.1 (fun i => (r.2 i).elim failure (k i)) := by
  unfold executePhase
  have hstart : startSteps worldRoles D (fun i => p i >>= k i) >>= executeRounds worldRoles D A F (a + b) st =
      startSteps worldRoles D p >>= fun s0 =>
        OverPermutation.sequenceFin (fun j => free (continueStep (k j) (s0 j))) >>=
          executeRounds worldRoles D A F (a + b) st := by
    unfold startSteps
    refine sequenceFin_bind_attach _ _ (fun j s => free (continueStep (k j) s)) (fun j => ?_) ?_ _
    · by_cases hj : j ∈ D.1
      · simp only [hj, ↓reduceIte, pure_bind, continueStep, free_pure]
      · simp only [hj, ↓reduceIte, worldRoles]
        rw [advance_bind (p j) (k j), free_bind]
    · cases a with
      | zero =>
        refine Or.inr fun j => ?_
        by_cases hj : j ∈ D.1
        · exact ⟨.done none, by simp only [hj, ↓reduceIte]⟩
        · obtain ⟨u, hu⟩ := free_advance_of_timedQuiet_zero (hp j hj)
          exact ⟨u, by simp only [hj, ↓reduceIte, worldRoles, hu]⟩
      | succ n =>
        refine Or.inl fun j u hu => ?_
        by_cases hj : j ∈ D.1
        · simp only [hj, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hu
          exact hu ▸ free_continueStep_of_output_none (k j) (.done none) rfl
        · simp only [hj, ↓reduceIte, worldRoles] at hu
          exact free_continueStep_of_output_none (k j) u
            ((timedQuiet_advance (hp j hj) u (support_free_subset _ hu)).stepTimed.output_none)
  refine hstart.trans ?_
  simp only [bind_assoc]
  refine bind_congr_of_forall_mem_support _ fun s0 hs0 => ?_
  obtain ⟨hD0, ht0⟩ := startSteps_timedQuiet D a p hp s0 hs0
  have hfin : (executeSteps worldRoles D A F a st s0 >>= fun q =>
        OverPermutation.sequenceFin (fun i => free (continueStep (k i) (q.2 i))) >>= fun next =>
          executeRounds worldRoles D A F b q.1 next) =
      (executeRounds worldRoles D A F a st s0 >>= fun r =>
        startSteps worldRoles D (fun i => (r.2 i).elim failure (k i)) >>=
          executeRounds worldRoles D A F b r.1) := by
    rw [executeRounds_eq_executeSteps, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun q hq => ?_
    obtain ⟨hDq, hdq⟩ := executeSteps_timedQuiet D A F a st s0 hD0 ht0 q hq
    exact congrArg (· >>= executeRounds worldRoles D A F b q.1)
      (startSteps_elim_of_honest_pure D worldRoles free_pure q.2 k hDq hdq).symm
  refine Eq.trans ?_ hfin
  cases a with
  | zero =>
    simp only [executeSteps, pure_bind, Nat.zero_add]
  | succ n =>
    have hattach : (fun i => free (continueStep (k i) (s0 i))) = fun i => pure (attachStep (k i) (s0 i)) :=
      funext fun i => by rw [continueStep_attach _ _ (output_none_of_timedQuiet D hD0 ht0 i), free_pure]
    rw [hattach, sequenceFin_pure, pure_bind]
    exact executeRounds_attach_eq D A F b k n st s0 hD0 ht0

end Compose

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.executePhase_bind_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.executePhase_bind_eq
