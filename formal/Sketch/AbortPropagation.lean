import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.MainStages

/-!
# No honest output after a partial abort

An honest operator that ends with no output sends the abort frame to each operator in each later
round (`Step.delivered`), and `exchange` aborts on an abort frame. So the round after a partial
abort ends each honest operator that waits in it with no output.

* `stepRound_abort` and `executeRounds_abort` are the general lemma. They hold for each pair of
  roles that keeps `pure`, so for `worldRoles` under each handler of `WorldSpec`
  (`executeRounds_abort_support`).
* `StartsWithRound` is the program property that feeds the general lemma. The forms are
  `startsWithRound_openRep` for the opening and `startsWithRound_check` for the check of a batch
  with a positive count. `startsWithRound_verify_output` covers each count. With the count 0 the
  check makes no round, and the round of the opening follows at once
  (`startsWithRound_verify_output_zero`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The round after a partial abort -/

/-- A step that waits in a round and aborts on each inbox with an abort frame. -/
def RejectsAbort {ι α : Type} {G : OracleSpec ι} (step : Step C E G α) : Prop :=
  ∃ outbox resume, step = .wait outbox resume ∧
    ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none)

section Round

variable {m : Type → Type} [Monad m] [LawfulMonad m] {I O L R Ia α : Type}

/-- The round after a partial abort. An honest operator is at `.done none`, and each other honest
operator is done or waits in a round that rejects an abort frame. The adversary sees the round, and
each operator then ends at its output. So each honest operator that waits ends with no output. -/
theorem stepRound_abort (Ro : Roles C m) (hpure : ∀ {β : Type} (x : β), Ro.honest (pure x) = pure x)
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (h : ∀ i ∉ D.1, (steps i).isDone ∨ RejectsAbort (steps i)) :
    stepRound Ro D A F st steps =
      (fun r => (r.1, fun j => Step.done (steps j).output, r.2)) <$>
        Ro.adversary (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) := by
  obtain ⟨a, ha, hadone⟩ := hab
  have hnocall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, hi, hc⟩, -⟩
    rcases h i hi with hd | ⟨outbox, resume, hw, -⟩
    · cases hs : steps i <;> simp_all [Step.isDone, Step.callInput]
    · simp [hw, Step.callInput] at hc
  unfold stepRound
  rw [ite_eq_right hnocall, map_eq_bind_pure_comp]
  refine bind_congr fun ⟨state, sent⟩ => ?_
  dsimp only
  rw [stages_sequenceFin_eq_pure _ (fun j => Step.done (steps j).output) (fun j => ?_), pure_bind]
  · rfl
  rcases hs : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · rfl
  · by_cases hj : j ∈ D.1
    · simp [hj, Step.output]
    · simp only [hj, ite_false, Step.output]
      rcases h j hj with hd | ⟨outbox', resume', hw, hres⟩
      · simp [hs, Step.isDone] at hd
      · rw [hs] at hw
        cases hw
        rw [hres _ ⟨a, by simp [ha, hadone]⟩, hpure]
  · rfl

/-- The rest of the run after a partial abort, for each fuel. If each honest operator is done, the
run stops. Otherwise the adversary sees one round, and each operator ends at the output of its
step. -/
theorem executeRounds_abort (Ro : Roles C m) (hpure : ∀ {β : Type} (x : β), Ro.honest (pure x) = pure x)
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (h : ∀ i ∉ D.1, (steps i).isDone ∨ RejectsAbort (steps i)) :
    executeRounds Ro D A F (fuel + 1) st steps =
      if ∀ i ∉ D.1, (steps i).isDone then pure (st, fun j => (steps j).output) else
        (fun r => (r.1, fun j => (steps j).output)) <$>
          Ro.adversary (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) := by
  rw [executeRounds]
  split_ifs with hdone
  · rfl
  rw [stepRound_abort Ro hpure D A F st steps hab h, map_eq_bind_pure_comp, bind_assoc,
    map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  rw [Function.comp_apply, pure_bind, Function.comp_apply]
  exact executeRounds_allDone D A F Ro fuel r.1 _ fun _ => trivial

/-- The honest roles of the real game keep `pure`. -/
theorem worldRoles_honest_pure {β : Type} (x : β) : (worldRoles (C := C)).honest (pure x) = pure x := by
  simp [worldRoles, free]

/-- The rest of the run after a partial abort in the real game, under each handler of `WorldSpec`
with a state and for each fuel. Each operator ends at the output of its step at the cut, so each
honest operator that waits ends with no output. -/
theorem executeRounds_abort_support {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (h : ∀ i ∉ D.1, (steps i).isDone ∨ RejectsAbort (steps i)) (s : σ)
    (z : (A.State × (C.Party → Option α)) × σ)
    (hz : z ∈ support ((simulateQ impl (executeRounds worldRoles D A F fuel st steps)).run s)) :
    z.1.2 = fun j => (steps j).output := by
  cases fuel with
  | zero =>
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | succ fuel =>
    rw [executeRounds_abort worldRoles (fun x => worldRoles_honest_pure x) D A F fuel st steps hab h] at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    · simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      rfl

end Round

/-! ## Programs that reach a round -/

section Programs

variable {ι : Type} {G : OracleSpec ι}

/-- The local work of the program stops at an abort or at a round. After the round, the program aborts
at once if the inbox holds an abort frame. -/
def StartsWithRound {α : Type} (p : PartyM C E G α) : Prop :=
  ∀ step ∈ support (advance p.run), step = .done none ∨
    ∃ outbox resume, step = .wait outbox resume ∧
      ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none)

/-- A round with `exchange` aborts on an abort frame, so it starts each continuation. -/
theorem startsWithRound_exchange_bind {α : Type} (outbox : Mail C E) (f : Mail C E → PartyM C E G α) :
    StartsWithRound (exchange outbox >>= f) := by
  intro step hs
  rw [advance_exchange_bind, support_pure, Set.mem_singleton_iff] at hs
  subst hs
  refine Or.inr ⟨outbox, _, rfl, fun inbox ⟨k, hk⟩ => ?_⟩
  have hany : (C.parties.any fun j => Msg.isAbort (inbox j)) = true :=
    List.any_eq_true.2 ⟨k, List.mem_finRange k, by simp [hk, Msg.isAbort]⟩
  simp only [exchangeResume, hany, ite_true, advance_pure]

/-- Local work before the round keeps the property. -/
theorem startsWithRound_oracleStep_bind {α β : Type} (oa : OracleComp (RoSpec C) β)
    (f : β → PartyM C E G α) (h : ∀ b, StartsWithRound (f b)) :
    StartsWithRound (oracleStep oa >>= f) := by
  intro step hs
  rw [advance_oracleStep_bind, mem_support_bind_iff] at hs
  obtain ⟨b, -, hb⟩ := hs
  exact h b step hb

/-- Local work in the local oracles before the round keeps the property. -/
theorem startsWithRound_localStep_bind {α β : Type} (oa : OracleComp (LocalSpec C) β)
    (f : β → PartyM C E G α) (h : ∀ b, StartsWithRound (f b)) :
    StartsWithRound (localStep oa >>= f) := by
  intro step hs
  rw [advance_localStep_bind, mem_support_bind_iff] at hs
  obtain ⟨b, -, hb⟩ := hs
  exact h b step hb

/-- A `require` before the round keeps the property, because a failed `require` aborts. -/
theorem startsWithRound_require_bind {α : Type} (c : Prop) (f : Unit → PartyM C E G α)
    (h : StartsWithRound (f ())) : StartsWithRound (require c >>= f) := by
  intro step hs
  rw [advance_require_bind] at hs
  split_ifs at hs
  · exact h step hs
  · rw [support_pure, Set.mem_singleton_iff] at hs
    exact Or.inl hs

/-- Any continuation after the program keeps the property. -/
theorem startsWithRound_bind {α β : Type} (p : PartyM C E G α) (k : α → PartyM C E G β)
    (h : StartsWithRound p) : StartsWithRound (p >>= k) := by
  intro step hs
  rw [advance_bind, mem_support_bind_iff] at hs
  obtain ⟨s, hs, hstep⟩ := hs
  rcases h s hs with rfl | ⟨outbox, resume, rfl, hres⟩
  · simp only [continueStep, support_pure, Set.mem_singleton_iff] at hstep
    exact Or.inl hstep
  · simp only [continueStep, support_pure, Set.mem_singleton_iff] at hstep
    refine Or.inr ⟨outbox, _, hstep, fun inbox hk => ?_⟩
    rw [advance_bind]
    change advance (resume inbox) >>= continueStep k = _
    rw [hres inbox hk, pure_bind]
    rfl

/-- Any continuation after a program on the run state keeps the property. -/
theorem startsWithRound_run_bind {α β : Type} (p : RunM C E G α) (k : α → RunM C E G β) (st : RunState C)
    (h : StartsWithRound (p.run st)) : StartsWithRound ((p >>= k).run st) := by
  rw [StateT.run_bind]
  exact startsWithRound_bind _ _ h

/-- Each honest step of a cut whose programs start with a round is done or rejects an abort frame. -/
theorem isDone_or_rejectsAbort {α : Type} (p : PartyM C E G α) (h : StartsWithRound p)
    (step : Step C E G α) (hs : step ∈ support (advance p.run)) : step.isDone ∨ RejectsAbort step := by
  rcases h step hs with rfl | hw
  · exact Or.inl trivial
  · exact Or.inr hw

/-- A step that the honest roles of the real game give for the local work of a program, under a
handler of `WorldSpec` with a state, is a step of the plain program. So `StartsWithRound` holds for
the steps under each such handler. -/
theorem mem_support_advance_of_handler {α σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (p : PartyM C E G α) (s : σ) (step : Step C E G α)
    (hs : step ∈ support ((simulateQ impl (worldRoles.honest (advance p.run))).run' s)) :
    step ∈ support (advance p.run) :=
  support_simulateQ_subset _ _ (support_simulateQ_run'_subset impl _ s hs)

end Programs

/-! ## The forms of the opening and of the check -/

section Forms

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C) {ι : Type} {G : OracleSpec ι}

/-- `OpenSh` starts with its round. -/
theorem startsWithRound_openSh (v : ℕ → E) (count : ℕ) : StartsWithRound (openSh (G := G) K ctx v count) :=
  startsWithRound_exchange_bind _ _

/-- `OpenRep` makes local hash calls and then sends its round. -/
theorem startsWithRound_openRep (v : Shares C Bit) (count : ℕ) :
    StartsWithRound (openRep (G := G) K ctx v count) :=
  startsWithRound_oracleStep_bind _ _ fun _ => startsWithRound_exchange_bind _ _

/-- The coin key of the real check draws its PRSS outputs and then sends the round of `OpenSh`. -/
theorem startsWithRound_coinKey (st : RunState C) :
    StartsWithRound ((coinKey (G := G) K (realCheckBuildingBlocks K ctx)).run st) := by
  unfold coinKey
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  refine startsWithRound_run_bind _ _ _ ?_
  change StartsWithRound ((prssRandomness ctx (elementCodec K) 1 2 >>= fun r => coinWith K ctx r 2).run st)
  rw [prssRandomness_run]
  refine startsWithRound_oracleStep_bind _ _ fun o => ?_
  unfold coinWith
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  exact startsWithRound_bind _ _ (startsWithRound_openSh K ctx _ _)

/-- The check of a batch with a positive count starts with the round of its first coin. -/
theorem startsWithRound_check (tuples : List (Tuple C)) (hcount : (tuples.map (·.count)).sum ≠ 0)
    (st : RunState C) :
    StartsWithRound ((check (G := G) K ctx (realCheckBuildingBlocks K ctx) tuples).run st) := by
  unfold check
  dsimp only
  rw [ite_eq_right hcount]
  exact startsWithRound_run_bind _ _ _ (startsWithRound_coinKey K ctx st)

/-- With the count 0 the check makes no round, and the batch goes on to the round of `OpenRep`. -/
theorem startsWithRound_verify_output_zero {β : Type} (mode : ReshareMode) (tuples : List (Tuple C))
    (hcount : (tuples.map (·.count)).sum = 0) (v : Shares C Bit) (count : ℕ) (k : (ℕ → Bit) → RunM C E G β)
    (st : RunState C) :
    StartsWithRound (((realRunBuildingBlocks K ctx mode).verify tuples >>= fun _ =>
      (realRunBuildingBlocks K ctx mode).output v count >>= k).run st) := by
  rw [StateT.run_bind]
  change StartsWithRound ((check K ctx (realCheckBuildingBlocks K ctx) tuples).run st >>= _)
  have hzero : (check (G := G) K ctx (realCheckBuildingBlocks K ctx) tuples).run st = pure ((), st) := by
    unfold check
    dsimp only
    rw [ite_eq_left hcount]
    rfl
  rw [hzero, pure_bind]
  rw [StateT.run_bind]
  change StartsWithRound ((StateT.lift (openRep K ctx v count)).run st >>= _)
  rw [StateT.run_lift, bind_assoc]
  exact startsWithRound_bind _ _ (startsWithRound_openRep K ctx v count)

/-- The end of the check and the opening. The last `require` of the check comes before the round
of `OpenRep`. -/
theorem startsWithRound_require_output {β : Type} (mode : ReshareMode) (c : Prop) (v : Shares C Bit)
    (count : ℕ) (k : (ℕ → Bit) → RunM C E G β) (st : RunState C) :
    StartsWithRound ((StateT.lift (require c) >>= fun _ =>
      (realRunBuildingBlocks K ctx mode).output v count >>= k).run st) := by
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  refine startsWithRound_require_bind _ _ ?_
  rw [pure_bind, StateT.run_bind]
  change StartsWithRound ((StateT.lift (openRep K ctx v count)).run st >>= _)
  rw [StateT.run_lift, bind_assoc]
  exact startsWithRound_bind _ _ (startsWithRound_openRep K ctx v count)

/-- The check and the opening of a batch start with a round for each count. With a positive count
the round is the first coin of the check, and with the count 0 it is the round of `OpenRep`. -/
theorem startsWithRound_verify_output {β : Type} (mode : ReshareMode) (tuples : List (Tuple C))
    (v : Shares C Bit) (count : ℕ) (k : (ℕ → Bit) → RunM C E G β) (st : RunState C) :
    StartsWithRound (((realRunBuildingBlocks K ctx mode).verify tuples >>= fun _ =>
      (realRunBuildingBlocks K ctx mode).output v count >>= k).run st) := by
  by_cases hcount : (tuples.map (·.count)).sum = 0
  · exact startsWithRound_verify_output_zero K ctx mode tuples hcount v count k st
  · exact startsWithRound_run_bind _ _ _ (startsWithRound_check K ctx tuples hcount st)

end Forms

/-! ## The cut -/

section Cut

variable {I O L R Ia α : Type}

/-- No honest output after a partial abort, under each handler of `WorldSpec` with a state. At the
cut, an honest operator is at `.done none`, and each other honest operator is done or is at a step
of a program that starts with a round. Then each honest operator at such a step ends with no
output. The programs are, for example, `startsWithRound_openRep`, `startsWithRound_check` and
`startsWithRound_verify_output` with any continuation (`startsWithRound_bind`). -/
theorem executeRounds_cut_noOutput {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) (prog : C.Party → PartyM C E (CallSpec I O) α)
    (hab : ∃ a ∉ D.1, steps a = .done none)
    (hcut : ∀ i ∉ D.1, (steps i).isDone ∨
      (StartsWithRound (prog i) ∧ steps i ∈ support (advance (prog i).run)))
    (s : σ) (z : (A.State × (C.Party → Option α)) × σ)
    (hz : z ∈ support ((simulateQ impl (executeRounds worldRoles D A F fuel st steps)).run s))
    (i : C.Party) (hlive : steps i ∈ support (advance (prog i).run))
    (hprog : StartsWithRound (prog i)) : z.1.2 i = none := by
  have h : ∀ j ∉ D.1, (steps j).isDone ∨ RejectsAbort (steps j) := fun j hj =>
    (hcut j hj).elim Or.inl fun hp => isDone_or_rejectsAbort _ hp.1 _ hp.2
  rw [executeRounds_abort_support impl D A F fuel st steps hab h s z hz]
  rcases hprog _ hlive with hs | ⟨outbox, resume, hs, -⟩ <;> simp [hs, Step.output]

end Cut

end ThresholdLeanXmss.Sketch

/-- info: 'ThresholdLeanXmss.Sketch.executeRounds_cut_noOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmss.Sketch.executeRounds_cut_noOutput

/-- info: 'ThresholdLeanXmss.Sketch.startsWithRound_verify_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmss.Sketch.startsWithRound_verify_output
