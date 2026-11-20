import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RecordedRun

/-!
# The rounds of an opening on the recorded run

The section `LiveRounds` follows one step of each honest operator on the recorded run (`Reach`,
`StepReach`, `FreePath`) and states the wait for the open frames (`OpenWait`). The section
`RecordedOpening` counts the rounds of a recorded batch (`TimedLog`) and gives the place of each
start and each opening in the log (`WaitAt`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace LiveRounds

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The wait of depth `n` -/

section Reach

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α ρ : Type}

/-- On each path, the program ends with a leaf in `P` before its wait of depth `n`, or it reaches
its wait of depth `n`, and the outbox and the continuation of that wait are in `Q`. -/
inductive Reach {γ : Type} (P : γ → Prop)
    (Q : Mail C E → (Mail C E → OracleComp (PartySpec C E G) γ) → Prop) :
    ℕ → OracleComp (PartySpec C E G) γ → Prop
  | early (n : ℕ) (x : γ) (h : P x) : Reach P Q n (pure x)
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E G) γ)
      (h : ∀ r, Reach P Q n (k r)) : Reach P Q n (.liftBind (.inl (.inl q)) k)
  | here (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E G) γ) (h : Q out k) :
      Reach P Q 0 (.liftBind (.inl (.inr out)) k)
  | round (n : ℕ) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E G) γ)
      (h : ∀ r, Reach P Q n (k r)) : Reach P Q (n + 1) (.liftBind (.inl (.inr out)) k)

/-- A ghost step that is done with a leaf in `P`, or that waits at depth `n` of its program. -/
def StepReach (P : Option α × ρ → Prop)
    (Q : Mail C E → (Mail C E → OracleComp (PartySpec C E G) (Option α × ρ)) → Prop) (n : ℕ) :
    RStep C E G α ρ → Prop
  | .done out record => P (out, record)
  | .wait outbox resume => match n with
    | 0 => Q outbox resume
    | n + 1 => ∀ inbox, Reach P Q n (resume inbox)
  | .call _ _ => False

/-- The outputs and records that a ghost step can still give, on each answer. -/
def stepOutputs : RStep C E G α ρ → Set (Option α × ρ)
  | .done out record => {(out, record)}
  | .wait _ resume => ⋃ inbox, support (resume inbox)
  | .call _ resume => ⋃ r, support (resume r)

/-- The local steps of a program stop at a step whose outputs are outputs of the program. -/
theorem stepOutputs_advanceR (p : OracleComp (PartySpec C E G) (Option α × ρ)) :
    ∀ s ∈ support (advanceR p), stepOutputs s ⊆ support p := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro s hs
    change s ∈ support (pure (RStep.done x.1 x.2) : OracleComp (LocalSpec C) _) at hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, support_pure]
    rfl
  | query_bind t k ih =>
    intro s hs y hy
    rw [mem_support_bind_iff]
    rcases t with (q | outbox) | input
    · have hR : advanceR (liftM (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl q))) >>= k) =
          OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (k r) := rfl
      rw [hR, mem_support_bind_iff] at hs
      obtain ⟨r, -, hr⟩ := hs
      exact ⟨r, by simp, ih r s hr hy⟩
    · change s ∈ support (pure (RStep.wait outbox k) : OracleComp (LocalSpec C) _) at hs
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      obtain ⟨inbox, hy⟩ := Set.mem_iUnion.1 hy
      exact ⟨inbox, by simp, hy⟩
    · change s ∈ support (pure (RStep.call input k) : OracleComp (LocalSpec C) _) at hs
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      obtain ⟨r, hy⟩ := Set.mem_iUnion.1 hy
      exact ⟨r, by simp, hy⟩

end Reach

/-! ## The lockstep of the ghost executor -/

section Execution

variable {C : Committee} {E : Type} {Ia L Rs O α ρ : Type}
  (D : C.Coalition) (net : Adversary C E Ia L Rs) (F : Functionality C PEmpty O L Rs) (blank : ρ)

/-- The mail that operator `i` gets in a round of the ghost executor from the steps `steps` and the
messages `sent` of the corrupt operators. -/
def roundInbox (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ) (sent : C.Party → C.Party → Option (Msg E))
    (i : C.Party) : Mail C E :=
  fun c => if c ∈ D.1 then sent c i else (steps c).delivered i

/-- The next ghost step of an honest step on the mail `inbox`. -/
def stepNext : RStep C E (CallSpec PEmpty O) α ρ → Mail C E → OracleComp (LocalSpec C) (RStep C E (CallSpec PEmpty O) α ρ)
  | .done out record, _ => pure (.done out record)
  | .wait _ resume, inbox => advanceR (resume inbox)
  | .call _ _, _ => pure (.done none blank)

/-- The rest of the program of an honest step on the mail `inbox`. -/
def nextR : RStep C E (CallSpec PEmpty O) α ρ → Mail C E → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ)
  | .done out record, _ => pure (out, record)
  | .wait _ resume, inbox => resume inbox
  | .call _ _, _ => pure (none, blank)

/-- A round of the ghost executor with no call. Each honest step goes to its next step on the mail of
the round, and the messages of the round are those of the corrupt operators. -/
theorem stepRoundR_next (state : net.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ) :
    ∀ r ∈ support (stepRoundR worldRoles D net F blank state steps), ∀ i, i ∉ D.1 →
      r.2.1 i ∈ support (stepNext blank (steps i) (roundInbox D steps r.2.2 i)) := by
  have hcall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, -, hi⟩, -⟩
    cases hs : steps i with
    | done out record => rw [hs] at hi; exact absurd hi (by simp [RStep.callInput])
    | wait outbox resume => rw [hs] at hi; exact absurd hi (by simp [RStep.callInput])
    | call input resume => exact input.elim
  intro r hr i hi
  unfold stepRoundR at hr
  simp only [hcall, ↓reduceIte] at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨⟨st, sent⟩, -, hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨steps', hsteps', hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  have hj := Fuel.mem_support_sequenceFin _ steps' hsteps' i
  show steps' i ∈ support (stepNext blank (steps i) (roundInbox D steps sent i))
  revert hj
  cases steps i with
  | done out record =>
    intro hj
    rw [stepNext, support_pure]
    simpa only [support_pure] using hj
  | wait outbox resume =>
    intro hj
    simp only [hi, ↓reduceIte] at hj
    exact Fuel.mem_support_honest _ _ hj
  | call input resume => exact input.elim

/-- The outputs of a ghost step are outputs of `prog`, or have the record `blank`. -/
def FreePath (prog : OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ))
    (step : RStep C E (CallSpec PEmpty O) α ρ) : Prop :=
  ∀ x ∈ stepOutputs step, x.2 = blank ∨ x ∈ support prog

/-- The next step of an honest step is on the path of the rest of its program. -/
theorem freePath_stepNext (step : RStep C E (CallSpec PEmpty O) α ρ) (inbox : Mail C E) :
    ∀ s ∈ support (stepNext blank step inbox), FreePath blank (nextR blank step inbox) s := by
  intro s hs x hx
  cases step with
  | done out record =>
    rw [stepNext, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    right
    rw [Set.mem_singleton_iff.1 hx, nextR, support_pure]
    rfl
  | wait outbox resume => exact Or.inr (stepOutputs_advanceR _ s hs hx)
  | call input resume => exact input.elim

/-- A round of the ghost executor keeps each honest step on the path of `prog`. -/
theorem stepRoundR_freePath (prog : C.Party → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ))
    (state : net.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ)
    (h : ∀ i, i ∉ D.1 → FreePath blank (prog i) (steps i)) :
    ∀ r ∈ support (stepRoundR worldRoles D net F blank state steps), ∀ i, i ∉ D.1 →
      FreePath blank (prog i) (r.2.1 i) := by
  intro r hr i hi x hx
  have hn := stepRoundR_next D net F blank state steps r hr i hi
  have hs := h i hi
  revert hn hs
  cases steps i with
  | done out record =>
    intro hn hs
    rw [stepNext, support_pure, Set.mem_singleton_iff] at hn
    rw [hn] at hx
    exact hs x hx
  | wait outbox resume =>
    intro hn hs
    exact hs x (Set.mem_iUnion.2 ⟨_, stepOutputs_advanceR _ _ hn hx⟩)
  | call input resume => exact input.elim

/-- The rounds of the ghost executor keep each honest step on the path of `prog`. -/
theorem executeRoundsR_freePath (prog : C.Party → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ)) :
    ∀ (fuel : ℕ) (state : net.State) (steps : C.Party → RStep C E (CallSpec PEmpty O) α ρ),
      (∀ i, i ∉ D.1 → FreePath blank (prog i) (steps i)) →
      ∀ z ∈ support (executeRoundsR worldRoles D net F blank fuel state steps), ∀ i, i ∉ D.1 →
        FreePath blank (prog i) (z.2 i)
  | 0, state, steps, h, z, hz, i, hi => by
    simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h i hi
  | fuel + 1, state, steps, h, z, hz, i, hi => by
    unfold executeRoundsR at hz
    split_ifs at hz
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h i hi
    · rw [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      exact executeRoundsR_freePath prog fuel r.1 r.2.1 (stepRoundR_freePath D net F blank prog state steps h r hr)
        z hz i hi

/-- The record of a step on the path of `prog` is `blank` or a record of an output of `prog`. -/
theorem FreePath.record {prog : OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ)}
    {step : RStep C E (CallSpec PEmpty O) α ρ} (h : FreePath blank prog step) :
    step.record blank = blank ∨ ∃ out, (out, step.record blank) ∈ support prog := by
  cases step with
  | done out record =>
    rcases h (out, record) rfl with h | h
    · exact Or.inl h
    · exact Or.inr ⟨out, h⟩
  | wait outbox resume => exact Or.inl rfl
  | call input resume => exact Or.inl rfl

end Execution

/-! ## The opening of batch `k` in the ghost run -/

section Opening

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)
  (budget : StartBudget)

/-- The depth of the exchange of `OpenRep` of batch `k` of the first ceremony under `parameter`. It
is the PRSS setup and the rounds of the batches up to `k`, less the last round, which is the round
of `OpenRep`. It reads only the public data. -/
def openPos (parameter : PublicParameter) (tree : Tree) (k : ℕ) : ℕ :=
  setupRounds + (((chunks settings.batchSize (CheckTiming.firstJobs tree)).take (k + 1)).map fun batch =>
    CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum - 1

/-- A leaf of a recorded program before the exchange of `OpenRep` of batch `k`. It is an abort, and
its record has at most `k` openings. -/
def OpenLeaf (k : ℕ) (x : Option TreeOutput × Record C E) : Prop :=
  x.1 = none ∧ (openingsOf x.2).length ≤ k

/-- The exchange of `OpenRep` of batch `k` at operator `j`. The outbox is the message of `OpenRep` of
the start `b` that each later record holds at index `k`, and each later record that holds an opening
at index `k` holds the received mail, with no abort frame in it. -/
def OpenWait (j : C.Party) (k : ℕ) (out : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option TreeOutput × Record C E)) : Prop :=
  (∃ (b : BatchStart C) (digests : List HashOutput),
      out = repOutbox K j b.v' (outputsOf b.circuits).length digests ∧
      ∀ inbox, ∀ x ∈ support (resume inbox), (startsOf x.2)[k]? = some b) ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), ∀ v inbox', (openingsOf x.2)[k]? = some (v, inbox') →
      inbox' = inbox ∧ ∀ c, inbox c ≠ some .abort

end Opening

end LiveRounds

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace RecordedOpening

open LiveRounds

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## Exact timing with a predicate on the leaves -/

section Generic

variable {C : Committee} {E : Type} {γ δ : Type}

/-- On each path, the program ends with a leaf in `A` at any depth, or with a leaf in `B` after
exactly `n` rounds. -/
inductive TimedLog (A B : γ → Prop) : ℕ → OracleComp (PartySpec C E RealSpec) γ → Prop
  | stop (n : ℕ) (x : γ) (h : A x) : TimedLog A B n (pure x)
  | done (x : γ) (h : B x) : TimedLog A B 0 (pure x)
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ r, TimedLog A B n (k r)) : TimedLog A B n (.liftBind (.inl (.inl q)) k)
  | round (n : ℕ) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ r, TimedLog A B n (k r)) : TimedLog A B (n + 1) (.liftBind (.inl (.inr out)) k)

/-- A timed program and then a timed continuation take the sum of the two depths. -/
theorem TimedLog.bind {A B : γ → Prop} {A' B' : δ → Prop} {m n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) γ} {g : γ → OracleComp (PartySpec C E RealSpec) δ}
    (hp : TimedLog A B m p) (hA : ∀ x, A x → ∃ y, g x = pure y ∧ A' y)
    (hB : ∀ x, B x → TimedLog A' B' n (g x)) : TimedLog A' B' (m + n) (p >>= g) := by
  induction hp with
  | stop m x hx =>
    obtain ⟨y, hy, hy'⟩ := hA x hx
    rw [pure_bind, hy]
    exact TimedLog.stop _ y hy'
  | done x hx =>
    rw [pure_bind, Nat.zero_add]
    exact hB x hx
  | queryLocal m q k _ ih => exact TimedLog.queryLocal (m + n) q _ ih
  | round m out k _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact TimedLog.round (m + n) out _ ih

/-- A timed program and then a continuation that reaches its wait of depth `n` reach that wait at
depth `m + n`. -/
theorem TimedLog.reach_bind {A B : γ → Prop} {P : δ → Prop}
    {Q : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) δ) → Prop} {m n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) γ} {g : γ → OracleComp (PartySpec C E RealSpec) δ}
    (hp : TimedLog A B m p) (hA : ∀ x, A x → ∃ y, g x = pure y ∧ P y)
    (hB : ∀ x, B x → Reach P Q n (g x)) : Reach P Q (m + n) (p >>= g) := by
  induction hp with
  | stop m x hx =>
    obtain ⟨y, hy, hy'⟩ := hA x hx
    rw [pure_bind, hy]
    exact Reach.early _ y hy'
  | done x hx =>
    rw [pure_bind, Nat.zero_add]
    exact hB x hx
  | queryLocal m q k _ ih => exact Reach.queryLocal (m + n) q _ ih
  | round m out k _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Reach.round (m + n) out _ ih

/-- A program that reaches its wait of depth `n` keeps that wait with a continuation that keeps
its leaves. -/
theorem reach_bind_left {P : γ → Prop} {P' : δ → Prop}
    {Q : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {Q' : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) δ) → Prop} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) γ} {g : γ → OracleComp (PartySpec C E RealSpec) δ}
    (hp : Reach P Q n p) (hP : ∀ x, P x → ∃ y, g x = pure y ∧ P' y)
    (hQ : ∀ out resume, Q out resume → Q' out fun r => resume r >>= g) : Reach P' Q' n (p >>= g) := by
  induction hp with
  | early n x hx =>
    obtain ⟨y, hy, hy'⟩ := hP x hx
    rw [pure_bind, hy]
    exact Reach.early n y hy'
  | queryLocal n q k _ ih => exact Reach.queryLocal n q _ ih
  | here out k hq => exact Reach.here out _ (hQ out k hq)
  | round n out k _ ih => exact Reach.round n out _ ih

/-- A map of the leaves keeps the wait of depth `n`. -/
theorem reach_map {P : γ → Prop} {P' : δ → Prop}
    {Q : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {Q' : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) δ) → Prop} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) γ} (g : γ → δ)
    (hp : Reach P Q n p) (hP : ∀ x, P x → P' (g x))
    (hQ : ∀ out resume, Q out resume → Q' out fun r => g <$> resume r) : Reach P' Q' n (g <$> p) := by
  rw [map_eq_bind_pure_comp]
  refine reach_bind_left hp (fun x hx => ⟨g x, rfl, hP x hx⟩) fun out resume h => ?_
  have hres : (fun r => resume r >>= pure ∘ g) = fun r => g <$> resume r :=
    funext fun r => (map_eq_bind_pure_comp _ g (resume r)).symm
  rw [hres]
  exact hQ out resume h

/-- A map of the leaves keeps the timing. -/
theorem TimedLog.map {A B : γ → Prop} {A' B' : δ → Prop} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) γ} (g : γ → δ)
    (hp : TimedLog A B n p) (hA : ∀ x, A x → A' (g x)) (hB : ∀ x, B x → B' (g x)) :
    TimedLog A' B' n (g <$> p) := by
  rw [map_eq_bind_pure_comp, ← Nat.add_zero n]
  exact hp.bind (fun x hx => ⟨g x, rfl, hA x hx⟩) fun x hx => TimedLog.done _ (hB x hx)

end Generic

/-! ## The recorded programs -/

section Rec

variable {C : Committee} {E : Type} {α β : Type}

/-- The rest of a recorded bind after the result and the record of its first part. -/
def recCont (f : α → RecM C E β) : Option α × List (RecEvent C E) →
    OracleComp (PartySpec C E RealSpec) (Option β × List (RecEvent C E))
  | (none, w) => pure (none, w)
  | (some a, w) => (fun y => (y.1, w ++ y.2)) <$> (f a).run.run

theorem run_recBind (x : RecM C E α) (f : α → RecM C E β) :
    (x >>= f).run.run = x.run.run >>= recCont f := by
  rw [OptionT.run_bind, Option.elimM, WriterT.run_bind]
  refine bind_congr fun z => ?_
  rcases z with ⟨_ | a, w⟩
  · simp [recCont]
  · simp [recCont]

theorem run_recLift (p : PartyM C E RealSpec α) :
    (RecM.lift p).run.run = (fun o => (o, [])) <$> p.run := by
  change (liftM p.run : WriterT (List (RecEvent C E)) _ _).run = _
  rw [WriterT.run_liftM]
  rfl

theorem run_recLift_bind (p : PartyM C E RealSpec α) (f : α → RecM C E β) :
    (RecM.lift p >>= f).run.run = p.run >>= fun o => o.elim (pure (none, [])) fun a => (f a).run.run := by
  rw [run_recBind, run_recLift, bind_map_left]
  refine bind_congr fun o => ?_
  rcases o with _ | a
  · rfl
  · simp [recCont]

theorem run_recRecord_bind (events : List (RecEvent C E)) (f : PUnit → RecM C E β) :
    (RecM.record events >>= f).run.run = (fun y => (y.1, events ++ y.2)) <$> (f PUnit.unit).run.run := by
  rw [run_recBind]
  simp [RecM.record, OptionT.run_lift, WriterT.run_tell, recCont]

theorem run_recPure (a : α) : (pure a : RecM C E α).run.run = pure (some a, []) := by
  simp

/-- A timed program with no record and then a timed continuation. -/
theorem timedLog_lift_bind {A B : Option β × List (RecEvent C E) → Prop} {m n : ℕ}
    {p : PartyM C E RealSpec α} {f : α → RecM C E β} (hp : Timed m p.run) (hA : A (none, []))
    (hf : ∀ a, TimedLog A B n (f a).run.run) : TimedLog A B (m + n) (RecM.lift p >>= f).run.run := by
  rw [run_recLift_bind]
  generalize p.run = oa at hp ⊢
  induction hp with
  | abort m => exact TimedLog.stop _ _ hA
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hf a
  | queryLocal m q k _ ih => exact TimedLog.queryLocal (m + n) q _ ih
  | round m out k _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact TimedLog.round (m + n) out _ ih
  | call m input k _ ih => exact input.elim

/-- A timed program with no record and then a continuation that reaches its wait of depth `n`. -/
theorem reach_lift_bind {P : Option β × List (RecEvent C E) → Prop}
    {Q : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) (Option β × List (RecEvent C E))) → Prop}
    {m n : ℕ} {p : PartyM C E RealSpec α} {f : α → RecM C E β} (hp : Timed m p.run) (hP : P (none, []))
    (hf : ∀ a, Reach P Q n (f a).run.run) : Reach P Q (m + n) (RecM.lift p >>= f).run.run := by
  rw [run_recLift_bind]
  generalize p.run = oa at hp ⊢
  induction hp with
  | abort m => exact Reach.early _ _ hP
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hf a
  | queryLocal m q k _ ih => exact Reach.queryLocal (m + n) q _ ih
  | round m out k _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact Reach.round (m + n) out _ ih
  | call m input k _ ih => exact input.elim

/-- An exchange with no record is a wait of depth `0`. The rest aborts on an abort frame. -/
theorem reach_lift_exchange {γ' : Type} {P : Option β × List (RecEvent C E) → Prop}
    {Q : Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) (Option β × List (RecEvent C E))) → Prop}
    (out : Mail C E) (h : Mail C E → PartyM C E RealSpec γ') (f : γ' → RecM C E β)
    (hQ : Q out fun inbox => if C.parties.any (fun c => Msg.isAbort (inbox c)) then pure (none, [])
      else (RecM.lift (h inbox) >>= f).run.run) :
    Reach P Q 0 (RecM.lift (exchange out >>= h) >>= f).run.run := by
  rw [run_recLift_bind]
  have he : (exchange (C := C) (G := RealSpec) out >>= h).run >>=
      (fun o => o.elim (pure (none, [])) fun a => (f a).run.run) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= fun inbox =>
        if C.parties.any (fun c => Msg.isAbort (inbox c)) then pure (none, [])
        else (h inbox).run >>= fun o => o.elim (pure (none, [])) fun a => (f a).run.run := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
    · simp only [Option.elim, hab, ↓reduceIte, OptionT.run_failure, pure_bind]
    · simp only [Option.elim, hab, Bool.false_eq_true, ↓reduceIte, OptionT.run_pure, pure_bind]
  rw [he]
  simp only [run_recLift_bind] at hQ
  exact Reach.here out _ hQ

end Rec

/-! ## The counts of a record and the stable wait of `OpenRep` -/

section Counts

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  {α β : Type}

/-- An abort whose record has at most `a` openings. -/
def Stop (a : ℕ) (x : Option α × Record C E) : Prop := x.1 = none ∧ (openingsOf x.2).length ≤ a

/-- A result whose record has `s` starts and `o` openings. -/
def Full (s o : ℕ) (x : Option α × Record C E) : Prop :=
  x.1.isSome ∧ (startsOf x.2).length = s ∧ (openingsOf x.2).length = o

/-- The exchange of `OpenRep` of the check with index `k` at operator `j`. The outbox is the
message of `OpenRep` of the start `b`. Each later record holds `b` at index `k`, holds an opening at
index `k` if the program gives a result, and the opening at index `k` holds the received mail with no
abort frame in it. -/
def WaitAt (j : C.Party) (k : ℕ) (out : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)) : Prop :=
  ∃ (b : BatchStart C) (digests : List HashOutput),
    out = repOutbox K j b.v' (outputsOf b.circuits).length digests ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), (startsOf x.2)[k]? = some b ∧
      (x.1.isSome → k < (openingsOf x.2).length) ∧
      ∀ v inbox', (openingsOf x.2)[k]? = some (v, inbox') → inbox' = inbox ∧ ∀ c, inbox c ≠ some .abort

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem startsOf_append (w w' : Record C E) : startsOf (w ++ w') = startsOf w ++ startsOf w' := by
  simp [startsOf, List.filterMap_append]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem openingsOf_append (w w' : Record C E) : openingsOf (w ++ w') = openingsOf w ++ openingsOf w' := by
  simp [openingsOf, List.filterMap_append]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem length_startsOf_append (w w' : Record C E) :
    (startsOf (w ++ w')).length = (startsOf w).length + (startsOf w').length := by
  rw [startsOf_append, List.length_append]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem length_openingsOf_append (w w' : Record C E) :
    (openingsOf (w ++ w')).length = (openingsOf w).length + (openingsOf w').length := by
  rw [openingsOf_append, List.length_append]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem length_startsOf_event (e : RecEvent C E) :
    (startsOf [e]).length = match e with | .start _ => 1 | _ => 0 := by
  cases e <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem length_openingsOf_event (e : RecEvent C E) :
    (openingsOf [e]).length = match e with | .opened _ _ => 1 | _ => 0 := by
  cases e <;> rfl

omit [Fintype E] [DecidableEq E] in
/-- The stable wait keeps its form under a later recorded continuation. -/
theorem WaitAt.bind {j : C.Party} {k : ℕ} {out : Mail C E}
    {resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)} (f : α → RecM C E β)
    (h : WaitAt K j k out resume) : WaitAt K j k out fun r => resume r >>= recCont f := by
  obtain ⟨b, digests, hout, h⟩ := h
  refine ⟨b, digests, hout, fun inbox x hx => ?_⟩
  rw [mem_support_bind_iff] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨h1, h2, h3⟩ := h inbox y hy
  rcases y with ⟨_ | a, w⟩
  · simp only [recCont, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨h1, h2, h3⟩
  · simp only [recCont, support_map, Set.mem_image] at hx
    obtain ⟨z, -, rfl⟩ := hx
    have hks : k < (startsOf w).length := (List.getElem?_eq_some_iff.1 h1).1
    have hko : k < (openingsOf w).length := h2 rfl
    refine ⟨?_, fun _ => ?_, fun v inbox' hv => h3 v inbox' ?_⟩
    · rw [startsOf_append, List.getElem?_append_left hks]
      exact h1
    · rw [openingsOf_append, List.length_append]
      omega
    · rwa [openingsOf_append, List.getElem?_append_left hko] at hv

omit [Fintype E] [DecidableEq E] in
/-- The stable wait after a prefix record with `k'` starts and `k'` openings is at index `k' + k`. -/
theorem WaitAt.shift {j : C.Party} {k k' : ℕ} {out : Mail C E}
    {resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)} (w : Record C E)
    (hs : (startsOf w).length = k') (ho : (openingsOf w).length = k')
    (h : WaitAt K j k out resume) :
    WaitAt K j (k' + k) out fun r => (fun y => (y.1, w ++ y.2)) <$> resume r := by
  obtain ⟨b, digests, hout, h⟩ := h
  refine ⟨b, digests, hout, fun inbox x hx => ?_⟩
  rw [support_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨h1, h2, h3⟩ := h inbox y hy
  refine ⟨?_, fun hsome => ?_, fun v inbox' hv => h3 v inbox' ?_⟩
  · rw [startsOf_append, List.getElem?_append_right (by omega), hs, Nat.add_sub_cancel_left]
    exact h1
  · rw [openingsOf_append, List.length_append, ho]
    have := h2 hsome
    omega
  · rwa [openingsOf_append, List.getElem?_append_right (by omega), ho, Nat.add_sub_cancel_left] at hv

omit [Fintype E] [DecidableEq E] in
/-- A recorded program that reaches its stable wait keeps it with any continuation. -/
theorem reach_recBind_left {j : C.Party} {k n : ℕ} {x : RecM C E α} (f : α → RecM C E β)
    (hx : Reach (Stop k) (WaitAt K j k) n x.run.run) :
    Reach (Stop k) (WaitAt K j k) n (x >>= f).run.run := by
  rw [run_recBind]
  refine reach_bind_left hx (fun y hy => ?_) fun out resume h => h.bind K f
  rcases y with ⟨_ | a, w⟩
  · exact ⟨(none, w), rfl, rfl, hy.2⟩
  · exact absurd hy.1 (by simp)

omit [Fintype E] [DecidableEq E] in
/-- A map of the result keeps the stable wait. -/
theorem reach_recMap {j : C.Party} {k n : ℕ} {x : RecM C E α} (g : α → β)
    (hx : Reach (Stop k) (WaitAt K j k) n x.run.run) :
    Reach (Stop k) (WaitAt K j k) n (g <$> x).run.run := by
  rw [map_eq_bind_pure_comp]
  exact reach_recBind_left K _ hx

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Timed recorded parts compose, and their counts add. -/
theorem timedLog_recBind {x : RecM C E α} {f : α → RecM C E β} {m n a₁ s₁ o₁ a₂ s₂ o₂ a s o : ℕ}
    (hx : TimedLog (Stop a₁) (Full s₁ o₁) m x.run.run)
    (hf : ∀ c, TimedLog (Stop a₂) (Full s₂ o₂) n (f c).run.run)
    (ha₁ : a₁ ≤ a) (ha₂ : o₁ + a₂ ≤ a) (hs : s₁ + s₂ = s) (ho : o₁ + o₂ = o) :
    TimedLog (Stop a) (Full s o) (m + n) (x >>= f).run.run := by
  rw [run_recBind]
  refine hx.bind (fun y hy => ?_) fun y hy => ?_
  · rcases y with ⟨_ | c, w⟩
    · exact ⟨(none, w), rfl, rfl, le_trans hy.2 ha₁⟩
    · exact absurd hy.1 (by simp)
  · rcases y with ⟨_ | c, w⟩
    · exact absurd hy.1 (by simp)
    obtain ⟨-, hs₁, ho₁⟩ := hy
    dsimp only at hs₁ ho₁
    show TimedLog _ _ n ((fun y => (y.1, w ++ y.2)) <$> (f c).run.run)
    refine (hf c).map _ (fun z hz => ⟨hz.1, ?_⟩) fun z hz => ⟨hz.1, ?_, ?_⟩
    · simp only [openingsOf_append, List.length_append]
      have := hz.2
      omega
    · simp only [startsOf_append, List.length_append]
      have := hz.2.1
      omega
    · simp only [openingsOf_append, List.length_append]
      have := hz.2.2
      omega

omit [Fintype E] [DecidableEq E] in
/-- A timed recorded prefix with `k'` starts and `k'` openings, and then a continuation that reaches
its stable wait of index `k`, reach the stable wait of index `k' + k`. -/
theorem reach_recBind {x : RecM C E α} {f : α → RecM C E β} {j : C.Party} {m n a₁ k' k kk : ℕ}
    (hx : TimedLog (Stop a₁) (Full k' k') m x.run.run)
    (hf : ∀ c, Reach (Stop k) (WaitAt K j k) n (f c).run.run) (ha : a₁ ≤ kk) (hk : k' + k = kk) :
    Reach (Stop kk) (WaitAt K j kk) (m + n) (x >>= f).run.run := by
  subst hk
  rw [run_recBind]
  refine hx.reach_bind (fun y hy => ?_) fun y hy => ?_
  · rcases y with ⟨_ | c, w⟩
    · exact ⟨(none, w), rfl, rfl, le_trans hy.2 ha⟩
    · exact absurd hy.1 (by simp)
  · rcases y with ⟨_ | c, w⟩
    · exact absurd hy.1 (by simp)
    obtain ⟨-, hs₁, ho₁⟩ := hy
    dsimp only at hs₁ ho₁
    show Reach _ _ n ((fun y => (y.1, w ++ y.2)) <$> (f c).run.run)
    refine reach_map _ (hf c) (fun z hz => ⟨hz.1, ?_⟩) fun out resume h => h.shift K w hs₁ ho₁
    simp only [openingsOf_append, List.length_append]
    have := hz.2
    omega

end Counts

section Batch

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem timed_pair {σ α : Type} {n : ℕ} {p : PartyM C E RealSpec α} (hp : Timed n p.run) (st : σ) :
    Timed n (p >>= fun a => pure (a, st)).run := by
  simpa only [Nat.add_zero] using hp.bind fun a => timed_pure (a, st)

omit [Fintype E] [DecidableEq E] in
theorem timed_repRest (i : C.Party) (v : Shares C Bit) (count : ℕ) (inbox : Mail C E) :
    Timed 0 (repRest (G := RealSpec) K i v count inbox).run := by
  unfold repRest
  exact Timed.oracleStep_bind 0 _ _ fun _ => Timed.require_bind 0 _ _ fun _ => timed_pure _

omit [Fintype E] [DecidableEq E] in
/-- The check of a recorded start covers the tuple count of its circuits. -/
theorem sum_batchTuples (b : BatchStart C) :
    ((batchTuples K b.mode b.circuits b.inputs b.zs b.v').map (·.count)).sum = tupleCount b.circuits := by
  have hs := congrArg (List.map Prod.fst) (batchTuples_shape K b.mode b.circuits b.inputs b.zs b.v')
  simp only [List.map_map, Function.comp_def, List.map_append, List.map_cons, List.map_nil] at hs
  rw [hs, tupleCount_eq, List.sum_append, List.sum_singleton]

omit [Fintype E] [DecidableEq E] in
/-- The check and the opening of a recorded start take the check rounds and one round. An abort
keeps at most one opening, and a result has one start and one opening. -/
theorem timedLog_recCheckOpen (b : BatchStart C) (k : ℕ) (st : ℕ × ℕ) :
    TimedLog (Stop 1) (Full 1 1) (checkLabels (tupleCount b.circuits) + 1)
      ((recCheckOpen K b k).run st).run.run := by
  simp only [recCheckOpen, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk,
    StateT.run_set, StateT.run_pure]
  rw [run_recRecord_bind]
  refine TimedLog.map _ (A := Stop 1) (B := Full 0 1) ?_ (fun z hz => ⟨hz.1, ?_⟩) fun z hz => ⟨hz.1, ?_, ?_⟩
  rotate_left
  · have := hz.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  · have := hz.2.1
    simp only [length_startsOf_append, length_startsOf_event]
    omega
  · have := hz.2.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  have hcheck := runTimed_realCheck (G := RealSpec) K b.ctx (batchTuples K b.mode b.circuits b.inputs b.zs b.v')
    b.state
  rw [sum_batchTuples] at hcheck
  rw [show checkLabels (tupleCount b.circuits) + 1 = checkLabels (tupleCount b.circuits) + (0 + (1 + 0)) by omega]
  refine timedLog_lift_bind (timed_pair hcheck st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  refine timedLog_lift_bind (timed_pair (timed_oracleStep _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  refine timedLog_lift_bind (timed_pair (timed_exchange _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₂ => ?_
  rw [run_recRecord_bind]
  refine TimedLog.map _ (A := Stop 0) (B := Full 0 0) ?_ (fun z hz => ⟨hz.1, ?_⟩) fun z hz => ⟨hz.1, ?_, ?_⟩
  rotate_left
  · have := hz.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  · have := hz.2.1
    simp only [length_startsOf_append, length_startsOf_event]
    omega
  · have := hz.2.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  rw [← Nat.add_zero 0]
  refine timedLog_lift_bind (timed_pair (timed_repRest K _ _ _ _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₃ => ?_
  rw [run_recRecord_bind]
  refine TimedLog.map _ (A := Stop 0) (B := Full 0 0) ?_ (fun z hz => ⟨hz.1, ?_⟩) fun z hz => ⟨hz.1, ?_, ?_⟩
  rotate_left
  · have := hz.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  · have := hz.2.1
    simp only [length_startsOf_append, length_startsOf_event]
    omega
  · have := hz.2.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  rw [run_recPure]
  exact TimedLog.done _ ⟨rfl, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The check and the opening of a recorded start at operator `j` reach the exchange of `OpenRep`
after the check rounds. -/
theorem reach_recCheckOpen (j : C.Party) (b : BatchStart C) (hj : b.ctx.self = j) (k : ℕ) (st : ℕ × ℕ) :
    Reach (Stop 0) (WaitAt K j 0) (checkLabels (tupleCount b.circuits))
      ((recCheckOpen K b k).run st).run.run := by
  simp only [recCheckOpen, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk,
    StateT.run_set, StateT.run_pure]
  rw [run_recRecord_bind]
  refine reach_map _ (P := Stop 0) (Q := fun out resume => ∃ digests : List HashOutput,
      out = repOutbox K j b.v' (outputsOf b.circuits).length digests ∧
      ∀ inbox, ∀ x ∈ support (resume inbox), (x.1.isSome → 0 < (openingsOf x.2).length) ∧
        ∀ v inbox', (openingsOf x.2)[0]? = some (v, inbox') → inbox' = inbox ∧ ∀ c, inbox c ≠ some .abort)
    ?_ (fun z hz => ⟨hz.1, ?_⟩) fun out resume h => ?_
  rotate_left
  · have := hz.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  · obtain ⟨digests, hout, h⟩ := h
    refine ⟨b, digests, hout, fun inbox x hx => ?_⟩
    rw [support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := h inbox y hy
    have ho : openingsOf ([RecEvent.start b] ++ y.2) = openingsOf y.2 := by
      rw [openingsOf_append]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [startsOf_append]
      rfl
    · rw [ho]
      exact h1
    · rw [ho]
      exact h2
  have hcheck := runTimed_realCheck (G := RealSpec) K b.ctx (batchTuples K b.mode b.circuits b.inputs b.zs b.v')
    b.state
  rw [sum_batchTuples] at hcheck
  rw [show checkLabels (tupleCount b.circuits) = checkLabels (tupleCount b.circuits) + (0 + 0) by omega]
  refine reach_lift_bind (timed_pair hcheck st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  refine reach_lift_bind (timed_pair (timed_oracleStep _) _) ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  refine reach_lift_exchange _ _ _ ⟨p₁.1, by rw [hj], fun inbox x hx => ?_⟩
  by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
  · simp only [hab, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp [openingsOf]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte, run_recLift_bind, OptionT.run_pure, pure_bind,
      Option.elim] at hx
    rw [run_recRecord_bind, support_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    have ho : openingsOf ([RecEvent.opened b.v' inbox] ++ y.2) = (b.v', inbox) :: openingsOf y.2 := by
      rw [openingsOf_append]
      rfl
    rw [ho]
    refine ⟨fun _ => Nat.succ_pos _, fun v inbox' hv => ?_⟩
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hv
    refine ⟨hv.2.symm, fun c hc => hab ?_⟩
    rw [List.any_eq_true]
    exact ⟨c, List.mem_finRange c, by rw [hc]; rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The AND layers of a recorded batch take `mode.rounds` rounds each. -/
theorem runTimed_recLayers (ctx : Context C) (mode : ReshareMode) (cs : List Circuit)
    (inputs : List (C.Term → List Bit)) (n : ℕ) :
    RunTimed (n * mode.rounds) (recLayers K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs n) := by
  unfold recLayers
  refine (RunTimed.foldlM (n := mode.rounds) _ (fun zs l => ?_) (List.range n) _).of_eq (by rw [List.length_range])
  rw [map_eq_bind_pure_comp, ← Nat.add_zero mode.rounds]
  exact (runTimed_realMult K ctx mode _ _ _).bind fun z => runTimed_pure _

omit [Fintype E] [DecidableEq E] in
/-- A full recorded batch takes `exactBatchRounds`. An abort keeps at most one opening, and a result
has one start and one opening. -/
theorem timedLog_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ) :
    TimedLog (Stop 1) (Full 1 1) (CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)))
      ((recBatch K circuits settings ctx parameter jobs).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk]
  have harith : CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)) =
      0 + (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds +
        (1 + (checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1))) := by
    unfold CheckTiming.exactBatchRounds checkLabels
    split_ifs <;> omega
  rw [harith]
  refine timedLog_lift_bind (timed_pair (timed_inputShares ctx jobs) _) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  refine timedLog_lift_bind (timed_pair (runTimed_recLayers K ctx settings.mode _ _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  refine timedLog_lift_bind (timed_pair (runTimed_realRerand K ctx settings.mode _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₂ => ?_
  exact timedLog_recCheckOpen K ⟨(realRunBuildingBlocks K ctx settings.mode).mode, jobs, parameter,
    jobs.map (circuits parameter ·.kind), p.1, p₁.1.1, p₂.1.1, ctx, p₂.1.2⟩ k p₂.2

omit [Fintype E] [DecidableEq E] in
/-- A recorded batch at operator `ctx.self` reaches its exchange of `OpenRep` one round before its
end. -/
theorem reach_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ) :
    Reach (Stop 0) (WaitAt K ctx.self 0)
      (CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)) - 1)
      ((recBatch K circuits settings ctx parameter jobs).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk]
  have harith : CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)) - 1 =
      0 + (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds +
        (1 + checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))))) := by
    unfold CheckTiming.exactBatchRounds checkLabels
    split_ifs <;> omega
  rw [harith]
  refine reach_lift_bind (timed_pair (timed_inputShares ctx jobs) _) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  refine reach_lift_bind (timed_pair (runTimed_recLayers K ctx settings.mode _ _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₁ => ?_
  refine reach_lift_bind (timed_pair (runTimed_realRerand K ctx settings.mode _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ fun p₂ => ?_
  exact reach_recCheckOpen K ctx.self ⟨(realRunBuildingBlocks K ctx settings.mode).mode, jobs, parameter,
    jobs.map (circuits parameter ·.kind), p.1, p₁.1.1, p₂.1.1, ctx, p₂.1.2⟩ rfl k p₂.2

omit [Fintype E] [DecidableEq E] in
/-- Full recorded batches take the sum of their rounds. An abort keeps at most one opening for each
batch, and a result has one start and one opening for each batch. -/
theorem timedLog_recBatches (ctx : Context C) (parameter : PublicParameter) :
    ∀ (js : List (List Job)) (st : ℕ × ℕ),
      TimedLog (Stop js.length) (Full js.length js.length)
        ((js.map fun batch => CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum)
        ((js.mapM (recBatch K circuits settings ctx parameter)).run st).run.run
  | [], st => by
    simp only [List.mapM_nil, StateT.run_pure, run_recPure, List.map_nil, List.sum_nil, List.length_nil]
    exact TimedLog.done _ ⟨rfl, rfl, rfl⟩
  | jobs :: js, st => by
    rw [List.mapM_cons, StateT.run_bind, List.map_cons, List.sum_cons, List.length_cons]
    refine timedLog_recBind (a₂ := js.length) (s₂ := js.length) (o₂ := js.length)
      (timedLog_recBatch K circuits settings ctx parameter jobs st) (fun c => ?_)
      (by omega) (by omega) (by omega) (by omega)
    rw [StateT.run_bind, ← Nat.add_zero (List.sum _)]
    refine timedLog_recBind (a₂ := 0) (s₂ := 0) (o₂ := 0) (n := 0)
      (timedLog_recBatches ctx parameter js c.2) (fun q => ?_) (le_refl _) (by omega) (by omega) (by omega)
    rw [StateT.run_pure, run_recPure]
    exact TimedLog.done _ ⟨rfl, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The batches of a recorded ceremony at operator `ctx.self` reach the exchange of `OpenRep` of
batch `k` after the rounds of the batches before `k`. -/
theorem reach_recBatches (ctx : Context C) (parameter : PublicParameter) (js : List (List Job)) (k : ℕ)
    (hk : k < js.length) (st : ℕ × ℕ) :
    Reach (Stop k) (WaitAt K ctx.self k)
      (((js.take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum +
        (CheckTiming.exactBatchRounds settings.mode (js[k].map (circuits parameter ·.kind)) - 1))
      ((js.mapM (recBatch K circuits settings ctx parameter)).run st).run.run := by
  have hsplit : js = js.take k ++ js[k] :: js.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hmap : js.mapM (recBatch K circuits settings ctx parameter) =
      (js.take k ++ js[k] :: js.drop (k + 1)).mapM (recBatch K circuits settings ctx parameter) :=
    congrArg (List.mapM _) hsplit
  have hlen : (js.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  rw [hmap, List.mapM_append, StateT.run_bind]
  refine reach_recBind K (k := 0) (timedLog_recBatches K circuits settings ctx parameter (js.take k) st)
    (fun c => ?_) hlen.le (by rw [hlen, Nat.add_zero])
  rw [StateT.run_bind]
  refine reach_recBind_left K _ ?_
  rw [List.mapM_cons, StateT.run_bind]
  exact reach_recBind_left K _ (reach_recBatch K circuits settings ctx parameter js[k] c.2)

end Batch

/-! ## The recorded tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- The recorded ceremony of `jobs` at operator `j` reaches its exchange of `OpenRep` of batch `k`
at the depth of `reach_ceremonyRun`. -/
theorem reach_recRun (j : C.Party) (keys : Keys C) (jobs : List Job) (k : ℕ)
    (hk : k < (chunks settings.batchSize jobs).length) (st : ℕ × ℕ) :
    Reach (Stop k) (WaitAt K j k)
      (setupRounds + ((((chunks settings.batchSize jobs).take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits keys.parameter ·.kind))).sum +
        (CheckTiming.exactBatchRounds settings.mode
          (((chunks settings.batchSize jobs)[k]).map (circuits keys.parameter ·.kind)) - 1)))
      ((recRun K circuits settings j keys jobs).run st).run.run := by
  simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
  refine reach_lift_bind (timed_pair (timed_prssSetup j) st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_
  simp only [batched, StateT.run_bind]
  exact reach_recBind_left K _
    (reach_recBatches K circuits settings ⟨j, keys, p.1⟩ keys.parameter _ k hk p.2)

omit [Fintype E] [DecidableEq E] in
/-- The depth of `reach_ceremonyRun` is `openPos`. -/
theorem openDepth_eq (parameter : PublicParameter) (tree : Tree) (k : ℕ)
    (hk : k < (chunks settings.batchSize (CheckTiming.firstJobs tree)).length) :
    setupRounds + ((((chunks settings.batchSize (CheckTiming.firstJobs tree)).take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum +
        (CheckTiming.exactBatchRounds settings.mode
          (((chunks settings.batchSize (CheckTiming.firstJobs tree))[k]).map (circuits parameter ·.kind)) - 1)) =
      openPos circuits settings parameter tree k := by
  unfold openPos
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]
  have h2 : 2 ≤ CheckTiming.exactBatchRounds settings.mode
      (((chunks settings.batchSize (CheckTiming.firstJobs tree))[k]).map (circuits parameter ·.kind)) := by
    unfold CheckTiming.exactBatchRounds
    omega
  omega

end Tree

/-! ## The position of the opening in the recorded program -/

section Main

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings) (prims : Primitives) (budget : StartBudget)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A program that reaches its wait of depth `n` keeps it under weaker predicates. -/
theorem reach_mono {ι γ : Type} {G : OracleSpec ι} {P P' : γ → Prop}
    {Q Q' : Mail C E → (Mail C E → OracleComp (PartySpec C E G) γ) → Prop} {n : ℕ}
    {p : OracleComp (PartySpec C E G) γ} (hp : Reach P Q n p) (hP : ∀ x, P x → P' x)
    (hQ : ∀ out resume, Q out resume → Q' out resume) : Reach P' Q' n p := by
  induction hp with
  | early n x hx => exact Reach.early n x (hP x hx)
  | queryLocal n q k _ ih => exact Reach.queryLocal n q _ ih
  | here out k hq => exact Reach.here out _ (hQ out k hq)
  | round n out k _ ih => exact Reach.round n out _ ih

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem run_recFailure {α : Type} : (failure : RecM C E α).run.run = pure (none, []) := by
  rfl

end Main

end RecordedOpening

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening.openDepth_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening.openDepth_eq
