import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Joint
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Record

/-!
# Recorded programs on the ghost executor

General facts of recorded programs and of ghost phases.

* `timedR_of_timed` gives the exact timing of a recorded program from the timing of the program with
  its record dropped.
* `RecordCount s o p` states that each outcome of `p` has at most `s` starts in its record, and that
  each outcome with a result has exactly `s` starts and `o` openings. `recordCount_passRun` gives it
  for one run of the batches with the record of a pass.
* `prEvent_tail_le` bounds an event of a timed phase with a local tail by an event of the phase with
  no tail, and `phase_fuel_eq` states that more rounds than a timed phase takes give the same law.
* `executePhaseR_mapSteps` states that a map of the records of the honest programs maps the records
  of the honest steps of a ghost phase.
* `executePhaseR_dead` states that in a phase with a dead honest operator, each honest program that
  aborts on an abort frame with the record `w i` ends with the blank record or with `w i`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Timing

variable {C : Committee} {E : Type} {α ρ : Type}

/-- A recorded program is timed when the program with its record dropped is timed. -/
theorem timedR_of_timed {n : ℕ} (p : OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (h : Timed n (Prod.fst <$> p)) : TimedR n p := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure x =>
    rcases x with ⟨_ | a, w⟩
    · exact TimedLog.stop n _ rfl
    · change Timed n (pure (some a)) at h
      cases h
      exact TimedLog.done _ rfl
  | query_bind t k ih =>
    rcases t with (q | out) | input
    · change Timed n (PFunctor.FreeM.liftBind (Sum.inl (Sum.inl q)) fun r => Prod.fst <$> k r) at h
      cases h with
      | queryLocal n q k' hk => exact TimedLog.queryLocal n q k fun r => ih r (hk r)
    · change Timed n (PFunctor.FreeM.liftBind (Sum.inl (Sum.inr out)) fun r => Prod.fst <$> k r) at h
      cases h with
      | round n out k' hk => exact TimedLog.round n out k fun r => ih r (hk r)
    · exact input.elim

/-- A timed recorded program with its record dropped is timed. -/
theorem timed_of_timedR {n : ℕ} (p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (h : TimedR n p) :
    Timed n (Prod.fst <$> p) := by
  induction h with
  | stop n x hx =>
    rw [map_pure, hx]
    exact Timed.abort n
  | done x hx =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hx
    rw [map_pure, ha]
    exact Timed.done a
  | queryLocal n q k _ ih => exact Timed.queryLocal n q _ ih
  | round n out k _ ih => exact Timed.round n out _ ih

end Timing

/-! ## The starts and the openings in the outcomes of a recorded program -/

section Count

variable {C : Committee} {E : Type} {α β : Type}

/-- Each outcome of a recorded program has at most `s` starts in its record, and each outcome with a
result has exactly `s` starts and `o` openings. -/
def RecordCount (s o : ℕ) (p : OracleComp (PartySpec C E RealSpec) (Option α × Record C E)) : Prop :=
  ∀ x ∈ support p, (startsOf x.2).length ≤ s ∧
    (x.1.isSome → (startsOf x.2).length = s ∧ (openingsOf x.2).length = o)

theorem recordCount_recBind {s₁ o₁ s₂ o₂ : ℕ} {x : RecM C E α} {f : α → RecM C E β}
    (hx : RecordCount s₁ o₁ x.run.run) (hf : ∀ a, RecordCount s₂ o₂ (f a).run.run) :
    RecordCount (s₁ + s₂) (o₁ + o₂) (x >>= f).run.run := by
  intro z hz
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind x f z hz
  · exact ⟨(hx z₁ h₁).1.trans (Nat.le_add_right _ _), fun h => absurd h (by simp)⟩
  · obtain ⟨-, hx'⟩ := hx z₁ h₁
    obtain ⟨hs₁, ho₁⟩ := hx' (by rw [ha]; rfl)
    obtain ⟨hs₂, hf'⟩ := hf a z₂ h₂
    refine ⟨?_, fun hsome => ?_⟩
    · rw [length_startsOf_append, hs₁]
      omega
    · obtain ⟨hs₂', ho₂'⟩ := hf' hsome
      rw [length_startsOf_append, length_openingsOf_append, hs₁, ho₁, hs₂', ho₂']
      exact ⟨rfl, rfl⟩

theorem recordCount_pure (a : α) : RecordCount 0 0 (pure a : RecM C E α).run.run := by
  intro z hz
  rw [run_recPure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [startsOf, openingsOf]

theorem recordCount_failure (s o : ℕ) : RecordCount s o (failure : RecM C E α).run.run := by
  intro z hz
  change z ∈ support (pure (none, []) : OracleComp (PartySpec C E RealSpec) _) at hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [startsOf]

theorem recordCount_lift (p : PartyM C E RealSpec α) : RecordCount 0 0 (RecM.lift p).run.run := by
  intro z hz
  rw [run_recLift, support_map] at hz
  obtain ⟨o, -, rfl⟩ := hz
  simp [startsOf, openingsOf]

theorem recordCount_record (events : List (RecEvent C E)) :
    RecordCount (startsOf events).length (openingsOf events).length (RecM.record events).run.run := by
  intro z hz
  have h : (RecM.record events >>= fun u => (pure u : RecM C E PUnit)).run.run =
      (fun y => (y.1, events ++ y.2)) <$> (pure PUnit.unit : RecM C E PUnit).run.run :=
    run_recRecord_bind events pure
  rw [bind_pure] at h
  rw [h, run_recPure, map_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [startsOf, openingsOf]

variable {S : Type}

theorem recordCount_stateBind {s₁ o₁ s₂ o₂ : ℕ} {x : StateT S (RecM C E) α} {f : α → StateT S (RecM C E) β}
    (hx : ∀ st, RecordCount s₁ o₁ (x.run st).run.run) (hf : ∀ a st, RecordCount s₂ o₂ ((f a).run st).run.run) :
    ∀ st, RecordCount (s₁ + s₂) (o₁ + o₂) ((x >>= f).run st).run.run := fun st => by
  rw [StateT.run_bind]
  exact recordCount_recBind (hx st) fun p => hf p.1 p.2

theorem recordCount_stateBind0 {s o : ℕ} {x : StateT S (RecM C E) α} {f : α → StateT S (RecM C E) β}
    (hx : ∀ st, RecordCount 0 0 (x.run st).run.run) (hf : ∀ a st, RecordCount s o ((f a).run st).run.run) :
    ∀ st, RecordCount s o ((x >>= f).run st).run.run := fun st => by
  simpa only [Nat.zero_add] using recordCount_stateBind hx hf st

theorem recordCount_statePure (a : α) : ∀ st : S, RecordCount 0 0 ((pure a : StateT S (RecM C E) α).run st).run.run :=
  fun st => by
    rw [StateT.run_pure]
    exact recordCount_pure _

theorem recordCount_liftS (y : StateT S (PartyM C E RealSpec) α) :
    ∀ st, RecordCount 0 0 ((RecM.liftS y).run st).run.run := fun _ => recordCount_lift _

theorem recordCount_stateLift {s o : ℕ} (x : RecM C E α) (hx : RecordCount s o x.run.run) :
    ∀ st : S, RecordCount s o ((StateT.lift x : StateT S (RecM C E) α).run st).run.run := fun st => by
  rw [StateT.run_lift]
  simpa only [Nat.add_zero] using recordCount_recBind hx fun a => recordCount_pure (a, st)

theorem recordCount_get : ∀ st : S, RecordCount 0 0 ((get : StateT S (RecM C E) S).run st).run.run := fun st => by
  rw [StateT.run_get]
  exact recordCount_pure _

theorem recordCount_set (t : S) : ∀ st : S, RecordCount 0 0 ((set t : StateT S (RecM C E) PUnit).run st).run.run :=
  fun st => by
    rw [StateT.run_set]
    exact recordCount_pure _

theorem recordCount_mapM {γ : Type} {s o : ℕ} (f : γ → StateT S (RecM C E) α)
    (hf : ∀ a st, RecordCount s o ((f a).run st).run.run) :
    ∀ (l : List γ) (st : S), RecordCount (l.length * s) (l.length * o) ((l.mapM f).run st).run.run
  | [], st => by
    rw [List.mapM_nil, List.length_nil, Nat.zero_mul, Nat.zero_mul]
    exact recordCount_statePure _ st
  | a :: l, st => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.succ_mul, Nat.add_comm (l.length * s),
      Nat.add_comm (l.length * o)]
    refine recordCount_stateBind (hf a) (fun b => ?_) st
    simpa only [Nat.add_zero] using recordCount_stateBind (recordCount_mapM f hf l) fun bs => recordCount_statePure _

end Count

section PassCount

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
theorem recordCount_passCheckOpen (b : BatchStart C) (k : ℕ) :
    ∀ st, RecordCount 1 1 ((passCheckOpen K plainShares b k).run st).run.run := by
  have hrec : ∀ e : RecEvent C E, ∀ st, RecordCount (startsOf [e]).length (openingsOf [e]).length
      ((StateT.lift (RecM.record [e]) : StateT (ℕ × ℕ) (RecM C E) PUnit).run st).run.run :=
    fun e st => recordCount_stateLift _ (recordCount_record [e]) st
  unfold passCheckOpen
  refine recordCount_stateBind (s₂ := 0) (o₂ := 1) (hrec _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind (s₁ := 0) (o₁ := 1) (s₂ := 0) (o₂ := 0) (hrec _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind0 (hrec _) fun _ => ?_
  exact recordCount_stateBind0 (recordCount_set _) fun _ => recordCount_statePure _

omit [Fintype E] [DecidableEq E] in
theorem recordCount_passBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    ∀ st, RecordCount 1 1 ((passBatch K circuits settings plainShares ctx parameter jobs).run st).run.run := by
  unfold passBatch
  refine recordCount_stateBind0 recordCount_get fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  refine recordCount_stateBind0 (recordCount_liftS _) fun _ => ?_
  exact recordCount_passCheckOpen K _ _

omit [Fintype E] [DecidableEq E] in
/-- Each outcome of one run of the batches with the record of a pass has at most one start for each
batch, and an outcome with a result has exactly one start and one opening for each batch. -/
theorem recordCount_passRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    ∀ st, RecordCount (chunks settings.batchSize jobs).length (chunks settings.batchSize jobs).length
      ((passRun K circuits settings plainShares i keys jobs).run st).run.run := by
  unfold passRun batched
  refine recordCount_stateBind0 (recordCount_liftS _) fun prss => ?_
  have h := recordCount_mapM _ (recordCount_passBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter)
    (chunks settings.batchSize jobs)
  simp only [Nat.mul_one] at h
  intro st
  simpa only [Nat.add_zero] using recordCount_stateBind h (fun outputs => recordCount_statePure _) st

end PassCount

/-! ## A ghost phase of local tails -/

section Tail

variable {C : Committee} {E : Type} {Ia L R α β ρ : Type}
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty PEmpty L R) (blank : ρ)

/-- A local tail keeps an abort with its record, makes no round, and keeps the record of each
result. -/
def LocalTail (g : Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) : Prop :=
  (∀ w, g (none, w) = pure (none, w)) ∧ ∀ x, TimedR 0 (g x) ∧ ∀ y ∈ support (g x), y.2 = x.2

/-- A ghost phase of timed programs with exactly their rounds ends with each corrupt step at its
blank end and each honest step done. -/
theorem executePhaseR_timed_shape (a : ℕ) (st : A.State)
    (prog : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (hp : ∀ i ∉ D.1, TimedR a (prog i)) :
    ∀ z ∈ support (executePhaseR worldRoles D A F blank a st prog),
      (∀ i ∈ D.1, z.2 i = .done none blank) ∧ ∀ i ∉ D.1, (z.2 i).isDone := by
  intro z hz
  unfold executePhaseR at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨s0, hs0, hz⟩ := hz
  obtain ⟨hD, ht⟩ := startStepsR_timed D blank a prog hp s0 hs0
  exact executeRoundsR_timed D A F blank a st s0 hD ht z hz

/-- A ghost phase of the results and the records of done steps returns those steps. -/
theorem executePhaseR_pure_done (b : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (hD : ∀ i ∈ D.1, steps i = .done none blank) (hd : ∀ i ∉ D.1, (steps i).isDone) :
    executePhaseR worldRoles D A F blank b st (fun i => pure ((steps i).output, (steps i).record blank)) =
      pure (st, steps) := by
  unfold executePhaseR startStepsR
  have h : (fun i => if i ∈ D.1 then (pure (RStep.done none blank) : OracleComp (WorldSpec C) _) else
      worldRoles.honest (advanceR (pure ((steps i).output, (steps i).record blank) :
        OracleComp (PartySpec C E RealSpec) _))) = fun i => pure (steps i) := by
    funext i
    by_cases hi : i ∈ D.1
    · rw [ite_eq_left hi, hD i hi]
    · rw [ite_eq_right hi]
      have hdi := hd i hi
      cases hs : steps i with
      | done out record => exact free_pure _
      | wait outbox resume => rw [hs] at hdi; exact hdi.elim
      | call input resume => exact input.elim
  rw [h, sequenceFin_pure, pure_bind]
  exact executeRoundsR_allDone D A F blank b st steps hd

/-- A ghost phase of local tails keeps the state of the adversary and the record of
each operator. -/
theorem executePhaseR_localTail (b : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (g : C.Party → Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) (hg : ∀ i, LocalTail (g i))
    (hD : ∀ i ∈ D.1, steps i = .done none blank) :
    ∀ z ∈ support (executePhaseR worldRoles D A F blank b st fun i =>
        g i ((steps i).output, (steps i).record blank)),
      z.1 = st ∧ ∀ i, (z.2 i).record blank = (steps i).record blank := by
  intro z hz
  have hz' := hz
  unfold executePhaseR at hz'
  rw [mem_support_bind_iff] at hz'
  obtain ⟨s0, hs0, hz'⟩ := hz'
  obtain ⟨hD0, ht0⟩ := startStepsR_timed D blank 0 _ (fun i _ => ((hg i).2 _).1) s0 hs0
  have hdone : ∀ i, i ∉ D.1 → (s0 i).isDone := fun i hi => (ht0 i hi).isDone
  rw [executeRoundsR_allDone D A F blank b st s0 hdone, support_pure, Set.mem_singleton_iff] at hz'
  subst hz'
  refine ⟨rfl, fun i => ?_⟩
  by_cases hi : i ∈ D.1
  · change (s0 i).record blank = _
    rw [hD0 i hi, hD i hi]
    rfl
  · have hmem := Joint.executePhaseR_out_mem D A F blank b st _ _ hz i hi (hdone i hi)
    exact ((hg i).2 _).2 _ hmem

theorem timedR_bind_localTail {a : ℕ} {p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)}
    {g : Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)} (hp : TimedR a p) (hg : LocalTail g) :
    TimedR a (p >>= g) := by
  have h := hp.bind (A' := fun x : Option β × ρ => x.1 = none) (B' := fun x => x.1.isSome) (n := 0)
    (fun x hx => ⟨(none, x.2), by rcases x with ⟨_ | _, w⟩; exact (hg.1 w); exact absurd hx (by simp), rfl⟩)
    fun x _ => (hg.2 x).1
  simpa only [Nat.add_zero] using h

end Tail

section TailLift

variable {C : Committee} {E : Type} {α β : Type}

/-- A program with no record and no round after a recorded result is a local tail. -/
theorem localTail_recCont_lift (tail : α → PartyM C E RealSpec β) (h : ∀ a, Timed 0 (tail a).run) :
    LocalTail (recCont fun a => RecM.lift (tail a)) := by
  refine ⟨fun w => rfl, fun x => ?_⟩
  rcases x with ⟨_ | a, w⟩
  · refine ⟨TimedLog.stop 0 _ rfl, fun y hy => ?_⟩
    change y ∈ support (pure (none, w) : OracleComp (PartySpec C E RealSpec) _) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    rw [hy]
  · have heq : recCont (fun a => RecM.lift (tail a)) (some a, w) =
        (fun o => (o, w ++ [])) <$> (tail a).run := by
      change (fun y => (y.1, w ++ y.2)) <$> (RecM.lift (tail a)).run.run = _
      rw [run_recLift, Functor.map_map]
    rw [heq]
    refine ⟨?_, fun y hy => ?_⟩
    · refine timedR_of_timed _ ?_
      rw [Functor.map_map]
      simpa only [id_map'] using h a
    · rw [support_map] at hy
      obtain ⟨o, -, rfl⟩ := hy
      exact List.append_nil w

theorem recM_lift_failure : RecM.lift (failure : PartyM C E RealSpec α) = failure := by
  have h := run_recLift (C := C) (E := E) (failure : PartyM C E RealSpec α)
  rw [OptionT.run_failure, map_pure] at h
  exact OptionT.ext h

end TailLift

/-! ## A timed recorded phase with a local tail, in law -/

section Law

variable {C : Committee} {E : Type} {Ia L R α β ρ : Type} (prims : Primitives)
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty PEmpty L R) (blank : ρ)

/-- A run of `a + b` rounds of programs that take exactly `a` rounds and then a local tail gives an
event at most as likely as the run of `a` rounds of the programs gives an event that follows from it
with the same records and a smaller hash cache. -/
theorem prEvent_tail_le (a b : ℕ) (st : A.State)
    (p : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (hp : ∀ i ∉ D.1, TimedR a (p i))
    (g : C.Party → Option α × ρ → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) (hg : ∀ i, LocalTail (g i))
    (world : StreamState C)
    (Ez : (A.State × (C.Party → RStep C E RealSpec β ρ)) × StreamState C → Prop)
    (Ey : (A.State × (C.Party → RStep C E RealSpec α ρ)) × StreamState C → Prop)
    (hE : ∀ y z, y.1 ∈ support (executePhaseR worldRoles D A F blank a st p) →
      (∀ i, (z.1.2 i).record blank = (y.1.2 i).record blank) → y.2.1 ≤ z.2.1 → Ez z → Ey y) :
    Pr{let z ← (simulateQ (streamWorld prims D) (executePhaseR worldRoles D A F blank (a + b) st
        fun i => p i >>= g i)).run world}[Ez z] ≤
      Pr{let y ← (simulateQ (streamWorld prims D) (executePhaseR worldRoles D A F blank a st p)).run world}[Ey y] := by
  have hw := GhostSplit.executePhaseR_bind_world D A F blank g (WorldSplit.streamWorld_freeCommute prims D)
    (fun i w => (hg i).1 w) a b st p hp world
  rw [hw.prEvent_eq]
  simp only [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_prEvent_of_support _ _ Ey Ez fun y hy hnot => ?_
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hEz => hnot ?_
  have hy' := mem_support_phase prims D _ world y hy
  obtain ⟨hD, -⟩ := executePhaseR_timed_shape D A F blank a st p hp y.1 hy'
  have hz' := mem_support_phase prims D _ y.2 z hz
  obtain ⟨-, hrec⟩ := executePhaseR_localTail D A F blank b y.1.1 y.1.2 g hg hD z.1 hz'
  exact hE y z hy' hrec (streamWorld_run_mono prims D _ y.2 z hz) hEz

/-- More rounds than a timed phase takes give the same law. -/
theorem phase_fuel_eq (a b : ℕ) (st : A.State)
    (p : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (hp : ∀ i ∉ D.1, TimedR a (p i))
    (world : StreamState C) :
    (simulateQ (streamWorld prims D) (executePhaseR worldRoles D A F blank (a + b) st p)).run world =ᵈ
      (simulateQ (streamWorld prims D) (executePhaseR worldRoles D A F blank a st p)).run world := by
  have hw := GhostSplit.executePhaseR_bind_world D A F blank (fun _ => pure) (WorldSplit.streamWorld_freeCommute prims D)
    (fun _ _ => rfl) a b st p hp world
  simp only [bind_pure] at hw
  refine hw.trans ?_
  simp only [simulateQ_bind, StateT.run_bind]
  conv_rhs => rw [← bind_pure ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D A F blank a st p)).run world)]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun y hy => ?_
  obtain ⟨hD, hd⟩ := executePhaseR_timed_shape D A F blank a st p hp y.1 (mem_support_phase prims D _ world y hy)
  rw [executePhaseR_pure_done D A F blank b y.1.1 y.1.2 hD hd, simulateQ_pure, StateT.run_pure]

end Law

/-! ## A map of the records of the honest operators through a ghost phase -/

section MapRecord

variable {C : Committee} {E : Type} {α ρ : Type}

/-- A ghost step with the map `f` on its record. -/
def mapStep (f : ρ → ρ) : RStep C E RealSpec α ρ → RStep C E RealSpec α ρ
  | .done out record => .done out (f record)
  | .wait outbox resume => .wait outbox fun inbox => (fun q => (q.1, f q.2)) <$> resume inbox
  | .call input resume => .call input fun r => (fun q => (q.1, f q.2)) <$> resume r

theorem advanceR_mapStep (f : ρ → ρ) (p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)) :
    advanceR ((fun q => (q.1, f q.2)) <$> p) = mapStep f <$> advanceR p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rcases t with (t | outbox) | input
    · have h : ∀ (g : (LocalSpec C).Range t → OracleComp (PartySpec C E RealSpec) (Option α × ρ)),
          advanceR (liftM (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl t))) >>= g) =
            OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advanceR (g r) :=
        fun g => rfl
      rw [map_bind, h, h, map_bind]
      simp only [ih]
    · rw [map_bind]
      rfl
    · exact input.elim

/-- The map of the records of the honest operators on the steps. -/
def mapSteps (D : C.Coalition) (f : C.Party → ρ → ρ) (steps : C.Party → RStep C E RealSpec α ρ) :
    C.Party → RStep C E RealSpec α ρ := fun i => if i ∈ D.1 then steps i else mapStep (f i) (steps i)

variable {Ia L R : Type}
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty PEmpty L R) (blank : ρ)
  (f : C.Party → ρ → ρ)

theorem mapStep_outbox (g : ρ → ρ) (step : RStep C E RealSpec α ρ) : (mapStep g step).outbox = step.outbox := by
  cases step <;> rfl

theorem mapStep_delivered (g : ρ → ρ) (step : RStep C E RealSpec α ρ) :
    (mapStep g step).delivered = step.delivered := by
  cases step with
  | done out record => cases out <;> rfl
  | wait outbox resume => rfl
  | call input resume => rfl

theorem mapStep_isDone (g : ρ → ρ) (step : RStep C E RealSpec α ρ) : (mapStep g step).isDone ↔ step.isDone := by
  cases step <;> exact Iff.rfl

theorem stepRoundR_mapSteps (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ) :
    stepRoundR worldRoles D A F blank st (mapSteps D f steps) =
      (fun r => (r.1, mapSteps D f r.2.1, r.2.2)) <$> stepRoundR worldRoles D A F blank st steps := by
  unfold stepRoundR
  rw [ite_eq_right (GhostSplit.stepRoundR_noCall D _), ite_eq_right (GhostSplit.stepRoundR_noCall D _)]
  have hout : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (mapSteps D f steps i).outbox c else none) =
      fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none := by
    funext c i
    unfold mapSteps
    split_ifs <;> simp_all [mapStep_outbox]
  have hdel : ∀ k, (mapSteps D f steps k).delivered = (steps k).delivered := fun k => by
    unfold mapSteps
    split_ifs
    · rfl
    · exact mapStep_delivered _ _
  rw [hout, map_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨state, sent⟩
  simp only [map_bind, map_pure]
  have key : ∀ X : C.Party → OracleComp (WorldSpec C) (RStep C E RealSpec α ρ),
      (OverPermutation.sequenceFin X >>= fun rs => pure (state, mapSteps D f rs, sent)) =
        OverPermutation.sequenceFin (fun j => X j >>= fun r => pure (if j ∈ D.1 then r else mapStep (f j) r)) >>=
          fun rs => pure (state, rs, sent) := fun X => by
    rw [sequenceFin_bind_pure, bind_assoc]
    simp only [pure_bind]
    rfl
  rw [key]
  congr 2
  funext j
  by_cases hj : j ∈ D.1
  · simp only [mapSteps, hj, ↓reduceIte, bind_pure]
  · rw [show mapSteps D f steps j = mapStep (f j) (steps j) from ite_eq_right hj]
    simp only [hdel, hj, ↓reduceIte]
    cases steps j with
    | done out record => simp [mapStep]
    | wait outbox resume =>
      simp only [mapStep]
      rw [advanceR_mapStep, worldRoles_honest_map, map_eq_bind_pure_comp]
      rfl
    | call input resume => exact input.elim

theorem executeRoundsR_mapSteps :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ),
    executeRoundsR worldRoles D A F blank fuel st (mapSteps D f steps) =
      (fun r => (r.1, mapSteps D f r.2)) <$> executeRoundsR worldRoles D A F blank fuel st steps
  | 0, st, steps => by simp [executeRoundsR]
  | fuel + 1, st, steps => by
    have hdone : (∀ i, i ∉ D.1 → (mapSteps D f steps i).isDone) ↔ ∀ i, i ∉ D.1 → (steps i).isDone := by
      refine forall_congr' fun i => imp_congr_right fun hi => ?_
      simp only [mapSteps, hi, ↓reduceIte]
      exact mapStep_isDone _ _
    simp only [executeRoundsR, hdone]
    split_ifs
    · simp
    · rw [stepRoundR_mapSteps, map_bind, bind_map_left]
      exact bind_congr fun r => executeRoundsR_mapSteps fuel r.1 r.2.1

/-- A map of the records of the honest programs maps the records of the honest steps of a ghost
phase. -/
theorem executePhaseR_mapSteps (fuel : ℕ) (st : A.State)
    (prog prog' : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (hprog : ∀ i, i ∉ D.1 → prog' i = (fun q => (q.1, f i q.2)) <$> prog i) :
    executePhaseR worldRoles D A F blank fuel st prog' =
      (fun r => (r.1, mapSteps D f r.2)) <$> executePhaseR worldRoles D A F blank fuel st prog := by
  unfold executePhaseR startStepsR
  have h : (fun i => if i ∈ D.1 then (pure (RStep.done none blank) : OracleComp (WorldSpec C) _) else
      worldRoles.honest (advanceR (prog' i))) = fun i =>
        (if i ∈ D.1 then pure (RStep.done none blank) else worldRoles.honest (advanceR (prog i))) >>=
          fun r => pure (if i ∈ D.1 then r else mapStep (f i) r) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp only [hi, ↓reduceIte, pure_bind]
    · simp only [hi, ↓reduceIte]
      rw [hprog i hi, advanceR_mapStep, worldRoles_honest_map, map_eq_bind_pure_comp]
      rfl
  rw [h, sequenceFin_bind_pure, bind_assoc, map_bind]
  simp only [pure_bind]
  refine bind_congr fun steps => ?_
  exact executeRoundsR_mapSteps D A F blank f fuel st steps

/-- The record of a mapped step is the mapped record of a done step, or the blank. -/
theorem mapStep_record (f : ρ → ρ) (blank : ρ) (step : RStep C E RealSpec α ρ) :
    (mapStep f step).record blank = blank ∨ (mapStep f step).record blank = f (step.record blank) := by
  cases step with
  | done out record => exact Or.inr rfl
  | wait outbox resume => exact Or.inl rfl
  | call input resume => exact Or.inl rfl

end MapRecord

/-! ## A ghost phase after a dead honest operator -/

section Dead

variable {C : Committee} {E : Type} {α β ρ : Type}

/-- A recorded program that aborts at once with the record `w`, or that waits for a round and then
aborts with the record `w` on each inbox with an abort frame. -/
def AbortsOnAbort (w : ρ) (p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)) : Prop :=
  ∀ step ∈ support (advanceR p), step = .done none w ∨
    ∃ outbox resume, step = .wait outbox resume ∧
      ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advanceR (resume inbox) = pure (.done none w)

/-- Advancing a program with no record and then a recorded continuation. -/
def contStep (G : Option α → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) :
    Step C E RealSpec α → OracleComp (LocalSpec C) (RStep C E RealSpec β ρ)
  | .done out => advanceR (G out)
  | .wait outbox resume => pure (.wait outbox fun inbox => resume inbox >>= G)
  | .call input resume => pure (.call input fun r => resume r >>= G)

theorem advanceR_bind_plain (oa : OracleComp (PartySpec C E RealSpec) (Option α))
    (G : Option α → OracleComp (PartySpec C E RealSpec) (Option β × ρ)) :
    advanceR (oa >>= G) = advance oa >>= contStep G := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    rw [pure_bind]
    change advanceR (G x) = pure (Step.done x) >>= contStep G
    rw [pure_bind]
    rfl
  | query_bind q f ih =>
    rcases q with (q | mail) | input
    · rw [bind_assoc]
      change (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (f r >>= G)) =
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (f r)) >>= contStep G
      rw [bind_assoc]
      exact bind_congr ih
    · rw [bind_assoc]
      change pure (RStep.wait mail fun inbox => f inbox >>= G) = pure (Step.wait mail f) >>= contStep G
      rw [pure_bind]
      rfl
    · exact input.elim

/-- A program that starts with a round and then a recorded continuation that keeps an abort with
the record `[]` aborts on an abort frame. -/
theorem abortsOnAbort_lift_bind {γ : Type} (q : PartyM C E RealSpec γ) (hq : StartsWithRound q)
    (K : γ → RecM C E β) : AbortsOnAbort ([] : Record C E) (RecM.lift q >>= K).run.run := by
  intro step hstep
  rw [run_recLift_bind, advanceR_bind_plain, mem_support_bind_iff] at hstep
  obtain ⟨s, hs, hstep⟩ := hstep
  rcases hq s hs with rfl | ⟨outbox, resume, rfl, habort⟩
  · left
    change step ∈ support (advanceR (pure (none, []))) at hstep
    change step ∈ support (pure (RStep.done none []) : OracleComp (LocalSpec C) _) at hstep
    rw [support_pure, Set.mem_singleton_iff] at hstep
    exact hstep
  · right
    change step ∈ support (pure _ : OracleComp (LocalSpec C) _) at hstep
    rw [support_pure, Set.mem_singleton_iff] at hstep
    refine ⟨outbox, _, hstep, fun inbox hinbox => ?_⟩
    rw [advanceR_bind_plain, habort inbox hinbox, pure_bind]
    rfl

/-- A prefix of the record keeps the abort on an abort frame. -/
theorem abortsOnAbort_prefix (pre : Record C E) (p : OracleComp (PartySpec C E RealSpec) (Option α × Record C E))
    (h : AbortsOnAbort [] p) : AbortsOnAbort pre ((fun q => (q.1, pre ++ q.2)) <$> p) := by
  intro step hstep
  rw [advanceR_mapStep, support_map] at hstep
  obtain ⟨s, hs, rfl⟩ := hstep
  rcases h s hs with rfl | ⟨outbox, resume, rfl, habort⟩
  · left
    simp [mapStep]
  · right
    refine ⟨outbox, _, rfl, fun inbox hinbox => ?_⟩
    rw [advanceR_mapStep, habort inbox hinbox, map_pure]
    simp [mapStep]

theorem abortsOnAbort_pure (w : ρ) : AbortsOnAbort w (pure (none, w) : OracleComp (PartySpec C E RealSpec) (Option α × ρ)) := by
  intro step hstep
  change step ∈ support (pure (RStep.done none w) : OracleComp (LocalSpec C) _) at hstep
  rw [support_pure, Set.mem_singleton_iff] at hstep
  exact Or.inl hstep

variable {Ia L R : Type}
  (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty PEmpty L R) (blank : ρ)

/-- A ghost phase with a dead honest operator. When an honest program ends at once with no output and
each honest program aborts on an abort frame with its record `w i`, each honest step ends with the
record `blank` or `w i`. -/
theorem executePhaseR_dead (fuel : ℕ) (st : A.State) (prog : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (w : C.Party → ρ) (j₀ : C.Party) (hj₀ : j₀ ∉ D.1) (hdead : prog j₀ = pure (none, w j₀))
    (habort : ∀ i, i ∉ D.1 → AbortsOnAbort (w i) (prog i)) :
    ∀ z ∈ support (executePhaseR worldRoles D A F blank fuel st prog), ∀ i, i ∉ D.1 →
      (z.2 i).record blank = blank ∨ (z.2 i).record blank = w i := by
  intro z hz
  unfold executePhaseR at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨s0, hs0, hz⟩ := hz
  have hstep : ∀ i, i ∉ D.1 → s0 i ∈ support (advanceR (prog i)) := fun i hi => by
    have h := Fuel.mem_support_sequenceFin _ s0 hs0 i
    simp only [hi, ↓reduceIte] at h
    exact Fuel.mem_support_honest _ _ h
  have hj₀' : s0 j₀ = .done none (w j₀) := by
    have h := hstep j₀ hj₀
    rw [hdead] at h
    change s0 j₀ ∈ support (pure (RStep.done none (w j₀)) : OracleComp (LocalSpec C) _) at h
    rwa [support_pure, Set.mem_singleton_iff] at h
  have hrec0 : ∀ i, i ∉ D.1 → (s0 i).record blank = blank ∨ (s0 i).record blank = w i := fun i hi => by
    rcases habort i hi (s0 i) (hstep i hi) with h | ⟨outbox, resume, h, -⟩ <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl
  cases fuel with
  | zero =>
    simp only [executeRoundsR, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hrec0
  | succ fuel =>
    simp only [executeRoundsR] at hz
    split_ifs at hz with hd
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hrec0
    · rw [mem_support_bind_iff] at hz
      obtain ⟨q, hq, hz⟩ := hz
      have hq' : ∀ i, i ∉ D.1 → q.2.1 i = .done none (w i) := by
        intro i hi
        unfold stepRoundR at hq
        rw [ite_eq_right (GhostSplit.stepRoundR_noCall D _), mem_support_bind_iff] at hq
        obtain ⟨⟨st', sent⟩, -, hq⟩ := hq
        rw [mem_support_bind_iff] at hq
        obtain ⟨steps', hsteps', hq⟩ := hq
        rw [support_pure, Set.mem_singleton_iff] at hq
        subst hq
        have h := Fuel.mem_support_sequenceFin _ steps' hsteps' i
        rcases habort i hi (s0 i) (hstep i hi) with h0 | ⟨outbox, resume, h0, hres⟩
        · rw [h0] at h
          change steps' i ∈ support (pure (RStep.done none (w i)) : OracleComp (WorldSpec C) _) at h
          rwa [support_pure, Set.mem_singleton_iff] at h
        · rw [h0] at h
          simp only [hi, ↓reduceIte] at h
          rw [hres _ ⟨j₀, by simp [hj₀, hj₀', RStep.delivered]⟩] at h
          change steps' i ∈ support (free (pure (RStep.done none (w i)))) at h
          rwa [free_pure, support_pure, Set.mem_singleton_iff] at h
      have hdone : ∀ i, i ∉ D.1 → (q.2.1 i).isDone := fun i hi => by rw [hq' i hi]; trivial
      rw [executeRoundsR_allDone D A F blank fuel q.1 q.2.1 hdone, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro i hi
      right
      change (q.2.1 i).record blank = w i
      rw [hq' i hi]
      rfl

end Dead

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.recordCount_passRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.recordCount_passRun

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.prEvent_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.prEvent_tail_le

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.executePhaseR_mapSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.executePhaseR_mapSteps
