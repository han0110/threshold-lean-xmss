import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Rounds
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.GhostSplit
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Law
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Abort
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Coupling

/-!
# The joint law of the ghost run and the cut at a check

The ghost run of one ceremony is, in law, three ghost phases. The first runs the recorded prefix up
to the start of the check of batch `k` (`pre1`), the second runs the check (`chk2`), and the third
runs the rest (`cont2`). `ghost_eq_phases` states this law by two splits of the ghost executor
(`GhostSplit.executePhaseR_bind_world`).

The first two phases, read as the cut at check `k` (`cutOutcome`), have the law of `ceremonyCheckAt`
(`cutOutcome_eq`). With its records dropped, the first phase has the law of the prefix of the cut on
the starts of the checks (`view1_eq_prefix`), and the second phase has the law of the check of the
pilot from the joint start (`phase2_eq_check`). On the support of the three phases, the cut outcome
is linked to the end of the ghost run (`cutLink_phases`). So `couplingLaw` proves `CouplingLaw`, and
`ceremonyCoupling` proves the leaf `CeremonyCoupling`.

Each program of a phase has a twin with the suffix `At` and the place `early` of the opening record
(`recCheckOpenWith`). At `early = false` the twin is the program itself, and each lemma above is the
instance at `false` of its general form. `couplingLawWith` states the joint law at both places, with
the link `CutLinkFree`. That link needs no honest output, because the bound of the coalition gives an
honest operator (`exists_honest`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace Joint

open RecordedOpening GhostSplit LiveRounds

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The programs of the three phases -/

section Programs

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The result of the recorded prefix. -/
abbrev PreOut (C : Committee) := (PrssKeys C × List (Option (List (List Bit))) × (BatchStart C × ℕ)) × (ℕ × ℕ)

/-- The result of the check part. -/
abbrev ChkOut (C : Committee) := (Unit × RunState C) × (ℕ × ℕ)

/-- `pre1` with the record of the opening at its place for `early`. -/
def pre1At (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    OracleComp (PartySpec C E RealSpec) (Option (PreOut C) × Record C E) :=
  match c.keys i with
  | some keys => ((recPrefixAt K circuits settings early k i keys c.jobs).run c.counters).run.run
  | none => pure (none, [])

/-- The program of the first phase, the recorded prefix up to the start of the check of batch `k`. -/
def pre1 (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    OracleComp (PartySpec C E RealSpec) (Option (PreOut C) × Record C E) :=
  match c.keys i with
  | some keys => ((recPrefix K circuits settings k i keys c.jobs).run c.counters).run.run
  | none => pure (none, [])

/-- `cont1` with the record of the opening at its place for `early`. -/
def cont1At (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Option (PreOut C) × Record C E → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  match c.keys i with
  | some keys => recCont (recFinishAt K circuits settings early k i keys c.jobs)
  | none => fun x => pure (none, x.2)

/-- The rest after the first phase. -/
def cont1 (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Option (PreOut C) × Record C E → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  match c.keys i with
  | some keys => recCont (recFinish K circuits settings k i keys c.jobs)
  | none => fun x => pure (none, x.2)

/-- The program of the second phase, the record of the start of the check and the check. -/
def chk2 (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (x : Option (PreOut C) × Record C E) :
    OracleComp (PartySpec C E RealSpec) (Option (ChkOut C) × Record C E) :=
  match c.keys i, x.1 with
  | some _, some p => (fun y => (y.1, x.2 ++ y.2)) <$> (recCheck K p.1.2.2.1 p.2).run.run
  | _, _ => pure (none, x.2)

/-- `cont2` with the record of the opening at its place for `early`. -/
def cont2At (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (x : Option (PreOut C) × Record C E) :
    Option (ChkOut C) × Record C E → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  match c.keys i, x.1 with
  | some keys, some p => recCont (finRestAt K circuits settings early k i keys c.jobs p)
  | _, _ => fun y => pure (none, y.2)

/-- The program of the third phase, the rest after the check. -/
def cont2 (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (x : Option (PreOut C) × Record C E) :
    Option (ChkOut C) × Record C E → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  match c.keys i, x.1 with
  | some keys, some p => recCont (finRest K circuits settings k i keys c.jobs p)
  | _, _ => fun y => pure (none, y.2)

omit [Fintype E] [DecidableEq E] in
theorem recCeremonyAt_split (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (hk : k < (chunks settings.batchSize c.jobs).length) :
    (recCeremonyAt K circuits settings early i c).run.run =
      pre1At K circuits settings early k i c >>= cont1At K circuits settings early k i c := by
  cases hkeys : c.keys i with
  | none =>
    simp only [recCeremonyAt, pre1At, cont1At, hkeys, pure_bind]
    exact run_recFailure
  | some keys =>
    simp only [pre1At, cont1At, hkeys]
    exact recCeremonyAt_eq K circuits settings early k i c keys hkeys hk

omit [Fintype E] [DecidableEq E] in
theorem recCeremony_split (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (hk : k < (chunks settings.batchSize c.jobs).length) :
    (recCeremony K circuits settings i c).run.run = pre1 K circuits settings k i c >>= cont1 K circuits settings k i c :=
  recCeremonyAt_split K circuits settings false k i c hk

omit [Fintype E] [DecidableEq E] in
theorem cont1At_split (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (x : Option (PreOut C) × Record C E) :
    cont1At K circuits settings early k i c x = chk2 K i c x >>= cont2At K circuits settings early k i c x := by
  rcases x with ⟨_ | p, w⟩ <;> cases hkeys : c.keys i <;>
    simp only [cont1At, chk2, cont2At, hkeys, recCont, pure_bind]
  rw [recFinishAt_eq, run_recBind, map_prepend_recCont]

omit [Fintype E] [DecidableEq E] in
theorem cont1_split (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (x : Option (PreOut C) × Record C E) :
    cont1 K circuits settings k i c x = chk2 K i c x >>= cont2 K circuits settings k i c x :=
  cont1At_split K circuits settings false k i c x

omit [Fintype E] [DecidableEq E] in
theorem cont1At_none (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (w : Record C E) :
    cont1At K circuits settings early k i c (none, w) = pure (none, w) := by
  cases hkeys : c.keys i <;> simp only [cont1At, hkeys, recCont]

omit [Fintype E] [DecidableEq E] in
theorem cont1_none (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (w : Record C E) :
    cont1 K circuits settings k i c (none, w) = pure (none, w) :=
  cont1At_none K circuits settings false k i c w

omit [Fintype E] [DecidableEq E] in
theorem cont2At_none (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (x : Option (PreOut C) × Record C E) (w : Record C E) :
    cont2At K circuits settings early k i c x (none, w) = pure (none, w) := by
  rcases x with ⟨_ | p, w'⟩ <;> cases hkeys : c.keys i <;> simp only [cont2At, hkeys, recCont]

omit [Fintype E] [DecidableEq E] in
theorem cont2_none (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (x : Option (PreOut C) × Record C E)
    (w : Record C E) : cont2 K circuits settings k i c x (none, w) = pure (none, w) :=
  cont2At_none K circuits settings false k i c x w

end Programs

/-! ## Timing and support of the phases -/

section Facts

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem _root_.ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening.TimedLog.mono' {γ : Type} {A B A' B' : γ → Prop} {n : ℕ} {p : OracleComp (PartySpec C E RealSpec) γ}
    (h : TimedLog A B n p) (hA : ∀ x, A x → A' x) (hB : ∀ x, B x → B' x) : TimedLog A' B' n p := by
  induction h with
  | stop n x hx => exact TimedLog.stop n x (hA x hx)
  | done x hx => exact TimedLog.done x (hB x hx)
  | queryLocal n q k _ ih => exact TimedLog.queryLocal n q k ih
  | round n out k _ ih => exact TimedLog.round n out k ih

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The outputs and records of the honest steps that are done at the end of a ghost phase are outputs
of their programs. -/
theorem executePhaseR_out_mem {Ia L R O α ρ : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty O L R) (blank : ρ) (fuel : ℕ) (st : A.State)
    (prog : C.Party → OracleComp (PartySpec C E (CallSpec PEmpty O)) (Option α × ρ))
    (z : A.State × (C.Party → RStep C E (CallSpec PEmpty O) α ρ))
    (hz : z ∈ support (executePhaseR worldRoles D A F blank fuel st prog)) (i : C.Party) (hi : i ∉ D.1)
    (hd : (z.2 i).isDone) : ((z.2 i).output, (z.2 i).record blank) ∈ support (prog i) := by
  unfold executePhaseR at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨steps, hsteps, hz⟩ := hz
  have hj := Fuel.mem_support_sequenceFin _ steps hsteps i
  simp only [hi, ↓reduceIte] at hj
  refine stepOutputs_advanceR _ _ (Fuel.mem_support_honest _ _ hj)
    (executeRoundsR_stepOutputs D A F blank fuel st steps z hz i hi ?_)
  cases hs : z.2 i with
  | done out record => exact rfl
  | wait outbox resume => rw [hs] at hd; exact hd.elim
  | call input resume => exact input.elim

omit [Fintype E] [DecidableEq E] in
/-- The first phase takes the rounds of the prefix under the parameter of the game, at both places of
the opening record. -/
theorem timedR_pre1At (early : Bool) (k : ℕ) (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length) (i : C.Party)
    (hi : i ∉ D.1) :
    TimedR (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k)
      (pre1At K circuits settings early k i c) := by
  cases hkeys : c.keys i with
  | none =>
    simp only [pre1At, hkeys]
    exact TimedLog.stop _ _ rfl
  | some keys =>
    simp only [pre1At, hkeys]
    rw [← parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys]
    exact (timedLog_recPrefixAt K circuits settings early k i keys c.jobs hk c.counters).mono' (fun x hx => hx.1)
      fun x hx => by rw [hx.1]

omit [Fintype E] [DecidableEq E] in
/-- The first phase takes the rounds of the prefix under the parameter of the game. -/
theorem timedR_pre1 (k : ℕ) (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length) (i : C.Party)
    (hi : i ∉ D.1) :
    TimedR (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) (pre1 K circuits settings k i c) :=
  timedR_pre1At K circuits settings false k D c hseeds hk i hi

/-- The second phase takes the check rounds of the head of batch `k`, from each result of the first
phase, at both places of the opening record. -/
theorem timedR_chk2At (early : Bool) (k : ℕ) (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length) (i : C.Party)
    (hi : i ∉ D.1) (x : Option (PreOut C) × Record C E) (hx : x ∈ support (pre1At K circuits settings early k i c)) :
    TimedR (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
      (circuits (gameParameter D c.keys) ·.kind))).sum) (chk2 K i c x) := by
  rcases x with ⟨_ | p, w⟩
  · cases hkeys : c.keys i <;> simp only [chk2, hkeys] <;> exact TimedLog.stop _ _ rfl
  cases hkeys : c.keys i with
  | none => simp only [chk2, hkeys]; exact TimedLog.stop _ _ rfl
  | some keys =>
    simp only [chk2, hkeys]
    simp only [pre1At, hkeys] at hx
    obtain ⟨prss, hpoint⟩ := recPrefixAt_pointAt K circuits settings early k i c keys hkeys hk _ hx p rfl
    have hcount : tupleCount p.1.2.2.1.circuits = (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum := by
      rw [← sum_batchTuples K p.1.2.2.1, ← parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys, ← hpoint.2.1]
      rfl
    rw [← hcount]
    exact (timedLog_recCheck K p.1.2.2.1 p.2).map _ (fun y hy => hy.1) fun y hy => hy.1

/-- The second phase takes the check rounds of the head of batch `k`, from each result of the first
phase. -/
theorem timedR_chk2 (k : ℕ) (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length) (i : C.Party)
    (hi : i ∉ D.1) (x : Option (PreOut C) × Record C E) (hx : x ∈ support (pre1 K circuits settings k i c)) :
    TimedR (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
      (circuits (gameParameter D c.keys) ·.kind))).sum) (chk2 K i c x) :=
  timedR_chk2At K circuits settings false k D c hseeds hk i hi x hx

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A ghost phase of timed programs with exactly their rounds ends with each honest step done. -/
theorem executePhaseR_timed_done {Ia L R α ρ : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty PEmpty L R) (blank : ρ) (a : ℕ) (st : A.State)
    (prog : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (hp : ∀ i ∉ D.1, TimedR a (prog i))
    (z : A.State × (C.Party → RStep C E RealSpec α ρ))
    (hz : z ∈ support (executePhaseR worldRoles D A F blank a st prog)) : ∀ i ∉ D.1, (z.2 i).isDone := by
  unfold executePhaseR at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨steps, hsteps, hz⟩ := hz
  obtain ⟨hD, ht⟩ := startStepsR_timed D blank a prog hp steps hsteps
  exact (executeRoundsR_timed D A F blank a st steps hD ht z hz).2

end Facts

/-! ## The ghost run as three phases -/

section Law

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The result and the record of a ghost step. -/
def outOf {α : Type} (steps : C.Party → RStep C E RealSpec α (Record C E)) (i : C.Party) : Option α × Record C E :=
  ((steps i).output, (steps i).record [])

/-- `phase1` with the record of the opening at its place for `early`. -/
def phase1At (early : Bool) (k a : ℕ) (c : CeremonyStart C net.State) (world : StreamState C) :
    ProbComp ((net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C) :=
  (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) a c.adversary
    fun i => pre1At K circuits settings early k i c)).run world

/-- The first phase, the recorded prefix. -/
def phase1 (k a : ℕ) (c : CeremonyStart C net.State) (world : StreamState C) :
    ProbComp ((net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C) :=
  (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) a c.adversary
    fun i => pre1 K circuits settings k i c)).run world

/-- The second phase, the check. -/
def phase2 (cc : ℕ) (c : CeremonyStart C net.State)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C) :
    ProbComp ((net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C) :=
  (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) cc y1.1.1
    fun i => chk2 K i c (outOf y1.1.2 i))).run y1.2

/-- `phase3` with the record of the opening at its place for `early`. -/
def phase3At (early : Bool) (k r3 : ℕ) (c : CeremonyStart C net.State)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (y2 : (net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C) :
    ProbComp ((net.State × CeremonySteps C E) × StreamState C) :=
  (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) r3 y2.1.1
    fun i => cont2At K circuits settings early k i c (outOf y1.1.2 i) (outOf y2.1.2 i))).run y2.2

/-- The third phase, the rest. -/
def phase3 (k r3 : ℕ) (c : CeremonyStart C net.State)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (y2 : (net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C) :
    ProbComp ((net.State × CeremonySteps C E) × StreamState C) :=
  (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) r3 y2.1.1
    fun i => cont2 K circuits settings k i c (outOf y1.1.2 i) (outOf y2.1.2 i))).run y2.2

/-- `ghostCeremony` with the record of the opening at its place for `early`. -/
def ghostCeremonyAt (early : Bool) (rounds : ℕ) (c : CeremonyStart C net.State) :
    StateT (StreamState C) ProbComp (net.State × CeremonySteps C E) :=
  simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds
    c.adversary fun i => (recCeremonyAt K circuits settings early i c).run.run)

/-- The ghost run of one ceremony has the law of its three phases, at both places of the opening
record. -/
theorem ghost_eq_phasesAt (early : Bool) (k rounds r3 : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (hrounds : rounds = prefixRounds circuits settings (gameParameter D c.keys) c.jobs k +
      (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum + r3)) :
    (ghostCeremonyAt prims K circuits settings D net early rounds c).run world =ᵈ
      (phase1At prims K circuits settings D net early k
          (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world >>= fun y1 =>
        phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
          (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 >>= fun y2 =>
          phase3At prims K circuits settings D net early k r3 c y1 y2) := by
  unfold ghostCeremonyAt
  have hprog : (fun i => (recCeremonyAt K circuits settings early i c).run.run) =
      fun i => pre1At K circuits settings early k i c >>= cont1At K circuits settings early k i c :=
    funext fun i => recCeremonyAt_split K circuits settings early k i c hk
  rw [hprog, hrounds]
  refine (GhostSplit.executePhaseR_bind_world D net noFunctionality ([] : Record C E)
    (fun i => cont1At K circuits settings early k i c) (WorldSplit.streamWorld_freeCommute prims D)
    (fun i w => cont1At_none K circuits settings early k i c w) _ _ c.adversary _
    (fun i hi => timedR_pre1At K circuits settings early k D c hseeds hk i hi) world).trans ?_
  rw [simulateQ_bind, StateT.run_bind]
  refine EvalDistEq.bind_congr_of_support _ fun y1 hy1 => ?_
  have hy1' := mem_support_phase prims D _ world y1 hy1
  have hdone := executePhaseR_timed_done D net noFunctionality ([] : Record C E) _ c.adversary _
    (fun i hi => timedR_pre1At K circuits settings early k D c hseeds hk i hi) y1.1 hy1'
  have hprog2 : (fun i => cont1At K circuits settings early k i c (outOf y1.1.2 i)) =
      fun i => chk2 K i c (outOf y1.1.2 i) >>= cont2At K circuits settings early k i c (outOf y1.1.2 i) :=
    funext fun i => cont1At_split K circuits settings early k i c _
  change (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) _ y1.1.1
    fun i => cont1At K circuits settings early k i c (outOf y1.1.2 i))).run y1.2 =ᵈ _
  rw [hprog2]
  refine (GhostSplit.executePhaseR_bind_world D net noFunctionality ([] : Record C E)
    (fun i => cont2At K circuits settings early k i c (outOf y1.1.2 i)) (WorldSplit.streamWorld_freeCommute prims D)
    (fun i w => cont2At_none K circuits settings early k i c _ w) _ r3 y1.1.1 _
    (fun i hi => timedR_chk2At K circuits settings early k D c hseeds hk i hi _
      (executePhaseR_out_mem D net noFunctionality ([] : Record C E) _ c.adversary _ y1.1 hy1' i hi
        (hdone i hi))) y1.2).trans ?_
  rw [simulateQ_bind, StateT.run_bind]
  exact EvalDistEq.rfl

/-- The ghost run of one ceremony has the law of its three phases. -/
theorem ghost_eq_phases (k rounds r3 : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (hrounds : rounds = prefixRounds circuits settings (gameParameter D c.keys) c.jobs k +
      (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum + r3)) :
    (ghostCeremony prims K circuits settings D net rounds c).run world =ᵈ
      (phase1 prims K circuits settings D net k (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k)
          c world >>= fun y1 =>
        phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
          (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 >>= fun y2 =>
          phase3 prims K circuits settings D net k r3 c y1 y2) :=
  ghost_eq_phasesAt prims K circuits settings D net false k rounds r3 c world hseeds hk hrounds

end Law

/-! ## The first phase and the prefix of the cut -/

section Prefix

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A ghost phase with the records dropped is the phase of the programs with the records dropped. -/
theorem ghostPhase_erase {α : Type} (fuel : ℕ) (st : net.State)
    (prog : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)) (world : StreamState C) :
    (fun w => ((w.1.1, fun i => (w.1.2 i).output), w.2)) <$> (simulateQ (streamWorld prims D)
      (executePhaseR worldRoles D net noFunctionality ([] : Record C E) fuel st prog)).run world =
      (simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality fuel st
        fun i => dropRecord (prog i))).run world := by
  rw [executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
    ([] : Record C E), simulateQ_map, StateT.run_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase reads only the honest programs. -/
theorem executePhase_congr {α : Type} (fuel : ℕ) (st : net.State) (p q : C.Party → PartyM C E RealSpec α)
    (h : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D net noFunctionality fuel st p = executePhase worldRoles D net noFunctionality fuel st q := by
  unfold executePhase startSteps
  congr 2
  funext i
  split_ifs with hi
  · rfl
  · rw [h i hi]

/-- The stop of an outcome of a cut program. -/
def stopF {α : Type} (r : CutOf C E α) : Option (CheckPoint C) := r.elim (fun _ => none) fun pr => some pr.1

/-- With its record dropped and its result mapped to its start of the check, the first phase program
is the cut program mapped to its stop. -/
theorem stopF_cutCeremony (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (hk : k < (chunks settings.batchSize c.jobs).length) :
    stopF <$> cutCeremony K circuits settings k i c =
      (fun x : PreOut C => some (pointOf K x.1.2.2.1)) <$> dropRecord (pre1 K circuits settings k i c) := by
  cases hkeys : c.keys i with
  | none =>
    simp only [cutCeremony, pre1, hkeys]
    rfl
  | some keys =>
    refine OptionT.ext ?_
    rw [OptionT.run_map, OptionT.run_map]
    have h := cutStop_cutCeremony K circuits settings k i c keys hkeys hk
    simp only [pre1, hkeys]
    exact h

/-- The view of the first phase, its state of the adversary, the start of the check at each operator
and its world. -/
def view1 (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C) :
    net.State × (C.Party → Option (Option (CheckPoint C))) × StreamState C :=
  (y1.1.1, fun i => (y1.1.2 i).output.map fun p => some (pointOf K p.1.2.2.1), y1.2)

/-- The same view of an outcome of the prefix of the cut. -/
def viewCut (z : (net.State × (C.Party → Option (CutOf C E RunResult))) × StreamState C) :
    net.State × (C.Party → Option (Option (CheckPoint C))) × StreamState C :=
  (z.1.1, fun i => cutStop (z.1.2 i), z.2)

/-- The first phase has the law of the prefix of the cut, on the view of each. -/
theorem view1_eq_prefix (k rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (hfuel : prefixRounds circuits settings (gameParameter D c.keys) c.jobs k ≤ rounds) :
    view1 K net <$> phase1 prims K circuits settings D net k
        (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world =ᵈ
      viewCut net <$> (ceremonyPrefix prims K circuits settings D net rounds k c).run world := by
  have hl : view1 K net <$> phase1 prims K circuits settings D net k
        (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world =
      (fun z => (z.1.1, z.1.2, z.2)) <$> (simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
        (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c.adversary
        fun i => (fun x : PreOut C => some (pointOf K x.1.2.2.1)) <$> dropRecord (pre1 K circuits settings k i c))).run
          world := by
    rw [WorldSplit.executePhase_map, simulateQ_map, StateT.run_map, Functor.map_map]
    unfold phase1
    rw [← ghostPhase_erase, Functor.map_map]
    rfl
  have hr : viewCut net <$> (ceremonyPrefix prims K circuits settings D net rounds k c).run world =
      (fun z => (z.1.1, z.1.2, z.2)) <$> (simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
        rounds c.adversary fun i => stopF <$> cutCeremony K circuits settings k i c)).run world := by
    rw [WorldSplit.executePhase_map, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  rw [hl, hr]
  refine EvalDistEq.map ?_ _
  obtain ⟨m, rfl⟩ : ∃ m, rounds = prefixRounds circuits settings (gameParameter D c.keys) c.jobs k + m :=
    ⟨rounds - prefixRounds circuits settings (gameParameter D c.keys) c.jobs k, by omega⟩
  have hext := WorldSplit.executePhase_extra (impl := streamWorld prims D) D net noFunctionality
    (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) m c.adversary
    (fun i => stopF <$> cutCeremony K circuits settings k i c)
    (fun i hi => Timed.map _ (timed_cutCeremony K circuits settings k i c _ fun keys hkeys =>
      parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys)) world
  refine EvalDistEq.trans ?_ hext.symm
  have hc := executePhase_congr D net (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c.adversary
    (fun i => stopF <$> cutCeremony K circuits settings k i c)
    (fun i => (fun x : PreOut C => some (pointOf K x.1.2.2.1)) <$> dropRecord (pre1 K circuits settings k i c))
    fun i _ => stopF_cutCeremony K circuits settings k i c hk
  rw [hc]

/-- With its record dropped, the program of the first phase is the same at both places of the
opening record. -/
theorem dropRecord_pre1At (early : Bool) (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    dropRecord (pre1At K circuits settings early k i c) = dropRecord (pre1 K circuits settings k i c) := by
  cases hkeys : c.keys i with
  | none => simp only [pre1At, pre1, hkeys]
  | some keys =>
    simp only [pre1At, pre1, hkeys]
    exact congrArg (fun x : StateT (ℕ × ℕ) (PartyM C E RealSpec) _ => OptionT.mk (x.run c.counters).run)
      (dropRecS_recPrefixAt K circuits settings early k i keys c.jobs)

/-- The view of the first phase is the same at both places of the opening record. -/
theorem view1_phase1At (early : Bool) (k a : ℕ) (c : CeremonyStart C net.State) (world : StreamState C) :
    view1 K net <$> phase1At prims K circuits settings D net early k a c world =
      view1 K net <$> phase1 prims K circuits settings D net k a c world := by
  have h1 := ghostPhase_erase prims D net a c.adversary (fun i => pre1At K circuits settings early k i c) world
  have h2 := ghostPhase_erase prims D net a c.adversary (fun i => pre1 K circuits settings k i c) world
  simp only [dropRecord_pre1At] at h1
  rw [← h2] at h1
  have h := congrArg (Functor.map fun w : (net.State × (C.Party → Option (PreOut C))) × StreamState C =>
    (w.1.1, fun i => (w.1.2 i).map fun p => some (pointOf K p.1.2.2.1), w.2)) h1
  rw [Functor.map_map, Functor.map_map] at h
  exact h

/-- The first phase has the law of the prefix of the cut, on the view of each, at both places of the
opening record. -/
theorem view1_eq_prefixAt (early : Bool) (k rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (hfuel : prefixRounds circuits settings (gameParameter D c.keys) c.jobs k ≤ rounds) :
    view1 K net <$> phase1At prims K circuits settings D net early k
        (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world =ᵈ
      viewCut net <$> (ceremonyPrefix prims K circuits settings D net rounds k c).run world := by
  rw [view1_phase1At]
  exact view1_eq_prefix prims K circuits settings D net k rounds c world hseeds hk hfuel

end Prefix

/-! ## The joint start from a view -/

section View

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- An outcome of a cut program with the given stop, with no rest. -/
def ofView (v : Option (Option (CheckPoint C))) : Option (CutOf C E RunResult) :=
  v.map fun q => q.elim (.inl (none, (0, 0))) fun p => .inr (p, fun _ => failure)

/-- The joint start of the check from a view. -/
def jointStopV (D : C.Coalition) {σ : Type} (v : σ × (C.Party → Option (Option (CheckPoint C))) × StreamState C) :
    Option (CheckStart C σ) :=
  jointStop D (v.1, fun i => ofView (E := E) (v.2.1 i)) v.2.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem stopPoint_ofView {α : Type} (i : C.Party) (o : Option (CutOf C E α)) :
    stopPoint i (ofView (E := E) (cutStop o)) = stopPoint i o := by
  rcases o with _ | a | ⟨p, r⟩ <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem isStop_ofView {α : Type} (o : Option (CutOf C E α)) :
    (∃ p r, ofView (E := E) (cutStop o) = some (.inr (p, r))) ↔ ∃ p r, o = some (.inr (p, r)) := by
  rcases o with _ | a | ⟨p, r⟩
  · simp [ofView, cutStop]
  · simp [ofView, cutStop]
  · exact ⟨fun _ => ⟨p, r, rfl⟩, fun _ => ⟨p, _, rfl⟩⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The joint start of an outcome of the prefix is the joint start of its view. -/
theorem jointStop_viewCut (D : C.Coalition) {σ : Type} (z : (σ × (C.Party → Option (CutOf C E RunResult))) × StreamState C) :
    jointStop D z.1 z.2 = jointStopV (E := E) D (z.1.1, (fun i => cutStop (z.1.2 i)), z.2) := by
  unfold jointStopV jointStop AllStop
  simp only [isStop_ofView, stopPoint_ofView]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The fields of a joint start. -/
theorem jointStop_some (D : C.Coalition) {σ α : Type} (r : σ × (C.Party → Option (CutOf C E α))) (w : StreamState C)
    (start : CheckStart C σ) (h : jointStop D r w = some start) :
    AllStop D r.2 ∧ ∃ j, j ∉ D.1 ∧ start.keys = (fun i => (stopPoint i (r.2 i)).ctx.keys) ∧
      start.prss = (fun i => (stopPoint i (r.2 i)).ctx.prss) ∧
      start.counts = (stopPoint j (r.2 j)).tuples.map (·.count) ∧ start.x = (fun i => (stopPoint i (r.2 i)).tuples) ∧
      start.L = (stopPoint j (r.2 j)).state.label ∧ start.tg = (stopPoint j (r.2 j)).state.tag ∧ start.st = r.1 ∧
      start.world = w := by
  unfold jointStop at h
  split_ifs at h with hall
  split at h
  · rename_i j hj
    cases h
    have hjD := List.find?_some hj
    simp only [decide_eq_true_eq] at hjD
    exact ⟨hall, j, hjD, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

end View

/-! ## The second phase and the pilot -/

section Check

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

omit [Fintype E] [DecidableEq E] in
/-- At a joint start of the first phase, each honest operator has keys and stopped at the start of
the check of its recorded prefix, with that start in the support of its program. It holds at both
places of the opening record. -/
theorem honest_stopAt (early : Bool) (k : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (phase1At prims K circuits settings D net early k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world))
    (start : CheckStart C net.State) (hj : jointStopV (E := E) D (view1 K net y1) = some start) (i : C.Party)
    (hi : i ∉ D.1) :
    ∃ keys p, c.keys i = some keys ∧ (y1.1.2 i).output = some p ∧
      outOf y1.1.2 i ∈ support (pre1At K circuits settings early k i c) ∧
      stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i)) = pointOf K p.1.2.2.1 := by
  obtain ⟨hall, -⟩ := jointStop_some D _ _ start hj
  obtain ⟨point, rest, hpt⟩ := hall i hi
  have hout : ∃ p, (y1.1.2 i).output = some p := by
    rcases ho : (y1.1.2 i).output with _ | p
    · simp [view1, ofView, ho] at hpt
    · exact ⟨p, rfl⟩
  obtain ⟨p, hp⟩ := hout
  have hdone : (y1.1.2 i).isDone := by
    cases hs : y1.1.2 i with
    | done out record => trivial
    | wait outbox resume => rw [hs] at hp; cases hp
    | call input resume => exact input.elim
  have hmem := executePhaseR_out_mem D net noFunctionality ([] : Record C E) _ c.adversary _ y1.1
    (mem_support_phase prims D _ world y1 hy1) i hi hdone
  cases hkeys : c.keys i with
  | none =>
    simp only [pre1At, hkeys, support_pure, Set.mem_singleton_iff] at hmem
    have h1 := congrArg Prod.fst hmem
    simp only at h1
    rw [hp] at h1
    cases h1
  | some keys =>
    refine ⟨keys, p, rfl, hp, hmem, ?_⟩
    simp [view1, ofView, hp, stopPoint]

omit [Fintype E] [DecidableEq E] in
/-- At a joint start of the first phase, each honest operator has keys and stopped at the start of
the check of its recorded prefix, with that start in the support of its program. -/
theorem honest_stop (k : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (phase1 prims K circuits settings D net k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world))
    (start : CheckStart C net.State) (hj : jointStopV (E := E) D (view1 K net y1) = some start) (i : C.Party)
    (hi : i ∉ D.1) :
    ∃ keys p, c.keys i = some keys ∧ (y1.1.2 i).output = some p ∧
      outOf y1.1.2 i ∈ support (pre1 K circuits settings k i c) ∧
      stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i)) = pointOf K p.1.2.2.1 :=
  honest_stopAt prims K circuits settings D net false k c world y1 hy1 start hj i hi

/-- The second phase from a joint start, with the records dropped and the results forgotten, has the
law of the check of the pilot from that start, at both places of the opening record. -/
theorem phase2_eq_checkAt (early : Bool) (k : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (phase1At prims K circuits settings D net early k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world))
    (start : CheckStart C net.State) (hj : jointStopV (E := E) D (view1 K net y1) = some start) :
    (fun y2 => ((y2.1.1, fun i => (y2.1.2 i).output.map fun _ => ()), y2.2)) <$>
        phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
          (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 =ᵈ
      checkFrom prims K D net start := by
  obtain ⟨-, j, hjD, hkeysS, hprssS, hcounts, hx, hL, htg, hst, hworld⟩ := jointStop_some D _ _ start hj
  have hfacts := fun i hi => honest_stopAt prims K circuits settings D net early k c world y1 hy1 start hj i hi
  have hpoint : ∀ i, i ∉ D.1 → ∃ keys p prss, c.keys i = some keys ∧ (y1.1.2 i).output = some p ∧
      stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i)) = pointOf K p.1.2.2.1 ∧
      PointAt K i ⟨i, keys, prss⟩ (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind)))
        (c.counters.1 + (((chunks settings.batchSize c.jobs).take k).map
          (jobLabel circuits (gameParameter D c.keys))).sum) (c.counters.2 + k) (pointOf K p.1.2.2.1) := by
    intro i hi
    obtain ⟨keys, p, hkeys, hp, hmem, hstop⟩ := hfacts i hi
    simp only [pre1At, hkeys] at hmem
    obtain ⟨prss, hpa⟩ := recPrefixAt_pointAt K circuits settings early k i c keys hkeys hk _ hmem p hp
    rw [parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys] at hpa
    exact ⟨keys, p, prss, hkeys, hp, hstop, hpa⟩
  obtain ⟨keysj, pj, prssj, -, -, hstopj, hpaj⟩ := hpoint j hjD
  have hcountsum : start.counts.sum = (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
      (circuits (gameParameter D c.keys) ·.kind))).sum := by
    rw [hcounts]
    change ((stopPoint j (ofView (E := E) ((view1 K net y1).2.1 j))).tuples.map (·.count)).sum = _
    rw [hstopj, hpaj.2.1]
  have hxi : ∀ i, i ∉ D.1 → ∃ p : PreOut C, (y1.1.2 i).output = some p ∧
      start.x i = (pointOf K p.1.2.2.1).tuples ∧ start.keys i = p.1.2.2.1.ctx.keys ∧
      start.prss i = p.1.2.2.1.ctx.prss ∧ p.1.2.2.1.ctx.self = i ∧
      p.1.2.2.1.state = ⟨filledHistory K i (start.x i), start.L, start.tg⟩ ∧
      ((start.x i).map (·.count)).sum = (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum := by
    intro i hi
    obtain ⟨keys, p, prss, -, hp, hstop, hpa⟩ := hpoint i hi
    have hxe : start.x i = (pointOf K p.1.2.2.1).tuples := by
      rw [hx]
      change (stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i))).tuples = _
      rw [hstop]
    have hctx : p.1.2.2.1.ctx = ⟨i, keys, prss⟩ := hpa.1
    refine ⟨p, hp, hxe, ?_, ?_, by rw [hctx], ?_, ?_⟩
    · rw [hkeysS]
      change (stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i))).ctx.keys = _
      rw [hstop]
      rfl
    · rw [hprssS]
      change (stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i))).ctx.prss = _
      rw [hstop]
      rfl
    · have hs := hpa.2.2
      have hsj := hpaj.2.2
      have hlen : (pointOf K p.1.2.2.1).tuples.length = (pointOf K pj.1.2.2.1).tuples.length := by
        rw [← List.length_map (f := (·.count)), hpa.2.1, ← hpaj.2.1, List.length_map]
      rw [hL, htg]
      change p.1.2.2.1.state = ⟨_, (stopPoint j (ofView (E := E) ((view1 K net y1).2.1 j))).state.label,
        (stopPoint j (ofView (E := E) ((view1 K net y1).2.1 j))).state.tag⟩
      rw [hstopj, hxe]
      change (pointOf K p.1.2.2.1).state = _
      rw [hs, hsj, hlen]
    · rw [hxe, hpa.2.1]
  have hL1 : (fun y2 : (net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C =>
        ((y2.1.1, fun i => (y2.1.2 i).output.map fun _ => ()), y2.2)) <$>
        phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
          (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 =
      (simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
        (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
          (circuits (gameParameter D c.keys) ·.kind))).sum) y1.1.1
        fun i => (fun _ => ()) <$> dropRecord (chk2 K i c (outOf y1.1.2 i)))).run y1.2 := by
    rw [WorldSplit.executePhase_map, simulateQ_map, StateT.run_map]
    unfold phase2
    rw [← ghostPhase_erase, Functor.map_map]
  rw [hL1]
  unfold checkFrom pilotRun
  rw [hcountsum, hst, hworld]
  obtain ⟨m, hm⟩ : ∃ m, checkRounds (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
      (circuits (gameParameter D c.keys) ·.kind))).sum = checkLabels (headCounts (((chunks settings.batchSize
        c.jobs).getD k []).map (circuits (gameParameter D c.keys) ·.kind))).sum + m := by
    have hle : ∀ n, checkLabels n ≤ checkRounds n := fun n => by
      unfold checkLabels checkRounds
      split_ifs <;> omega
    exact ⟨_, (Nat.add_sub_cancel' (hle _)).symm⟩
  rw [hm]
  refine EvalDistEq.trans ?_ (WorldSplit.executePhase_extra (impl := streamWorld prims D) D net noFunctionality _ m
    y1.1.1 _ (fun i hi => ?_) y1.2).symm
  · have hc := executePhase_congr D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
      (circuits (gameParameter D c.keys) ·.kind))).sum) y1.1.1
      (fun i => (fun _ => ()) <$> dropRecord (chk2 K i c (outOf y1.1.2 i)))
      (fun i => (check K (pilotContext start.keys start.prss i) (realCheckBuildingBlocks K
        (pilotContext start.keys start.prss i)) (start.x i)).run' ⟨filledHistory K i (start.x i), start.L, start.tg⟩)
      fun i hi => by
        obtain ⟨p, hp, hxe, hkeysI, hprssI, hself, hstate, -⟩ := hxi i hi
        obtain ⟨keys, -, -, hkeys, -⟩ := hpoint i hi
        have hout : outOf y1.1.2 i = (some p, (y1.1.2 i).record []) := by
          unfold outOf
          rw [hp]
        rw [hout]
        simp only [chk2, hkeys]
        have hdrop : dropRecord ((fun y => (y.1, (y1.1.2 i).record [] ++ y.2)) <$>
            (recCheck K p.1.2.2.1 p.2).run.run) = dropRec (recCheck K p.1.2.2.1 p.2) := by
          change OptionT.mk (Prod.fst <$> _) = OptionT.mk (Prod.fst <$> _)
          rw [Functor.map_map]
        rw [hdrop]
        refine dropRec_recCheck K p.1.2.2.1 p.2 start.keys start.prss i (start.x i) start.L start.tg ?_ ?_ hstate
        · rw [pilotContext, hkeysI, hprssI, ← hself]
        · rw [hxe]
          rfl
    rw [hc]
  · have ht := runTimed_realCheck (G := RealSpec) K (pilotContext start.keys start.prss i) (start.x i)
      ⟨filledHistory K i (start.x i), start.L, start.tg⟩
    obtain ⟨-, -, -, -, -, -, -, hsum⟩ := hxi i hi
    rw [hsum] at ht
    rw [StateT.run'_eq]
    exact Timed.map _ ht

/-- The second phase from a joint start, with the records dropped and the results forgotten, has the
law of the check of the pilot from that start. -/
theorem phase2_eq_check (k : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (phase1 prims K circuits settings D net k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world))
    (start : CheckStart C net.State) (hj : jointStopV (E := E) D (view1 K net y1) = some start) :
    (fun y2 => ((y2.1.1, fun i => (y2.1.2 i).output.map fun _ => ()), y2.2)) <$>
        phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
          (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 =ᵈ
      checkFrom prims K D net start :=
  phase2_eq_checkAt prims K circuits settings D net false k c world hseeds hk y1 hy1 start hj

end Check

/-! ## The first part of the joint law -/

section First

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The outcome of the cut at check `k` that the first two phases give. -/
def cutOutcome (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (y2 : (net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C) :
    Option (CheckStart C net.State) × Option ((net.State × (C.Party → Option Unit)) × StreamState C) :=
  match jointStopV (E := E) D (view1 K net y1) with
  | some start => (some start, some ((y2.1.1, fun i => (y2.1.2 i).output.map fun _ => ()), y2.2))
  | none => (none, none)

/-- The rest of `ceremonyCheckAt` after the prefix, on the view of the prefix. -/
def checkCont (v : net.State × (C.Party → Option (Option (CheckPoint C))) × StreamState C) :
    ProbComp (Option (CheckStart C net.State) × Option ((net.State × (C.Party → Option Unit)) × StreamState C)) :=
  match jointStopV (E := E) D v with
  | some start => (fun out => (some start, some out)) <$> checkFrom prims K D net start
  | none => pure (none, none)

/-- The first two phases, read as the cut at check `k`, have the law of `ceremonyCheckAt`, at both
places of the opening record. -/
theorem cutOutcome_eqAt (early : Bool) (k rounds r3 : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (hfuel : prefixRounds circuits settings (gameParameter D c.keys) c.jobs k ≤ rounds) :
    (phase1At prims K circuits settings D net early k (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k)
        c world >>= fun y1 =>
      phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 >>= fun y2 =>
        phase3At prims K circuits settings D net early k r3 c y1 y2 >>= fun _ => pure (cutOutcome K D net y1 y2)) =ᵈ
      ceremonyCheckAt prims K circuits settings D net rounds k c world := by
  refine (EvalDistEq.bind_right _ fun y1 => EvalDistEq.bind_right _ fun y2 =>
    EvalDistEq.bind_const _ _).trans ?_
  refine (EvalDistEq.bind_congr_of_support _ (g := fun y1 => checkCont prims K D net (view1 K net y1))
    fun y1 hy1 => ?_).trans ?_
  · cases hj : jointStopV (E := E) D (view1 K net y1) with
    | none =>
      simp only [cutOutcome, checkCont, hj]
      exact EvalDistEq.bind_const _ _
    | some start =>
      simp only [cutOutcome, checkCont, hj]
      have h := phase2_eq_checkAt prims K circuits settings D net early k c world hseeds hk y1 hy1 start hj
      have h' := h.map fun out => (some start, some out)
      rw [Functor.map_map] at h'
      rw [← bind_pure_comp] at h'
      exact h'
  · rw [← bind_map_left (view1 K net) _ (checkCont prims K D net)]
    refine (EvalDistEq.bind (view1_eq_prefixAt prims K circuits settings D net early k rounds c world hseeds hk hfuel)
      fun _ => EvalDistEq.rfl).trans ?_
    rw [bind_map_left]
    unfold ceremonyCheckAt
    refine EvalDistEq.bind_right _ fun z => ?_
    simp only [checkCont, viewCut]
    rw [jointStop_viewCut]
    exact EvalDistEq.rfl

/-- The first two phases, read as the cut at check `k`, have the law of `ceremonyCheckAt`. -/
theorem cutOutcome_eq (k rounds r3 : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (hfuel : prefixRounds circuits settings (gameParameter D c.keys) c.jobs k ≤ rounds) :
    (phase1 prims K circuits settings D net k (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k)
        c world >>= fun y1 =>
      phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 >>= fun y2 =>
        phase3 prims K circuits settings D net k r3 c y1 y2 >>= fun _ => pure (cutOutcome K D net y1 y2)) =ᵈ
      ceremonyCheckAt prims K circuits settings D net rounds k c world :=
  cutOutcome_eqAt prims K circuits settings D net false k rounds r3 c world hseeds hk hfuel

end First

/-! ## The rounds of the three phases -/

section Count

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The prefix and the check of batch `k` fit in the rounds of the ceremony. -/
theorem prefix_add_check_le (circuits : Circuits) (settings : Settings) (parameter : PublicParameter) (jobs : List Job)
    (k : ℕ) (hk : k < (chunks settings.batchSize jobs).length) :
    prefixRounds circuits settings parameter jobs k +
        checkLabels (headCounts (((chunks settings.batchSize jobs).getD k []).map (circuits parameter ·.kind))).sum ≤
      CheckTiming.ceremonyRounds circuits settings parameter jobs := by
  have hsplit : chunks settings.batchSize jobs = (chunks settings.batchSize jobs).take k ++
      (chunks settings.batchSize jobs).getD k [] :: (chunks settings.batchSize jobs).drop (k + 1) := by
    rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hsum : ∀ cs : List Circuit, (headCounts cs).sum = tupleCount cs := fun cs => by
    rw [headCounts, List.sum_append, List.sum_singleton, tupleCount_eq]
  unfold prefixRounds stopRounds CheckTiming.ceremonyRounds
  rw [List.getElem?_eq_getElem hk, ← List.getD_eq_getElem _ [] hk, hsum]
  dsimp only
  conv_rhs => rw [hsplit]
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  rw [show ∀ (m : ReshareMode) (cs : List Circuit), headRounds m cs = depth cs * m.rounds + 1 from fun _ _ => rfl]
  unfold CheckTiming.exactBatchRounds checkLabels
  generalize depth (((chunks settings.batchSize jobs).getD k []).map (circuits parameter ·.kind)) *
    settings.mode.rounds = dr
  generalize ((List.take k (chunks settings.batchSize jobs)).map fun batch =>
    depth (batch.map (circuits parameter ·.kind)) * settings.mode.rounds + 2 +
      if tupleCount (batch.map (circuits parameter ·.kind)) = 0 then 0
      else 2 * halvings (tupleCount (batch.map (circuits parameter ·.kind))) + 5).sum = A
  split_ifs <;> omega

end Count

/-! ## The link on the support of the joint law -/

section Link

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem timedLog_mem {γ : Type} {A B : γ → Prop} {n : ℕ} {p : OracleComp (PartySpec C E RealSpec) γ}
    (h : TimedLog A B n p) : ∀ x ∈ support p, A x ∨ B x := by
  induction h with
  | stop n x hx =>
    intro y hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Or.inl hx
  | done x hx =>
    intro y hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Or.inr hx
  | queryLocal n q k _ ih =>
    intro y hy
    change y ∈ support (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k) at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨r, -, hr⟩ := hy
    exact ih r y hr
  | round n out k _ ih =>
    intro y hy
    change y ∈ support (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k) at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨r, -, hr⟩ := hy
    exact ih r y hr

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The record of each honest step at the end of a ghost phase is blank or a record of an output of
its program. -/
theorem executePhaseR_record {α : Type} (fuel : ℕ) (st : net.State)
    (prog : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × Record C E))
    (z : net.State × (C.Party → RStep C E RealSpec α (Record C E)))
    (hz : z ∈ support (executePhaseR worldRoles D net noFunctionality ([] : Record C E) fuel st prog)) (i : C.Party)
    (hi : i ∉ D.1) : (z.2 i).record [] = [] ∨ ∃ out, (out, (z.2 i).record []) ∈ support (prog i) := by
  cases hs : z.2 i with
  | done out record =>
    right
    refine ⟨out, ?_⟩
    have h := executePhaseR_out_mem D net noFunctionality ([] : Record C E) fuel st prog z hz i hi (by rw [hs]; trivial)
    rw [hs] at h
    exact h
  | wait outbox resume => exact Or.inl rfl
  | call input resume => exact Or.inl rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem jointStop_isSome {σ α : Type} (r : σ × (C.Party → Option (CutOf C E α))) (w : StreamState C)
    (hall : AllStop D r.2) (i : C.Party) (hi : i ∉ D.1) : ∃ start, jointStop D r w = some start := by
  unfold jointStop
  rw [ite_eq_left hall]
  cases hf : C.parties.find? fun i => i ∉ D.1 with
  | some j => exact ⟨_, rfl⟩
  | none =>
    have := List.find?_eq_none.1 hf i (List.mem_finRange i)
    simp only [decide_eq_true_eq, not_not] at this
    exact absurd this hi

/-- On the support of the three phases, the cut outcome of the first two phases is linked to the end
of the third by `CutLinkFree`, at both places of the opening record. An honest index comes from the
bound of the coalition, so the link needs no honest output. -/
theorem cutLink_phasesAt (early : Bool) (k r3 : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (phase1At prims K circuits settings D net early k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world))
    (y2 : (net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C)
    (hy2 : y2 ∈ support (phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum) c y1))
    (y3 : (net.State × CeremonySteps C E) × StreamState C)
    (hy3 : y3 ∈ support (phase3At prims K circuits settings D net early k r3 c y1 y2)) :
    CutLinkFree K D k (cutOutcome K D net y1 y2) y3 := by
  intro hstart hglobal
  have hy1' := mem_support_phase prims D _ world y1 hy1
  have hy2' := mem_support_phase prims D _ y1.2 y2 hy2
  have hy3' := mem_support_phase prims D _ y2.2 y3 hy3
  have hdone1 := executePhaseR_timed_done D net noFunctionality ([] : Record C E) _ c.adversary _
    (fun i hi => timedR_pre1At K circuits settings early k D c hseeds hk i hi) y1.1 hy1'
  have hmem1 : ∀ i, i ∉ D.1 → outOf y1.1.2 i ∈ support (pre1At K circuits settings early k i c) := fun i hi =>
    executePhaseR_out_mem D net noFunctionality ([] : Record C E) _ c.adversary _ y1.1 hy1' i hi (hdone1 i hi)
  have hdone2 := executePhaseR_timed_done D net noFunctionality ([] : Record C E) _ y1.1.1 _
    (fun i hi => timedR_chk2At K circuits settings early k D c hseeds hk i hi _ (hmem1 i hi)) y2.1 hy2'
  have hmem2 : ∀ i, i ∉ D.1 → outOf y2.1.2 i ∈ support (chk2 K i c (outOf y1.1.2 i)) := fun i hi =>
    executePhaseR_out_mem D net noFunctionality ([] : Record C E) _ y1.1.1 _ y2.1 hy2' i hi (hdone2 i hi)
  have hrec3 := fun i hi => executePhaseR_record D net _ y2.1.1 _ y3.1 hy3' i hi
  have hall : ∀ i, i ∉ D.1 → ∃ p, (y1.1.2 i).output = some p := by
    intro i hi
    by_contra hnone
    have hnone' : (y1.1.2 i).output = none := by
      rcases ho : (y1.1.2 i).output with _ | p
      · rfl
      · exact absurd ⟨p, ho⟩ hnone
    have hw : (startsOf ((y1.1.2 i).record [])).length ≤ k := by
      have hm := hmem1 i hi
      unfold outOf at hm
      cases hkeys : c.keys i with
      | none =>
        simp only [pre1At, hkeys, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
        rw [hm.2]
        simp [startsOf]
      | some keys =>
        simp only [pre1At, hkeys] at hm
        exact leafStarts_recPrefixAt K circuits settings early k i keys c.jobs c.counters _ hm
    have h2 : outOf y2.1.2 i = (none, (y1.1.2 i).record []) := by
      have hm := hmem2 i hi
      have hx : outOf y1.1.2 i = (none, (y1.1.2 i).record []) := by unfold outOf; rw [hnone']
      rw [hx] at hm
      cases hkeys : c.keys i <;> simp only [chk2, hkeys, support_pure, Set.mem_singleton_iff] at hm <;> exact hm
    have hrec : ceremonyRecord y3.1.2 i = [] ∨ ceremonyRecord y3.1.2 i = (y1.1.2 i).record [] := by
      rcases hrec3 i hi with h | ⟨out, h⟩
      · exact Or.inl h
      · right
        have hx : outOf y1.1.2 i = (none, (y1.1.2 i).record []) := by unfold outOf; rw [hnone']
        rw [hx, h2] at h
        cases hkeys : c.keys i <;>
          simp only [cont2At, hkeys, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h <;>
          exact h.2
    have hs := hstart i hi
    rcases hrec with h | h
    · rw [h] at hs
      simp [startsOf] at hs
    · rw [h, List.getElem?_eq_none hw] at hs
      simp at hs
  obtain ⟨i0, hi0⟩ := exists_honest D
  have hAll : AllStop D (fun i => ofView (E := E) ((view1 K net y1).2.1 i)) := fun i hi => by
    obtain ⟨p, hp⟩ := hall i hi
    exact ⟨pointOf K p.1.2.2.1, fun _ => failure, by simp [view1, ofView, hp]⟩
  obtain ⟨start, hjV⟩ := jointStop_isSome D ((view1 K net y1).1, fun i => ofView (E := E) ((view1 K net y1).2.1 i))
    (view1 K net y1).2.2 hAll i0 hi0
  change jointStopV (E := E) D (view1 K net y1) = some start at hjV
  obtain ⟨-, j, hjD, hkeysS, hprssS, hcounts, hx, hL, htg, hst, hworld⟩ := jointStop_some D _ _ start hjV
  have hfacts : ∀ i, i ∉ D.1 → ∃ p : PreOut C, stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i)) =
      pointOf K p.1.2.2.1 ∧ (startsOf ((y1.1.2 i).record [])).length = k ∧
      (openingsOf ((y1.1.2 i).record [])).length = k ∧
      (ceremonyRecord y3.1.2 i = [] ∨ ∃ t, ceremonyRecord y3.1.2 i = (y1.1.2 i).record [] ++ .start p.1.2.2.1 :: t) ∧
      ((y2.1.2 i).output = none →
        ceremonyRecord y3.1.2 i = [] ∨ ceremonyRecord y3.1.2 i = (y1.1.2 i).record [] ++ [.start p.1.2.2.1]) := by
    intro i hi
    obtain ⟨keys, p, hkeys, hp, hmem, hstop⟩ :=
      honest_stopAt prims K circuits settings D net early k c world y1 hy1 start hjV i hi
    have hx1 : outOf y1.1.2 i = (some p, (y1.1.2 i).record []) := by unfold outOf; rw [hp]
    rw [hx1] at hmem
    simp only [pre1At, hkeys] at hmem
    have hfull := timedLog_mem (timedLog_recPrefixAt K circuits settings early k i keys c.jobs hk c.counters) _ hmem
    rcases hfull with ⟨hn, -⟩ | ⟨-, hs1, ho1⟩
    · cases hn
    have hm2 := hmem2 i hi
    rw [hx1] at hm2
    simp only [chk2, hkeys, support_map, Set.mem_image] at hm2
    obtain ⟨y, hy, hy2e⟩ := hm2
    have hyrec : y.2 = [.start p.1.2.2.1] := by
      rcases timedLog_mem (timedLog_recCheck K p.1.2.2.1 p.2) y hy with h | h
      · exact h.2
      · exact h.2
    refine ⟨p, hstop, hs1, ho1, ?_, ?_⟩
    · rcases hrec3 i hi with h | ⟨out, h⟩
      · exact Or.inl h
      · right
        rw [hx1, ← hy2e] at h
        rcases hyo : y.1 with _ | r
        · rw [hyo] at h
          simp only [cont2At, hkeys, recCont, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
          exact ⟨[], by unfold ceremonyRecord; rw [h.2, hyrec]⟩
        · rw [hyo] at h
          simp only [cont2At, hkeys, recCont, support_map, Set.mem_image] at h
          obtain ⟨z, -, hz⟩ := h
          refine ⟨z.2, ?_⟩
          have := congrArg Prod.snd hz
          simp only at this
          unfold ceremonyRecord
          rw [← this, hyrec, List.append_assoc]
          rfl
    · intro hnone
      rcases hrec3 i hi with h | ⟨out, h⟩
      · exact Or.inl h
      · right
        have hy1o : y.1 = none := by
          have := congrArg Prod.fst hy2e
          simp only [outOf] at this
          rw [this]
          exact hnone
        rw [hx1, ← hy2e, hy1o] at h
        simp only [cont2At, hkeys, recCont, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        unfold ceremonyRecord
        rw [h.2, hyrec]
  have hrecK : ∀ i, i ∉ D.1 → ∃ p : PreOut C, stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i)) =
      pointOf K p.1.2.2.1 ∧ (startsOf (ceremonyRecord y3.1.2 i))[k]? = some p.1.2.2.1 ∧
      ((y2.1.2 i).output = none → (openingsOf (ceremonyRecord y3.1.2 i)).length ≤ k) := by
    intro i hi
    obtain ⟨p, hstop, hs1, ho1, hrec, hnone⟩ := hfacts i hi
    have hne : ceremonyRecord y3.1.2 i ≠ [] := fun h => by
      have := hstart i hi
      rw [h] at this
      simp [startsOf] at this
    obtain ⟨t, ht⟩ := hrec.resolve_left hne
    refine ⟨p, hstop, ?_, fun hn => ?_⟩
    · rw [ht, startsOf_append, List.getElem?_append_right (by omega), hs1, Nat.sub_self]
      simp [startsOf]
    · rcases hnone hn with h | h
      · exact absurd h hne
      · rw [h, length_openingsOf_append, ho1]
        simp [openingsOf]
  refine ⟨start, ((y2.1.1, fun i => (y2.1.2 i).output.map fun _ => ()), y2.2), by simp only [cutOutcome, hjV],
    fun i hi => ?_, fun i hi hopen => ?_, ?_, ?_⟩
  · obtain ⟨p, hstop, hk', -⟩ := hrecK i hi
    refine ⟨?_, fun b' hb' => ?_⟩
    · rw [hx]
      change (stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i))).tuples = _
      rw [hstop]
      unfold ceremonyTuplesAt
      rw [hk']
      rfl
    · rw [hk'] at hb'
      cases hb'
      rw [hprssS]
      change _ = (stopPoint i (ofView (E := E) ((view1 K net y1).2.1 i))).ctx.prss
      rw [hstop]
      rfl
  · obtain ⟨p, -, -, hle⟩ := hrecK i hi
    rcases ho : (y2.1.2 i).output with _ | r
    · exact absurd (hle ho) (by omega)
    · simp [ho]
  · rw [hworld]
    exact (streamWorld_run_mono prims D _ y1.2 y2 hy2).trans (streamWorld_run_mono prims D _ y2.2 y3 hy3)
  · exact streamWorld_run_mono prims D _ y2.2 y3 hy3

/-- On the support of the three phases, the cut outcome of the first two phases is linked to the end
of the third. -/
theorem cutLink_phases (k r3 : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (hk : k < (chunks settings.batchSize c.jobs).length)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (phase1 prims K circuits settings D net k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world))
    (y2 : (net.State × (C.Party → RStep C E RealSpec (ChkOut C) (Record C E))) × StreamState C)
    (hy2 : y2 ∈ support (phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
        (circuits (gameParameter D c.keys) ·.kind))).sum) c y1))
    (y3 : (net.State × CeremonySteps C E) × StreamState C)
    (hy3 : y3 ∈ support (phase3 prims K circuits settings D net k r3 c y1 y2)) :
    CutLink K D k (cutOutcome K D net y1 y2) y3 :=
  fun hstart _ hglobal =>
    cutLink_phasesAt prims K circuits settings D net false k r3 c world hseeds hk y1 hy1 y2 hy2 y3 hy3 hstart hglobal

end Link

/-! ## `CouplingLaw` and `CeremonyCoupling` -/

section Leaf

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The joint law of the cut at check `k` and the ghost run, at both places of the opening record,
with `CutLinkFree` on its support. The joint law is the three phases with the cut outcome of the
first two. Its first part has the law of `ceremonyCheckAt` (`cutOutcome_eqAt`), its second part has
the law of the ghost run (`ghost_eq_phasesAt`), and its support has the link (`cutLink_phasesAt`). -/
theorem couplingLawWith (early : Bool) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (ℓ : StartBudget) (c : CeremonyStart C net.State) (world : StreamState C) (hready : CeremonyReady D ℓ c world)
    (hfuel : CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length) :
    ∃ J : ProbComp ((Option (CheckStart C net.State) ×
        Option ((net.State × (C.Party → Option Unit)) × StreamState C)) ×
        ((net.State × CeremonySteps C E) × StreamState C)),
      (Prod.fst <$> J) =ᵈ ceremonyCheckAt prims K circuits settings D net rounds k c world ∧
      (Prod.snd <$> J) =ᵈ (ghostCeremonyAt prims K circuits settings D net early rounds c).run world ∧
      ∀ x ∈ support J, CutLinkFree K D k x.1 x.2 := by
  have hseeds : seedsDiffer D c.keys = false := hready.1
  have hle := prefix_add_check_le circuits settings (gameParameter D c.keys) c.jobs k hk
  refine ⟨phase1At prims K circuits settings D net early k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world >>= fun y1 =>
    phase2 prims K D net (checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
      (circuits (gameParameter D c.keys) ·.kind))).sum) c y1 >>= fun y2 =>
      phase3At prims K circuits settings D net early k
        (rounds - (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k +
          checkLabels (headCounts (((chunks settings.batchSize c.jobs).getD k []).map
            (circuits (gameParameter D c.keys) ·.kind))).sum)) c y1 y2 >>= fun y3 =>
        pure (cutOutcome K D net y1 y2, y3), ?_, ?_, ?_⟩
  · simp only [map_bind, map_pure]
    exact cutOutcome_eqAt prims K circuits settings D net early k rounds _ c world hseeds hk (by omega)
  · simp only [map_bind, map_pure, bind_pure]
    exact (ghost_eq_phasesAt prims K circuits settings D net early k rounds _ c world hseeds hk (by omega)).symm
  · intro x hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨y1, hy1, y2, hy2, y3, hy3, rfl⟩ := hx
    exact cutLink_phasesAt prims K circuits settings D net early k _ c world hseeds hk y1 hy1 y2 hy2 y3 hy3

/-- The proof of `CouplingLaw`, as `couplingLawWith` at `early = false`. -/
theorem couplingLaw : CouplingLaw prims K circuits settings := by
  intro _ D net rounds ℓ c world hready hfuel k hk
  obtain ⟨J, h1, h2, h3⟩ := couplingLawWith prims K circuits settings false D net rounds ℓ c world hready hfuel k hk
  exact ⟨J, h1, h2, fun x hx hs _ hg => h3 x hx hs hg⟩

/-- `couplingLaw` and `ceremonyCoupling_of_law` give `CeremonyCoupling`. -/
theorem ceremonyCoupling : CeremonyCoupling prims K circuits settings :=
  ceremonyCoupling_of_law prims K circuits settings (couplingLaw prims K circuits settings)

end Leaf

end Joint

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Joint.ceremonyCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Joint.ceremonyCoupling

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Joint.couplingLawWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Joint.couplingLawWith
