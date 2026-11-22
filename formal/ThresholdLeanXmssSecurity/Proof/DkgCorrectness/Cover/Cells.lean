import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.SharesAgree
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.MonitorReplay

/-!
# The PRF cells at the end of a ceremony

`CeremonyCells` states that the hash cache at the end of a ceremony holds the PRF cells of its jobs,
when an honest operator ends it. `ceremonyCells_of_started` proves it from `CeremonyStarted`, which
states that each honest operator records the start of each check of a ceremony that an honest
operator ends. Each honest holder of a term then made the PRF calls of the term at the start of each
check, and a call that left no cell would leave the record free in that cell.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The ghost run with `H` fixed -/

section Path

variable {ι : Type} {G : OracleSpec ι} {α ρ : Type} (prims : Primitives) (D : C.Coalition)

/-- A ghost step is on the path of its recorded program with `H` fixed to `h`. -/
def OnPathRH (h : Query C → HashOutput) (program : OracleComp (PartySpec C E G) (Option α × ρ))
    (step : RStep C E G α ρ) : Prop :=
  OnPath h (some <$> program) (GhostBatch.toStep step)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A done ghost step on the path of its program with `H` fixed to `h` has its output and its record
in the support of the program with `H` fixed to `h`. -/
theorem OnPathRH.done {h : Query C → HashOutput} {program : OracleComp (PartySpec C E G) (Option α × ρ)}
    {out : Option α} {record : ρ} (hpath : OnPathRH h program (.done out record)) :
    (out, record) ∈ support (simulateQ (fixHash h) program) := by
  have hmem := hpath (out, record) (by simp [GhostBatch.toStep, stepProgram])
  rw [simulateQ_map, support_map] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  cases hpe
  exact hp

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem free_advanceR_onPathRH (oa : OracleComp (PartySpec C E G) (Option α × ρ)) (s : HashCache C × HiddenCache C)
    (z : RStep C E G α ρ × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (free (advanceR oa))).run s)) :
    s.1 ≤ z.2.1 ∧ ∀ h, Good prims h → Agrees h z.2.1 → OnPathRH h oa z.1 := by
  have hz' : (GhostBatch.toStep z.1, z.2) ∈
      support ((simulateQ (streamWorld prims D) (free (advance (some <$> oa)))).run s) := by
    rw [← GhostBatch.advanceR_toStep]
    change _ ∈ support ((simulateQ (streamWorld prims D) ((worldRoles (C := C)).honest
      (GhostBatch.toStep <$> advanceR oa))).run s)
    rw [worldRoles_honest_map, simulateQ_map, StateT.run_map, support_map]
    exact ⟨z, hz, rfl⟩
  exact advance_onPath prims D _ s _ hz'

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A round of the ghost run grows the hash cache and keeps each honest step on the path of its
program with `H` fixed to each good `h` that agrees with the new cache. -/
theorem stepRoundR_onPathRH {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (blank : ρ) (steps : C.Party → RStep C E RealSpec α ρ)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (s : HashCache C × HiddenCache C) (y : (A.State × (C.Party → RStep C E RealSpec α ρ) ×
      (C.Party → C.Party → Option (Msg E))) × (HashCache C × HiddenCache C))
    (hy : y ∈ support ((simulateQ (streamWorld prims D)
      (stepRoundR worldRoles D' A noFunctionality blank st steps)).run s)) :
    s.1 ≤ y.2.1 ∧ ∀ h, Good prims h → Agrees h y.2.1 → (∀ i, i ∉ D'.1 → OnPathRH h (program i) (steps i)) →
      ∀ i, i ∉ D'.1 → OnPathRH h (program i) (y.1.2.1 i) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D'.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D'.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRoundR at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, ha, w, hw, rfl⟩ := hy
  have hseq := sequenceFin_streamWorld prims D (fun j v c => j ∉ D'.1 → ∀ h, Good prims h → Agrees h c →
      OnPathRH h (program j) (steps j) → OnPathRH h (program j) v) _
    (fun j b c c' hq hle hj h hg hagree => hq hj h hg (hagree.mono hle)) (fun j s' y hy hj h hg hagree hon => ?_)
    a.2 w hw
  · exact ⟨(streamWorld_run_mono prims D _ s a ha).trans (streamWorld_run_mono prims D _ a.2 w hw),
      fun h hg hagree hon i hi => hseq i hi h hg hagree (hon i hi)⟩
  rcases hsj : steps j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [← hsj]
    exact hon
  · simp only [hsj, hj, ↓reduceIte] at hy
    obtain ⟨-, hpath⟩ := free_advanceR_onPathRH prims D _ s' y hy
    intro a' hmem
    rw [hsj] at hon
    refine hon a' ?_
    simp only [GhostBatch.toStep, stepProgram]
    rw [simulateQ_fixHash_query_bind, mem_support_bind_iff]
    exact ⟨_, by simp [fixHash], hpath h hg hagree a' hmem⟩
  · exact input.elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem executeRoundsR_onPathRH {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (fuel : ℕ) :
    ∀ st steps s z, z ∈ support ((simulateQ (streamWorld prims D)
      (executeRoundsR worldRoles D' A noFunctionality blank fuel st steps)).run s) →
      ∀ h, Good prims h → Agrees h z.2.1 → (∀ i, i ∉ D'.1 → OnPathRH h (program i) (steps i)) →
        ∀ i, i ∉ D'.1 → OnPathRH h (program i) (z.1.2 i) := by
  induction fuel with
  | zero =>
    intro st steps s z hz
    simp only [executeRoundsR, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun _ _ _ hon => hon
  | succ fuel ih =>
    intro st steps s z hz h hg hagree hon
    unfold executeRoundsR at hz
    split_ifs at hz with hdone
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hon
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rcases y with ⟨⟨state, steps', sent⟩, c⟩
      obtain ⟨-, hstep⟩ := stepRoundR_onPathRH prims D D' A st blank steps program s _ hy
      exact ih state steps' c z hz h hg hagree
        (hstep h hg (hagree.mono (streamWorld_run_mono prims D _ c z hz)) hon)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase of the ghost run ends with each honest step on the path of its program with `H` fixed to
each good `h` that agrees with the end cache. -/
theorem executePhaseR_onPathRH {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ)
    (fuel : ℕ) (st : A.State) (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (s : HashCache C × HiddenCache C)
    (z : (A.State × (C.Party → RStep C E RealSpec α ρ)) × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executePhaseR worldRoles D' A noFunctionality blank fuel st program)).run s))
    (h : Query C → HashOutput) (hg : Good prims h) (hagree : Agrees h z.2.1) :
    ∀ i, i ∉ D'.1 → OnPathRH h (program i) (z.1.2 i) := by
  unfold executePhaseR at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startStepsR at hy
  have hstart := sequenceFin_streamWorld prims D (fun j v c => j ∉ D'.1 → ∀ h, Good prims h → Agrees h c →
      OnPathRH h (program j) v) _
    (fun j b c c' hq hle hj h hg hagree => hq hj h hg (hagree.mono hle)) (fun j s' w hw hj h hg hagree => ?_) s y hy
  · exact executeRoundsR_onPathRH prims D D' A blank program fuel st y.1 y.2 z hz h hg hagree
      fun i hi => hstart i hi h hg (hagree.mono (streamWorld_run_mono prims D _ y.2 z hz))
  simp only [hj, ↓reduceIte] at hw
  exact (free_advanceR_onPathRH prims D _ s' w hw).2 h hg hagree

end Path

/-! ## The starts of the record of one ceremony -/

section Starts

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each start of a record of full batches and a cut batch has the shape of the starts. -/
theorem outcomeOk_starts {β : Type} {S : BatchStart C → Prop}
    {P : BatchStart C × Mail C E × List (List Bit) → Prop} (hP : ∀ x, P x → S x.1) {z : Option β × Record C E}
    (hz : GhostBatch.OutcomeOk S P z) : ∀ b ∈ startsOf z.2, S b := by
  have hfull : ∀ bs : List (BatchStart C × Mail C E × List (List Bit)), (∀ x ∈ bs, P x) →
      ∀ b ∈ startsOf (bs.flatMap GhostBatch.blockOf), S b := by
    intro bs hbs b hb
    induction bs with
    | nil => simp [startsOf] at hb
    | cons x bs ih =>
      rw [List.flatMap_cons, GhostMonitor.startsOf_append] at hb
      rcases List.mem_append.1 hb with hb | hb
      · simp [startsOf, GhostBatch.blockOf] at hb
        rw [hb]
        exact hP x (hbs x (List.mem_cons_self))
      · exact ih (fun y hy => hbs y (List.mem_cons_of_mem _ hy)) hb
  rcases hz with ⟨bs, hbs, hrec⟩ | ⟨-, bs, tail, hbs, hrec, htail⟩
  · rw [hrec]
    exact hfull bs hbs
  · intro b hb
    rw [hrec, GhostMonitor.startsOf_append] at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hfull bs hbs b hb
    · rcases htail with rfl | ⟨b', hb', rfl | ⟨inbox, rfl⟩⟩
      · simp [startsOf] at hb
      · simp [startsOf] at hb
        rw [hb]
        exact hb'
      · simp [startsOf] at hb
        rw [hb]
        exact hb'

include prims in
/-- A start `k` in the record of an operator with keys in one ceremony, with `H` fixed to `h`, has the
`k`-th batch of the jobs and the input shares of the operator with `H` fixed to `h`. -/
theorem recCeremony_start (h : Query C → HashOutput) (j : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (keys : Keys C) (hk : c.keys j = some keys) (z : Option CeremonyResult × Record C E)
    (hz : z ∈ support (simulateQ (fixHash h) (recCeremony K circuits settings j c).run.run)) (k : ℕ)
    (b : BatchStart C) (hb : (startsOf z.2)[k]? = some b) :
    (chunks settings.batchSize c.jobs)[k]? = some b.jobs ∧ b.inputs = batchInputs h keys.seed b.jobs j := by
  unfold recCeremony at hz
  rw [hk] at hz
  obtain ⟨z₁, h₁, hstarts⟩ : ∃ z₁ ∈ support (simulateQ (fixHash h)
      ((recRun K circuits settings j keys c.jobs).run c.counters).run.run), startsOf z.2 = startsOf z₁.2 := by
    obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨a, -, z₂, h₂, rfl⟩⟩ := GhostBatch.mem_support_fix_bind h _ _ z hz
    · exact ⟨z₁, h₁, rfl⟩
    · refine ⟨z₁, h₁, ?_⟩
      rcases a with ⟨_ | outputs, st⟩
      · simp [Option.elim, OptionT.run_failure] at h₂
        simp [h₂, startsOf]
      · simp at h₂
        simp [h₂, startsOf]
  rw [hstarts] at hb
  have hshape := outcomeOk_starts (fun x hx => hx.1)
    (GhostBatch.recOkS_recRun K circuits settings h prims j keys c.jobs c.counters z₁ h₁) b
    (List.mem_of_getElem? hb)
  have hjobs := (BatchCounters.jobsIn_recRun K circuits settings j keys c.jobs c.counters z₁
    (support_simulateQ_subset _ _ h₁)).1
  refine ⟨BatchCounters.getElem?_of_prefix hjobs k b.jobs (by simp [hb]), hshape.2.2.2.2⟩

end Starts

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## A free cell changes the record -/

section Free

/-- Two lists of blocks of one length are equal only block by block. -/
theorem flatMap_blocks_eq {α β : Type} (d : ℕ) (f g : α → List β) (hf : ∀ a, (f a).length = d)
    (hg : ∀ a, (g a).length = d) : ∀ l : List α, l.flatMap f = l.flatMap g → ∀ a ∈ l, f a = g a
  | [], _, a, ha => by cases ha
  | b :: l, h, a, ha => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [hf, hg])
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h₁
    · exact flatMap_blocks_eq d f g hf hg l h₂ a ha

theorem bitsOfDigest_injective {a b : Digest} (h : bitsOfDigest a = bitsOfDigest b) : a = b := by
  unfold bitsOfDigest at h
  have hfun := List.ofFn_injective h
  refine BitVec.eq_of_getLsbD_eq fun k hk => ?_
  have hk' := congrFun hfun ⟨k, hk⟩
  by_cases ha : a.getLsbD k <;> by_cases hb : b.getLsbD k <;> simp_all

/-- Each hash output has another one with a different digest. -/
theorem exists_truncateHash_ne (u : HashOutput) : ∃ v : HashOutput, truncateHash v ≠ truncateHash u := by
  by_cases hu : truncateHash u = 0
  · refine ⟨1, ?_⟩
    rw [hu]
    decide
  · exact ⟨0, fun h => hu (by rw [← h]; decide)⟩

end Free

/-! ## The cells from the lock step -/

section Main

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `CeremonyCells` from the lock step `CeremonyStarted`. Take a PRF cell of a job and a term that is
absent from the end cache. An honest holder of the term recorded the start of the check of the batch
of the job, with its input shares on each good `h` that agrees with the end cache. Two such `h` that
differ only in the absent cell give two different input shares, which is not possible. -/
theorem ceremonyCells_of_started (started : CeremonyStarted prims K circuits settings) :
    CeremonyCells prims K circuits settings := by
  intro hsize D net rounds c world hw hseeds hkeys r hr hge hout job hjob T x hx
  rw [ghostCeremony_erase, support_map] at hr
  obtain ⟨ω, hω, rfl⟩ := hr
  obtain ⟨i, hi, hsome⟩ := hout
  have hstarted := started hsize D net rounds c world hw hseeds hkeys ω hω hge ⟨i, hi, hsome⟩
  rw [← chunks_flatten settings.batchSize hsize c.jobs, List.mem_flatten] at hjob
  obtain ⟨js, hjs, hjob⟩ := hjob
  obtain ⟨k, hk, hkjs⟩ := List.getElem_of_mem hjs
  obtain ⟨j, hjT, hj⟩ := exists_honest_holder D T
  obtain ⟨kj, hkj⟩ := Option.isSome_iff_exists.1 (hkeys j hj)
  have hseed := seed_eq_gameSeeds D c.keys hseeds j hj kj hkj T hjT
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hstarted k hk j hj)
  rcases hstep : ω.1.2 j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩
  rotate_left
  · simp [ceremonyRecord, hstep, RStep.record, startsOf] at hb
  · exact input.elim
  have hb' : (startsOf record)[k]? = some b := by simpa [ceremonyRecord, hstep, RStep.record] using hb
  have hno : NoMpc ω.2.1 := streamWorld_noMpc prims D _ world hw ω hω
  by_contra hcell
  have hnone : ω.2.1 (.prf (gameSeeds D c.keys T) x) = none := by simpa using hcell
  obtain ⟨v, hv⟩ := exists_truncateHash_ne (hashOf prims ω.2.1 (.prf (gameSeeds D c.keys T) x))
  have hg₁ := good_hashOf prims ω.2.1
  have ha₁ := agrees_hashOf prims hno
  have hg₂ : Good prims (Function.update (hashOf prims ω.2.1) (.prf (gameSeeds D c.keys T) x) v) := by
    intro y hy
    rw [Function.update_of_ne (by simp)]
    exact hg₁ y hy
  have ha₂ : Agrees (Function.update (hashOf prims ω.2.1) (.prf (gameSeeds D c.keys T) x) v) ω.2.1 := by
    intro q w hq
    by_cases hqe : q = .prf (gameSeeds D c.keys T) x
    · rw [hqe, hnone] at hq
      cases hq
    · rw [Function.update_of_ne hqe]
      exact ha₁ q w hq
  have hpath := fun h hg ha => executePhaseR_onPathRH prims D D net [] rounds c.adversary _ world ω hω h hg ha j hj
  rw [hstep] at hpath
  obtain ⟨hjobs, hin₁⟩ := recCeremony_start prims K circuits settings _ j c kj hkj _ (hpath _ hg₁ ha₁).done k b hb'
  obtain ⟨-, hin₂⟩ := recCeremony_start prims K circuits settings _ j c kj hkj _ (hpath _ hg₂ ha₂).done k b hb'
  have hbjobs : b.jobs = js := by
    rw [List.getElem?_eq_getElem hk, hkjs] at hjobs
    exact (Option.some.inj hjobs).symm
  have heq := hin₁.symm.trans hin₂
  unfold batchInputs at heq
  have hjobeq := List.map_inj_left.1 heq job (hbjobs ▸ hjob)
  have hTeq := congrFun hjobeq T
  simp only [hjT, ↓reduceIte] at hTeq
  unfold inputBits at hTeq
  have hxeq := flatMap_blocks_eq digestBits _ _ (fun _ => length_bitsOfDigest _) (fun _ => length_bitsOfDigest _)
    job.points hTeq x hx
  have hd := bitsOfDigest_injective hxeq
  rw [hseed, Function.update_self] at hd
  exact hv hd.symm

end Main

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyCells_of_started' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyCells_of_started
