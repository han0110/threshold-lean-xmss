import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.MonitorReplay
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.BatchRecords
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningDigests
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.SharesAgree
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Statements

/-!
# The records of one ceremony

`GhostOnPath` states that each last honest step of a ghost phase is on the path of its recorded
program with `H` fixed to each good `h` that agrees with the end hash cache. The ghost run of one
ceremony from the clean world (`ghostCeremony_clean`) has an end cache with no cell of the MPC, so
`hashOf` of that cache is such an `h`. `recCeremony_support` and `recCeremony_fix_support` give the
record of `recCeremony` as the record of `recRun`.

* `termDraws_agree` states that two holders of a term that draw under one key at one label get the
  same bits.
* `ceremony_delivery` gives the message of `OpenRep` of each honest operator in the mail of the
  opening of another honest operator.
* `ceremonyMonitor_of`, `ceremonySync` and `ceremonyBatch_of` are the leaves `CeremonyMonitor`,
  `CeremonySync` and `CeremonyBatch`. `ceremonyBatchFor` is the part of `ceremonyBatch_of` for each
  good `h` that agrees with the clean end cache, with `seedsDiffer = false` in the place of
  `CeremonyReady`.
* `ceremonyOutputsAgree_of_parts` gives `CeremonyOutputsAgree` from the ghost path, the start of each
  check, the term keys, the draws of `Rerand` and the digest round.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CeremonyRecords

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The path with `H` fixed -/

section Path

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The ghost path with `H` fixed. Each last honest step of a phase of the ghost executor in
`streamWorld` is on the path of its recorded program with `H` fixed to each good `h` that agrees with
the end hash cache. -/
def GhostOnPath : Prop :=
  ∀ (Dw D' : C.Coalition) {Ia : Type} (A : Adversary C E Ia PEmpty PEmpty) {α ρ : Type} (blank : ρ) (fuel : ℕ)
    (st : A.State) (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (s : HashCache C × HiddenCache C)
    (z : (A.State × (C.Party → RStep C E RealSpec α ρ)) × (HashCache C × HiddenCache C)),
    z ∈ support ((simulateQ (streamWorld prims Dw)
      (executePhaseR worldRoles D' A noFunctionality blank fuel st program)).run s) →
    ∀ h, Good prims h → Agrees h z.2.1 → ∀ i, i ∉ D'.1 →
      OnPath h (some <$> program i) (GhostBatch.toStep (z.1.2 i))

variable {prims}

/-- A done ghost step on the path of its program with `H` fixed to `h` has its output and its record
in the support of the program with `H` fixed to `h`. -/
theorem onPath_done {ι : Type} {G : OracleSpec ι} {α ρ : Type} {h : Query C → HashOutput}
    {program : OracleComp (PartySpec C E G) (Option α × ρ)} {out : Option α} {record : ρ}
    (hpath : OnPath h (some <$> program) (GhostBatch.toStep (.done out record))) :
    (out, record) ∈ support (simulateQ (fixHash h) program) := by
  have hmem := hpath (out, record) (by simp [GhostBatch.toStep, stepProgram])
  rw [simulateQ_map, support_map] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  cases hpe
  exact hp

variable (prims)

/-- `hashOf` reads no cell of the MPC, so it is the same on the clean cache. -/
theorem hashOf_cleanCache (c : HashCache C) : hashOf prims (MpcCells.cleanCache c) = hashOf prims c := by
  funext q
  have hne : ∀ q : Query C, (∀ x, q = .hash x → ¬ MpcInput x) → MpcCells.cleanCache c q = c q :=
    fun q hq => MpcCells.cleanCache_of_not fun ⟨x, hx, hm⟩ => hq x hx hm
  cases q with
  | hash x =>
    by_cases hx : MpcInput x
    · simp [hashOf, hx]
    · simp only [hashOf, hx, ↓reduceIte]
      rw [hne _ fun y hy => by cases hy; exact hx]
  | _ => simp only [hashOf]; rw [hne _ fun y hy => by cases hy]

end Path


/-! ## The draws of the PRSS terms -/

section Draws

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The draws of `count` bits of each held term at operator `self`, at the label `ρ` and the index
`idx`, under the term keys `keyOf`. It is the first part of `prssRandomness` with the bit codec, which
`Rerand` and the reshares of the AND layers call. -/
def termDraws (self : C.Party) (keyOf : C.Term → HashOutput) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (List (ℕ → Bit)) :=
  C.terms.mapM fun T => if self ∈ C.holders T then prgBits (.term T) (keyOf T) ρ idx count else pure fun _ => 0

/-- A free run of the draws of the terms of a list in `streamWorld` grows the world, and the draw of
each held term is a free draw of its stream below the end world. -/
theorem streamWorld_free_draws (self : C.Party) (keyOf : C.Term → HashOutput) (ρ idx count : ℕ) :
    ∀ (terms : List C.Term) (s : HashCache C × HiddenCache C),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (terms.mapM fun T =>
          if self ∈ C.holders T then prgBits (.term T) (keyOf T) ρ idx count else pure fun _ => 0)
            (LocalSpec C)))).run s),
        s ≤ z.2 ∧ ∀ (m : ℕ) T, terms[m]? = some T → self ∈ C.holders T →
          KnownTupleInputs.Drawn prims D (.term T) (keyOf T) ρ idx count z.2 (z.1.getD m fun _ => 0)
  | [], s, z, hz => by
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun m T h => by simp at h⟩
  | T :: terms, s, z, hz => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨hle₂, hdraws⟩ := streamWorld_free_draws self keyOf ρ idx count terms a.2 b hb
    have hle₁ : s ≤ a.2 := streamWorld_le prims D _ s a ha
    refine ⟨hle₁.trans hle₂, fun m T' hm hT' => ?_⟩
    rcases m with _ | m
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      simp only [hT', ↓reduceIte] at ha
      exact ⟨s, a, ha, (Prod.mk_le_mk.1 hle₂).1, (Prod.mk_le_mk.1 hle₂).2, fun g _ => rfl⟩
    · exact hdraws m T' hm hT'

/-- The rerand draws agree. Two operators that hold a term `T`, draw under one key of `T` at one label
and one index, and end below one world `w` get the same bits of `T` below the count. -/
theorem termDraws_agree {self self' : C.Party} {keyOf keyOf' : C.Term → HashOutput} {ρ idx count : ℕ}
    {s s' : HashCache C × HiddenCache C} {z z' : List (ℕ → Bit) × (HashCache C × HiddenCache C)}
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (termDraws self keyOf ρ idx count)
      (LocalSpec C)))).run s))
    (hz' : z' ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (termDraws self' keyOf' ρ idx count)
      (LocalSpec C)))).run s'))
    {w : HashCache C × HiddenCache C} (hw : z.2 ≤ w) (hw' : z'.2 ≤ w) {T : C.Term} (hT : self ∈ C.holders T)
    (hT' : self' ∈ C.holders T) (hkey : keyOf T = keyOf' T) :
    ∀ g < count, z.1.getD (C.terms.idxOf T) (fun _ => 0) g = z'.1.getD (C.terms.idxOf T) (fun _ => 0) g := by
  have hidx : C.terms[C.terms.idxOf T]? = some T := List.getElem?_idxOf (mem_terms T)
  have mono : ∀ {key : HashOutput} {w₁ : HashCache C × HiddenCache C} {r : ℕ → Bit}, w₁ ≤ w →
      KnownTupleInputs.Drawn prims D (.term T) key ρ idx count w₁ r →
        KnownTupleInputs.Drawn prims D (.term T) key ρ idx count w r := by
    rintro key w₁ r hle ⟨s₀, z₀, h₀, h1, h2, hr⟩
    exact ⟨s₀, z₀, h₀, h1.trans (Prod.mk_le_mk.1 hle).1, h2.trans (Prod.mk_le_mk.1 hle).2, hr⟩
  have hd := mono hw ((streamWorld_free_draws prims D self keyOf ρ idx count C.terms s z hz).2 _ T hidx hT)
  have hd' := mono hw' ((streamWorld_free_draws prims D self' keyOf' ρ idx count C.terms s' z' hz').2 _ T hidx hT')
  rw [← hkey] at hd'
  exact KnownTupleInputs.drawn_agree prims D hd hd'

end Draws

/-! ## The blocks of a record -/

section Blocks

variable {C : Committee} {E : Type}

theorem startsOf_blocks (bs : List (BatchStart C × Mail C E × List (List Bit))) :
    startsOf (bs.flatMap GhostBatch.blockOf) = bs.map (·.1) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    rw [List.flatMap_cons, GhostMonitor.startsOf_append, ih]
    rfl

theorem openingsOf_blocks (bs : List (BatchStart C × Mail C E × List (List Bit))) :
    openingsOf (bs.flatMap GhostBatch.blockOf) = bs.map fun x => (x.1.v', x.2.1) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    rw [List.flatMap_cons, RecordedOpening.openingsOf_append, ih]
    rfl

theorem batchOutputsOf_blocks (bs : List (BatchStart C × Mail C E × List (List Bit))) :
    batchOutputsOf (bs.flatMap GhostBatch.blockOf) = bs.map (·.2.2) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    rw [List.flatMap_cons, GhostMonitor.batchOutputsOf_append, ih]
    rfl

/-- The facts of an outcome of a recorded program with full batches and a cut batch. Each start has
`S`, each batch output is the output of a full batch with `P` whose start and opening have the same
index, and a result has as many openings as starts. -/
theorem outcome_facts {β : Type} {S : BatchStart C → Prop} {P : BatchStart C × Mail C E × List (List Bit) → Prop}
    (hPS : ∀ x, P x → S x.1) {z : Option β × Record C E} (hz : GhostBatch.OutcomeOk S P z) :
    (∀ (m : ℕ) b, (startsOf z.2)[m]? = some b → S b) ∧
      (∀ (m : ℕ) out, (batchOutputsOf z.2)[m]? = some out → ∃ x, P x ∧ (startsOf z.2)[m]? = some x.1 ∧
        (openingsOf z.2)[m]? = some (x.1.v', x.2.1) ∧ x.2.2 = out) ∧
      (z.1.isSome → (openingsOf z.2).length = (startsOf z.2).length) := by
  obtain ⟨bs, tail, hbs, hrec, hout, hS, hfull⟩ : ∃ (bs : List (BatchStart C × Mail C E × List (List Bit)))
      (tail : Record C E), (∀ x ∈ bs, P x) ∧ z.2 = bs.flatMap GhostBatch.blockOf ++ tail ∧
      batchOutputsOf tail = [] ∧ (∀ b ∈ startsOf tail, S b) ∧ (z.1.isSome → tail = []) := by
    rcases hz with ⟨bs, hbs, hrec⟩ | ⟨hnone, bs, tail, hbs, hrec, htail⟩
    · exact ⟨bs, [], hbs, by simp [hrec], rfl, by simp [startsOf], fun _ => rfl⟩
    · refine ⟨bs, tail, hbs, hrec, ?_, ?_, fun h => by simp [hnone] at h⟩
      · rcases htail with rfl | ⟨b, -, rfl | ⟨inbox, rfl⟩⟩ <;> rfl
      · rcases htail with rfl | ⟨b, hb, rfl | ⟨inbox, rfl⟩⟩
        · simp [startsOf]
        · simpa [startsOf] using hb
        · simpa [startsOf] using hb
  rw [hrec, GhostMonitor.startsOf_append, RecordedOpening.openingsOf_append, GhostMonitor.batchOutputsOf_append,
    startsOf_blocks, openingsOf_blocks, batchOutputsOf_blocks, hout, List.append_nil]
  refine ⟨fun m b hb => ?_, fun m out ho => ?_, fun hsome => ?_⟩
  · rcases Nat.lt_or_ge m bs.length with hm | hm
    · rw [List.getElem?_append_left (by simpa using hm)] at hb
      simp only [List.getElem?_map, List.getElem?_eq_getElem hm, Option.map_some, Option.some.injEq] at hb
      exact hb ▸ hPS _ (hbs _ (List.getElem_mem hm))
    · rw [List.getElem?_append_right (by simpa using hm)] at hb
      exact hS b (List.mem_of_getElem? hb)
  · have hm : m < bs.length := by simpa using (List.getElem?_eq_some_iff.1 ho).1
    simp only [List.getElem?_map, List.getElem?_eq_getElem hm, Option.map_some, Option.some.injEq] at ho
    refine ⟨bs[m], hbs _ (List.getElem_mem hm), ?_, ?_, ho⟩
    · rw [List.getElem?_append_left (by simpa using hm)]
      simp [List.getElem?_eq_getElem hm]
    · rw [List.getElem?_append_left (by simpa using hm)]
      simp [List.getElem?_eq_getElem hm]
  · rw [hfull hsome]
    simp [startsOf, openingsOf]

end Blocks

/-! ## The ghost run of one ceremony -/

section Ghost

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- An outcome of the ghost run of one ceremony gives an outcome from the clean world with the same
steps and the clean end world. -/
theorem ghostCeremony_clean (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) :
    (ω.1, MpcCells.cleanWorld ω.2) ∈
      support ((ghostCeremony prims K circuits settings D net rounds c).run (MpcCells.cleanWorld world)) := by
  unfold ghostCeremony at hω ⊢
  rw [MpcCells.streamWorld_run_clean, support_map]
  exact ⟨ω, hω, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- Each last honest step of the ghost run of one ceremony is on the path of `recCeremony` with `H`
fixed to each good `h` that agrees with the clean end hash cache. -/
theorem ceremony_onPath (hpath : GhostOnPath (C := C) (E := E) prims) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world))
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h (MpcCells.cleanCache ω.2.1)) (i : C.Party)
    (hi : i ∉ D.1) :
    OnPath h (some <$> (recCeremony K circuits settings i c).run.run) (GhostBatch.toStep (ω.1.2 i)) := by
  have hclean := ghostCeremony_clean prims K circuits settings D net rounds c world ω hω
  unfold ghostCeremony at hclean
  exact hpath D D net ([] : Record C E) rounds c.adversary (fun i => (recCeremony K circuits settings i c).run.run)
    _ _ hclean h hg ha i hi

omit [Fintype E] [DecidableEq E] in
/-- The outcomes of `recCeremony` with `H` fixed. A dead operator aborts with the empty record. Each
other outcome has the record of an outcome of `recRun`, and a result is the result of that outcome. -/
theorem recCeremony_fix_support (h : Query C → HashOutput) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (z : Option CeremonyResult × Record C E)
    (hz : z ∈ support (simulateQ (fixHash h) (recCeremony K circuits settings i c).run.run)) :
    z = (none, []) ∨ ∃ keys, c.keys i = some keys ∧
      ∃ z₁ ∈ support (simulateQ (fixHash h) ((recRun K circuits settings i keys c.jobs).run c.counters).run.run),
        z.2 = z₁.2 ∧ ∀ o, z.1 = some o → z₁.1 = some (some o.1, o.2) := by
  unfold recCeremony at hz
  split at hz
  · rename_i keys hk
    right
    refine ⟨keys, hk, ?_⟩
    obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := GhostMonitor.mem_support_fix_bind h _ _ z hz
    · exact ⟨z₁, h₁, rfl, fun o ho => by cases ho⟩
    · refine ⟨z₁, h₁, ?_⟩
      rcases a with ⟨_ | outputs, st⟩
      · simp at h₂
        subst h₂
        exact ⟨by simp, fun o ho => by cases ho⟩
      · simp at h₂
        subst h₂
        refine ⟨by simp, fun o ho => ?_⟩
        simp only [Option.some.injEq] at ho
        subst ho
        exact ha
  · left
    simpa using hz

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The record of a done ghost step. -/
theorem step_done {steps : CeremonySteps C E} {i : C.Party} {o : CeremonyResult}
    (ho : (steps i).output = some o) : steps i = .done (some o) (ceremonyRecord steps i) := by
  unfold ceremonyRecord
  rcases hs : steps i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at ho
  · cases ho
    rfl
  · cases ho
  · cases ho

/-! ## The monitor -/

omit [Fintype E] [DecidableEq E] in
/-- `CeremonyMonitor` from the ghost path. The outcome of `recRun` of an honest operator with wrong
opened outputs has a batch that is not right for `hashOf` of the end cache, by `condR_recRun`. That
batch is a wrong batch. -/
theorem ceremonyMonitor_of (hpath : GhostOnPath (C := C) (E := E) prims) :
    CeremonyMonitor prims K circuits settings := by
  intro hsize D net rounds ℓ c world hready ω hω ⟨i, hi, o, ho, hwrong⟩ _
  by_contra hnot
  push Not at hnot
  have hmem := onPath_done ((step_done ho) ▸ ceremony_onPath prims K circuits settings hpath D net rounds c world ω hω
    _ (good_hashOf prims _) (agrees_hashOf prims (MpcCells.noMpc_cleanCache _)) i hi)
  rw [hashOf_cleanCache] at hmem
  rcases recCeremony_fix_support K circuits settings _ i c _ hmem with h | ⟨keys, hk, z₁, h₁, hrec, hres⟩
  · simp at h
  have hcount := (BatchCounters.counted_recRun K circuits settings i keys c.jobs c.counters z₁
    (GhostMonitor.support_fixHash_subset _ _ h₁)).1
  have hpar : keys.parameter = gameParameter D c.keys :=
    parameter_eq_gameParameter D c.keys hready.1 i hi keys hk
  have hcond := GhostMonitor.condR_recRun K circuits settings prims (hashOf prims ω.2.1) (gameSeeds D c.keys) hsize
    i keys c.jobs c.counters z₁ h₁ (some o.1) o.2 (hres o rfl)
  refine hwrong ?_
  rw [← hpar]
  refine (hcond fun k hk b out hb hout => ?_).2
  by_contra hnr
  refine hnot k hk ⟨i, hi, by rw [ho]; rfl, b, out, by rw [show ceremonyRecord ω.1.2 i = z₁.2 from hrec]; exact hb,
    by rw [show ceremonyRecord ω.1.2 i = z₁.2 from hrec]; exact hout, fun heq => hnr ?_⟩
  have hshape := (BatchCounters.placed_getElem _ _ _ hcount k b hb).1
  unfold GhostMonitor.RightAt RightBatch
  rw [heq, evalRun_eq, hshape.2.1, hpar]

omit [Fintype E] [DecidableEq E] in
/-- The record of an honest operator that is not empty in the ghost run of one ceremony is the record
of an outcome of `recRun` with its keys, with `H` fixed to each good `h` that agrees with the clean
end hash cache, and a result is the result of that outcome. -/
theorem ceremony_fix_record (hpath : GhostOnPath (C := C) (E := E) prims) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world))
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h (MpcCells.cleanCache ω.2.1)) (i : C.Party)
    (hi : i ∉ D.1) (hne : ceremonyRecord ω.1.2 i ≠ []) :
    ∃ keys, c.keys i = some keys ∧
      ∃ z₁ ∈ support (simulateQ (fixHash h) ((recRun K circuits settings i keys c.jobs).run c.counters).run.run),
        ceremonyRecord ω.1.2 i = z₁.2 ∧ ∀ o, (ω.1.2 i).output = some o → z₁.1 = some (some o.1, o.2) := by
  have hpath := ceremony_onPath prims K circuits settings hpath D net rounds c world ω hω h hg ha i hi
  unfold ceremonyRecord at hne ⊢
  rcases hs : ω.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hne hpath
  · rcases recCeremony_fix_support K circuits settings h i c _ (onPath_done hpath) with hz | ⟨keys, hk, z₁, h₁, hrec, hres⟩
    · simp only [Prod.mk.injEq] at hz
      exact absurd hz.2 hne
    · exact ⟨keys, hk, z₁, h₁, hrec, fun o ho => hres o ho⟩
  · exact absurd rfl hne
  · exact absurd rfl hne

/-! ## The opened outputs of a ceremony -/

omit [Fintype E] [DecidableEq E] in
/-- The values of the recorded batches of a list are their recorded batch outputs. -/
theorem recBatches_value (ctx : Context C) (parameter : PublicParameter) :
    ∀ (l : List (List Job)) (st : ℕ × ℕ) (z : Option (List (Option (List (List Bit))) × (ℕ × ℕ)) × Record C E),
      z ∈ support ((l.mapM (recBatch K circuits settings ctx parameter)).run st).run.run →
      ∀ vs st', z.1 = some (vs, st') → vs = (batchOutputsOf z.2).map some
  | [], st, z, hz, vs, st', h => by
    simp at hz
    subst hz
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | js :: l, st, z, hz, vs, st', h => by
    rw [List.mapM_cons, StateT.run_bind] at hz
    obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
    · cases h
    rw [StateT.run_bind] at h₂
    obtain ⟨z₃, h₃, ⟨-, rfl⟩ | ⟨b, hb, z₄, h₄, rfl⟩⟩ := mem_support_recM_bind _ _ z₂ h₂
    · cases h
    simp at h₄
    subst h₄
    obtain ⟨bs, -, -, inbox, out, hrec, hout⟩ :=
      GhostMonitor.recBatch_complete K circuits settings ctx parameter js st z₁ h₁ a.1 a.2 ha
    have hih := recBatches_value ctx parameter l a.2 z₃ h₃ b.1 b.2 hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, hrec, hout, hih, GhostMonitor.batchOutputsOf_append, GhostMonitor.batchOutputsOf_append]
    simp [batchOutputsOf]

omit [Fintype E] [DecidableEq E] in
/-- A result of `recRun` is the join of its recorded batch outputs. -/
theorem recRun_value (i : C.Party) (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ)
    (z : Option (Option (List (List Bit)) × (ℕ × ℕ)) × Record C E)
    (hz : z ∈ support ((recRun K circuits settings i keys jobs).run st).run.run) (a : Option (List (List Bit)))
    (st' : ℕ × ℕ) (ha : z.1 = some (a, st')) : a = some (batchOutputsOf z.2).flatten := by
  simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift] at hz
  rcases mem_support_lift_bind _ _ z hz with rfl | ⟨p, z₂, h₂, rfl⟩
  · cases ha
  simp only [batched, StateT.run_bind] at h₂
  obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨b, hb, z₃, h₃, rfl⟩⟩ := mem_support_recM_bind _ _ _ h₂
  · cases ha
  simp at h₃
  subst h₃
  have hv := recBatches_value K circuits settings _ _ _ _ z₁ h₁ b.1 b.2 hb
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  rw [← ha.1, hv, foldlM_some_append, List.nil_append, List.append_nil]

/-! ## The synchronization -/

omit [Fintype E] [DecidableEq E] in
/-- The outcomes of `recCeremony`. A dead operator aborts with the empty record. Each other outcome
has the record of an outcome of `recRun`. -/
theorem recCeremony_support (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (z : Option CeremonyResult × Record C E)
    (hz : z ∈ support (recCeremony K circuits settings i c).run.run) :
    z = (none, []) ∨ ∃ keys, c.keys i = some keys ∧
      ∃ z₁ ∈ support ((recRun K circuits settings i keys c.jobs).run c.counters).run.run, z.2 = z₁.2 ∧
        ∀ o, z.1 = some o → z₁.1 = some (some o.1, o.2) := by
  unfold recCeremony at hz
  split at hz
  · rename_i keys hk
    right
    refine ⟨keys, hk, ?_⟩
    obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
    · exact ⟨z₁, h₁, rfl, fun o ho => by cases ho⟩
    · refine ⟨z₁, h₁, ?_⟩
      rcases a with ⟨_ | outputs, st⟩
      · simp at h₂
        subst h₂
        exact ⟨by simp, fun o ho => by cases ho⟩
      · simp at h₂
        subst h₂
        refine ⟨by simp, fun o ho => ?_⟩
        simp only [Option.some.injEq] at ho
        subst ho
        exact ha
  · left
    simpa using hz

omit [Fintype E] [DecidableEq E] in
/-- The record of an honest operator with a start in the ghost run of one ceremony is the record of
an outcome of `recRun` with its keys. -/
theorem ceremony_record (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (hne : startsOf (ceremonyRecord ω.1.2 i) ≠ []) :
    ∃ keys, c.keys i = some keys ∧
      ∃ z₁ ∈ support ((recRun K circuits settings i keys c.jobs).run c.counters).run.run,
        ceremonyRecord ω.1.2 i = z₁.2 := by
  unfold ghostCeremony at hω
  have hpath := BatchCounters.executePhaseR_onPathR prims D D net ([] : Record C E) rounds c.adversary
    (fun i => (recCeremony K circuits settings i c).run.run) world ω hω i hi
  unfold ceremonyRecord at hne ⊢
  rcases hs : ω.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hne hpath
  · rcases recCeremony_support K circuits settings i c _ hpath.done with h | h
    · simp only [Prod.mk.injEq] at h
      exact absurd (by simp [RStep.record, h.2, startsOf]) hne
    · obtain ⟨keys, hk, z₁, h₁, hrec, -⟩ := h
      exact ⟨keys, hk, z₁, h₁, hrec⟩
  · simp [RStep.record, startsOf] at hne
  · simp [RStep.record, startsOf] at hne

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The public coordinates of the start `n` of `Placed` starts of the batches `J`, from the counters
`st`. -/
theorem start_public (i : C.Party) (keys : Keys C) (st : ℕ × ℕ) (ss : List (BatchStart C)) (J : List (List Job))
    (hp : BatchCounters.Placed (BatchCounters.Shape circuits settings i keys) st ss) (hj : ss.map (·.jobs) <+: J)
    (n : ℕ) (hn : n < ss.length) :
    ss[n]?.map (fun b => (b.mode, b.circuits, b.state.label, b.state.tag)) =
      J[n]?.map fun js => (settings.mode, js.map (circuits keys.parameter ·.kind),
        st.1 + ((J.take n).map fun js => batchLabel (js.map (circuits keys.parameter ·.kind))).sum +
          (headCounts (js.map (circuits keys.parameter ·.kind))).length, st.2 + n) := by
  have hjob : ∀ m (hm : m < ss.length), J[m]? = some ss[m].jobs := fun m hm =>
    BatchCounters.getElem?_of_prefix hj m _ (by simp [List.getElem?_eq_getElem hm])
  have hshape : ∀ m (hm : m < ss.length), BatchCounters.Shape circuits settings i keys ss[m] := fun m hm =>
    (BatchCounters.placed_getElem _ ss st hp m ss[m] (List.getElem?_eq_getElem hm)).1
  have htake : (ss.take n).map (batchLabel ·.circuits) =
      (J.take n).map fun js => batchLabel (js.map (circuits keys.parameter ·.kind)) := by
    refine List.ext_getElem? fun m => ?_
    simp only [List.getElem?_map, List.getElem?_take]
    split_ifs with hm
    · rw [List.getElem?_eq_getElem (by omega), hjob m (by omega), Option.map_some, Option.map_some,
        (hshape m (by omega)).2.2.1]
    · rfl
  obtain ⟨-, htag, hlabel⟩ := BatchCounters.placed_getElem _ ss st hp n ss[n] (List.getElem?_eq_getElem hn)
  rw [List.getElem?_eq_getElem hn, hjob n hn, Option.map_some, Option.map_some, hlabel, htag, htake,
    (hshape n hn).2.2.1, (hshape n hn).1]

omit [Fintype E] [DecidableEq E] in
/-- `CeremonySync`. Each honest operator with a start of check `k` places its starts at the public
counters of the job list, by `counted_recRun` and `jobsIn_recRun`, and the honest parameters agree. -/
theorem ceremonySync : CeremonySync prims K circuits settings := by
  intro D net rounds ℓ c world hready ω hω _ k _ hstarted i j hi hj k' hk'
  have hpublic : ∀ l, l ∉ D.1 →
      ((startsOf (ceremonyRecord ω.1.2 l))[k']?).map (fun b => (b.mode, b.circuits, b.state.label, b.state.tag)) =
        (chunks settings.batchSize c.jobs)[k']?.map fun js => (settings.mode,
          js.map (circuits (gameParameter D c.keys) ·.kind),
          c.counters.1 + (((chunks settings.batchSize c.jobs).take k').map fun js =>
            batchLabel (js.map (circuits (gameParameter D c.keys) ·.kind))).sum +
            (headCounts (js.map (circuits (gameParameter D c.keys) ·.kind))).length, c.counters.2 + k') := by
    intro l hl
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hstarted l hl)
    have hlen : k < (startsOf (ceremonyRecord ω.1.2 l)).length := (List.getElem?_eq_some_iff.1 hb).1
    obtain ⟨keys, hk, z₁, h₁, hrec⟩ := ceremony_record prims K circuits settings D net rounds c world ω hω l hl
      (List.ne_nil_of_length_pos (by omega))
    rw [hrec] at hlen ⊢
    rw [← parameter_eq_gameParameter D c.keys hready.1 l hl keys hk]
    exact start_public circuits settings l keys c.counters _ _
      (BatchCounters.counted_recRun K circuits settings l keys c.jobs c.counters z₁ h₁).1
      ((BatchCounters.jobsIn_recRun K circuits settings l keys c.jobs c.counters z₁ h₁).1) k' (by omega)
  rw [hpublic i hi, hpublic j hj]

omit [Fintype E] [DecidableEq E] in
/-- A start that an honest operator recorded in the ghost run of one ceremony is a start of the
batch of the job list at its index, with the public facts of its keys. -/
theorem ceremony_start (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (m : ℕ) (b : BatchStart C) (hb : (startsOf (ceremonyRecord ω.1.2 i))[m]? = some b) :
    ∃ keys, c.keys i = some keys ∧ (chunks settings.batchSize c.jobs)[m]? = some b.jobs ∧
      BatchCounters.Shape circuits settings i keys b := by
  have hne : startsOf (ceremonyRecord ω.1.2 i) ≠ [] := fun h => by simp [h] at hb
  obtain ⟨keys, hk, z₁, h₁, hrec⟩ := ceremony_record prims K circuits settings D net rounds c world ω hω i hi hne
  rw [hrec] at hb
  refine ⟨keys, hk, BatchCounters.getElem?_of_prefix
    (BatchCounters.jobsIn_recRun K circuits settings i keys c.jobs c.counters z₁ h₁).1 m _
    (by simp [List.getElem?_map, hb]), ?_⟩
  exact (BatchCounters.placed_getElem _ _ _
    (BatchCounters.counted_recRun K circuits settings i keys c.jobs c.counters z₁ h₁).1 m b hb).1

/-! ## The delivery of an opening -/

omit [Fintype E] [DecidableEq E] in
/-- `recCeremony` at operator `l` reaches its exchange of `OpenRep` of batch `k` at the depth of the
parameter `P` of its keys, with the copy hashes of the outbox in the history. A dead operator aborts
with the empty record. -/
theorem reachH_recCeremony (l : C.Party) {σ : Type} (c : CeremonyStart C σ) (P : PublicParameter)
    (hP : ∀ keys, c.keys l = some keys → keys.parameter = P) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length) :
    CachedOpening.ReachH (RecordedOpening.Stop k) (OpeningDigests.WaitAtH K l k)
      (setupRounds + ((((chunks settings.batchSize c.jobs).take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits P ·.kind))).sum +
        (CheckTiming.exactBatchRounds settings.mode
          (((chunks settings.batchSize c.jobs)[k]).map (circuits P ·.kind)) - 1))) []
      (recCeremony K circuits settings l c).run.run := by
  unfold recCeremony
  split
  · rename_i keys hkeys
    rw [← hP keys hkeys]
    refine OpeningDigests.reachH_recBind_left K _ ?_
    simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
    refine OpeningDigests.reachH_lift_bind (RecordedOpening.timed_pair (timed_prssSetup l) c.counters)
      ⟨rfl, by simp [openingsOf]⟩ (fun hist p => ?_) []
    simp only [batched, StateT.run_bind]
    exact OpeningDigests.reachH_recBind_left K _
      (OpeningDigests.reachH_recBatches K circuits settings ⟨l, keys, p.1⟩ keys.parameter _ k hk p.2 hist)
  · rw [RecordedOpening.run_recFailure]
    exact CachedOpening.ReachH.early _ _ _ ⟨rfl, by simp [openingsOf]⟩

omit [Fintype E] [DecidableEq E] in
/-- The delivery of the opening of batch `k`. When the honest operator `i` recorded the opening of
batch `k` with the mail `inbox`, the mail holds the message of `OpenRep` of each other honest
operator `j`, for the sharing of a start `b`, with copy hashes that the end hash cache holds. The
start `b` is the start of check `k` that `j` recorded, or `j` has the empty record. -/
theorem ceremony_delivery (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length) (i : C.Party) (hi : i ∉ D.1) (v : Shares C Bit)
    (inbox : Mail C E) (hopen : (openingsOf (ceremonyRecord ω.1.2 i))[k]? = some (v, inbox)) :
    ∀ j, j ∉ D.1 → j ≠ i → ∃ (b : BatchStart C) (digests : List HashOutput),
      inbox j = repOutbox K j b.v' (outputsOf b.circuits).length digests i ∧
      List.Forall₂ (fun T d => ω.2.1 (.copy (vector (outputsOf b.circuits).length (b.v' T))) = some d)
        C.terms digests ∧
      (ceremonyRecord ω.1.2 j = [] ∨ (startsOf (ceremonyRecord ω.1.2 j))[k]? = some b) := by
  unfold ghostCeremony at hω
  have hlen : k < (openingsOf (ceremonyRecord ω.1.2 i)).length := (List.getElem?_eq_some_iff.1 hopen).1
  have hne : ceremonyRecord ω.1.2 i ≠ [] := fun h => by simp [h, openingsOf] at hlen
  have hreach := fun l (hl : l ∉ D.1) => reachH_recCeremony K circuits settings l c (gameParameter D c.keys)
    (fun keys hkeys => parameter_eq_gameParameter D c.keys hseeds l hl keys hkeys) k hk
  rcases CachedOpening.executePhaseR_reachH prims D D net ([] : Record C E) (fun _ => RecordedOpening.Stop k)
    (fun l => OpeningDigests.WaitAtH K l k) _ rounds c.adversary _ hreach world ω hω with
    hstop | ⟨steps₀, sent, cache, hle, hsteps, hrest⟩
  · exfalso
    rcases hstop i hi with h | ⟨out, hout⟩
    · exact hne h
    · have := hout.2
      change (openingsOf (ceremonyRecord ω.1.2 i)).length ≤ k at this
      omega
  have hi' : ∃ out, (out, ceremonyRecord ω.1.2 i) ∈
      support (LiveRounds.nextR ([] : Record C E) (steps₀ i) (LiveRounds.roundInbox D steps₀ sent i)) := by
    rcases hrest i hi with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨out, hout⟩ := hi'
  have hsi := hsteps i hi
  have hinbox : inbox = LiveRounds.roundInbox D steps₀ sent i ∧ ∀ c, inbox c ≠ some .abort := by
    rcases hs : steps₀ i with ⟨out', r'⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hsi hout
    · simp only [LiveRounds.nextR, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
      have := hsi.2
      rw [← hout.2] at this
      change (openingsOf (ceremonyRecord ω.1.2 i)).length ≤ k at this
      omega
    · obtain ⟨hist, -, b, digests, -, -, hwait⟩ := hsi
      obtain ⟨-, -, h3⟩ := hwait _ _ hout
      obtain ⟨he, hab⟩ := h3 v inbox hopen
      exact ⟨he, he ▸ hab⟩
    · exact input.elim
  intro j hj hji
  have hinj : inbox j = (steps₀ j).delivered i := by
    rw [hinbox.1]
    simp [LiveRounds.roundInbox, hj]
  have hsj := hsteps j hj
  rcases hs : steps₀ j with ⟨out', r'⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hsj hinj
  · exfalso
    have h1 : out' = none := hsj.1
    subst h1
    exact hinbox.2 j hinj
  · obtain ⟨hist, hc, b, digests, hout', hfor, hwait⟩ := hsj
    refine ⟨b, digests, by rw [hinj, hout']; rfl, hfor.imp fun T d hd => hle (hc _ hd ?_), ?_⟩
    · rintro ⟨_, he, -⟩
      cases he
    · rcases hrest j hj with h | ⟨out'', hout''⟩
      · exact Or.inl h
      · rw [hs] at hout''
        exact Or.inr (hwait _ _ hout'').1
  · exact input.elim

/-! ## The blocks of the honest operators -/

/-- A start that an honest operator recorded has the shape of its keys with `H` fixed to each good
`h` that agrees with the clean end hash cache. -/
theorem ceremony_startShape (hpath : GhostOnPath (C := C) (E := E) prims) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (keys : Keys C) (hk : c.keys i = some keys) (m : ℕ) (b : BatchStart C)
    (hb : (startsOf (ceremonyRecord ω.1.2 i))[m]? = some b) (h : Query C → HashOutput) (hg : Good prims h)
    (ha : Agrees h (MpcCells.cleanCache ω.2.1)) :
    GhostBatch.StartShape circuits settings h i keys b := by
  have hne : ceremonyRecord ω.1.2 i ≠ [] := fun hnil => by simp [hnil, startsOf] at hb
  obtain ⟨keys', hk', z₁, h₁, hrec, -⟩ :=
    ceremony_fix_record prims K circuits settings hpath D net rounds c world ω hω h hg ha i hi hne
  obtain rfl : keys' = keys := Option.some.inj (hk'.symm.trans hk)
  rw [hrec] at hb
  exact (outcome_facts (fun x hx => hx.1) (GhostBatch.recOkS_recRun K circuits settings h prims i keys' c.jobs c.counters
    z₁ h₁)).1 m b hb

/-- A batch output that an honest operator with an output recorded is the output of a full block of
its start and its opening, with the block shape for each good `h` that agrees with the clean end hash
cache. -/
theorem ceremony_block (hpath : GhostOnPath (C := C) (E := E) prims) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (hout : (ω.1.2 i).output.isSome) (m : ℕ) (b : BatchStart C) (out : List (List Bit))
    (hb : (startsOf (ceremonyRecord ω.1.2 i))[m]? = some b)
    (ho : (batchOutputsOf (ceremonyRecord ω.1.2 i))[m]? = some out) :
    ∃ keys inbox, c.keys i = some keys ∧ (openingsOf (ceremonyRecord ω.1.2 i))[m]? = some (b.v', inbox) ∧
      (openingsOf (ceremonyRecord ω.1.2 i)).length = (startsOf (ceremonyRecord ω.1.2 i)).length ∧
      ∀ h, Good prims h → Agrees h (MpcCells.cleanCache ω.2.1) →
        GhostBatch.BlockShape K circuits settings h i keys (b, inbox, out) := by
  have hne : ceremonyRecord ω.1.2 i ≠ [] := fun hnil => by simp [hnil, startsOf] at hb
  obtain ⟨o, hio⟩ := Option.isSome_iff_exists.1 hout
  have hblock : ∀ h, Good prims h → Agrees h (MpcCells.cleanCache ω.2.1) → ∃ keys, c.keys i = some keys ∧
      (openingsOf (ceremonyRecord ω.1.2 i)).length = (startsOf (ceremonyRecord ω.1.2 i)).length ∧
      ∃ x : BatchStart C × Mail C E × List (List Bit), GhostBatch.BlockShape K circuits settings h i keys x ∧
        x.1 = b ∧ (openingsOf (ceremonyRecord ω.1.2 i))[m]? = some (b.v', x.2.1) ∧ x.2.2 = out := by
    intro h hg ha
    obtain ⟨keys, hk, z₁, h₁, hrec, hres⟩ :=
      ceremony_fix_record prims K circuits settings hpath D net rounds c world ω hω h hg ha i hi hne
    obtain ⟨-, hblocks, hfull⟩ := outcome_facts (fun x hx => hx.1)
      (GhostBatch.recOkS_recRun K circuits settings h prims i keys c.jobs c.counters z₁ h₁)
    rw [← hrec] at hblocks hfull
    obtain ⟨x, hx, hxs, hxo, hxout⟩ := hblocks m out ho
    rw [hb, Option.some.injEq] at hxs
    subst hxs
    exact ⟨keys, hk, hfull (by rw [hres o hio]; rfl), x, hx, rfl, hxo, hxout⟩
  obtain ⟨keys, hk, hlen, x, -, hx1, hxo, -⟩ := hblock _ (good_hashOf prims _)
    (agrees_hashOf prims (MpcCells.noMpc_cleanCache _))
  refine ⟨keys, x.2.1, hk, hxo, hlen, fun h hg ha => ?_⟩
  obtain ⟨keys', hk', -, y, hy, hy1, hyo, hyout⟩ := hblock h hg ha
  obtain rfl : keys' = keys := Option.some.inj (hk'.symm.trans hk)
  rw [hxo, Option.some.injEq, Prod.mk.injEq] at hyo
  have hy' : y = (b, x.2.1, out) := by
    obtain ⟨y1, y2, y3⟩ := y
    simp only at hy1 hyo hyout
    rw [hy1, hyo.2, hyout]
  rwa [← hy']

/-! ## The wrong batch -/

/-- The sharing after `Rerand` that operator `j` recorded at the start of check `k`, and zero when it
recorded no such start. -/
def startShares (steps : CeremonySteps C E) (k : ℕ) : C.Party → Shares C Bit := fun j =>
  (((startsOf (ceremonyRecord steps j))[k]?).map (·.v')).getD fun _ _ => 0

/-- The products of the AND layers that operator `j` recorded at the start of check `k`, and zero
when it recorded no such start. -/
def startProducts (steps : CeremonySteps C E) (k : ℕ) : C.Party → ℕ → Shares C Bit := fun j =>
  (((startsOf (ceremonyRecord steps j))[k]?).map (·.zs)).getD fun _ _ _ => 0

omit [Fintype E] [DecidableEq E] in
/-- The circuits of a start that an honest operator recorded are the circuits of the batch of the job
list at its index under the parameter of the game. -/
theorem ceremony_startCircuits (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (m : ℕ) (js : List Job) (hjs : (chunks settings.batchSize c.jobs)[m]? = some js) (b : BatchStart C)
    (hb : (startsOf (ceremonyRecord ω.1.2 i))[m]? = some b) :
    b.jobs = js ∧ b.circuits = js.map (circuits (gameParameter D c.keys) ·.kind) := by
  obtain ⟨keys, hk, hjobs, hshape⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω i hi m b hb
  obtain rfl : b.jobs = js := Option.some.inj (hjobs.symm.trans hjs)
  exact ⟨rfl, by rw [hshape.2.2.1, parameter_eq_gameParameter D c.keys hseeds i hi keys hk]⟩

omit [Fintype E] [DecidableEq E] in
/-- The delivery of the opening of batch `k` in the form of the recorded sharings. When each honest
operator recorded the start of check `k`, the mail of the opening of the honest operator `i` holds
the message of `OpenRep` of each other honest operator for its recorded sharing, with copy hashes that
the clean end hash cache holds. -/
theorem ceremony_deliveredShares (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length) (hst : StartedAt D k ω.1.2) (i : C.Party) (hi : i ∉ D.1)
    (v : Shares C Bit) (inbox : Mail C E) (hopen : (openingsOf (ceremonyRecord ω.1.2 i))[k]? = some (v, inbox)) :
    ∀ j, j ∉ D.1 → j ≠ i → ∃ digests, inbox j = repOutbox K j (startShares ω.1.2 k j)
      (outputsOf (((chunks settings.batchSize c.jobs)[k]).map (circuits (gameParameter D c.keys) ·.kind))).length
        digests i ∧
      List.Forall₂ (fun T d => MpcCells.cleanCache ω.2.1 (.copy (vector (outputsOf
        (((chunks settings.batchSize c.jobs)[k]).map (circuits (gameParameter D c.keys) ·.kind))).length
          (startShares ω.1.2 k j T))) = some d) C.terms digests := by
  intro j hj hji
  obtain ⟨bj, digests, hin, hcells, hrec⟩ :=
    ceremony_delivery prims K circuits settings D net rounds c world hseeds ω hω k hk i hi v inbox hopen j hj hji
  obtain ⟨bj', hbj'⟩ := Option.isSome_iff_exists.1 (hst j hj)
  have hbj : (startsOf (ceremonyRecord ω.1.2 j))[k]? = some bj := by
    rcases hrec with hnil | h
    · simp [hnil, startsOf] at hbj'
    · exact h
  have hcj := (ceremony_startCircuits prims K circuits settings D net rounds c world hseeds ω hω j hj k _
    (List.getElem?_eq_getElem hk) bj hbj).2
  have hvj : startShares ω.1.2 k j = bj.v' := by simp [startShares, hbj]
  rw [hvj]
  rw [hcj] at hin hcells
  refine ⟨digests, hin, hcells.imp fun T d hd => ?_⟩
  rw [MpcCells.cleanCache_of_not (by rintro ⟨_, he, -⟩; cases he)]
  exact hd

/-- A recorded batch `k` of an honest operator with a result, whose output is not right for a good
`h` that agrees with the clean end cache, gives a wrong tuple or split copies at check `k` when each
honest operator recorded its start. -/
theorem ceremonyBatchFor (hpath : GhostOnPath (C := C) (E := E) prims) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (hglobal : ¬ GlobalEvent ω.2)
    (k : ℕ) (hk : k < (chunks settings.batchSize c.jobs).length) (i : C.Party) (hi : i ∉ D.1)
    (hiout : (ω.1.2 i).output.isSome) (b : BatchStart C) (out : List (List Bit))
    (hb : (startsOf (ceremonyRecord ω.1.2 i))[k]? = some b) (hout : (batchOutputsOf (ceremonyRecord ω.1.2 i))[k]? = some out)
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h (MpcCells.cleanCache ω.2.1))
    (hwrong : ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D c.keys) b out) (hst : StartedAt D k ω.1.2) :
    WrongTuple D (ceremonyTuplesAt K k ω.1.2) ∨ ¬ MultVerifyAgree D (honestTuples D (ceremonyTuplesAt K k ω.1.2)) := by
  obtain ⟨keys_i, inbox, hki, hopen, hlen, hblock⟩ :=
    ceremony_block prims K circuits settings hpath D net rounds c world ω hω i hi hiout k b out hb hout
  by_contra hgood
  rw [not_or, not_not] at hgood
  obtain ⟨hright, hmv⟩ := hgood
  apply hwrong
  obtain ⟨keys_i', hki', hjobs_i, hshape_i⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω i hi k b hb
  obtain rfl : keys_i = keys_i' := Option.some.inj (hki.symm.trans hki')
  have hpar_i := parameter_eq_gameParameter D c.keys hseeds i hi keys_i hki
  -- the starts of the honest operators
  have hstarts : ∀ l, l ∉ D.1 → ∃ bl, (startsOf (ceremonyRecord ω.1.2 l))[k]? = some bl ∧
      bl.jobs = b.jobs ∧ (l ∉ D.1 → c.keys l = some ((c.keys l).getD noKeys)) ∧
      ((c.keys l).getD noKeys).parameter = gameParameter D c.keys ∧
      ∀ h, Good prims h → Agrees h (MpcCells.cleanCache ω.2.1) →
        GhostBatch.StartShape circuits settings h l ((c.keys l).getD noKeys) bl := by
    intro l hl
    obtain ⟨bl, hbl⟩ := Option.isSome_iff_exists.1 (hst l hl)
    obtain ⟨keys, hk, hjobs, -⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω l hl k bl hbl
    refine ⟨bl, hbl, Option.some.inj (hjobs.symm.trans hjobs_i), fun _ => by simp [hk], ?_, fun h hg ha => ?_⟩
    · simp only [hk, Option.getD_some]
      exact parameter_eq_gameParameter D c.keys hseeds l hl keys hk
    · simp only [hk, Option.getD_some]
      exact ceremony_startShape prims K circuits settings hpath D net rounds c world ω hω l hl keys hk k bl hbl h hg ha
  have hcirc : b.circuits = b.jobs.map (circuits (gameParameter D c.keys) ·.kind) := by
    rw [hshape_i.2.2.1, hpar_i]
  -- the tuples, the products and the sharings of the honest operators
  have hv : ∀ l, l ∉ D.1 → ∀ bl, (startsOf (ceremonyRecord ω.1.2 l))[k]? = some bl →
      startShares ω.1.2 k l = bl.v' ∧ startProducts ω.1.2 k l = bl.zs ∧
        ceremonyTuplesAt K k ω.1.2 l = batchTuples K bl.mode bl.circuits bl.inputs bl.zs bl.v' := by
    intro l _ bl hbl
    simp [startShares, startProducts, ceremonyTuplesAt, hbl]
  have hshapeX : ∀ l, l ∉ D.1 → ceremonyTuplesAt K k ω.1.2 l =
      batchTuples K settings.mode (b.jobs.map (circuits ((c.keys l).getD noKeys).parameter ·.kind))
        (batchInputs h ((c.keys l).getD noKeys).seed b.jobs l)
        (startProducts ω.1.2 k l) (startShares ω.1.2 k l) := by
    intro l hl
    obtain ⟨bl, hbl, hjobs, -, -, hshape⟩ := hstarts l hl
    obtain ⟨hv', hz', hx'⟩ := hv l hl bl hbl
    obtain ⟨-, hmode, -, hcircl, hinputs⟩ := hshape _ hg ha
    rw [hx', hv', hz', hmode, hcircl, hinputs, hjobs]
  have hagree := shares_agree_of_multVerifyAgree K settings.mode (b.jobs.map (circuits (gameParameter D c.keys) ·.kind))
    D (fun l => batchInputs (h) ((c.keys l).getD noKeys).seed b.jobs l)
    (startProducts ω.1.2 k) (startShares ω.1.2 k) (ceremonyTuplesAt K k ω.1.2)
    (fun l hl => by obtain ⟨-, -, -, -, hp, -⟩ := hstarts l hl; rw [hshapeX l hl, hp]) hmv
  set count := (outputsOf (b.jobs.map (circuits (gameParameter D c.keys) ·.kind))).length with hcount
  -- the delivery of the opening
  have hdeliver : ∀ j, j ∉ D.1 → j ≠ i → ∃ digests, inbox j = repOutbox K j (startShares ω.1.2 k j) count digests i ∧
      List.Forall₂ (fun T d => MpcCells.cleanCache ω.2.1 (.copy (vector count (startShares ω.1.2 k j T))) = some d)
        C.terms digests := by
    have hjs : (chunks settings.batchSize c.jobs)[k] = b.jobs :=
      Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hjobs_i)
    have h := ceremony_deliveredShares prims K circuits settings D net rounds c world hseeds ω hω k hk hst i hi _ _
      hopen
    rwa [hjs] at h
  have hvi : startShares ω.1.2 k i = b.v' := (hv i hi b hb).1
  have hchecks : ∀ h', Good prims h' → Agrees h' (MpcCells.cleanCache ω.2.1) →
      repCheck K i inbox (copyHashes h' (repCopy K i (startShares ω.1.2 k i) count inbox) count) := by
    intro h' hg' ha'
    have := (hblock h' hg' ha').2.1
    simp only at this
    rwa [hcirc, ← hvi] at this
  have hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < count →
      startShares ω.1.2 k j T g = startShares ω.1.2 k (refHolder D T) T g :=
    fun j T g hj hjT hg' => hagree T j (refHolder D T) hj (refHolder_spec D T).2 hjT (refHolder_spec D T).1 g hg'
  have hcoll : ¬ DomainCollision CopyDomain (MpcCells.cleanCache ω.2.1) := fun hc =>
    hglobal (Or.inr (Or.inr (Or.inl ((MpcCells.domainCollision_cleanCache (fun _ h => h) _).1 hc))))
  have hcopy := OpenedAgreement.copySound_of_cache K prims D (MpcCells.cleanCache ω.2.1) _ hg ha
    (fun T => startShares ω.1.2 k (refHolder D T) T) (startShares ω.1.2 k) count hvr i hi inbox hchecks hdeliver hcoll
  have hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (startShares ω.1.2 k j) count
      (copyHashes h (startShares ω.1.2 k j) count) i := by
    intro j hj hji
    obtain ⟨digests, hin, hcells⟩ := hdeliver j hj hji
    exact OpenedAgreement.inbox_of_cached K _ _ ha j i _ count _ digests hin hcells
  have hright' := opened_right prims K settings.mode circuits (gameParameter D c.keys) b.jobs D i hi
    h (gameSeeds D c.keys) (fun l => (c.keys l).getD noKeys)
    (startProducts ω.1.2 k) (startShares ω.1.2 k) (ceremonyTuplesAt K k ω.1.2) inbox hshapeX
    (fun l hl => by obtain ⟨-, -, -, -, hp, -⟩ := hstarts l hl; exact hp)
    (fun l T hl hlT => by
      obtain ⟨-, -, -, hk', -, -⟩ := hstarts l hl
      have hk'' := hk' hl
      rw [hk'']
      exact seed_eq_gameSeeds D c.keys hseeds l hl _ hk'' T hlT)
    hright hagree hinbox (hchecks _ hg ha) hcopy
  have hout' := (hblock _ hg ha).2.2
  simp only at hout'
  unfold GhostMonitor.RightAt RightBatch
  rw [hout', hshape_i.2.1, hpar_i, ← hright', hcirc, hvi]

/-- `CeremonyBatch` from the ghost path. Take a wrong recorded batch `k` of an honest operator `i`
with an output, when each honest operator recorded the start of check `k`. Then `i` passed the
opening of batch `k`, and `ceremonyBatchFor` at `hashOf` of the clean end cache gives a bad check. -/
theorem ceremonyBatch_of (hpath : GhostOnPath (C := C) (E := E) prims) : CeremonyBatch prims K circuits settings := by
  intro D net rounds ℓ c world hready ω hω hglobal k hk ⟨i, hi, hiout, b, out, hb, hout, hwrong⟩
  by_cases hst : StartedAt D k ω.1.2
  swap
  · exact Or.inr hst
  left
  have hg : Good prims (hashOf prims (MpcCells.cleanCache ω.2.1)) := good_hashOf prims _
  have ha : Agrees (hashOf prims (MpcCells.cleanCache ω.2.1)) (MpcCells.cleanCache ω.2.1) :=
    agrees_hashOf prims (MpcCells.noMpc_cleanCache _)
  obtain ⟨-, -, -, -, hlen, -⟩ :=
    ceremony_block prims K circuits settings hpath D net rounds c world ω hω i hi hiout k b out hb hout
  refine ⟨hst, ceremonyBatchFor prims K circuits settings hpath D net rounds c world hready.1 ω hω hglobal k hk i hi
    hiout b out hb hout _ hg ha (fun hright => hwrong ?_) hst, i, hi,
    by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hb).1⟩
  obtain ⟨keys_i, hki, -, hshape_i⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω i hi k b hb
  unfold GhostMonitor.RightAt RightBatch at hright
  rw [hright, evalRun_eq, ← hashOf_cleanCache prims ω.2.1, hshape_i.2.1,
    parameter_eq_gameParameter D c.keys hready.1 i hi keys_i hki]

/-! ## The agreement of the opened outputs -/

omit [Fintype E] [DecidableEq E] in
/-- The result of an honest operator in the ghost run of one ceremony is the join of its recorded
batch outputs, and its record has one start and one batch output for each batch of the job list. -/
theorem ceremony_value (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (o : CeremonyResult) (ho : (ω.1.2 i).output = some o) :
    o.1 = (batchOutputsOf (ceremonyRecord ω.1.2 i)).flatten ∧
      (startsOf (ceremonyRecord ω.1.2 i)).length = (chunks settings.batchSize c.jobs).length ∧
      (batchOutputsOf (ceremonyRecord ω.1.2 i)).length = (chunks settings.batchSize c.jobs).length := by
  unfold ghostCeremony at hω
  have hpath := BatchCounters.executePhaseR_onPathR prims D D net ([] : Record C E) rounds c.adversary
    (fun i => (recCeremony K circuits settings i c).run.run) world ω hω i hi
  rw [step_done ho] at hpath
  rcases recCeremony_support K circuits settings i c _ hpath.done with h | ⟨keys, hk, z₁, h₁, hrec, hres⟩
  · simp at h
  have hz := hres o rfl
  have hv := recRun_value K circuits settings i keys c.jobs c.counters z₁ h₁ _ _ hz
  have hjobs := (BatchCounters.jobsIn_recRun K circuits settings i keys c.jobs c.counters z₁ h₁).2 (by rw [hz]; rfl)
  have hbal := GhostMonitor.balR_recRun K circuits settings i keys c.jobs c.counters z₁ h₁ _ _ hz
  have hs : (startsOf z₁.2).length = (chunks settings.batchSize c.jobs).length := by
    rw [← hjobs, List.length_map]
  have hrec' : ceremonyRecord ω.1.2 i = z₁.2 := hrec
  refine ⟨by rw [Option.some.inj hv, hrec'], by rw [hrec', hs], by rw [hrec', ← hbal, hs]⟩

/-- The agreement of the recorded sharings of one ceremony. With no global event at the end of one
ceremony from a ready start, when an honest operator has a result, each honest operator recorded the
start of each check, and two honest holders of a term recorded the same sharing after `Rerand` at that
term below the output count of the batch. -/
def CeremonyPassedShares : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ¬ GlobalEvent ω.2 →
      ∀ i, i ∉ D.1 → (ω.1.2 i).output.isSome → ∀ k (hk : k < (chunks settings.batchSize c.jobs).length),
        StartedAt D k ω.1.2 ∧ ∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
          ∀ g < (outputsOf (((chunks settings.batchSize c.jobs)[k]).map
            (circuits (gameParameter D c.keys) ·.kind))).length,
            startShares ω.1.2 k j T g = startShares ω.1.2 k j' T g

/-- `CeremonyOutputsAgree` from the ghost path and the agreement of the recorded sharings. The result
of each honest operator is the join of its batch outputs. Two honest operators with a result have
equal batch outputs at each batch by `blockOutputs_agree_of_cache`, with the delivery of the opening. -/
theorem ceremonyOutputsAgree_of (hpath : GhostOnPath (C := C) (E := E) prims)
    (hshares : CeremonyPassedShares prims K circuits settings) : CeremonyOutputsAgree prims K circuits settings := by
  intro D net rounds ℓ c world hready r hr hglobal i j oi oj hi hj hoi hoj
  rw [ghostCeremony_erase, support_map] at hr
  obtain ⟨ω, hω, rfl⟩ := hr
  change (ω.1.2 i).output = some oi at hoi
  change (ω.1.2 j).output = some oj at hoj
  change ¬ GlobalEvent ω.2 at hglobal
  obtain ⟨hvi, hsi, hoi'⟩ := ceremony_value prims K circuits settings D net rounds c world ω hω i hi oi hoi
  obtain ⟨hvj, hsj, hoj'⟩ := ceremony_value prims K circuits settings D net rounds c world ω hω j hj oj hoj
  rw [hvi, hvj]
  congr 1
  refine List.ext_getElem? fun m => ?_
  by_cases hm : m < (chunks settings.batchSize c.jobs).length
  swap
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  obtain ⟨outi, hout_i⟩ : ∃ out, (batchOutputsOf (ceremonyRecord ω.1.2 i))[m]? = some out :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨outj, hout_j⟩ : ∃ out, (batchOutputsOf (ceremonyRecord ω.1.2 j))[m]? = some out :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨bi, hbi⟩ : ∃ b, (startsOf (ceremonyRecord ω.1.2 i))[m]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨bj, hbj⟩ : ∃ b, (startsOf (ceremonyRecord ω.1.2 j))[m]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [hout_i, hout_j]
  congr 1
  have hg : Good prims (hashOf prims (MpcCells.cleanCache ω.2.1)) := good_hashOf prims _
  have ha : Agrees (hashOf prims (MpcCells.cleanCache ω.2.1)) (MpcCells.cleanCache ω.2.1) :=
    agrees_hashOf prims (MpcCells.noMpc_cleanCache _)
  obtain ⟨keys_i, inbox_i, -, hopen_i, -, hblock_i⟩ := ceremony_block prims K circuits settings hpath D net rounds c
    world ω hω i hi (by rw [hoi]; rfl) m bi outi hbi hout_i
  obtain ⟨keys_j, inbox_j, -, hopen_j, -, hblock_j⟩ := ceremony_block prims K circuits settings hpath D net rounds c
    world ω hω j hj (by rw [hoj]; rfl) m bj outj hbj hout_j
  have hci := (ceremony_startCircuits prims K circuits settings D net rounds c world hready.1 ω hω i hi m _
    (List.getElem?_eq_getElem hm) bi hbi).2
  have hcj := (ceremony_startCircuits prims K circuits settings D net rounds c world hready.1 ω hω j hj m _
    (List.getElem?_eq_getElem hm) bj hbj).2
  obtain ⟨hst, hagree⟩ := hshares D net rounds ℓ c world hready ω hω hglobal i hi (by rw [hoi]; rfl) m hm
  have hdel_i := ceremony_deliveredShares prims K circuits settings D net rounds c world hready.1 ω hω m hm hst i hi _ _
    hopen_i
  have hdel_j := ceremony_deliveredShares prims K circuits settings D net rounds c world hready.1 ω hω m hm hst j hj _ _
    hopen_j
  rw [← hci] at hdel_i hdel_j hagree
  have hcoll : ¬ DomainCollision CopyDomain (MpcCells.cleanCache ω.2.1) := fun hc =>
    hglobal (Or.inr (Or.inr (Or.inl ((MpcCells.domainCollision_cleanCache (fun _ h => h) _).1 hc))))
  exact OpenedAgreement.blockOutputs_agree_of_cache K prims circuits settings D (MpcCells.cleanCache ω.2.1) _ hg ha
    (fun T => startShares ω.1.2 m (refHolder D T) T) (startShares ω.1.2 m) i j hi hj keys_i keys_j
    (bi, inbox_i, outi) (bj, inbox_j, outj) hblock_i hblock_j (by rw [hci, hcj])
    (by simp [startShares, hbi]) (by simp [startShares, hbj])
    (fun l T g hl hlT hg' => hagree T l (refHolder D T) hl (refHolder_spec D T).2 hlT (refHolder_spec D T).1 g hg')
    hdel_i hdel_j hcoll

/-! ## The parts of the agreement of the recorded sharings -/

/-- The term keys at a check. With no global event at the end of one ceremony from a ready start, when
each honest operator recorded the start of check `k`, two honest holders of a term recorded the same
PRSS key of that term. -/
def RecordedTermKeys : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ¬ GlobalEvent ω.2 →
      ∀ k < (chunks settings.batchSize c.jobs).length, StartedAt D k ω.1.2 →
      ∀ T j j' b b', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
        (startsOf (ceremonyRecord ω.1.2 j))[k]? = some b → (startsOf (ceremonyRecord ω.1.2 j'))[k]? = some b' →
        b.ctx.prss.term T = b'.ctx.prss.term T

/-- The draws of `Rerand`. In one ceremony, the share after `Rerand` of each held term with no filler
at each start that an honest operator recorded has the stream cell of the PRSS key of that term, at
the label of `Rerand`, which is the label of the start less one, in the end world. -/
def RecordedRerandDraws : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State)
    (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C),
    ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world) →
    ∀ j, j ∉ D.1 → ∀ b ∈ startsOf (ceremonyRecord ω.1.2 j), ∀ T, T ∉ filledTerms K → b.ctx.self ∈ C.holders T →
      ∀ g < (outputsOf b.circuits).length,
        StreamCell prims D (.term T, b.ctx.prss.term T, b.state.label - 1, 0, g) ω.2 (b.v' T g)

/-- The digest round of check `k`. With no global event at the end of one ceremony from a ready start,
when each honest operator recorded the start of check `k`, the honest operator `i` has the output of
batch `k` and the batch has a positive output count, there are digest lists `ds` that agree on each
pair of honest holders of each term, and the list of each honest operator is its honest digests in
the end hash cache. -/
def RecordedDigests : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world),
      ∀ k (hk : k < (chunks settings.batchSize c.jobs).length),
        tupleCount (((chunks settings.batchSize c.jobs)[k]).map (circuits (gameParameter D c.keys) ·.kind)) ≠ 0 →
      ∀ i, i ∉ D.1 → (ω.1.2 i).output.isSome →
        ∃ ds : C.Party → List HashOutput,
          (∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
            (ds j)[C.terms.idxOf T]? = (ds j')[C.terms.idxOf T]?) ∧
          ∀ j b, j ∉ D.1 → (startsOf (ceremonyRecord ω.1.2 j))[k]? = some b →
            PassedShares.HonestDigests ω.2.1 j b (ds j)

omit [Fintype E] [DecidableEq E] in
/-- Each start that an honest operator recorded in the ghost run of one ceremony holds the filled
history of the tuples of its batch. -/
theorem ceremony_startHistory (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (m : ℕ) (b : BatchStart C) (hb : (startsOf (ceremonyRecord ω.1.2 i))[m]? = some b) :
    PassedShares.StartHistory K b := by
  have hne : startsOf (ceremonyRecord ω.1.2 i) ≠ [] := fun h => by simp [h] at hb
  obtain ⟨keys, -, z₁, h₁, hrec⟩ := ceremony_record prims K circuits settings D net rounds c world ω hω i hi hne
  rw [hrec] at hb
  exact PassedShares.histories_recRun K circuits settings i keys c.jobs c.counters z₁ h₁ b (List.mem_of_getElem? hb)

/-- `CeremonyPassedShares` from its parts. The honest operators started each check. A filled term
agrees through the equal digests of its honest holders, and a term with no filler through one stream. -/
theorem ceremonyPassedShares_of_parts (hstarted : CeremonyStarted prims K circuits settings)
    (hkeys : RecordedTermKeys prims K circuits settings) (hdraws : RecordedRerandDraws prims K circuits settings)
    (hdigests : RecordedDigests prims K circuits settings) : CeremonyPassedShares prims K circuits settings := by
  intro D net rounds ℓ c world hready ω hω hglobal i hi hout k hk
  have hlive : ∀ l, l ∉ D.1 → (c.keys l).isSome := by
    intro l hl
    by_contra hnone
    have hr : ((ω.1.1, ceremonyOutputs ω.1.2), ω.2) ∈
        support ((ceremonyPhase prims K circuits settings D net rounds c).run world) := by
      rw [ghostCeremony_erase, support_map]
      exact ⟨ω, hω, rfl⟩
    have := ceremonyDead prims K circuits settings D net rounds c world _ hr
      ⟨l, hl, Option.not_isSome_iff_eq_none.1 hnone⟩ i hi
    change (ω.1.2 i).output = none at this
    rw [this] at hout
    cases hout
  have hsize : 0 < settings.batchSize := Nat.pos_of_ne_zero fun h0 => by simp [chunks, h0] at hk
  have hst : StartedAt D k ω.1.2 := hstarted hsize D net rounds c (MpcCells.cleanWorld world)
    (MpcCells.noMpc_cleanCache _) hready.1 hlive _ (ghostCeremony_clean prims K circuits settings D net rounds c world ω hω)
    (fun hg => hglobal ((MpcCells.globalEvent_cleanWorld _).1 hg)) ⟨i, hi, hout⟩ k hk
  refine ⟨hst, fun T j j' hj hj' hjT hj'T g hg => ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hst j hj)
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hst j' hj')
  obtain ⟨bi, hbi⟩ := Option.isSome_iff_exists.1 (hst i hi)
  have hcirc := (ceremony_startCircuits prims K circuits settings D net rounds c world hready.1 ω hω j hj k _
    (List.getElem?_eq_getElem hk) b hb).2
  have hcirc' := (ceremony_startCircuits prims K circuits settings D net rounds c world hready.1 ω hω j' hj' k _
    (List.getElem?_eq_getElem hk) b' hb').2
  have hsync := ceremonySync prims K circuits settings D net rounds ℓ c world hready ω hω hglobal k hk hst j j' hj hj'
    k le_rfl
  rw [hb, hb', Option.map_some, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq,
    Prod.mk.injEq] at hsync
  obtain ⟨hmode, -, hlabel, -⟩ := hsync
  simp only [startShares, hb, hb', Option.map_some, Option.getD_some]
  rw [← hcirc] at hg
  by_cases hT : T ∈ filledTerms K
  · have htup : tupleCount (((chunks settings.batchSize c.jobs)[k]).map
        (circuits (gameParameter D c.keys) ·.kind)) ≠ 0 := by
      rw [← hcirc]
      have := main_outputsOf_length b.circuits
      unfold tupleCount
      omega
    obtain ⟨ds, hagree, hhon⟩ := hdigests D net rounds ℓ c world hready ω hω k hk htup i hi hout
    obtain ⟨hist, hh⟩ := hhon j b hj hb
    obtain ⟨hist', hh'⟩ := hhon j' b' hj' hb'
    obtain ⟨hpre, salt, hh₁, d, c₁, c₂, cd⟩ := hh T hjT
    obtain ⟨hpre', salt', hh₁', d', c₁', c₂', cd'⟩ := hh' T hj'T
    have hdd : d = d' := by
      have := hagree T j j' hj hj' hjT hj'T
      rw [cd, cd'] at this
      exact Option.some.inj this
    subst hdd
    have hsplit : ¬ DomainCollision SplitHashDomain ω.2.1 := fun h => hglobal (Or.inr (Or.inr (Or.inr h)))
    have hH := PassedShares.history_eq_of_digests ω.2.1 hsplit _ _ _ _ _ _ _ c₁ c₂ c₁' c₂'
    have hsh := ceremony_startHistory prims K circuits settings D net rounds c world ω hω j hj k b hb
    have hsh' := ceremony_startHistory prims K circuits settings D net rounds c world ω hω j' hj' k b' hb'
    obtain ⟨kj, -, -, hS⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω j hj k b hb
    obtain ⟨kj', -, -, hS'⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω j' hj' k b' hb'
    have hcc : b'.circuits = b.circuits := by rw [hcirc, hcirc']
    unfold PassedShares.StartHistory at hsh hsh'
    rw [hS.2.2.2.1] at hsh
    rw [hS'.2.2.2.1, ← hmode, hcc] at hsh'
    have hlen : (b.state.history T).length = (b'.state.history T).length := by
      rw [hsh, hsh', PassedShares.filledHistory_batchTuples K j T hjT hT,
        PassedShares.filledHistory_batchTuples K j' T hj'T hT, List.length_append, List.length_append,
        PassedShares.layerHistory_length K j j' T hjT hj'T b.mode b.circuits b.inputs b'.inputs b.zs b'.zs]
      simp
    have heq := PassedShares.prefix_eq hpre (hH ▸ hpre') hlen
    rw [hsh, hsh'] at heq
    exact PassedShares.filled_agree K j j' T hjT hj'T hT b.mode b.circuits b.inputs b'.inputs b.zs b'.zs b.v' b'.v'
      heq g hg
  · obtain ⟨kj, -, -, hS⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω j hj k b hb
    obtain ⟨kj', -, -, hS'⟩ := ceremony_start prims K circuits settings D net rounds c world ω hω j' hj' k b' hb'
    have hd := hdraws D net rounds c world ω hω j hj b (List.mem_of_getElem? hb) T hT
      (by rw [hS.2.2.2.1]; exact hjT) g hg
    have hd' := hdraws D net rounds c world ω hω j' hj' b' (List.mem_of_getElem? hb') T hT
      (by rw [hS'.2.2.2.1]; exact hj'T) g (by rw [show b'.circuits = b.circuits by rw [hcirc, hcirc']]; exact hg)
    rw [hkeys D net rounds ℓ c world hready ω hω hglobal k hk hst T j j' b b' hj hj' hjT hj'T hb hb', hlabel] at hd
    exact StreamCell.unique prims D hd hd'

/-- `CeremonyOutputsAgree` from the ghost path, the start of each check, the term keys, the draws of
`Rerand` and the digest round. -/
theorem ceremonyOutputsAgree_of_parts (hpath : GhostOnPath (C := C) (E := E) prims)
    (hstarted : CeremonyStarted prims K circuits settings) (hkeys : RecordedTermKeys prims K circuits settings)
    (hdraws : RecordedRerandDraws prims K circuits settings) (hdigests : RecordedDigests prims K circuits settings) :
    CeremonyOutputsAgree prims K circuits settings :=
  ceremonyOutputsAgree_of prims K circuits settings hpath
    (ceremonyPassedShares_of_parts prims K circuits settings hstarted hkeys hdraws hdigests)

end Ghost

end CeremonyRecords

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyMonitor_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyMonitor_of

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonySync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonySync

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyBatch_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyBatch_of

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree_of

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.termDraws_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.termDraws_agree

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree_of_parts
