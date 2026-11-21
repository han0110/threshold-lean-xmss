import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutWalk
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RecordedRun

/-!
# The record of each batch and its counters

`RecOkS` states that the record of a run of `recRun` has the shape of the batches of the job list,
and `recOkS_recRun` proves it. The section `BatchCounters` places each start of a batch at the label
and the tag of the counters of the job list (`Placed`, `counted_recRun`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace GhostBatch

attribute [local instance] Classical.propDecidable

/-! ## The shape of a record with `H` fixed -/

section Shape

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- The start `b` of a check of operator `j` with the keys `keys`, with `H` fixed to `h`. -/
def StartShape (h : Query C → HashOutput) (j : C.Party) (keys : Keys C) (b : BatchStart C) : Prop :=
  b.ctx.self = j ∧ b.mode = settings.mode ∧ b.parameter = keys.parameter ∧
    b.circuits = b.jobs.map (circuits keys.parameter ·.kind) ∧ b.inputs = batchInputs h keys.seed b.jobs j

/-- A full batch of operator `j` with the start, the inbox of `OpenRep` and the output. The inbox
passes the hash check with `H` fixed to `h`, and the output is the sum of the copies. -/
def BlockShape (h : Query C → HashOutput) (j : C.Party) (keys : Keys C)
    (x : BatchStart C × Mail C E × List (List Bit)) : Prop :=
  StartShape circuits settings h j keys x.1 ∧
    repCheck K j x.2.1 (copyHashes h (repCopy K j x.1.v' (outputsOf x.1.circuits).length x.2.1)
      (outputsOf x.1.circuits).length) ∧
    x.2.2 = ThresholdLeanXmssSecurity.assemble x.1.circuits
      (fun g => ∑ T, repCopy K j x.1.v' (outputsOf x.1.circuits).length x.2.1 T g)

end Shape

/-! ## The path of an honest operator in the ghost run -/

section Walk

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α ρ : Type}

/-- A ghost step as a step whose output is the output and the record. -/
def toStep : RStep C E G α ρ → Step C E G (Option α × ρ)
  | .done out record => .done (some (out, record))
  | .wait outbox resume => .wait outbox fun inbox => some <$> resume inbox
  | .call input resume => .call input fun r => some <$> resume r

/-- `advanceR` is `advance` of the program with the output and the record in its output. -/
theorem advanceR_toStep (oa : OracleComp (PartySpec C E G) (Option α × ρ)) :
    toStep <$> advanceR oa = advance (some <$> oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rcases t with (t | outbox) | input
    · have h : ∀ {γ : Type} (g : (LocalSpec C).Range t → OracleComp (PartySpec C E G) (Option γ)),
          advance (liftM (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) >>= g) =
            OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (g r) :=
        fun g => rfl
      have hR : ∀ (g : (LocalSpec C).Range t → OracleComp (PartySpec C E G) (Option α × ρ)),
          advanceR (liftM (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl t))) >>= g) =
            OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advanceR (g r) :=
        fun g => rfl
      rw [map_bind, h, hR, map_bind]
      simp only [ih]
    · rw [map_bind]
      rfl
    · rw [map_bind]
      rfl

variable (prims : Primitives) (Dw : C.Coalition)

end Walk

/-! ## The records of a recorded program with `H` fixed -/

section Support

variable {C : Committee} {E : Type} (h : Query C → HashOutput)

/-- The decomposition of an outcome of a bind of recorded programs with `H` fixed. -/
theorem mem_support_fix_bind {α β : Type} (x : RecM C E α) (f : α → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (simulateQ (fixHash h) (x >>= f).run.run)) :
    ∃ z₁ ∈ support (simulateQ (fixHash h) x.run.run), (z₁.1 = none ∧ z = (none, z₁.2)) ∨
      ∃ a, z₁.1 = some a ∧ ∃ z₂ ∈ support (simulateQ (fixHash h) (f a).run.run), z = (z₂.1, z₁.2 ++ z₂.2) := by
  rw [OptionT.run_bind, Option.elimM, WriterT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
  obtain ⟨z₁, h₁, hz⟩ := hz
  refine ⟨z₁, h₁, ?_⟩
  rcases z₁ with ⟨_ | a, w⟩
  · left
    simp only [Option.elim, WriterT.run_pure, simulateQ_map, simulateQ_pure, support_map, support_pure,
      Set.image_singleton, Set.mem_singleton_iff] at hz
    simp at hz
    exact ⟨rfl, hz⟩
  · right
    refine ⟨a, rfl, ?_⟩
    simp only [Option.elim, simulateQ_map, support_map, Set.mem_image] at hz
    obtain ⟨z₂, h₂, rfl⟩ := hz
    exact ⟨z₂, h₂, rfl⟩

/-- An outcome of a program with no record, with `H` fixed, has the empty record. -/
theorem mem_support_fix_lift {α : Type} (p : PartyM C E RealSpec α)
    (z : Option α × List (RecEvent C E)) (hz : z ∈ support (simulateQ (fixHash h) (RecM.lift p).run.run)) :
    z.2 = [] ∧ z.1 ∈ support (simulateQ (fixHash h) p.run) := by
  change z ∈ support (simulateQ (fixHash h) (liftM p.run : WriterT (List (RecEvent C E)) _ _).run) at hz
  rw [WriterT.run_liftM, simulateQ_map, support_map] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  exact ⟨rfl, ho⟩

theorem mem_support_fix_lift_bind {α β : Type} (p : PartyM C E RealSpec α) (f : α → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (simulateQ (fixHash h) (RecM.lift p >>= f).run.run)) :
    z = (none, []) ∨ ∃ a, some a ∈ support (simulateQ (fixHash h) p.run) ∧
      z ∈ support (simulateQ (fixHash h) (f a).run.run) := by
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_fix_bind h _ _ z hz
  · left
    rw [(mem_support_fix_lift h p z₁ h₁).1]
  · right
    obtain ⟨hnil, hmem⟩ := mem_support_fix_lift h p z₁ h₁
    rw [ha] at hmem
    rw [hnil, List.nil_append]
    exact ⟨a, hmem, h₂⟩

theorem mem_support_fix_record_bind {β : Type} (events : List (RecEvent C E)) (f : PUnit → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (simulateQ (fixHash h) (RecM.record events >>= f).run.run)) :
    ∃ z₂ ∈ support (simulateQ (fixHash h) (f PUnit.unit).run.run), z = (z₂.1, events ++ z₂.2) := by
  obtain ⟨z₁, h₁, ⟨hnone, -⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_fix_bind h _ _ z hz
  · simp [RecM.record, OptionT.run_lift, WriterT.run_tell] at h₁
    rw [h₁] at hnone
    cases hnone
  · simp [RecM.record, OptionT.run_lift, WriterT.run_tell] at h₁
    subst h₁
    exact ⟨z₂, h₂, rfl⟩

end Support

section Blocks

variable {C : Committee} {E : Type}

/-- The record of one full batch. -/
def blockOf (x : BatchStart C × Mail C E × List (List Bit)) : Record C E :=
  [.start x.1, .opened x.1.v' x.2.1, .output x.2.2]

/-- A record of full batches, each with `P`. -/
def Full (P : BatchStart C × Mail C E × List (List Bit) → Prop) (record : Record C E) : Prop :=
  ∃ bs : List (BatchStart C × Mail C E × List (List Bit)), (∀ x ∈ bs, P x) ∧ record = bs.flatMap blockOf

/-- A record of full batches, each with `P`, and a cut batch whose start has `S`. -/
def Cut (S : BatchStart C → Prop) (P : BatchStart C × Mail C E × List (List Bit) → Prop) (record : Record C E) :
    Prop :=
  ∃ (bs : List (BatchStart C × Mail C E × List (List Bit))) (tail : Record C E), (∀ x ∈ bs, P x) ∧
    record = bs.flatMap blockOf ++ tail ∧
    (tail = [] ∨ ∃ b, S b ∧ (tail = [.start b] ∨ ∃ inbox, tail = [.start b, .opened b.v' inbox]))

theorem Full.cut {S : BatchStart C → Prop} {P : BatchStart C × Mail C E × List (List Bit) → Prop}
    {record : Record C E} (hf : Full P record) : Cut S P record := by
  obtain ⟨bs, hbs, rfl⟩ := hf
  exact ⟨bs, [], hbs, by simp, Or.inl rfl⟩

/-- An outcome of a recorded program. It has a value and full batches, or it aborts with a cut
record. -/
def OutcomeOk {β : Type} (S : BatchStart C → Prop) (P : BatchStart C × Mail C E × List (List Bit) → Prop)
    (z : Option β × Record C E) : Prop :=
  Full P z.2 ∨ (z.1 = none ∧ Cut S P z.2)

variable (h : Query C → HashOutput) (S : BatchStart C → Prop)
  (P : BatchStart C × Mail C E × List (List Bit) → Prop)

/-- Each outcome of `y` with `H` fixed to `h` is `OutcomeOk`. -/
def RecOk {β : Type} (y : RecM C E β) : Prop :=
  ∀ z ∈ support (simulateQ (fixHash h) y.run.run), OutcomeOk S P z

/-- `RecOk` from each counter state. -/
def RecOkS {β : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop := ∀ st, RecOk h S P (x.run st)

theorem recOk_pure {β : Type} (b : β) : RecOk h S P (pure b : RecM C E β) := by
  intro z hz
  simp at hz
  subst hz
  exact Or.inl ⟨[], by simp, rfl⟩

theorem recOk_lift {β : Type} (p : PartyM C E RealSpec β) : RecOk h S P (RecM.lift p) := by
  intro z hz
  refine Or.inl ⟨[], by simp, ?_⟩
  rw [(mem_support_fix_lift h p z hz).1]
  rfl

theorem recOk_bind {β γ : Type} (x : RecM C E β) (f : β → RecM C E γ) (hx : RecOk h S P x)
    (hf : ∀ a, RecOk h S P (f a)) : RecOk h S P (x >>= f) := by
  intro z hz
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_fix_bind h _ _ z hz
  · rcases hx z₁ h₁ with hfull | ⟨-, hcut⟩
    · exact Or.inr ⟨rfl, hfull.cut⟩
    · exact Or.inr ⟨rfl, hcut⟩
  · obtain ⟨bs₁, hbs₁, hr₁⟩ : Full P z₁.2 := by
      rcases hx z₁ h₁ with hfull | ⟨hn, -⟩
      · exact hfull
      · rw [ha] at hn
        cases hn
    rcases hf a z₂ h₂ with ⟨bs₂, hbs₂, hr₂⟩ | ⟨hn, bs₂, tail, hbs₂, hr₂, htail⟩
    · refine Or.inl ⟨bs₁ ++ bs₂, fun x hx => ?_, by simp [hr₁, hr₂, List.flatMap_append]⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact hbs₁ x hx
      · exact hbs₂ x hx
    · refine Or.inr ⟨hn, bs₁ ++ bs₂, tail, fun x hx => ?_, by simp [hr₁, hr₂, List.flatMap_append], htail⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact hbs₁ x hx
      · exact hbs₂ x hx

theorem recOkS_pure {β : Type} (b : β) : RecOkS h S P (pure b : StateT (ℕ × ℕ) (RecM C E) β) :=
  fun st => by rw [StateT.run_pure]; exact recOk_pure h S P _

theorem recOkS_bind {β γ : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) (f : β → StateT (ℕ × ℕ) (RecM C E) γ)
    (hx : RecOkS h S P x) (hf : ∀ a, RecOkS h S P (f a)) : RecOkS h S P (x >>= f) :=
  fun st => by
    rw [StateT.run_bind]
    exact recOk_bind h S P _ _ (hx st) fun p => hf p.1 p.2

theorem recOkS_liftS {β : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) : RecOkS h S P (RecM.liftS x) :=
  fun _ => recOk_lift h S P _

end Blocks

/-! ## The record of a recorded tree program -/

section Program

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings) (h : Query C → HashOutput) (prims : Primitives)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The input sharings of a job at operator `ctx.self` with `H` fixed to `h`. -/
theorem D_inputQuery_self (ctx : Context C) (job : Job) :
    ThresholdLeanXmssSecurity.D prims h (inputQuery ctx job) =
      fun T => if ctx.self ∈ C.holders T then inputBits h ctx.keys.seed job T else [] := by
  funext T
  unfold inputQuery
  simp only [D_bind, D_pure, D_mapM]
  rw [getD_terms_idxOf]
  by_cases hi : ctx.self ∈ C.holders T
  · simp only [hi, ↓reduceIte, D_flatMapM, prf, D_map, D_hashQuery, inputBits]
  · simp [hi, D_pure]

omit [Fintype E] [DecidableEq E] in
theorem pins_map {β γ : Type} (f : β → γ) (oa : OracleComp (RoSpec C) β) (ha : Pins (E := E) h prims oa) :
    Pins (E := E) h prims (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact pins_bind h prims _ _ ha fun _ => pins_pure h prims _

omit [Fintype E] [DecidableEq E] in
theorem pins_flatMapM {β γ : Type} (f : β → OracleComp (RoSpec C) (List γ)) (hf : ∀ b, Pins (E := E) h prims (f b)) :
    ∀ l : List β, Pins (E := E) h prims (l.flatMapM f)
  | [] => pins_pure h prims _
  | a :: l => by
    rw [List.flatMapM_cons]
    exact pins_bind h prims _ _ (hf a) fun _ => pins_bind h prims _ _ (pins_flatMapM f hf l) fun _ =>
      pins_pure h prims _

omit [Fintype E] [DecidableEq E] in
theorem pins_inputQuery (ctx : Context C) (job : Job) : Pins (E := E) h prims (inputQuery ctx job) := by
  unfold inputQuery
  refine pins_bind h prims _ _ (pins_mapM h prims _ (fun T => ?_) _) fun _ => pins_pure h prims _
  split
  · exact pins_flatMapM h prims _ (fun x => pins_map h prims _ _ (pins_map h prims _ _ (pins_hashQuery h prims _))) _
  · exact pins_pure h prims _

include prims in
omit [Fintype E] [DecidableEq E] in
/-- The input sharings of a batch with `H` fixed to `h` are `batchInputs`. -/
theorem holds_inputs (ctx : Context C) (jobs : List Job) :
    Holds (E := E) h (· = batchInputs h ctx.keys.seed jobs ctx.self) (jobs.mapM (inputShares (G := RealSpec) ctx)) := by
  rw [inputShares_fun, mapM_oracleStep]
  intro z hz a ha
  rw [pins_mapM h prims _ (pins_inputQuery h prims ctx) jobs z hz a ha, D_mapM]
  unfold batchInputs
  refine List.map_congr_left fun job _ => ?_
  rw [D_inputQuery_self]

omit [Fintype E] [DecidableEq E] in
include prims in
/-- The rest of `OpenRep` with `H` fixed to `h` passes the hash check and opens the sum of the
copies. -/
theorem holds_repRest (i : C.Party) (v : Shares C Bit) (count : ℕ) (inbox : Mail C E) :
    Holds h (fun opened => repCheck K i inbox (copyHashes h (repCopy K i v count inbox) count) ∧
      opened = fun g => ∑ T, repCopy K i v count inbox T g) (repRest (G := RealSpec) K i v count inbox) := by
  unfold repRest
  refine holds_bind h _ _ _ _ (pins_mapM h prims _ (fun T => pins_hashQuery h prims _) _) fun cds hcds => ?_
  refine holds_bind h _ _ _ _ (holds_require h _) fun _ hcheck => holds_pure h _ _ ⟨?_, rfl⟩
  rw [hcds, D_mapM] at hcheck
  simpa [D_hashQuery, copyHashes] using hcheck

omit [Fintype E] [DecidableEq E] in
include prims in
theorem recOk_recCheckOpen (j : C.Party) (keys : Keys C) (b : BatchStart C)
    (hb : StartShape circuits settings h j keys b) (k : ℕ) (st : ℕ × ℕ) :
    RecOk h (StartShape circuits settings h j keys) (BlockShape K circuits settings h j keys)
      ((recCheckOpen K b k).run st) := by
  intro z hz
  unfold recCheckOpen at hz
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_set,
    StateT.run_pure] at hz
  obtain ⟨z₁, h₁, rfl⟩ := mem_support_fix_record_bind h _ _ z hz
  have hcut₁ : OutcomeOk (StartShape circuits settings h j keys) (BlockShape K circuits settings h j keys)
      ((none : Option (Option (List (List Bit)) × ℕ × ℕ)), [RecEvent.start b] ++ []) :=
    Or.inr ⟨rfl, [], [.start b], by simp, by simp, Or.inr ⟨b, hb, Or.inl rfl⟩⟩
  rcases mem_support_fix_lift_bind h _ _ z₁ h₁ with rfl | ⟨p, -, h₂⟩
  · exact hcut₁
  rcases mem_support_fix_lift_bind h _ _ _ h₂ with rfl | ⟨p₁, -, h₃⟩
  · exact hcut₁
  rcases mem_support_fix_lift_bind h _ _ _ h₃ with rfl | ⟨p₂, -, h₄⟩
  · exact hcut₁
  obtain ⟨z₅, h₅, rfl⟩ := mem_support_fix_record_bind h _ _ _ h₄
  rcases mem_support_fix_lift_bind h _ _ _ h₅ with rfl | ⟨p₃, hp₃, h₆⟩
  · exact Or.inr ⟨rfl, [], [.start b, .opened b.v' p₂.1], by simp, by simp, Or.inr ⟨b, hb, Or.inr ⟨p₂.1, rfl⟩⟩⟩
  obtain ⟨z₇, h₇, rfl⟩ := mem_support_fix_record_bind h _ _ _ h₆
  have hlog : z₇.2 = [] := by
    simp at h₇
    rw [h₇]
  obtain ⟨hcheck, hopened⟩ := (holds_bind h _ (fun q : (ℕ → Bit) × (ℕ × ℕ) =>
      repCheck K b.ctx.self p₂.1 (copyHashes h (repCopy K b.ctx.self b.v' (outputsOf b.circuits).length p₂.1)
        (outputsOf b.circuits).length) ∧
      q.1 = fun g => ∑ T, repCopy K b.ctx.self b.v' (outputsOf b.circuits).length p₂.1 T g) _ _
    (holds_repRest K h prims _ _ _ _) fun a ha => holds_pure h _ _ ha) _ hp₃ p₃ rfl
  rw [hb.1] at hcheck hopened
  left
  refine ⟨[(b, p₂.1, ThresholdLeanXmssSecurity.assemble b.circuits p₃.1)], ?_, ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hb, hcheck, by rw [hopened]⟩
  · simp [blockOf, hlog]

include prims in
theorem recOkS_recBatch (j : C.Party) (keys : Keys C) (prss : PrssKeys C) (jobs : List Job) :
    RecOkS h (StartShape circuits settings h j keys) (BlockShape K circuits settings h j keys)
      (recBatch K circuits settings ⟨j, keys, prss⟩ keys.parameter jobs) := by
  rintro ⟨label, k⟩ z hz
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_lift] at hz
  rcases mem_support_fix_lift_bind h _ _ z hz with rfl | ⟨p, hp, h₂⟩
  · exact Or.inl ⟨[], by simp, rfl⟩
  rcases mem_support_fix_lift_bind h _ _ _ h₂ with rfl | ⟨p₁, -, h₃⟩
  · exact Or.inl ⟨[], by simp, rfl⟩
  rcases mem_support_fix_lift_bind h _ _ _ h₃ with rfl | ⟨p₂, -, h₄⟩
  · exact Or.inl ⟨[], by simp, rfl⟩
  have hinputs : p.1 = batchInputs h keys.seed jobs j :=
    (holds_bind h _ (fun q : List (C.Term → List Bit) × (ℕ × ℕ) => q.1 = batchInputs h keys.seed jobs j) _ _
      (holds_inputs h prims ⟨j, keys, prss⟩ jobs) fun a ha => holds_pure h _ _ ha) _ hp p rfl
  exact recOk_recCheckOpen K circuits settings h prims j keys _ ⟨rfl, rfl, rfl, rfl, hinputs⟩ k _ z h₄

include prims in
theorem recOkS_recRun (j : C.Party) (keys : Keys C) (jobs : List Job) :
    RecOkS h (StartShape circuits settings h j keys) (BlockShape K circuits settings h j keys)
      (recRun K circuits settings j keys jobs) :=
  recOkS_bind h _ _ _ _ (recOkS_liftS h _ _ _) fun prss =>
    closed_batched (fun x => RecOkS h (StartShape circuits settings h j keys) (BlockShape K circuits settings h j keys) x)
      (recOkS_pure h _ _) (recOkS_bind h _ _) _ _ (recOkS_recBatch K circuits settings h prims j keys prss) jobs

end Program

/-! ## The premises and the hop -/

section Hop

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)
  (budget : StartBudget)

omit [Fintype E] [DecidableEq E] in
/-- An outcome of a computation in `streamWorld` that runs `oa` and then `f` has the value of `oa` in
its first part, and its hash cache grows the cache of `oa`. -/
theorem support_pair_mono (D : C.Coalition) {β γ : Type} (oa : OracleComp (WorldSpec C) β) (f : β → OracleComp (WorldSpec C) γ)
    (world : StreamState C) (ω : (β × γ) × StreamState C)
    (hω : ω ∈ support ((simulateQ (streamWorld prims D) (do
      let r ← oa
      let bad ← f r
      pure (r, bad))).run world)) :
    ∃ y ∈ support ((simulateQ (streamWorld prims D) oa).run world), ω.1.1 = y.1 ∧ y.2.1 ≤ ω.2.1 := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hω
  obtain ⟨y, hy, hω⟩ := hω
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hω
  obtain ⟨w, hw, hω⟩ := hω
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hω
  subst hω
  exact ⟨y, hy, rfl, streamWorld_run_mono prims D _ y.2 w hw⟩

/-- A list of cached values is the list of the values of each `h` that agrees with the cache. -/
theorem forall₂_cached {α : Type} (cache : HashCache C) (h : Query C → HashOutput) (ha : Agrees h cache)
    (q : α → Query C) : ∀ {l : List α} {ds : List HashOutput},
      List.Forall₂ (fun a d => cache (q a) = some d) l ds → ds = l.map fun a => h (q a)
  | _, _, .nil => rfl
  | _, _, .cons hd tl => by rw [forall₂_cached cache h ha q tl, List.map_cons, ha _ _ hd]

/-- Each element of a list of cached values has a cell. -/
theorem forall₂_cell {α : Type} (cache : HashCache C) (q : α → Query C) : ∀ {l : List α} {ds : List HashOutput},
      List.Forall₂ (fun a d => cache (q a) = some d) l ds → ∀ a ∈ l, (cache (q a)).isSome
  | _, _, .nil => fun _ ha => by cases ha
  | _, _, .cons hd tl => fun a ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [hd]; rfl
    · exact forall₂_cell cache q tl a ha

theorem vector_congr {R : Type} (count : ℕ) (f f' : ℕ → R) (hf : ∀ g < count, f g = f' g) :
    vector count f = vector count f' :=
  List.map_congr_left fun g hg => hf g (List.mem_range.1 hg)

end Hop

end GhostBatch

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace BatchCounters

attribute [local instance] Classical.propDecidable

attribute [local instance] inhabitedField

/-! ## Paths of a recorded program -/

section Support

variable {C : Committee} {E : Type}

/-- A lifted program in a recorded program either aborts with no record or gives a value on one of
its paths. -/
theorem mem_support_lift_bind {α β : Type} (p : PartyM C E RealSpec α) (f : α → RecM C E β)
    (z : Option β × List (RecEvent C E)) (hz : z ∈ support (RecM.lift p >>= f).run.run) :
    z = (none, []) ∨ ∃ a, some a ∈ support p.run ∧ z ∈ support (f a).run.run := by
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · change z₁ ∈ support (liftM p.run : WriterT (List (RecEvent C E)) _ _).run at h₁
    simp only [WriterT.run_liftM, support_map, Set.mem_image] at h₁
    obtain ⟨_, -, rfl⟩ := h₁
    left
    rfl
  · change z₁ ∈ support (liftM p.run : WriterT (List (RecEvent C E)) _ _).run at h₁
    simp only [WriterT.run_liftM, support_map, Set.mem_image] at h₁
    obtain ⟨o, ho, rfl⟩ := h₁
    cases ha
    right
    exact ⟨a, ho, by simpa using h₂⟩

end Support

/-! ## One batch -/

section Batch

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- The check and the opening of a recorded batch record the start `b` and no other start. On success
the label is the label after the check of `b` and the tag is `k + 1`. -/
theorem recCheckOpen_counters (b : BatchStart C) (k : ℕ) (st : ℕ × ℕ) (z)
    (hz : z ∈ support ((recCheckOpen K b k).run st).run.run) :
    startsOf z.2 = [b] ∧ ∀ o st', z.1 = some (o, st') → ∃ s3 : Unit × RunState C,
      some s3 ∈ support (((realRunBuildingBlocks (G := RealSpec) K b.ctx b.mode).verify
        (batchTuples K b.mode b.circuits b.inputs b.zs b.v')).run b.state).run ∧ st' = (s3.2.label, k + 1) := by
  unfold recCheckOpen at hz
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_set,
    StateT.run_pure] at hz
  obtain ⟨z₁, h₁, rfl⟩ := mem_support_record_bind _ _ z hz
  have hstart : ∀ rest : Record C E, startsOf rest = [] → startsOf ([RecEvent.start b] ++ rest) = [b] := by
    intro rest hr
    simp [startsOf] at hr ⊢
    exact hr
  rcases mem_support_lift_bind _ _ z₁ h₁ with rfl | ⟨p, hp, h₂⟩
  · exact ⟨hstart [] rfl, fun _ _ h => by cases h⟩
  rcases mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, -, h₃⟩
  · exact ⟨hstart [] rfl, fun _ _ h => by cases h⟩
  rcases mem_support_lift_bind _ _ _ h₃ with rfl | ⟨p₂, -, h₄⟩
  · exact ⟨hstart [] rfl, fun _ _ h => by cases h⟩
  obtain ⟨z₅, h₅, rfl⟩ := mem_support_record_bind _ _ _ h₄
  rcases mem_support_lift_bind _ _ _ h₅ with rfl | ⟨p₃, -, h₆⟩
  · exact ⟨hstart _ (by simp [startsOf]), fun _ _ h => by cases h⟩
  obtain ⟨z₇, h₇, rfl⟩ := mem_support_record_bind _ _ _ h₆
  simp at h₇
  subst h₇
  refine ⟨hstart _ (by simp [startsOf]), fun o st' h => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rcases mem_support_optionT_bind _ _ _ hp with h' | ⟨a, ha, hr⟩
  · cases h'
  · have : p = (a, st) := by simpa using hr
    subst this
    exact ⟨a, ha, by rw [← h.2]⟩

/-- The layers and `Rerand` of a recorded batch from the label `L` and the tag `k` end at the label `L`
plus the number of the tuples of the head and at the tag `k`. -/
theorem head_counters (ctx : Context C) (mode : ReshareMode) (cs : List Circuit) (inputs : List (C.Term → List Bit))
    (L k : ℕ) (q₁ : (ℕ → Shares C Bit) × RunState C)
    (h₁ : some q₁ ∈ support ((recLayers K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs
      (depth cs)).run ⟨fun _ => [], L, k⟩).run)
    (q₂ : Shares C Bit × RunState C)
    (h₂ : some q₂ ∈ support (((realRunBuildingBlocks (G := RealSpec) K ctx mode).rerand (outputShares K cs
      (layerPrefix K mode cs inputs q₁.1 (depth cs)).1) (outputsOf cs).length).run q₁.2).run) :
    q₂.2.label = L + (headCounts cs).length ∧ q₂.2.tag = k := by
  have hf := foldlM_layerBody_eq K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs (depth cs)
  have h₁' : some (layerPrefix K mode cs inputs q₁.1 (depth cs), q₁.2) ∈ support
      ((((List.range (depth cs)).foldlM (layerBody K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs)
        (inputs, [])).run ⟨fun _ => [], L, k⟩).run) := by
    rw [hf, StateT.run_map]
    simp only [OptionT.run_map, support_map, Set.mem_image]
    exact ⟨some q₁, h₁, rfl⟩
  have he : (⟨fun _ => [], L, k⟩ : RunState C) =
      ⟨filledHistory K ctx.self ([] : List (Tuple C)), L + ([] : List (Tuple C)).length, k⟩ := by
    congr 1
    funext T
    simp [filledHistory]
  rw [he] at h₁'
  obtain ⟨hs, hc⟩ := layers_support K ctx mode cs _ (inputs, []) L k _ h₁'
  have hr := rerand_support K ctx mode _ _ _ q₂ h₂
  rw [hr, hs]
  have hlen : (layerPrefix K mode cs inputs q₁.1 (depth cs)).2.length = depth cs := by
    simpa using congrArg List.length hc
  simp [afterReply, hlen, headCounts, Nat.add_assoc]

/-- The facts of a start `b` of a batch of the jobs `jobs` at the context `ctx` from the counters
`(L, k)`. -/
def StartAt (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (L k : ℕ) (b : BatchStart C) : Prop :=
  b.jobs = jobs ∧ b.mode = settings.mode ∧ b.parameter = parameter ∧
    b.circuits = jobs.map (circuits parameter ·.kind) ∧ b.ctx = ctx ∧ b.state.tag = k ∧
      b.state.label = L + (headCounts b.circuits).length

/-- One recorded batch from the counters `(L, k)` aborts with no start, or it records one start with
`StartAt`. On success the counters are `L` plus `batchLabel` of its circuits and `k + 1`. -/
theorem recBatch_counters (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (L k : ℕ) (z)
    (hz : z ∈ support ((recBatch K circuits settings ctx parameter jobs).run (L, k)).run.run) :
    (startsOf z.2 = [] ∧ z.1 = none) ∨ ∃ b, startsOf z.2 = [b] ∧ StartAt circuits settings ctx parameter jobs L k b ∧
      ∀ o st', z.1 = some (o, st') → st' = (L + batchLabel b.circuits, k + 1) := by
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_lift] at hz
  rcases mem_support_lift_bind _ _ z hz with rfl | ⟨p, -, h₂⟩
  · exact Or.inl ⟨rfl, rfl⟩
  rcases mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, hp₁, h₃⟩
  · exact Or.inl ⟨rfl, rfl⟩
  rcases mem_support_lift_bind _ _ _ h₃ with rfl | ⟨p₂, hp₂, h₄⟩
  · exact Or.inl ⟨rfl, rfl⟩
  obtain ⟨-, hq₁⟩ := mem_support_lift_run _ _ _ hp₁
  obtain ⟨hst, hq₂⟩ := mem_support_lift_run _ _ _ hp₂
  obtain ⟨hlabel, htag⟩ := head_counters K ctx settings.mode _ p.1 L k p₁.1 hq₁ p₂.1 hq₂
  obtain ⟨hstarts, hend⟩ := recCheckOpen_counters K _ k _ z h₄
  refine Or.inr ⟨_, hstarts, ⟨rfl, rfl, rfl, rfl, rfl, htag, hlabel⟩, fun o st' h => ?_⟩
  obtain ⟨s3, hs3, rfl⟩ := hend o st' h
  have hcl := check_label K ctx _ _ s3 hs3
  have hcounts : (batchTuples K (realRunBuildingBlocks (G := RealSpec) K ctx settings.mode).mode
      (jobs.map (circuits parameter ·.kind)) p.1 p₁.1.1 p₂.1.1).map
      (·.count) = headCounts (jobs.map (circuits parameter ·.kind)) := by
    have hs := congrArg (List.map Prod.fst) (batchTuples_shape K (realRunBuildingBlocks (G := RealSpec) K ctx
      settings.mode).mode (jobs.map (circuits parameter ·.kind))
      p.1 p₁.1.1 p₂.1.1)
    simpa [List.map_map, Function.comp_def, headCounts] using hs
  simp only [Prod.mk.injEq, and_true]
  rw [hcl]
  dsimp only at hcounts ⊢
  rw [hcounts, hlabel, batchLabel]
  omega

end Batch

/-! ## The counters along a list of starts -/

section Placed

variable {C : Committee}

/-- The counters after the starts `ss` of full batches from the counters `st`. -/
def after (st : ℕ × ℕ) (ss : List (BatchStart C)) : ℕ × ℕ :=
  (st.1 + (ss.map (batchLabel ·.circuits)).sum, st.2 + ss.length)

/-- The starts `ss` from the counters `st`. Each start has `S`, its tag is the tag before it, and its
label is the label before it plus the number of the tuples of its head. A full batch adds
`batchLabel` of its circuits to the label and one to the tag. -/
def Placed (S : BatchStart C → Prop) (st : ℕ × ℕ) : List (BatchStart C) → Prop
  | [] => True
  | b :: ss => S b ∧ b.state.tag = st.2 ∧ b.state.label = st.1 + (headCounts b.circuits).length ∧
      Placed S (st.1 + batchLabel b.circuits, st.2 + 1) ss

theorem after_nil (st : ℕ × ℕ) : after st ([] : List (BatchStart C)) = st := by
  simp [after]

theorem after_append (st : ℕ × ℕ) (ss₁ ss₂ : List (BatchStart C)) :
    after st (ss₁ ++ ss₂) = after (after st ss₁) ss₂ := by
  simp [after, Nat.add_assoc]

theorem placed_append (S : BatchStart C → Prop) :
    ∀ (ss₁ ss₂ : List (BatchStart C)) (st : ℕ × ℕ),
      Placed S st (ss₁ ++ ss₂) ↔ Placed S st ss₁ ∧ Placed S (after st ss₁) ss₂
  | [], ss₂, st => by simp [Placed, after_nil]
  | b :: ss₁, ss₂, st => by
    have h := placed_append S ss₁ ss₂ (st.1 + batchLabel b.circuits, st.2 + 1)
    have ha : after (st.1 + batchLabel b.circuits, st.2 + 1) ss₁ = after st (b :: ss₁) := by
      simp only [after, List.map_cons, List.sum_cons, List.length_cons]
      ext <;> simp only <;> omega
    simp only [List.cons_append, Placed, h, ha, and_assoc]

/-- The start `n` of `Placed` starts has `S`, the tag `st.2 + n`, and the label `st.1` plus
`batchLabel` of the circuits of the starts before it plus the number of the tuples of its head. -/
theorem placed_getElem (S : BatchStart C → Prop) :
    ∀ (ss : List (BatchStart C)) (st : ℕ × ℕ), Placed S st ss → ∀ (n : ℕ) b, ss[n]? = some b →
      S b ∧ b.state.tag = st.2 + n ∧
        b.state.label = st.1 + ((ss.take n).map (batchLabel ·.circuits)).sum + (headCounts b.circuits).length
  | [], _, _, n, b, hb => by simp at hb
  | b' :: ss, st, hp, 0, b, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
    subst hb
    obtain ⟨hS, htag, hlabel, -⟩ := hp
    exact ⟨hS, by simp [htag], by simp [hlabel]⟩
  | b' :: ss, st, hp, n + 1, b, hb => by
    simp only [List.getElem?_cons_succ] at hb
    obtain ⟨hS, htag, hlabel⟩ := placed_getElem S ss _ hp.2.2.2 n b hb
    refine ⟨hS, by simp [htag]; omega, ?_⟩
    rw [hlabel]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    omega

end Placed

/-! ## Recorded programs that keep the counters -/

section Counted

variable {C : Committee} {E : Type}

theorem startsOf_append (r₁ r₂ : Record C E) : startsOf (r₁ ++ r₂) = startsOf r₁ ++ startsOf r₂ := by
  simp [startsOf, List.filterMap_append]

theorem mem_support_lift {α : Type} (p : PartyM C E RealSpec α) (z : Option α × List (RecEvent C E))
    (hz : z ∈ support (RecM.lift p).run.run) : z.2 = [] ∧ ∀ a, z.1 = some a → some a ∈ support p.run := by
  change z ∈ support (liftM p.run : WriterT (List (RecEvent C E)) _ _).run at hz
  simp only [WriterT.run_liftM, support_map, Set.mem_image] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  exact ⟨rfl, fun a h => by simpa [← h] using ho⟩

/-- A recorded program on the counters whose starts are `Placed` from the counters at its start, and
whose counters at a success are `after` its starts. -/
def Counted (S : BatchStart C → Prop) {β : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop :=
  ∀ st z, z ∈ support ((x.run st).run.run) →
    Placed S st (startsOf z.2) ∧ ∀ a st', z.1 = some (a, st') → st' = after st (startsOf z.2)

variable (S : BatchStart C → Prop)

theorem counted_pure {β : Type} (b : β) : Counted S (pure b : StateT (ℕ × ℕ) (RecM C E) β) := by
  intro st z hz
  simp at hz
  subst hz
  refine ⟨trivial, fun a st' h => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact (after_nil st).symm

theorem counted_bind {β γ : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) (f : β → StateT (ℕ × ℕ) (RecM C E) γ)
    (hx : Counted S x) (hf : ∀ b, Counted S (f b)) : Counted S (x >>= f) := by
  intro st z hz
  rw [StateT.run_bind] at hz
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · exact ⟨(hx st z₁ h₁).1, fun _ _ h => by cases h⟩
  · obtain ⟨hp₁, he₁⟩ := hx st z₁ h₁
    have hst := he₁ a.1 a.2 ha
    obtain ⟨hp₂, he₂⟩ := hf a.1 a.2 z₂ h₂
    rw [hst] at hp₂ he₂
    refine ⟨?_, fun b st' h => ?_⟩
    · simp only [startsOf_append]
      exact (placed_append S _ _ st).2 ⟨hp₁, hp₂⟩
    · simp only [startsOf_append, after_append]
      exact he₂ b st' h

theorem counted_liftS {β : Type} (y : PartyM C E RealSpec β) :
    Counted S (RecM.liftS (StateT.lift y : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)) := by
  intro st z hz
  obtain ⟨hlog, hval⟩ := mem_support_lift _ z hz
  rw [hlog]
  refine ⟨trivial, fun a st' h => ?_⟩
  have := (mem_support_lift_run y st (a, st') (hval _ h)).1
  simp only at this
  rw [this]
  exact (after_nil st).symm

end Counted

/-! ## The recorded program of one operator -/

section Program

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

/-- The public facts of a start of operator `i` with the keys `keys`. -/
def Shape (i : C.Party) (keys : Keys C) (b : BatchStart C) : Prop :=
  b.mode = settings.mode ∧ b.parameter = keys.parameter ∧ b.circuits = b.jobs.map (circuits keys.parameter ·.kind) ∧
    b.ctx.self = i ∧ b.ctx.keys = keys

theorem counted_recBatch (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (jobs : List Job) :
    Counted (E := E) (Shape circuits settings i keys) (recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter jobs) := by
  rintro ⟨L, k⟩ z hz
  rcases recBatch_counters K circuits settings _ _ jobs L k z hz with ⟨hs, hn⟩ | ⟨b, hs, hb, he⟩
  · rw [hs, hn]
    exact ⟨trivial, fun _ _ h => by cases h⟩
  · obtain ⟨hjobs, hmode, hpar, hcirc, hctx, htag, hlabel⟩ := hb
    rw [hs]
    refine ⟨⟨⟨hmode, hpar, by rw [hcirc, hjobs], by rw [hctx], by rw [hctx]⟩, htag, hlabel, trivial⟩,
      fun a st' h => ?_⟩
    rw [he a st' h]
    simp [after]

theorem counted_recRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    Counted (E := E) (Shape circuits settings i keys) (recRun K circuits settings i keys jobs) :=
  counted_bind _ _ _ (counted_liftS _ _) fun prss =>
    closed_batched (fun x => Counted (Shape circuits settings i keys) x) (counted_pure _) (counted_bind _) _ _
      (counted_recBatch K circuits settings i keys prss) jobs

theorem counted_ceremonyOutput (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    Counted (E := E) (Shape circuits settings i keys)
      (ceremonyOutput (m := StateT (ℕ × ℕ) (RecM C E)) (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa))))
        keys.parameter (recRun K circuits settings i keys) top tree) :=
  closed_ceremonyOutput (fun x => Counted (Shape circuits settings i keys) x) (counted_pure _) (counted_bind _) _
    (fun _ => counted_liftS _ _) _ (counted_recRun K circuits settings i keys) _ top tree

omit [Field E] [Algebra Bit E] in
/-- A recorded program whose continuation records nothing keeps the record of its first part. -/
theorem record_of_bind_silent {β γ : Type} (x : RecM C E β) (f : β → RecM C E γ)
    (hf : ∀ b, ∀ w ∈ support (f b).run.run, w.2 = []) (z : Option γ × List (RecEvent C E))
    (hz : z ∈ support (x >>= f).run.run) : ∃ z₁ ∈ support x.run.run, z.2 = z₁.2 := by
  obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨a, -, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · exact ⟨z₁, h₁, rfl⟩
  · exact ⟨z₁, h₁, by simp [hf a z₂ h₂]⟩

end Program

/-! ## The jobs of the first ceremony -/

section Jobs

variable {C : Committee} {E : Type}

/-- The jobs of the starts of a recorded program are a prefix of `J`, and all of `J` at a success. -/
def JobsIn (J : List (List Job)) {β : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop :=
  ∀ st z, z ∈ support ((x.run st).run.run) →
    (startsOf z.2).map (·.jobs) <+: J ∧ (z.1.isSome → (startsOf z.2).map (·.jobs) = J)

theorem jobsIn_pure {β : Type} (b : β) : JobsIn [] (pure b : StateT (ℕ × ℕ) (RecM C E) β) := by
  intro st z hz
  simp at hz
  subst hz
  simp [startsOf]

theorem jobsIn_bind {β γ : Type} (J₁ J₂ : List (List Job)) (x : StateT (ℕ × ℕ) (RecM C E) β)
    (f : β → StateT (ℕ × ℕ) (RecM C E) γ) (hx : JobsIn J₁ x) (hf : ∀ b, JobsIn J₂ (f b)) :
    JobsIn (J₁ ++ J₂) (x >>= f) := by
  intro st z hz
  rw [StateT.run_bind] at hz
  obtain ⟨z₁, h₁, ⟨hnone, rfl⟩ | ⟨a, ha, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · exact ⟨(hx st z₁ h₁).1.trans (List.prefix_append _ _), fun h => by cases h⟩
  · have he₁ := (hx st z₁ h₁).2 (by rw [ha]; rfl)
    obtain ⟨hp₂, he₂⟩ := hf a.1 a.2 z₂ h₂
    simp only [startsOf_append, List.map_append, he₁]
    exact ⟨(List.prefix_append_right_inj J₁).2 hp₂, fun h => by rw [he₂ h]⟩

theorem jobsIn_liftS {β : Type} (y : PartyM C E RealSpec β) :
    JobsIn [] (RecM.liftS (StateT.lift y : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)) := by
  intro st z hz
  obtain ⟨hlog, -⟩ := mem_support_lift _ z hz
  rw [hlog]
  simp [startsOf]

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem jobsIn_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    JobsIn [jobs] (recBatch K circuits settings ctx parameter jobs) := by
  rintro ⟨L, k⟩ z hz
  rcases recBatch_counters K circuits settings ctx parameter jobs L k z hz with ⟨hs, hn⟩ | ⟨b, hs, hb, -⟩
  · rw [hs, hn]
    simp
  · rw [hs]
    simp [hb.1]

theorem jobsIn_mapM (ctx : Context C) (parameter : PublicParameter) :
    ∀ l : List (List Job), JobsIn l (l.mapM (recBatch K circuits settings ctx parameter))
  | [] => jobsIn_pure _
  | js :: l => by
    rw [List.mapM_cons]
    have h : JobsIn ([js] ++ (l ++ [])) (recBatch K circuits settings ctx parameter js >>= fun a =>
        l.mapM (recBatch K circuits settings ctx parameter) >>= fun as => pure (a :: as)) :=
      jobsIn_bind _ _ _ _ (jobsIn_recBatch K circuits settings ctx parameter js) fun a =>
        jobsIn_bind _ _ _ _ (jobsIn_mapM ctx parameter l) fun as => jobsIn_pure _
    simpa using h

theorem jobsIn_recRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    JobsIn (chunks settings.batchSize jobs) (recRun K circuits settings i keys jobs) := by
  have h : JobsIn ([] ++ (chunks settings.batchSize jobs ++ [])) (recRun K circuits settings i keys jobs) :=
    jobsIn_bind _ _ _ _ (jobsIn_liftS _) fun prss => by
      unfold batched
      exact jobsIn_bind _ _ _ _ (jobsIn_mapM K circuits settings ⟨i, keys, prss⟩ keys.parameter
        (chunks settings.batchSize jobs)) fun _ => jobsIn_pure _
  rwa [List.nil_append, List.append_nil] at h

/-- The jobs of the first ceremony of a tree. -/
def firstJobs : Tree → List Job
  | .top => topJobs
  | .bottom b => bottomJobs b

omit [Field E] [Algebra Bit E] in
theorem getElem?_of_prefix {α : Type} {l J : List α} (h : l <+: J) (n : ℕ) (a : α) (ha : l[n]? = some a) :
    J[n]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1, ha]

end Jobs

/-! ## The honest steps of the ghost run with free oracle answers

The walk 74 to 232 with no fixed `H`. Each answer of an oracle is in the support
of its query, so it needs no good `H` that agrees with the final hash cache. -/

section Walk

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- Each output of the step is an output of the program. -/
def OnPathFree {α : Type} (program : OracleComp (PartySpec C E G) (Option α)) (step : Step C E G α) : Prop :=
  ∀ a, some a ∈ support (stepProgram step) → some a ∈ support program

variable (prims : Primitives) (Dw : C.Coalition)

/-- The local steps of an honest operator in `streamWorld` reach a step on the path of the program. -/
theorem advance_onPathFree {α : Type} (oa : OracleComp (PartySpec C E G) (Option α)) :
    ∀ s z, z ∈ support ((simulateQ (streamWorld prims Dw) (free (advance oa))).run s) → OnPathFree oa z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro s z hz
    simp only [advance_pure, free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun a ha => by simpa [stepProgram] using ha
  | query_bind t k ih =>
    intro s z hz
    rcases t with (q | outbox) | input
    · change z ∈ support ((simulateQ (streamWorld prims Dw) (free (OracleComp.lift
        (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)))).run s) at hz
      simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, -, hz⟩ := hz
      intro a hmem
      rw [mem_support_bind_iff]
      exact ⟨y.1, mem_support_query _ _, ih y.1 y.2 z hz a hmem⟩
    · change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (Step.wait outbox k)))).run s) at hz
      simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact fun _ ha => ha
    · change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (Step.call input k)))).run s) at hz
      simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact fun _ ha => ha

variable {α ρ : Type}

/-- A ghost step on the path of its recorded program. -/
def OnPathR (program : OracleComp (PartySpec C E G) (Option α × ρ)) (step : RStep C E G α ρ) : Prop :=
  OnPathFree (some <$> program) (GhostBatch.toStep step)

variable {prims Dw} in
/-- A done ghost step on the path of its program has its output and its record in the support of the
program. -/
theorem OnPathR.done {program : OracleComp (PartySpec C E G) (Option α × ρ)} {out : Option α} {record : ρ}
    (hpath : OnPathR program (.done out record)) : (out, record) ∈ support program := by
  have hmem := hpath (out, record) (by simp [GhostBatch.toStep, stepProgram])
  rw [support_map] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  cases hpe
  exact hp

theorem free_advanceR_onPathR (oa : OracleComp (PartySpec C E G) (Option α × ρ)) (s : HashCache C × HiddenCache C)
    (z : RStep C E G α ρ × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims Dw) (free (advanceR oa))).run s)) : OnPathR oa z.1 := by
  have hz' : (GhostBatch.toStep z.1, z.2) ∈
      support ((simulateQ (streamWorld prims Dw) (free (advance (some <$> oa)))).run s) := by
    rw [← GhostBatch.advanceR_toStep]
    change _ ∈ support ((simulateQ (streamWorld prims Dw) ((worldRoles (C := C)).honest
      (GhostBatch.toStep <$> advanceR oa))).run s)
    rw [worldRoles_honest_map, simulateQ_map, StateT.run_map, support_map]
    exact ⟨z, hz, rfl⟩
  exact advance_onPathFree prims Dw _ s _ hz'

/-- A round of the ghost run keeps each honest step on the path of its program. -/
theorem stepRoundR_onPathR {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (blank : ρ) (steps : C.Party → RStep C E RealSpec α ρ)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (s : HashCache C × HiddenCache C) (y : (A.State × (C.Party → RStep C E RealSpec α ρ) ×
      (C.Party → C.Party → Option (Msg E))) × (HashCache C × HiddenCache C))
    (hy : y ∈ support ((simulateQ (streamWorld prims Dw)
      (stepRoundR worldRoles D' A noFunctionality blank st steps)).run s)) :
    (∀ i, i ∉ D'.1 → OnPathR (program i) (steps i)) → ∀ i, i ∉ D'.1 → OnPathR (program i) (y.1.2.1 i) := by
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
  obtain ⟨a, -, w, hw, rfl⟩ := hy
  have hseq := sequenceFin_streamWorld prims Dw (fun j v _ => j ∉ D'.1 →
      OnPathR (program j) (steps j) → OnPathR (program j) v) _
    (fun j b c c' hq _ => hq) (fun j s' y hy hj hon => ?_) a.2 w hw
  · exact fun hon i hi => hseq i hi (hon i hi)
  rcases hsj : steps j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [← hsj]
    exact hon
  · simp only [hsj, hj, ↓reduceIte] at hy
    have hpath := free_advanceR_onPathR prims Dw _ s' y hy
    intro a' hmem
    rw [hsj] at hon
    refine hon a' ?_
    simp only [GhostBatch.toStep, stepProgram]
    rw [mem_support_bind_iff]
    exact ⟨_, mem_support_query _ _, hpath a' hmem⟩
  · exact input.elim

/-- The rounds of the ghost run keep each honest step on the path of its program. -/
theorem executeRoundsR_onPathR {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) (fuel : ℕ) :
    ∀ st steps s z, z ∈ support ((simulateQ (streamWorld prims Dw)
      (executeRoundsR worldRoles D' A noFunctionality blank fuel st steps)).run s) →
      (∀ i, i ∉ D'.1 → OnPathR (program i) (steps i)) → ∀ i, i ∉ D'.1 → OnPathR (program i) (z.1.2 i) := by
  induction fuel with
  | zero =>
    intro st steps s z hz
    simp only [executeRoundsR, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun hon => hon
  | succ fuel ih =>
    intro st steps s z hz
    unfold executeRoundsR at hz
    split_ifs at hz with hdone
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact fun hon => hon
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rcases y with ⟨⟨state, steps', sent⟩, c⟩
      have hstep := stepRoundR_onPathR prims Dw D' A st blank steps program s _ hy
      exact fun hon => ih state steps' c z hz (hstep hon)

/-- A phase of the ghost run ends with each honest step on the path of its program. -/
theorem executePhaseR_onPathR {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ)
    (fuel : ℕ) (st : A.State) (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (s : HashCache C × HiddenCache C) (z : (A.State × (C.Party → RStep C E RealSpec α ρ)) × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims Dw)
      (executePhaseR worldRoles D' A noFunctionality blank fuel st program)).run s)) :
    ∀ i, i ∉ D'.1 → OnPathR (program i) (z.1.2 i) := by
  unfold executePhaseR at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startStepsR at hy
  have hstart := sequenceFin_streamWorld prims Dw (fun j v _ => j ∉ D'.1 → OnPathR (program j) v) _
    (fun j b c c' hq _ => hq) (fun j s' w hw hj => ?_) s y hy
  · exact executeRoundsR_onPathR prims Dw D' A blank program fuel st y.1 y.2 z hz hstart
  simp only [hj, ↓reduceIte] at hw
  exact free_advanceR_onPathR prims Dw _ s' w hw

end Walk

/-! ## The counters on the ghost run -/

section Ghost

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)
  (budget : StartBudget)

/-- Two honest operators with keys hold one parameter when the seeds do not differ. -/
theorem parameter_eq_of_seeds (D : C.Coalition) (keys : C.Party → Option (Keys C))
    (hseeds : seedsDiffer D keys = false) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) (ki kj : Keys C)
    (hki : keys i = some ki) (hkj : keys j = some kj) : ki.parameter = kj.parameter := by
  by_contra hne
  have : seedsDiffer D keys = true := by
    unfold seedsDiffer
    exact decide_eq_true ⟨i, j, ki, kj, hi, hj, hki, hkj, Or.inl hne⟩
  rw [hseeds] at this
  cases this

theorem take_map_eq {α β : Type} (f : α → β) (l l' : List α) (k : ℕ)
    (h : ∀ n < k, (l[n]?).map f = (l'[n]?).map f) : (l.take k).map f = (l'.take k).map f := by
  refine List.ext_getElem? fun n => ?_
  simp only [List.getElem?_map, List.getElem?_take]
  split_ifs with hn
  · exact h n hn
  · rfl

end Ghost

end BatchCounters

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostBatch.recOkS_recRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostBatch.recOkS_recRun

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.BatchCounters.counted_recRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.BatchCounters.counted_recRun
