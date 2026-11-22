import ThresholdLeanXmss.Ideal
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutRun
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RecordedRun

/-!
# The replay of the monitor on the recorded run

`streamWorld_preservesInv` states that each call of `streamWorld` keeps `NoMpc` on the hash cache. The
section `GhostMonitor` gives the balance and the condition of the record of `recRun` (`balR_recRun`,
`condR_recRun`) and of the ceremony output (`condR_ceremonyOutput`), and replays the reference of the
monitor on the cache (`RefW`). The section `MpcCells` removes the MPC cells from a cache
(`cleanCache`). A computation in `streamWorld` from the clean world is the computation with its final
world cleaned (`streamWorld_run_clean`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## One call of the stream world -/

section World

variable {C : Committee} (prims : Primitives)

/-- The programming call keeps `NoMpc`. It writes no cell on an input of the MPC. -/
theorem programAnswer_preservesInv (x : Query C × HashOutput) :
    StateT.PreservesInv (programAnswer x) (NoMpc (C := C)) := by
  intro s hs z hz
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hg
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    intro y hy
    have hne : Query.hash y ≠ x.1 := fun he => hg (Or.inl ⟨y, he.symm, hy⟩)
    show (s.cacheQuery x.1 x.2) (.hash y) = none
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    exact hs y hy

theorem localAnswer_preservesInv (t : (LocalSpec C).Domain) :
    StateT.PreservesInv (localAnswer prims t) (NoMpc (C := C)) :=
  fun s hs p hp => (localAnswer_support (fun _ => 0) t s p hp).2.1 hs

theorem onHash_preservesInv {α : Type} {m : StateT (HashCache C) ProbComp α}
    (hm : StateT.PreservesInv m (NoMpc (C := C))) :
    StateT.PreservesInv (onHash m) fun st : StreamState C => NoMpc st.1 := by
  intro st hst z hz
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact hm st.1 hst r hr

/-- Each call of `streamWorld` keeps `NoMpc` on the hash cache. -/
theorem streamWorld_preservesInv (D : C.Coalition) :
    QueryImpl.PreservesInv (streamWorld prims D) fun st : StreamState C => NoMpc st.1 := by
  rintro ((t | p) | (u | q | x))
  · exact onHash_preservesInv (localAnswer_preservesInv prims t)
  · exact onHash_preservesInv (programAnswer_preservesInv p)
  · exact onHash_preservesInv (localAnswer_preservesInv prims _)
  · exact onHash_preservesInv (localAnswer_preservesInv prims _)
  · show StateT.PreservesInv (if Hidden D x.1 then _ else _) _
    split_ifs
    · intro st hst z hz
      simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨r, -, rfl⟩ := hz
      exact hst
    · exact onHash_preservesInv (localAnswer_preservesInv prims _)

/-- Each computation in `streamWorld` from a start with `NoMpc` ends with `NoMpc`. -/
theorem streamWorld_noMpc (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (world : StreamState C) (h : NoMpc world.1) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run world), NoMpc z.2.1 :=
  OracleComp.simulateQ_run_preservesInv _ _ (streamWorld_preservesInv prims D) oa world h

/-- A cache with `NoMpc` agrees with a good `H`, namely `hashOf`. -/
theorem exists_good_agrees {s : HashCache C} (h : NoMpc s) : ∃ hf, Good prims hf ∧ Agrees hf s :=
  ⟨hashOf prims s, good_hashOf prims s, agrees_hashOf prims h⟩

end World

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace GhostMonitor

attribute [local instance] Classical.propDecidable

/-! ## The support with `H` fixed -/

section Support

variable {C : Committee} {E : Type}

/-- With `H` fixed to `h`, a program has only outcomes of the program. -/
theorem support_fixHash_subset {ι : Type} {G : OracleSpec ι} (h : Query C → HashOutput) {α : Type}
    (oa : OracleComp (PartySpec C E G) α) : support (simulateQ (fixHash h) oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro z hz
    rw [simulateQ_bind, simulateQ_query, mem_support_bind_iff] at hz
    obtain ⟨r, -, hz⟩ := hz
    rw [mem_support_bind_iff]
    exact ⟨r, by simp, ih r hz⟩

/-- The decomposition of an outcome of a bind of recorded programs with `H` fixed. -/
theorem mem_support_fix_bind (h : Query C → HashOutput) {α β : Type} (x : RecM C E α) (f : α → RecM C E β)
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

/-- An outcome of a program with no record has the empty record. -/
theorem mem_support_fix_lift (h : Query C → HashOutput) {α : Type} (p : PartyM C E RealSpec α)
    (z : Option α × List (RecEvent C E)) (hz : z ∈ support (simulateQ (fixHash h) (RecM.lift p).run.run)) :
    z.2 = [] ∧ z.1 ∈ support (simulateQ (fixHash h) p.run) := by
  change z ∈ support (simulateQ (fixHash h) (liftM p.run : WriterT (List (RecEvent C E)) _ _).run) at hz
  rw [WriterT.run_liftM, simulateQ_map, support_map] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  exact ⟨rfl, ho⟩

end Support

/-! ## The records of the batches -/

section Records

variable {C : Committee} {E : Type}

theorem startsOf_append (r₁ r₂ : Record C E) : startsOf (r₁ ++ r₂) = startsOf r₁ ++ startsOf r₂ := by
  simp [startsOf, List.filterMap_append]

theorem batchOutputsOf_append (r₁ r₂ : Record C E) :
    batchOutputsOf (r₁ ++ r₂) = batchOutputsOf r₁ ++ batchOutputsOf r₂ := by
  simp [batchOutputsOf, List.filterMap_append]

/-- A record has as many batch outputs as starts of checks. -/
def Balanced (record : Record C E) : Prop := (startsOf record).length = (batchOutputsOf record).length

theorem Balanced.append {r₁ r₂ : Record C E} (h₁ : Balanced r₁) (h₂ : Balanced r₂) : Balanced (r₁ ++ r₂) := by
  unfold Balanced at *
  rw [startsOf_append, batchOutputsOf_append, List.length_append, List.length_append, h₁, h₂]

/-- The first `N` batches of a record are right. -/
def RightUpTo (right : BatchStart C → List (List Bit) → Prop) (N : ℕ) (record : Record C E) : Prop :=
  ∀ k < N, ∀ b out, (startsOf record)[k]? = some b → (batchOutputsOf record)[k]? = some out → right b out

theorem rightUpTo_left {right : BatchStart C → List (List Bit) → Prop} {N : ℕ} {r₁ r₂ : Record C E}
    (hb : Balanced r₁) (hr : RightUpTo right N (r₁ ++ r₂)) : RightUpTo right N r₁ := by
  intro k hk b out hs ho
  have hlt : k < (startsOf r₁).length := (List.getElem?_eq_some_iff.1 hs).1
  refine hr k hk b out ?_ ?_
  · rw [startsOf_append, List.getElem?_append_left hlt]
    exact hs
  · rw [batchOutputsOf_append, List.getElem?_append_left (hb ▸ hlt)]
    exact ho

theorem rightUpTo_right {right : BatchStart C → List (List Bit) → Prop} {N M : ℕ} {r₁ r₂ : Record C E}
    (hb : Balanced r₁) (hlen : (startsOf r₁).length ≤ N) (hr : RightUpTo right (N + M) (r₁ ++ r₂)) :
    RightUpTo right M r₂ := by
  intro k hk b out hs ho
  refine hr ((startsOf r₁).length + k) (by omega) b out ?_ ?_
  · rw [startsOf_append, List.getElem?_append_right (by omega)]
    simpa using hs
  · rw [batchOutputsOf_append, List.getElem?_append_right (by rw [← hb]; omega), hb]
    simpa using ho

end Records

/-! ## Balanced records -/

section Balance

variable {C : Committee} {E : Type}

/-- Each outcome of `x` with a value has a balanced record. -/
def BalR {β : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop :=
  ∀ st z, z ∈ support ((x.run st).run.run) → ∀ a st', z.1 = some (a, st') → Balanced z.2

theorem balR_pure {β : Type} (b : β) : BalR (pure b : StateT (ℕ × ℕ) (RecM C E) β) := by
  intro st z hz a st' _
  simp at hz
  subst hz
  rfl

theorem balR_bind {β γ : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) (f : β → StateT (ℕ × ℕ) (RecM C E) γ)
    (hx : BalR x) (hf : ∀ b, BalR (f b)) : BalR (x >>= f) := by
  intro st z hz a st' hza
  rw [StateT.run_bind] at hz
  obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨p, hp, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · cases hza
  · obtain ⟨c, st₁⟩ := p
    exact (hx st z₁ h₁ c st₁ hp).append (hf c st₁ z₂ h₂ a st' hza)

theorem balR_liftS {β : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) : BalR (RecM.liftS x) := by
  intro st z hz a st' _
  change z ∈ support (liftM (x.run st).run : WriterT (List (RecEvent C E)) _ _).run at hz
  rw [WriterT.run_liftM, support_map] at hz
  obtain ⟨o, -, rfl⟩ := hz
  rfl

end Balance

/-! ## The record of one batch -/

section BatchRecord

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- An outcome of `recCheckOpen b` with a value records the start `b`, the opening of `b.v'` and
the batch output, and it gives this output. -/
theorem recCheckOpen_complete (b : BatchStart C) (k : ℕ) (st : ℕ × ℕ)
    (z : Option (Option (List (List Bit)) × (ℕ × ℕ)) × Record C E)
    (hz : z ∈ support ((recCheckOpen K b k).run st).run.run) (a : Option (List (List Bit))) (st' : ℕ × ℕ)
    (hza : z.1 = some (a, st')) :
    ∃ inbox out, z.2 = [RecEvent.start b, RecEvent.opened b.v' inbox, RecEvent.output out] ∧ a = some out := by
  unfold recCheckOpen at hz
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_set,
    StateT.run_pure] at hz
  obtain ⟨z₁, h₁, rfl⟩ := mem_support_record_bind _ _ z hz
  rcases mem_support_lift_bind _ _ z₁ h₁ with rfl | ⟨p, z₂, h₂, rfl⟩
  · cases hza
  rcases mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, z₃, h₃, rfl⟩
  · cases hza
  rcases mem_support_lift_bind _ _ _ h₃ with rfl | ⟨p₂, z₄, h₄, rfl⟩
  · cases hza
  obtain ⟨z₅, h₅, rfl⟩ := mem_support_record_bind _ _ _ h₄
  rcases mem_support_lift_bind _ _ _ h₅ with rfl | ⟨p₃, z₆, h₆, rfl⟩
  · cases hza
  obtain ⟨z₇, h₇, rfl⟩ := mem_support_record_bind _ _ _ h₆
  simp at h₇
  subst h₇
  simp only [Option.some.injEq, Prod.mk.injEq] at hza
  exact ⟨p₂.1, _, by simp, hza.1.symm⟩

/-- An outcome of `recBatch` with a value records one start of the jobs and the parameter of the
batch, the opening and the batch output, and it gives this output. -/
theorem recBatch_complete (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ)
    (z : Option (Option (List (List Bit)) × (ℕ × ℕ)) × Record C E)
    (hz : z ∈ support ((recBatch K circuits settings ctx parameter jobs).run st).run.run)
    (a : Option (List (List Bit))) (st' : ℕ × ℕ) (hza : z.1 = some (a, st')) :
    ∃ b : BatchStart C, b.jobs = jobs ∧ b.parameter = parameter ∧ ∃ inbox out,
      z.2 = [RecEvent.start b, RecEvent.opened b.v' inbox, RecEvent.output out] ∧ a = some out := by
  rcases st with ⟨label, k⟩
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_lift] at hz
  rcases mem_support_lift_bind _ _ z hz with rfl | ⟨p, z₂, h₂, rfl⟩
  · cases hza
  rcases mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, z₃, h₃, rfl⟩
  · cases hza
  rcases mem_support_lift_bind _ _ _ h₃ with rfl | ⟨p₂, z₄, h₄, rfl⟩
  · cases hza
  exact ⟨_, rfl, rfl, recCheckOpen_complete K _ _ _ _ h₄ a st' hza⟩

end BatchRecord

/-! ## Graded soundness of a recorded program -/

section Graded

variable {C : Committee} {E : Type} (h : Query C → HashOutput) (right : BatchStart C → List (List Bit) → Prop)

/-- Each outcome of `x` with `H` fixed to `h` and a value, whose first `N` batches are right, has at
most `N` batches and a value with `P`. -/
def CondR (N : ℕ) {β : Type} (P : β → Prop) (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop :=
  ∀ st z, z ∈ support (simulateQ (fixHash h) ((x.run st).run.run)) → ∀ a st', z.1 = some (a, st') →
    RightUpTo right N z.2 → (startsOf z.2).length ≤ N ∧ P a

theorem condR_pure {β : Type} (P : β → Prop) (b : β) (hb : P b) :
    CondR (E := E) h right 0 P (pure b) := by
  intro st z hz a st' hza _
  simp at hz
  subst hz
  simp only [Option.some.injEq, Prod.mk.injEq] at hza
  obtain ⟨rfl, -⟩ := hza
  exact ⟨by simp [startsOf], hb⟩

variable {h right}

theorem condR_mono {β : Type} {N N' : ℕ} {P : β → Prop} {x : StateT (ℕ × ℕ) (RecM C E) β}
    (hx : CondR h right N P x) (hle : N ≤ N') : CondR h right N' P x := by
  intro st z hz a st' hza hr
  obtain ⟨hlen, hP⟩ := hx st z hz a st' hza fun k hk => hr k (by omega)
  exact ⟨hlen.trans hle, hP⟩

theorem condR_bind {β γ : Type} {n k : ℕ} {Q : β → Prop} {P : γ → Prop} {x : StateT (ℕ × ℕ) (RecM C E) β}
    {f : β → StateT (ℕ × ℕ) (RecM C E) γ} (hx : CondR h right n Q x) (hbal : BalR x)
    (hf : ∀ b, Q b → CondR h right k P (f b)) : CondR h right (n + k) P (x >>= f) := by
  intro st z hz a st' hza hr
  rw [StateT.run_bind] at hz
  obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨p, hp, z₂, h₂, rfl⟩⟩ := mem_support_fix_bind h _ _ z hz
  · cases hza
  · obtain ⟨c, st₁⟩ := p
    have hb₁ := hbal st z₁ (support_fixHash_subset h _ h₁) c st₁ hp
    obtain ⟨hlen₁, hQ⟩ := hx st z₁ h₁ c st₁ hp fun j hj => rightUpTo_left hb₁ hr j (by omega)
    obtain ⟨hlen₂, hP⟩ := hf c hQ st₁ z₂ h₂ a st' hza (rightUpTo_right hb₁ hlen₁ hr)
    refine ⟨?_, hP⟩
    rw [startsOf_append, List.length_append]
    omega

theorem condR_liftS {β : Type} (P : β → Prop) (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hx : ∀ st o, o ∈ support (simulateQ (fixHash h) (x.run st).run) → ∀ b st', o = some (b, st') → P b) :
    CondR h right 0 P (RecM.liftS x) := by
  intro st z hz a st' hza _
  obtain ⟨hnil, ho⟩ := mem_support_fix_lift h (x.run st) z hz
  rw [hnil]
  exact ⟨by simp [startsOf], hx st _ ho a st' hza⟩

theorem condR_true {β : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) :
    CondR h right 0 (fun _ => True) (RecM.liftS x) :=
  condR_liftS _ x fun _ _ _ _ _ _ => trivial

variable (h right) in
theorem condR_hash (prims : Primitives) {β : Type} (oa : OracleComp HashSpec β) :
    CondR h right 0 (· = D prims h (tweakable oa))
      (RecM.liftS (StateT.lift (oracleStep (tweakable oa))) : StateT (ℕ × ℕ) (RecM C E) β) := by
  refine condR_liftS _ _ fun st o ho b st' hob => ?_
  subst hob
  rw [StateT.run_lift, OptionT.run_bind, Option.elimM, simulateQ_bind,
    fixHash_oracleStep_tweakable prims h oa, pure_bind] at ho
  simp at ho
  exact ho.1

theorem condR_mapM {β γ : Type} (f : β → StateT (ℕ × ℕ) (RecM C E) γ) (g : β → γ)
    (hf : ∀ b, CondR h right 1 (· = g b) (f b)) (hb : ∀ b, BalR (f b)) :
    ∀ l : List β, CondR h right l.length (· = l.map g) (l.mapM f)
  | [] => condR_pure h right _ _ rfl
  | b :: l => by
    rw [List.mapM_cons]
    refine condR_mono (condR_bind (hf b) (hb b) fun c hc => condR_bind (condR_mapM f g hf hb l)
      (closed_mapM (fun x => BalR x) balR_pure balR_bind f hb l) fun cs hcs => condR_pure h right _ _ ?_)
      (by simp; omega)
    rw [hc, hcs, List.map_cons]

theorem condR_batched (size : ℕ) (run : List Job → StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))))
    (run' : List Job → Option (List (List Bit))) (hr : ∀ js, CondR h right 1 (· = run' js) (run js))
    (hb : ∀ js, BalR (run js)) (jobs : List Job) :
    CondR h right (chunks size jobs).length (· = batched (m := Id) size run' jobs) (batched size run jobs) := by
  unfold batched
  refine condR_mono (condR_bind (condR_mapM run run' hr hb _) (closed_mapM (fun x => BalR x) balR_pure balR_bind
    run hb _) fun outs houts => condR_pure h right _ _ ?_) (by omega)
  rw [houts, id_bind_eq, id_mapM]
  rfl

theorem chunks_signJobs_length (size : ℕ) (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    (chunks size (signJobs b encoding)).length = (chunks size (signJobs b fun _ => digit 0)).length := by
  simp [chunks, signJobs]

/-- The
grade of a tree is `treeBatches`. -/
theorem condR_ceremonyOutput (settings : Settings)
    (lift : ∀ {β : Type}, OracleComp HashSpec β → StateT (ℕ × ℕ) (RecM C E) β)
    (lift' : ∀ {β : Type}, OracleComp HashSpec β → β)
    (hl : ∀ {β : Type} (oa : OracleComp HashSpec β), CondR h right 0 (· = lift' oa) (lift oa))
    (hlb : ∀ {β : Type} (oa : OracleComp HashSpec β), BalR (lift oa))
    (run : List Job → StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))))
    (run' : List Job → Option (List (List Bit)))
    (hr : ∀ js, CondR h right (chunks settings.batchSize js).length (· = run' js) (run js))
    (hrb : ∀ js, BalR (run js)) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    CondR h right (treeBatches settings tree)
      (· = ceremonyOutput (m := Id) (fun oa => lift' oa) parameter run' top tree)
      (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine condR_mono (condR_bind (k := 0) (hr topJobs) (hrb _) fun o ho => ?_) (by simp [treeBatches])
    subst ho
    rcases run' topJobs with _ | outputs
    · exact condR_pure h right _ _ rfl
    · refine condR_mono (condR_bind (k := 0) (hl _) (hlb _) fun root hroot => condR_pure h right _ _ ?_) le_rfl
      subst hroot
      rfl
  | bottom b =>
    simp only [ceremonyOutput, id_bind_eq]
    refine condR_mono
      (condR_bind (k := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length) (hr (bottomJobs b))
        (hrb _) fun o ho => ?_) (by simp [treeBatches])
    subst ho
    rcases run' (bottomJobs b) with _ | outputs
    · exact condR_mono (condR_pure h right _ _ rfl) (Nat.zero_le _)
    · refine condR_mono (condR_bind (hl _) (hlb _) fun root hroot => ?_) (Nat.zero_add _).le
      subst hroot
      refine condR_mono (condR_bind (hl _) (hlb _) fun base hbase => ?_) (Nat.zero_add _).le
      subst hbase
      refine condR_mono (condR_bind (hl _) (hlb _) fun g hg => ?_) (Nat.zero_add _).le
      simp only [← hg]
      rcases g with _ | ⟨randomness, encoding⟩
      · exact condR_mono (condR_pure h right _ _ rfl) (Nat.zero_le _)
      · refine condR_mono (condR_bind (k := 0) (hr _) (hrb _) fun o ho => ?_)
          (by rw [chunks_signJobs_length]; simp)
        simp only [← ho]
        rcases o with _ | values
        · exact condR_pure h right _ _ rfl
        · refine condR_mono (condR_bind (k := 0) (hl _) (hlb _) fun path hpath => ?_) le_rfl
          subst hpath
          refine condR_mono (condR_bind (k := 0) (hl _) (hlb _) fun topRoot htopRoot => ?_) le_rfl
          simp only [← htopRoot]
          split_ifs
          · exact condR_pure h right _ _ rfl
          · exact condR_pure h right _ _ rfl

end Graded

/-! ## The recorded program with right batches -/

section Program

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings) (prims : Primitives)

/-- A batch start `b` with the output `out` is right for `h` on `seeds`. -/
def RightAt (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (b : BatchStart C) (out : List (List Bit)) :
    Prop :=
  RightBatch prims circuits h b.parameter seeds b.jobs (some out)

omit [Fintype E] [DecidableEq E] in
theorem balR_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    BalR (recBatch K circuits settings ctx parameter jobs) := by
  intro st z hz a st' hza
  obtain ⟨b, -, -, inbox, out, hz2, -⟩ := recBatch_complete K circuits settings ctx parameter jobs st z hz a st' hza
  rw [hz2]
  simp [Balanced, startsOf, batchOutputsOf]

omit [Fintype E] [DecidableEq E] in
theorem condR_recBatch (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (ctx : Context C)
    (parameter : PublicParameter) (jobs : List Job) :
    CondR h (RightAt circuits prims h seeds) 1
      (· = some (jobs.map fun job => D prims h (evalJob circuits parameter seeds job)))
      (recBatch K circuits settings ctx parameter jobs) := by
  intro st z hz a st' hza hr
  obtain ⟨b, hjobs, hparameter, inbox, out, hz2, rfl⟩ :=
    recBatch_complete K circuits settings ctx parameter jobs st z (support_fixHash_subset h _ hz) a st' hza
  rw [hz2] at hr ⊢
  refine ⟨by simp [startsOf], ?_⟩
  have hright := hr 0 Nat.one_pos b out (by simp [startsOf]) (by simp [batchOutputsOf])
  unfold RightAt RightBatch at hright
  rw [hright, hjobs, hparameter]

omit [Fintype E] [DecidableEq E] in
theorem balR_recRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    BalR (recRun K circuits settings i keys jobs) :=
  balR_bind _ _ (balR_liftS _) fun _ =>
    closed_batched (fun x => BalR x) balR_pure balR_bind _ _ (balR_recBatch K circuits settings _ _) jobs

omit [Fintype E] [DecidableEq E] in
theorem condR_recRun (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (hsize : 0 < settings.batchSize)
    (i : C.Party) (keys : Keys C) (jobs : List Job) :
    CondR h (RightAt circuits prims h seeds) (chunks settings.batchSize jobs).length
      (· = evalRun prims circuits keys.parameter seeds h jobs) (recRun K circuits settings i keys jobs) := by
  rw [evalRun_eq, ← batched_id settings.batchSize hsize]
  refine condR_mono (condR_bind (condR_true _) (balR_liftS _) fun prss _ => ?_) (Nat.zero_add _).le
  exact condR_batched _ _ _ (fun js => condR_recBatch K circuits settings prims h seeds _ _ js)
    (fun js => balR_recBatch K circuits settings _ _ js) jobs

end Program

/-! ## A computation of `H` on the free copy of `streamWorld` -/

section Reference

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- From a cache that agrees with a good `h`, some answer of `H` is `h q` with a cache that agrees
with `h`. -/
theorem hashAnswer_exists (q : Query C) (s : HashCache C) (h : Query C → HashOutput) (hg : Good prims h)
    (ha : Agrees h s) : ∃ p ∈ support ((hashAnswer prims q).run s), p.1 = h q ∧ Agrees h p.2 := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm]
    exact ⟨(prims.Th input, s), by simp, (hg input hm).symm, ha⟩
  · rw [hashAnswer_of_not_isFixed prims hq]
    rcases hs : s q with _ | u
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs]
      refine ⟨(h q, QueryCache.cacheQuery s q (h q)), ?_, rfl, ?_⟩
      · rw [support_map]
        exact ⟨h q, by simp [uniformSampleImpl], rfl⟩
      · intro q' v hv
        by_cases hqq : q' = q
        · subst hqq
          simp at hv
          exact hv
        · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hv
          exact ha q' v hv
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs]
      exact ⟨(u, s), by simp, (ha q u hs).symm, ha⟩

/-- The runs of a computation on the free copy of `streamWorld` have the value with `H` fixed to
each good `h` that agrees with the end cache, and from each cache that agrees with a good `h` one run
has this value and an end cache that agrees with `h`. A computation of `H` alone has this property. -/
def RefW {α : Type} (oa : OracleComp (RoSpec C) α) : Prop :=
  (∀ s z, z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp oa (LocalSpec C)))).run s) →
      ∀ h, Good prims h → Agrees h z.2.1 → z.1 = ThresholdLeanXmssSecurity.D prims h oa) ∧
    ∀ s h, Good prims h → Agrees h s.1 →
      ∃ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp oa (LocalSpec C)))).run s),
        z.1 = ThresholdLeanXmssSecurity.D prims h oa ∧ Agrees h z.2.1

theorem refW_pure {α : Type} (a : α) : RefW prims D (pure a : OracleComp (RoSpec C) α) := by
  refine ⟨fun s z hz h _ _ => ?_, fun s h _ ha => ⟨(a, s), by simp [free], rfl, ha⟩⟩
  simp [free] at hz
  rw [hz]
  rfl

theorem refW_bind {α β : Type} (x : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β)
    (hx : RefW prims D x) (hf : ∀ a, RefW prims D (f a)) : RefW prims D (x >>= f) := by
  refine ⟨fun s z hz h hg ha => ?_, fun s h hg ha => ?_⟩
  · simp only [liftComp_bind, free, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hle := streamWorld_run_mono prims D _ y.2 z hz
    rw [D_bind, ← hx.1 s y hy h hg (ha.mono hle)]
    exact (hf y.1).1 y.2 z hz h hg ha
  · obtain ⟨y, hy, hyv, hya⟩ := hx.2 s h hg ha
    obtain ⟨z, hz, hzv, hza⟩ := (hf y.1).2 y.2 h hg hya
    refine ⟨z, ?_, ?_, hza⟩
    · simp only [liftComp_bind, free, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨y, hy, hz⟩
    · rw [hzv, D_bind, hyv]

theorem refW_hashQuery (q : Query C) : RefW prims D (hashQuery q) := by
  have hrun : ∀ s, (simulateQ (streamWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C)))).run s =
      (onHash (hashAnswer prims q)).run s := fun s => by
    rw [show free (liftComp (hashQuery q) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) _) from rfl,
      simulateQ_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rfl
  refine ⟨fun s z hz h hg ha => ?_, fun s h hg ha => ?_⟩
  · rw [hrun] at hz
    obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s z hz
    rw [D_hashQuery]
    exact ((hashAnswer_support q s.1 r hr).2.2 h hg ha).symm
  · obtain ⟨p, hp, hpv, hpa⟩ := hashAnswer_exists prims q s.1 h hg ha
    refine ⟨(p.1, (p.2, s.2)), ?_, by rw [D_hashQuery]; exact hpv, hpa⟩
    rw [hrun]
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image]
    exact ⟨p, hp, rfl⟩

theorem refW_map {α β : Type} (f : α → β) (x : OracleComp (RoSpec C) α) (hx : RefW prims D x) :
    RefW prims D (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact refW_bind prims D _ _ hx fun _ => refW_pure prims D _

theorem refW_tweakable {α : Type} (oa : OracleComp HashSpec α) : RefW prims D (tweakable (C := C) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rw [tweakable_pure]; exact refW_pure prims D a
  | query_bind t k ih =>
    rw [tweakable_bind]
    refine refW_bind prims D _ _ ?_ ih
    simpa [tweakable] using refW_hashQuery prims D (.hash t)

theorem refW_prfValue (seeds : C.Term → HashOutput) (x : Point) : RefW prims D (prfValue seeds x) :=
  refW_bind prims D _ _ (closed_mapM (fun oa => RefW prims D oa) (refW_pure prims D) (refW_bind prims D) _
    (fun _ => refW_map prims D _ _ (refW_hashQuery prims D _)) _) fun _ => refW_pure prims D _

theorem refW_referenceJob (seeds : C.Term → HashOutput) (parameter : PublicParameter) (job : Job) :
    RefW prims D (referenceJob (fun oa => tweakable oa) (prfValue seeds) parameter job) := by
  unfold referenceJob
  refine refW_bind prims D _ _ (closed_mapM (fun oa => RefW prims D oa) (refW_pure prims D) (refW_bind prims D) _
    (refW_prfValue prims D seeds) _) fun values => ?_
  split
  · exact refW_map prims D _ _ (refW_tweakable prims D _)
  · exact refW_bind prims D _ _ (refW_tweakable prims D _) fun _ => refW_bind prims D _ _ (refW_tweakable prims D _)
      fun _ => refW_bind prims D _ _ (refW_tweakable prims D _) fun _ => refW_pure prims D _
  · exact refW_map prims D _ _ (refW_tweakable prims D _)
  · exact refW_map prims D _ _ (refW_tweakable prims D _)
  · exact refW_pure prims D _

theorem refW_referenceTree (seeds : C.Term → HashOutput) (parameter : PublicParameter) (top : TopTree)
    (tree : Tree) : RefW prims D (referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter top tree) :=
  closed_ceremonyOutput (fun oa => RefW prims D oa) (refW_pure prims D) (refW_bind prims D) _
    (fun oa => refW_tweakable prims D oa) _
    (fun js => refW_map prims D _ _ (closed_mapM (fun oa => RefW prims D oa) (refW_pure prims D) (refW_bind prims D) _
      (refW_referenceJob prims D seeds parameter) js)) parameter top tree

/-- The reference of `wrongOutput`, the output of `referenceTree` on the seeds and the parameter of
the game, with the reference top tree for a bottom tree. It is irreducible, so that the elaborator
does not unfold a hypothesis on its runs. -/
@[irreducible] def monitorReference (D : C.Coalition) (keys : C.Party → Option (Keys C)) (tree : Tree) :
    OracleComp (RoSpec C) (Option TreeOutput) := do
  let top ← referenceTree (fun oa => tweakable oa) (prfValue (gameSeeds D keys)) (gameParameter D keys) emptyTop .top
  match tree, TreeOutput.topTree top with
  | .top, _ => pure top
  | .bottom b, some topTree =>
    referenceTree (fun oa => tweakable oa) (prfValue (gameSeeds D keys)) (gameParameter D keys) topTree (.bottom b)
  | .bottom _, none => pure none

theorem wrongOutput_eq (D : C.Coalition) (keys : C.Party → Option (Keys C)) (tree : Tree)
    (outputs : C.Party → Option TreeOutput) :
    wrongOutput D keys tree outputs = (do
      let reference ← free (liftComp (monitorReference D keys tree) (LocalSpec C))
      pure (decide (∃ i, i ∉ D.1 ∧ (outputs i).isSome ∧ outputs i ≠ reference))) := by
  unfold monitorReference
  rfl

theorem refW_monitorReference (D : C.Coalition) (keys : C.Party → Option (Keys C)) (tree : Tree) :
    RefW prims D (monitorReference D keys tree) := by
  unfold monitorReference
  refine refW_bind prims D _ _ (refW_referenceTree prims D _ _ _ _) fun top => ?_
  rcases tree with _ | b
  · exact refW_pure prims D _
  · rcases TreeOutput.topTree top with _ | topTree
    · exact refW_pure prims D _
    · exact refW_referenceTree prims D _ _ _ _

/-- A run of a computation of `H` from a cache that agrees with a good `h` has the value with `H`
fixed to `h`, so a property of all outcomes holds for this value. -/
theorem refW_forall {α : Type} {oa : OracleComp (RoSpec C) α} (hW : RefW prims D oa) (s : StreamState C)
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h s.1) (P : α → Prop)
    (hP : ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp oa (LocalSpec C)))).run s), P z.1) :
    P (ThresholdLeanXmssSecurity.D prims h oa) := by
  obtain ⟨z, hz, hzv, -⟩ := hW.2 s h hg ha
  rw [← hzv]
  exact hP z hz

end Reference

/-! ## The ghost run with the records in the outputs -/

section Pair

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α ρ : Type}

/-- The output of a ghost program with its record. -/
def pairOut (p : Option α × ρ) : Option (α × ρ) := p.1.map (·, p.2)

/-- A ghost step with its record in its output. -/
def pairStep : RStep C E G α ρ → Step C E G (α × ρ)
  | .done out record => .done (pairOut (out, record))
  | .wait outbox resume => .wait outbox fun inbox => pairOut <$> resume inbox
  | .call input resume => .call input fun r => pairOut <$> resume r

theorem outbox_pairStep (s : RStep C E G α ρ) : (pairStep s).outbox = s.outbox := by
  cases s <;> rfl

theorem delivered_pairStep (s : RStep C E G α ρ) : (pairStep s).delivered = s.delivered := by
  rcases s with ⟨_ | _, _⟩ | _ | _ <;> rfl

theorem callInput_pairStep (s : RStep C E G α ρ) : (pairStep s).callInput = s.callInput := by
  cases s <;> rfl

theorem isDone_pairStep (s : RStep C E G α ρ) : (pairStep s).isDone = s.isDone := by
  cases s <;> rfl

/-- `advanceR_erase` with the record in the output. -/
theorem advanceR_pair (oa : OracleComp (PartySpec C E G) (Option α × ρ)) :
    pairStep <$> advanceR oa = advance (pairOut <$> oa) := by
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

end Pair

section PairExecution

variable {C : Committee} {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {I O L Rs Ia α ρ : Type}

/-- `stepRoundR_erase` with the record in the output. -/
theorem stepRoundR_pair (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) (state : A.State)
    (steps : C.Party → RStep C E (CallSpec I O) α ρ) :
    stepRound Ro D A F state (fun i => pairStep (steps i)) =
      (fun r => (r.1, (fun i => pairStep (r.2.1 i)), r.2.2)) <$> stepRoundR Ro D A F blank state steps := by
  unfold stepRound stepRoundR
  simp only [callInput_pairStep, isDone_pairStep, outbox_pairStep, delivered_pairStep]
  split_ifs
  · simp only [map_bind, map_pure]
    refine bind_congr fun r => ?_
    rw [sequenceFin_map_bind (g := pairStep) (k := fun steps' => pure (r.1, steps', fun _ _ => none))]
    congr 2
    funext j
    cases hs : steps j with
    | done out record => simp [pairStep]
    | wait outbox resume => simp [pairStep]
    | call input resume =>
      simp only [pairStep]
      split_ifs
      · simp [pairStep, pairOut]
      · rw [← advanceR_pair, hRo]
  · simp only [map_bind, map_pure]
    refine bind_congr fun r => ?_
    rw [sequenceFin_map_bind (g := pairStep) (k := fun steps' => pure (r.1, steps', r.2))]
    congr 2
    funext j
    cases hs : steps j with
    | done out record => simp [pairStep]
    | wait outbox resume =>
      simp only [pairStep]
      split_ifs
      · simp [pairStep, pairOut]
      · rw [← advanceR_pair, hRo]
    | call input resume => simp [pairStep, pairOut]

/-- `executeRoundsR_erase` with the record in the output. -/
theorem executeRoundsR_pair (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → RStep C E (CallSpec I O) α ρ),
    executeRounds Ro D A F fuel state (fun i => pairStep (steps i)) =
      (fun r => (r.1, fun i => (pairStep (r.2 i)).output)) <$> executeRoundsR Ro D A F blank fuel state steps
  | 0, state, steps => by simp [executeRounds, executeRoundsR]
  | fuel + 1, state, steps => by
    simp only [executeRounds, executeRoundsR, isDone_pairStep]
    split_ifs
    · simp
    · rw [stepRoundR_pair Ro hRo D A F blank, map_bind, bind_map_left]
      refine bind_congr fun r => ?_
      exact executeRoundsR_pair Ro hRo D A F blank fuel r.1 r.2.1

/-- `startStepsR_erase` with the record in the output. -/
theorem startStepsR_pair (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (blank : ρ) (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    startSteps Ro D (fun i => OptionT.mk (pairOut <$> program i)) =
      (fun steps i => pairStep (steps i)) <$> startStepsR Ro D blank program := by
  unfold startSteps startStepsR
  have h : ∀ i : C.Party, (if i ∈ D.1 then pure (Step.done none) else
      Ro.honest (advance (OptionT.mk (pairOut <$> program i)).run)) =
      ((if i ∈ D.1 then pure (RStep.done none blank) else Ro.honest (advanceR (program i))) >>=
        fun s => pure (pairStep s)) := by
    intro i
    split_ifs
    · simp [pairStep, pairOut]
    · rw [show (OptionT.mk (pairOut <$> program i)).run = pairOut <$> program i from rfl, ← advanceR_pair, hRo,
        map_eq_bind_pure_comp]
      rfl
  simp only [h]
  rw [sequenceFin_bind_pure, map_eq_bind_pure_comp]
  rfl

/-- The ghost run with the record of each operator in its output is `executePhase` of the programs
with the records in their outputs. -/
theorem executePhaseR_pair (Ro : Roles C m) (hRo : ∀ {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ),
      Ro.honest (g <$> oa) = g <$> Ro.honest oa)
    (D : C.Coalition) (A : Adversary C E Ia L Rs) (F : Functionality C I O L Rs) (blank : ρ) (fuel : ℕ)
    (state : A.State) (program : C.Party → OracleComp (PartySpec C E (CallSpec I O)) (Option α × ρ)) :
    executePhase Ro D A F fuel state (fun i => OptionT.mk (pairOut <$> program i)) =
      (fun r => (r.1, fun i => (pairStep (r.2 i)).output)) <$> executePhaseR Ro D A F blank fuel state program := by
  unfold executePhase executePhaseR
  rw [startStepsR_pair Ro hRo, bind_map_left, map_bind]
  exact bind_congr fun steps => executeRoundsR_pair Ro hRo D A F blank fuel state steps

end PairExecution

/-! ## The hop -/

section Hop

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives) (budget : StartBudget)

/-- An outcome of a computation and a test of its value in a world, from its two parts. -/
theorem mem_support_run_test {ι : Type} {spec : OracleSpec ι} {σ α β : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (A : OracleComp spec α) (B : α → OracleComp spec β) (s : σ) (ω : (α × β) × σ)
    (hω : ω ∈ support ((simulateQ impl (do let r ← A; let b ← B r; pure (r, b))).run s)) :
    ∃ y ∈ support ((simulateQ impl A).run s), ∃ w ∈ support ((simulateQ impl (B y.1)).run y.2),
      ω = ((y.1, w.1), w.2) := by
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hω
  obtain ⟨y, hy, w, hw, rfl⟩ := hω
  exact ⟨y, hy, w, hw, rfl⟩

end Hop

end GhostMonitor

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.TprfSecurityProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.MpcCells

attribute [local instance] Classical.propDecidable

section Cache

variable {C : Committee}

/-- The query is a `.hash` call on an input that the MPC evaluates with `Th`. -/
def MpcCell (q : Query C) : Prop := ∃ input, q = .hash input ∧ MpcInput input

/-- The hash cache without its cells on the inputs of the MPC. -/
def cleanCache (c : HashCache C) : HashCache C :=
  QueryCache.ofFn fun q => if MpcCell q then none else c q

/-- The world with a clean hash cache. -/
def cleanWorld (w : StreamState C) : StreamState C := (cleanCache w.1, w.2)

theorem cleanCache_of_not {c : HashCache C} {q : Query C} (hq : ¬ MpcCell q) : cleanCache c q = c q := by
  simp [cleanCache, hq]

theorem cleanCache_ne_none {c : HashCache C} {q : Query C} (h : cleanCache c q ≠ none) : c q ≠ none := by
  by_cases hq : MpcCell q
  · simp [cleanCache, hq] at h
  · rwa [cleanCache_of_not hq] at h

theorem cleanCache_cacheQuery {c : HashCache C} {q : Query C} (hq : ¬ MpcCell q) (u : HashOutput) :
    cleanCache (c.cacheQuery q u) = (cleanCache c).cacheQuery q u := by
  refine QueryCache.ext fun t => ?_
  by_cases ht : t = q
  · subst ht
    rw [cleanCache_of_not hq, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ ht]
    by_cases hm : MpcCell t
    · simp [cleanCache, hm]
    · rw [cleanCache_of_not hm, cleanCache_of_not hm, QueryCache.cacheQuery_of_ne _ _ ht]

theorem noMpc_cleanCache (c : HashCache C) : NoMpc (cleanCache c) := fun x hx => by
  simp [cleanCache, show MpcCell (C := C) (.hash x) from ⟨x, rfl, hx⟩]

theorem splitRegionCache_cleanCache {P : Query C → Prop} (hP : ∀ input, ¬ P (.hash input)) (c : HashCache C) :
    splitRegionCache P (cleanCache c) = splitRegionCache P c := by
  refine QueryCache.ext fun t => ?_
  simp only [splitRegionCache, QueryCache.ofFn_apply]
  split_ifs with ht
  · refine cleanCache_of_not ?_
    rintro ⟨input, rfl, -⟩
    exact hP input ht
  · rfl

end Cache

/-! ## One call of the stream world -/

section World

variable {C : Committee} (prims : Primitives)

/-- `H` from the clean cache is `H` from the cache with its final cache cleaned. -/
theorem hashAnswer_stateMap (q : Query C) : StateMap cleanCache (hashAnswer prims q) (hashAnswer prims q) := by
  intro g
  by_cases hm : MpcCell q
  · obtain ⟨input, rfl, hmpc⟩ := hm
    simp [hashAnswer, hmpc]
  · have hu : ∀ input, q = .hash input → ¬ MpcInput input := fun input h hmpc => hm ⟨input, h, hmpc⟩
    rw [hashAnswer_eq_randomOracle prims hu]
    have hc := cleanCache_of_not (c := g) hm
    cases hg : g q with
    | some v =>
      simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hg,
        QueryImpl.withCaching_run_some _ (hc.trans hg), map_pure, Prod.map_apply, id]
    | none =>
      simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hg,
        QueryImpl.withCaching_run_none _ (hc.trans hg), Functor.map_map, Prod.map_apply, id,
        cleanCache_cacheQuery hm]

theorem localAnswer_stateMap (t : (LocalSpec C).Domain) :
    StateMap cleanCache (localAnswer prims t) (localAnswer prims t) := by
  rcases t with n | u | x
  · intro g
    simp only [localAnswer_unif_run, Functor.map_map, Prod.map_apply, id]
  · exact hashAnswer_stateMap prims u
  · change StateMap _ (prgAnswer prims x) (prgAnswer prims x)
    simp only [prgAnswer]
    exact (hashAnswer_stateMap prims _).bind fun d => StateMap.pure _ _

theorem programAnswer_stateMap (x : Query C × HashOutput) :
    StateMap cleanCache (programAnswer x) (programAnswer x) := by
  intro g
  by_cases hm : MpcCell x.1
  · have hm' : ∃ input, x.1 = .hash input ∧ MpcInput input := hm
    simp [programAnswer, hm']
  · have hn : ¬ ∃ input, x.1 = .hash input ∧ MpcInput input := hm
    have hc := cleanCache_of_not (c := g) hm
    cases hg : g x.1 with
    | some v => simp [programAnswer, StateT.run_bind, hn, hc, hg]
    | none => simp [programAnswer, StateT.run_bind, hn, hc, hg, cleanCache_cacheQuery hm]

theorem onHash_stateMap {α : Type} {m : StateT (HashCache C) ProbComp α} (h : StateMap cleanCache m m) :
    StateMap cleanWorld (onHash m) (onHash m) := by
  intro st
  simp only [onHash, StateT.run_mk, cleanWorld]
  rw [h st.1]
  simp only [Functor.map_map]
  rfl

/-- Each call of `streamWorld` from the clean world is the call from the world with its final world
cleaned. -/
theorem streamWorld_stateMap (D : C.Coalition) (t : (WorldSpec C).Domain) :
    StateMap cleanWorld (streamWorld prims D t) (streamWorld prims D t) := by
  rcases t with ((t | p) | (u | q | x))
  · exact onHash_stateMap (localAnswer_stateMap prims t)
  · exact onHash_stateMap (programAnswer_stateMap p)
  · exact onHash_stateMap (localAnswer_stateMap prims _)
  · exact onHash_stateMap (localAnswer_stateMap prims _)
  · show StateMap _ (if Hidden D x.1 then _ else _) (if Hidden D x.1 then _ else _)
    split_ifs
    · intro st
      simp [cleanWorld, Functor.map_map]
    · exact onHash_stateMap (localAnswer_stateMap prims _)

/-- Each computation in `streamWorld` from the clean world is the computation from the world with
its final world cleaned. -/
theorem streamWorld_run_clean (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (world : StreamState C) :
    (simulateQ (streamWorld prims D) oa).run (cleanWorld world) =
      Prod.map id cleanWorld <$> (simulateQ (streamWorld prims D) oa).run world :=
  StateMap.simulateQ (streamWorld_stateMap prims D) oa world

end World

/-! ## The events and the readiness -/

section Events

variable {C : Committee}

theorem domainCollision_cleanCache {P : Query C → Prop} (hP : ∀ input, ¬ P (.hash input)) (c : HashCache C) :
    DomainCollision P (cleanCache c) ↔ DomainCollision P c := by
  rw [DomainCollision, DomainCollision, splitRegionCache_cleanCache hP]

theorem splitHash_cleanCache (c : HashCache C) :
    DomainCollision SplitHashDomain (cleanCache c) ↔ DomainCollision SplitHashDomain c :=
  domainCollision_cleanCache (fun _ h => h) c

/-- The global events read no cell on an input of the MPC. -/
theorem globalEvent_cleanWorld (w : StreamState C) : GlobalEvent (cleanWorld w) ↔ GlobalEvent w := by
  simp only [GlobalEvent, cleanWorld]
  rw [domainCollision_cleanCache (fun _ h => h), domainCollision_cleanCache (fun _ h => h),
    domainCollision_cleanCache (fun _ h => h), splitHash_cleanCache]

/-- The clean world of a ready start is ready. -/
theorem runReady_cleanWorld (prims : Primitives) (budget : StartBudget) (D : C.Coalition) {σ : Type}
    {s : RealState C σ} {world : StreamState C} (ready : RunReady prims budget D s world) :
    RunReady prims budget D s (cleanWorld world) := by
  obtain ⟨hseeds, htop, hsplit, ⟨seen, keys, hsound, hseen, hkeys⟩, ⟨salts, hsalts, hcard⟩, hhidden⟩ := ready
  refine ⟨hseeds, ?_, ?_, ⟨seen, keys, ⟨?_, ?_⟩, hseen, hkeys⟩, ⟨salts, ?_, hcard⟩, hhidden⟩
  · intro i hi top htop'
    rw [streamWorld_run_clean, support_map, Set.forall_mem_image]
    exact htop i hi top htop'
  · show SplitCacheBound (splitRegionCache SplitHashDomain (cleanCache world.1)) budget.split
    rw [splitRegionCache_cleanCache (P := SplitHashDomain) (fun _ h => h)]
    exact hsplit
  · exact fun tag label bits hL h => hsound.1 tag label bits hL (cleanCache_ne_none h)
  · exact fun key idx h => hsound.2 key idx (cleanCache_ne_none h)
  · exact fun salt h hd => hsalts salt h (cleanCache_ne_none hd)

end Events

/-! ## The runs and the hop -/

section Run

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives) (budget : StartBudget)

/-- The start of a check with a clean world. -/
def cleanStart {σ : Type} (c : CheckStart C σ) : CheckStart C σ := { c with world := cleanWorld c.world }

/-- The result of `checkAt` with clean worlds. -/
def cleanCheck {σ : Type}
    (r : Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C)) :
    Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C) :=
  (r.1.map cleanStart, r.2.map (Prod.map id cleanWorld))

theorem streamTreeRun_clean (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (world : StreamState C) :
    (streamTreeRun prims K circuits settings D net tree s).run (cleanWorld world) =
      Prod.map id cleanWorld <$> (streamTreeRun prims K circuits settings D net tree s).run world :=
  streamWorld_run_clean prims D _ world

theorem checkFrom_clean (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (c : CheckStart C net.State) :
    checkFrom prims K D net (cleanStart c) = Prod.map id cleanWorld <$> checkFrom prims K D net c :=
  streamWorld_run_clean prims D _ c.world

/-- `CheckBad` reads the worlds only through the global events, the hidden cache and the history and
digest cells. -/
theorem checkBad_cleanCheck (D : C.Coalition) {σ : Type}
    (r : Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C)) :
    CheckBad D (cleanCheck r) ↔ CheckBad D r := by
  rcases r with ⟨_ | c, _ | out⟩
  · simp [CheckBad, cleanCheck]
  · simp [CheckBad, cleanCheck]
  · simp [CheckBad, cleanCheck]
  · simp only [CheckBad, cleanCheck, Option.map_some, Prod.mk.injEq, Option.some.injEq]
    constructor
    · rintro ⟨c', out', ⟨rfl, rfl⟩, hout, hwrong, hfresh, hglobal, hsplit⟩
      exact ⟨c, out, ⟨rfl, rfl⟩, hout, hwrong, hfresh, fun h => hglobal ((globalEvent_cleanWorld _).2 h),
        fun h => hsplit ((splitHash_cleanCache _).2 h)⟩
    · rintro ⟨c', out', ⟨rfl, rfl⟩, hout, hwrong, hfresh, hglobal, hsplit⟩
      exact ⟨_, _, ⟨rfl, rfl⟩, hout, hwrong, hfresh,
        fun h => hglobal ((globalEvent_cleanWorld _).1 h), fun h => hsplit ((splitHash_cleanCache _).1 h)⟩

end Run

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.MpcCells

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostMonitor.balR_recRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostMonitor.balR_recRun

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostMonitor.condR_recRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostMonitor.condR_recRun

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostMonitor.condR_ceremonyOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostMonitor.condR_ceremonyOutput

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.MpcCells.streamWorld_run_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.MpcCells.streamWorld_run_clean
