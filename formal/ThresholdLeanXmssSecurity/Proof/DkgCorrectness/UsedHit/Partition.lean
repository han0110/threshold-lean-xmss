import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Slots
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Birthday
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.PhaseAbort

/-!
# The partition of the cache of `jointKeyWorld` for a slot reduction

`mergeSetup h s` is the private state `s` with the cells of the class `prssSetup` of the outer cache
`h`. `partition_run` states that a computation with no programming query, run under
`jointKeyWorld` from `mergeSetup h s`, is its run under `slotHandler` from `s` on the local oracles of
the world from `h`, with the outer cache merged back. The handler of a slot reduction thus forwards
exactly the setup cells, and `UsedHit` reads only private cells (`usedHit_mergeSetup`).

`executePhase_coupling` runs a phase of a setup under `slotHandler` as the phase of an adversary that
runs the rounds under `slotHandler` itself. `discardAnswer` drops a computation whose result
is unused, and `freeDraw_commutes` moves a private draw across a computation in
`jointKeyWorld`. `executePhase_dead_congr` states that the continuations of the honest programs of
a phase are never run when an honest operator aborts at once. The section on the hybrid game states
that it makes no programming call.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The merge of the setup cells -/

/-- A cell of the class `prssSetup`. -/
def setupCell (q : Query C) : Bool := decide (queryClass q = .prssSetup)

/-- The cache with the cells of the class `prssSetup` from `h` and the other cells from `c`. -/
def mergeCache (h c : HashCache C) : HashCache C := QueryCache.ofFn fun q => if setupCell q then h q else c q

/-- The private state `s` with the cells of the class `prssSetup` of the outer cache `h`. -/
def mergeSetup (h : HashCache C) (s : KeyJointState C) : KeyJointState C :=
  { s with hash := mergeCache h s.hash }

theorem mergeCache_read_setup {q : Query C} (hq : setupCell q = true) (h c : HashCache C) :
    mergeCache h c q = h q := by
  simp [mergeCache, hq]

theorem mergeCache_read_other {q : Query C} (hq : setupCell q = false) (h c : HashCache C) :
    mergeCache h c q = c q := by
  simp [mergeCache, hq]

theorem mergeCache_write_setup {q : Query C} (hq : setupCell q = true) (h c : HashCache C) (v : HashOutput) :
    mergeCache (h.cacheQuery q v) c = (mergeCache h c).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases e : q' = q
  · subst e
    simp [mergeCache, hq]
  · by_cases h' : setupCell q' <;> simp [mergeCache, h', QueryCache.cacheQuery_of_ne, e]

theorem mergeCache_write_other {q : Query C} (hq : setupCell q = false) (h c : HashCache C) (v : HashOutput) :
    mergeCache h (c.cacheQuery q v) = (mergeCache h c).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases e : q' = q
  · subst e
    simp [mergeCache, hq]
  · by_cases h' : setupCell q' <;> simp [mergeCache, h', QueryCache.cacheQuery_of_ne, e]

theorem mergeSetup_empty : mergeSetup (∅ : HashCache C) keyJointInitial = keyJointInitial := by
  have e : mergeCache (∅ : HashCache C) ∅ = ∅ := by
    refine QueryCache.ext fun q => ?_
    simp [mergeCache]
  simp only [mergeSetup, keyJointInitial, e]

/-- `UsedHit` reads only the stream keys, `keys` and `used`, so it does not read the setup cells. -/
theorem usedHit_mergeSetup (D : C.Coalition) (h : HashCache C) (s : KeyJointState C) :
    UsedHit D (mergeSetup h s) ↔ UsedHit D s := by
  have hs : ∀ k, (mergeSetup h s).hash (.streamKey k) = s.hash (.streamKey k) := fun k =>
    mergeCache_read_other (by simp [setupCell, queryClass]) h s.hash
  simp only [UsedHit, hs]
  rfl

/-! ## One step of the lazy random oracle on a map of caches -/

/-- One step of the lazy random oracle moves along a map of caches that keeps the cell of the query and
commutes with a write to that cell. -/
theorem randomOracle_map (q : Query C) (f : HashCache C → HashCache C) (c : HashCache C)
    (hread : f c q = c q) (hwrite : ∀ v : HashOutput, f (c.cacheQuery q v) = (f c).cacheQuery q v) :
    ((Query C →ₒ HashOutput).randomOracle q).run (f c) =
      (fun z => (z.1, f z.2)) <$> ((Query C →ₒ HashOutput).randomOracle q).run c := by
  rw [randomOracle.run_eq, randomOracle.run_eq, hread]
  cases c q with
  | some u => simp
  | none => simp [hwrite]

theorem hashAnswer_map (prims : Primitives) (q : Query C) (f : HashCache C → HashCache C) (c : HashCache C)
    (hread : f c q = c q) (hwrite : ∀ v : HashOutput, f (c.cacheQuery q v) = (f c).cacheQuery q v) :
    (hashAnswer prims q).run (f c) = (fun z => (z.1, f z.2)) <$> (hashAnswer prims q).run c := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simp [hashAnswer, hm]
    · simp only [hashAnswer, hm, ite_false]
      exact randomOracle_map _ f c hread hwrite
  all_goals exact randomOracle_map _ f c hread hwrite

/-! ## The steps of `jointKeyWorld` that keep the setup cells -/

/-- A step on the private state that reads and writes no setup cell. -/
def Frames {α : Type} (m : StateT (KeyJointState C) ProbComp α) : Prop :=
  ∀ h s, m.run (mergeSetup h s) = (fun z => (z.1, mergeSetup h z.2)) <$> m.run s

theorem Frames.pure {α : Type} (a : α) : Frames (pure a : StateT (KeyJointState C) ProbComp α) := by
  intro h s
  simp

theorem Frames.bind {α β : Type} {m : StateT (KeyJointState C) ProbComp α}
    {f : α → StateT (KeyJointState C) ProbComp β} (hm : Frames m) (hf : ∀ a, Frames (f a)) : Frames (m >>= f) := by
  intro h s
  rw [StateT.run_bind, StateT.run_bind, hm h s, bind_map_left, map_bind]
  exact bind_congr fun z => hf z.1 h z.2

theorem Frames.onJointHash_hash (prims : Primitives) {q : Query C} (hq : setupCell q = false) :
    Frames (onJointHash (hashAnswer prims q)) := by
  intro h s
  simp only [onJointHash, StateT.run_mk, mergeSetup]
  rw [hashAnswer_map prims q (mergeCache h) s.hash (mergeCache_read_other hq h s.hash)
    (mergeCache_write_other hq h s.hash), Functor.map_map, Functor.map_map]

theorem Frames.onJointHash_sample (u : unifSpec.Domain) :
    Frames (onJointHash (C := C) ((unifFwdImpl (Query C →ₒ HashOutput)) u)) := by
  intro h s
  simp [onJointHash, unifFwdImpl, mergeSetup]

theorem Frames.ofJointHash (prims : Primitives) {q : Query C} (hq : setupCell q = false) :
    Frames (jointHash prims false q) := by
  intro h s
  cases q <;> simp only [jointHash, StateT.run_mk, Bool.false_eq_true, ite_false] <;>
    exact Frames.onJointHash_hash prims hq h s

theorem Frames.ofJointHidden (x : KeyName C × HashOutput) : Frames (C := C) (jointHidden false x) := by
  intro h s
  simp only [jointHidden, StateT.run_mk, mergeSetup]
  cases s.keys x with
  | some v => simp
  | none => simp

theorem setupCell_streamKey (k : HashOutput) : setupCell (C := C) (.streamKey k) = false := by
  simp [setupCell, queryClass]

theorem Frames.ofJointLocal (prims : Primitives) (t : (LocalSpec C).Domain)
    (ht : ∀ q, t = .inr (.inl q) → setupCell q = false) : Frames (jointLocal prims false t) := by
  rcases t with u | q | x
  · exact Frames.onJointHash_sample u
  · exact Frames.ofJointHash prims (ht q rfl)
  · exact (Frames.ofJointHash prims (setupCell_streamKey _)).bind fun _ => Frames.pure _

/-- A call of the class `prssSetup` on either copy. `slotHandler` forwards exactly these calls. -/
def SetupQuery : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inr (.inl q))) => queryClass q = .prssSetup
  | .inr (.inr (.inl q)) => queryClass q = .prssSetup
  | _ => False

theorem keyJointRisk_mergeSetup (D : C.Coalition) (t : (WorldSpec C).Domain) (h : HashCache C)
    (s : KeyJointState C) : keyJointRisk D t (mergeSetup h s) = keyJointRisk D t s := by
  rcases t with ((u | q | x) | p) | (u | q | x) <;>
    simp [keyJointRisk, mergeSetup, mergeCache_read_other (setupCell_streamKey (C := C) _)]

/-- A step of `jointKeyWorld` on a call that is no setup call and no programming call keeps the
setup cells. -/
theorem frames_jointKeyWorld (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (hs : ¬ SetupQuery t) (hp : ¬ WorldProgramQuery t) : Frames (jointKeyWorld prims D false t) := by
  have core : Frames (jointKeyWorldCore prims D false t) := by
    rcases t with ((u | q | x) | p) | (u | q | x)
    · exact Frames.ofJointLocal prims (.inl u) fun _ e => by simp at e
    · exact Frames.ofJointLocal prims (.inr (.inl q)) fun q' e => by
        simp only [Sum.inr.injEq, Sum.inl.injEq] at e
        subst e
        simpa [setupCell, SetupQuery] using hs
    · exact Frames.ofJointLocal prims (.inr (.inr x)) fun _ e => by simp at e
    · exact absurd trivial hp
    · exact Frames.ofJointLocal prims (.inl u) fun _ e => by simp at e
    · exact Frames.ofJointLocal prims (.inr (.inl q)) fun q' e => by
        simp only [Sum.inr.injEq, Sum.inl.injEq] at e
        subst e
        simpa [setupCell, SetupQuery] using hs
    · simp only [jointKeyWorldCore]
      split_ifs
      · exact (Frames.ofJointHidden _).bind fun _ => Frames.pure _
      · exact Frames.ofJointLocal prims (.inr (.inr x)) fun _ e => by simp at e
  intro h s
  simp only [jointKeyWorld, StateT.run_mk, core h s, Functor.map_map, keyJointRisk_mergeSetup]
  rfl

theorem keyJointRisk_setup (D : C.Coalition) {q : Query C} (hq : queryClass q = .prssSetup)
    (s : KeyJointState C) :
    keyJointRisk D (.inl (.inl (.inr (.inl q)))) s = false ∧ keyJointRisk D (.inr (.inr (.inl q))) s = false := by
  cases q <;> simp_all [keyJointRisk, queryClass]

/-- A setup call reads the cell of `h` and writes it back to `h`. -/
theorem jointHash_setup (prims : Primitives) {q : Query C} (hq : queryClass q = .prssSetup)
    (h : HashCache C) (s : KeyJointState C) :
    (ThresholdLeanXmssSecurity.jointHash prims false q).run (mergeSetup h s) =
      (fun z => (z.1, mergeSetup z.2 s)) <$> (hashAnswer prims q).run h := by
  have hcell : setupCell q = true := by simp [setupCell, hq]
  have hhash : (hashAnswer prims q).run (mergeCache h s.hash) =
      (fun z => (z.1, mergeCache z.2 s.hash)) <$> (hashAnswer prims q).run h :=
    hashAnswer_map prims q (fun c => mergeCache c s.hash) h (mergeCache_read_setup hcell h s.hash)
      (fun v => mergeCache_write_setup hcell h s.hash v)
  have e : (ThresholdLeanXmssSecurity.jointHash prims false q).run (mergeSetup h s) =
      (onJointHash (hashAnswer prims q)).run (mergeSetup h s) := by
    cases q <;> simp_all [ThresholdLeanXmssSecurity.jointHash, queryClass]
  rw [e]
  simp only [onJointHash, StateT.run_mk, mergeSetup, hhash, Functor.map_map]

/-- A setup call on the counted copy under `jointKeyWorld` from `mergeSetup h s` is the lazy random
oracle on `h`. -/
theorem jointKeyWorld_setup_counted (prims : Primitives) (D : C.Coalition) {q : Query C}
    (hq : queryClass q = .prssSetup) (h : HashCache C) (s : KeyJointState C) :
    (jointKeyWorld prims D false (.inl (.inl (.inr (.inl q))))).run (mergeSetup h s) =
      (fun z => (z.1, mergeSetup z.2 s)) <$> (hashAnswer prims q).run h := by
  simp only [jointKeyWorld, StateT.run_mk, jointKeyWorldCore, jointLocal, jointHash_setup prims hq,
    Functor.map_map, (keyJointRisk_setup D hq _).1, Bool.or_false]
  rfl

/-- A setup call on the free copy under `jointKeyWorld` from `mergeSetup h s` is the lazy random
oracle on `h`. -/
theorem jointKeyWorld_setup_free (prims : Primitives) (D : C.Coalition) {q : Query C}
    (hq : queryClass q = .prssSetup) (h : HashCache C) (s : KeyJointState C) :
    (jointKeyWorld prims D false (.inr (.inr (.inl q)))).run (mergeSetup h s) =
      (fun z => (z.1, mergeSetup z.2 s)) <$> (hashAnswer prims q).run h := by
  simp only [jointKeyWorld, StateT.run_mk, jointKeyWorldCore, jointLocal, jointHash_setup prims hq,
    Functor.map_map, (keyJointRisk_setup D hq _).2, Bool.or_false]
  rfl

/-! ## The run of a computation under the partition -/

/-- A setup call under `slotHandler`, run on the local oracles of the world, is the lazy random oracle
on the outer cache and keeps the private state. -/
theorem slotHandler_setup_run (prims : Primitives) {q : Query C} (s : KeyJointState C) (h : HashCache C) :
    (simulateQ (localAnswer prims) ((liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C)
      (.inr (.inl q)))) : StateT (KeyJointState C) (OracleComp (LocalSpec C)) _).run s)).run h =
      (fun z => ((z.1, s), z.2)) <$> (hashAnswer prims q).run h := by
  simp only [StateT.run_monadLift, monadLift_self]
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_spec_query, simulateQ_pure, StateT.run_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Another call under `slotHandler`, run on the local oracles of the world, is the step of
`jointKeyWorld` on the private state and keeps the outer cache. -/
theorem slotHandler_other_run (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (hs : ¬ SetupQuery t) (s : KeyJointState C) (h : HashCache C) :
    (simulateQ (localAnswer prims) ((slotHandler prims D t).run s)).run h =
      (fun z => (z, h)) <$> (jointKeyWorld prims D false t).run s := by
  have e : (slotHandler prims D t).run s = liftComp ((jointKeyWorld prims D false t).run s) (LocalSpec C) := by
    rcases t with ((u | q | x) | p) | (u | q | x)
    all_goals first
      | (have hq : queryClass q ≠ .prssSetup := by simpa [SetupQuery] using hs
         simp only [slotHandler, hq, ite_false, StateT.run_mk])
      | rfl
  rw [e, simulateQ_local_sample_seedGensecurity, StateT.run_lift, map_eq_bind_pure_comp]
  rfl

/-- One query under the partition, for a continuation with the partition. -/
theorem partition_step (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain) (hp : ¬ WorldProgramQuery t)
    {β : Type} (f : (WorldSpec C).Range t → OracleComp (WorldSpec C) β)
    (hf : ∀ u h s, (simulateQ (jointKeyWorld prims D false) (f u)).run (mergeSetup h s) =
      (fun z => (z.1.1, mergeSetup z.2 z.1.2)) <$>
        (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D) (f u)).run s)).run h)
    (h : HashCache C) (s : KeyJointState C) :
    (simulateQ (jointKeyWorld prims D false) (liftM (OracleSpec.query t) >>= f)).run (mergeSetup h s) =
      (fun z => (z.1.1, mergeSetup z.2 z.1.2)) <$>
        (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D) (liftM (OracleSpec.query t) >>= f)).run s)).run h := by
  simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query]
  by_cases hs : SetupQuery t
  · rcases t with ((u | q | x) | p) | (u | q | x)
    all_goals try exact (hs : False).elim
    · have hq : queryClass q = .prssSetup := hs
      rw [jointKeyWorld_setup_counted prims D hq h s]
      simp only [slotHandler, hq, ite_true]
      rw [slotHandler_setup_run, bind_map_left, bind_map_left, map_bind]
      exact bind_congr fun z => hf z.1 z.2 s
    · have hq : queryClass q = .prssSetup := hs
      rw [jointKeyWorld_setup_free prims D hq h s]
      simp only [slotHandler, hq, ite_true]
      rw [slotHandler_setup_run, bind_map_left, bind_map_left, map_bind]
      exact bind_congr fun z => hf z.1 z.2 s
  · rw [frames_jointKeyWorld prims D t hs hp h s, slotHandler_other_run prims D t hs s h, bind_map_left,
      bind_map_left, map_bind]
    exact bind_congr fun z => hf z.1 h z.2

/-- The partition. A computation with no programming call, run under `jointKeyWorld` from
`mergeSetup h s`, is its run under `slotHandler` from `s` on the local oracles of the world from `h`,
with the outer cache merged back. -/
theorem partition_run (prims : Primitives) (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hp : AllQueriesSatisfy oa fun t => ¬ WorldProgramQuery t) (h : HashCache C) (s : KeyJointState C) :
    (simulateQ (jointKeyWorld prims D false) oa).run (mergeSetup h s) =
      (fun z => (z.1.1, mergeSetup z.2 z.1.2)) <$>
        (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D) oa).run s)).run h := by
  induction oa using OracleComp.inductionOn generalizing h s with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    exact partition_step prims D t hp.1 k (fun u h s => ih u (hp.2 u) h s) h s

/-! ## A phase of a setup under the partition -/

section Phase

variable {E : Type}

/-- A local call of an honest operator in a setup, namely a private draw or a call of the class
`prssSetup`. -/
def SetupLocal : (LocalSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.inl q) => queryClass q = .prssSetup
  | .inr (.inr _) => False

/-- A call on the free copy that `SetupLocal` allows. -/
def HonestSetup : (WorldSpec C).Domain → Prop
  | .inr t => SetupLocal t
  | _ => False

theorem sample_run (prims : Primitives) (D : C.Coalition) (n : unifSpec.Domain) (priv : KeyJointState C)
    (h : HashCache C) :
    (simulateQ (localAnswer prims) ((slotHandler prims D (.inr (.inl n))).run priv)).run h =
      (fun z => ((z.1, priv), z.2)) <$> (worldAnswer prims (.inr (.inl n))).run h := by
  simp only [slotHandler, StateT.run_mk, simulateQ_local_sample_seedGensecurity, StateT.run_lift]
  simp [jointKeyWorld, jointKeyWorldCore, jointLocal, onJointHash, keyJointRisk, unifFwdImpl, localAnswer]

theorem setupFree_run (prims : Primitives) (D : C.Coalition) {q : Query C} (hq : queryClass q = .prssSetup)
    (priv : KeyJointState C) (h : HashCache C) :
    (simulateQ (localAnswer prims) ((slotHandler prims D (.inr (.inr (.inl q)))).run priv)).run h =
      (fun z => ((z.1, priv), z.2)) <$> (worldAnswer prims (.inr (.inr (.inl q)))).run h := by
  simp only [slotHandler, hq, ite_true]
  rw [slotHandler_setup_run]
  rfl

/-- A computation of the honest operators with only setup calls, under `slotHandler` and the local
oracles of the world, is its run in the world and keeps the private state. -/
theorem honest_run (prims : Primitives) (D : C.Coalition) {β : Type} (X : OracleComp (WorldSpec C) β)
    (hX : AllQueriesSatisfy X HonestSetup) (priv : KeyJointState C) (h : HashCache C) :
    (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D) X).run priv)).run h =
      (fun z => ((z.1, priv), z.2)) <$> (simulateQ (worldAnswer prims) X).run h := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hX
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have step : (simulateQ (localAnswer prims) ((slotHandler prims D t).run priv)).run h =
        (fun z => ((z.1, priv), z.2)) <$> (worldAnswer prims t).run h := by
      rcases t with ((u | q | x) | p) | (u | q | x)
      all_goals try exact (hX.1 : False).elim
      · exact sample_run prims D u priv h
      · exact setupFree_run prims D hX.1 priv h
    rw [step, bind_map_left, map_bind]
    exact bind_congr fun z => ih z.1 (hX.2 z.1) z.2

/-- A query of the program of an operator whose local part is a setup call. -/
def PartySetup {ι : Type} {G : OracleSpec ι} : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => SetupLocal t
  | _ => True

/-- A step whose continuations make only setup calls. -/
def StepSetup {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ k => ∀ m, AllQueriesSatisfy (k m) (PartySetup (E := E) (G := RealSpec))
  | .call _ k => ∀ r, AllQueriesSatisfy (k r) (PartySetup (E := E) (G := RealSpec))

theorem advance_setup {α : Type} (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (hp : AllQueriesSatisfy p (PartySetup (E := E) (G := RealSpec))) : AllQueriesSatisfy (advance p) SetupLocal := by
  induction p using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rcases t with (t | outbox) | input
    · change AllQueriesSatisfy
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (k r)) _
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := LocalSpec C) t _).2 hp.1)
        fun r => ih r (hp.2 r)
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _

theorem advance_stepSetup {α : Type} (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (hp : AllQueriesSatisfy p (PartySetup (E := E) (G := RealSpec))) : ∀ z ∈ support (advance p), StepSetup z := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro z hz
    change z ∈ support (pure (Step.done x) : OracleComp (LocalSpec C) _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [StepSetup]
  | query_bind t k ih =>
    intro z hz
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rcases t with (t | outbox) | input
    · change z ∈ support
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (k r)) at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨r, -, hz⟩ := hz
      exact ih r (hp.2 r) z hz
    · change z ∈ support (pure (Step.wait outbox k) : OracleComp (LocalSpec C) _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only [StepSetup]
      exact hp.2
    · exact input.elim

theorem free_setup {β : Type} {oa : OracleComp (LocalSpec C) β} (h : AllQueriesSatisfy oa SetupLocal) :
    AllQueriesSatisfy (free oa) HonestSetup :=
  AllQueriesSatisfy.simulateQ h fun t ht => (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inr t) _).2 ht

/-- The next honest steps of a round on the real network, after the messages `sent` of the coalition. -/
def nextSteps {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (sent : C.Party → C.Party → Option (Msg E)) : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec α) :=
  OverPermutation.sequenceFin fun j => match steps j with
    | .done out => pure (Step.done out)
    | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (resume fun k => if k ∈ D.1 then sent k j else (steps k).delivered j))
    | .call _ _ => pure (Step.done none)

theorem stepRound_real {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality st steps =
      worldRoles.adversary (A.round st fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) >>=
        fun r => nextSteps D steps r.2 >>= fun steps' => pure (r.1, steps', r.2) := by
  simp only [stepRound, callInput_real, Option.isSome_none, Bool.false_eq_true, and_false,
    exists_false, false_and, ite_false]
  refine bind_congr fun r => ?_
  unfold nextSteps
  congr 2
  funext j
  cases steps j <;> rfl

theorem sequenceFin_setup {κ : Type} {spec : OracleSpec κ} {P : κ → Prop} {β : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec β), (∀ i, AllQueriesSatisfy (f i) P) →
      AllQueriesSatisfy (OverPermutation.sequenceFin f) P := by
  intro n
  induction n with
  | zero => intro f _; exact allQueriesSatisfy_pure _ _
  | succ n ih =>
    intro f hf
    rw [OverPermutation.sequenceFin]
    exact allQueriesSatisfy_bind (hf 0) fun _ => allQueriesSatisfy_bind (ih _ fun i => hf i.succ) fun _ =>
      allQueriesSatisfy_pure _ _

theorem nextSteps_setup {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepSetup (steps i)) (sent : C.Party → C.Party → Option (Msg E)) :
    AllQueriesSatisfy (nextSteps D steps sent) HonestSetup := by
  refine sequenceFin_setup _ fun j => ?_
  have hj := hsteps j
  split
  · exact allQueriesSatisfy_pure _ _
  · rename_i heq
    rw [heq] at hj
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact free_setup (advance_setup _ (hj _))
  · exact allQueriesSatisfy_pure _ _

theorem nextSteps_stepSetup {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepSetup (steps i)) (sent : C.Party → C.Party → Option (Msg E))
    (steps' : C.Party → Step C E RealSpec α) (h' : steps' ∈ support (nextSteps D steps sent)) :
    ∀ i, StepSetup (steps' i) := by
  intro i
  have hi := mem_support_sequenceFin_oc _ steps' h' i
  have hpi := hsteps i
  revert hi hpi
  cases steps i with
  | done out =>
    intro hi _
    simp only [support_pure, Set.mem_singleton_iff] at hi
    rw [hi]
    simp only [StepSetup]
  | wait outbox resume =>
    intro hi hpi
    dsimp only at hi
    split_ifs at hi
    · simp only [support_pure, Set.mem_singleton_iff] at hi
      rw [hi]
      simp only [StepSetup]
    · exact advance_stepSetup _ (hpi _) _ (support_simulateQ_subset _ _ hi)
  | call input resume => exact input.elim

/-- A program of an operator whose local calls are setup calls. -/
def SetupM {ι : Type} {G : OracleSpec ι} {α : Type} (x : PartyM C E G α) : Prop :=
  AllQueriesSatisfy x.run (PartySetup (E := E) (G := G))

section SetupM

variable {ι : Type} {G : OracleSpec ι}

theorem SetupM.pure {α : Type} (a : α) : SetupM (E := E) (G := G) (Pure.pure a : PartyM C E G α) := by
  unfold SetupM
  rw [OptionT.run_pure]
  exact allQueriesSatisfy_pure _ _

theorem SetupM.failure {α : Type} : SetupM (E := E) (G := G) (Alternative.failure : PartyM C E G α) := by
  unfold SetupM
  rw [OptionT.run_failure]
  exact allQueriesSatisfy_pure _ _

theorem SetupM.bind {α β : Type} {x : PartyM C E G α} {f : α → PartyM C E G β} (hx : SetupM x)
    (hf : ∀ a, SetupM (f a)) : SetupM (x >>= f) := by
  unfold SetupM at *
  rw [OptionT.run_bind]
  refine allQueriesSatisfy_bind hx fun o => ?_
  cases o with
  | none => exact allQueriesSatisfy_pure _ _
  | some a => exact hf a

theorem SetupM.localStep {β : Type} {oa : OracleComp (LocalSpec C) β} (h : AllQueriesSatisfy oa SetupLocal) :
    SetupM (E := E) (G := G) (localStep oa) := by
  unfold SetupM ThresholdLeanXmss.localStep
  simp only [OptionT.run_lift]
  refine allQueriesSatisfy_bind (AllQueriesSatisfy.simulateQ h fun t ht => ?_) fun _ => allQueriesSatisfy_pure _ _
  rw [liftM_query_local]
  exact (allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inl t)) _).2 ht

theorem SetupM.oracleStep {β : Type} {oa : OracleComp (RoSpec C) β} (h : AllQueriesSatisfy oa fun x => SetupLocal (.inr x)) :
    SetupM (E := E) (G := G) (oracleStep oa) := by
  refine SetupM.localStep (AllQueriesSatisfy.simulateQ h fun x hx => ?_)
  rcases x with q | x
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inl q)) _).2 hx
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inr x)) _).2 hx

theorem SetupM.sample {β : Type} (pc : ProbComp β) :
    SetupM (E := E) (G := G) (ThresholdLeanXmss.localStep (liftComp pc (LocalSpec C))) := by
  refine SetupM.localStep (AllQueriesSatisfy.simulateQ
    (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) pc) fun t _ => ?_)
  exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 trivial

theorem SetupM.exchange (outbox : Mail C E) : SetupM (G := G) (ThresholdLeanXmss.exchange outbox) := by
  unfold SetupM ThresholdLeanXmss.exchange
  simp only [OptionT.run_bind, OptionT.run_lift]
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inr outbox)) _).2
    trivial) fun inbox => ?_
  rcases inbox with _ | x
  · exact allQueriesSatisfy_pure _ _
  · dsimp only [Option.elim]
    split_ifs
    exacts [SetupM.failure (E := E) (G := G) (α := Mail C E), SetupM.pure (E := E) (G := G) x]

theorem SetupM.require (c : Prop) : SetupM (E := E) (G := G) (ThresholdLeanXmss.require (C := C) c) := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact SetupM.pure _
  · exact SetupM.failure

end SetupM

theorem mapM_satisfy {κ : Type} {spec : OracleSpec κ} {α β : Type} (P : κ → Prop) (f : α → OracleComp spec β)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : ∀ l : List α, AllQueriesSatisfy (l.mapM f) P
  | [] => allQueriesSatisfy_pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf a) fun _ =>
      allQueriesSatisfy_bind (mapM_satisfy P f hf l) fun _ => allQueriesSatisfy_pure _ _

theorem hashQuery_setup {q : Query C} (hq : queryClass q = .prssSetup) :
    AllQueriesSatisfy (ThresholdLeanXmss.hashQuery q) fun x => SetupLocal (C := C) (.inr x) :=
  (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 hq

theorem deriveKeys_setup (i : C.Party) (view : C.Party → Parts C) :
    AllQueriesSatisfy (deriveKeys (C := C) .prss i view) fun x => SetupLocal (.inr x) := by
  have hd : ∀ k l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.derive .prss k l))
      fun x => SetupLocal (.inr x) := fun _ _ => hashQuery_setup rfl
  unfold ThresholdLeanXmss.deriveKeys
  refine allQueriesSatisfy_bind ?_ fun _ => allQueriesSatisfy_bind
    (mapM_satisfy _ _ (fun T => ?_) _) fun _ =>
    allQueriesSatisfy_bind (mapM_satisfy _ _ (fun j => ?_) _) fun _ => allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _
  · split_ifs
    · exact hd _ _
    · exact allQueriesSatisfy_pure _ _
  · split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact hd _ _

theorem commitRevealEcho_setup (i : C.Party) (own : Parts C) :
    SetupM (E := E) (G := RealSpec) (commitRevealEcho .prss i own) := by
  have hc : ∀ a b l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.commit .prss a b l))
      fun x => SetupLocal (.inr x) := fun _ _ _ => hashQuery_setup rfl
  have hs : ∀ l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.sharedKeys .prss l))
      fun x => SetupLocal (.inr x) := fun _ => hashQuery_setup rfl
  unfold commitRevealEcho
  refine SetupM.bind (SetupM.oracleStep (mapM_satisfy _ _ (fun _ => hc _ _ _) _)) fun commitments => ?_
  refine SetupM.bind (SetupM.exchange _) fun committed => ?_
  refine SetupM.bind (SetupM.exchange _) fun revealed => ?_
  refine SetupM.bind (SetupM.oracleStep (mapM_satisfy _ _ (fun _ => hc _ _ _) _)) fun opens => ?_
  refine SetupM.bind (SetupM.require _) fun _ => ?_
  refine SetupM.bind (SetupM.oracleStep (deriveKeys_setup _ _)) fun keys => ?_
  refine SetupM.bind (SetupM.oracleStep (mapM_satisfy _ _ (fun _ => hs _) _)) fun shared => ?_
  refine SetupM.bind (SetupM.exchange _) fun received => ?_
  refine SetupM.bind (SetupM.require _) fun _ => ?_
  exact SetupM.pure _

/-- The honest program of one PRSS setup makes only setup calls. -/
theorem setupKeys_setup (i : C.Party) : SetupM (E := E) (G := RealSpec) (setupKeys .prss i) := by
  unfold setupKeys setupWith
  exact SetupM.bind (SetupM.sample _) fun own => SetupM.bind (commitRevealEcho_setup i own) fun _ => SetupM.pure _

/-- One round of a phase of a setup. The run of the round of `A` under `slotHandler` is the round of an
adversary `R` whose round is the round of `A` under `slotHandler`, with the private state embedded in
the state of `R` by `emb`. -/
theorem stepRound_coupling {Ia α : Type} (prims : Primitives) (D : C.Coalition) (A R : Adversary C E Ia PEmpty PEmpty)
    (emb : KeyJointState C → A.State → R.State)
    (hR : ∀ priv st sent, R.round (emb priv st) sent = (fun r => (emb r.2 r.1.1, r.1.2)) <$>
      (simulateQ (slotHandler prims D) (worldRoles.adversary (A.round st sent))).run priv)
    (st : A.State) (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepSetup (steps i))
    (priv : KeyJointState C) (h : HashCache C) :
    (fun z => ((emb z.1.2 z.1.1.1, z.1.1.2.1, z.1.1.2.2), z.2)) <$>
      (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D)
        (stepRound worldRoles D A noFunctionality st steps)).run priv)).run h =
      (simulateQ (worldAnswer prims) (stepRound worldRoles D R noFunctionality (emb priv st) steps)).run h := by
  rw [stepRound_real, stepRound_real]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_world_adversary, hR]
  rw [simulateQ_map, StateT.run_map, bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  rw [honest_run prims D _ (nextSteps_setup D steps hsteps _), bind_map_left, map_bind]
  refine bind_congr fun y => ?_
  simp

theorem mem_support_twoLevel (prims : Primitives) (D : C.Coalition) {β : Type} (X : OracleComp (WorldSpec C) β)
    (priv : KeyJointState C) (h : HashCache C) (p : (β × KeyJointState C) × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D) X).run priv)).run h)) :
    p.1.1 ∈ support X := by
  have h1 : p.1 ∈ support ((simulateQ (slotHandler prims D) X).run priv) :=
    support_simulateQ_run'_subset (localAnswer prims) _ h (by
      rw [StateT.run'_eq, support_map]
      exact ⟨p, hp, rfl⟩)
  exact support_simulateQ_run'_subset (slotHandler prims D) X priv (by
    rw [StateT.run'_eq, support_map]
    exact ⟨p.1, h1, rfl⟩)

theorem stepRound_stepSetup {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepSetup (steps i))
    (z : A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E)))
    (hz : z ∈ support (stepRound worldRoles D A noFunctionality st steps)) : ∀ i, StepSetup (z.2.1 i) := by
  rw [stepRound_real, mem_support_bind_iff] at hz
  obtain ⟨r, -, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨steps', hsteps', hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact nextSteps_stepSetup D steps hsteps _ steps' hsteps'

/-- The rounds of a phase of a setup under `slotHandler` are the rounds of `R`. -/
theorem executeRounds_coupling {Ia α : Type} (prims : Primitives) (D : C.Coalition)
    (A R : Adversary C E Ia PEmpty PEmpty) (emb : KeyJointState C → A.State → R.State)
    (hR : ∀ priv st sent, R.round (emb priv st) sent = (fun r => (emb r.2 r.1.1, r.1.2)) <$>
      (simulateQ (slotHandler prims D) (worldRoles.adversary (A.round st sent))).run priv) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α), (∀ i, StepSetup (steps i)) →
      ∀ (priv : KeyJointState C) (h : HashCache C),
        (fun z => ((emb z.1.2 z.1.1.1, z.1.1.2), z.2)) <$>
          (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D)
            (executeRounds worldRoles D A noFunctionality fuel st steps)).run priv)).run h =
          (simulateQ (worldAnswer prims) (executeRounds worldRoles D R noFunctionality fuel (emb priv st) steps)).run h
  | 0, st, steps, _, priv, h => by simp [executeRounds]
  | fuel + 1, st, steps, hsteps, priv, h => by
    simp only [executeRounds]
    split_ifs with hdone
    · simp
    · rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
        ← stepRound_coupling prims D A R emb hR st steps hsteps priv h, bind_map_left, map_bind]
      refine bind_congr_of_forall_mem_support _ fun z hz => ?_
      exact executeRounds_coupling prims D A R emb hR fuel z.1.1.1 z.1.1.2.1
        (stepRound_stepSetup D A st steps hsteps z.1.1 (mem_support_twoLevel prims D _ priv h z hz)) z.1.2 z.2

/-- A phase of a setup, whose honest programs make only setup calls, under `slotHandler` is the phase
of `R`. -/
theorem executePhase_coupling {Ia α : Type} (prims : Primitives) (D : C.Coalition)
    (A R : Adversary C E Ia PEmpty PEmpty) (emb : KeyJointState C → A.State → R.State)
    (hR : ∀ priv st sent, R.round (emb priv st) sent = (fun r => (emb r.2 r.1.1, r.1.2)) <$>
      (simulateQ (slotHandler prims D) (worldRoles.adversary (A.round st sent))).run priv)
    (fuel : ℕ) (st : A.State) (program : C.Party → PartyM C E RealSpec α)
    (hprog : ∀ i, AllQueriesSatisfy (program i).run (PartySetup (E := E) (G := RealSpec)))
    (priv : KeyJointState C) (h : HashCache C) :
    (fun z => ((emb z.1.2 z.1.1.1, z.1.1.2), z.2)) <$>
      (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D)
        (executePhase worldRoles D A noFunctionality fuel st program)).run priv)).run h =
      (simulateQ (worldAnswer prims) (executePhase worldRoles D R noFunctionality fuel (emb priv st) program)).run h := by
  have hstart : AllQueriesSatisfy (startSteps worldRoles D program) HonestSetup := by
    refine sequenceFin_setup _ fun i => ?_
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact free_setup (advance_setup _ (hprog i))
  unfold executePhase
  simp only [simulateQ_bind, StateT.run_bind]
  rw [honest_run prims D _ hstart priv h, bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  have hsteps : ∀ i, StepSetup (z.1 i) := by
    have hz' : z.1 ∈ support (startSteps worldRoles D program) :=
      support_simulateQ_run'_subset (worldAnswer prims) _ h (by
        rw [StateT.run'_eq, support_map]
        exact ⟨z, hz, rfl⟩)
    intro i
    have hi := mem_support_sequenceFin_oc _ z.1 hz' i
    split_ifs at hi
    · simp only [support_pure, Set.mem_singleton_iff] at hi
      rw [hi]
      simp only [StepSetup]
    · exact advance_stepSetup _ (hprog i) _ (support_simulateQ_subset _ _ hi)
  exact executeRounds_coupling prims D A R emb hR fuel st z.1 hsteps priv z.2

end Phase

/-! ## Helpers of the reduction view -/

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

theorem allQueries_of_noCall {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa) :
    AllQueriesSatisfy oa fun t => ¬ WorldProgramQuery t :=
  (isQueryBoundP_zero_iff _ _).1 ((isQueryBoundP_congr_pred fun _ => not_not).2 ((noCall_iff _ _).1 h))

theorem bind_map_congr {α β γ : Type} {m₁ : ProbComp α} {m₂ : ProbComp β} {φ : β → α} {f : α → ProbComp γ}
    {g : β → ProbComp γ} (h : m₁ = φ <$> m₂) (hfg : ∀ b, f (φ b) =ᵈ g b) : m₁ >>= f =ᵈ m₂ >>= g := by
  subst h
  rw [bind_map_left]
  exact EvalDistEq.bind_congr EvalDistEq.rfl hfg

/-- An adversary whose rounds from `st` are idle keeps `st` through a phase. -/
theorem executePhase_idle {E Ia α : Type} (D : C.Coalition) (R : Adversary C E Ia PEmpty PEmpty) (st : R.State)
    (hR : ∀ sent, R.round st sent = pure (st, fun _ _ => none)) (fuel : ℕ) (program : C.Party → PartyM C E RealSpec α) :
    ∀ r ∈ support (executePhase worldRoles D R noFunctionality fuel st program), r.1 = st := by
  have rounds : ∀ (fuel : ℕ) (steps : C.Party → Step C E RealSpec α),
      ∀ r ∈ support (executeRounds worldRoles D R noFunctionality fuel st steps), r.1 = st := by
    intro fuel
    induction fuel with
    | zero =>
      intro steps r hr
      simp only [executeRounds, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
    | succ fuel ih =>
      intro steps r hr
      simp only [executeRounds] at hr
      split_ifs at hr
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
      · rw [stepRound_real, hR, mem_support_bind_iff] at hr
        obtain ⟨z, hz, hr⟩ := hr
        rw [mem_support_bind_iff] at hz
        obtain ⟨p, hp, hz⟩ := hz
        have hp' : p = (st, fun _ _ => none) := by simpa [worldRoles, counted] using hp
        subst hp'
        rw [mem_support_bind_iff] at hz
        obtain ⟨steps', -, hz⟩ := hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ih steps' r hr
  intro r hr
  unfold executePhase at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨steps, -, hr⟩ := hr
  exact rounds fuel steps r hr

/-! ## A discarded computation in the world -/

/-- A computation of the world with no programming call keeps its law when a computation with no
programming call and an unused result runs before it, from each cache. It is stated for `worldAnswer`. -/
def DiscardAnswer (prims : Primitives) : Prop :=
  ∀ {α : Type} (X : OracleComp (WorldSpec C) α) (Y : OracleComp (WorldSpec C) Bool) (cache : HashCache C),
    NoCall WorldProgramQuery X → NoCall WorldProgramQuery Y →
      (simulateQ (worldAnswer prims) (X >>= fun _ => Y)).run' cache =ᵈ (simulateQ (worldAnswer prims) Y).run' cache

/-- The calls of the world on the local oracles. A programming call, which no computation here makes,
answers `false`. -/
def toLocal : QueryImpl (WorldSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inl (.inl t) => liftM (OracleSpec.query (spec := LocalSpec C) t)
  | .inl (.inr _) => pure false
  | .inr t => liftM (OracleSpec.query (spec := LocalSpec C) t)

/-- With no programming call, the world is the local oracles of both copies. -/
theorem world_toLocal (prims : Primitives) {α : Type} (X : OracleComp (WorldSpec C) α)
    (hX : AllQueriesSatisfy X fun t => ¬ WorldProgramQuery t) :
    simulateQ (worldAnswer prims) X = simulateQ (localAnswer prims) (simulateQ toLocal X) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hX
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with (t | x) | t
    · simp only [toLocal, simulateQ_spec_query]
      exact bind_congr fun u => ih u (hX.2 u)
    · exact absurd trivial hX.1
    · simp only [toLocal, simulateQ_spec_query]
      exact bind_congr fun u => ih u (hX.2 u)

/-- From each cache, a computation with no programming call whose result is unused can be dropped
before a computation with no programming call. This is lazy sampling. The two computations commute,
and then the first one runs last and is discarded. -/
theorem discardAnswer (prims : Primitives) : DiscardAnswer (C := C) prims := by
  intro α X Y cache hX hY
  have hXY : AllQueriesSatisfy (X >>= fun _ => Y) fun t => ¬ WorldProgramQuery t :=
    allQueriesSatisfy_bind (allQueries_of_noCall hX) fun _ => allQueries_of_noCall hY
  rw [world_toLocal prims _ hXY, world_toLocal prims Y (allQueries_of_noCall hY), simulateQ_bind]
  have hswap := sameRun_swap prims (simulateQ toLocal X) (simulateQ toLocal Y) (fun _ b => pure b) cache
  simp only [bind_pure] at hswap
  rw [StateT.run'_eq, StateT.run'_eq]
  refine (hswap.map Prod.fst).trans ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_congr EvalDistEq.rfl fun a => ?_
  simp only [map_pure, Function.comp_apply]
  exact EvalDistEq.bind_const _ _

/-! ## No programming call in the hybrid game -/

section NoProgram

open ThresholdLeanXmssSecurity.SigningSelectionProof (noCall_bind noCall_pure noCall_map)

variable {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- A program on the state of the game that makes no programming call from each state. -/
def NoProg {σ α : Type} (m : RealM C σ α) : Prop := ∀ s, NoCall WorldProgramQuery (m.run s)

theorem NoProg.bind {σ α β : Type} {m : RealM C σ α} {f : α → RealM C σ β} (hm : NoProg m)
    (hf : ∀ a, NoProg (f a)) : NoProg (m >>= f) := fun s => by
  rw [StateT.run_bind]
  exact noCall_bind _ (hm s) fun p => hf p.1 p.2

theorem NoProg.pure {σ α : Type} (a : α) : NoProg (Pure.pure a : RealM C σ α) := fun _ => noCall_pure _ _

theorem NoProg.lift {σ α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa) :
    NoProg (StateT.lift oa : RealM C σ α) := fun s => by
  rw [StateT.run_lift]
  exact noCall_bind _ h fun _ => noCall_pure _ _

theorem NoProg.get {σ : Type} : NoProg (get : RealM C σ (RealState C σ)) := fun _ => noCall_pure _ _

theorem NoProg.set {σ : Type} (s' : RealState C σ) : NoProg (set s' : RealM C σ PUnit) := fun _ => noCall_pure _ _

theorem NoProg.modify {σ : Type} (f : RealState C σ → RealState C σ) : NoProg (modify f : RealM C σ PUnit) :=
  fun _ => noCall_pure _ _

theorem noProgram_wrongOutput (D : C.Coalition) (keys : C.Party → Option (Keys C)) (tree : Tree)
    (outputs : C.Party → Option TreeOutput) : NoCall WorldProgramQuery (wrongOutput D keys tree outputs) :=
  GameCount.wrongOutput_noCall D WorldProgramQuery (fun t ht hp => by
    rcases t with (_ | _) | _ <;> simp_all [GameCount.MonitorCall, WorldProgramQuery]) keys tree outputs

theorem noProg_fixedTreeRun (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    NoProg (fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net tree) := by
  unfold fixedTreeRun
  exact NoProg.get.bind fun s => (NoProg.lift (Collision.noProgram_free _)).bind fun fresh =>
    (NoProg.lift (Collision.noProgram_executePhase D net _ _ _)).bind fun r =>
      (NoProg.lift (noProgram_wrongOutput D _ tree _)).bind fun _ =>
        (NoProg.lift (Collision.noProgram_voteRound D net _ _)).bind fun _ => NoProg.set _

theorem noProg_fixedTreeRuns (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count, NoProg (fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net tree count)
  | 0 => NoProg.pure _
  | count + 1 => by
    unfold fixedTreeRuns
    refine NoProg.get.bind fun s => ?_
    split_ifs
    · exact (noProg_fixedTreeRun K circuits settings runLimit j D net tree).bind fun _ =>
        noProg_fixedTreeRuns j D net tree count
    · exact NoProg.pure _

theorem noProg_topLoop (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    ∀ count, NoProg (topLoop K circuits settings runLimit j D net count)
  | 0 => NoProg.pure _
  | count + 1 => by
    unfold topLoop
    refine NoProg.get.bind fun s => ?_
    split_ifs
    · exact (noProg_fixedTreeRun K circuits settings runLimit j D net .top).bind fun _ =>
        noProg_topLoop j D net count
    · exact NoProg.pure _

/-- The answer of an honest operator to a signing request is a computation of `H` and `PRG` on the
free copy, and it keeps the state of the game. -/
theorem operatorAnswer_eq_free {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) (st : TsigState C) :
    (operatorAnswer (m := RealM C σ) realLift (gameValue D operators) operator e q).run st =
      StateT.lift (free (liftComp ((operatorAnswer (fun oa => oa)
        (prfValue (gameSeeds D fun i => (operators i).keys)) operator e q).run st) (LocalSpec C))) := by
  have h1 := hom_operatorAnswer (realHom σ) (fun oa => free (liftComp oa (LocalSpec C)))
    (fun x => free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))) operator e q st
  have h2 := hom_operatorAnswer DkgCompletenessProof.freeHom (fun oa => oa)
    (prfValue (gameSeeds D fun i => (operators i).keys)) operator e q st
  exact h1.symm.trans (congrArg (StateT.lift (σ := RealState C σ)) h2.symm)

/-- The win test is a computation of `H` and `PRG` on the free copy, and it keeps the state. -/
theorem forgeryWins_eq_free {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (parameter : PublicParameter) (top : TopTree) (st : TsigState C) (forgery : Forgery) :
    forgeryWins (m := RealM C σ) realLift (canonicalDealt D operators parameter top) st forgery =
      StateT.lift (free (liftComp (forgeryWins (fun oa => oa)
        { dealtWith (fun oa => oa) parameter (fun i => ((operators i).keys).getD noKeys) top
            (prfValue (gameSeeds D fun i => (operators i).keys)) with
          bottom := fun b => pure (heldBottom D operators b) } st forgery) (LocalSpec C))) := by
  let dealt₀ : Dealt C (OracleComp (RoSpec C)) :=
    { dealtWith (fun oa => oa) parameter (fun i => ((operators i).keys).getD noKeys) top
        (prfValue (gameSeeds D fun i => (operators i).keys)) with
      bottom := fun b => pure (heldBottom D operators b) }
  have hom := hom_forgeryWins DkgCompletenessProof.freeHom (fun oa => oa) dealt₀ st forgery
  have hdealt : SeedHitProof.Dealt.hmap DkgCompletenessProof.freeHom dealt₀ = worldDealt D operators parameter top := by
    simp only [SeedHitProof.Dealt.hmap, dealt₀, worldDealt, dealtWith]
    rfl
  rw [hdealt] at hom
  rw [forgeryWins_canonicalDealt]
  exact congrArg (StateT.lift (σ := RealState C σ)) hom.symm

/-- A program of the signing phase that makes no programming call from each signing state and each
state of the game. -/
def NoProgT {σ α : Type} (m : StateT (TsigState C) (RealM C σ) α) : Prop := ∀ st, NoProg (m.run st)

theorem noProgT_simulateQ {σ ι : Type} {spec : OracleSpec ι} {α : Type}
    (impl : QueryImpl spec (StateT (TsigState C) (RealM C σ))) (h : ∀ t, NoProgT (impl t))
    (oa : OracleComp spec α) : NoProgT (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun st => NoProg.pure _
  | query_bind t k ih =>
    intro st
    rw [simulateQ_query_bind, StateT.run_bind]
    exact (h t st).bind fun p => ih p.1 p.2

theorem noProg_fixedTreeRequest (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) : NoProg (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b) := by
  unfold fixedTreeRequest
  refine (noProg_fixedTreeRuns K circuits settings runLimit j D net _ 1).bind fun _ => NoProg.get.bind fun s => ?_
  split
  · exact (NoProg.lift (Collision.noProgram_free _)).bind fun _ => NoProg.pure _
  · exact NoProg.pure _

theorem noProgT_signRequest {σ : Type} (D : C.Coalition) (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    NoProgT (signRequest (σ := σ) D i e q) := by
  intro st
  unfold signRequest
  simp only [StateT.run_bind, StateT.run_lift]
  refine ((NoProg.modify _).bind fun _ => NoProg.pure _).bind fun p => ?_
  refine (NoProg.get.bind fun _ => NoProg.pure _).bind fun p' => ?_
  rw [operatorAnswer_eq_free]
  exact NoProg.lift (Collision.noProgram_free _)

theorem NoProgT.lift {σ α : Type} {x : RealM C σ α} (h : NoProg x) :
    NoProgT (StateT.lift x : StateT (TsigState C) (RealM C σ) α) := fun st => by
  rw [StateT.run_lift]
  exact h.bind fun _ => NoProg.pure _

theorem noProgT_fixedOracles (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (q : (TsigSpec C).Domain) :
    NoProgT (fixedOracles K circuits settings runLimit j (wrongOutput D) D A q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun st => NoProg.pure _
  · exact NoProgT.lift (noProg_fixedTreeRequest K circuits settings runLimit j D A.net b)
  · exact noProgT_signRequest D i e _
  · exact noProgT_signRequest D i e _

theorem noProg_fixedSigning (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    NoProg (fixedSigning K circuits settings runLimit j (wrongOutput D) D A) := by
  unfold fixedSigning
  refine NoProg.get.bind fun s => ?_
  split
  · refine (noProgT_simulateQ _ (fun t => ?_) _ _).bind fun p => NoProg.get.bind fun s' => ?_
    · rcases t with t | q | q
      · exact NoProgT.lift (NoProg.lift (Collision.noProgram_adversary _))
      · exact noProgT_fixedOracles K circuits settings runLimit j D A q
      · rcases q with _ | state
        · exact NoProgT.lift (fun _ => noCall_pure _ _)
        · exact NoProgT.lift (NoProg.modify _)
    · rw [forgeryWins_eq_free]
      exact NoProg.lift (Collision.noProgram_free _)
  · exact NoProg.pure _

/-- A run of `tree` adds one to the runs of `tree`. -/
theorem fixedTreeRun_runs (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    ∀ r ∈ support ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net tree).run s),
      r.2.runs = Function.update s.runs tree (s.runs tree + 1) := by
  intro r hr
  unfold fixedTreeRun at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hr
  rfl

end NoProgram

/-! ## Phases with an operator that aborts at once -/

section Network

variable {E : Type}

/-- A program with an extra counter that erases, run from a counter and bound, is the erased program
bound to a continuation that ignores the counter. -/
theorem erases_run_bind {P : Type → Type} [Monad P] [LawfulMonad P] {σ α β : Type}
    (x : StateT σ (StateT ℕ P) α) (y : StateT σ P α) (hxy : HybridStartProof.Erases x y) (s : σ) (n : ℕ)
    (k2 : (α × σ) × ℕ → P β) (k1 : α × σ → P β) (hk : ∀ z, k2 z = k1 z.1) :
    (x.run s).run n >>= k2 = y.run s >>= k1 := by
  rw [← hxy s n, bind_map_left]
  exact bind_congr fun z => hk z

/-- A phase reads only the programs of the honest operators. -/
theorem executePhase_congr_honest {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (fuel : ℕ) (st : A.State) (p q : C.Party → PartyM C E RealSpec α) (h : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D A noFunctionality fuel st p = executePhase worldRoles D A noFunctionality fuel st q := by
  unfold executePhase startSteps
  congr 2
  funext i
  split_ifs with hi
  · rfl
  · rw [h i hi]

/-- A step that is done with no output, or that waits for a round that it aborts on an abort frame. -/
def AbortsAtRound {α : Type} (step : Step C E RealSpec α) : Prop :=
  step = .done none ∨ ∃ outbox resume, step = .wait outbox resume ∧
    ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none)

/-- The next step of an honest operator whose step aborts at the round, after an inbox with an abort
frame, is done with no output for each attached continuation. -/
theorem attach_next {α β : Type} (D : C.Coalition) (j : C.Party) (hj : j ∉ D.1) (k : α → PartyM C E RealSpec β)
    (step : Step C E RealSpec α) (hs : AbortsAtRound step) (inbox : Mail C E) (hab : ∃ k, inbox k = some .abort) :
    (match attachStep k step with
      | .done out => pure (Step.done out)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (resume inbox))
      | .call _ _ => pure (Step.done none) : OracleComp (WorldSpec C) (Step C E RealSpec β)) = pure (.done none) := by
  rcases hs with h | ⟨outbox, resume, h, habort⟩
  · subst h
    rfl
  · subst h
    simp only [attachStep, hj, ↓reduceIte]
    rw [advance_bind]
    change worldRoles.honest (advance (resume inbox) >>= continueStep k) = _
    rw [habort inbox hab, pure_bind]
    rfl

/-- The rounds of a phase in which an honest operator is done with no output and each other honest
step aborts at its round. The continuations attached to the steps are never run, so the rounds are
one program for each pair of continuations. -/
theorem executeRounds_dead_congr {Ia α β : Type} (D : C.Coalition) (net : Adversary C E Ia PEmpty PEmpty)
    (fuel : ℕ) (st : net.State) (v : C.Party → Step C E RealSpec α) (k1 k2 : C.Party → α → PartyM C E RealSpec β)
    (i₀ : C.Party) (hi₀ : i₀ ∉ D.1) (h₀ : v i₀ = .done none) (hv : ∀ i, i ∉ D.1 → AbortsAtRound (v i))
    (hD : ∀ i, i ∈ D.1 → v i = .done none) :
    executeRounds worldRoles D net noFunctionality fuel st (fun i => attachStep (k1 i) (v i)) =
      executeRounds worldRoles D net noFunctionality fuel st (fun i => attachStep (k2 i) (v i)) := by
  have hdone : ∀ i, (attachStep (k1 i) (v i)).isDone ↔ (attachStep (k2 i) (v i)).isDone := fun i => by
    cases v i <;> rfl
  have hout : ∀ i, (attachStep (k1 i) (v i)).output = (attachStep (k2 i) (v i)).output := fun i => by
    cases v i <;> rfl
  have hdel : ∀ i, (attachStep (k1 i) (v i)).delivered = (attachStep (k2 i) (v i)).delivered := fun i => by
    cases v i <;> rfl
  cases fuel with
  | zero => simp only [executeRounds, hout]
  | succ fuel =>
    simp only [executeRounds, hdone, hout]
    split_ifs
    · rfl
    · rw [stepRound_real, stepRound_real]
      have hbox : ∀ i, (attachStep (k1 i) (v i)).outbox = (attachStep (k2 i) (v i)).outbox := fun i => by
        cases v i <;> rfl
      simp only [hbox, bind_assoc]
      refine bind_congr fun r => ?_
      have hnext : nextSteps D (fun i => attachStep (k1 i) (v i)) r.2 = nextSteps D (fun i => attachStep (k2 i) (v i)) r.2 := by
        unfold nextSteps
        congr 1
        funext j
        simp only [hdel]
        by_cases hj : j ∈ D.1
        · rw [hD j hj]
          rfl
        · have hab : ∃ k, (fun k => if k ∈ D.1 then r.2 k j else (attachStep (k2 k) (v k)).delivered j) k = some .abort :=
            ⟨i₀, by simp only [hi₀, ↓reduceIte, h₀]; rfl⟩
          rw [attach_next D j hj (k1 j) (v j) (hv j hj) _ hab, attach_next D j hj (k2 j) (v j) (hv j hj) _ hab]
      rw [hnext]

/-- A phase in which an honest operator aborts at once and each honest program starts with a round
is one program for each pair of continuations of the honest programs. -/
theorem executePhase_dead_congr {Ia α β : Type} (D : C.Coalition) (net : Adversary C E Ia PEmpty PEmpty)
    (fuel : ℕ) (st : net.State) (X : C.Party → PartyM C E RealSpec α) (k1 k2 : C.Party → α → PartyM C E RealSpec β)
    (i₀ : C.Party) (hi₀ : i₀ ∉ D.1) (hdead : X i₀ = failure) (hround : ∀ i, i ∉ D.1 → StartsWithRound (X i)) :
    executePhase worldRoles D net noFunctionality fuel st (fun i => X i >>= k1 i) =
      executePhase worldRoles D net noFunctionality fuel st (fun i => X i >>= k2 i) := by
  have hstart : ∀ k : C.Party → α → PartyM C E RealSpec β,
      startSteps worldRoles D (fun i => X i >>= k i) =
        OverPermutation.sequenceFin (fun i => (if i ∈ D.1 then pure (Step.done none) else free (advance (X i).run)))
          >>= fun v => pure fun i => attachStep (k i) (v i) := by
    intro k
    unfold startSteps
    rw [← sequenceFin_bind_pure]
    congr 1
    funext i
    split_ifs with hi
    · rw [pure_bind]
      rfl
    · change free (advance (X i >>= k i).run) = _
      rw [advance_bind, ThresholdLeanXmssSecurity.free_bind]
      refine bind_congr_of_forall_mem_support _ fun s hs => ?_
      have hs' := support_free_subset _ hs
      rw [continueStep_attach]
      · rfl
      · rcases hround i hi s hs' with h | ⟨outbox, resume, h, _⟩ <;> rw [h] <;> rfl
  unfold executePhase
  rw [hstart k1, hstart k2, bind_assoc, bind_assoc]
  refine bind_congr_of_forall_mem_support _ fun v hv => ?_
  simp only [pure_bind]
  have hmem := mem_support_sequenceFin_oc _ v hv
  refine executeRounds_dead_congr D net fuel st v k1 k2 i₀ hi₀ ?_ (fun i hi => ?_) (fun i hi => ?_)
  · have h := hmem i₀
    simp only [hi₀, ↓reduceIte] at h
    have h' := support_free_subset _ h
    rw [hdead, advance_run_failure, support_pure, Set.mem_singleton_iff] at h'
    exact h'
  · have h := hmem i
    simp only [hi, ↓reduceIte] at h
    exact hround i hi _ (support_free_subset _ h)
  · have h := hmem i
    simp only [hi, ↓reduceIte, support_pure, Set.mem_singleton_iff] at h
    exact h

end Network

/-! ## One joint law of `jointKeyWorld` and a private draw -/

section Joint

variable (prims : Primitives)

/-- Two computations with one law of the result and of the state of `jointKeyWorld`, from each state. -/
def JEq (D : C.Coalition) {α : Type} (X Y : OracleComp (WorldSpec C) α) : Prop :=
  ∀ w : KeyJointState C, (simulateQ (jointKeyWorld prims D false) X).run w =ᵈ
    (simulateQ (jointKeyWorld prims D false) Y).run w

theorem JEq.of_eq {D : C.Coalition} {α : Type} {X Y : OracleComp (WorldSpec C) α} (h : X = Y) :
    JEq prims D X Y := fun _ => h ▸ EvalDistEq.rfl

theorem JEq.bind {D : C.Coalition} {α β : Type} {X Y : OracleComp (WorldSpec C) α}
    {f g : α → OracleComp (WorldSpec C) β} (h : JEq prims D X Y) (hfg : ∀ a, JEq prims D (f a) (g a)) :
    JEq prims D (X >>= f) (Y >>= g) := fun w => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact (h w).bind fun p => hfg p.1 p.2

theorem JEq.bind_support {D : C.Coalition} {α β : Type} (X : OracleComp (WorldSpec C) α)
    {f g : α → OracleComp (WorldSpec C) β} (hfg : ∀ a ∈ support X, JEq prims D (f a) (g a)) :
    JEq prims D (X >>= f) (X >>= g) := fun w => by
  simp only [simulateQ_bind, StateT.run_bind]
  refine EvalDistEq.bind_congr_of_support ((simulateQ (jointKeyWorld prims D false) X).run w)
    fun p hp => hfg p.1 ?_ p.2
  exact support_simulateQ_run'_subset (jointKeyWorld prims D false) X w (by
    rw [StateT.run'_eq, support_map]
    exact ⟨p, hp, rfl⟩)

theorem JEq.trans {D : C.Coalition} {α : Type} {X Y Z : OracleComp (WorldSpec C) α} (h1 : JEq prims D X Y)
    (h2 : JEq prims D Y Z) : JEq prims D X Z := fun w => (h1 w).trans (h2 w)

/-- A private draw on the free copy keeps the state of `jointKeyWorld`. -/
theorem jointKeyWorld_sample_run (D : C.Coalition) {α : Type} (p : ProbComp α) (w : KeyJointState C) :
    (simulateQ (jointKeyWorld prims D false) (free (liftComp p (LocalSpec C)))).run w = (fun a => (a, w)) <$> p := by
  induction p using OracleComp.inductionOn generalizing w with
  | pure a => simp
  | query_bind n k ih =>
    have e : free (liftComp (liftM (unifSpec.query n) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inl n))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    simp only [jointKeyWorld, jointKeyWorldCore, jointLocal, onJointHash, keyJointRisk, unifFwdImpl,
      StateT.run_mk, Bool.or_false, map_bind, ih]
    simp

/-- A private draw on the free copy commutes with each computation in `jointKeyWorld`. -/
theorem freeDraw_commutes (D : C.Coalition) {α β γ : Type} (p : ProbComp α) (X : OracleComp (WorldSpec C) β)
    (g : α → β → OracleComp (WorldSpec C) γ) :
    JEq prims D (free (liftComp p (LocalSpec C)) >>= fun a => X >>= fun b => g a b)
      (X >>= fun b => free (liftComp p (LocalSpec C)) >>= fun a => g a b) := fun w => by
  simp only [simulateQ_bind, StateT.run_bind, jointKeyWorld_sample_run, bind_map_left]
  exact EvalDistEq.bind_bind_swap p _ _

end Joint

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.partition_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.partition_run

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.executePhase_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.executePhase_coupling

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.discardAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.discardAnswer

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.freeDraw_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.freeDraw_commutes

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.executePhase_dead_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.executePhase_dead_congr
