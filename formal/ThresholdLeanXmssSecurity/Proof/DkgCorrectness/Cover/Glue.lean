import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.PhaseAbort
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutBounds
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.SharesAgree
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.MonitorReplay
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HeadLaw
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Cells

/-!
# The cover of a ceremony and a local tail

A run of the top tree, and the rest of a bottom tree after the cut, is one ceremony and then a local
tail with no round, and then the monitor. `cover_of_tail` bounds a wrong output of such a run with no
global event by wrong opened outputs of the ceremony with no global event. It needs the PRF cells of
the jobs in the cache at the end of the ceremony, which `CeremonyCells` states. `topCover_of_cells`
and `restCover_of_cells` give `TopCover` and `RestCover` from `CeremonyCells`, and
`topCover_of_started` and `restCover_of_started` give them from the lock step `CeremonyStarted`.
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

/-! ## A phase on the network -/

section Phase

variable (prims : Primitives) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each honest output of a phase in `streamWorld` is an output of its program with `H` fixed to each
good `h` that agrees with the end cache. -/
theorem executePhase_onPath {α : Type} (fuel : ℕ) (st : net.State) (program : C.Party → PartyM C E RealSpec α)
    (s : StreamState C) (z : (net.State × (C.Party → Option α)) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executePhase worldRoles D net noFunctionality fuel st program)).run s))
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h z.2.1) :
    ∀ i, i ∉ D.1 → ∀ a, z.1.2 i = some a → some a ∈ support (simulateQ (fixHash h) (program i).run) := by
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startSteps at hy
  have hseq := sequenceFin_streamWorld prims D (fun j v c => j ∉ D.1 → ∀ h, Good prims h → Agrees h c →
      OnPath h (program j).run v) _
    (fun j b c c' hq hle hj h hg hagree => hq hj h hg (hagree.mono hle)) (fun j s' w hw hj h hg hagree => ?_) s y hy
  · exact executeRounds_onPath prims D D net (fun j => (program j).run) fuel st y.1 y.2 z hz h hg ha
      (fun i hi => hseq i hi h hg (ha.mono (streamWorld_run_mono prims D _ y.2 z hz)))
  simp only [hj, ↓reduceIte] at hw
  exact (advance_onPath prims D _ s' w hw).2 h hg hagree

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase whose honest programs end at once returns their outputs, with no round and no change of
the world. -/
theorem executePhase_ready {α : Type} (fuel : ℕ) (st : net.State) (outs : C.Party → Option α)
    (w : StreamState C) :
    (simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality fuel st
      fun i => (outs i).elim failure pure)).run w =
      pure ((st, fun i => if i ∈ D.1 then none else outs i), w) := by
  have hstart : startSteps worldRoles D (fun i => ((outs i).elim failure pure : PartyM C E RealSpec α)) =
      pure fun i => Step.done (if i ∈ D.1 then none else outs i) := by
    unfold startSteps
    rw [← sequenceFin_pure]
    congr 1
    funext i
    dsimp only
    split_ifs with hi
    · rfl
    · rcases outs i with _ | a
      · change (worldRoles (C := C)).honest (advance (pure none)) = _
        rw [advance_pure, worldRoles_honest_pure]
      · change (worldRoles (C := C)).honest (advance (pure (some a))) = _
        rw [advance_pure, worldRoles_honest_pure]
  unfold executePhase
  rw [hstart, pure_bind]
  cases fuel <;> simp [executeRounds, Step.isDone, Step.output]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem executeRounds_short {α : Type} (n : ℕ) :
    ∀ (fuel : ℕ) (st : net.State) (steps : C.Party → Step C E RealSpec α),
      (∀ i ∈ D.1, steps i = .done none) → (∀ i ∉ D.1, StepTimed (fuel + n + 1) (steps i)) →
      ∀ r ∈ support (executeRounds worldRoles D net noFunctionality fuel st steps), ∀ i, i ∉ D.1 → r.2 i = none
  | 0, st, steps, _, ht, r, hr, i, hi => by
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact (ht i hi).output_none
  | fuel + 1, st, steps, hD, ht, r, hr, i, hi => by
    unfold executeRounds at hr
    split_ifs at hr with hdone
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact (ht i hi).output_none
    · simp only [support_bind, Set.mem_iUnion] at hr
      obtain ⟨q, hq, hr⟩ := hr
      obtain ⟨hD', ht'⟩ := WorldSplit.stepRound_timed_world D net noFunctionality (fuel + n + 1) st steps hD
        (fun j hj => by rw [show fuel + n + 1 + 1 = fuel + 1 + n + 1 by omega]; exact ht j hj) q hq
      exact executeRounds_short n fuel q.1 q.2.1 hD' ht' r hr i hi

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase of fewer rounds than the exact rounds of the honest programs gives no honest output. -/
theorem executePhase_short {α : Type} (a fuel : ℕ) (hlt : fuel < a) (st : net.State)
    (program : C.Party → PartyM C E RealSpec α) (hp : ∀ i ∉ D.1, Timed a (program i).run) (s : StreamState C)
    (z : (net.State × (C.Party → Option α)) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executePhase worldRoles D net noFunctionality fuel st program)).run s)) :
    ∀ i, i ∉ D.1 → z.1.2 i = none := by
  have hz' : z.1 ∈ support (executePhase worldRoles D net noFunctionality fuel st program) :=
    support_simulateQ_run'_subset (streamWorld prims D)
      (executePhase worldRoles D net noFunctionality fuel st program) s
      (by rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)
  unfold executePhase at hz'
  simp only [support_bind, Set.mem_iUnion] at hz'
  obtain ⟨s0, hs0, hz'⟩ := hz'
  obtain ⟨hD, ht⟩ := WorldSplit.startSteps_timed_world D a program hp s0 hs0
  obtain ⟨n, rfl⟩ : ∃ n, a = fuel + n + 1 := ⟨a - fuel - 1, by omega⟩
  exact executeRounds_short D net n fuel st s0 hD ht z.1 hz'

end Phase

/-! ## The PRF cells of a ceremony -/

section Cells

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The circuit values of jobs on `hashOf` of a cache are the values on each `h` that agrees with the
cache, when the cache holds the PRF cells of the jobs. -/
theorem evalRun_hashOf_of_cells (parameter : PublicParameter) (seeds : C.Term → HashOutput) (c : HashCache C)
    (h : Query C → HashOutput) (ha : Agrees h c) (jobs : List Job)
    (hcells : ∀ job ∈ jobs, ∀ T, PrfCached c (seeds T) job.points) :
    evalRun prims circuits parameter seeds (hashOf prims c) jobs = evalRun prims circuits parameter seeds h jobs := by
  rw [evalRun_eq, evalRun_eq]
  congr 1
  refine List.map_congr_left fun job hjob => ?_
  rw [D_evalJob, D_evalJob]
  congr 1
  congr 1
  refine List.map_congr_left fun x hx => ?_
  congr 2
  funext T
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hcells job hjob T x hx)
  rw [ha _ v hv]
  simp [hashOf, hv]

end Cells

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

/-! ## The cover of a ceremony and a local tail -/

section Cover

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The program of an operator in one ceremony takes exactly the rounds of its PRSS setup and its
batches under the parameter of its keys. -/
theorem timed_ceremonyProgram (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (parameter : PublicParameter)
    (h : ∀ keys, c.keys i = some keys → keys.parameter = parameter) :
    Timed (setupRounds + Fuel.batchesRounds circuits settings parameter c.jobs)
      (ceremonyProgram K circuits settings i c).run := by
  unfold ceremonyProgram
  split
  · rename_i keys hk
    rw [← h keys hk, ← Nat.add_zero (setupRounds + _)]
    refine (Fuel.runTimed_ceremonyRun K circuits settings i keys c.jobs c.counters).bind fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · exact timed_failure 0
    · exact timed_pure _
  · exact timed_failure _

omit [Fintype E] [DecidableEq E] in
/-- The cells of `CeremonyCells` for each start with consistent keys. An honest operator with no keys
leaves no honest result. -/
theorem cells_of_ceremonyCells (cells : CeremonyCells prims K circuits settings) (hsize : 0 < settings.batchSize)
    (rounds : ℕ) (c : CeremonyStart C net.State) (w : StreamState C) (hw : NoMpc w.1)
    (hseeds : seedsDiffer D c.keys = false) :
    ∀ y ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run w), ¬ GlobalEvent y.2 →
      (∃ i, i ∉ D.1 ∧ (y.1.2 i).isSome) → ∀ job ∈ c.jobs, ∀ T, PrfCached y.2.1 (gameSeeds D c.keys T) job.points := by
  intro y hy hge hout
  by_cases hdead : ∃ i, i ∉ D.1 ∧ c.keys i = none
  · obtain ⟨i, hi, hsome⟩ := hout
    rw [ceremonyDead prims K circuits settings D net rounds c w y hy hdead i hi] at hsome
    cases hsome
  · refine cells hsize D net rounds c w hw hseeds (fun i hi => ?_) y hy hge hout
    rcases hk : c.keys i with _ | keys
    · exact absurd ⟨i, hi, hk⟩ hdead
    · rfl

omit [Fintype E] [DecidableEq E] in
/-- A ceremony in `a + b` rounds has the law of the ceremony in `a` rounds, when each honest program
takes exactly `a` rounds. The corrupt operators have no result. -/
theorem ceremonyPhase_fuel (a b : ℕ) (c : CeremonyStart C net.State)
    (htimed : ∀ i ∉ D.1, Timed a (ceremonyProgram K circuits settings i c).run) (w : StreamState C) :
    (ceremonyPhase prims K circuits settings D net (a + b) c).run w =ᵈ
      (fun y => ((y.1.1, fun i => if i ∈ D.1 then none else y.1.2 i), y.2)) <$>
        (ceremonyPhase prims K circuits settings D net a c).run w := by
  unfold ceremonyPhase
  have h := WorldSplit.executePhase_split prims D net a b c.adversary
    (fun i => ceremonyProgram K circuits settings i c) (fun _ => pure) htimed w
  simp only [bind_pure] at h
  refine h.trans ?_
  simp only [simulateQ_bind, StateT.run_bind, executePhase_ready, map_eq_bind_pure_comp]
  exact .rfl

omit [Fintype E] [DecidableEq E] in
/-- The cover of a ceremony and a local tail. A run of `a + b` rounds of a ceremony that takes exactly
`a` rounds, then a local tail, then the monitor, gives a wrong output with no global event at most as
likely as the ceremony gives wrong opened outputs with no global event. The premises are the PRF cells
of the jobs at the end of the ceremony, and the value of the tail with `H` fixed to each good `h` that
agrees with the start cache, from right outputs of the ceremony on `h`. -/
theorem cover_of_tail (a b : ℕ) (c : CeremonyStart C net.State)
    (tail : C.Party → CeremonyResult → PartyM C E RealSpec TreeOutput)
    (keys : C.Party → Option (Keys C)) (tree : Tree) (w : StreamState C) (hw : NoMpc w.1)
    (htimed : ∀ i ∉ D.1, Timed a (ceremonyProgram K circuits settings i c).run)
    (hcells : ∀ y ∈ support ((ceremonyPhase prims K circuits settings D net a c).run w), ¬ GlobalEvent y.2 →
      (∃ i, i ∉ D.1 ∧ (y.1.2 i).isSome) → ∀ job ∈ c.jobs, ∀ T, PrfCached y.2.1 (gameSeeds D c.keys T) job.points)
    (htail : ∀ i, i ∉ D.1 → ∀ (o : CeremonyResult) (h : Query C → HashOutput), Good prims h → Agrees h w.1 →
      some o.1 = evalRun prims circuits (gameParameter D c.keys) (gameSeeds D c.keys) h c.jobs →
      ∀ out, some out ∈ support (simulateQ (fixHash h) (tail i o).run) →
        some out = ThresholdLeanXmssSecurity.D prims h (GhostMonitor.monitorReference D keys tree)) :
    Pr{let r ← (simulateQ (streamWorld prims D) (do
        let r ← executePhase worldRoles D net noFunctionality (a + b) c.adversary fun i =>
          ceremonyProgram K circuits settings i c >>= tail i
        let bad ← wrongOutput D keys tree r.2
        pure (r, bad))).run w}[r.1.2 = true ∧ ¬ GlobalEvent r.2] ≤
      Pr{let r ← (ceremonyPhase prims K circuits settings D net (a + b) c).run w}[
        WrongCeremony prims circuits D c r ∧ ¬ GlobalEvent r.2] := by
  have hsplit := WorldSplit.executePhase_split prims D net a b c.adversary
    (fun i => ceremonyProgram K circuits settings i c) tail htimed w
  have hL : (simulateQ (streamWorld prims D) (do
        let r ← executePhase worldRoles D net noFunctionality (a + b) c.adversary fun i =>
          ceremonyProgram K circuits settings i c >>= tail i
        let bad ← wrongOutput D keys tree r.2
        pure (r, bad))).run w =ᵈ
      ((ceremonyPhase prims K circuits settings D net a c).run w >>= fun y =>
        (simulateQ (streamWorld prims D) (do
          let r ← executePhase worldRoles D net noFunctionality b y.1.1 fun i => (y.1.2 i).elim failure (tail i)
          let bad ← wrongOutput D keys tree r.2
          pure (r, bad))).run y.2) := by
    unfold ceremonyPhase
    simp only [simulateQ_bind, StateT.run_bind] at hsplit ⊢
    exact (hsplit.bind fun p => .rfl).trans (by rw [bind_assoc])
  rw [hL.prEvent_eq, (ceremonyPhase_fuel prims K circuits settings D net a b c htimed w).prEvent_eq, prEvent_map]
  refine (prEvent_bind_le_prEvent_of_support _ _
    (fun y => WrongCeremony prims circuits D c y ∧ ¬ GlobalEvent y.2) _ ?_).trans (le_of_eq ?_)
  · intro y hy hnot
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun ω hω hbad => hnot ?_
    obtain ⟨v, hv, u, hu, rfl⟩ := GhostMonitor.mem_support_run_test _ _ _ _ _ hω
    rw [GhostMonitor.wrongOutput_eq] at hu
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    have hyv : y.2.1 ≤ v.2.1 := streamWorld_run_mono prims D _ y.2 v hv
    have hvr : v.2.1 ≤ r.2.1 := streamWorld_run_mono prims D _ v.2 r hr
    have hwy : w.1 ≤ y.2.1 := streamWorld_run_mono prims D _ w y hy
    have hno : NoMpc r.2.1 := streamWorld_noMpc prims D _ v.2
      (streamWorld_noMpc prims D _ y.2 (streamWorld_noMpc prims D _ w hw y hy) v hv) r hr
    obtain ⟨hbad, hge⟩ := hbad
    simp only [decide_eq_true_eq] at hbad
    have hglobal : ¬ GlobalEvent y.2 := fun h => hge (globalEvent_mono (hyv.trans hvr) h)
    refine ⟨?_, hglobal⟩
    by_contra hnw
    obtain ⟨i, hi, hsome, hne⟩ := hbad
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.1 hsome
    have hg := good_hashOf prims r.2.1
    have ha := agrees_hashOf prims hno
    have href := (GhostMonitor.refW_monitorReference prims D keys tree).1 v.2 r hr _ hg ha
    have hpath := executePhase_onPath prims D net b y.1.1 _ y.2 v hv _ hg (ha.mono hvr) i hi out hout
    rcases hyi : y.1.2 i with _ | o
    · rw [hyi] at hpath
      simp [OptionT.run_failure] at hpath
    rw [hyi] at hpath
    have hcell := hcells y hy hglobal ⟨i, hi, by rw [hyi]; rfl⟩
    have hright : some o.1 = evalRun prims circuits (gameParameter D c.keys) (gameSeeds D c.keys)
        (hashOf prims r.2.1) c.jobs := by
      rw [← evalRun_hashOf_of_cells prims circuits _ _ y.2.1 _ (ha.mono (hyv.trans hvr)) c.jobs hcell]
      by_contra hw'
      exact hnw ⟨i, hi, o, hyi, hw'⟩
    refine hne ?_
    rw [hout, href]
    exact htail i hi o _ hg (ha.mono (hwy.trans (hyv.trans hvr))) hright out hpath
  · refine prEvent_congr _ _ _ fun y => ?_
    simp only [WrongCeremony]
    constructor
    · rintro ⟨⟨i, hi, o, ho, hw'⟩, hg⟩
      exact ⟨⟨i, hi, o, by simpa [hi] using ho, hw'⟩, hg⟩
    · rintro ⟨⟨i, hi, o, ho, hw'⟩, hg⟩
      exact ⟨⟨i, hi, o, by simpa [hi] using ho, hw'⟩, hg⟩

end Cover

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

/-! ## The top tree -/

section Top

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The local tail of the top tree after its ceremony at an operator, namely the root of the chain
ends. An operator with no keys aborts. -/
def topTail (operator : OperatorState C) (o : CeremonyResult) : PartyM C E RealSpec TreeOutput :=
  match operator.keys with
  | some keys => (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter (fun _ => pure (some o.1)) emptyTop
        .top).run' o.2 >>= fun out => out.elim failure pure
  | none => failure

omit [Fintype E] [DecidableEq E] in
/-- The program of the top tree is its ceremony and then its local tail. -/
theorem treeProgram_top (i : C.Party) {σ : Type} (s : RealState C σ) :
    treeProgram K circuits settings i (s.operators i) .top =
      ceremonyProgram K circuits settings i (topStart s) >>= topTail (s.operators i) := by
  unfold treeProgram ceremonyProgram topTail topStart
  rcases hk : (s.operators i).keys with _ | keys
  · simp only [hk, failure_bind]
  · simp only
    rw [hk]
    unfold newTree
    simp only [ceremonyOutput, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · simp only [Option.elim, failure_bind, StateT.run_pure, map_pure, pure_bind]
    · simp only [Option.elim, pure_bind, StateT.run_pure]
      refine bind_congr fun out => ?_
      rcases out with _ | out <;> rfl

end Top

/-! ## A local program with `H` fixed -/

section Fixed

/-- Each outcome of a program on the counters with `H` fixed to `h` has a value with `P`. -/
def FixedVal (h : Query C → HashOutput) {β : Type} (P : β → Prop) (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) :
    Prop :=
  ∀ st z, z ∈ support (simulateQ (fixHash h) (x.run st).run) → ∀ b st', z = some (b, st') → P b

variable (h : Query C → HashOutput)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem fixedVal_pure {β : Type} (P : β → Prop) (b : β) (hb : P b) :
    FixedVal (E := E) h P (pure b) := by
  intro st z hz a st' hza
  simp only [StateT.run_pure, OptionT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  cases hza
  exact hb

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem fixedVal_bind {β γ : Type} (Q : β → Prop) (P : γ → Prop) (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (f : β → StateT (ℕ × ℕ) (PartyM C E RealSpec) γ) (hx : FixedVal h Q x) (hf : ∀ b, Q b → FixedVal h P (f b)) :
    FixedVal h P (x >>= f) := by
  intro st z hz a st' hza
  subst hza
  rw [StateT.run_bind, OptionT.run_bind, Option.elimM, simulateQ_bind, mem_support_bind_iff] at hz
  obtain ⟨o, ho, hz⟩ := hz
  rcases o with _ | ⟨b, st₁⟩
  · simp at hz
  · exact hf b (hx st _ ho b st₁ rfl) st₁ _ hz a st' rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A local hash computation has the value with `H` fixed to `h`. -/
theorem fixedVal_hash (prims : Primitives) {β : Type} (oa : OracleComp HashSpec β) :
    FixedVal (E := E) h (· = ThresholdLeanXmssSecurity.D prims h (tweakable oa))
      (StateT.lift (oracleStep (tweakable oa))) := by
  intro st z hz a st' hza
  subst hza
  rw [StateT.run_lift, OptionT.run_bind, Option.elimM, simulateQ_bind,
    fixHash_oracleStep_tweakable prims h oa, pure_bind] at hz
  simp at hz
  exact hz.1

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A ceremony output from fixed opened outputs has, with `H` fixed to `h`, the value in the clear. -/
theorem fixedVal_ceremonyOutput (prims : Primitives) (parameter : PublicParameter)
    (run' : List Job → Option (List (List Bit))) (top : TopTree) (tree : Tree) :
    FixedVal (E := E) h (· = ceremonyOutput (m := Id) (fun oa => ThresholdLeanXmssSecurity.D prims h (tweakable oa))
        parameter run' top tree)
      (ceremonyOutput (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter (fun js => pure (run' js)) top
        tree) :=
  rel_ceremonyOutput (fun P x => FixedVal h P x) (fun P b hb => fixedVal_pure h P b hb)
    (fun Q P x f hx hf => fixedVal_bind h Q P x f hx hf) _ _ (fun oa => fixedVal_hash h prims oa) _ _
    (fun _ => fixedVal_pure h _ _ rfl) parameter top tree

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An output of a program on the counters that aborts on `none` has, with `H` fixed to `h`, the value
of the program. -/
theorem fixedVal_elim {P : Option TreeOutput → Prop} {x : StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput)}
    (hx : FixedVal h P x) (st : ℕ × ℕ) (out : TreeOutput)
    (hout : some out ∈ support (simulateQ (fixHash h) ((x.run' st >>= fun o => o.elim failure pure :
      PartyM C E RealSpec TreeOutput)).run)) : P (some out) := by
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, mem_support_bind_iff, StateT.run'_eq] at hout
  obtain ⟨o, ho, hout⟩ := hout
  rw [OptionT.run_map, simulateQ_map, support_map] at ho
  obtain ⟨p, hp, rfl⟩ := ho
  rcases p with _ | ⟨v, st'⟩
  · simp at hout
  · have hv := hx st _ hp v st' rfl
    rcases v with _ | v
    · simp [OptionT.run_failure] at hout
    · simp at hout
      rw [hout]
      exact hv

end Fixed

/-! ## The clean world -/

section Clean

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `hashOf` reads no cell on an input of the MPC. -/
theorem hashOf_cleanCache (c : HashCache C) : hashOf prims (MpcCells.cleanCache c) = hashOf prims c := by
  funext q
  cases q with
  | hash x =>
    by_cases hx : MpcInput x
    · simp [hashOf, hx]
    · simp only [hashOf, hx, ↓reduceIte]
      rw [MpcCells.cleanCache_of_not fun ⟨_, he, hm⟩ => hx (by cases he; exact hm)]
  | _ => simp only [hashOf]; rw [MpcCells.cleanCache_of_not fun ⟨_, he, _⟩ => by cases he]

omit [Fintype E] [DecidableEq E] in
/-- A ceremony from the clean world has the law of the ceremony on wrong outputs with no global event. -/
theorem ceremonyPhase_clean (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (w : StreamState C) :
    Pr{let r ← (ceremonyPhase prims K circuits settings D net rounds c).run (MpcCells.cleanWorld w)}[
        WrongCeremony prims circuits D c r ∧ ¬ GlobalEvent r.2] =
      Pr{let r ← (ceremonyPhase prims K circuits settings D net rounds c).run w}[
        WrongCeremony prims circuits D c r ∧ ¬ GlobalEvent r.2] := by
  unfold ceremonyPhase
  rw [MpcCells.streamWorld_run_clean, prEvent_map]
  refine prEvent_congr _ _ _ fun r => ?_
  simp only [WrongCeremony, WrongOutputs, Prod.map_fst, Prod.map_snd, id_eq, MpcCells.cleanWorld,
    hashOf_cleanCache]
  rw [show ((MpcCells.cleanCache r.2.1, r.2.2) : StreamState C) = MpcCells.cleanWorld r.2 from rfl,
    MpcCells.globalEvent_cleanWorld]

end Clean

/-! ## `TopCover` -/

section TopLeaf

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `TopCover` from the PRF cells of a ceremony. -/
theorem topCover_of_cells (cells : CeremonyCells prims K circuits settings) :
    TopCover prims K circuits settings := by
  intro hsize compute budget D net s world ready _
  rw [← ceremonyPhase_clean]
  have hL : Pr{let r ← (streamTreeRun prims K circuits settings D net .top s).run world}[
      r.1.2 = true ∧ ¬ GlobalEvent r.2] =
      Pr{let r ← (streamTreeRun prims K circuits settings D net .top s).run (MpcCells.cleanWorld world)}[
        r.1.2 = true ∧ ¬ GlobalEvent r.2] := by
    rw [MpcCells.streamTreeRun_clean, prEvent_map]
    refine prEvent_congr _ _ _ fun r => ?_
    simp only [Prod.map_fst, Prod.map_snd, id_eq, MpcCells.globalEvent_cleanWorld]
  rw [hL]
  have hw : NoMpc (MpcCells.cleanWorld world).1 := MpcCells.noMpc_cleanCache _
  have ready' := MpcCells.runReady_cleanWorld prims budget D ready
  generalize MpcCells.cleanWorld world = w at ready' hw ⊢
  obtain ⟨parameter, hpar⟩ := exists_parameter D s ready'.1
  have hj : (topStart (σ := net.State) s).jobs = topJobs := by simp only [topStart]
  obtain ⟨a, ha⟩ : ∃ a, setupRounds + Fuel.batchesRounds circuits settings parameter (topStart s).jobs = a :=
    ⟨_, rfl⟩
  have hale : a ≤ treeFuel circuits settings := by
    have := topRounds_le circuits settings parameter
    rw [hj] at ha
    unfold treeFuel
    unfold Fuel.batchesRounds at ha
    omega
  obtain ⟨b, hb⟩ : ∃ b, treeFuel circuits settings = a + b := ⟨_, (Nat.add_sub_cancel' hale).symm⟩
  have htimed : ∀ i ∉ D.1, Timed a (ceremonyProgram K circuits settings i (topStart s)).run := by
    intro i hi
    rw [← ha]
    exact timed_ceremonyProgram K circuits settings i (topStart s) parameter (hpar i hi)
  unfold streamTreeRun
  rw [show (fun i => treeProgram K circuits settings i (s.operators i) .top) =
      fun i => ceremonyProgram K circuits settings i (topStart s) >>= topTail (s.operators i) from
    funext fun i => treeProgram_top K circuits settings i s, hb]
  refine cover_of_tail prims K circuits settings D net a b (topStart s)
    (fun i => topTail (s.operators i)) (fun i => (s.operators i).keys) .top w hw htimed
    (cells_of_ceremonyCells prims K circuits settings D net cells hsize a (topStart s) w hw ready'.1) ?_
  intro i hi o h hg _ hright out hpath
  rcases hk : (s.operators i).keys with _ | keys
  · simp only [topTail, hk] at hpath
    simp [OptionT.run_failure] at hpath
  simp only [topTail, hk] at hpath
  have hval := fixedVal_elim h (fixedVal_ceremonyOutput h prims keys.parameter (fun _ => some o.1) emptyTop .top)
    o.2 out hpath
  rw [hval]
  have hparam := parameter_eq_gameParameter D (fun j => (s.operators j).keys) ready'.1 i hi keys hk
  have hmon : ThresholdLeanXmssSecurity.D prims h
      (GhostMonitor.monitorReference D (fun j => (s.operators j).keys) .top) =
      ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
        (prfValue (gameSeeds D fun j => (s.operators j).keys)) keys.parameter emptyTop .top) := by
    rw [hparam]
    unfold GhostMonitor.monitorReference
    rw [D_bind]
    exact D_pure (prims := prims) h _
  rw [hmon, ← ceremonyAt_eq_referenceTree prims circuits compute hg]
  unfold ceremonyAt
  simp only [ceremonyOutput]
  rw [hj] at hright
  change some o.1 = evalRun prims circuits (gameParameter D fun j => (s.operators j).keys)
    (gameSeeds D fun j => (s.operators j).keys) h topJobs at hright
  rw [← hparam] at hright
  rw [← hright]

end TopLeaf

/-! ## The local parts of a bottom tree -/

section BottomLocal

variable {m : Type → Type} [Monad m] (lift : ∀ {β : Type}, OracleComp HashSpec β → m β)

/-- The local search of a bottom tree after its first ceremony, from the opened outputs. -/
def firstLocal (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) :
    m (Option (List (List Bit) × Digest × Randomizer × Encoding)) := do
  let root ← lift (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)
  let base ← lift (truncateHash <$> Verification.oracleHashWithHash
    (randomizerInput parameter topLayer (topKey b) (bRho b outputs) (littleEndianBytes 16 root)))
  let some (randomness, encoding) ← lift (grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base
      randomizerAttemptLimit 0) | pure none
  pure (some (outputs, root, randomness, encoding))

/-- The local end of a bottom tree after its signature ceremony, from the result `x` of the search and
the opened values. -/
def secondLocal (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (values : List (List Bit)) : m (Option TreeOutput) := do
  let path ← lift (merklePath parameter topLayer top.chainEnd (topKey b))
  let signature : LayerSignature := ⟨x.2.2.1, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← lift (Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 x.2.1)
    signature)
  if topRoot ≠ some top.root then pure none else
  pure (some (.bottom ⟨bCpk b x.1, bCommitment b x.1, x.2.1, signature⟩))

/-- A bottom tree is its first ceremony, the local search, the signature ceremony and the local end. -/
theorem ceremonyOutput_bottom_split [LawfulMonad m] (parameter : PublicParameter)
    (run : List Job → m (Option (List (List Bit)))) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    ceremonyOutput lift parameter run top (.bottom b) =
      run (bottomJobs b) >>= fun o => o.elim (pure none) fun outputs =>
        firstLocal lift parameter b outputs >>= fun g => g.elim (pure none) fun x =>
          run (signJobs b x.2.2.2) >>= fun o' => o'.elim (pure none) (secondLocal lift parameter top b x) := by
  simp only [ceremonyOutput, firstLocal, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | outputs
  · simp only [Option.elim]
  · simp only [bCpk, bRho, bottomKeys, Option.elim]
    refine bind_congr fun root => bind_congr fun base => bind_congr fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · simp only [pure_bind]
    · simp only [pure_bind]
      refine bind_congr fun o' => ?_
      rcases o' with _ | values
      · rfl
      · rfl

end BottomLocal

/-! ## The programs of a bottom tree as ceremonies and local tails -/

section BottomPrograms

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The local search of a bottom tree after its first ceremony at an operator. An operator with no keys
aborts. -/
def headTail (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) (o : CeremonyResult) :
    PartyM C E RealSpec HeadResult :=
  match operator.keys with
  | some keys => (firstLocal (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter b o.1).run o.2 >>=
      fun p => p.1.elim failure fun x => pure (x, p.2)
  | none => failure

/-- The local end of a bottom tree after its signature ceremony at an operator, from the result `x` of
the search. An operator with no keys or no top tree aborts. -/
def secondTail (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (o : CeremonyResult) : PartyM C E RealSpec TreeOutput :=
  match operator.keys, operator.top with
  | some keys, some top => (secondLocal (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter top b x o.1).run' o.2 >>=
      fun out => out.elim failure pure
  | _, _ => failure

omit [Fintype E] [DecidableEq E] in
theorem firstPart_split (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) :
    CheckTiming.firstPart K circuits settings i keys b =
      ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys (bottomJobs b) >>=
        fun o => o.elim (pure none) (firstLocal (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter b) := by
  unfold CheckTiming.firstPart
  refine bind_congr fun o => ?_
  rcases o with _ | outputs
  · rfl
  · rfl

omit [Fintype E] [DecidableEq E] in
theorem secondPart_split (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) :
    CheckTiming.secondPart K circuits settings i keys top b x =
      ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys
        (signJobs b x.2.2.2) >>=
        fun o => o.elim (pure none) (secondLocal (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter top b x) := by
  unfold CheckTiming.secondPart
  refine bind_congr fun o => ?_
  rcases o with _ | values
  · rfl
  · rfl

omit [Fintype E] [DecidableEq E] in
/-- The head of a bottom tree is its first ceremony and then the local search. -/
theorem bottomHead_split (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    CheckTiming.bottomHead K circuits settings i (s.operators i) b =
      ceremonyProgram K circuits settings i (firstStart b s) >>= headTail (E := E) (s.operators i) b := by
  unfold CheckTiming.bottomHead ceremonyProgram firstStart aliveKeys headTail
  rcases hk : (s.operators i).keys with _ | keys <;> rcases ht : (s.operators i).top with _ | top
  · simp only [hk, ht, failure_bind]
  · simp only [hk, ht, failure_bind]
  · simp only [hk, ht, failure_bind]
  · simp only [hk, ht]
    rw [firstPart_split K circuits settings i keys b]
    simp only [StateT.run_bind, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · simp only [Option.elim, StateT.run_pure, pure_bind, failure_bind]
    · simp only [Option.elim, pure_bind]

omit [Fintype E] [DecidableEq E] in
/-- The rest of a bottom tree after the cut is its signature ceremony and then the local end. -/
theorem bottomTail_split (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) (st : σ)
    (x : HeadResult) :
    CheckTiming.bottomTail K circuits settings i (s.operators i) b x =
      ceremonyProgram K circuits settings i (secondStart b s st x) >>= secondTail (E := E) (s.operators i) b x.1 := by
  unfold CheckTiming.bottomTail ceremonyProgram secondStart aliveKeys secondTail
  rcases hk : (s.operators i).keys with _ | keys <;> rcases ht : (s.operators i).top with _ | top
  · simp only [hk, ht, failure_bind]
  · simp only [hk, ht, failure_bind]
  · simp only [hk, ht, failure_bind]
  · simp only [hk, ht]
    rw [secondPart_split K circuits settings i keys top b x.1]
    simp only [StateT.run_bind, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | values, st'⟩
    · simp only [Option.elim, StateT.run_pure, pure_bind, failure_bind]
    · simp only [Option.elim, pure_bind, StateT.run'_eq, bind_map_left]

end BottomPrograms

/-! ## The local parts of a bottom tree with `H` fixed -/

section BottomRel

variable {m : Type → Type} [Monad m] (S : ∀ {β : Type}, (β → Prop) → m β → Prop)
  (hpure : ∀ {β : Type} (P : β → Prop) (b : β), P b → S P (pure b))
  (hbind : ∀ {β γ : Type} (Q : β → Prop) (P : γ → Prop) (x : m β) (f : β → m γ),
    S Q x → (∀ b, Q b → S P (f b)) → S P (x >>= f))
  (lift : ∀ {β : Type}, OracleComp HashSpec β → m β) (lift' : ∀ {β : Type}, OracleComp HashSpec β → β)
  (hl : ∀ {β : Type} (oa : OracleComp HashSpec β), S (· = lift' oa) (lift oa))

include hpure hbind hl in
theorem rel_firstLocal (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) :
    S (· = firstLocal (m := Id) (fun oa => lift' oa) parameter b outputs) (firstLocal lift parameter b outputs) := by
  simp only [firstLocal, id_bind_eq]
  refine hbind _ _ _ _ (hl _) fun root hroot => ?_
  subst hroot
  refine hbind _ _ _ _ (hl _) fun base hbase => ?_
  subst hbase
  refine hbind _ _ _ _ (hl _) fun g hg => ?_
  simp only [← hg]
  rcases g with _ | ⟨randomness, encoding⟩ <;> exact hpure _ _ rfl

include hpure hbind hl in
theorem rel_secondLocal (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (values : List (List Bit)) :
    S (· = secondLocal (m := Id) (fun oa => lift' oa) parameter top b x values)
      (secondLocal lift parameter top b x values) := by
  simp only [secondLocal, id_bind_eq]
  refine hbind _ _ _ _ (hl _) fun path hpath => ?_
  subst hpath
  refine hbind _ _ _ _ (hl _) fun topRoot htopRoot => ?_
  simp only [← htopRoot]
  split_ifs <;> exact hpure _ _ rfl

end BottomRel

section BottomFixed

variable (prims : Primitives) (h : Query C → HashOutput)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem fixedVal_firstLocal (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) :
    FixedVal (E := E) h (· = firstLocal (m := Id) (fun oa => ThresholdLeanXmssSecurity.D prims h (tweakable oa))
        parameter b outputs)
      (firstLocal (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter b outputs) :=
  rel_firstLocal (fun P x => FixedVal h P x) (fun P b hb => fixedVal_pure h P b hb)
    (fun Q P x f hx hf => fixedVal_bind h Q P x f hx hf) _ _ (fun oa => fixedVal_hash h prims oa) parameter b outputs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem fixedVal_secondLocal (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (values : List (List Bit)) :
    FixedVal (E := E) h (· = secondLocal (m := Id) (fun oa => ThresholdLeanXmssSecurity.D prims h (tweakable oa))
        parameter top b x values)
      (secondLocal (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter top b x values) :=
  rel_secondLocal (fun P x => FixedVal h P x) (fun P b hb => fixedVal_pure h P b hb)
    (fun Q P x f hx hf => fixedVal_bind h Q P x f hx hf) _ _ (fun oa => fixedVal_hash h prims oa) parameter top b x
    values

end BottomFixed

/-! ## Helpers of the rest of a bottom tree -/

section RestHelpers

variable (prims : Primitives) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase reads only the programs of the honest operators. -/
theorem executePhase_congr {α : Type} (fuel : ℕ) (st : net.State) (p q : C.Party → PartyM C E RealSpec α)
    (h : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D net noFunctionality fuel st p = executePhase worldRoles D net noFunctionality fuel st q := by
  unfold executePhase startSteps
  congr 2
  funext i
  split_ifs with hi
  · rfl
  · rw [h i hi]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase with no honest output gives no wrong output. -/
theorem monitor_false (fuel : ℕ) (st : net.State) (prog : C.Party → PartyM C E RealSpec TreeOutput)
    (keys : C.Party → Option (Keys C)) (tree : Tree) (w : StreamState C)
    (hnone : ∀ v ∈ support ((simulateQ (streamWorld prims D)
      (executePhase worldRoles D net noFunctionality fuel st prog)).run w), ∀ i, i ∉ D.1 → v.1.2 i = none) :
    ∀ ω ∈ support ((simulateQ (streamWorld prims D) (do
      let r ← executePhase worldRoles D net noFunctionality fuel st prog
      let bad ← wrongOutput D keys tree r.2
      pure (r, bad))).run w), ω.1.2 = false := by
  intro ω hω
  obtain ⟨v, hv, u, hu, rfl⟩ := GhostMonitor.mem_support_run_test _ _ _ _ _ hω
  rw [GhostMonitor.wrongOutput_eq] at hu
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hu
  obtain ⟨r, -, rfl⟩ := hu
  simp only [decide_eq_false_iff_not]
  rintro ⟨i, hi, hsome, -⟩
  rw [hnone v hv i hi] at hsome
  cases hsome

/-- The local search returns the outputs of the first ceremony. -/
theorem firstLocal_fst (lift' : ∀ {β : Type}, OracleComp HashSpec β → β) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (x : List (List Bit) × Digest × Randomizer × Encoding)
    (hx : firstLocal (m := Id) (fun oa => lift' oa) parameter b outputs = some x) : x.1 = outputs := by
  unfold firstLocal at hx
  simp only [id_bind_eq] at hx
  split at hx
  · cases hx
    rfl
  · cases hx

end RestHelpers

/-! ## The cut of a bottom tree -/

section CutHead

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An outcome of a program on the counters and a continuation, with `H` fixed to `h`, continues from
a value with `P`. -/
theorem fixedVal_run_bind (h : Query C → HashOutput) {α β : Type} {P : α → Prop}
    {y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α} (hy : FixedVal h P y) (st : ℕ × ℕ)
    (g : α × (ℕ × ℕ) → PartyM C E RealSpec β) (out : β)
    (hout : some out ∈ support (simulateQ (fixHash h) ((y.run st >>= g).run))) :
    ∃ a st', P a ∧ some out ∈ support (simulateQ (fixHash h) (g (a, st')).run) := by
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, mem_support_bind_iff] at hout
  obtain ⟨o, ho, hout⟩ := hout
  rcases o with _ | ⟨a, st'⟩
  · simp at hout
  · exact ⟨a, st', hy st _ ho a st' rfl, hout⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem aliveKeys_eq_some {σ : Type} (s : RealState C σ) (i : C.Party) (k : Keys C) (h : aliveKeys s i = some k) :
    (s.operators i).keys = some k ∧ ∃ top, (s.operators i).top = some top := by
  unfold aliveKeys at h
  split at h
  · rename_i hk ht
    cases h
    exact ⟨hk, _, ht⟩
  · cases h

/-- The cut of a bottom tree at which each honest operator holds the head result `x`, with no global
event. Each honest operator has keys and a top tree, the search of `x` is the local search on its first
outputs with `H` fixed to each good `h` that agrees with the cut cache, and the cut cache holds the PRF
cells of the first ceremony. -/
theorem cut_head (cells : CeremonyCells prims K circuits settings) (hsize : 0 < settings.batchSize)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) (s : RealState C net.State)
    (world : StreamState C) (hw : NoMpc world.1) (n : ℕ) (hseeds : seedsDiffer D (fun i => (s.operators i).keys) = false)
    (z : (net.State × (C.Party → Option HeadResult)) × StreamState C)
    (hz : z ∈ support ((bottomCut prims K circuits settings D net b s n).run world)) (x : HeadResult)
    (hx : ∀ i, i ∉ D.1 → z.1.2 i = some x) (hge : ¬ GlobalEvent z.2) (i : C.Party) (hi : i ∉ D.1)
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h z.2.1) :
    ∃ keys, (s.operators i).keys = some keys ∧ (∀ j, j ∉ D.1 → aliveKeys s j = (s.operators j).keys) ∧
      firstLocal (m := Id) (fun oa => ThresholdLeanXmssSecurity.D prims h (tweakable oa)) keys.parameter b x.1.1 =
        some x.1 ∧
      ∀ job ∈ bottomJobs b, ∀ T, PrfCached z.2.1 (gameSeeds D (aliveKeys s) T) job.points := by
  obtain ⟨parameter, hpar⟩ := exists_parameter D s hseeds
  have hkeys : seedsDiffer D (aliveKeys s) = false := seedsDiffer_sub D _ _ (aliveKeys_some s) hseeds
  obtain ⟨a, ha1⟩ : ∃ a, setupRounds + Fuel.batchesRounds circuits settings parameter (firstStart b s).jobs = a :=
    ⟨_, rfl⟩
  have htimed : ∀ j ∉ D.1, Timed a (ceremonyProgram K circuits settings j (firstStart b s)).run := by
    intro j hj
    rw [← ha1]
    exact timed_ceremonyProgram K circuits settings j (firstStart b s) parameter
      fun k hk => hpar j hj k (aliveKeys_some s j k hk)
  by_cases hlt : n < a
  · have hfirst : CheckTiming.firstRounds circuits settings parameter (.bottom b) = a := by
      rw [← ha1]
      exact (CheckTiming.batchesRounds_eq circuits settings parameter (bottomJobs b)).symm
    have hnone := executePhase_short prims D net a n hlt s.adversary _
      (fun j hj => hfirst ▸ CheckTiming.timed_bottomHead K circuits settings parameter j (s.operators j) b
        (hpar j hj)) world z hz i hi
    rw [hx i hi] at hnone
    cases hnone
  obtain ⟨b₁, rfl⟩ : ∃ b₁, n = a + b₁ := ⟨n - a, by omega⟩
  have hsplit := WorldSplit.executePhase_split prims D net a b₁ s.adversary
    (fun j => ceremonyProgram K circuits settings j (firstStart b s)) (fun j => headTail (s.operators j) b) htimed world
  have hz' := hz
  unfold bottomCut at hz'
  rw [show (fun j => CheckTiming.bottomHead K circuits settings j (s.operators j) b) =
      fun j => ceremonyProgram K circuits settings j (firstStart b s) >>= headTail (E := E) (s.operators j) b from
    funext fun j => bottomHead_split K circuits settings j s b, support_eq_of_evalDistEq hsplit] at hz'
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz'
  obtain ⟨y, hy, hzy⟩ := hz'
  have hyz : y.2.1 ≤ z.2.1 := streamWorld_run_mono prims D _ y.2 z hzy
  have hpath := executePhase_onPath prims D net b₁ y.1.1 _ y.2 z hzy h hg ha i hi x (hx i hi)
  rcases hyi : y.1.2 i with _ | o
  · rw [hyi] at hpath
    simp [OptionT.run_failure] at hpath
  rw [hyi] at hpath
  have halive : ∀ j, j ∉ D.1 → ∃ k, aliveKeys s j = some k := by
    intro j hj
    by_contra hnot
    have hdead : ∃ j, j ∉ D.1 ∧ (firstStart b s).keys j = none :=
      ⟨j, hj, Option.eq_none_iff_forall_not_mem.2 fun k hk => hnot ⟨k, hk⟩⟩
    have := ceremonyDead prims K circuits settings D net a (firstStart b s) world y hy hdead i hi
    rw [hyi] at this
    cases this
  obtain ⟨k, hk⟩ := halive i hi
  obtain ⟨hki, -⟩ := aliveKeys_eq_some s i k hk
  refine ⟨k, hki, fun j hj => ?_, ?_, ?_⟩
  · obtain ⟨kj, hkj⟩ := halive j hj
    rw [hkj, (aliveKeys_eq_some s j kj hkj).1]
  · simp only [Option.elim_some, headTail, hki] at hpath
    obtain ⟨v, st', hv, hpath⟩ := fixedVal_run_bind h
      (fixedVal_firstLocal prims h k.parameter b o.1) o.2 _ x hpath
    rcases v with _ | x₁
    · simp [OptionT.run_failure] at hpath
    simp at hpath
    subst hpath
    have hfst := firstLocal_fst (fun {β} (oa : OracleComp HashSpec β) =>
      ThresholdLeanXmssSecurity.D prims h (tweakable oa)) k.parameter b o.1 x₁ hv.symm
    rw [hfst]
    exact hv.symm
  · intro job hjob T
    exact (cells_of_ceremonyCells prims K circuits settings D net cells hsize a (firstStart b s) world hw hkeys y hy
      (fun hgy => hge (globalEvent_mono hyz hgy)) ⟨i, hi, by rw [hyi]; rfl⟩ job hjob T).mono hyz

end CutHead

/-! ## `RestCover` -/

section RestLeaf

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The local end of a bottom tree takes no round. -/
theorem timed_secondTail (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (o : CeremonyResult) :
    Timed 0 (secondTail (E := E) operator b x o).run := by
  unfold secondTail
  split
  · rename_i keys top _ _
    have hrun : RunTimed 0 (secondLocal (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter top b x o.1) := by
      unfold secondLocal
      refine (RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun path => ?_).of_eq rfl
      refine (RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun topRoot => ?_).of_eq rfl
      split_ifs
      · exact runTimed_pure _
      · exact runTimed_pure _
    have h1 := (Timed.map Prod.fst (hrun o.2)).bind (n := 0) fun out =>
      show Timed 0 (out.elim failure pure : PartyM C E RealSpec TreeOutput).run by
        rcases out with _ | out
        · exact timed_failure 0
        · exact timed_pure out
    exact h1
  · exact timed_failure 0

/-- `RestCover` from a start with no MPC cell in the hash cache. -/
theorem restCover_core (cells : CeremonyCells prims K circuits settings) (hsize : 0 < settings.batchSize)
    (compute : CircuitsCompute circuits prims.Th)
    (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (hw : NoMpc world.1) (n m : ℕ)
    (ready : RunReady prims budget D s world)
    (z : (net.State × (C.Party → Option HeadResult)) × StreamState C)
    (hz : z ∈ support ((bottomCut prims K circuits settings D net b s n).run world)) (x : HeadResult)
    (hx : ∀ i, i ∉ D.1 → z.1.2 i = some x) (hfw : ¬ FirstWrong prims circuits D b s z) :
    Pr{let y ← (bottomRest prims K circuits settings D net b s z.1.1 z.1.2 m).run z.2}[
        y.1.2 = true ∧ ¬ GlobalEvent y.2] ≤
      Pr{let r ← (ceremonyPhase prims K circuits settings D net m (secondStart b s z.1.1 x)).run z.2}[
        WrongCeremony prims circuits D (secondStart b s z.1.1 x) r ∧ ¬ GlobalEvent r.2] := by
  by_cases hge : GlobalEvent z.2
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun y hy h =>
      h.2 (cutMonotone prims K circuits settings D net b s z.1.1 z.1.2 m z.2 hge y hy)]
    exact bot_le
  have hwz : world.1 ≤ z.2.1 := streamWorld_run_mono prims D _ world z hz
  have hz2 : NoMpc z.2.1 := streamWorld_noMpc prims D _ world hw z hz
  obtain ⟨parameter, hpar⟩ := exists_parameter D s ready.1
  have hkeys : seedsDiffer D (aliveKeys s) = false := seedsDiffer_sub D _ _ (aliveKeys_some s) ready.1
  obtain ⟨a, ha⟩ : ∃ a, setupRounds + Fuel.batchesRounds circuits settings parameter
      (secondStart b s z.1.1 x).jobs = a := ⟨_, rfl⟩
  have htimed : ∀ j ∉ D.1, Timed a (ceremonyProgram K circuits settings j (secondStart b s z.1.1 x)).run := by
    intro j hj
    rw [← ha]
    exact timed_ceremonyProgram K circuits settings j (secondStart b s z.1.1 x) parameter
      fun k hk => hpar j hj k (aliveKeys_some s j k hk)
  have hprog : executePhase worldRoles D net noFunctionality m z.1.1 (fun i =>
      (z.1.2 i).elim failure (CheckTiming.bottomTail K circuits settings i (s.operators i) b)) =
      executePhase worldRoles D net noFunctionality m z.1.1 (fun i =>
        ceremonyProgram K circuits settings i (secondStart b s z.1.1 x) >>= secondTail (s.operators i) b x.1) :=
    executePhase_congr D net m z.1.1 _ _ fun i hi => by
      rw [hx i hi, Option.elim_some, bottomTail_split K circuits settings i s b z.1.1 x]
  unfold bottomRest
  rw [hprog]
  by_cases hlt : m < a
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun y hy h => ?_) bot_le
    have hfalse := monitor_false prims D net m z.1.1 _ (fun i => (s.operators i).keys) (.bottom b) z.2
      (fun v hv => executePhase_short prims D net a m hlt z.1.1 _ (fun j hj => by
        simpa only [Nat.add_zero] using (htimed j hj).bind (n := 0) fun o => timed_secondTail _ b x.1 o)
        z.2 v hv) y hy
    rw [hfalse] at h
    exact absurd h.1 (by simp)
  obtain ⟨b₂, rfl⟩ : ∃ b₂, m = a + b₂ := ⟨m - a, by omega⟩
  refine cover_of_tail prims K circuits settings D net a b₂ (secondStart b s z.1.1 x)
    (fun i => secondTail (s.operators i) b x.1) (fun i => (s.operators i).keys) (.bottom b) z.2 hz2 htimed
    (cells_of_ceremonyCells prims K circuits settings D net cells hsize a _ z.2 hz2 hkeys) ?_
  intro i hi o h hg haz hright out hpath
  obtain ⟨k, hki, halive, hfirst, hcells⟩ :=
    cut_head prims K circuits settings cells hsize D net b s world hw n ready.1 z hz x hx hge i hi h hg haz
  rcases ht : (s.operators i).top with _ | top
  · simp [secondTail, hki, ht, OptionT.run_failure] at hpath
  simp only [secondTail, hki, ht] at hpath
  have hval := fixedVal_elim h (fixedVal_secondLocal prims h k.parameter top b x.1 o.1) o.2 out hpath
  rw [hval]
  have hS := gameSeeds_congr D halive
  have hP := gameParameter_congr D halive
  have hparam := parameter_eq_gameParameter D (fun j => (s.operators j).keys) ready.1 i hi k hki
  have hfirstRight : some x.1.1 = evalRun prims circuits (gameParameter D fun j => (s.operators j).keys)
      (gameSeeds D fun j => (s.operators j).keys) h (bottomJobs b) := by
    have h1 : ¬ WrongOutputs prims circuits D (fun j => (s.operators j).keys) (bottomJobs b) z.2.1 x.1.1 :=
      fun hw => hfw ⟨i, hi, x, hx i hi, hw⟩
    unfold WrongOutputs at h1
    rw [not_not] at h1
    rw [h1, evalRun_hashOf_of_cells prims circuits _ _ z.2.1 h haz _ (by rw [← hS]; exact hcells)]
  change some o.1 = evalRun prims circuits (gameParameter D (aliveKeys s)) (gameSeeds D (aliveKeys s)) h
    (signJobs b x.1.2.2.2) at hright
  rw [hS, hP] at hright
  have htopRef : ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
      (prfValue (gameSeeds D fun j => (s.operators j).keys)) (gameParameter D fun j => (s.operators j).keys)
      emptyTop .top) = some (.top top) :=
    GhostMonitor.refW_forall prims D (GhostMonitor.refW_referenceTree prims D _ _ _ _) world h hg (haz.mono hwz)
      (· = some (.top top)) (ready.2.1 i hi top ht)
  have hmon : ThresholdLeanXmssSecurity.D prims h
      (GhostMonitor.monitorReference D (fun j => (s.operators j).keys) (.bottom b)) =
      ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
        (prfValue (gameSeeds D fun j => (s.operators j).keys)) (gameParameter D fun j => (s.operators j).keys)
        top (.bottom b)) := by
    unfold GhostMonitor.monitorReference
    rw [D_bind, htopRef]
    rfl
  rw [hmon, ← ceremonyAt_eq_referenceTree prims circuits compute hg]
  unfold ceremonyAt
  rw [ceremonyOutput_bottom_split, ← hfirstRight, ← hparam]
  rw [← hparam] at hright
  rw [id_bind_eq, Option.elim_some, hfirst, id_bind_eq, Option.elim_some, ← hright, id_bind_eq, Option.elim_some]

/-- `RestCover` from the PRF cells of a ceremony. -/
theorem restCover_of_cells (cells : CeremonyCells prims K circuits settings) :
    RestCover prims K circuits settings := by
  intro hsize compute budget D net b s world n m ready _ z hz x hx hfw
  have hz' : ((z.1, MpcCells.cleanWorld z.2) : (net.State × (C.Party → Option HeadResult)) × StreamState C) ∈
      support ((bottomCut prims K circuits settings D net b s n).run (MpcCells.cleanWorld world)) := by
    unfold bottomCut
    rw [MpcCells.streamWorld_run_clean, support_map]
    exact ⟨z, hz, rfl⟩
  have hfw' : ¬ FirstWrong prims circuits D b s (z.1, MpcCells.cleanWorld z.2) := by
    simpa only [FirstWrong, WrongOutputs, MpcCells.cleanWorld, hashOf_cleanCache] using hfw
  have hL : Pr{let y ← (bottomRest prims K circuits settings D net b s z.1.1 z.1.2 m).run z.2}[
      y.1.2 = true ∧ ¬ GlobalEvent y.2] =
      Pr{let y ← (bottomRest prims K circuits settings D net b s z.1.1 z.1.2 m).run (MpcCells.cleanWorld z.2)}[
        y.1.2 = true ∧ ¬ GlobalEvent y.2] := by
    unfold bottomRest
    rw [MpcCells.streamWorld_run_clean, prEvent_map]
    refine prEvent_congr _ _ _ fun r => ?_
    simp only [Prod.map_fst, Prod.map_snd, id_eq, MpcCells.globalEvent_cleanWorld]
  rw [hL, ← ceremonyPhase_clean]
  exact restCover_core prims K circuits settings cells hsize compute budget D net b s (MpcCells.cleanWorld world)
    (MpcCells.noMpc_cleanCache _) n m (MpcCells.runReady_cleanWorld prims budget D ready) _ hz' x hx hfw'

end RestLeaf

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.topCover_of_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.topCover_of_cells

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.restCover_of_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.restCover_of_cells

section
open ThresholdLeanXmss

set_option autoImplicit false

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `TopCover` from the lock step of one ceremony. -/
theorem topCover_of_started (started : CeremonyStarted prims K circuits settings) :
    TopCover prims K circuits settings :=
  topCover_of_cells prims K circuits settings (ceremonyCells_of_started prims K circuits settings started)

/-- `RestCover` from the lock step of one ceremony. -/
theorem restCover_of_started (started : CeremonyStarted prims K circuits settings) :
    RestCover prims K circuits settings :=
  restCover_of_cells prims K circuits settings (ceremonyCells_of_started prims K circuits settings started)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.topCover_of_started' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.topCover_of_started

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.restCover_of_started' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.restCover_of_started
