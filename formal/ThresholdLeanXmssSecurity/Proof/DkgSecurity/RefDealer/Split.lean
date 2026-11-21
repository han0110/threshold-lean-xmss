import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Hops
import ThresholdLeanXmssSecurity.Proof.Pilot.Outputs
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Erasure
import ThresholdLeanXmssSecurity.Proof.Pilot.Final
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Search
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.Birthday
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.MonitorReplay

/-!
# The split of `SharedRefDealer`

`RefInv keys D s w` is the invariant of a state `s` of the game with the world `w`. Each honest
operator holds the keys `keys`, the hash cache holds no input that the MPC evaluates with `Th`, and
with no flag the honest keys are consistent and each kept output of an honest operator is the
output of `referenceTree` on the seeds and the parameter of the game, for each good `H` that agrees
with the hash cache.

* `RefRunKeeps` states that one real recorded run keeps the invariant. `refRunKeeps_of_clean`
  proves it from `PassCleanOutput`, the outputs of one run with no bad check and no global event.
  `passCleanOutput_of` proves `PassCleanOutput` from `PassWrongCheck`.
* `RefSigning` compares the two signing phases from a state with the invariant.
  `refSigning_of_ghosts` proves it from `GhostErase` and `GhostCouple`, through `ghostSigning`, the
  signing phase of the real game with the calls of the dealer as ghosts.
* `sharedRefDealer_of_parts` proves `SharedRefDealer` from `RefRunKeeps` and `RefSigning`.
* `FlagUp` states that the flag of the game stays set.
* `LeArrow` is a one-sided coupling of two programs for the order of two event probabilities, with
  the rules for a composition, a common source, an escape of the left side and `simulateQ`
  (`leArrow_simulateQ`).
* `GhostRel` is the relation of the two sides of `GhostCouple` between two calls, `GhostStep` the
  step of one call and `GhostWin` the step of the win test.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The invariant -/

/-- The honest keys are consistent, and each kept output of an honest operator is the output of
`referenceTree` on the seeds and the parameter of the game, for each good `h` that agrees with
`cache`. A bottom tree has the kept top tree of its operator. -/
def RefOutputs (D : C.Coalition) {σ : Type} (s : RealState C σ) (cache : HashCache C) : Prop :=
  seedsDiffer D (fun i => (s.operators i).keys) = false ∧
    ∀ i, i ∉ D.1 → ∀ h, Good prims h → Agrees h cache →
      (∀ t, (s.operators i).top = some t →
        ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
          (prfValue (gameSeeds D fun i => (s.operators i).keys)) (gameParameter D fun i => (s.operators i).keys)
          emptyTop .top) = some (.top t)) ∧
      (∀ b bt, (s.operators i).bottom b = some bt → ∃ t, (s.operators i).top = some t ∧
        ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
          (prfValue (gameSeeds D fun i => (s.operators i).keys)) (gameParameter D fun i => (s.operators i).keys)
          t (.bottom b)) = some (.bottom bt))

/-- The invariant of a state of the game. Each operator holds the keys `keys`, the hash cache holds
no input that the MPC evaluates with `Th`, and with no flag the kept outputs are the reference
outputs. -/
def RefInv (keys : C.Party → Option (Keys C)) (D : C.Coalition) {σ : Type} (s : RealState C σ) (w : LogState C) :
    Prop :=
  (∀ i, (s.operators i).keys = keys i) ∧ NoMpc w.1.1 ∧ (s.flag = false → RefOutputs prims D s w.1.1)

/-! ## The parts -/

/-- One real recorded run of `tree` keeps the invariant. With no flag after the run, no honest
operator kept a wrong output, because a wrong output needs a bad check in the records of the run or a
global event after it. -/
def RefRunKeeps : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (keys : C.Party → Option (Keys C)) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
      (s : RealState C net.State) (w : LogState C), RefInv prims keys D s w →
      ∀ z ∈ support (((sharedRunWith K circuits settings (loggedWorld prims D) Prod.fst D net
          (fun i => passTree K circuits settings plainShares none i (s.operators i) tree) tree).run s).run w),
        RefInv prims keys D z.1.2 z.2

/-- The signing phase from a state with the invariant. With the outputs of the operators it wins with
no flag at most as often as with the answers of the dealer on the seeds of the game. -/
def RefSigning : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
      (s : RealState C A.net.State) (w : LogState C), RefInv prims keys D s w →
      Pr{let z ← ((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst true Mode.real D A
          (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)).run s).run w}[
          z.1.1 = true ∧ z.1.2.flag = false] ≤
        Pr{let z ← ((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A
          (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)).run s).run w}[
          z.1.1 = true ∧ z.1.2.flag = false]

/-! ## The runs keep the invariant -/

omit [Fintype E] [DecidableEq E] in
/-- A real run of `tree` is the recorded run of `passTree` with the opened sharing of a real run. -/
theorem sharedRun_real {M : Type → Type} [Monad M] [LawfulMonad M] {W : Type}
    (impl : QueryImpl (WorldSpec C) (StateT W M)) (view : W → StreamState C) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    sharedRun K circuits settings impl view Mode.real D net parameter seeds dealt emu tree =
      (get >>= fun s => sharedRunWith K circuits settings impl view D net
        (fun i => passTree K circuits settings plainShares none i (s.operators i) tree) tree) := by
  unfold sharedRun
  simp [Mode.real]

omit [Fintype E] [DecidableEq E] in
/-- The real runs of a tree keep the invariant. -/
theorem sharedRuns_keeps (keeps : RefRunKeeps prims K circuits settings)
    (batch : 0 < settings.batchSize) (compute : CircuitsCompute circuits prims.Th)
    (keys : C.Party → Option (Keys C)) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ (count : ℕ) (s : RealState C net.State) (w : LogState C), RefInv prims keys D s w →
      ∀ z ∈ support (((sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
          parameter seeds dealt emu tree count).run s).run w), RefInv prims keys D z.1.2 z.2
  | 0, s, w, h, z, hz => by
    simp only [sharedRuns, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h
  | count + 1, s, w, h, z, hz => by
    simp only [sharedRuns, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz with hmay
    · rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rw [sharedRun_real, StateT.run_bind, StateT.run_get, pure_bind] at hy
      exact sharedRuns_keeps keeps batch compute keys D net parameter seeds dealt emu tree count y.1.2 y.2
        (keeps batch compute keys D net tree s w h y hy) z hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h

/-! ## The glue -/

/-- An event of a bind is at most as likely as an event of another bind with the same first program,
when it holds on the support of the first program. -/
theorem probEvent_bind_le_of_support {α β γ : Type} (oa : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (P : β → Prop) (Q : γ → Prop) (h : ∀ a ∈ support oa, Pr{let z ← f a}[P z] ≤ Pr{let z ← g a}[Q z]) :
    Pr{let z ← oa >>= f}[P z] ≤ Pr{let z ← oa >>= g}[Q z] := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support oa
  · exact mul_le_mul' le_rfl (h a ha)
  · rw [prEvent_eq_zero_of_not_mem_support oa ha, zero_mul, zero_mul]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run in `loggedWorld` from a hash cache with no input of the MPC ends with no such input. -/
theorem loggedWorld_noMpc (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) (w : LogState C)
    (hw : NoMpc w.1.1) : ∀ z ∈ support ((simulateQ (loggedWorld prims D) oa).run w), NoMpc z.2.1.1 := by
  intro z hz
  have hl := withLog_run (streamWorld prims D) countedCells oa w.1 w.2
  rw [show withLog (streamWorld prims D) countedCells = loggedWorld prims D from rfl] at hl
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D) oa).run w.1) := by
    rw [← hl, support_map]
    exact ⟨z, hz, rfl⟩
  exact streamWorld_noMpc prims D oa w.1 hw _ hz'

/-- The start state of the rest has the invariant. -/
theorem refInv_startState {σ : Type} (D : C.Coalition) (state : σ) (keys : C.Party → Option (Keys C))
    (w : LogState C) (hw : NoMpc w.1.1) : RefInv prims keys D (startState D state keys) w := by
  refine ⟨fun i => rfl, hw, fun hflag => ⟨hflag, fun i _ h _ _ => ⟨fun t ht => ?_, fun b bt hb => ?_⟩⟩⟩
  · simp [startState] at ht
  · simp [startState] at hb

omit [Fintype E] [DecidableEq E] in
/-- `SharedRefDealer` from the two parts. -/
theorem sharedRefDealer_of_parts (keeps : RefRunKeeps prims K circuits settings)
    (signing : RefSigning prims K circuits settings runLimit) :
    SharedRefDealer prims K circuits settings runLimit := by
  intro batch compute D A
  unfold realProb
  refine ENNReal.toReal_mono ?_ ?_
  · exact prEvent_ne_top _
  unfold sharedReal sharedRestOf sharedRest
  simp only [StateT.run_bind]
  refine probEvent_bind_le_of_support _ _ _ _ _ fun p hp => ?_
  simp only [bind_assoc]
  refine probEvent_bind_le_of_support _ _ _ _ _ fun y hy => ?_
  have hinv := sharedRuns_keeps prims K circuits settings runLimit keeps batch compute p.1.2 D A.net _ _ _ _ .top
    runLimit _ p.2 (refInv_startState prims D p.1.1 p.1.2 p.2 (loggedWorld_noMpc prims D _ _ noMpc_empty p hp)) y hy
  have h := signing batch compute p.1.2 D A y.1.2 y.2 hinv
  simp only [Clean, StateT.run_pure, bind_pure_comp, prEvent_map]
  exact h

/-! ## One real run -/

/-- The top tree of a run of `tree` at an operator. The top tree runs from `emptyTop`, and a bottom
tree runs from the kept top tree of the operator. -/
def treeTop (operator : OperatorState C) : Tree → Option TopTree
  | .top => some emptyTop
  | .bottom _ => operator.top

/-- The outputs of one real recorded run. From a state whose kept outputs are the reference outputs,
an honest output of a run with no bad check in its records and no global event at its end is the
output of `referenceTree` on the seeds and the parameter of the game, with the top tree of its
operator, for each good `h` that agrees with the end cache. -/
def PassCleanOutput : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State)
      (w : LogState C), NoMpc w.1.1 → RefOutputs prims D s w.1.1 →
      ∀ r ∈ support ((simulateQ (loggedWorld prims D) (executePhaseR worldRoles D net noFunctionality
          ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
            (passTree K circuits settings plainShares none i (s.operators i) tree).run.run)).run w),
        ¬ PassBad K D (fun i => (r.1.2 i).record []) → ¬ GlobalEvent r.2.1 →
        ∀ i, i ∉ D.1 → ∀ o, (r.1.2 i).output = some o → ∀ h, Good prims h → Agrees h r.2.1.1 →
          ∃ top, treeTop (s.operators i) tree = some top ∧
            ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
              (prfValue (gameSeeds D fun i => (s.operators i).keys)) (gameParameter D fun i => (s.operators i).keys)
              top tree) = some o

/-! ## The outputs of one run from a wrong check -/

/-- A wrong output of one real recorded run has a bad check in the records of the run. -/
def PassWrongCheck : Prop :=
  0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State)
      (w : LogState C), NoMpc w.1.1 → RefOutputs prims D s w.1.1 →
      ∀ r ∈ support ((simulateQ (loggedWorld prims D) (executePhaseR worldRoles D net noFunctionality
          ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
            (passTree K circuits settings plainShares none i (s.operators i) tree).run.run)).run w),
        ¬ GlobalEvent r.2.1 →
        ∀ i, i ∉ D.1 → ∀ o, (r.1.2 i).output = some o → ∀ h, Good prims h → Agrees h r.2.1.1 →
          ¬ (∃ top, treeTop (s.operators i) tree = some top ∧
            ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
              (prfValue (gameSeeds D fun i => (s.operators i).keys)) (gameParameter D fun i => (s.operators i).keys)
              top tree) = some o) →
          PassBad K D fun i => (r.1.2 i).record []

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An outcome in `loggedWorld` with the log dropped is an outcome in `streamWorld`. -/
theorem loggedWorld_support_stream (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) (w : LogState C)
    (z : α × LogState C) (hz : z ∈ support ((simulateQ (loggedWorld prims D) oa).run w)) :
    (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D) oa).run w.1) := by
  have hl := withLog_run (streamWorld prims D) countedCells oa w.1 w.2
  rw [show withLog (streamWorld prims D) countedCells = loggedWorld prims D from rfl] at hl
  rw [← hl, support_map]
  exact ⟨z, hz, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- `PassCleanOutput` from `PassWrongCheck`. -/
theorem passCleanOutput_of (wrong : PassWrongCheck prims K circuits settings) : PassCleanOutput prims K circuits settings := by
  intro batch compute D net tree s w hmpc hout r hr hbad hglobal i hi o ho h hg ha
  by_contra hnot
  exact hbad (wrong batch compute D net tree s w hmpc hout r hr hglobal i hi o ho h hg ha hnot)

/-! ## The cache grows -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run in `loggedWorld` only adds cells to the hash cache. -/
theorem loggedWorld_cache_le (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) (w : LogState C) :
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) oa).run w), w.1.1 ≤ z.2.1.1 := by
  intro z hz
  have hw := withLog_run (streamWorld prims D) countedCells oa w.1 w.2
  rw [show withLog (streamWorld prims D) countedCells = loggedWorld prims D from rfl] at hw
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D) oa).run w.1) := by
    rw [← hw, support_map]
    exact ⟨z, hz, rfl⟩
  exact (streamWorld_le prims D oa w.1 _ hz').1

/-! ## The support of one recorded run -/

omit [Fintype E] [DecidableEq E] in
/-- An outcome of `sharedRunWith` in `loggedWorld` is an outcome of its phase with the kept outputs,
the run count and the flag of the run. -/
theorem sharedRunWith_support (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (program : C.Party → RecM C E TreeOutput) (tree : Tree) (s : RealState C net.State) (w : LogState C)
    (z : (PUnit × RealState C net.State) × LogState C)
    (hz : z ∈ support (((sharedRunWith K circuits settings (loggedWorld prims D) Prod.fst D net program tree).run s).run w)) :
    ∃ r ∈ support ((simulateQ (loggedWorld prims D) (executePhaseR worldRoles D net noFunctionality
        ([] : Record C E) (treeFuel circuits settings) s.adversary fun i => (program i).run.run)).run w),
      z.2 = r.2 ∧ z.1.2 = ⟨r.1.1, fun i => (s.operators i).keep (r.1.2 i).output tree,
        Function.update s.runs tree (s.runs tree + 1), s.closed,
        s.flag || decide (PassBad K D (fun i => (r.1.2 i).record []) ∨
          ReusedBefore D w.1.2 (fun i => (r.1.2 i).record []) ∨ GlobalEvent r.2.1)⟩ := by
  unfold sharedRunWith inWorld at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_map, StateT.run_set,
    bind_assoc, mem_support_bind_iff, support_map, Set.mem_image] at hz
  obtain ⟨x, ⟨x1, hx1, rfl⟩, r, hr, x2, ⟨x3, hx3, rfl⟩, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hx1 hx3
  subst hx1 hx3
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨r, hr, rfl, rfl⟩


/-! ## The proof of `RefRunKeeps` -/

omit [Fintype E] [DecidableEq E] in
/-- `RefRunKeeps` from the outputs of one run. -/
theorem refRunKeeps_of_clean (clean : PassCleanOutput prims K circuits settings) :
    RefRunKeeps prims K circuits settings := by
  intro batch compute keys D net tree s w hinv z hz
  obtain ⟨r, hr, hz2, hz1⟩ := sharedRunWith_support prims K circuits settings D net _ tree s w z hz
  have hkeys : ∀ i, (z.1.2.operators i).keys = (s.operators i).keys := fun i => by
    rw [hz1]
    exact Ready.keep_keys _ _ _
  refine ⟨fun i => (hkeys i).trans (hinv.1 i), hz2 ▸ loggedWorld_noMpc prims D _ w hinv.2.1 r hr, fun hflag => ?_⟩
  rw [hz1] at hflag
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or] at hflag
  obtain ⟨hs, hbad, -, hglobal⟩ := hflag
  obtain ⟨hsame, hout⟩ := hinv.2.2 hs
  have hle : w.1.1 ≤ z.2.1.1 := hz2 ▸ loggedWorld_cache_le prims D _ w r hr
  have hk : (fun i => (z.1.2.operators i).keys) = fun i => (s.operators i).keys := funext hkeys
  refine ⟨by rw [hk]; exact hsame, fun i hi h hg ha => ?_⟩
  have ha' : Agrees h w.1.1 := Agrees.mono hle ha
  have ha'' : Agrees h r.2.1.1 := hz2 ▸ ha
  obtain ⟨htop, hbottom⟩ := hout i hi h hg ha'
  have hnew := clean batch compute D net tree s w hinv.2.1 (hinv.2.2 hs) r hr hbad hglobal i hi
  rw [hk]
  rw [hz1]
  cases tree with
  | top =>
    refine ⟨fun t ht => ?_, fun b bt hb => ?_⟩
    · simp only [OperatorState.keep] at ht
      rcases hst : (s.operators i).top with _ | t'
      · simp only [hst, Option.orElse_eq_orElse, Option.orElse_none] at ht
        rcases hro : (r.1.2 i).output with _ | o
        · rw [hro] at ht
          simp [TreeOutput.topTree] at ht
        · obtain ⟨top, htop', hD⟩ := hnew o hro h hg ha''
          simp only [treeTop, Option.some.injEq] at htop'
          subst htop'
          rw [hD]
          rw [hro] at ht
          cases o with
          | top t'' => simp [TreeOutput.topTree] at ht; rw [ht]
          | bottom _ => simp [TreeOutput.topTree] at ht
      · simp only [hst, Option.orElse_eq_orElse, Option.orElse_some] at ht
        exact htop t (hst.trans ht)
    · simp only [OperatorState.keep] at hb
      obtain ⟨t, ht, hD⟩ := hbottom b bt hb
      exact ⟨t, by simp only [OperatorState.keep]; rw [ht]; rfl, hD⟩
  | bottom b₀ =>
    refine ⟨fun t ht => ?_, fun b bt hb => ?_⟩
    · simp only [OperatorState.keep] at ht
      exact htop t ht
    · simp only [OperatorState.keep] at hb ⊢
      by_cases hbb : b = b₀
      · subst hbb
        rw [Function.update_self] at hb
        rcases hsb : (s.operators i).bottom b with _ | bt'
        · simp only [hsb, Option.orElse_eq_orElse, Option.orElse_none] at hb
          rcases hro : (r.1.2 i).output with _ | o
          · rw [hro] at hb
            simp [bottomOf] at hb
          · obtain ⟨top, htop', hD⟩ := hnew o hro h hg ha''
            refine ⟨top, htop', ?_⟩
            rw [hD]
            rw [hro] at hb
            cases o with
            | top _ => simp [bottomOf] at hb
            | bottom bt'' => simp [bottomOf] at hb; rw [hb]
        · simp only [hsb, Option.orElse_eq_orElse, Option.orElse_some] at hb
          exact hbottom b bt (hsb.trans hb)
      · rw [Function.update_of_ne hbb] at hb
        exact hbottom b bt hb

omit [Fintype E] [DecidableEq E] in
/-- `SharedRefDealer` from the outputs of one run and the signing phase. -/
theorem sharedRefDealer_of_clean (runLimit : ℕ) (clean : PassCleanOutput prims K circuits settings)
    (signing : RefSigning prims K circuits settings runLimit) :
    SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_parts prims K circuits settings runLimit (refRunKeeps_of_clean prims K circuits settings clean)
    signing




/-! ## Facts on the free computations of the dealer -/

section Free

open GameCount (OnlySign)

variable (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run of a handler with a log whose calls add no cell keeps the log. -/
theorem withLog_keeps_log {ι : Type} {spec : OracleSpec ι} {W L : Type} (impl : QueryImpl spec (StateT W ProbComp))
    (cells : ι → List L) {α : Type} (oa : OracleComp spec α) (h : AllQueriesSatisfy oa fun t => cells t = [])
    (w : W) (log : List L) : ∀ z ∈ support ((simulateQ (withLog impl cells) oa).run (w, log)), z.2.2 = log := by
  induction oa using OracleComp.inductionOn generalizing w with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    intro z hz
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self, withLog,
      StateT.run_bind, StateT.run_mk, bind_map_left, mem_support_bind_iff] at hz
    obtain ⟨y, -, hz⟩ := hz
    rw [h.1, List.append_nil] at hz
    exact ih y.1 (h.2 _) y.2 z hz

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A free computation on `.hash` and `.prf` in `loggedWorld` is its run on the hash cache, with the
hidden cache and the log kept. -/
theorem loggedFree_support {γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) (w : LogState C)
    (z : γ × LogState C) (hz : z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))).run w)) :
    ∃ y ∈ support (roRun prims oa w.1.1), z = (y.1, ((y.2, w.1.2), w.2)) := by
  have hlog := withLog_keeps_log (streamWorld prims D) countedCells (free (liftComp oa (LocalSpec C)))
    ((GameCount.allQueries_free_liftComp h).mono fun t ht => by
      rcases t with ((_ | _) | _) | _ <;> first | rfl | exact absurd ht (by simp [GameCount.MonitorCall]))
    w.1 w.2 z hz
  have hs := loggedWorld_support_stream prims D _ w z hz
  change (z.1, z.2.1) ∈ support (Ready.freeRun prims D oa w.1) at hs
  rw [freeRun_onlySign prims D oa h, support_map] at hs
  obtain ⟨y, hy, hyz⟩ := hs
  refine ⟨y, hy, ?_⟩
  obtain ⟨z₁, ⟨z₂, z₃⟩⟩ := z
  simp only [Prod.mk.injEq] at hyz hlog
  obtain ⟨rfl, rfl⟩ := hyz
  rw [← hlog]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A free computation whose value is fixed by the hash cache gives that value. -/
theorem loggedFree_determined {γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) (w : LogState C)
    (hw : NoMpc w.1.1) (a : γ) (hdet : ∀ hf, Good prims hf → Agrees hf w.1.1 → ThresholdLeanXmssSecurity.D prims hf oa = a)
    (z : γ × LogState C) (hz : z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))).run w)) :
    z.1 = a := by
  obtain ⟨y, hy, rfl⟩ := loggedFree_support prims D oa h w z hz
  obtain ⟨hle, hmpc, hD⟩ := roRun_support prims oa w.1.1 y hy
  obtain ⟨hf, hg, ha⟩ := exists_good_agrees prims (hmpc hw)
  exact (hD hf hg ha).trans (hdet hf hg (Agrees.mono hle ha))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A free computation run again from a larger world gives its first value and keeps the world. -/
theorem loggedFree_replay {γ : Type} (oa : OracleComp (RoSpec C) γ) (h : OnlySign oa) (w : LogState C)
    (z : γ × LogState C) (hz : z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))).run w))
    (w' : LogState C) (hle : z.2.1 ≤ w'.1) :
    ∀ z' ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))).run w'), z' = (z.1, w') := by
  intro z' hz'
  have hs := loggedWorld_support_stream prims D _ w z hz
  have hs' := loggedWorld_support_stream prims D _ w' z' hz'
  have hlog := withLog_keeps_log (streamWorld prims D) countedCells (free (liftComp oa (LocalSpec C)))
    ((GameCount.allQueries_free_liftComp h).mono fun t ht => by
      rcases t with ((_ | _) | _) | _ <;> first | rfl | exact absurd ht (by simp [GameCount.MonitorCall]))
    w'.1 w'.2 z' hz'
  have e := Ready.freeRun_replay prims D oa w.1 _ hs w'.1 hle _ hs'
  obtain ⟨z₁, ⟨z₂, z₃⟩⟩ := z'
  simp only [Prod.mk.injEq] at e hlog ⊢
  exact ⟨e.1, Prod.ext e.2 hlog⟩

end Free

/-! ## A one-sided coupling for the coupling of the signing phases -/

section Le

variable {A B A' B' A'' B'' : Type}

/-- From inputs related by `P`, the left program `X` and the right program `Y` end in outputs related
by `Q`, for the order of the probabilities of two events after two continuations. Each pair of
continuations whose probabilities are ordered on the outputs with `Q` has ordered probabilities after
`X` and `Y`. -/
def LeArrow (P : A → B → Prop) (X : A → ProbComp A') (Y : B → ProbComp B') (Q : A' → B' → Prop) : Prop :=
  ∀ a b, P a b → ∀ (γ δ : Type) (kT : A' → ProbComp γ) (kF : B' → ProbComp δ) (ET : γ → Prop) (EF : δ → Prop),
    (∀ a' b', Q a' b' → Pr{let z ← kT a'}[ET z] ≤ Pr{let z ← kF b'}[EF z]) →
    Pr{let z ← X a >>= kT}[ET z] ≤ Pr{let z ← Y b >>= kF}[EF z]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem le_prEvent_bind_of_support {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (q : β → Prop) (ε : ℝ≥0∞)
    (h : ∀ a ∈ support mx, ε ≤ Pr{let y ← f a}[q y]) : ε ≤ Pr{let y ← mx >>= f}[q y] := by
  rw [bind_eq_attach_bind mx f]
  exact le_prEvent_bind_of_forall_le _ (OracleComp.prEvent_true_eq_one _) _ q fun a => h a.1 a.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem LeArrow.comp {P : A → B → Prop} {X : A → ProbComp A'} {Y : B → ProbComp B'} {Q : A' → B' → Prop}
    {X' : A' → ProbComp A''} {Y' : B' → ProbComp B''} {R : A'' → B'' → Prop}
    (h₁ : LeArrow P X Y Q) (h₂ : LeArrow Q X' Y' R) :
    LeArrow P (fun a => X a >>= X') (fun b => Y b >>= Y') R := by
  intro a b hab γ δ kT kF ET EF hk
  simp only [bind_assoc]
  exact h₁ a b hab γ δ (fun a' => X' a' >>= kT) (fun b' => Y' b' >>= kF) ET EF fun a' b' hq =>
    h₂ a' b' hq γ δ kT kF ET EF hk

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem LeArrow.mono {P P' : A → B → Prop} {X : A → ProbComp A'} {Y : B → ProbComp B'} {Q Q' : A' → B' → Prop}
    (h : LeArrow P X Y Q) (hP : ∀ a b, P' a b → P a b) (hQ : ∀ a' b', Q a' b' → Q' a' b') : LeArrow P' X Y Q' :=
  fun a b hab γ δ kT kF ET EF hk => h a b (hP a b hab) γ δ kT kF ET EF fun a' b' hq => hk a' b' (hQ a' b' hq)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The escape. Outputs of the left program keep a property `L` of the inputs, and `L` relates to
each right output. -/
theorem leArrow_escape {L : A → Prop} {L' : A' → Prop} {X : A → ProbComp A'} {Y : B → ProbComp B'}
    (hX : ∀ a, L a → ∀ a' ∈ support (X a), L' a') :
    LeArrow (fun a _ => L a) X Y (fun a' _ => L' a') := by
  intro a b ha γ δ kT kF ET EF hk
  refine le_trans (prEvent_bind_le_of_forall_le_of_support _ _ _ (ε := ⨅ b' ∈ support (Y b),
    Pr{let z ← kF b'}[EF z]) fun a' ha' => le_iInf₂ fun b' _ => hk a' b' (hX a ha a' ha')) ?_
  exact le_prEvent_bind_of_support _ _ _ _ fun b' hb' => iInf₂_le b' hb'

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem LeArrow.or {P₁ P₂ : A → B → Prop} {X : A → ProbComp A'} {Y : B → ProbComp B'} {Q : A' → B' → Prop}
    (h₁ : LeArrow P₁ X Y Q) (h₂ : LeArrow P₂ X Y Q) : LeArrow (fun a b => P₁ a b ∨ P₂ a b) X Y Q :=
  fun a b hab => hab.elim (h₁ a b) (h₂ a b)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The two programs are maps of one program, and its outcomes give related outputs. -/
theorem leArrow_common {P : A → B → Prop} {X : A → ProbComp A'} {Y : B → ProbComp B'} {Q : A' → B' → Prop}
    (h : ∀ a b, P a b → ∃ (Z : Type) (z : ProbComp Z) (f : Z → A') (g : Z → B'), X a = f <$> z ∧ Y b = g <$> z ∧
      ∀ c ∈ support z, Q (f c) (g c)) : LeArrow P X Y Q := by
  intro a b hab γ δ kT kF ET EF hk
  obtain ⟨Z, z, f, g, hX, hY, hQ⟩ := h a b hab
  rw [hX, hY, bind_map_left, bind_map_left]
  exact probEvent_bind_le_of_support _ _ _ _ _ fun c hc => hk (f c) (g c) (hQ c hc)

/-! ### The signing layer as one state -/

variable {σ : Type}

/-- A program of the signing layer from its three states. -/
def runSig {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α)
    (u : TsigState C × RealState C σ × LogState C) : ProbComp (α × (TsigState C × RealState C σ × LogState C)) :=
  (fun o => (o.1.1.1, (o.1.1.2, o.1.2, o.2))) <$> ((x.run u.1).run u.2.1).run u.2.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem runSig_pure {α : Type} (a : α) (u : TsigState C × RealState C σ × LogState C) :
    runSig (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) u = pure (a, u) := by
  simp [runSig]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem runSig_bind {α β : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α)
    (f : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β) (u : TsigState C × RealState C σ × LogState C) :
    runSig (x >>= f) u = runSig x u >>= fun o => runSig (f o.1) o.2 := by
  simp [runSig, StateT.run_bind, map_bind, bind_map_left]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A property of the states that each call of the left oracles keeps is kept by each program. -/
theorem keeps_simulateQ {ι : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (LogState C) σ)))
    (L : TsigState C × RealState C σ × LogState C → Prop)
    (hH : ∀ t u, L u → ∀ o ∈ support (runSig (H t) u), L o.2) {α : Type} (oa : OracleComp spec α) :
    ∀ u, L u → ∀ o ∈ support (runSig (simulateQ H oa) u), L o.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro u hu o ho
    rw [simulateQ_pure, runSig_pure, support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact hu
  | query_bind t k ih =>
    intro u hu o ho
    rw [simulateQ_query_bind, runSig_bind, mem_support_bind_iff] at ho
    obtain ⟨o', ho', ho⟩ := ho
    exact ih o'.1 o'.2 (hH t u hu o' ho') o ho

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The one-sided coupling of two oracles up to an escape of the left side. Each call keeps the
relation `G` with equal answers or reaches the escape `L`, and the left oracles keep `L`. -/
theorem leArrow_simulateQ {ι : Type} {spec : OracleSpec ι}
    (HT HF : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (LogState C) σ)))
    (L : TsigState C × RealState C σ × LogState C → Prop)
    (G : TsigState C × RealState C σ × LogState C → TsigState C × RealState C σ × LogState C → Prop)
    (hstep : ∀ t, LeArrow G (runSig (HT t)) (runSig (HF t)) fun oT oF => L oT.2 ∨ (oT.1 = oF.1 ∧ G oT.2 oF.2))
    (hL : ∀ t u, L u → ∀ o ∈ support (runSig (HT t) u), L o.2) {α : Type} (oa : OracleComp spec α) :
    LeArrow (fun u v => L u ∨ G u v) (runSig (simulateQ HT oa)) (runSig (simulateQ HF oa))
      fun oT oF => L oT.2 ∨ (oT.1 = oF.1 ∧ G oT.2 oF.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    refine leArrow_common fun u v huv => ⟨Unit, pure (), fun _ => (a, u), fun _ => (a, v), ?_, ?_, ?_⟩
    · simp [runSig_pure]
    · simp [runSig_pure]
    · intro _ _
      exact huv.imp id fun h => ⟨rfl, h⟩
  | query_bind t k ih =>
    have e : ∀ (H : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (LogState C) σ))),
        runSig (simulateQ H (liftM (OracleSpec.query t) >>= k)) =
          fun u => runSig (H t) u >>= fun o => runSig (simulateQ H (k o.1)) o.2 := fun H => by
      funext u
      rw [simulateQ_query_bind, runSig_bind]
      rfl
    rw [e HT, e HF]
    refine LeArrow.comp (Q := fun oT oF => L oT.2 ∨ (oT.1 = oF.1 ∧ G oT.2 oF.2)) ?_ ?_
    · refine LeArrow.or ?_ (hstep t)
      exact (leArrow_escape (L := L) (L' := fun o : spec.Range t × (TsigState C × RealState C σ × LogState C) => L o.2)
        (Y := runSig (HF t)) (hL t)).mono (fun _ _ h => h) fun _ _ h => Or.inl h
    · refine LeArrow.or ?_ ?_
      · exact (leArrow_escape (L := fun o : spec.Range t × (TsigState C × RealState C σ × LogState C) => L o.2)
          (L' := fun o : α × (TsigState C × RealState C σ × LogState C) => L o.2)
          (Y := fun o : spec.Range t × (TsigState C × RealState C σ × LogState C) => runSig (simulateQ HF (k o.1)) o.2)
          fun o ho o' ho' => keeps_simulateQ HT L hL (k o.1) o.2 ho o' ho').mono (fun _ _ h => h)
            fun _ _ h => Or.inl h
      · rintro ⟨a₁, u₁⟩ ⟨a₂, u₂⟩ ⟨hans, hG⟩
        dsimp only at hans hG ⊢
        subst hans
        exact ih a₁ u₁ u₂ (Or.inr hG)

end Le

/-! ## The flag only grows -/

section FlagUp

variable (D : C.Coalition) {σ : Type}

/-- From each state with the flag, each outcome of `x` has the flag. -/
def FlagUp {α : Type} (x : SharedM C ProbComp (LogState C) σ α) : Prop :=
  ∀ s w, s.flag = true → ∀ z ∈ support ((x.run s).run w), z.1.2.flag = true

/-- `FlagUp` from each signing state. -/
def FlagUpT {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) : Prop :=
  ∀ st, FlagUp (x.run st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUp_pure {α : Type} (a : α) : FlagUp (pure a : SharedM C ProbComp (LogState C) σ α) := by
  intro s w hs z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem FlagUp.bind {α β : Type} {x : SharedM C ProbComp (LogState C) σ α} {f : α → SharedM C ProbComp (LogState C) σ β}
    (hx : FlagUp x) (hf : ∀ a, FlagUp (f a)) : FlagUp (x >>= f) := by
  intro s w hs z hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  exact hf y.1.1 y.1.2 y.2 (hx s w hs y hy) z hz

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUp_get_bind {α : Type} {f : RealState C σ → SharedM C ProbComp (LogState C) σ α}
    (hf : ∀ s, FlagUp (f s)) : FlagUp (get >>= f) := by
  intro s w hs z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf s s w hs z hz

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUp_lift {α : Type} (X : StateT (LogState C) ProbComp α) :
    FlagUp (StateT.lift X : SharedM C ProbComp (LogState C) σ α) := by
  intro s w hs z hz
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, -, rfl⟩ := hz
  exact hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUp_modify (f : RealState C σ → RealState C σ) (hf : ∀ s, (f s).flag = s.flag) :
    FlagUp (modify f : SharedM C ProbComp (LogState C) σ PUnit) := by
  intro s w hs z hz
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact (hf s).trans hs

omit [Fintype E] [DecidableEq E] in
theorem flagUp_sharedRunWith (net : Adversary C E Unit PEmpty PEmpty) (program : C.Party → RecM C E TreeOutput)
    (tree : Tree) : FlagUp (sharedRunWith K circuits settings (loggedWorld prims D) Prod.fst D net program tree) := by
  intro s w hs z hz
  obtain ⟨r, -, -, hz1⟩ := sharedRunWith_support prims K circuits settings D net program tree s w z hz
  rw [hz1]
  simp [hs]

omit [Fintype E] [DecidableEq E] in
theorem flagUp_sharedRuns_real (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, FlagUp (sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
      parameter seeds dealt emu tree count)
  | 0 => flagUp_pure ()
  | count + 1 => by
    unfold sharedRuns
    refine flagUp_get_bind fun s => ?_
    split_ifs
    · rw [sharedRun_real]
      exact FlagUp.bind (flagUp_get_bind fun _ => flagUp_sharedRunWith prims K circuits settings D net _ tree)
        fun _ => flagUp_sharedRuns_real net parameter seeds dealt emu tree count
    · exact flagUp_pure ()

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUpT_pure {α : Type} (a : α) :
    FlagUpT (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) := fun st => by
  simpa using flagUp_pure (σ := σ) (a, st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem FlagUpT.bind {α β : Type} {x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    {f : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β}
    (hx : FlagUpT x) (hf : ∀ a, FlagUpT (f a)) : FlagUpT (x >>= f) := fun st => by
  rw [StateT.run_bind]
  exact FlagUp.bind (hx st) fun p => hf p.1 p.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUpT_lift {α : Type} {x : SharedM C ProbComp (LogState C) σ α} (hx : FlagUp x) :
    FlagUpT (StateT.lift x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) := fun st => by
  simp only [StateT.run_lift]
  exact FlagUp.bind hx fun _ => flagUp_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUpT_get_bind {α : Type} {f : TsigState C → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    (hf : ∀ st, FlagUpT (f st)) : FlagUpT (get >>= f) := fun st => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf st st

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUpT_simulateQ {ι : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (LogState C) σ)))
    (hH : ∀ t, FlagUpT (H t)) {α : Type} (oa : OracleComp spec α) : FlagUpT (simulateQ H oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using flagUpT_pure (σ := σ) a
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    exact FlagUpT.bind (hH t) ih

end FlagUp

/-! ## The signing phase with the dealer calls as ghosts -/

section Ghost

variable {M : Type → Type} [Monad M] {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W M))
  (view : W → StreamState C)

/-- The bottom tree `b` of the dealer on the top tree `top`, on `H`, as `dealtWith` builds it. -/
def refBottom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : OracleComp (RoSpec C) (Option BottomTree) :=
  bottomOf <$> referenceTree tweakable (prfValue seeds) parameter top (.bottom b)

/-- The calls of the dealer for a request of bottom tree `b` with no cached tree, as `tsigOracles`
of the dealer makes them. The result is dropped. -/
def ghostTreeRo (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : OracleComp (RoSpec C) Unit := do
  let some _ ← refBottom parameter seeds top b | pure ()
  let _ ← prfValue seeds (.randomizer topLayer (topKey b))
  pure ()

/-- The signing oracles of the real game with the calls of the dealer before a request of a bottom
tree and before the build of a bottom tree in `round2`, as ghosts. -/
def ghostOracles (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (top : TopTree) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (SharedM C M W net.State)) := fun q =>
  match q with
  | .tree b => do
      StateT.lift (sharedLift impl (ghostTreeRo parameter seeds top b))
      sharedOwnOracles K circuits settings runLimit impl view Mode.real D net parameter seeds dealt
        (fun _ => none) (.tree b)
  | .round2 i J e message parts => do
      let st ← get
      let s ← StateT.lift get
      if (s.operators i).keys.isSome ∧ (s.operators i).top.isSome ∧ ((s.operators i).bottom (treeOf e)).isSome ∧
          ¬ (i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message) then
        StateT.lift (sharedLift impl ((fun _ => ()) <$> refBottom parameter seeds top (treeOf e)))
      sharedOwnOracles K circuits settings runLimit impl view Mode.real D net parameter seeds dealt
        (fun _ => none) (.round2 i J e message parts)
  | q => sharedOwnOracles K circuits settings runLimit impl view Mode.real D net parameter seeds dealt
      (fun _ => none) q

/-- The forger of the signing phase, as `sharedSigning` and `ghostSigning` define it. -/
def sigForger {M : Type → Type} [Monad M] {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W M)) (σ : Type) :
    QueryImpl (LocalSpec C) (StateT (TsigState C) (SharedM C M W σ)) :=
  fun t => StateT.lift (inWorld impl (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))

/-- The cell of the state of the adversary, as `sharedSigning` and `ghostSigning` define it. -/
def sigCell {M : Type → Type} [Monad M] {W : Type} (σ : Type) :
    QueryImpl (StateSpec σ) (StateT (TsigState C) (SharedM C M W σ)) := fun q =>
  match q with
  | .read => StateT.lift ((·.adversary) <$> (get : SharedM C M W σ _))
  | .write state => StateT.lift (modify fun s : RealState C σ => { s with adversary := state })

/-- The start of the signing state. -/
def startSig (D : C.Coalition) : TsigState C := ⟨D.1, fun _ => none, [], fun _ => none⟩

/-- The win test of the real game with the ghost build of the bottom tree of the dealer before the
read of the held bottom tree. -/
def ghostWinTest {σ : Type} (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (keys : Keys C) (p : Forgery × TsigState C) : SharedM C M W σ Bool := do
  let s ← get
  forgeryWins (sharedLift impl)
    { dealtWith (m := SharedM C M W σ) (sharedLift impl) keys.parameter (fun i => ((s.operators i).keys).getD noKeys)
        top (fun x => sharedLift impl (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) with
      bottom := fun b => do
        sharedLift impl ((fun _ => ()) <$> refBottom parameter seeds top b)
        pure (heldBottom D s.operators b) } p.2 p.1

/-- The signing phase of the real game with the calls of the dealer as ghosts. It computes the top
tree of the dealer first, and the win test builds the bottom tree of the dealer before it reads the
held bottom tree. -/
def ghostSigning (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) : SharedM C M W A.net.State Bool := do
  let s ← get
  match topHolder D s.operators with
  | none => pure false
  | some (keys, top) => do
    sharedLift impl ((fun _ => ()) <$> referenceTree tweakable (prfValue seeds) parameter emptyTop .top)
    let p ← (simulateQ ((sigForger impl A.net.State + (ghostOracles K circuits settings runLimit impl view D A.net
      parameter seeds dealt top + sigCell (C := C) (M := M) (W := W) A.net.State) :
        QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) (StateT (TsigState C) (SharedM C M W A.net.State))))
      (A.forge ⟨top.root, keys.parameter⟩ top)).run (startSig D)
    ghostWinTest impl D parameter seeds top keys p

end Ghost


/-- The local computations of the honest operators as a map of monads. -/
def roHom (D : C.Coalition) (σ : Type) : OracleComp (RoSpec C) →ᵐ SharedM C ProbComp (LogState C) σ where
  toFun _ oa := sharedLift (loggedWorld prims D) oa
  toFun_pure' a := by ext; simp [sharedLift, inWorld]
  toFun_bind' _ _ := by ext; simp [sharedLift, inWorld, free]

/-- The key generation of the win test of the real game on `H`, with the held bottom trees `held`. -/
def heldDealt (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree) (seeds : C.Term → HashOutput)
    (held : Fin (2 ^ layerHeight) → Option BottomTree) : Dealt C (OracleComp (RoSpec C)) :=
  { dealtWith (m := OracleComp (RoSpec C)) (fun oa => oa) parameter keys top (prfValue seeds) with
    bottom := fun b => pure (held b) }

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hmap_heldDealt (D : C.Coalition) (σ : Type) (parameter : PublicParameter) (keys : C.Party → Keys C)
    (top : TopTree) (seeds : C.Term → HashOutput) (held : Fin (2 ^ layerHeight) → Option BottomTree) :
    SeedHitProof.Dealt.hmap (roHom prims D σ) (heldDealt parameter keys top seeds held) =
      { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
          (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
        bottom := fun b => pure (held b) } := by
  unfold SeedHitProof.Dealt.hmap heldDealt
  congr 1

/-! ## Facts for the proof of `GhostCouple` -/

section CoupleFacts

variable (D : C.Coalition) {σ : Type}

omit [Fintype E] [DecidableEq E] in
/-- The invariant stays when the hash cache grows with no input of the MPC. -/
theorem refInv_mono {keys : C.Party → Option (Keys C)} {s : RealState C σ} {w w' : LogState C}
    (h : RefInv prims keys D s w) (hle : w.1.1 ≤ w'.1.1) (hmpc : NoMpc w'.1.1) : RefInv prims keys D s w' :=
  ⟨h.1, hmpc, fun hf => ⟨(h.2.2 hf).1, fun i hi hh hg ha => (h.2.2 hf).2 i hi hh hg (Agrees.mono hle ha)⟩⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUp_sharedLift {α : Type} (oa : OracleComp (RoSpec C) α) :
    FlagUp (sharedLift (σ := σ) (loggedWorld prims D) oa) :=
  flagUp_lift _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUpT_operatorAnswer (seeds : C.Term → HashOutput) (operator : OperatorState C) (e : KeyIndex)
    (q : TsigQuery C) :
    FlagUpT (operatorAnswer (sharedLift (σ := σ) (loggedWorld prims D))
      (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) operator e q) := fun st => by
  have h := hom_operatorAnswer (roHom prims D σ) (fun oa => oa) (fun x => prfValue seeds x) operator e q st
  have h' : (operatorAnswer (sharedLift (σ := σ) (loggedWorld prims D))
      (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) operator e q).run st =
      roHom prims D σ ((operatorAnswer (fun oa => oa) (fun x => prfValue seeds x) operator e q).run st) := h.symm
  rw [h']
  exact flagUp_lift _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagUp_mapGet {β : Type} (f : RealState C σ → β) :
    FlagUp (f <$> (get : SharedM C ProbComp (LogState C) σ (RealState C σ))) := by
  intro s w hs z hz
  simp only [StateT.run_map, StateT.run_get, map_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact hs

omit [Fintype E] [DecidableEq E] in
theorem flagUpT_ownOracles (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (q : TsigQuery C) :
    FlagUpT (sharedOwnOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
      parameter seeds dealt emu q) := by
  unfold sharedOwnOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact flagUpT_pure _
  · refine flagUpT_lift (FlagUp.bind (flagUp_sharedRuns_real prims K circuits settings runLimit D net
      parameter seeds dealt emu _ 1) fun _ => flagUp_get_bind fun s => ?_)
    split
    · exact FlagUp.bind (flagUp_sharedLift prims D _) fun _ => flagUp_pure _
    · exact flagUp_pure _
  all_goals
    exact FlagUpT.bind (flagUpT_lift (flagUp_modify _ fun _ => rfl)) fun _ =>
      FlagUpT.bind (flagUpT_lift (by simpa using flagUp_mapGet (σ := net.State) id)) fun s =>
        flagUpT_operatorAnswer prims D _ _ _ _


omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem onlySign_refBottom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : GameCount.OnlySign (refBottom parameter seeds top b) :=
  GameCount.onlySign_map _ (GameCount.onlySign_referenceTree seeds parameter top _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem onlySign_ghostTreeRo (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : GameCount.OnlySign (ghostTreeRo parameter seeds top b) := by
  unfold ghostTreeRo
  refine GameCount.onlySign_bind (onlySign_refBottom parameter seeds top b) fun o => ?_
  cases o with
  | none => exact GameCount.onlySign_pure _
  | some _ => exact GameCount.onlySign_bind (GameCount.onlySign_prfValue _ _) fun _ => GameCount.onlySign_pure _

end CoupleFacts

/-! ## The handler relation of `GhostCouple` -/

/-- The relation of the two sides of `GhostCouple` between two calls. The game states and the worlds
are equal, the signing states are equal besides the cached trees, the left state has the invariant
and no flag, `top` is a held top tree, each cached tree of the dealer is the result of `refBottom`
that a run from the present world gives again with no change of the world, the corrupt operators
are the coalition, and each release is from an honest operator that holds the bottom tree of its
key. -/
def GhostRel (keys : C.Party → Option (Keys C)) (D : C.Coalition) {σ : Type} (top : TopTree)
    (uT uF : TsigState C × RealState C σ × LogState C) : Prop :=
  uT.2 = uF.2 ∧ uT.1.corrupt = uF.1.corrupt ∧ uT.1.bound = uF.1.bound ∧ uT.1.released = uF.1.released ∧
    RefInv prims keys D uT.2.1 uT.2.2 ∧ uT.2.1.flag = false ∧
    (∃ i, i ∉ D.1 ∧ (uT.2.1.operators i).top = some top) ∧
    (∀ b r, uF.1.trees b = some r → ∀ z ∈ support ((simulateQ (loggedWorld prims D)
      (free (liftComp (refBottom (gameParameter D keys) (gameSeeds D keys) top b) (LocalSpec C)))).run uT.2.2),
      z = (r, uT.2.2)) ∧
    uT.1.corrupt = D.1 ∧
    ∀ r ∈ uT.1.released, r.2.2 ∉ D.1 ∧ ((uT.2.1.operators r.2.2).bottom (treeOf r.1)).isSome

/-- The step of `GhostCouple` for one call of the signing phase. From related states, the call with
ghosts and the call with the answers of the dealer on the top tree `top` give equal answers and
related states, or the left side has the flag. -/
def GhostStep : Prop :=
  RefRunKeeps prims K circuits settings → 0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E) (top : TopTree)
      (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain),
      LeArrow (GhostRel prims keys D top)
        (runSig (((sigForger (loggedWorld prims D) A.net.State + (ghostOracles K circuits settings runLimit
          (loggedWorld prims D) Prod.fst D A.net (gameParameter D keys) (gameSeeds D keys)
          (fun i => (keys i).getD noKeys) top + sigCell (C := C) (M := ProbComp) (W := LogState C) A.net.State) : QueryImpl (LocalSpec C + (TsigSpec C +
            StateSpec A.net.State)) (StateT (TsigState C) (SharedM C ProbComp (LogState C) A.net.State)))) t))
        (runSig (((sigForger (loggedWorld prims D) A.net.State + (sharedDealerOracles K circuits settings runLimit
          (loggedWorld prims D) Prod.fst Mode.real D A.net (gameParameter D keys) (gameSeeds D keys)
          (fun i => (keys i).getD noKeys) (fun _ => none)
          (dealtWith (sharedLift (loggedWorld prims D)) (gameParameter D keys) (fun i => (keys i).getD noKeys) top
            fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D keys) x)) + sigCell (C := C) (M := ProbComp) (W := LogState C) A.net.State) :
              QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State))
                (StateT (TsigState C) (SharedM C ProbComp (LogState C) A.net.State)))) t))
        fun oT oF => oT.2.2.1.flag = true ∨ (oT.1 = oF.1 ∧ GhostRel prims keys D top oT.2 oF.2)

omit [Fintype E] [DecidableEq E] in
/-- The oracles of the left side keep the flag. -/
theorem flagUpT_ghostHandlers (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : C.Party → Option (Keys C)) (top : TopTree)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    FlagUpT (((sigForger (loggedWorld prims D) A.net.State + (ghostOracles K circuits settings runLimit
      (loggedWorld prims D) Prod.fst D A.net (gameParameter D keys) (gameSeeds D keys)
      (fun i => (keys i).getD noKeys) top + sigCell (C := C) (M := ProbComp) (W := LogState C) A.net.State) :
        QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State))
          (StateT (TsigState C) (SharedM C ProbComp (LogState C) A.net.State)))) t) := by
  have own := flagUpT_ownOracles prims K circuits settings runLimit D A.net (gameParameter D keys)
    (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)
  rcases t with t | q | q
  · exact flagUpT_lift (flagUp_lift _)
  · change FlagUpT (ghostOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst D A.net
      (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) top q)
    unfold ghostOracles
    rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · exact own _
    · exact FlagUpT.bind (flagUpT_lift (flagUp_sharedLift prims D _)) fun _ => own (.tree b)
    · exact own _
    · have hget : FlagUp (get : SharedM C ProbComp (LogState C) A.net.State (RealState C A.net.State)) := by
        simpa using flagUp_mapGet (σ := A.net.State) id
      refine flagUpT_get_bind fun st => FlagUpT.bind (flagUpT_lift hget) fun s => ?_
      dsimp only
      split_ifs
      · exact FlagUpT.bind (flagUpT_lift (flagUp_sharedLift prims D _)) fun _ => own (.round2 i J e message parts)
      · exact own (.round2 i J e message parts)
  · rcases q with _ | state
    · exact flagUpT_lift (flagUp_mapGet _)
    · exact flagUpT_lift (flagUp_modify _ fun _ => rfl)

/-- The win test of `GhostCouple`. From related states and one forgery, the win test with the ghost
build of the bottom tree wins with no flag at most as often as the win test of the dealer. -/
def GhostWin : Prop :=
  ∀ (keys : C.Party → Option (Keys C)) (D : C.Coalition) (σ : Type) (top : TopTree) (keysT : Keys C)
    (uT uF : TsigState C × RealState C σ × LogState C) (forgery : Forgery),
    GhostRel prims keys D top uT uF → keysT.parameter = gameParameter D keys →
    Pr{let z ← ((do
        let s ← get
        forgeryWins (sharedLift (loggedWorld prims D))
          { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) keysT.parameter
              (fun i => ((s.operators i).keys).getD noKeys) top
              (fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) with
            bottom := fun b => do
              sharedLift (loggedWorld prims D)
                ((fun _ => ()) <$> refBottom (gameParameter D keys) (gameSeeds D keys) top b)
              pure (heldBottom D s.operators b) } uT.1 forgery : SharedM C ProbComp (LogState C) σ Bool).run
          uT.2.1).run uT.2.2}[z.1.1 = true ∧ z.1.2.flag = false] ≤
      Pr{let z ← ((forgeryWins (sharedLift (loggedWorld prims D))
          (dealtWith (sharedLift (loggedWorld prims D)) (gameParameter D keys) (fun i => (keys i).getD noKeys) top
            fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D keys) x)) uF.1 forgery :
          SharedM C ProbComp (LogState C) σ Bool).run uF.2.1).run uF.2.2}[z.1.1 = true ∧ z.1.2.flag = false]

/-- The ghosts change no law. From each state, the signing phase of the real game and the same phase
with the calls of the dealer as ghosts give "win and no flag" with one probability. -/
def GhostErase : Prop :=
  ∀ (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (s : RealState C A.net.State) (w : LogState C),
    Pr{let z ← ((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst true Mode.real D A
        (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)).run s).run w}[
        z.1.1 = true ∧ z.1.2.flag = false] =
      Pr{let z ← ((ghostSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D A
        (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys)).run s).run w}[
        z.1.1 = true ∧ z.1.2.flag = false]

/-- The coupling of the signing phase with ghosts and the signing phase with the answers of the
dealer. Both make the same calls of the world. From a state with the invariant, with no flag each
answer of the dealer is the answer of the operators. A run of a bottom tree in a tree request keeps
the invariant by `RefRunKeeps`. -/
def GhostCouple : Prop :=
  RefRunKeeps prims K circuits settings → 0 < settings.batchSize → CircuitsCompute circuits prims.Th →
    ∀ (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
      (s : RealState C A.net.State) (w : LogState C), RefInv prims keys D s w →
      Pr{let z ← ((ghostSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D A
          (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys)).run s).run w}[
          z.1.1 = true ∧ z.1.2.flag = false] ≤
        Pr{let z ← ((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A
          (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)).run s).run w}[
          z.1.1 = true ∧ z.1.2.flag = false]


/-! ## The two signing phases with a held top tree -/

section Unfold

/-- The oracles of the left side of `GhostCouple`. -/
abbrev ghostHandlers (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E) (top : TopTree) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State))
      (StateT (TsigState C) (SharedM C ProbComp (LogState C) A.net.State)) :=
  sigForger (loggedWorld prims D) A.net.State + (ghostOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst
    D A.net (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) top +
    sigCell (C := C) (M := ProbComp) (W := LogState C) A.net.State)

/-- The dealer of the right side of `GhostCouple` on the top tree `top`. -/
abbrev coupleDealer (keys : C.Party → Option (Keys C)) (D : C.Coalition) (σ : Type) (top : TopTree) :
    Dealt C (SharedM C ProbComp (LogState C) σ) :=
  dealtWith (sharedLift (loggedWorld prims D)) (gameParameter D keys) (fun i => (keys i).getD noKeys) top
    fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D keys) x)

/-- The oracles of the right side of `GhostCouple`. -/
abbrev dealerHandlers (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (dealer : Dealt C (SharedM C ProbComp (LogState C) A.net.State)) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State))
      (StateT (TsigState C) (SharedM C ProbComp (LogState C) A.net.State)) :=
  sigForger (loggedWorld prims D) A.net.State + (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D)
    Prod.fst Mode.real D A.net (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys)
    (fun _ => none) dealer + sigCell (C := C) (M := ProbComp) (W := LogState C) A.net.State)

omit [Fintype E] [DecidableEq E] in
/-- The signing phase with the answers of the dealer when a top tree is held. -/
theorem dealerSigning_run_some (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (s : RealState C A.net.State) (w : LogState C) (keysT : Keys C) (top : TopTree)
    (htop : topHolder D s.operators = some (keysT, top)) :
    ((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A
        (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)).run s).run w =
      ((sharedLift (loggedWorld prims D) (referenceTree tweakable (prfValue (gameSeeds D keys)) (gameParameter D keys)
          emptyTop .top)).run s).run w >>= fun p =>
        (((simulateQ (dealerHandlers prims K circuits settings runLimit keys D A
            (coupleDealer prims keys D A.net.State ((TreeOutput.topTree p.1.1).getD emptyTop)))
          (A.forge ⟨((TreeOutput.topTree p.1.1).getD emptyTop).root, gameParameter D keys⟩
            ((TreeOutput.topTree p.1.1).getD emptyTop))).run (startSig D) >>= fun q =>
            forgeryWins (sharedLift (loggedWorld prims D))
              (coupleDealer prims keys D A.net.State ((TreeOutput.topTree p.1.1).getD emptyTop)) q.2 q.1).run
          p.1.2).run p.2 := by
  unfold sharedSigning sharedDealer
  simp only [StateT.run_bind, StateT.run_get, pure_bind, htop, Bool.false_eq_true, ↓reduceIte]
  rw [show referenceTree (fun {α} oa => sharedLift (σ := A.net.State) (loggedWorld prims D) (tweakable oa))
      (fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D keys) x)) (gameParameter D keys) emptyTop .top =
      sharedLift (loggedWorld prims D) (referenceTree tweakable (prfValue (gameSeeds D keys)) (gameParameter D keys)
        emptyTop .top) from (SeedHitProof.hom_referenceTree (roHom prims D A.net.State) tweakable
          (prfValue (gameSeeds D keys)) (gameParameter D keys) emptyTop .top).symm]
  simp only [bind_assoc, StateT.run_pure, pure_bind]
  refine bind_congr fun p => ?_
  congr 1
  · congr 4
    funext t
    rcases t with t | q | q
    · rfl
    · rfl
    · cases q <;> rfl

omit [Fintype E] [DecidableEq E] in
/-- The signing phase with ghosts when a top tree is held. -/
theorem ghostSigning_run_some (keys : C.Party → Option (Keys C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (s : RealState C A.net.State) (w : LogState C) (keysT : Keys C) (top : TopTree)
    (htop : topHolder D s.operators = some (keysT, top)) :
    ((ghostSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D A (gameParameter D keys)
        (gameSeeds D keys) (fun i => (keys i).getD noKeys)).run s).run w =
      ((sharedLift (loggedWorld prims D) (referenceTree tweakable (prfValue (gameSeeds D keys)) (gameParameter D keys)
          emptyTop .top)).run s).run w >>= fun p =>
        (((simulateQ (ghostHandlers prims K circuits settings runLimit keys D A top)
          (A.forge ⟨top.root, keysT.parameter⟩ top)).run (startSig D) >>=
            ghostWinTest (loggedWorld prims D) D (gameParameter D keys) (gameSeeds D keys) top keysT).run p.1.2).run p.2 := by
  unfold ghostSigning
  simp only [StateT.run_bind, StateT.run_get, pure_bind, htop]
  rw [show sharedLift (σ := A.net.State) (loggedWorld prims D) ((fun _ => ()) <$> referenceTree tweakable
      (prfValue (gameSeeds D keys)) (gameParameter D keys) emptyTop .top) =
      (fun _ => ()) <$> sharedLift (loggedWorld prims D) (referenceTree tweakable (prfValue (gameSeeds D keys))
        (gameParameter D keys) emptyTop .top) from SeedHitProof.hom_map (roHom prims D A.net.State) _ _]
  simp only [StateT.run_map, bind_map_left]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem topHolder_some {σ : Type} {D : C.Coalition} {s : RealState C σ} {keysT : Keys C} {top : TopTree}
    (h : topHolder D s.operators = some (keysT, top)) :
    ∃ i, i ∉ D.1 ∧ (s.operators i).keys = some keysT ∧ (s.operators i).top = some top := by
  unfold topHolder at h
  split at h
  · rename_i i hi
    have hi' := List.find?_some hi
    simp only [decide_eq_true_eq] at hi'
    split at h
    · rename_i k t hk ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨i, hi'.1, hk, ht⟩
    · simp at h
  · simp at h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sharedLift_run_support {σ γ : Type} (D : C.Coalition) (oa : OracleComp (RoSpec C) γ) (s : RealState C σ)
    (w : LogState C) (p : (γ × RealState C σ) × LogState C)
    (hp : p ∈ support (((sharedLift (loggedWorld prims D) oa : SharedM C ProbComp (LogState C) σ γ).run s).run w)) :
    p.1.2 = s ∧ (p.1.1, p.2) ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))).run w) := by
  simp only [sharedLift, inWorld, StateT.run_lift, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  exact ⟨rfl, hy⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem runSig_support {σ α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α)
    (u : TsigState C × RealState C σ × LogState C) (o : α × (TsigState C × RealState C σ × LogState C))
    (ho : o ∈ support (runSig x u)) :
    ∃ z ∈ support (((x.run u.1).run u.2.1).run u.2.2), o = (z.1.1.1, (z.1.1.2, z.1.2, z.2)) := by
  unfold runSig at ho
  rw [support_map] at ho
  obtain ⟨z, hz, rfl⟩ := ho
  exact ⟨z, hz, rfl⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem run_bind_runSig {σ α β : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α)
    (f : α × TsigState C → SharedM C ProbComp (LogState C) σ β) (st : TsigState C) (s : RealState C σ)
    (w : LogState C) :
    ((x.run st >>= f).run s).run w = runSig x (st, s, w) >>= fun o => ((f (o.1, o.2.1)).run o.2.2.1).run o.2.2.2 := by
  simp [runSig, StateT.run_bind, bind_map_left]

end Unfold

omit [Fintype E] [DecidableEq E] in
/-- `RefSigning` from the erasure of the ghosts and the coupling. -/
theorem refSigning_of_ghosts (keeps : RefRunKeeps prims K circuits settings)
    (erase : GhostErase prims K circuits settings runLimit)
    (couple : GhostCouple prims K circuits settings runLimit) : RefSigning prims K circuits settings runLimit := by
  intro batch compute keys D A s w hinv
  rw [erase keys D A s w]
  exact couple keeps batch compute keys D A s w hinv

omit [Fintype E] [DecidableEq E] in
/-- `SharedRefDealer` from the outputs of one run, the erasure of the ghosts and the coupling. -/
theorem sharedRefDealer_of_ghosts (clean : PassCleanOutput prims K circuits settings)
    (erase : GhostErase prims K circuits settings runLimit) (couple : GhostCouple prims K circuits settings runLimit) :
    SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_clean prims K circuits settings runLimit clean (refSigning_of_ghosts prims K circuits settings
    runLimit (refRunKeeps_of_clean prims K circuits settings clean) erase couple)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_clean

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_ghosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_ghosts
