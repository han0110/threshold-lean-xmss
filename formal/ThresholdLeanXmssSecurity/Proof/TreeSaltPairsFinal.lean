import ThresholdLeanXmssSecurity.Proof.LifetimeSaltFrom
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltCertificatesFrom
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom
import ThresholdLeanXmssSecurity.Proof.TreeHashBudgetRun

/-!
# The first-run cut of the actual salt-pair experiment

The cut retains the adversary state, all pending honest programs, and both
caches with their complete log. Its round count is the exact first-run batch
schedule. In particular, stopping early preserves aborted prefixes.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeSaltPairsFinal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

def firstParty : C.Party := ⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩

def parameter (x : C.Party → Keys C) : PublicParameter := (x firstParty).parameter

def firstRounds (tree : Tree) (parameter : PublicParameter) : ℕ :=
  ((chunks settings.batchSize (treeLockstepFirstJobs tree)).map
    (batchRounds circuits settings.mode parameter)).sum

theorem firstRounds_le (tree : Tree) (parameter : PublicParameter) :
    firstRounds circuits settings tree parameter ≤ ceremonyFuel circuits settings - setupRounds := by
  have count : (chunks settings.batchSize (treeLockstepFirstJobs tree)).length ≤
      treeBatches settings tree := by
    cases tree <;> simp [treeLockstepFirstJobs, treeBatches]
  have cost : firstRounds circuits settings tree parameter ≤
      (chunks settings.batchSize (treeLockstepFirstJobs tree)).length *
        maxBatch circuits settings (runRounds settings.mode) := by
    cases tree with
    | top =>
      exact chunks_rounds_le circuits settings parameter 0 (fun _ => digit 0) _
        (fun _ h => Or.inl h)
    | bottom b =>
      exact chunks_rounds_le circuits settings parameter b (fun _ => digit 0) _
        (fun _ h => Or.inr (Or.inl h))
  exact cost.trans (by
    simp only [ceremonyFuel, Nat.add_sub_cancel_left]
    exact Nat.mul_le_mul_right _ (count.trans (treeBatches_le_ceremonyBatches settings tree)))

def first (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    ProbComp (TreeSimConfig A (TreeSimState C)) := do
  let next ← (simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2)).run p.2
  (executeSteps (treeSimRealRoles prims D) D A noFunctionality
    (firstRounds circuits settings tree (parameter x)) p.1.1 next.1).run next.2

def rest (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (m : TreeSimConfig A (TreeSimState C)) :
    ProbComp (Bool × TreeSimLog C) := do
  let out ← (executeRounds (treeSimRealRoles prims D) D A noFunctionality
    (ceremonyFuel circuits settings - setupRounds - firstRounds circuits settings tree (parameter x))
    m.1.1 m.1.2).run m.2
  treeSimRealObserve prims D A Z out

theorem split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    treeSaltAfterSetup prims K circuits settings top tree D A x Z p =
      first prims K circuits settings top tree D A x p >>= rest prims circuits settings tree D A x Z := by
  unfold treeSaltAfterSetup first rest
  rw [bind_assoc]
  apply bind_congr
  intro next
  have fuel := Nat.add_sub_of_le (firstRounds_le circuits settings tree (parameter x))
  conv_lhs => rw [← fuel, executeRounds_add, StateT.run_bind, bind_assoc]

theorem rest_extends (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (m : TreeSimConfig A (TreeSimState C))
    (r : Bool × TreeSimLog C)
    (hr : r ∈ support (rest prims circuits settings tree D A x Z m)) : m.2.2 <+: r.2 := by
  simp only [rest, mem_support_bind_iff] at hr
  obtain ⟨out, ho, hr⟩ := hr
  have hp : m.2.2 <+: out.2.2 := by
    apply treeSimLoggedWorld_prefix prims D _ m.2 out
    rw [simulateQ_executeRounds]
    exact ho
  exact hp.trans (treeSim_observe_prefix prims D A Z out r hr)

/-- The same concrete first-run cut is used for every address and pair. -/
def splits : TreeSaltStageSplits prims K circuits settings :=
  fun top tree D A x Z p =>
  { View := TreeSimConfig A (TreeSimState C)
    first := first prims K circuits settings top tree D A x p
    log := fun m => m.2.2
    rest := rest prims circuits settings tree D A x Z
    split := split prims K circuits settings top tree D A x Z p
    extend := fun m _ r hr => rest_extends prims circuits settings tree D A x Z m r hr }

theorem parameters_of_dealt (D : C.Coalition) (x : C.Party → Keys C)
    (hx : DealtInputs D x) : ∀ i, (x i).parameter = parameter x := by
  obtain ⟨P, seeds, pairs, hx⟩ := hx
  intro i
  simp only [parameter, hx, dealtKeys]

/-- A supported first stage is a prefix of the same real ceremony, after
the same counted prefix and start call. -/
theorem first_reach_from (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top tree D A x p)) :
    ∃ start ∈ support (LifetimeSaltFrom.prefixState prims D
        (pre >>= fun _ => A.start (corruptInputs D x) z)),
      TreeStagesReach prims K circuits settings top tree D A x start.1 start.2
        (firstRounds circuits settings tree (parameter x)) m := by
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  refine ⟨start, ?_, ?_⟩
  · simp only [LifetimeSaltFrom.prefixState, adversary_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff]
    exact ⟨s, hs, hstart⟩
  · simp only [TreeStagesReach, treeStagesTrace, StateT.run_bind, mem_support_bind_iff]
    exact ⟨p, hp, by simpa only [first, mem_support_bind_iff] using hm⟩

theorem trace_real (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (fuel : ℕ) :
    treeStagesTrace prims K circuits settings top tree D A x state fuel =
      simulateQ (treeSimLoggedWorld prims D) (do
        let p ← executePhase worldRoles D A noFunctionality 3 state
          (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
        let steps ← treeSimContinue (treeSimRealCont K circuits settings top tree x) p.2
        executeSteps worldRoles D A noFunctionality fuel p.1 steps) := by
  simp only [treeStagesTrace, simulateQ_bind, simulateQ_executePhase, treeLate_executeSteps_real]
  rfl

/-- The retained boundary log uses the actual final hash interpretation of
the whole prefix; no independence or extra row premise is imposed. -/
theorem first_rows_from (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top tree D A x p)) :
    ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ m.2.2 →
      TreeSimCheckWorldHashes (hashOf prims m.2.1.1) t u := by
  obtain ⟨start, hstart, reach⟩ := first_reach_from prims K circuits settings top tree D A x z pre s hs p hp m hm
  unfold TreeStagesReach at reach
  rw [trace_real] at reach
  apply treeHashBudget_logged_hashes prims D
    (worldRoles.adversary (pre >>= fun _ => A.start (corruptInputs D x) z) >>= fun st => do
      let p ← executePhase worldRoles D A noFunctionality 3 st
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
      let steps ← treeSimContinue (treeSimRealCont K circuits settings top tree x) p.2
      executeSteps worldRoles D A noFunctionality
        (firstRounds circuits settings tree (parameter x)) p.1 steps) (∅, ∅) m
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨start, hstart, by
    simpa only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] using reach⟩

/-- One boundary view fixes a common second-run encoding, including the
case in which every honest operator has already aborted. -/
theorem bottom_boundary_from (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top (.bottom b) D A x p))
    (good : ¬ TreeSimHashBudgetCollision m.2.2) :
    ∃ enc : Encoding, ∀ i, i ∉ D.1 → SegmentsStep
      (fun j _ _ label => TreeLateScheduleShape circuits settings (parameter x) b enc j label)
      (firstRounds circuits settings (.bottom b) (parameter x) + 1) (m.1.2 i) := by
  by_cases live : ∃ i, i ∉ D.1 ∧ m.1.2 i ≠ .done none
  · obtain ⟨start, _, reach⟩ := first_reach_from prims K circuits settings top (.bottom b) D A x z
      pre s hs p hp m hm
    exact treeLate_reach_boundary K circuits settings prims D A start.1 x (parameter x)
      (fun i _ => parameters_of_dealt D x hx i) top b (hashOf prims m.2.1.1) start.2 m reach good
      (first_rows_from prims K circuits settings top (.bottom b) D A x z pre s hs p hp m hm) live
  · refine ⟨fun _ => digit 0, fun i hi => ?_⟩
    have dead : m.1.2 i = .done none := by by_contra h; exact live ⟨i, hi, h⟩
    rw [dead]
    trivial

theorem bottom_early_from (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top (.bottom b) D A x p))
    (enc : Encoding) :
    ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ m.2.2 →
      ∀ T key label g, y = (.term T, key, label, 2, g) →
        ∃ j ≤ firstRounds circuits settings (.bottom b) (parameter x),
          TreeLateScheduleShape circuits settings (parameter x) b enc j label := by
  obtain ⟨start, hstart, reach⟩ := first_reach_from prims K circuits settings top (.bottom b) D A x z
    pre s hs p hp m hm
  apply treeLate_early_log K circuits settings prims D A start.1 x (parameter x)
    (fun i _ => parameters_of_dealt D x hx i) top b enc start.2 m reach
  intro y bit hy
  exact (TreeRawSaltCertificatesFromProof.prefix_no_free prims D _ start hstart
    (.inr (.inr y)) bit hy).elim

theorem setup_from_noSalt (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ p.2.2 →
      SaltRead (fun _ _ _ => False) y := by
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  have combined : start ∈ support (LifetimeSaltFrom.prefixState prims D
      (pre >>= fun _ => A.start (corruptInputs D x) z)) := by
    simp only [LifetimeSaltFrom.prefixState, adversary_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff]
    exact ⟨s, hs, hstart⟩
  obtain ⟨log, logs, noSalt⟩ := treeSetup_noSalt prims D A start.1 start.2 p hp
  intro y bit hy
  rw [logs] at hy
  rcases List.mem_append.mp hy with old | added
  · exact (TreeRawSaltCertificatesFromProof.prefix_no_free prims D _ start combined
      (.inr (.inr y)) bit old).elim
  · exact noSalt y bit added

/-- The exact setup outputs, rather than a separately chosen setup run,
determine the holder and key in each retained salt read. -/
theorem start_schedule (top : TopTree) (tree : Tree) (D : C.Coalition)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))
    (corrupt : ∀ i ∈ D.1, setup i = none) (s : TreeSimState C)
    (next : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (hn : next ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeSimContinue (treeSimRealCont K circuits settings top tree x) setup)).run s)) :
    ∃ log, next.2.2 = s.2 ++ log ∧
      (∀ i, i ∉ D.1 → SegmentsStep (OpSchedule circuits settings x tree setup i) 1 (next.1 i)) ∧
      ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
          (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
        ∃ i, i ∉ D.1 ∧ SaltRead (OpSchedule circuits settings x tree setup i 0) y := by
  have schedule : ∀ i prss, setup i = some prss → TreeSegmentsFrom
      (OpSchedule circuits settings x tree setup i) 0
      (treeSimRealCont K circuits settings top tree x i prss).run := fun i prss hk =>
    (treeSegmentsFrom_ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree).mono
      fun _ _ _ _ h => ⟨prss, hk, h⟩
  have world : WorldSalts prims D (fun y => ∃ i, i ∉ D.1 ∧
      SaltRead (OpSchedule circuits settings x tree setup i 0) y)
      (treeSimContinue (treeSimRealCont K circuits settings top tree x) setup) := by
    unfold treeSimContinue
    rw [free_sequenceFin]
    refine worldSalts_sequenceFin prims D _ fun i => ?_
    cases hk : setup i with
    | none =>
      simp only [continueStep, free_pure]
      exact WorldSalts.pure prims D _ _
    | some prss =>
      have hi : i ∉ D.1 := fun hi => by rw [corrupt i hi] at hk; cases hk
      simp only [continueStep]
      exact worldSalts_free_advance prims D
        ((schedule i prss hk).segmentSalts fun y hy => ⟨i, hi, hy⟩)
  obtain ⟨log, logs, salts⟩ := world s next hn
  refine ⟨log, logs, ?_, salts⟩
  have raw : next.1 ∈ support (treeSimContinue (treeSimRealCont K circuits settings top tree x) setup) := by
    apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨next, hn, rfl⟩
  intro i hi
  have row := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ raw) i
  cases hk : setup i with
  | none =>
    simp only [hk, continueStep, support_pure, Set.mem_singleton_iff] at row
    rw [row]
    trivial
  | some prss =>
    simp only [hk, continueStep] at row
    exact (schedule i prss hk).advance_mem _ row

theorem first_schedule (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (corrupt : ∀ i ∈ D.1, p.1.2 i = none)
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top tree D A x p)) :
    ∃ log, m.2.2 = p.2.2 ++ log ∧
      (∀ i, i ∉ D.1 → SegmentsStep (OpSchedule circuits settings x tree p.1.2 i)
        (firstRounds circuits settings tree (parameter x) + 1) (m.1.2 i)) ∧
      ∀ y bit, (⟨.inr (.inr (.inr y)), bit⟩ :
          (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
        ∃ i, i ∉ D.1 ∧ ∃ j ≤ firstRounds circuits settings tree (parameter x),
          SaltRead (OpSchedule circuits settings x tree p.1.2 i j) y := by
  simp only [first, mem_support_bind_iff] at hm
  obtain ⟨next, hn, hm⟩ := hm
  obtain ⟨before, beforeEq, steps, beforeSalts⟩ := start_schedule prims K circuits settings
    top tree D x p.1.2 corrupt p.2 next hn
  rw [treeLate_executeSteps_real] at hm
  obtain ⟨after, afterEq, finalSteps, afterSalts⟩ := treeLate_segments_steps prims D A
    (OpSchedule circuits settings x tree p.1.2)
    (firstRounds circuits settings tree (parameter x)) 1 p.1.1 next.1 next.2 m steps hm
  refine ⟨before ++ after, by rw [afterEq, beforeEq, List.append_assoc], ?_, ?_⟩
  · simpa only [Nat.add_comm] using finalSteps
  · intro y bit hy
    rcases List.mem_append.mp hy with old | added
    · obtain ⟨i, hi, salt⟩ := beforeSalts y bit old
      exact ⟨i, hi, 0, Nat.zero_le _, salt⟩
    · obtain ⟨i, hi, j, _, hj, salt⟩ := afterSalts y bit added
      exact ⟨i, hi, j, by omega, salt⟩

def commonKeys (setup : C.Party → Option (PrssKeys C)) (T : C.Term) : HashOutput :=
  if h : ∃ key, ∃ i pi, setup i = some pi ∧ i ∈ C.holders T ∧ key = pi.term T then
    Classical.choose h else 0

theorem commonKeys_eq (setup : C.Party → Option (PrssKeys C))
    (agree : ∀ i j ki kj, setup i = some ki → setup j = some kj →
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T)
    (i : C.Party) (pi : PrssKeys C) (present : setup i = some pi)
    (T : C.Term) (held : i ∈ C.holders T) : pi.term T = commonKeys setup T := by
  have h : ∃ key, ∃ i pi, setup i = some pi ∧ i ∈ C.holders T ∧ key = pi.term T :=
    ⟨pi.term T, i, pi, present, held, rfl⟩
  rw [commonKeys, dif_pos h]
  obtain ⟨j, pj, hpj, hj, eq⟩ := Classical.choose_spec h
  exact (agree i j pi pj present hpj T held hj).trans eq.symm

def firstLabels (tree : Tree) (parameter : PublicParameter) : List ℕ :=
  lockstepSaltLabels circuits parameter (chunks settings.batchSize (treeLockstepFirstJobs tree))

theorem first_label (tree : Tree) (parameter : PublicParameter) (keys : C.Term → HashOutput)
    (i : C.Party) (j : ℕ) (T : C.Term) (key : HashOutput) (label : ℕ)
    (early : j ≤ firstRounds circuits settings tree parameter)
    (h : CeremonySchedule circuits settings settings.mode parameter keys i tree j T key label) :
    label ∈ firstLabels circuits settings tree parameter := by
  obtain ⟨enc, _, _, k, hk, hc, hl, hj⟩ := h
  cases tree with
  | top =>
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hl.symm⟩
  | bottom b =>
    have first : k < (chunks settings.batchSize (bottomJobs b)).length := by
      by_contra h
      have mono := lockstepRoundStart_mono circuits settings.mode parameter
        (lockstepChunks settings enc (.bottom b)) (show
          (chunks settings.batchSize (bottomJobs b)).length ≤ k by omega)
      have start : lockstepRoundStart circuits settings.mode parameter
          (lockstepChunks settings enc (.bottom b)) (chunks settings.batchSize (bottomJobs b)).length =
          firstRounds circuits settings (.bottom b) parameter := by
        simp only [lockstepRoundStart, lockstepChunks, List.take_left, firstRounds, treeLockstepFirstJobs]
      rw [start] at mono
      unfold lockstepSaltRound at hj
      omega
    refine List.mem_map.mpr ⟨k, List.mem_range.mpr first, ?_⟩
    simpa only [lockstepSaltLabel, lockstepStart, lockstepChunks, treeLockstepFirstJobs,
      List.take_append_of_le_length first.le, List.getD_append _ _ [] k first] using hl.symm

theorem first_agreement_from (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top tree D A x p))
    (good : ¬ TreeSimHashBudgetCollision m.2.2) :
    TreeAgreementLog (commonKeys p.1.2) (firstLabels circuits settings tree (parameter x)) m.2.2 := by
  have noSalt := setup_from_noSalt prims D A x z pre s hs p hp
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, _, hp⟩ := hp
  obtain ⟨log, logs, _, salts⟩ := first_schedule prims K circuits settings top tree D A x p
    (treeSetup_corrupt_none prims D A start.1 start.2 p hp) m hm
  have setupGood : ¬ TreeSimHashBudgetCollision p.2.2 := fun bad =>
    good (treeSimHashBudgetCollision_mono (by rw [logs]; exact List.prefix_append _ _) bad)
  constructor
  intro T key label g bit hmem
  rw [logs] at hmem
  rcases List.mem_append.mp hmem with old | added
  · exact (noSalt _ bit old T key label g rfl).elim
  · obtain ⟨i, hi, j, hj, salt⟩ := salts _ bit added
    obtain ⟨pi, present, enc, keyEq, held, schedule⟩ := salt T key label g rfl
    refine ⟨keyEq.trans (commonKeys_eq p.1.2
      (treeSetup_phase_agree prims D A start.1 start.2 p hp setupGood) i pi present T held), ?_⟩
    apply first_label circuits settings tree (parameter x) pi.term i j T key label hj
    rw [← parameters_of_dealt D x hx i]
    exact ⟨enc, keyEq, held, schedule⟩

def encoding (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (m : TreeSimConfig A (TreeSimState C)) : Encoding :=
  match tree with
  | .top => fun _ => digit 0
  | .bottom b =>
    if h : ∃ enc : Encoding, ∀ i, i ∉ D.1 → SegmentsStep
        (fun j _ _ label => TreeLateScheduleShape circuits settings (parameter x) b enc j label)
        (firstRounds circuits settings (.bottom b) (parameter x) + 1) (m.1.2 i) then
      Classical.choose h else fun _ => digit 0

theorem segments_and {α : Type} {S S' : ℕ → C.Term → HashOutput → ℕ → Prop} {j : ℕ}
    {oa : OracleComp (PartySpec C E RealSpec) (Option α)}
    (left : TreeSegmentsFrom S j oa) :
    TreeSegmentsFrom S' j oa → TreeSegmentsFrom (fun j T key label => S j T key label ∧ S' j T key label) j oa := by
  induction left with
  | pure j a => intro _; exact .pure j a
  | queryLocal j q k hq h ih =>
    intro right
    cases right with
    | queryLocal _ _ _ hr rest =>
      exact .queryLocal j q k (fun y hy T key label g eq =>
        ⟨hq y hy T key label g eq, hr y hy T key label g eq⟩) (fun v => ih v (rest v))
  | round j out k h ih =>
    intro right
    cases right with
    | round _ _ _ rest => exact .round j out k (fun v => ih v (rest v))

theorem fixed_steps_from (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top tree D A x p))
    (good : ¬ TreeSimHashBudgetCollision m.2.2) :
    ∀ i, i ∉ D.1 → SegmentsStep
      (OpScheduleEnc circuits settings x tree (encoding circuits settings tree D x A m) p.1.2 i)
      (firstRounds circuits settings tree (parameter x) + 1) (m.1.2 i) := by
  have hp' := hp
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp'
  obtain ⟨start, _, hp'⟩ := hp'
  obtain ⟨_, _, steps, _⟩ := first_schedule prims K circuits settings top tree D A x p
    (treeSetup_corrupt_none prims D A start.1 start.2 p hp') m hm
  cases tree with
  | top =>
    intro i hi
    have old := steps i hi
    cases he : m.1.2 i with
    | done out => trivial
    | call input _ => exact input.elim
    | wait out resume =>
      rw [he] at old
      exact fun inbox => (old inbox).mono fun j T key label h => by
        obtain ⟨pi, present, enc, schedule⟩ := h
        exact ⟨pi, present, schedule⟩
  | bottom b =>
    have boundaryExists := bottom_boundary_from prims K circuits settings top b D A x z hx pre s hs p hp m hm good
    have chosen : ∀ i, i ∉ D.1 → SegmentsStep
        (fun j _ _ label => TreeLateScheduleShape circuits settings (parameter x) b
          (encoding circuits settings (.bottom b) D x A m) j label)
        (firstRounds circuits settings (.bottom b) (parameter x) + 1) (m.1.2 i) := by
      simpa only [encoding, dif_pos boundaryExists] using Classical.choose_spec boundaryExists
    intro i hi
    have old := steps i hi
    have shaped := chosen i hi
    cases he : m.1.2 i with
    | done out => trivial
    | call input _ => exact input.elim
    | wait out resume =>
      rw [he] at old shaped
      exact fun inbox => (segments_and (old inbox) (shaped inbox)).mono fun j T key label h =>
        treeLate_schedule_transfer circuits settings x (parameter x) b _ p.1.2 i
          (parameters_of_dealt D x hx i) j j T key label h.1 h.2

theorem firstLabels_subset (tree : Tree) (parameter : PublicParameter) (enc : Encoding) :
    firstLabels circuits settings tree parameter ⊆
      lockstepSaltLabels circuits parameter (lockstepChunks settings enc tree) := by
  intro label hlabel
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hlabel
  have hk := List.mem_range.mp hk
  cases tree with
  | top => exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  | bottom b =>
    change k < (chunks settings.batchSize (bottomJobs b)).length at hk
    refine List.mem_map.mpr ⟨k, List.mem_range.mpr (by
      simpa only [lockstepChunks, List.length_append] using
        hk.trans_le (Nat.le_add_right _ (chunks settings.batchSize (signJobs b enc)).length)), ?_⟩
    simp only [lockstepSaltLabel, lockstepStart, lockstepChunks, treeLockstepFirstJobs,
      List.take_append_of_le_length hk.le, List.getD_append _ _ [] k hk]

theorem observe_agreement (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (keys : C.Term → HashOutput) (labels : List ℕ)
    (out : TreeSimRoundOutput A (TreeSimState C)) (r : Bool × TreeSimLog C)
    (agree : TreeAgreementLog keys labels out.2.2)
    (hr : r ∈ support (treeSimRealObserve prims D A Z out)) :
    TreeAgreementLog keys labels r.2 := by
  simp only [treeSimRealObserve, support_map, Set.mem_image] at hr
  obtain ⟨result, run, rfl⟩ := hr
  obtain ⟨log, logs, noSalt⟩ := worldSalts_counted prims D (fun _ => False)
    (liftComp (Z out.1) _) out.2 result run
  constructor
  intro T key label g bit hmem
  rw [logs] at hmem
  rcases List.mem_append.mp hmem with old | added
  · exact agree.salt T key label g bit old
  · exact (noSalt _ bit added).elim

/-- Every suffix of the same boundary uses its selected encoding, including
suffixes that stop before a successful output and the final observation. -/
theorem rest_agreement_from (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (hx : DealtInputs D x)
    {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (first prims K circuits settings top tree D A x p))
    (r : Bool × TreeSimLog C) (hr : r ∈ support (rest prims circuits settings tree D A x Z m))
    (good : ¬ TreeSimHashBudgetCollision r.2) :
    TreeAgreementLog (commonKeys p.1.2)
      (lockstepSaltLabels circuits (parameter x)
        (lockstepChunks settings (encoding circuits settings tree D x A m) tree)) r.2 := by
  have midGood : ¬ TreeSimHashBudgetCollision m.2.2 := fun bad =>
    good (treeSimHashBudgetCollision_mono (rest_extends prims circuits settings tree D A x Z m r hr) bad)
  have early := first_agreement_from prims K circuits settings top tree D A x z hx pre s hs p hp m hm midGood
  have fixed := fixed_steps_from prims K circuits settings top tree D A x z hx pre s hs p hp m hm midGood
  have hp' := hp
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp'
  obtain ⟨start, _, hp'⟩ := hp'
  obtain ⟨firstLog, firstEq, _, _⟩ := first_schedule prims K circuits settings top tree D A x p
    (treeSetup_corrupt_none prims D A start.1 start.2 p hp') m hm
  have setupGood : ¬ TreeSimHashBudgetCollision p.2.2 := fun bad =>
    midGood (treeSimHashBudgetCollision_mono (by rw [firstEq]; exact List.prefix_append _ _) bad)
  simp only [rest, mem_support_bind_iff] at hr
  obtain ⟨out, ho, observe⟩ := hr
  rw [executeRounds_eq_executeSteps, StateT.run_map, support_map] at ho
  obtain ⟨last, tail, rfl⟩ := ho
  rw [treeLate_executeSteps_real] at tail
  obtain ⟨log, logs, _, salts⟩ := treeLate_segments_steps prims D A
    (OpScheduleEnc circuits settings x tree (encoding circuits settings tree D x A m) p.1.2)
    _ _ m.1.1 m.1.2 m.2 last fixed tail
  apply observe_agreement prims D A Z _ _ _ r (hr := observe)
  constructor
  intro T key label g bit hmem
  change _ ∈ last.2.2 at hmem
  rw [logs] at hmem
  rcases List.mem_append.mp hmem with old | added
  · obtain ⟨hk, hl⟩ := early.salt T key label g bit old
    exact ⟨hk, firstLabels_subset circuits settings tree (parameter x) _ hl⟩
  · obtain ⟨i, hi, j, _, _, salt⟩ := salts _ bit added
    obtain ⟨pi, present, keyEq, held, k, hk, _, hl, _⟩ := salt T key label g rfl
    refine ⟨keyEq.trans (commonKeys_eq p.1.2
      (treeSetup_phase_agree prims D A start.1 start.2 p hp' setupGood) i pi present T held), ?_⟩
    rw [parameters_of_dealt D x hx i] at hl
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hl.symm⟩

def addressSet (keys : C.Term → HashOutput) (labels : List ℕ) :
    Finset (C.Term × HashOutput × ℕ) :=
  ((Finset.univ : Finset C.Term) ×ˢ labels.toFinset).image fun a => (a.1, keys a.1, a.2)

def enumerate (S : Finset (C.Term × HashOutput × ℕ)) : Fin S.card → C.Term × HashOutput × ℕ :=
  fun i => (S.equivFin.symm i).1

theorem enumerate_injective (S : Finset (C.Term × HashOutput × ℕ)) :
    Function.Injective (enumerate S) := fun _ _ h => S.equivFin.symm.injective (Subtype.ext h)

theorem enumerate_mem (S : Finset (C.Term × HashOutput × ℕ)) (i : Fin S.card) :
    enumerate S i ∈ S := (S.equivFin.symm i).2

theorem mem_enumerate (S : Finset (C.Term × HashOutput × ℕ))
    (a : C.Term × HashOutput × ℕ) (ha : a ∈ S) : ∃ i, enumerate S i = a :=
  ⟨S.equivFin ⟨a, ha⟩, by simp [enumerate]⟩

theorem addressSet_mono (keys : C.Term → HashOutput) {labels labels' : List ℕ}
    (h : labels ⊆ labels') : addressSet keys labels ⊆ addressSet keys labels' := by
  apply Finset.image_mono
  intro x hx
  obtain ⟨hT, hl⟩ := Finset.mem_product.mp hx
  exact Finset.mem_product.mpr ⟨hT, List.mem_toFinset.mpr (h (List.mem_toFinset.mp hl))⟩

theorem addressSet_card (keys : C.Term → HashOutput) (labels : List ℕ) :
    (addressSet keys labels).card ≤ labels.length * termCount C := by
  calc (addressSet keys labels).card ≤ ((Finset.univ : Finset C.Term) ×ˢ labels.toFinset).card :=
        Finset.card_image_le
    _ = termCount C * labels.toFinset.card := by
        rw [Finset.card_product, Finset.card_univ, card_term C, termCount]
    _ ≤ termCount C * labels.length := Nat.mul_le_mul_left _ (List.toFinset_card_le _)
    _ = labels.length * termCount C := Nat.mul_comm _ _

theorem agreement_mem (keys : C.Term → HashOutput) (labels : List ℕ) (log : TreeSimLog C)
    (agree : TreeAgreementLog keys labels log) (T : C.Term) (key : HashOutput)
    (label g : ℕ) (bit : Bit)
    (h : (⟨.inr (.inr (.inr (.term T, key, label, 2, g))), bit⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log) :
    (T, key, label) ∈ addressSet keys labels := by
  obtain ⟨hk, hl⟩ := agree.salt T key label g bit h
  subst key
  exact Finset.mem_image.mpr ⟨(T, label), Finset.mem_product.mpr
    ⟨Finset.mem_univ _, List.mem_toFinset.mpr hl⟩, rfl⟩

def firstSet (tree : Tree) (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) :=
  addressSet (commonKeys setup) (firstLabels circuits settings tree (parameter x))

def fullSet (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (m : TreeSimConfig A (TreeSimState C)) :=
  addressSet (commonKeys setup) (lockstepSaltLabels circuits (parameter x)
    (lockstepChunks settings (encoding circuits settings tree D x A m) tree))

def secondSet (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (m : TreeSimConfig A (TreeSimState C)) :=
  fullSet circuits settings tree D x setup A m \ firstSet circuits settings tree x setup

theorem firstSet_subset (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (m : TreeSimConfig A (TreeSimState C)) :
    firstSet circuits settings tree x setup ⊆ fullSet circuits settings tree D x setup A m :=
  addressSet_mono _ (firstLabels_subset circuits settings tree (parameter x) _)

theorem table_injective (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (m : TreeSimConfig A (TreeSimState C)) :
    Function.Injective (Fin.append (enumerate (firstSet circuits settings tree x setup))
      (enumerate (secondSet circuits settings tree D x setup A m))) := by
  refine Fin.append_injective_iff.mpr ⟨enumerate_injective _, enumerate_injective _, ?_⟩
  intro i j eq
  exact (Finset.mem_sdiff.mp (enumerate_mem (secondSet circuits settings tree D x setup A m) j)).2
    (eq ▸ enumerate_mem (firstSet circuits settings tree x setup) i)

theorem table_card (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (m : TreeSimConfig A (TreeSimState C)) :
    (firstSet circuits settings tree x setup).card +
      (secondSet circuits settings tree D x setup A m).card ≤ treeBatches settings tree * termCount C := by
  rw [Nat.add_comm, secondSet, Finset.card_sdiff_add_card_eq_card (firstSet_subset circuits settings tree D x setup A m)]
  exact (addressSet_card _ _).trans (by
    simp only [lockstepSaltLabels, List.length_map, List.length_range, lockstepChunks_length, le_refl])

theorem fullSet_covered (tree : Tree) (D : C.Coalition) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (m : TreeSimConfig A (TreeSimState C)) (a : C.Term × HashOutput × ℕ)
    (ha : a ∈ fullSet circuits settings tree D x setup A m) :
    ∃ i, Fin.append (enumerate (firstSet circuits settings tree x setup))
      (enumerate (secondSet circuits settings tree D x setup A m)) i = a := by
  by_cases early : a ∈ firstSet circuits settings tree x setup
  · obtain ⟨i, hi⟩ := mem_enumerate _ a early
    exact ⟨i.castAdd _, by simpa only [Fin.append_left] using hi⟩
  · obtain ⟨i, hi⟩ := mem_enumerate (secondSet circuits settings tree D x setup A m) a
      (Finset.mem_sdiff.mpr ⟨ha, early⟩)
    exact ⟨i.natAdd _, by simpa only [Fin.append_right] using hi⟩

/-- A single pair of tables covers both stages of the actual split. The
second table removes repeated addresses before it is appended to the first. -/
theorem cover_from (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (hx : DealtInputs D x)
    {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    TreeSaltStagesCover (splits prims K circuits settings top tree D A x Z p)
      (treeBatches settings tree * termCount C)
      (firstSet circuits settings tree x p.1.2).card
      (enumerate (firstSet circuits settings tree x p.1.2))
      (fun m => (secondSet circuits settings tree D x p.1.2 A m).card)
      (fun m => enumerate (secondSet circuits settings tree D x p.1.2 A m)) := by
  intro m hm
  refine ⟨?_, table_injective circuits settings tree D x p.1.2 A m,
    table_card circuits settings tree D x p.1.2 A m, ?_⟩
  · intro good T key label g bit h
    apply mem_enumerate
    exact agreement_mem _ _ _
      (first_agreement_from prims K circuits settings top tree D A x z hx pre s hs p hp m hm good)
      T key label g bit h
  · intro r hr good T key label g bit h
    apply fullSet_covered circuits settings tree D x p.1.2 A m
    exact agreement_mem _ _ _
      (rest_agreement_from prims K circuits settings top tree D A x z Z hx pre s hs p hp m hm r hr good)
      T key label g bit h

/-- The probability estimate for the fixed tables of `cover_from`. This
contains no address-cover premise and no choice of a split or table. -/
def PairBoundsFrom : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ i j : ℕ, i < j →
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧
          TreeSaltPairReuse D
            (Fin.append (enumerate (firstSet circuits settings tree x p.1.2))
              (enumerate (secondSet circuits settings tree D x p.1.2 A r.1))) i j r.2.2 |
        (splits prims K circuits settings top tree D A x Z p).paired] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

theorem pairs_from_of_bounds (bounds : PairBoundsFrom prims K circuits settings) :
    LifetimeSaltFrom.TreeSaltStagesPairsFrom (splits prims K circuits settings) := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp
  refine ⟨(firstSet circuits settings tree x p.1.2).card,
    enumerate (firstSet circuits settings tree x p.1.2),
    (fun m => (secondSet circuits settings tree D x p.1.2 A m).card),
    (fun m => enumerate (secondSet circuits settings tree D x p.1.2 A m)),
    cover_from prims K circuits settings top tree D A x z Z hx pre s hs p hp, ?_⟩
  exact bounds hb top tree D A x z Z q hx hq hsmall pre s hs p hp

theorem pairs_of_bounds (bounds : PairBoundsFrom prims K circuits settings) :
    TreeSaltStagesPairs (splits prims K circuits settings) :=
  LifetimeSaltFrom.pairs_of_from _ (pairs_from_of_bounds prims K circuits settings bounds)

theorem addresses : TreeSaltStagesAddresses (splits prims K circuits settings) := by
  intro _ top tree D A x z Z hx p hp
  refine ⟨(firstSet circuits settings tree x p.1.2).card,
    enumerate (firstSet circuits settings tree x p.1.2),
    (fun m => (secondSet circuits settings tree D x p.1.2 A m).card),
    (fun m => enumerate (secondSet circuits settings tree D x p.1.2 A m)), ?_⟩
  exact cover_from prims K circuits settings top tree D A x z Z hx (pure ())
    ((), ((∅, ∅), [])) (by change _ ∈ support (pure _ : ProbComp _); simp) p hp

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.bottom_boundary_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bottom_boundary_from

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.first_agreement_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_agreement_from

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.rest_agreement_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rest_agreement_from

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.cover_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cover_from

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.pairs_from_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairs_from_of_bounds

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.pairs_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairs_of_bounds

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsFinal.addresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addresses

end ThresholdLeanXmssSecurity.TreeSaltPairsFinal
