import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.First
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Ceremony
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HeadCut
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.PhaseAbort
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Cells
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Sound
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.Walk

/-!
# The bound of one recorded run of a tree

`PassTopCover` and `PassBottomBound` state the bound of one recorded run of the top tree and of a
bottom tree with the shared event. `passTopCover` and `passBottomBound` prove them.

* `passBad_split` states that a bad check in records with a head of `n` batches and a tail is a bad
  check of the head below `n`, or a bad check of the tail with each honest head complete
  (`HeadComplete`). `reusedBefore_split` is the same split for a reused key.
* The recorded program of the top tree is one ceremony with the record of a pass and then the local
  hash of the root, which records nothing (`passTree_top`). The ceremony takes exactly its rounds
  under the parameter of the honest keys (`timedR_passCeremony`). So `passTopCover` bounds the
  recorded run of the top tree by the ghost run of its ceremony.
* The recorded program of a bottom tree is its recorded head `passHead` (the first ceremony and the
  local search) and then its recorded rest `passRest` (the second ceremony and the local end), by
  `passTree_bottom`. `passBottomBound` splits a run at the end of the head
  (`executePhaseR_bind_world`), and `passCeremonyBad` bounds the event of the head. A dead honest
  operator at the cut gives no start and no opening in the rest (`executePhaseR_dead`). With each
  honest operator alive, the records of the rest are the head record and then the record of the
  ghost run of the second ceremony (`executePhaseR_mapSteps`), and `passCeremonyBad` bounds that
  ghost run. The premises of `passBottomBound` are `PassLaw` and `PassFresh`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

/-! ## The two bounds of one recorded run -/

section Statements

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The run of the top tree is its one ceremony. A recorded run of the top tree with the shared event
and no global event at its end is at most as likely as a bad check or a reused key of the ghost run
of the ceremony of `topStart`, with no global event at its end. The run is that ceremony and the
local hash of the root, which records nothing. The honest operators of the start hold consistent
seeds, so the ceremony has one round count for all of them. -/
def PassTopCover : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (s : RealState C net.State) (world : StreamState C),
    seedsDiffer D (fun i => (s.operators i).keys) = false →
    Pr{let r ← (passTreeRun prims K circuits settings D net .top s).run world}[r.1.2 = true ∧ ¬ GlobalEvent r.2] ≤
      Pr{let ω ← (passGhost prims K circuits settings D net (treeFuel circuits settings) (topStart s)).run world}[
        ((∃ k ∈ Finset.range (chunks settings.batchSize (topStart (σ := net.State) s).jobs).length,
          BadCheckAt K D k ω.1.2) ∨ ReusedKey D world.2 ω.1.2) ∧ ¬ GlobalEvent ω.2]

/-- The bound of one recorded run of a bottom tree with the shared event from a ready start. The
run has the cut of the library before its second ceremony, as `runBad_bottom`, and `passCeremonyBad`
is the bound of each of its two ceremonies. -/
def PassBottomBound : Prop :=
  0 < settings.batchSize → 0 < runLimit → CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      ∀ (b : Fin (2 ^ layerHeight)) (s : RealState C A.net.State) (world : StreamState C),
        PassReady (startBudget circuits settings runLimit C q) D s world → s.flag = false →
        (Pr{let r ← (passTreeRun prims K circuits settings D A.net (.bottom b) s).run world}[
            r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤ runError (E := E) circuits settings runLimit C q (.bottom b)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The fuel of a run covers the ceremony of the top tree, for each parameter. -/
theorem topFuel (parameter : PublicParameter) :
    CheckTiming.ceremonyRounds circuits settings parameter topJobs ≤ treeFuel circuits settings := by
  have h := topRounds_le circuits settings parameter
  rw [← CheckTiming.batchesRounds_eq circuits settings parameter topJobs]
  unfold Fuel.batchesRounds treeFuel
  omega

end Statements

/-! ## The shared event on records with a head and a tail -/

section Records

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E)

/-- The bad check `k` of `PassBad`. -/
def PassBadAt (D : C.Coalition) (k : ℕ) (records : C.Party → Record C E) : Prop :=
  (∀ i, i ∉ D.1 → ((startsOf (records i))[k]?).isSome) ∧
    (WrongTuple D (passTuples K k records) ∨ ¬ MultVerifyAgree D (honestTuples D (passTuples K k records))) ∧
    ∃ i, i ∉ D.1 ∧ k < (openingsOf (records i)).length

omit [Fintype E] [DecidableEq E] in
theorem passBad_iff (D : C.Coalition) (records : C.Party → Record C E) :
    PassBad K D records ↔ ∃ k, PassBadAt K D k records := Iff.rfl

omit [Fintype E] [DecidableEq E] in
/-- A bad check reads the records of the honest operators only, and only their starts at `k` and the
count of their openings. -/
theorem passBadAt_congr (D : C.Coalition) (k : ℕ) (r r' : C.Party → Record C E)
    (hstart : ∀ i, i ∉ D.1 → (startsOf (r i))[k]? = (startsOf (r' i))[k]?)
    (hopen : ∀ i, i ∉ D.1 → (k < (openingsOf (r i)).length ↔ k < (openingsOf (r' i)).length)) :
    PassBadAt K D k r ↔ PassBadAt K D k r' := by
  have htuples : ∀ i, i ∉ D.1 → passTuples K k r i = passTuples K k r' i := fun i hi => by
    simp only [passTuples, hstart i hi]
  have hview := honestView_congr D htuples
  unfold PassBadAt
  unfold WrongTuple honestTuples
  rw [hview]
  constructor
  · rintro ⟨hs, hw, i, hi, ho⟩
    exact ⟨fun j hj => hstart j hj ▸ hs j hj, hw, i, hi, (hopen i hi).1 ho⟩
  · rintro ⟨hs, hw, i, hi, ho⟩
    exact ⟨fun j hj => (hstart j hj).symm ▸ hs j hj, hw, i, hi, (hopen i hi).2 ho⟩

/-- A head record of a ceremony of `n` batches is complete when it has `n` starts and `n` openings. -/
def HeadComplete (n : ℕ) (head : Record C E) : Prop :=
  (startsOf head).length = n ∧ (openingsOf head).length = n

/-- The shape of the records of a run with a head of `n` batches. Each honest operator has the record
`[]` or its head and then its tail. Each head has at most `n` starts, and a tail with a start or an
opening comes only after a complete head. -/
def SplitRecords (D : C.Coalition) (n : ℕ) (r h t : C.Party → Record C E) : Prop :=
  ∀ i, i ∉ D.1 → (r i = [] ∨ r i = h i ++ t i) ∧ (startsOf (h i)).length ≤ n ∧
    (startsOf (t i) ≠ [] ∨ openingsOf (t i) ≠ [] → HeadComplete n (h i))

omit [Fintype E] [DecidableEq E] in
/-- The split of a bad check. A bad check in records with a head of `n` batches is a bad check of
the head below `n`, or a bad check of the tail with each honest head complete. -/
theorem passBad_split (D : C.Coalition) (n : ℕ) (r h t : C.Party → Record C E) (hs : SplitRecords D n r h t)
    (hbad : PassBad K D r) :
    (∃ k < n, PassBadAt K D k h) ∨ ((∀ i, i ∉ D.1 → HeadComplete n (h i)) ∧ PassBad K D t) := by
  obtain ⟨k, hstarted, hwrong, i₀, hi₀, hopen₀⟩ := hbad
  have hr : ∀ i, i ∉ D.1 → r i = h i ++ t i := fun i hi => by
    rcases (hs i hi).1 with h0 | h0
    · have := hstarted i hi
      rw [h0] at this
      simp [startsOf] at this
    · exact h0
  by_cases hk : k < n
  · left
    -- Each honest record has its start `k` in the head.
    have hhead : ∀ i, i ∉ D.1 → k < (startsOf (h i)).length ∨ (startsOf (t i) = [] ∧ openingsOf (t i) = []) := by
      intro i hi
      by_cases ht : startsOf (t i) ≠ [] ∨ openingsOf (t i) ≠ []
      · exact Or.inl (((hs i hi).2.2 ht).1 ▸ hk)
      · simp only [ne_eq, not_or, not_not] at ht
        exact Or.inr ht
    have hstart : ∀ i, i ∉ D.1 → (startsOf (r i))[k]? = (startsOf (h i))[k]? := by
      intro i hi
      rw [hr i hi, startsOf_append]
      rcases hhead i hi with hlt | ⟨ht, -⟩
      · exact List.getElem?_append_left hlt
      · rw [ht, List.append_nil]
    have hopen : ∀ i, i ∉ D.1 → (k < (openingsOf (r i)).length ↔ k < (openingsOf (h i)).length) := by
      intro i hi
      rw [hr i hi, length_openingsOf_append]
      by_cases ht : startsOf (t i) ≠ [] ∨ openingsOf (t i) ≠ []
      · have hc := (hs i hi).2.2 ht
        constructor
        · intro _
          rw [hc.2]
          exact hk
        · intro h'
          omega
      · simp only [ne_eq, not_or, not_not] at ht
        rw [ht.2, List.length_nil, Nat.add_zero]
    exact ⟨k, hk, (passBadAt_congr K D k r h hstart hopen).1 ⟨hstarted, hwrong, i₀, hi₀, hopen₀⟩⟩
  · right
    simp only [not_lt] at hk
    -- Each honest record has its start `k` in the tail, so each honest head is complete.
    have hcomplete : ∀ i, i ∉ D.1 → HeadComplete n (h i) := by
      intro i hi
      refine (hs i hi).2.2 (Or.inl fun ht => ?_)
      have h1 := hstarted i hi
      rw [hr i hi, startsOf_append, ht, List.append_nil] at h1
      have h2 := (hs i hi).2.1
      rw [Option.isSome_iff_exists] at h1
      obtain ⟨b, hb⟩ := h1
      have := (List.getElem?_eq_some_iff.1 hb).1
      omega
    refine ⟨hcomplete, k - n, ?_⟩
    have hstart : ∀ i, i ∉ D.1 → (startsOf (r i))[k]? = (startsOf (t i))[k - n]? := by
      intro i hi
      rw [hr i hi, startsOf_append, List.getElem?_append_right (by rw [(hcomplete i hi).1]; exact hk),
        (hcomplete i hi).1]
    have hopen : ∀ i, i ∉ D.1 → (k < (openingsOf (r i)).length ↔ k - n < (openingsOf (t i)).length) := by
      intro i hi
      rw [hr i hi, length_openingsOf_append, (hcomplete i hi).2]
      omega
    have htuples : ∀ i, i ∉ D.1 → passTuples K k r i = passTuples K (k - n) t i := fun i hi => by
      simp only [passTuples, hstart i hi]
    have hview := honestView_congr D htuples
    unfold WrongTuple honestTuples at hwrong
    unfold WrongTuple honestTuples
    rw [hview] at hwrong
    exact ⟨fun i hi => hstart i hi ▸ hstarted i hi, hwrong, i₀, hi₀, (hopen i₀ hi₀).1 hopen₀⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The split of a reused key. A start of the records is a start of the head or of the tail. -/
theorem reusedBefore_split (D : C.Coalition) (hidden : HiddenCache C) (r h t : C.Party → Record C E)
    (hr : ∀ i, i ∉ D.1 → r i = [] ∨ r i = h i ++ t i) (hreused : ReusedBefore D hidden r) :
    ReusedBefore D hidden h ∨ ReusedBefore D hidden t := by
  obtain ⟨name, key, hhid, ⟨i, hi, b, hb, hkey⟩, hcell⟩ := hreused
  rcases hr i hi with h0 | h0
  · rw [h0] at hb
    simp [startsOf] at hb
  · rw [h0, startsOf_append, List.mem_append] at hb
    rcases hb with hb | hb
    · exact Or.inl ⟨name, key, hhid, ⟨i, hi, b, hb, hkey⟩, hcell⟩
    · exact Or.inr ⟨name, key, hhid, ⟨i, hi, b, hb, hkey⟩, hcell⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A reused key at a cache is reused at each larger cache. -/
theorem reusedBefore_mono (D : C.Coalition) (hidden hidden' : HiddenCache C) (r : C.Party → Record C E)
    (hle : ∀ c, hidden c ≠ none → hidden' c ≠ none) (hreused : ReusedBefore D hidden r) :
    ReusedBefore D hidden' r := by
  obtain ⟨name, key, hhid, huses, ρ, idx, position, hcell⟩ := hreused
  exact ⟨name, key, hhid, huses, ρ, idx, position, hle _ hcell⟩

end Records

section Top

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## One recorded ceremony -/

omit [Fintype E] [DecidableEq E] in
/-- One recorded ceremony with its record dropped is `ceremonyProgram`. -/
theorem dropRec_passCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    dropRec (passCeremony K circuits settings i c) = ceremonyProgram K circuits settings i c := by
  unfold passCeremony ceremonyProgram
  rcases c.keys i with _ | keys
  · exact dropRec_failure
  · rw [MonadHom.mmap_bind]
    change (dropRecS (passRun K circuits settings plainShares i keys c.jobs)).run c.counters >>= _ = _
    rw [dropRecS_passRun_plain]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · exact dropRec_failure
    · exact MonadHom.mmap_pure _ _

/-- One recorded ceremony at an honest operator takes exactly the rounds of the ceremony under the
parameter of its keys. -/
theorem timedR_passCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (parameter : PublicParameter)
    (h : ∀ keys, c.keys i = some keys → keys.parameter = parameter) :
    TimedR (CheckTiming.ceremonyRounds circuits settings parameter c.jobs)
      (passCeremony K circuits settings i c).run.run := by
  refine timedR_of_timed _ ?_
  change Timed _ (dropRec (passCeremony K circuits settings i c)).run
  rw [dropRec_passCeremony]
  rcases hk : c.keys i with _ | keys
  · unfold ceremonyProgram
    rw [hk]
    exact timed_failure _
  · rw [← h keys hk]
    exact timed_ceremonyProgram_exact K circuits settings i c keys hk

omit [Fintype E] [DecidableEq E] in
/-- Each outcome of one recorded ceremony has at most one start for each batch, and an outcome with
a result has exactly one start and one opening for each batch. -/
theorem recordCount_passCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    RecordCount (chunks settings.batchSize c.jobs).length (chunks settings.batchSize c.jobs).length
      (passCeremony K circuits settings i c).run.run := by
  unfold passCeremony
  rcases c.keys i with _ | keys
  · exact recordCount_failure _ _
  · have h := recordCount_recBind (recordCount_passRun K circuits settings i keys c.jobs c.counters)
      fun p => show RecordCount 0 0 ((p.1.elim failure fun outputs => pure (outputs, p.2) : RecM C E _)).run.run by
        rcases p with ⟨_ | outputs, st⟩
        · exact recordCount_failure 0 0
        · exact recordCount_pure _
    simpa only [Nat.add_zero] using h

/-! ## The top tree -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The local tail of the top tree takes no round. -/
theorem timed_topTail (operator : OperatorState C) (o : CeremonyResult) :
    Timed 0 (topTail (E := E) operator o).run := by
  unfold topTail
  split
  · rename_i keys _
    have hrun : RunTimed 0 (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter (fun _ => pure (some o.1)) emptyTop
          .top) := by
      simp only [ceremonyOutput, pure_bind]
      refine (RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun root => ?_).of_eq rfl
      exact runTimed_pure _
    have h1 := (Timed.map Prod.fst (hrun o.2)).bind (n := 0) fun out =>
      show Timed 0 (out.elim failure pure : PartyM C E RealSpec TreeOutput).run by
        rcases out with _ | out
        · exact timed_failure 0
        · exact timed_pure out
    exact h1
  · exact timed_failure 0

omit [Fintype E] [DecidableEq E] in
/-- The recorded program of the top tree is one recorded ceremony and then the local tail. -/
theorem passTree_top (i : C.Party) {σ : Type} (s : RealState C σ) :
    passTree K circuits settings plainShares none i (s.operators i) .top =
      passCeremony K circuits settings i (topStart s) >>= fun o => RecM.lift (topTail (s.operators i) o) := by
  unfold passTree passCeremony topTail
  simp only [topStart]
  rcases (s.operators i).keys with _ | keys
  · simp only [failure_bind]
  · simp only [ceremonyOutput, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · simp only [Option.elim, failure_bind, StateT.run_pure, map_pure, pure_bind]
    · simp only [Option.elim, pure_bind, StateT.run_pure, RecM.liftS, StateT.run_lift, recM_lift_bind,
        recM_lift_pure]
      simp only [map_eq_bind_pure_comp, StateT.run_bind, StateT.run_mk, StateT.run_lift, StateT.run_pure,
        recM_lift_bind, recM_lift_pure, bind_assoc, pure_bind, Function.comp_apply]

omit [Fintype E] [DecidableEq E] in
/-- The shared event of a recorded run is an event of its phase. -/
theorem passTreeRun_prEvent (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (world : StreamState C) :
    Pr{let r ← (passTreeRun prims K circuits settings D net tree s).run world}[r.1.2 = true ∧ ¬ GlobalEvent r.2] =
      Pr{let z ← (simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E)
          (treeFuel circuits settings) s.adversary fun i =>
            (passTree K circuits settings plainShares none i (s.operators i) tree).run.run)).run world}[
        (PassBad K D (fun i => (z.1.2 i).record []) ∨ ReusedBefore D world.2 (fun i => (z.1.2 i).record [])) ∧
          ¬ GlobalEvent z.2] := by
  unfold passTreeRun
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure]
  rw [bind_pure_comp, prEvent_map]
  refine prEvent_congr _ _ _ fun z => ?_
  simp only [decide_eq_true_eq]
  tauto

/-- The cover of the top tree. A recorded run of the top tree with the shared event and no global
event at its end is at most as likely as a bad check or a reused key of the ghost run of its ceremony
with no global event at its end. -/
theorem passTopCover : PassTopCover prims K circuits settings := by
  intro D net s world hseeds
  obtain ⟨parameter, hpar⟩ := exists_parameter D s hseeds
  have hfuel := topFuel circuits settings parameter
  obtain ⟨a, ha⟩ : ∃ a, CheckTiming.ceremonyRounds circuits settings parameter topJobs = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, treeFuel circuits settings = a + b := ⟨treeFuel circuits settings - a, by omega⟩
  have hj : (topStart (σ := net.State) s).jobs = topJobs := by simp only [topStart]
  have htimed : ∀ i ∉ D.1, TimedR a (passCeremony K circuits settings i (topStart s)).run.run := fun i hi => by
    have h := timedR_passCeremony K circuits settings i (topStart s) parameter (hpar i hi)
    rwa [hj, ha] at h
  have hprog : (fun i => (passTree K circuits settings plainShares none i (s.operators i) .top).run.run) =
      fun i => (passCeremony K circuits settings i (topStart s)).run.run >>=
        recCont (fun o => RecM.lift (topTail (s.operators i) o)) :=
    funext fun i => by rw [passTree_top, run_recBind]
  rw [passTreeRun_prEvent, hprog]
  unfold passGhost
  rw [hb, (phase_fuel_eq prims D net noFunctionality ([] : Record C E) _ b (topStart s).adversary _ htimed
    world).prEvent_eq]
  refine prEvent_tail_le prims D net noFunctionality ([] : Record C E) _ b (topStart s).adversary _ htimed _
    (fun i => localTail_recCont_lift _ (timed_topTail (s.operators i))) world _ _ ?_
  rintro y z hy hrec hle ⟨hbad, hglobal⟩
  have hrecs : (fun i => (z.1.2 i).record []) = ceremonyRecord y.1.2 := funext hrec
  rw [hrecs] at hbad
  refine ⟨?_, fun h => hglobal (globalEvent_mono hle h)⟩
  rcases hbad with hbad | hreused
  · obtain ⟨k, hk⟩ := (passBad_iff K D _).1 hbad
    refine Or.inl ⟨k, Finset.mem_range.2 ?_, hk⟩
    obtain ⟨hstart, -, i, hi, -⟩ := hk
    obtain ⟨-, hdone⟩ := executePhaseR_timed_shape D net noFunctionality ([] : Record C E) _ _ _ htimed y.1 hy
    have hmem := Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) _ _ _ y.1 hy i hi (hdone i hi)
    have hcount := (recordCount_passCeremony K circuits settings i (topStart s) _ hmem).1
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hstart i hi)
    exact lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hb').1 hcount
  · exact Or.inr hreused

end Top

section Bottom

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The recorded programs of a bottom tree -/

/-- The recorded head of a bottom tree, the first recorded ceremony and then the local search. -/
def passHead (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) : RecM C E HeadResult :=
  passCeremony K circuits settings i (firstStart b s) >>= fun o => RecM.lift (headTail (s.operators i) b o)

/-- The recorded rest of a bottom tree after the head result `x`, the second recorded ceremony and then
the local end. -/
def passRest (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) (x : HeadResult) :
    RecM C E TreeOutput :=
  passCeremony K circuits settings i (secondStart b s s.adversary x) >>= fun o =>
    RecM.lift (secondTail (s.operators i) b x.1 o)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem firstLocal_liftS (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (st : ℕ × ℕ) :
    (firstLocal (m := StateT (ℕ × ℕ) (RecM C E)) (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa))))
        parameter b outputs).run st =
      RecM.lift ((firstLocal (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter b outputs).run st) := by
  unfold firstLocal
  simp only [StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift, recM_lift_bind, recM_lift_pure, bind_assoc,
    pure_bind]
  refine bind_congr fun root => bind_congr fun base => bind_congr fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩ <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem secondLocal_liftS (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (values : List (List Bit)) (st : ℕ × ℕ) :
    (secondLocal (m := StateT (ℕ × ℕ) (RecM C E)) (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa))))
        parameter top b x values).run st =
      RecM.lift ((secondLocal (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter top b x values).run st) := by
  unfold secondLocal
  simp only [StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift, recM_lift_bind, recM_lift_pure, bind_assoc,
    pure_bind]
  refine bind_congr fun path => bind_congr fun topRoot => ?_
  split_ifs <;> rfl

omit [Fintype E] [DecidableEq E] in
/-- The recorded program of a bottom tree is the recorded head and then the recorded rest. -/
theorem passTree_bottom (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    passTree K circuits settings plainShares none i (s.operators i) (.bottom b) =
      passHead K circuits settings i s b >>= passRest K circuits settings i s b := by
  unfold passTree passHead passRest passCeremony headTail secondTail
  simp -implicitDefEqProofs only [firstStart, secondStart, aliveKeys]
  rcases (s.operators i).keys with _ | keys <;> rcases (s.operators i).top with _ | top
  · simp -implicitDefEqProofs only [failure_bind]
  · simp -implicitDefEqProofs only [failure_bind]
  · simp -implicitDefEqProofs only [failure_bind]
  · simp -implicitDefEqProofs only
    rw [ceremonyOutput_bottom_split]
    simp -implicitDefEqProofs only [StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · simp -implicitDefEqProofs only [Option.elim, failure_bind, StateT.run_pure, map_pure, pure_bind]
    · simp -implicitDefEqProofs only [Option.elim, pure_bind, StateT.run_bind, firstLocal_liftS, map_bind, bind_assoc, recM_lift_bind]
      refine bind_congr fun g => ?_
      rcases g with ⟨_ | x, st'⟩
      · simp -implicitDefEqProofs only [StateT.run_pure, map_pure, pure_bind, recM_lift_failure, failure_bind]
      · simp -implicitDefEqProofs only [StateT.run_bind, map_bind, bind_assoc, recM_lift_pure, pure_bind]
        refine bind_congr fun p => ?_
        rcases p with ⟨_ | values, st''⟩
        · simp -implicitDefEqProofs only [StateT.run_pure, map_pure, pure_bind, failure_bind]
        · simp -implicitDefEqProofs only [pure_bind, secondLocal_liftS, map_eq_bind_pure_comp, recM_lift_bind, bind_assoc,
            Function.comp_apply, recM_lift_pure]
          refine bind_congr fun out => ?_
          rcases out with _ | out
          · simp -implicitDefEqProofs only [recM_lift_failure]
          · rfl

/-! ## Facts of the recorded head and the recorded rest -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The local search of a bottom tree takes no round. -/
theorem timed_headTail (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) (o : CeremonyResult) :
    Timed 0 (headTail (E := E) operator b o).run := by
  unfold headTail
  split
  · rename_i keys _
    have hrun : RunTimed 0 (firstLocal (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter b o.1) := by
      unfold firstLocal
      refine (RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun root => ?_).of_eq rfl
      refine (RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun base => ?_).of_eq rfl
      refine (RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun g => ?_).of_eq rfl
      rcases g with _ | ⟨randomness, encoding⟩
      · exact runTimed_pure _
      · exact runTimed_pure _
    have h1 := (hrun o.2).bind (n := 0) fun p =>
      show Timed 0 (p.1.elim failure fun x => pure (x, p.2) : PartyM C E RealSpec HeadResult).run by
        rcases p with ⟨_ | x, st⟩
        · exact timed_failure 0
        · exact timed_pure _
    exact h1
  · exact timed_failure 0

omit [Fintype E] [DecidableEq E] in
theorem passHead_run (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    (passHead K circuits settings i s b).run.run = (passCeremony K circuits settings i (firstStart b s)).run.run >>=
      recCont (fun o => RecM.lift (headTail (s.operators i) b o)) := by
  unfold passHead
  rw [run_recBind]

omit [Fintype E] [DecidableEq E] in
theorem passRest_run (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) (st : σ)
    (x : HeadResult) :
    (passRest K circuits settings i s b x).run.run =
      (passCeremony K circuits settings i (secondStart b s st x)).run.run >>=
        recCont (fun o => RecM.lift (secondTail (s.operators i) b x.1 o)) := by
  unfold passRest
  rw [run_recBind]
  rfl

/-- The recorded head takes exactly the rounds of the first ceremony under the parameter `P` of the
keys of the operator. -/
theorem timedR_passHead (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight))
    (P : PublicParameter) (h : ∀ keys, aliveKeys s i = some keys → keys.parameter = P) :
    TimedR (CheckTiming.ceremonyRounds circuits settings P (bottomJobs b)) (passHead K circuits settings i s b).run.run := by
  rw [passHead_run]
  have hj : (firstStart (σ := σ) b s).jobs = bottomJobs b := by simp only [firstStart]
  have h1 := timedR_passCeremony K circuits settings i (firstStart b s) P h
  rw [hj] at h1
  exact timedR_bind_localTail h1 (localTail_recCont_lift _ fun o => timed_headTail (s.operators i) b o)

omit [Fintype E] [DecidableEq E] in
theorem recordCount_passHead (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    RecordCount (chunks settings.batchSize (firstStart (σ := σ) b s).jobs).length
      (chunks settings.batchSize (firstStart (σ := σ) b s).jobs).length (passHead K circuits settings i s b).run.run := by
  unfold passHead
  have h := recordCount_recBind (s₂ := 0) (o₂ := 0) (recordCount_passCeremony K circuits settings i (firstStart b s))
    fun o => recordCount_lift (headTail (s.operators i) b o)
  rwa [Nat.add_zero] at h

omit [Fintype E] [DecidableEq E] in
/-- The recorded rest starts with the exchange of the second PRSS setup, so it aborts on an abort
frame with no record. -/
theorem abortsOnAbort_passRest (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight))
    (x : HeadResult) : AbortsOnAbort ([] : Record C E) (passRest K circuits settings i s b x).run.run := by
  unfold passRest passCeremony
  simp -implicitDefEqProofs only [secondStart]
  rcases aliveKeys s i with _ | keys
  · rw [failure_bind]
    exact abortsOnAbort_pure (α := TreeOutput) []
  · unfold passRun
    simp -implicitDefEqProofs only [StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift, recM_lift_bind,
      bind_assoc]
    exact abortsOnAbort_lift_bind _ (startsWithRound_prssSetup i) _

omit [Fintype E] [DecidableEq E] in
/-- The recorded head with its record dropped is `bottomHead`. -/
theorem dropRec_passHead (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    dropRec (passHead K circuits settings i s b) = CheckTiming.bottomHead K circuits settings i (s.operators i) b := by
  unfold passHead
  rw [MonadHom.mmap_bind, dropRec_passCeremony, bottomHead_split]
  refine bind_congr fun o => ?_
  exact dropRec_lift _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The fuel of a run covers both ceremonies of a bottom tree, for each parameter and encoding. -/
theorem bottomFuel (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    CheckTiming.ceremonyRounds circuits settings parameter (bottomJobs b) +
        CheckTiming.ceremonyRounds circuits settings parameter (signJobs b encoding) ≤ treeFuel circuits settings := by
  have h := bottomRounds_le circuits settings parameter b encoding
  rw [← CheckTiming.batchesRounds_eq circuits settings parameter (bottomJobs b),
    ← CheckTiming.batchesRounds_eq circuits settings parameter (signJobs b encoding)]
  unfold Fuel.batchesRounds treeFuel
  omega

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hidden_cell_mono {w w' : HiddenCache C} (hle : w ≤ w') (c : _) (h : w c ≠ none) : w' c ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hle hv]
  simp

end Bottom

/-! ## The bound of a recorded run of a bottom tree -/

section BottomBound

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [DecidableEq E] in
/-- The bound of one recorded run of a bottom tree with the shared event from a ready start, from
the joint law `PassLaw` and the fresh part `PassFresh` of one recorded ceremony. -/
theorem passBottomBound (law : PassLaw prims K circuits settings) (fresh : PassFresh prims K circuits settings) :
    PassBottomBound prims K circuits settings runLimit := by
  intro batch runs compute D A q bounded b s world ready flag
  obtain ⟨start, step, forge, hsum, -, hround, -⟩ := id bounded
  have hstep : ∀ st sent, IsQueryBoundP (A.net.round st sent) Counted step := fun st sent =>
    isQueryBoundP_of_queryCostAtMost (hround st sent) fun _ ht =>
      one_le_ownCost (exists_inClass ht).choose_spec
  have hq : dkgTsigRounds circuits settings runLimit * step ≤ q := by omega
  have hkeys : seedsDiffer D (aliveKeys s) = false := seedsDiffer_sub D _ _ (aliveKeys_some s) ready.1
  obtain ⟨P, hP⟩ : ∃ P, gameParameter D (aliveKeys s) = P := ⟨_, rfl⟩
  have hpar : ∀ i, i ∉ D.1 → ∀ keys, aliveKeys s i = some keys → keys.parameter = P :=
    fun i hi keys hk => hP ▸ parameter_eq_gameParameter D _ hkeys i hi keys hk
  obtain ⟨n, hn⟩ : ∃ n, CheckTiming.ceremonyRounds circuits settings P (bottomJobs b) = n := ⟨_, rfl⟩
  have hfuel₂ : ∀ enc, n + CheckTiming.ceremonyRounds circuits settings P (signJobs b enc) ≤
      treeFuel circuits settings := fun enc => hn ▸ bottomFuel circuits settings P b enc
  have hnle : n ≤ treeFuel circuits settings := (Nat.le_add_right _ _).trans (hfuel₂ fun _ => digit 0)
  obtain ⟨m, hm⟩ : ∃ m, treeFuel circuits settings = n + m := ⟨_, (Nat.add_sub_cancel' hnle).symm⟩
  obtain ⟨b₁, hb₁⟩ : ∃ k, (chunks settings.batchSize (bottomJobs b)).length = k := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ k, (chunks settings.batchSize (signJobs b fun _ => digit 0)).length = k := ⟨_, rfl⟩
  have hlen₂ : ∀ enc, (chunks settings.batchSize (signJobs b enc)).length = b₂ := fun enc => by
    rw [← hb₂]
    simp [chunks_length, signJobs]
  have hb : b₁ + b₂ = treeBatches settings (.bottom b) := by
    rw [← hb₁, ← hb₂]
    exact bottomBatches settings b _
  have hj₁ : (firstStart (σ := A.net.State) b s).jobs = bottomJobs b := by simp only [firstStart]
  have htimed₁ : ∀ i ∉ D.1, TimedR n (passHead K circuits settings i s b).run.run := fun i hi =>
    hn ▸ timedR_passHead K circuits settings i s b P (hpar i hi)
  have hprog : (fun i => (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run) =
      fun i => (passHead K circuits settings i s b).run.run >>= recCont (passRest K circuits settings i s b) :=
    funext fun i => by rw [passTree_bottom, run_recBind]
  have hsplit := GhostSplit.executePhaseR_bind_world D A.net noFunctionality ([] : Record C E)
    (fun i => recCont (passRest K circuits settings i s b)) (WorldSplit.streamWorld_freeCommute prims D)
    (fun i w => rfl) n m s.adversary _ htimed₁ world
  obtain ⟨ε₂, hε₂⟩ : ∃ ε : ℝ, ε = b₂ * checkErrorMax (E := E) circuits settings runLimit C q +
      ceremonyFresh C (gameSetups runLimit + 1) := ⟨_, rfl⟩
  have hε₂0 : 0 ≤ ε₂ := by
    rw [hε₂]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (checkErrorMax_nonneg circuits settings runLimit q))
      (by unfold ceremonyFresh; positivity)
  let HeadBad : (A.net.State × (C.Party → RStep C E RealSpec HeadResult (Record C E))) × StreamState C → Prop :=
    fun y => ((∃ k < b₁, PassBadAt K D k fun i => (y.1.2 i).record []) ∨
      ReusedBefore D world.2 (fun i => (y.1.2 i).record [])) ∧ ¬ GlobalEvent y.2
  have hready₁ : CeremonyReady D (startBudget circuits settings runLimit C q) (firstStart b s) world :=
    ⟨hkeys, ready.2.1, ready.2.2⟩
  rw [passTreeRun_prEvent, hprog, hm, hsplit.prEvent_eq]
  simp only [simulateQ_bind, StateT.run_bind]
  have hrest : ∀ y ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D A.net noFunctionality
      ([] : Record C E) n s.adversary fun i => (passHead K circuits settings i s b).run.run)).run world),
      Pr{let z ← (simulateQ (streamWorld prims D) (executePhaseR worldRoles D A.net noFunctionality
          ([] : Record C E) m y.1.1 fun i => recCont (passRest K circuits settings i s b)
            ((y.1.2 i).output, (y.1.2 i).record []))).run y.2}[
          (PassBad K D (fun i => (z.1.2 i).record []) ∨ ReusedBefore D world.2 (fun i => (z.1.2 i).record [])) ∧
            ¬ GlobalEvent z.2] ≤
        (if HeadBad y then 1 else 0) + (if True then ENNReal.ofReal ε₂ else 0) := by
    intro y hy
    by_cases hH : HeadBad y
    · rw [ite_eq_left hH]
      exact (prEvent_le_one _).trans le_self_add
    rw [ite_eq_right hH, zero_add, ite_eq_left trivial]
    have hy' := mem_support_phase prims D _ world y hy
    obtain ⟨hD, hd⟩ := executePhaseR_timed_shape D A.net noFunctionality ([] : Record C E) n s.adversary _
      htimed₁ y.1 hy'
    have hL₁ : (chunks settings.batchSize (firstStart (σ := A.net.State) b s).jobs).length = b₁ := by
      rw [hj₁, hb₁]
    have hcount : ∀ i, i ∉ D.1 → (startsOf ((y.1.2 i).record [])).length ≤ b₁ ∧
        ((y.1.2 i).output.isSome → HeadComplete b₁ ((y.1.2 i).record [])) := fun i hi => by
      have h := recordCount_passHead K circuits settings i s b _
        (Joint.executePhaseR_out_mem D A.net noFunctionality ([] : Record C E) n s.adversary _ y.1 hy' i hi (hd i hi))
      rw [hL₁] at h
      exact h
    by_cases hG : GlobalEvent y.2
    · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_)).trans bot_le
      exact h.2 (globalEvent_mono (streamWorld_run_mono prims D _ y.2 z hz) hG)
    have hnotHead : ¬ ((∃ k < b₁, PassBadAt K D k fun i => (y.1.2 i).record []) ∨
        ReusedBefore D world.2 (fun i => (y.1.2 i).record [])) := fun h => hH ⟨h, hG⟩
    by_cases hdead : ∃ j, j ∉ D.1 ∧ (y.1.2 j).output = none
    · obtain ⟨j₀, hj₀, hnone⟩ := hdead
      refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => ?_)).trans bot_le
      have hz' := mem_support_phase prims D _ y.2 z hz
      have hrec := executePhaseR_dead D A.net noFunctionality ([] : Record C E) m y.1.1 _
        (fun i => (y.1.2 i).record []) j₀ hj₀ (by rw [hnone]; rfl) (fun i hi => by
          rcases ho : (y.1.2 i).output with _ | x
          · exact abortsOnAbort_pure _
          · exact abortsOnAbort_prefix _ _ (abortsOnAbort_passRest K circuits settings i s b x)) z.1 hz'
      have hsplitR : SplitRecords D b₁ (fun i => (z.1.2 i).record []) (fun i => (y.1.2 i).record [])
          (fun _ => []) := fun i hi =>
        ⟨by rcases hrec i hi with h | h
            · exact Or.inl h
            · exact Or.inr (by simp only [h, List.append_nil]),
          (hcount i hi).1, fun ht => by simp [startsOf, openingsOf] at ht⟩
      obtain ⟨hbad, -⟩ := hE
      rcases hbad with hbad | hre
      · rcases passBad_split K D b₁ _ _ _ hsplitR hbad with h | ⟨-, k, -, -, i, -, hk⟩
        · exact hnotHead (Or.inl h)
        · simp [openingsOf] at hk
      · rcases reusedBefore_split D world.2 _ _ _ (fun i hi => (hsplitR i hi).1) hre with
          h | ⟨-, -, -, ⟨i, -, b', hb', -⟩, -⟩
        · exact hnotHead (Or.inr h)
        · simp [startsOf] at hb'
    simp only [not_exists, not_and] at hdead
    have htimedPlain : ∀ i ∉ D.1, Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run :=
      fun i hi => by
        rw [← dropRec_passHead K circuits settings i s b]
        exact timed_of_timedR _ (htimed₁ i hi)
    have hsupp : ((y.1.1, fun i => (y.1.2 i).output), y.2) ∈
        support ((bottomCut prims K circuits settings D A.net b s n).run world) := by
      unfold bottomCut
      have heq : (fun i => CheckTiming.bottomHead K circuits settings i (s.operators i) b) =
          fun i => dropRecord (passHead K circuits settings i s b).run.run :=
        funext fun i => (dropRec_passHead K circuits settings i s b).symm
      rw [heq, executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D A.net noFunctionality
        ([] : Record C E) n s.adversary _, simulateQ_map, StateT.run_map, support_map]
      exact ⟨y, hy, rfl⟩
    obtain ⟨hfit, hPz, hagree⟩ := cutState_of_supports K circuits settings (fun prims =>
      ceremonySupport_of_parts prims K circuits settings (ceremonyCounters prims K circuits settings)
        (CeremonyRecords.ceremonyOutputsAgree prims K circuits settings)
        (ledgerSplit prims K circuits settings) (ledgerSound prims K circuits settings)
        (ledgerSalts prims K circuits settings) (ledgerHidden prims K circuits settings)
        (ceremonyProvenance prims K circuits settings)) prims D A.net step hstep _ b s world n htimedPlain
      hready₁ _ hsupp
    obtain ⟨x, hx⟩ : ∃ x : HeadResult, ∀ i, i ∉ D.1 → (y.1.2 i).output = some x := by
      by_cases hne : ∃ i, i ∉ D.1
      · obtain ⟨i₀, hi₀⟩ := hne
        obtain ⟨x, hxo⟩ := Option.ne_none_iff_exists'.1 (hdead i₀ hi₀)
        refine ⟨x, fun i hi => ?_⟩
        obtain ⟨xi, hxi⟩ := Option.ne_none_iff_exists'.1 (hdead i hi)
        rw [hxi, hagree hG i i₀ xi x hi hi₀ hxi hxo]
      · exact ⟨(([], 0, 0, fun _ => digit 0), (0, 0)), fun i hi => absurd ⟨i, hi⟩ hne⟩
    -- The rest is the second ceremony with the head records in front.
    have hR : ∀ i, i ∉ D.1 → recCont (passRest K circuits settings i s b) ((y.1.2 i).output, (y.1.2 i).record []) =
        (fun q => (q.1, (y.1.2 i).record [] ++ q.2)) <$> (passRest K circuits settings i s b x).run.run :=
      fun i hi => by rw [hx i hi]; rfl
    rw [executePhaseR_mapSteps D A.net noFunctionality ([] : Record C E) (fun i => ((y.1.2 i).record [] ++ ·)) m
      y.1.1 (fun i => (passRest K circuits settings i s b x).run.run) _ hR, simulateQ_map, StateT.run_map, prEvent_map]
    obtain ⟨a₂, ha₂⟩ : ∃ a, CheckTiming.ceremonyRounds circuits settings P (signJobs b x.1.2.2.2) = a := ⟨_, rfl⟩
    have hm₂ : m = a₂ + (m - a₂) := by
      have := hfuel₂ x.1.2.2.2
      omega
    have hj₂ : (secondStart (σ := A.net.State) b s y.1.1 x).jobs = signJobs b x.1.2.2.2 := by
      simp only [secondStart]
    have htimed₂ : ∀ i ∉ D.1, TimedR a₂ (passCeremony K circuits settings i (secondStart b s y.1.1 x)).run.run :=
      fun i hi => by
        have h := timedR_passCeremony K circuits settings i (secondStart b s y.1.1 x) P (hpar i hi)
        rwa [hj₂, ha₂] at h
    have hQ : (fun i => (passRest K circuits settings i s b x).run.run) = fun i =>
        (passCeremony K circuits settings i (secondStart b s y.1.1 x)).run.run >>=
          recCont (fun o => RecM.lift (secondTail (s.operators i) b x.1 o)) :=
      funext fun i => passRest_run K circuits settings i s b y.1.1 x
    have hworld : world.2 ≤ y.2.2 := streamWorld_run_hidden_mono prims D _ world y hy
    rw [hQ, hm₂]
    refine (prEvent_tail_le prims D A.net noFunctionality ([] : Record C E) a₂ (m - a₂) y.1.1 _ htimed₂ _
      (fun i => localTail_recCont_lift _ fun o => timed_secondTail (s.operators i) b x.1 o) y.2 _
      (fun ω => ((∃ k ∈ Finset.range (chunks settings.batchSize (secondStart (σ := A.net.State) b s y.1.1 x).jobs).length,
          BadCheckAt K D k ω.1.2) ∨ ReusedKey D y.2.2 ω.1.2) ∧ ¬ GlobalEvent ω.2) ?_).trans ?_
    · rintro y' z' hy'' hrec' hle' hEz
      obtain ⟨hbad, hglobal⟩ := hEz
      refine ⟨?_, fun h => hglobal (globalEvent_mono hle' h)⟩
      have hsplitR : SplitRecords D b₁ (fun i => (mapSteps D (fun i => ((y.1.2 i).record [] ++ ·)) z'.1.2 i).record [])
          (fun i => (y.1.2 i).record []) (ceremonyRecord y'.1.2) := fun i hi => by
        refine ⟨?_, (hcount i hi).1, fun _ => (hcount i hi).2 (by rw [hx i hi]; rfl)⟩
        have hmi : mapSteps D (fun i => ((y.1.2 i).record [] ++ ·)) z'.1.2 i =
            mapStep ((y.1.2 i).record [] ++ ·) (z'.1.2 i) := ite_eq_right hi
        simp only [hmi]
        rcases mapStep_record ((y.1.2 i).record [] ++ ·) [] (z'.1.2 i) with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h, hrec' i]; rfl)
      rcases hbad with hbad | hre
      · rcases passBad_split K D b₁ _ _ _ hsplitR hbad with h | ⟨-, hbad₂⟩
        · exact absurd (Or.inl h) hnotHead
        · obtain ⟨k, hk⟩ := (passBad_iff K D _).1 hbad₂
          refine Or.inl ⟨k, Finset.mem_range.2 ?_, hk⟩
          obtain ⟨hstart, -, i, hi, -⟩ := hk
          obtain ⟨-, hdone⟩ := executePhaseR_timed_shape D A.net noFunctionality ([] : Record C E) _ _ _ htimed₂
            y'.1 hy''
          have hmem := Joint.executePhaseR_out_mem D A.net noFunctionality ([] : Record C E) _ _ _ y'.1 hy'' i hi
            (hdone i hi)
          have hc := (recordCount_passCeremony K circuits settings i (secondStart b s y.1.1 x) _ hmem).1
          obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hstart i hi)
          exact lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hb').1 hc
      · rcases reusedBefore_split D world.2 _ _ _ (fun i hi => (hsplitR i hi).1) hre with h | h
        · exact absurd (Or.inr h) hnotHead
        · exact Or.inr (reusedBefore_mono D world.2 y.2.2 _ (fun c hc => hidden_cell_mono hworld c hc) h)
    · have hready₂ : CeremonyReady D (ledgerStep circuits settings C step n b₁ (startBudget circuits settings runLimit C q))
          (secondStart b s y.1.1 x) y.2 := ⟨hkeys, hb₁ ▸ hfit, hPz⟩
      have hbad₂ := passCeremonyBad prims K circuits settings runLimit law fresh D A.net q step a₂ hstep _
        (secondStart b s y.1.1 x) y.2
        (admissible_of_protocol circuits settings b x.1.2.2.2 _ (Or.inr (Or.inr hj₂))) hready₂
        (by rw [hj₂, hlen₂]
            exact ledgerRoom_second circuits settings runLimit runs (.bottom b) q step n a₂ b₁ b₂
              (ha₂ ▸ hfuel₂ x.1.2.2.2) hb.le hq)
        (padded_le circuits settings runLimit runs q step a₂ (le_trans (Nat.le_add_left _ _) (ha₂ ▸ hfuel₂ x.1.2.2.2)) hq)
        (by rw [hj₂, show gameParameter D (secondStart (σ := A.net.State) b s y.1.1 x).keys = P from hP, ha₂])
      rw [hj₂, hlen₂] at hbad₂
      rw [ENNReal.le_ofReal_iff_toReal_le (prEvent_ne_top _) hε₂0]
      unfold passGhost at hbad₂
      rw [hε₂, hj₂, hlen₂]
      exact hbad₂
  have hhead : Pr{let y ← (simulateQ (streamWorld prims D) (executePhaseR worldRoles D A.net noFunctionality
      ([] : Record C E) n s.adversary fun i => (passHead K circuits settings i s b).run.run)).run world}[HeadBad y] ≤
      Pr{let ω ← (passGhost prims K circuits settings D A.net n (firstStart b s)).run world}[
        ((∃ k ∈ Finset.range (chunks settings.batchSize (firstStart (σ := A.net.State) b s).jobs).length,
          BadCheckAt K D k ω.1.2) ∨ ReusedKey D world.2 ω.1.2) ∧ ¬ GlobalEvent ω.2] := by
    have hp : (fun i => (passHead K circuits settings i s b).run.run) = fun i =>
        (passCeremony K circuits settings i (firstStart b s)).run.run >>=
          recCont (fun o => RecM.lift (headTail (s.operators i) b o)) :=
      funext fun i => passHead_run K circuits settings i s b
    have htimedc : ∀ i ∉ D.1, TimedR n (passCeremony K circuits settings i (firstStart b s)).run.run :=
      fun i hi => by
        have h := timedR_passCeremony K circuits settings i (firstStart b s) P (hpar i hi)
        rwa [hj₁, hn] at h
    have h := prEvent_tail_le prims D A.net noFunctionality ([] : Record C E) n 0 s.adversary _ htimedc _
      (fun i => localTail_recCont_lift _ fun o => timed_headTail (s.operators i) b o) world HeadBad
      (fun ω => ((∃ k ∈ Finset.range (chunks settings.batchSize (firstStart (σ := A.net.State) b s).jobs).length,
          BadCheckAt K D k ω.1.2) ∨ ReusedKey D world.2 ω.1.2) ∧ ¬ GlobalEvent ω.2) (by
        rintro y z - hrec hle ⟨hbad, hglobal⟩
        have hrecs : (fun i => (z.1.2 i).record []) = ceremonyRecord y.1.2 := funext hrec
        refine ⟨?_, fun h => hglobal (globalEvent_mono hle h)⟩
        rcases hbad with ⟨k, hk, hbadk⟩ | hre
        · rw [hrecs] at hbadk
          exact Or.inl ⟨k, Finset.mem_range.2 (by rw [hj₁, hb₁]; exact hk), hbadk⟩
        · rw [hrecs] at hre
          exact Or.inr hre)
    rw [Nat.add_zero] at h
    rw [hp]
    exact h
  have hroom₁ := ledgerRoom_first (C := C) circuits settings runLimit runs (.bottom b) q step n b₁ hnle
    (by omega) hq
  have hbad₁ := passCeremonyBad prims K circuits settings runLimit law fresh D A.net q step n hstep _
    (firstStart b s) world
    (admissible_of_protocol circuits settings b (fun _ => digit 0) _ (Or.inr (Or.inl hj₁))) hready₁
    (by rw [hj₁, hb₁]; exact hroom₁) (padded_le circuits settings runLimit runs q step n hnle hq)
    (by rw [hj₁, show gameParameter D (firstStart (σ := A.net.State) b s).keys = P from hP, hn])
  rw [hj₁, hb₁] at hbad₁ hhead
  have hmain := probEvent_bind_le_split HeadBad (fun _ => True) (ENNReal.ofReal ε₂) hrest
  have hle := hmain.trans (add_le_add hhead (mul_le_of_le_one_left' (prEvent_le_one _)))
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨prEvent_ne_top _, ENNReal.ofReal_ne_top⟩) hle
  rw [ENNReal.toReal_add (prEvent_ne_top _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε₂0] at hreal
  have hfresh := bottomFresh_le (C := C) runLimit b
  have hk : (startBudget circuits settings runLimit C q).hiddenKeys = gameSetups runLimit := rfl
  rw [hk] at hbad₁
  unfold runError
  rw [← hb]
  push_cast
  unfold ceremonyFresh at hfresh hε₂ hbad₁
  rw [hε₂] at hreal
  linarith

end BottomBound

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passTopCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passTopCover

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passBottomBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passBottomBound
