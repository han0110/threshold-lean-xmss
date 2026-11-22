import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutWalk

/-!
# The end counters, the check with the count zero and the monitor

`ceremonyCounters` proves `CeremonyCounters`. Each batch of a ceremony adds `jobLabel` to the label
and one to the tag, so the end counters of an honest result are `endCounters` of the job list, at the
parameter of the game. `zeroCheck` proves `ZeroCheck`. The tuples of the first honest operator are the
first input of the honest tuples, and their counts are zero. `monitorProvenance` proves
`MonitorProvenance`. The monitor calls `H` on the free copy only, so the hidden cache stays and the
hash cache grows.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)
open GameCount (MonitorCall)

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## The end counters -/

/-- The real batches of a ceremony add `jobLabel` of each batch to the label and their number to the
tag. -/
theorem mapM_realBatch_counters {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (parameter : PublicParameter) :
    ∀ (l : List (List Job)) (st : ℕ × ℕ) (r : List (Option (List (List Bit))) × (ℕ × ℕ)),
      some r ∈ support ((l.mapM (realBatch K circuits settings.mode ctx parameter)).run st).run →
        r.2 = (st.1 + (l.map (jobLabel circuits parameter)).sum, st.2 + l.length)
  | [], st, r, hr => by
    simp only [List.mapM_nil, StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq] at hr
    subst hr
    simp
  | b :: l, st, r, hr => by
    rw [List.mapM_cons, StateT.run_bind] at hr
    rcases mem_support_optionT_bind _ _ _ hr with h | ⟨p, hp, hr⟩
    · cases h
    rw [StateT.run_bind] at hr
    rcases mem_support_optionT_bind _ _ _ hr with h | ⟨q, hq, hr⟩
    · cases h
    simp only [StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
    subst hr
    have h₁ := realBatch_support K circuits settings ctx parameter b st p hp
    have h₂ := mapM_realBatch_counters K circuits settings ctx parameter l p.2 q hq
    rw [h₂, h₁]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Prod.mk.injEq]
    constructor <;> ring

/-- Each result of the program of one ceremony has the end counters of the job list at the parameter
of the keys of the operator. -/
theorem ceremonyProgram_counters (i : C.Party) {σ : Type} (s : CeremonyStart C σ) (keys : Keys C)
    (hk : s.keys i = some keys) (o : CeremonyResult)
    (ho : some o ∈ support (ceremonyProgram K circuits settings i s).run) :
    o.2 = endCounters circuits settings keys.parameter s.counters s.jobs := by
  unfold ceremonyProgram at ho
  rw [hk] at ho
  rcases mem_support_optionT_bind _ _ _ ho with h | ⟨p, hp, ho⟩
  · cases h
  rcases p with ⟨_ | outputs, st⟩
  · simp at ho
  simp only [Option.elim, OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at ho
  subst ho
  rw [CheckTiming.ceremonyRun_run_keys] at hp
  rcases mem_support_optionT_bind _ _ _ hp with h | ⟨prss, -, hp⟩
  · cases h
  rcases mem_support_optionT_bind _ _ _ hp with h | ⟨q, hq, hp⟩
  · cases h
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hp
  rw [hp.2]
  exact mapM_realBatch_counters K circuits settings _ _ _ _ _ hq

/-- `CeremonyCounters`. -/
theorem ceremonyCounters : CeremonyCounters prims K circuits settings := by
  intro D net rounds ℓ c world ready r hr i o hi ho
  have hr' : r.1 ∈ support (executePhase worldRoles D net noFunctionality rounds c.adversary fun i =>
      ceremonyProgram K circuits settings i c) := by
    refine support_simulateQ_run'_subset (streamWorld prims D) _ world ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  have hprog := SetupCut.executePhase_reach D net rounds c.adversary _ r.1 hr' i hi o ho
  rcases hk : c.keys i with _ | keys
  · unfold ceremonyProgram at hprog
    rw [hk] at hprog
    simp at hprog
  · rw [ceremonyProgram_counters K circuits settings i c keys hk o hprog,
      parameter_eq_gameParameter D c.keys ready.1 i hi keys hk]

/-! ## The check with the count zero -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The first value of a list under a partial map is the value at the first element that it maps. -/
theorem headD_filterMap_of_find {β : Type} (p : C.Party → Bool) (x : C.Party → β) (d : β) :
    ∀ (l : List C.Party) (j : C.Party), l.find? p = some j →
      (l.filterMap fun i => if p i then some (x i) else none).headD d = x j
  | [], j, h => by simp at h
  | a :: l, j, h => by
    by_cases ha : p a
    · simp only [List.find?_cons, ha, Option.some.injEq] at h
      subst h
      simp [ha]
    · simp only [List.find?_cons, ha] at h
      simp only [List.filterMap_cons, ha]
      exact headD_filterMap_of_find p x d l j h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The first input of the honest tuples is the list of the first honest operator. -/
theorem firstInput_honestTuples (D : C.Coalition) (x : C.Party → List (Tuple C)) (j : C.Party)
    (hj : C.parties.find? (fun i => decide (i ∉ D.1)) = some j) :
    firstInput (honestTuples D x) = x j := by
  have h := headD_filterMap_of_find (fun i => decide (i ∉ D.1)) x default C.parties j hj
  unfold firstInput honestTuples
  rw [← h]
  congr 1
  refine List.filterMap_congr fun i _ => ?_
  by_cases hi : i ∈ D.1 <;> simp [hi]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A tuple of a first input whose counts sum to zero has the count zero. -/
theorem tupleAt_count_zero (views : C.Party → Option (List (Tuple C)))
    (hzero : ((firstInput views).map (·.count)).sum = 0) (m : ℕ) : (tupleAt views m).count = 0 := by
  unfold tupleAt
  dsimp only
  rcases hm : (firstInput views)[m]? with _ | τ
  · rfl
  · have hmem : τ.count ∈ (firstInput views).map (·.count) := List.mem_map.2 ⟨τ, List.mem_of_getElem? hm, rfl⟩
    simpa using List.sum_eq_zero_iff.1 hzero τ.count hmem

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `ZeroCheck`. -/
theorem zeroCheck : ZeroCheck (C := C) (E := E) := by
  intro D σ α r world start hstop hsum
  unfold jointStop at hstop
  split_ifs at hstop with hall
  split at hstop
  · rename_i j hj
    simp only [Option.some.injEq] at hstop
    subst hstop
    dsimp only at hsum ⊢
    have hfirst := firstInput_honestTuples D (fun i => (stopPoint i (r.2 i)).tuples) j hj
    have hzero : ((firstInput (honestTuples D fun i => (stopPoint i (r.2 i)).tuples)).map (·.count)).sum = 0 := by
      rw [hfirst]
      exact hsum
    have hcount := tupleAt_count_zero _ hzero
    refine ⟨?_, ?_⟩
    · rintro ⟨m, -, g, hg, -⟩
      have := hcount m
      unfold honestTuples at this
      omega
    · intro k hk T i _ j' _ _ _ g hg
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range, hcount k] at hg
      omega
  · cases hstop

/-! ## The monitor -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A call of the monitor in `streamWorld` keeps the hidden cache and grows the hash cache. -/
theorem streamWorld_monitorCall (D : C.Coalition) (t : (WorldSpec C).Domain) (ht : MonitorCall t)
    (w : StreamState C) : ∀ y ∈ support ((streamWorld prims D t).run w), y.2.2 = w.2 ∧ w.1 ≤ y.2.1 := by
  intro y hy
  refine ⟨?_, streamWorld_mono prims D t w y hy⟩
  rcases t with (_ | _) | (_ | q | x)
  · exact ht.elim
  · exact ht.elim
  · exact ht.elim
  · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ w y hy
    rfl
  · exact ht.elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation with only calls of the monitor in `streamWorld` keeps the hidden cache and grows
the hash cache. -/
theorem simulateQ_monitorCall (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : NoCall (fun t => ¬ MonitorCall t) oa) :
    ∀ w, ∀ y ∈ support ((simulateQ (streamWorld prims D) oa).run w), y.2.2 = w.2 ∧ w.1 ≤ y.2.1 := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro w y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨rfl, le_rfl⟩
  | query_bind t k ih =>
    intro w y hy
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have ht : MonitorCall t := by
      rcases h.1 with h1 | h1
      · exact not_not.1 h1
      · omega
    obtain ⟨hz₁, hz₂⟩ := streamWorld_monitorCall prims D t ht w z hz
    have hk := h.2 z.1
    simp only [not_not.2 ht, ↓reduceIte] at hk
    obtain ⟨hy₁, hy₂⟩ := ih z.1 hk z.2 y hy
    exact ⟨hy₁.trans hz₁, hz₂.trans hy₂⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation with only calls of the monitor keeps the provenance of the hidden keys. -/
theorem keepsProvenance_of_monitorOnly (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : NoCall (fun t => ¬ MonitorCall t) oa) : KeepsProvenance prims D oa := by
  intro world hworld r hr
  obtain ⟨hhidden, hle⟩ := simulateQ_monitorCall prims D oa h world r hr
  intro name key ρ idx position hname hcell
  rw [hhidden] at hcell
  obtain ⟨kind, parts, hderive⟩ := hworld name key ρ idx position hname hcell
  exact ⟨kind, parts, hle hderive⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The monitor keeps the provenance of the hidden keys. -/
theorem monitorProvenance : MonitorProvenance prims (C := C) := fun D keys tree outputs =>
  keepsProvenance_of_monitorOnly prims D _
    (GameCount.wrongOutput_noCall D (fun t => ¬ MonitorCall t) (fun _ ht h => h ht) keys tree outputs)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyCounters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyCounters

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.zeroCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.zeroCheck

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.monitorProvenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.monitorProvenance
