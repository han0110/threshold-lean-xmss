import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.PassCeremony

/-!
# The wrong outputs of the recorded runs of a tree

`passGhostBatch` states that in one ceremony with the record of a pass (`passGhost`), a recorded batch
of an honest operator with a result that is not right for a good `h` has a pass, a positive tuple
count, and a wrong tuple or split copies when each honest operator recorded its start. It reads the
ghost run of `ghostCeremony` with the same law by `passGhost_erase`, and `ceremonyBatchFor`.
`passGhost_started` gives each start from one honest output.

* `passWrongTop` is the top tree of `PassWrongCheck` on `streamWorld`. The path of the whole program
  with `H` fixed to `h` gives a recorded batch that is not right (`topTail_fix`, `condR_recRun`), and
  the phase split at the end of the ceremony gives the ghost run of the ceremony with the same
  records.
* `passBottom_fix` is the path of one operator in a run of a bottom tree with `H` fixed. A wrong output
  has a recorded batch that is not right, in the first or in the second ceremony.
* `passBottom_cut` splits a real recorded run of a bottom tree at the end of its head. It gives the
  ghost run of the first ceremony, the phase of the heads, and the phase of the rests from the head
  results. Each honest operator ends the run (`passDone`), so its record is the head record and
  then the rest record.
* `PassBottomBatch` is the joint part of a bottom tree. `passBottomHead` proves it for a batch of the
  first ceremony, and `passBottomBatch_of_rest` proves it from `PassBottomRest`, its case of the
  second ceremony.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.RecordedOpening ThresholdLeanXmssSecurity.DkgCorrectnessProof.GhostSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A batch with no output wire is right for each `h`. -/
theorem rightAt_of_noOutputs (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (b : BatchStart C)
    (opened : ℕ → Bit) (hcirc : b.circuits = b.jobs.map (circuits b.parameter ·.kind))
    (hzero : (outputsOf b.circuits).length = 0) :
    GhostMonitor.RightAt circuits prims h seeds b (ThresholdLeanXmssSecurity.assemble b.circuits opened) := by
  have hnil : ∀ c ∈ b.circuits, c.outputs = [] := by
    intro c hc
    have h0 : outputsOf b.circuits = [] := List.eq_nil_of_length_eq_zero hzero
    unfold outputsOf at h0
    rw [List.flatMap_eq_nil_iff] at h0
    obtain ⟨k, hk⟩ := List.mem_iff_getElem.1 hc
    have := h0 (c, k) (by rw [List.mem_zipIdx_iff_getElem?]; simp [← hk.2, List.getElem?_eq_getElem hk.1])
    simpa using this
  unfold GhostMonitor.RightAt RightBatch ThresholdLeanXmssSecurity.assemble
  rw [Option.some.injEq]
  refine List.ext_getElem (by simp [hcirc]) fun m h₁ h₂ => ?_
  simp only [List.length_map] at h₂
  have hm : m < b.circuits.length := by rw [hcirc, List.length_map]; exact h₂
  have hc : (circuits b.parameter b.jobs[m].kind).outputs = [] :=
    hnil _ (by rw [hcirc]; exact List.mem_map.2 ⟨_, List.getElem_mem h₂, rfl⟩)
  simp only [List.getElem_map, List.getElem_zipIdx, D_evalJob, Circuit.eval, hc, List.map_nil]
  have hw : b.circuits[m].outputs.length = 0 := by
    rw [hnil _ (List.getElem_mem hm)]
    rfl
  simp only [hw]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- A batch with an output wire has a positive tuple count. -/
theorem count_ne_zero_of_outputs (b : BatchStart C) (h : (outputsOf b.circuits).length ≠ 0) :
    ((batchTuples K b.mode b.circuits b.inputs b.zs b.v').map (·.count)).sum ≠ 0 := by
  unfold batchTuples
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- One ceremony with the record of a pass. A recorded batch `k` of an honest operator with a result,
whose output is not right for a good `h` that agrees with the clean end cache, with no global event,
has a pass and a positive tuple count, and it has a wrong tuple or split copies when each honest
operator recorded its start. -/
theorem passGhostBatch (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((passGhost prims K circuits settings D net rounds c).run world)) (hglobal : ¬ GlobalEvent ω.2)
    (i : C.Party) (hi : i ∉ D.1) (hiout : (ω.1.2 i).output.isSome) (k : ℕ) (b : BatchStart C) (out : List (List Bit))
    (hb : (startsOf (ceremonyRecord ω.1.2 i))[k]? = some b) (hout : (batchOutputsOf (ceremonyRecord ω.1.2 i))[k]? = some out)
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h (MpcCells.cleanCache ω.2.1))
    (hnr : ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D c.keys) b out) :
    k < (openingsOf (ceremonyRecord ω.1.2 i)).length ∧
      ((batchTuples K b.mode b.circuits b.inputs b.zs b.v').map (·.count)).sum ≠ 0 ∧
      (StartedAt D k ω.1.2 →
        WrongTuple D (ceremonyTuplesAt K k ω.1.2) ∨ ¬ MultVerifyAgree D (honestTuples D (ceremonyTuplesAt K k ω.1.2))) := by
  obtain ⟨ω', hω', hw, hstarts, houts, houtput⟩ := passGhost_erase prims K circuits settings D net rounds c world ω hω
  have hiout' : (ω'.1.2 i).output.isSome := by rw [houtput i]; exact hiout
  have ha' : Agrees h (MpcCells.cleanCache ω'.2.1) := by rw [hw]; exact ha
  have hb' : (startsOf (ceremonyRecord ω'.1.2 i))[k]? = some b := by rw [hstarts i]; exact hb
  have hout' : (batchOutputsOf (ceremonyRecord ω'.1.2 i))[k]? = some out := by rw [houts i hi]; exact hout
  obtain ⟨keys, hk', hjobs, hshape⟩ := ceremony_start prims K circuits settings D net rounds c world ω' hω' i hi k b hb'
  have hk : k < (chunks settings.batchSize c.jobs).length := (List.getElem?_eq_some_iff.1 hjobs).1
  obtain ⟨keys2, inbox, hk2, -, -, hblock⟩ := ceremony_block prims K circuits settings (ghostOnPath prims) D net rounds
    c world ω' hω' i hi hiout' k b out hb' hout'
  have hcount : ((batchTuples K b.mode b.circuits b.inputs b.zs b.v').map (·.count)).sum ≠ 0 := by
    refine count_ne_zero_of_outputs K b fun hzero => hnr ?_
    have hout := (hblock h hg ha').2.2
    simp only at hout
    rw [hout]
    refine rightAt_of_noOutputs prims circuits h _ b _ ?_ hzero
    rw [hshape.2.2.1, hshape.2.1]
  have hω1 := mem_support_phase prims D _ world ω hω
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hiout
  have hdone : (ω.1.2 i).isDone := by
    rcases hs : ω.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at ho
    · trivial
    · cases ho
    · cases ho
  have hmem := Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) rounds c.adversary _ ω.1 hω1 i hi
    hdone
  have hrc := (recordCount_passCeremony K circuits settings i c _ hmem).2 (by rw [ho]; rfl)
  refine ⟨?_, hcount, fun hst => ?_⟩
  · change k < (openingsOf ((ω.1.2 i).record [])).length
    rw [hrc.2]
    exact hk
  · have htuples : ceremonyTuplesAt K k ω'.1.2 = ceremonyTuplesAt K k ω.1.2 := by
      funext l
      unfold ceremonyTuplesAt
      rw [hstarts l]
    have hst' : StartedAt D k ω'.1.2 := fun l hl => by rw [hstarts l]; exact hst l hl
    have hglobal' : ¬ GlobalEvent ω'.2 := by rw [hw]; exact hglobal
    have := ceremonyBatchFor prims K circuits settings (ghostOnPath prims) D net rounds c world hseeds ω' hω' hglobal' k hk i hi
      hiout' b out hb' hout' h hg ha' hnr hst'
    rwa [htuples] at this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The local tail of the top tree with `H` fixed to `h` gives the top tree of its opened outputs,
computed in the clear. -/
theorem topTail_fix (h : Query C → HashOutput) (operator : OperatorState C) (o : CeremonyResult) (keys : Keys C)
    (hk : operator.keys = some keys) (t : TreeOutput)
    (ht : some t ∈ support (simulateQ (fixHash h) (topTail (E := E) operator o).run)) :
    some t = ceremonyOutput (m := Id) (fun oa => D prims h (tweakable oa)) keys.parameter (fun _ => some o.1)
      emptyTop .top := by
  unfold topTail at ht
  rw [hk] at ht
  simp only [ceremonyOutput, pure_bind, StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
    map_bind, bind_assoc] at ht
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, fixHash_oracleStep_tweakable prims h] at ht
  simp only [pure_bind, Option.elim, map_pure, OptionT.run_pure] at ht
  simp only [simulateQ_pure,
    support_pure, Set.mem_singleton_iff] at ht
  rw [ht]
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem agrees_cleanCache {h : Query C → HashOutput} {c : HashCache C} (ha : Agrees h c) :
    Agrees h (MpcCells.cleanCache c) := fun q v hq => by
  by_cases hm : MpcCells.MpcCell q
  · simp [MpcCells.cleanCache, hm] at hq
  · rw [MpcCells.cleanCache_of_not hm] at hq
    exact ha q v hq

/-- One ceremony with the record of a pass, with `H` fixed to `h`. Its record has one batch output for
each start, and its result is the right result on `seeds`, or it has a recorded batch that is not
right. -/
theorem passCeremony_fix (hsize : 0 < settings.batchSize) (h : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C) (hk : c.keys i = some keys)
    (z : Option CeremonyResult × Record C E)
    (hz : z ∈ support (simulateQ (fixHash h) (passCeremony K circuits settings i c).run.run)) (oc : CeremonyResult)
    (hoc : z.1 = some oc) :
    GhostMonitor.Balanced z.2 ∧
      ((∃ k : ℕ, ∃ b out, (startsOf z.2)[k]? = some b ∧ (batchOutputsOf z.2)[k]? = some out ∧
        ¬ GhostMonitor.RightAt circuits prims h seeds b out) ∨
        some oc.1 = evalRun prims circuits keys.parameter seeds h c.jobs) := by
  have hz' : Prod.map id filterOpened z ∈ support (simulateQ (fixHash h)
      (Prod.map id filterOpened <$> (recCeremony K circuits settings i c).run.run)) := by
    rw [← passCeremony_records, simulateQ_map, support_map]
    exact ⟨z, hz, rfl⟩
  rw [simulateQ_map, support_map] at hz'
  obtain ⟨z', hz'', hzeq⟩ := hz'
  simp only [Prod.map, Prod.mk.injEq, id] at hzeq
  obtain ⟨hz1, hz2⟩ := hzeq
  rcases recCeremony_fix_support K circuits settings h i c z' hz'' with hnil | ⟨keys', hk', z₃, h₃, hrec₃, hres⟩
  · rw [hnil, hoc] at hz1
    cases hz1
  obtain rfl : keys = keys' := Option.some.inj (hk.symm.trans hk')
  have hzo : z'.1 = some oc := by rw [hz1, hoc]
  have hz₃ := hres oc hzo
  have hstarts : startsOf z.2 = startsOf z₃.2 := by rw [← startsOf_filterOpened, ← hz2, startsOf_filterOpened, hrec₃]
  have houts : batchOutputsOf z.2 = batchOutputsOf z₃.2 := by
    rw [← batchOutputsOf_filterOpened, ← hz2, batchOutputsOf_filterOpened, hrec₃]
  have hbal := GhostMonitor.balR_recRun K circuits settings i keys c.jobs c.counters z₃
    (GhostMonitor.support_fixHash_subset _ _ h₃) (some oc.1) oc.2 hz₃
  refine ⟨by unfold GhostMonitor.Balanced at hbal ⊢; rw [hstarts, houts]; exact hbal, ?_⟩
  have hcond := GhostMonitor.condR_recRun K circuits settings prims h seeds hsize i keys c.jobs c.counters z₃ h₃
    (some oc.1) oc.2 hz₃
  by_cases hall : ∃ k : ℕ, ∃ b out, (startsOf z.2)[k]? = some b ∧ (batchOutputsOf z.2)[k]? = some out ∧
      ¬ GhostMonitor.RightAt circuits prims h seeds b out
  · exact Or.inl hall
  push Not at hall
  exact Or.inr (hcond fun k _ b out hb hout => hall k b out (by rw [hstarts]; exact hb) (by rw [houts]; exact hout)).2



/-- The top tree of `PassWrongCheck` on `streamWorld`. A wrong output of an honest operator in a real
recorded run of the top tree, for a good `h` that agrees with the end cache, with no global event,
gives a bad check in the records of the run. -/
theorem passWrongTop (hsize : 0 < settings.batchSize) (hc : CircuitsCompute circuits prims.Th) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (s : RealState C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D (fun i => (s.operators i).keys) = false)
    (r : (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) .top).run.run)).run world))
    (hglobal : ¬ GlobalEvent r.2) (i : C.Party) (hi : i ∉ D.1) (o : TreeOutput) (ho : (r.1.2 i).output = some o)
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h r.2.1)
    (hwrong : some o ≠ ThresholdLeanXmssSecurity.D prims h (referenceTree tweakable
      (prfValue (gameSeeds D fun i => (s.operators i).keys))
      (gameParameter D fun i => (s.operators i).keys) emptyTop .top)) :
    PassBad K D fun j => (r.1.2 j).record [] := by
  obtain ⟨parameter, hpar⟩ := exists_parameter D s hseeds
  have hfuel := topFuel circuits settings parameter
  obtain ⟨a, ha'⟩ : ∃ a, CheckTiming.ceremonyRounds circuits settings parameter topJobs = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, treeFuel circuits settings = a + b := ⟨treeFuel circuits settings - a, by omega⟩
  have hj : (topStart (σ := net.State) s).jobs = topJobs := by simp only [topStart]
  have htimed : ∀ i ∉ D.1, TimedR a (passCeremony K circuits settings i (topStart s)).run.run := fun i hi => by
    have h := timedR_passCeremony K circuits settings i (topStart s) parameter (hpar i hi)
    rwa [hj, ha'] at h
  have hprog : (fun i => (passTree K circuits settings plainShares none i (s.operators i) .top).run.run) =
      fun i => (passCeremony K circuits settings i (topStart s)).run.run >>=
        recCont (fun o => RecM.lift (topTail (s.operators i) o)) :=
    funext fun i => by rw [passTree_top, run_recBind]
  -- the path of the whole program with `H` fixed to `h`
  have hstep : r.1.2 i = .done (some o) ((r.1.2 i).record []) := by
    rcases hs : r.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at ho
    · cases ho
      rfl
    · cases ho
    · cases ho
  have hpath := onPath_done (hstep ▸ ghostOnPath prims D D net ([] : Record C E) (treeFuel circuits settings)
    s.adversary _ world r hr h hg ha i hi)
  rw [passTree_top] at hpath
  obtain ⟨z₁, h₁, hcase⟩ := GhostMonitor.mem_support_fix_bind h _ _ _ hpath
  rcases hcase with ⟨-, heq⟩ | ⟨oc, hoc, z₂, h₂, heq⟩
  · simp at heq
  rw [run_recLift, simulateQ_map, support_map] at h₂
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  simp only [Prod.mk.injEq, List.append_nil] at heq
  obtain ⟨hyo, hrec⟩ := heq
  have hkeys_i : ∃ keys, (s.operators i).keys = some keys := by
    rcases hk : (s.operators i).keys with _ | keys
    · exfalso
      unfold topTail at hy₂
      rw [hk] at hy₂
      rw [← hyo] at hy₂
      simp [OptionT.run_failure] at hy₂
    · exact ⟨keys, rfl⟩
  obtain ⟨keysI, hkI⟩ := hkeys_i
  have htail := topTail_fix prims h (s.operators i) oc keysI hkI o (by rw [hyo]; exact hy₂)
  -- a recorded batch that is not right
  have hpar' : keysI.parameter = gameParameter D fun i => (s.operators i).keys :=
    parameter_eq_gameParameter D _ hseeds i hi keysI hkI
  obtain ⟨-, hcase⟩ := passCeremony_fix prims K circuits settings hsize h (gameSeeds D (topStart s).keys) i
    (topStart s) keysI hkI z₁ h₁ oc hoc
  obtain ⟨k, bb, out, hb₃, hout₃, hnr⟩ := hcase.resolve_right fun hright => by
    apply hwrong
    simp only [topStart] at hright
    rw [hpar'] at hright
    rw [htail, ← ceremonyAt_eq_referenceTree prims circuits hc hg]
    unfold ceremonyAt
    simp only [ceremonyOutput]
    rw [← hright, hpar']
  -- the phase of the ceremony and the phase of the local tails
  rw [hprog, hb] at hr
  have hw := executePhaseR_bind_world D net noFunctionality ([] : Record C E)
    (fun i => recCont (fun o => RecM.lift (topTail (s.operators i) o))) (WorldSplit.streamWorld_freeCommute prims D)
    (fun _ _ => rfl) a b s.adversary _ htimed world
  rw [support_eq_of_evalDistEq hw, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hzr⟩ := hr
  have hy1 := mem_support_phase prims D _ world y hy
  obtain ⟨hD, -⟩ := executePhaseR_timed_shape D net noFunctionality ([] : Record C E) a s.adversary _ htimed y.1 hy1
  have hr1 := mem_support_phase prims D _ y.2 r hzr
  obtain ⟨-, hrecs⟩ := executePhaseR_localTail D net noFunctionality ([] : Record C E) b y.1.1 y.1.2 _
    (fun i => localTail_recCont_lift _ (timed_topTail (s.operators i))) hD r.1 hr1
  have hle : y.2.1 ≤ r.2.1 := streamWorld_run_mono prims D _ y.2 r hzr
  have hdone : (r.1.2 i).isDone := by rw [hstep]; trivial
  have hmem := Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) b y.1.1 _ r.1 hr1 i hi hdone
  have hiout : (y.1.2 i).output.isSome := by
    rcases hyo' : (y.1.2 i).output with _ | oy
    · rw [hyo'] at hmem
      simp only [recCont, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [ho] at hmem
      cases hmem.1
    · rfl
  have hrecY : ceremonyRecord y.1.2 i = z₁.2 := (hrecs i).symm.trans hrec
  have hglobalY : ¬ GlobalEvent y.2 := fun hy' => hglobal (globalEvent_mono hle hy')
  have haY : Agrees h (MpcCells.cleanCache y.2.1) := agrees_cleanCache fun q v hq => ha q v (hle hq)
  have hyG : y ∈ support ((passGhost prims K circuits settings D net a (topStart s)).run world) := hy
  obtain ⟨hopen, hcount, himp⟩ := passGhostBatch prims K circuits settings D net a (topStart s) world hseeds y hyG
    hglobalY i hi hiout k bb out (by rw [hrecY]; exact hb₃) (by rw [hrecY]; exact hout₃) h hg haY hnr
  have hrecsR : ∀ j, (r.1.2 j).record [] = ceremonyRecord y.1.2 j := hrecs
  obtain ⟨-, -, hjobsK, -⟩ := passGhost_start prims K circuits settings D net a (topStart s) world y hyG i hi k bb
    (by rw [hrecY]; exact hb₃)
  have hst := passGhost_started prims K circuits settings D net a (topStart s) world hseeds y hyG i hi hiout k
    (List.getElem?_eq_some_iff.1 hjobsK).1
  have htuples : (passTuples K k fun j => (r.1.2 j).record []) = ceremonyTuplesAt K k y.1.2 := by
    funext l
    unfold passTuples ceremonyTuplesAt
    dsimp only
    rw [hrecsR l]
  refine ⟨k, fun l hl => by dsimp only; rw [hrecsR l]; exact hst l hl, by rw [htuples]; exact himp hst, i, hi, ?_⟩
  dsimp only
  rw [hrecsR i]
  exact hopen

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The local search of a bottom tree with `H` fixed to `h` is the search computed in the clear. -/
theorem headTail_fix (h : Query C → HashOutput) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (o : CeremonyResult) (keys : Keys C) (hk : operator.keys = some keys) (x : HeadResult)
    (hx : some x ∈ support (simulateQ (fixHash h) (headTail (E := E) operator b o).run)) :
    firstLocal (m := Id) (fun oa => D prims h (tweakable oa)) keys.parameter b o.1 = some x.1 ∧ x.2 = o.2 := by
  unfold headTail at hx
  rw [hk] at hx
  simp only [firstLocal, StateT.run_bind, StateT.run_lift, bind_assoc] at hx
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, fixHash_oracleStep_tweakable prims h] at hx
  simp only [pure_bind, Option.elim] at hx
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, fixHash_oracleStep_tweakable prims h] at hx
  simp only [pure_bind, Option.elim] at hx
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, fixHash_oracleStep_tweakable prims h] at hx
  simp only [pure_bind, Option.elim] at hx
  split at hx
  · rename_i randomness encoding hgr
    simp only [StateT.run_pure, OptionT.run_pure, simulateQ_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    subst hx
    refine ⟨?_, rfl⟩
    simp only [firstLocal, bind]
    rw [hgr]
    rfl
  · simp only [StateT.run_pure, simulateQ_pure, pure_bind,
      OptionT.run_failure, support_pure, Set.mem_singleton_iff] at hx
    cases hx


omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The local end of a bottom tree with `H` fixed to `h` is the end computed in the clear. -/
theorem secondTail_fix (h : Query C → HashOutput) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) (o : CeremonyResult) (keys : Keys C) (top : TopTree)
    (hk : operator.keys = some keys) (ht : operator.top = some top) (t : TreeOutput)
    (htt : some t ∈ support (simulateQ (fixHash h) (secondTail (E := E) operator b x o).run)) :
    secondLocal (m := Id) (fun oa => D prims h (tweakable oa)) keys.parameter top b x o.1 = some t := by
  unfold secondTail at htt
  rw [hk, ht] at htt
  simp only [secondLocal, StateT.run'_eq, StateT.run_bind, StateT.run_lift, map_bind, bind_assoc] at htt
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, fixHash_oracleStep_tweakable prims h] at htt
  simp only [pure_bind, Option.elim] at htt
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, fixHash_oracleStep_tweakable prims h] at htt
  simp only [pure_bind, Option.elim] at htt
  simp only [secondLocal, bind]
  split_ifs at htt ⊢ with hroot
  · simp only [StateT.run_pure, map_pure, simulateQ_pure,
      pure_bind, OptionT.run_failure, support_pure, Set.mem_singleton_iff] at htt
    cases htt
  · simp only [StateT.run_pure, map_pure, OptionT.run_pure, simulateQ_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at htt
    rw [htt]
    rfl


omit [Fintype E] [DecidableEq E] in
/-- The recorded head of a bottom tree with `H` fixed is one recorded ceremony with `H` fixed and the
local search computed in the clear. -/
theorem passHead_fix (h : Query C → HashOutput) (i : C.Party) {σ : Type} (s : RealState C σ)
    (b : Fin (2 ^ layerHeight)) (keys : Keys C) (hk : (s.operators i).keys = some keys) (x : HeadResult)
    (rec : Record C E)
    (hpath : (some x, rec) ∈ support (simulateQ (fixHash h) (passHead K circuits settings i s b).run.run)) :
    ∃ z ∈ support (simulateQ (fixHash h) (passCeremony K circuits settings i (firstStart b s)).run.run),
      ∃ oc, z.1 = some oc ∧ rec = z.2 ∧
        firstLocal (m := Id) (fun oa => D prims h (tweakable oa)) keys.parameter b oc.1 = some x.1 ∧ x.2 = oc.2 := by
  unfold passHead at hpath
  obtain ⟨z₃, h₃, hcase₃⟩ := GhostMonitor.mem_support_fix_bind h _ _ _ hpath
  rcases hcase₃ with ⟨-, heq₃⟩ | ⟨oc₁, hoc₁, z₄, h₄, heq₃⟩
  · simp at heq₃
  rw [run_recLift, simulateQ_map, support_map] at h₄
  obtain ⟨y₄, hy₄, rfl⟩ := h₄
  simp only [Prod.mk.injEq, List.append_nil] at heq₃
  obtain ⟨hx, hrec⟩ := heq₃
  rw [← hx] at hy₄
  obtain ⟨hfirst, hx2⟩ := headTail_fix prims h (s.operators i) b oc₁ keys hk x hy₄
  exact ⟨z₃, h₃, oc₁, hoc₁, hrec, hfirst, hx2⟩

/-- The path of one operator in a real recorded run of a bottom tree, with `H` fixed to a good `h`. A
wrong output on `seeds` has a recorded batch that is not right. -/
theorem passBottom_fix (hsize : 0 < settings.batchSize) (hc : CircuitsCompute circuits prims.Th)
    (h : Query C → HashOutput) (hg : Good prims h) (seeds : C.Term → HashOutput) (i : C.Party) {σ : Type}
    (s : RealState C σ) (b : Fin (2 ^ layerHeight)) (keys : Keys C) (top : TopTree)
    (hk : (s.operators i).keys = some keys) (ht : (s.operators i).top = some top) (o : TreeOutput) (rec : Record C E)
    (hpath : (some o, rec) ∈ support (simulateQ (fixHash h)
      (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run))
    (hwrong : some o ≠ D prims h (referenceTree tweakable (prfValue seeds) keys.parameter top (.bottom b))) :
    ∃ k : ℕ, ∃ b' out, (startsOf rec)[k]? = some b' ∧ (batchOutputsOf rec)[k]? = some out ∧
      ¬ GhostMonitor.RightAt circuits prims h seeds b' out := by
  have halive : aliveKeys s i = some keys := by simp [aliveKeys, hk, ht]
  rw [passTree_bottom] at hpath
  obtain ⟨z₁, h₁, hcase⟩ := GhostMonitor.mem_support_fix_bind h _ _ _ hpath
  rcases hcase with ⟨-, heq⟩ | ⟨xh, hxh, z₂, h₂, heq⟩
  · simp at heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hz₂o, hrec⟩ := heq
  -- the head
  obtain ⟨z₃, h₃, oc₁, hoc₁, hz₁, hfirst, -⟩ := passHead_fix prims K circuits settings h i s b keys hk xh z₁.2
    (by rw [← hxh]; exact h₁)
  obtain ⟨hbal₁, hcase₁⟩ := passCeremony_fix prims K circuits settings hsize h seeds i (firstStart b s) keys halive
    z₃ h₃ oc₁ hoc₁
  -- the rest
  unfold passRest at h₂
  obtain ⟨z₅, h₅, hcase₅⟩ := GhostMonitor.mem_support_fix_bind h _ _ _ h₂
  rcases hcase₅ with ⟨-, heq₅⟩ | ⟨oc₂, hoc₂, z₆, h₆, heq₅⟩
  · rw [heq₅] at hz₂o
    cases hz₂o
  rw [run_recLift, simulateQ_map, support_map] at h₆
  obtain ⟨y₆, hy₆, rfl⟩ := h₆
  rw [heq₅] at hz₂o
  simp only at hz₂o
  rw [← hz₂o] at hy₆
  have hsecond := secondTail_fix prims h (s.operators i) b xh.1 oc₂ keys top hk ht o hy₆
  have hz₂ : z₂.2 = z₅.2 := by rw [heq₅]; simp
  obtain ⟨-, hcase₂⟩ := passCeremony_fix prims K circuits settings hsize h seeds i (secondStart b s s.adversary xh) keys
    halive z₅ h₅ oc₂ hoc₂
  have hrec' : rec = z₃.2 ++ z₅.2 := by rw [hrec, hz₁, hz₂]
  rcases hcase₁ with ⟨k, b', out, hb', hout', hnr⟩ | hright₁
  · refine ⟨k, b', out, ?_, ?_, hnr⟩
    · rw [hrec', startsOf_append, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hb').1]
      exact hb'
    · rw [hrec', GhostMonitor.batchOutputsOf_append, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hout').1]
      exact hout'
  rcases hcase₂ with ⟨k, b', out, hb', hout', hnr⟩ | hright₂
  · refine ⟨(startsOf z₃.2).length + k, b', out, ?_, ?_, hnr⟩
    · rw [hrec', startsOf_append, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact hb'
    · rw [hrec', GhostMonitor.batchOutputsOf_append, hbal₁, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact hout'
  exfalso
  apply hwrong
  rw [← ceremonyAt_eq_referenceTree prims circuits hc hg]
  unfold ceremonyAt
  rw [ceremonyOutput_bottom_split]
  simp only [firstStart, secondStart] at hright₁ hright₂
  simp only [bind, ← hright₁, Option.elim, hfirst, ← hright₂, hsecond]


/-- The joint part of a real recorded run of a bottom tree. A recorded batch of an honest operator with
an output, whose output is not right for a good `h` that agrees with the end cache, with no global
event, gives a bad check in the records of the run. The bad check can be at another batch than the
batch that is not right, because a bad check of the first ceremony can split the head results of the
honest operators. -/
def PassBottomBatch : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) (s : RealState C net.State)
    (world : StreamState C), seedsDiffer D (fun i => (s.operators i).keys) = false →
    ∀ r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
          (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run)).run world),
      ¬ GlobalEvent r.2 → ∀ i, i ∉ D.1 → (r.1.2 i).output.isSome → ∀ h, Good prims h → Agrees h r.2.1 →
      ∀ (n : ℕ) (b₀ : BatchStart C) (out : List (List Bit)), (startsOf ((r.1.2 i).record []))[n]? = some b₀ →
        (batchOutputsOf ((r.1.2 i).record []))[n]? = some out →
        ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D fun i => (s.operators i).keys) b₀ out →
        PassBad K D fun j => (r.1.2 j).record []


omit [Fintype E] [DecidableEq E] in
/-- The recorded program of a bottom tree starts with the exchange of the PRSS setup, so it aborts on
an abort frame with no record. -/
theorem abortsOnAbort_passTreeBottom (i : C.Party) {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    AbortsOnAbort ([] : Record C E)
      (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run := by
  rw [passTree_bottom]
  unfold passHead passCeremony
  simp -implicitDefEqProofs only [firstStart]
  rcases aliveKeys s i with _ | keys
  · rw [failure_bind, failure_bind]
    exact abortsOnAbort_pure _
  · unfold passRun
    simp -implicitDefEqProofs only [StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift, recM_lift_bind,
      bind_assoc]
    exact abortsOnAbort_lift_bind _ (startsWithRound_prssSetup i) _

omit [Fintype E] [DecidableEq E] in
/-- In a real recorded run of a bottom tree where an honest operator recorded a start, each honest
operator holds keys and a top tree. -/
theorem passBottom_alive (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C)
    (r : (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run)).run world))
    (i : C.Party) (hi : i ∉ D.1) (n : ℕ) (b₀ : BatchStart C)
    (hb₀ : (startsOf ((r.1.2 i).record []))[n]? = some b₀) :
    ∀ j, j ∉ D.1 → aliveKeys s j = (s.operators j).keys := by
  by_contra hnot
  push Not at hnot
  obtain ⟨j₀, hj₀, hne⟩ := hnot
  have hdead : (passTree K circuits settings plainShares none j₀ (s.operators j₀) (.bottom b)).run.run =
      pure (none, []) := by
    rcases hk : (s.operators j₀).keys with _ | k
    · unfold passTree
      rw [hk]
      rfl
    rcases ht : (s.operators j₀).top with _ | t
    · unfold passTree
      rw [hk, ht]
      rfl
    exfalso
    apply hne
    simp [aliveKeys, hk, ht]
  have hrec := executePhaseR_dead D net noFunctionality ([] : Record C E) (treeFuel circuits settings) s.adversary _
    (fun _ => []) j₀ hj₀ hdead (fun j _ => abortsOnAbort_passTreeBottom K circuits settings j s b) r.1
    (mem_support_phase prims D _ world r hr) i hi
  have hnil : (r.1.2 i).record [] = [] := by rcases hrec with h | h <;> exact h
  rw [hnil] at hb₀
  simp [startsOf] at hb₀


/-- In the ghost run of one ceremony with the record of a pass, an honest operator with a result has
one batch output for each batch of the job list. -/
theorem passGhost_outputs (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((passGhost prims K circuits settings D net rounds c).run world)) (i : C.Party) (hi : i ∉ D.1)
    (o : CeremonyResult) (ho : (ω.1.2 i).output = some o) :
    (batchOutputsOf (ceremonyRecord ω.1.2 i)).length = (chunks settings.batchSize c.jobs).length := by
  obtain ⟨ω', hω', -, -, houts, houtput⟩ := passGhost_erase prims K circuits settings D net rounds c world ω hω
  have ho' : (ω'.1.2 i).output = some o := by rw [houtput i]; exact ho
  rw [← houts i hi]
  exact (ceremony_value prims K circuits settings D net rounds c world ω' hω' i hi o ho').2.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A bad check reads only the tuples of the honest operators. -/
theorem badCheck_congr (D : C.Coalition) {x x' : C.Party → List (Tuple C)} (h : ∀ i, i ∉ D.1 → x i = x' i) :
    (WrongTuple D x ∨ ¬ MultVerifyAgree D (honestTuples D x)) ↔
      (WrongTuple D x' ∨ ¬ MultVerifyAgree D (honestTuples D x')) := by
  have e := honestView_congr D h
  have e' : honestTuples D x = honestTuples D x' := e
  unfold WrongTuple
  rw [e, e']


omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem mapStep_record_of_isDone {α ρ : Type} (f : ρ → ρ) (blank : ρ) (step : RStep C E RealSpec α ρ)
    (h : (mapStep f step).isDone) : (mapStep f step).record blank = f (step.record blank) := by
  cases step with
  | done out record => rfl
  | wait outbox resume => exact (h : False).elim
  | call input resume => exact (h : False).elim

/-- The recorded rest of a bottom tree at an operator from its head result, or no program. -/
def restAt {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) (x : Option HeadResult) (j : C.Party) :
    OracleComp (PartySpec C E RealSpec) (Option TreeOutput × Record C E) :=
  match x with
  | some x => (passRest K circuits settings j s b x).run.run
  | none => pure (none, [])

/-- The cut of a real recorded run of a bottom tree at the end of its head. -/
theorem passBottom_cut (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (hseeds : seedsDiffer D (fun i => (s.operators i).keys) = false)
    (r : (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run)).run world)) :
    ∃ (P : PublicParameter) (m : ℕ) (y₀ : (net.State × CeremonySteps C E) × StreamState C)
      (y : (net.State × (C.Party → RStep C E RealSpec HeadResult (Record C E))) × StreamState C)
      (r₀ : (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) × StreamState C),
      (∀ j, j ∉ D.1 → ∀ keys, aliveKeys s j = some keys → keys.parameter = P) ∧
      treeFuel circuits settings = CheckTiming.ceremonyRounds circuits settings P (bottomJobs b) + m ∧
      y₀ ∈ support ((passGhost prims K circuits settings D net
        (CheckTiming.ceremonyRounds circuits settings P (bottomJobs b)) (firstStart b s)).run world) ∧
      y ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        ([] : Record C E) (CheckTiming.ceremonyRounds circuits settings P (bottomJobs b)) s.adversary fun j =>
          (passHead K circuits settings j s b).run.run)).run world) ∧
      (∀ j, (y.1.2 j).record [] = ceremonyRecord y₀.1.2 j) ∧
      (∀ j, j ∉ D.1 → (y.1.2 j).isDone) ∧
      (∀ j, j ∉ D.1 → (y.1.2 j).output.isSome → (y₀.1.2 j).output.isSome) ∧
      r₀ ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        ([] : Record C E) m y.1.1 fun j => restAt K circuits settings s b (y.1.2 j).output j)).run y.2) ∧
      y₀.2.1 ≤ y.2.1 ∧ y.2.1 ≤ r.2.1 ∧ r.2 = r₀.2 ∧
      (∀ j, j ∉ D.1 → (r.1.2 j).output = (r₀.1.2 j).output ∧
        (r.1.2 j).record [] = (y.1.2 j).record [] ++ (r₀.1.2 j).record [] ∧ (r₀.1.2 j).isDone) := by
  have hdoneR := passDone prims K circuits settings D net plainShares none s.operators (.bottom b) s.adversary world
    (Or.inl rfl) hseeds r hr
  have hkeys : seedsDiffer D (aliveKeys s) = false := seedsDiffer_sub D _ _ (aliveKeys_some s) hseeds
  obtain ⟨P, hP⟩ : ∃ P, gameParameter D (aliveKeys s) = P := ⟨_, rfl⟩
  have hpar : ∀ j, j ∉ D.1 → ∀ keys, aliveKeys s j = some keys → keys.parameter = P :=
    fun j hj keys hk => hP ▸ parameter_eq_gameParameter D _ hkeys j hj keys hk
  obtain ⟨nr, hnr'⟩ : ∃ n, CheckTiming.ceremonyRounds circuits settings P (bottomJobs b) = n := ⟨_, rfl⟩
  have hfuel := bottomFuel circuits settings P b fun _ => digit 0
  rw [hnr'] at hfuel
  have hnle : nr ≤ treeFuel circuits settings := by omega
  obtain ⟨m, hm⟩ : ∃ m, treeFuel circuits settings = nr + m := ⟨_, (Nat.add_sub_cancel' hnle).symm⟩
  have htimed₁ : ∀ j ∉ D.1, TimedR nr (passHead K circuits settings j s b).run.run := fun j hj =>
    hnr' ▸ timedR_passHead K circuits settings j s b P (hpar j hj)
  have hprog : (fun j => (passTree K circuits settings plainShares none j (s.operators j) (.bottom b)).run.run) =
      fun j => (passHead K circuits settings j s b).run.run >>= recCont (passRest K circuits settings j s b) :=
    funext fun j => by rw [passTree_bottom, run_recBind]
  rw [hprog, hm] at hr
  have hsplit := executePhaseR_bind_world D net noFunctionality ([] : Record C E)
    (fun j => recCont (passRest K circuits settings j s b)) (WorldSplit.streamWorld_freeCommute prims D)
    (fun _ _ => rfl) nr m s.adversary _ htimed₁ world
  rw [support_eq_of_evalDistEq hsplit, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hzr⟩ := hr
  have hj₁ : (firstStart (σ := net.State) b s).jobs = bottomJobs b := by simp only [firstStart]
  have htimedC : ∀ j ∉ D.1, TimedR nr (passCeremony K circuits settings j (firstStart b s)).run.run := fun j hj => by
    have h1 := timedR_passCeremony K circuits settings j (firstStart b s) P (hpar j hj)
    rwa [hj₁, hnr'] at h1
  have hheadprog : (fun j => (passHead K circuits settings j s b).run.run) = fun j =>
      (passCeremony K circuits settings j (firstStart b s)).run.run >>=
        recCont (fun o => RecM.lift (headTail (s.operators j) b o)) :=
    funext fun j => passHead_run K circuits settings j s b
  have hy' := hy
  rw [hheadprog, ← Nat.add_zero nr] at hy'
  have hsplit₂ := executePhaseR_bind_world D net noFunctionality ([] : Record C E)
    (fun j => recCont (fun o => RecM.lift (headTail (s.operators j) b o))) (WorldSplit.streamWorld_freeCommute prims D)
    (fun _ _ => rfl) nr 0 s.adversary _ htimedC world
  rw [support_eq_of_evalDistEq hsplit₂, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy'
  obtain ⟨y₀, hy₀, hyy⟩ := hy'
  have hy₀1 := mem_support_phase prims D _ world y₀ hy₀
  obtain ⟨hD₀, -⟩ := executePhaseR_timed_shape D net noFunctionality ([] : Record C E) nr s.adversary _ htimedC y₀.1
    hy₀1
  have hyy1 := mem_support_phase prims D _ y₀.2 y hyy
  obtain ⟨-, hrecy⟩ := executePhaseR_localTail D net noFunctionality ([] : Record C E) 0 y₀.1.1 y₀.1.2 _
    (fun j => localTail_recCont_lift _ (timed_headTail (s.operators j) b)) hD₀ y.1 hyy1
  have hy1 := mem_support_phase prims D _ world y hy
  obtain ⟨-, hd⟩ := executePhaseR_timed_shape D net noFunctionality ([] : Record C E) nr s.adversary _ htimed₁ y.1 hy1
  have hR : ∀ j, j ∉ D.1 → recCont (passRest K circuits settings j s b) ((y.1.2 j).output, (y.1.2 j).record []) =
      (fun q => (q.1, (y.1.2 j).record [] ++ q.2)) <$> restAt K circuits settings s b (y.1.2 j).output j :=
    fun j _ => by
      rcases ho : (y.1.2 j).output with _ | x
      · simp only [restAt, recCont, map_pure, List.append_nil]
      · simp only [restAt, recCont]
  rw [executePhaseR_mapSteps D net noFunctionality ([] : Record C E) (fun j => ((y.1.2 j).record [] ++ ·)) m y.1.1
    _ _ hR, simulateQ_map, StateT.run_map, support_map] at hzr
  obtain ⟨r₀, hr₀, hreq⟩ := hzr
  refine ⟨P, m, y₀, y, r₀, hpar, by rw [hnr', hm], by rw [hnr']; exact hy₀, by rw [hnr']; exact hy, hrecy, hd,
    fun j hj hsome => ?_, hr₀, streamWorld_run_mono prims D _ y₀.2 y hyy, ?_, by rw [← hreq], fun j hj => ⟨?_, ?_, ?_⟩⟩
  · have hmem := Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) 0 y₀.1.1 _ y.1 hyy1 j hj (hd j hj)
    rcases ho0 : (y₀.1.2 j).output with _ | o0
    · rw [ho0] at hmem
      simp only [recCont, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [hmem.1] at hsome
      cases hsome
    · rfl
  · rw [← hreq]
    exact streamWorld_run_mono prims D _ y.2 r₀ hr₀
  · rw [← hreq]
    exact mapSteps_output D (fun j => ((y.1.2 j).record [] ++ ·)) r₀.1.2 j
  · have hmj : mapSteps D (fun j => ((y.1.2 j).record [] ++ ·)) r₀.1.2 j = mapStep ((y.1.2 j).record [] ++ ·) (r₀.1.2 j) :=
      ite_eq_right hj
    have hdj := hdoneR j hj
    rw [← hreq] at hdj ⊢
    dsimp only at hdj ⊢
    rw [hmj] at hdj ⊢
    exact mapStep_record_of_isDone _ [] (r₀.1.2 j) hdj
  · have hmj : mapSteps D (fun j => ((y.1.2 j).record [] ++ ·)) r₀.1.2 j = mapStep ((y.1.2 j).record [] ++ ·) (r₀.1.2 j) :=
      ite_eq_right hj
    have hdj := hdoneR j hj
    rw [← hreq] at hdj
    dsimp only at hdj
    rw [hmj] at hdj
    cases hs : r₀.1.2 j with
    | done out record => trivial
    | wait outbox resume => rw [hs] at hdj; exact (hdj : False).elim
    | call input resume => rw [hs] at hdj; exact (hdj : False).elim

omit [Fintype E] [DecidableEq E] in
/-- After the cut of a real recorded run of a bottom tree at its head, a start of an honest operator
after the batches of the first ceremony gives a complete head with a result at each honest operator.
An honest operator with no head result stops each rest by `executePhaseR_dead`. -/
theorem passBottom_heads (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (nr m : ℕ)
    (y : (net.State × (C.Party → RStep C E RealSpec HeadResult (Record C E))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) nr s.adversary fun j => (passHead K circuits settings j s b).run.run)).run world))
    (hd : ∀ j, j ∉ D.1 → (y.1.2 j).isDone)
    (r₀ : (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) × StreamState C)
    (hr₀ : r₀ ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) m y.1.1 fun j => restAt K circuits settings s b (y.1.2 j).output j)).run y.2))
    (i : C.Party) (hi : i ∉ D.1) (n : ℕ) (b₀ : BatchStart C)
    (hb₀ : (startsOf ((y.1.2 i).record [] ++ (r₀.1.2 i).record []))[n]? = some b₀)
    (hn : (chunks settings.batchSize (bottomJobs b)).length ≤ n) :
    ∀ j, j ∉ D.1 → (y.1.2 j).output.isSome ∧
      (startsOf ((y.1.2 j).record [])).length = (chunks settings.batchSize (bottomJobs b)).length ∧
      (openingsOf ((y.1.2 j).record [])).length = (chunks settings.batchSize (bottomJobs b)).length := by
  have hhead : ∀ j, j ∉ D.1 →
      (startsOf ((y.1.2 j).record [])).length ≤ (chunks settings.batchSize (bottomJobs b)).length ∧
      ((y.1.2 j).output.isSome →
        (startsOf ((y.1.2 j).record [])).length = (chunks settings.batchSize (bottomJobs b)).length ∧
        (openingsOf ((y.1.2 j).record [])).length = (chunks settings.batchSize (bottomJobs b)).length) := fun j hj =>
    recordCount_passHead K circuits settings j s b _
      (Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) _ s.adversary _ y.1
        (mem_support_phase prims D _ world y hy) j hj (hd j hj))
  have hallx : ∀ j, j ∉ D.1 → (y.1.2 j).output.isSome := by
    by_contra hnot
    push Not at hnot
    obtain ⟨j₀, hj₀, hnone⟩ := hnot
    have hnone' : (y.1.2 j₀).output = none := by
      rcases hx : (y.1.2 j₀).output with _ | x
      · rfl
      · rw [hx] at hnone
        simp at hnone
    have hdead := executePhaseR_dead D net noFunctionality ([] : Record C E) m y.1.1
      (fun j => restAt K circuits settings s b (y.1.2 j).output j) (fun _ => []) j₀ hj₀
      (by simp only [restAt, hnone']) (fun j _ => by
        rcases (y.1.2 j).output with _ | x
        · exact abortsOnAbort_pure _
        · exact abortsOnAbort_passRest K circuits settings j s b x)
      r₀.1 (mem_support_phase prims D _ y.2 r₀ hr₀) i hi
    have hnil : (r₀.1.2 i).record [] = [] := by rcases hdead with h | h <;> exact h
    rw [hnil, List.append_nil, List.getElem?_eq_none (by have := (hhead i hi).1; omega)] at hb₀
    cases hb₀
  exact fun j hj => ⟨hallx j hj, (hhead j hj).2 (hallx j hj)⟩

/-- The head of the joint part of a bottom tree. A recorded batch below the batches of the first
ceremony that is not right gives a bad check in the records of the run. -/
theorem passBottomHead (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (hseeds : seedsDiffer D (fun i => (s.operators i).keys) = false)
    (r : (net.State × (C.Party → RStep C E RealSpec TreeOutput (Record C E))) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
      ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
        (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run)).run world))
    (hglobal : ¬ GlobalEvent r.2) (i : C.Party) (hi : i ∉ D.1) (hiout : (r.1.2 i).output.isSome)
    (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h r.2.1) (n : ℕ) (b₀ : BatchStart C)
    (out : List (List Bit)) (hb₀ : (startsOf ((r.1.2 i).record []))[n]? = some b₀)
    (hout₀ : (batchOutputsOf ((r.1.2 i).record []))[n]? = some out)
    (hnr : ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D fun i => (s.operators i).keys) b₀ out)
    (hn : n < (chunks settings.batchSize (bottomJobs b)).length) :
    PassBad K D fun j => (r.1.2 j).record [] := by
  have halive := passBottom_alive prims K circuits settings D net b s world r hr i hi n b₀ hb₀
  have hkeys : seedsDiffer D (aliveKeys s) = false := seedsDiffer_sub D _ _ (aliveKeys_some s) hseeds
  have hseedsEq : gameSeeds D (aliveKeys s) = gameSeeds D fun i => (s.operators i).keys := gameSeeds_congr D halive
  obtain ⟨P, m, y₀, y, r₀, -, -, hy₀, hy, hrecy, hd, hy₀out, hr₀, hle₁, hle₂, -, hrr⟩ :=
    passBottom_cut prims K circuits settings D net b s world hseeds r hr
  have hj₁ : (firstStart (σ := net.State) b s).jobs = bottomJobs b := rfl
  have hreci := (hrr i hi).2.1
  -- the head of `i` has a result
  have hyi : (y.1.2 i).output.isSome := by
    have hro : (r₀.1.2 i).output.isSome := by rw [← (hrr i hi).1]; exact hiout
    have hdone : (r₀.1.2 i).isDone := by
      rcases hs : r₀.1.2 i with ⟨o, rec⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hro
      · trivial
      · cases hro
      · cases hro
    have hmem := Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) m y.1.1 _ r₀.1
      (mem_support_phase prims D _ y.2 r₀ hr₀) i hi hdone
    rcases hoi : (y.1.2 i).output with _ | xi
    · rw [hoi] at hmem
      simp only [restAt, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [hmem.1] at hro
      cases hro
    · rfl
  have hy₀i := hy₀out i hi hyi
  obtain ⟨o0, ho0⟩ := Option.isSome_iff_exists.1 hy₀i
  have hcnt := passGhost_outputs prims K circuits settings D net _ (firstStart b s) world y₀ hy₀ i hi o0 ho0
  rw [hj₁] at hcnt
  have hst := passGhost_started prims K circuits settings D net _ (firstStart b s) world hkeys y₀ hy₀ i hi hy₀i n hn
  have hstartsJ : ∀ j, j ∉ D.1 →
      (startsOf ((r.1.2 j).record []))[n]? = (startsOf (ceremonyRecord y₀.1.2 j))[n]? := by
    intro j hj
    have hlt : n < (startsOf (ceremonyRecord y₀.1.2 j)).length := by
      obtain ⟨bj, hbj⟩ := Option.isSome_iff_exists.1 (hst j hj)
      exact (List.getElem?_eq_some_iff.1 hbj).1
    rw [(hrr j hj).2.1, GhostMonitor.startsOf_append, hrecy j, List.getElem?_append_left hlt]
  have hb₀' : (startsOf (ceremonyRecord y₀.1.2 i))[n]? = some b₀ := by rw [← hstartsJ i hi]; exact hb₀
  have hout₀' : (batchOutputsOf (ceremonyRecord y₀.1.2 i))[n]? = some out := by
    rw [← hout₀, hreci, GhostMonitor.batchOutputsOf_append, hrecy i, List.getElem?_append_left (by rw [hcnt]; exact hn)]
  have hle : y₀.2.1 ≤ r.2.1 := le_trans hle₁ hle₂
  have hglobal₀ : ¬ GlobalEvent y₀.2 := fun hg' => hglobal (globalEvent_mono hle hg')
  have ha₀ : Agrees h (MpcCells.cleanCache y₀.2.1) := agrees_cleanCache fun q v hq => ha q v (hle hq)
  have hnr' : ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D (firstStart (σ := net.State) b s).keys) b₀ out := by
    simp only [firstStart]
    rw [hseedsEq]
    exact hnr
  obtain ⟨hopen, -, himp⟩ := passGhostBatch prims K circuits settings D net _ (firstStart b s) world hkeys y₀ hy₀
    hglobal₀ i hi hy₀i n b₀ out hb₀' hout₀' h hg ha₀ hnr'
  refine ⟨n, fun j hj => by rw [hstartsJ j hj]; exact hst j hj, ?_, i, hi, ?_⟩
  · refine (badCheck_congr D fun j hj => ?_).2 (himp hst)
    unfold passTuples ceremonyTuplesAt
    dsimp only
    rw [hstartsJ j hj]
  · dsimp only
    rw [hreci, openingsOf_append, List.length_append, hrecy i]
    omega

/-- The rest of the joint part of a bottom tree. `PassBottomBatch` for a recorded batch at or after the
batches of the first ceremony, in the second ceremony. -/
def PassBottomRest : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) (s : RealState C net.State)
    (world : StreamState C), seedsDiffer D (fun i => (s.operators i).keys) = false →
    ∀ r ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        ([] : Record C E) (treeFuel circuits settings) s.adversary fun i =>
          (passTree K circuits settings plainShares none i (s.operators i) (.bottom b)).run.run)).run world),
      ¬ GlobalEvent r.2 → ∀ i, i ∉ D.1 → (r.1.2 i).output.isSome → ∀ h, Good prims h → Agrees h r.2.1 →
      ∀ (n : ℕ) (b₀ : BatchStart C) (out : List (List Bit)), (startsOf ((r.1.2 i).record []))[n]? = some b₀ →
        (batchOutputsOf ((r.1.2 i).record []))[n]? = some out →
        ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D fun i => (s.operators i).keys) b₀ out →
        (chunks settings.batchSize (bottomJobs b)).length ≤ n →
        PassBad K D fun j => (r.1.2 j).record []

/-- `PassBottomBatch` from its rest, with `passBottomHead` for a batch of the first ceremony. -/
theorem passBottomBatch_of_rest (rest : PassBottomRest prims K circuits settings) :
    PassBottomBatch prims K circuits settings := by
  intro D net b s world hseeds r hr hglobal i hi hiout h hg ha n b₀ out hb₀ hout₀ hnr
  by_cases hn : n < (chunks settings.batchSize (bottomJobs b)).length
  · exact passBottomHead prims K circuits settings D net b s world hseeds r hr hglobal i hi hiout h hg ha n b₀ out hb₀
      hout₀ hnr hn
  · exact rest D net b s world hseeds r hr hglobal i hi hiout h hg ha n b₀ out hb₀ hout₀ hnr (by omega)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passGhostBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passGhostBatch

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passWrongTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passWrongTop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passBottomBatch_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passBottomBatch_of_rest
