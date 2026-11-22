import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.PassTree

/-!
# The second ceremony of the recorded runs of a bottom tree

* `passBottomRest` proves `PassBottomRest`. An honest operator with no head result stops each rest by
  `executePhaseR_dead`. A first batch that is not right at an honest operator gives its check by
  `passGhostBatch`. Otherwise the honest head results agree, and the rest is the ghost run of one
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
theorem mapSteps_id {α ρ : Type} (D : C.Coalition) (steps : C.Party → RStep C E RealSpec α ρ) :
    mapSteps D (fun _ => id) steps = steps := by
  funext l
  unfold mapSteps
  split_ifs
  · rfl
  · cases steps l <;> simp [mapStep]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase reads only the programs of the honest operators. -/
theorem executePhaseR_honest_congr {Ia L R α ρ : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty PEmpty L R) (blank : ρ) (fuel : ℕ) (st : A.State)
    (prog prog' : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (h : ∀ i, i ∉ D.1 → prog' i = prog i) :
    executePhaseR worldRoles D A F blank fuel st prog' = executePhaseR worldRoles D A F blank fuel st prog := by
  rw [executePhaseR_mapSteps D A F blank (fun _ => id) fuel st prog prog' fun i hi => by rw [h i hi]; simp]
  simp only [mapSteps_id]
  simp

omit [DecidableEq E] in
/-- One recorded ceremony with `H` fixed has the end counters of the job list in its result. -/
theorem passCeremony_fix_counters (h : Query C → HashOutput) (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (keys : Keys C) (hk : c.keys i = some keys) (z : Option CeremonyResult × Record C E)
    (hz : z ∈ support (simulateQ (fixHash h) (passCeremony K circuits settings i c).run.run)) (oc : CeremonyResult)
    (hoc : z.1 = some oc) : oc.2 = endCounters circuits settings keys.parameter c.counters c.jobs := by
  have hz' := GhostMonitor.support_fixHash_subset h _ hz
  refine ceremonyProgram_counters K circuits settings i c keys hk oc ?_
  rw [← dropRec_passCeremony K circuits settings i c]
  change some oc ∈ support (Prod.fst <$> (passCeremony K circuits settings i c).run.run)
  rw [support_map]
  exact ⟨z, hz', hoc⟩

/-- `PassBottomRest` for a positive batch size. -/
theorem passBottomRest (hsize : 0 < settings.batchSize) : PassBottomRest prims K circuits settings := by
  intro D net b s world hseeds r hr hglobal i hi hiout h hg ha n b₀ out hb₀ hout₀ hnr hn
  have halive := passBottom_alive prims K circuits settings D net b s world r hr i hi n b₀ hb₀
  have hkeys : seedsDiffer D (aliveKeys s) = false := seedsDiffer_sub D _ _ (aliveKeys_some s) hseeds
  have hseedsEq : gameSeeds D (aliveKeys s) = gameSeeds D fun i => (s.operators i).keys := gameSeeds_congr D halive
  obtain ⟨P, m, y₀, y, r₀, hpar, hm, hy₀, hy, hrecy, hd, hy₀out, hr₀, hle₁, hle₂, hw, hrr⟩ :=
    passBottom_cut prims K circuits settings D net b s world hseeds r hr
  have hj₁ : (firstStart (σ := net.State) b s).jobs = bottomJobs b := rfl
  have hreci := (hrr i hi).2.1
  have hheads := passBottom_heads prims K circuits settings D net b s world _ m y hy hd r₀ hr₀ i hi n b₀
    (by rw [← hreci]; exact hb₀) hn
  have hallx : ∀ j, j ∉ D.1 → (y.1.2 j).output.isSome := fun j hj => (hheads j hj).1
  have hhead : ∀ j, j ∉ D.1 →
      (startsOf ((y.1.2 j).record [])).length ≤ (chunks settings.batchSize (bottomJobs b)).length ∧
      ((y.1.2 j).output.isSome →
        (startsOf ((y.1.2 j).record [])).length = (chunks settings.batchSize (bottomJobs b)).length ∧
        (openingsOf ((y.1.2 j).record [])).length = (chunks settings.batchSize (bottomJobs b)).length) :=
    fun j hj => ⟨(hheads j hj).2.1.le, fun _ => (hheads j hj).2⟩
  -- the path of each honest head with `H` fixed to `h`
  have hay : Agrees h y.2.1 := fun q v hq => ha q v (hle₂ hq)
  have hpathJ : ∀ j, j ∉ D.1 → ∃ x, (y.1.2 j).output = some x ∧ ∃ keys, aliveKeys s j = some keys ∧
      ∃ z ∈ support (simulateQ (fixHash h) (passCeremony K circuits settings j (firstStart b s)).run.run),
        ∃ oc, z.1 = some oc ∧ (y.1.2 j).record [] = z.2 ∧
          firstLocal (m := Id) (fun oa => ThresholdLeanXmssSecurity.D prims h (tweakable oa)) keys.parameter b oc.1 =
            some x.1 ∧ x.2 = oc.2 := by
    intro j hj
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hallx j hj)
    have hstep : y.1.2 j = .done (some x) ((y.1.2 j).record []) := by
      rcases hs : y.1.2 j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hx
      · cases hx
        rfl
      · cases hx
      · cases hx
    have hpath := onPath_done (hstep ▸ ghostOnPath prims D D net ([] : Record C E) _ s.adversary _ world y hy h hg hay
      j hj)
    rcases hk : aliveKeys s j with _ | keys
    · exfalso
      simp [passHead, passCeremony, firstStart, hk, OptionT.run_failure] at hpath
    obtain ⟨z, hz, oc, hoc, hrec, hfirst, hx2⟩ := passHead_fix prims K circuits settings h j s b keys
      (aliveKeys_some s j keys hk) x _ hpath
    exact ⟨x, hx, keys, rfl, z, hz, oc, hoc, hrec, hfirst, hx2⟩
  by_cases hA : ∃ j, j ∉ D.1 ∧ ∃ (k : ℕ) (b' : BatchStart C) (out' : List (List Bit)), (startsOf ((y.1.2 j).record []))[k]? = some b' ∧
      (batchOutputsOf ((y.1.2 j).record []))[k]? = some out' ∧
      ¬ GhostMonitor.RightAt circuits prims h (gameSeeds D (aliveKeys s)) b' out'
  · -- a first batch that is not right gives its check
    obtain ⟨j, hj, k, b', out', hb', hout', hnr'⟩ := hA
    have hglobal₀ : ¬ GlobalEvent y₀.2 := fun hg' => hglobal (globalEvent_mono (le_trans hle₁ hle₂) hg')
    have ha₀ : Agrees h (MpcCells.cleanCache y₀.2.1) :=
      agrees_cleanCache fun q v hq => ha q v (le_trans hle₁ hle₂ hq)
    have hb'' : (startsOf (ceremonyRecord y₀.1.2 j))[k]? = some b' := by rw [← hrecy j]; exact hb'
    have hout'' : (batchOutputsOf (ceremonyRecord y₀.1.2 j))[k]? = some out' := by rw [← hrecy j]; exact hout'
    have hjout := hy₀out j hj (hallx j hj)
    obtain ⟨-, -, himp⟩ := passGhostBatch prims K circuits settings D net _ (firstStart b s) world hkeys y₀ hy₀
      hglobal₀ j hj hjout k b' out' hb'' hout'' h hg ha₀ hnr'
    have hkL : k < (chunks settings.batchSize (bottomJobs b)).length := by
      have h1 := (List.getElem?_eq_some_iff.1 hb').1
      have h2 := (hhead j hj).1
      omega
    have hst := passGhost_started prims K circuits settings D net _ (firstStart b s) world hkeys y₀ hy₀ j hj hjout k hkL
    have hstartsK : ∀ l, l ∉ D.1 →
        (startsOf ((r.1.2 l).record []))[k]? = (startsOf (ceremonyRecord y₀.1.2 l))[k]? := by
      intro l hl
      rw [(hrr l hl).2.1, GhostMonitor.startsOf_append, hrecy l,
        List.getElem?_append_left (by rw [← hrecy l, ((hhead l hl).2 (hallx l hl)).1]; exact hkL)]
    have hheadi := (hhead i hi).2 (hallx i hi)
    refine ⟨k, fun l hl => by rw [hstartsK l hl]; exact hst l hl, ?_, i, hi, ?_⟩
    · refine (badCheck_congr D fun l hl => ?_).2 (himp hst)
      unfold passTuples ceremonyTuplesAt
      dsimp only
      rw [hstartsK l hl]
    · dsimp only
      rw [hreci, openingsOf_append, List.length_append, hheadi.2]
      omega
  · -- each honest first batch is right, so the honest head results agree
    push Not at hA
    have hres : ∀ j, j ∉ D.1 → ∀ keys z oc, aliveKeys s j = some keys →
        z ∈ support (simulateQ (fixHash h) (passCeremony K circuits settings j (firstStart b s)).run.run) →
        z.1 = some oc → (y.1.2 j).record [] = z.2 →
        some oc.1 = evalRun prims circuits P (gameSeeds D (aliveKeys s)) h (bottomJobs b) ∧
          oc.2 = endCounters circuits settings P (0, 0) (bottomJobs b) := by
      intro j hj keys z oc hk hz hoc hrec
      obtain ⟨-, hcase⟩ := passCeremony_fix prims K circuits settings hsize h (gameSeeds D (aliveKeys s)) j
        (firstStart b s) keys hk z hz oc hoc
      rcases hcase with ⟨k, b', out', hb', hout', hnr'⟩ | hright
      · exact absurd (hA j hj k b' out' (by rw [hrec]; exact hb') (by rw [hrec]; exact hout')) hnr'
      · refine ⟨by rw [hright, hpar j hj keys hk]; rfl, ?_⟩
        rw [passCeremony_fix_counters K circuits settings h j (firstStart b s) keys hk z hz oc hoc, hpar j hj keys hk]
        rfl
    obtain ⟨xi, hxi, keysI, hkI, zi, hzi, oci, hoci, hreci', hfirsti, hx2i⟩ := hpathJ i hi
    have hsame : ∀ j, j ∉ D.1 → (y.1.2 j).output = some xi := by
      intro j hj
      obtain ⟨x, hx, keys, hk, z, hz, oc, hoc, hrec, hfirst, hx2⟩ := hpathJ j hj
      obtain ⟨h1, h2⟩ := hres j hj keys z oc hk hz hoc hrec
      obtain ⟨h1i, h2i⟩ := hres i hi keysI zi oci hkI hzi hoci hreci'
      have e1 : oc.1 = oci.1 := Option.some.inj (h1.trans h1i.symm)
      rw [hx]
      refine congrArg some (Prod.ext (Option.some.inj ?_) (by rw [hx2, hx2i, h2, h2i]))
      rw [← hfirst, ← hfirsti, hpar j hj keys hk, hpar i hi keysI hkI, e1]
    -- the rest is the ghost run of one second ceremony
    have hfuel := bottomFuel circuits settings P b xi.1.2.2.2
    obtain ⟨m₂, hm₂⟩ : ∃ m₂, m = CheckTiming.ceremonyRounds circuits settings P (signJobs b xi.1.2.2.2) + m₂ :=
      ⟨m - CheckTiming.ceremonyRounds circuits settings P (signJobs b xi.1.2.2.2), by omega⟩
    have htimed₂ : ∀ j ∉ D.1, TimedR (CheckTiming.ceremonyRounds circuits settings P (signJobs b xi.1.2.2.2))
        (passCeremony K circuits settings j (secondStart b s y.1.1 xi)).run.run := fun j hj =>
      timedR_passCeremony K circuits settings j (secondStart b s y.1.1 xi) P (hpar j hj)
    have hprog₂ : ∀ j, j ∉ D.1 → restAt K circuits settings s b (y.1.2 j).output j =
        (passCeremony K circuits settings j (secondStart b s y.1.1 xi)).run.run >>=
          recCont (fun o => RecM.lift (secondTail (s.operators j) b xi.1 o)) := fun j hj => by
      rw [hsame j hj]
      exact passRest_run K circuits settings j s b y.1.1 xi
    rw [executePhaseR_honest_congr D net noFunctionality ([] : Record C E) m y.1.1 _ _ hprog₂, hm₂] at hr₀
    have hsplit := executePhaseR_bind_world D net noFunctionality ([] : Record C E)
      (fun j => recCont (fun o => RecM.lift (secondTail (s.operators j) b xi.1 o)))
      (WorldSplit.streamWorld_freeCommute prims D) (fun _ _ => rfl) _ m₂ y.1.1 _ htimed₂ y.2
    rw [support_eq_of_evalDistEq hsplit, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr₀
    obtain ⟨y₂, hy₂, hr₂⟩ := hr₀
    have hy₂1 := mem_support_phase prims D _ y.2 y₂ hy₂
    obtain ⟨hD₂, -⟩ := executePhaseR_timed_shape D net noFunctionality ([] : Record C E) _ y.1.1 _ htimed₂ y₂.1 hy₂1
    have hr₂1 := mem_support_phase prims D _ y₂.2 r₀ hr₂
    obtain ⟨-, hrec₂⟩ := executePhaseR_localTail D net noFunctionality ([] : Record C E) m₂ y₂.1.1 y₂.1.2 _
      (fun j => localTail_recCont_lift _ (timed_secondTail (s.operators j) b xi.1)) hD₂ r₀.1 hr₂1
    have hy₂G : y₂ ∈ support ((passGhost prims K circuits settings D net
        (CheckTiming.ceremonyRounds circuits settings P (signJobs b xi.1.2.2.2)) (secondStart b s y.1.1 xi)).run y.2) :=
      hy₂
    have hle₃ : y₂.2.1 ≤ r.2.1 := by
      rw [hw]
      exact streamWorld_run_mono prims D _ y₂.2 r₀ hr₂
    have hy₂i : (y₂.1.2 i).output.isSome := by
      have hro : (r₀.1.2 i).output.isSome := by rw [← (hrr i hi).1]; exact hiout
      have hdone : (r₀.1.2 i).isDone := by
        rcases hs : r₀.1.2 i with ⟨o, rec⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hro
        · trivial
        · cases hro
        · cases hro
      have hmem := Joint.executePhaseR_out_mem D net noFunctionality ([] : Record C E) m₂ y₂.1.1 _ r₀.1 hr₂1 i hi hdone
      rcases ho2 : (y₂.1.2 i).output with _ | o2
      · rw [ho2] at hmem
        simp only [recCont, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1] at hro
        cases hro
      · rfl
    have hL := (hhead i hi).2 (hallx i hi)
    obtain ⟨o0, ho0⟩ := Option.isSome_iff_exists.1 (hy₀out i hi (hallx i hi))
    have hcnt := passGhost_outputs prims K circuits settings D net _ (firstStart b s) world y₀ hy₀ i hi o0 ho0
    rw [hj₁] at hcnt
    have hb₂ : (startsOf (ceremonyRecord y₂.1.2 i))[n - (chunks settings.batchSize (bottomJobs b)).length]? =
        some b₀ := by
      have e := hb₀
      rw [hreci, GhostMonitor.startsOf_append, List.getElem?_append_right (by rw [hL.1]; exact hn), hL.1, hrec₂ i] at e
      exact e
    have hout₂ : (batchOutputsOf (ceremonyRecord y₂.1.2 i))[n - (chunks settings.batchSize (bottomJobs b)).length]? =
        some out := by
      have e := hout₀
      rw [hreci, GhostMonitor.batchOutputsOf_append, List.getElem?_append_right (by rw [hrecy i, hcnt]; exact hn),
        hrecy i, hcnt, hrec₂ i] at e
      exact e
    obtain ⟨hopen, -, himp⟩ := passGhostBatch prims K circuits settings D net _ (secondStart b s y.1.1 xi) y.2
      hkeys y₂ hy₂G (fun hg' => hglobal (globalEvent_mono hle₃ hg')) i hi hy₂i _ b₀ out hb₂ hout₂ h hg
      (agrees_cleanCache fun q v hq => ha q v (hle₃ hq)) (by rw [← hseedsEq] at hnr; exact hnr)
    obtain ⟨-, -, hjobs₂, -⟩ := passGhost_start prims K circuits settings D net _ (secondStart b s y.1.1 xi) y.2 y₂ hy₂G
      i hi _ b₀ hb₂
    have hst := passGhost_started prims K circuits settings D net _ (secondStart b s y.1.1 xi) y.2 hkeys y₂ hy₂G i hi
      hy₂i _ (List.getElem?_eq_some_iff.1 hjobs₂).1
    have hstartsN : ∀ l, l ∉ D.1 → (startsOf ((r.1.2 l).record []))[n]? =
        (startsOf (ceremonyRecord y₂.1.2 l))[n - (chunks settings.batchSize (bottomJobs b)).length]? := by
      intro l hl
      have hLl := ((hhead l hl).2 (hallx l hl)).1
      rw [(hrr l hl).2.1, GhostMonitor.startsOf_append, List.getElem?_append_right (by rw [hLl]; exact hn), hLl, hrec₂ l]
      rfl
    have hopen' : (openingsOf ((r₀.1.2 i).record [])).length = (openingsOf (ceremonyRecord y₂.1.2 i)).length := by
      rw [hrec₂ i]
      rfl
    refine ⟨n, fun l hl => by rw [hstartsN l hl]; exact hst l hl, ?_, i, hi, ?_⟩
    · refine (badCheck_congr D fun l hl => ?_).2 (himp hst)
      unfold passTuples ceremonyTuplesAt
      dsimp only
      rw [hstartsN l hl]
    · dsimp only
      rw [hreci, openingsOf_append, List.length_append, hL.2, hopen']
      omega

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passBottomRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passBottomRest
