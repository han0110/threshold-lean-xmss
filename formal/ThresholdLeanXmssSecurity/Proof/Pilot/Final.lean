import ThresholdLeanXmssSecurity.Proof.BatchCheck.History
import ThresholdLeanXmssSecurity.Proof.Pilot.Split
import ThresholdLeanXmssSecurity.Proof.Pilot.TailErasure

/-!
# The assembly of the pilot

The rows of the pilot give `PilotSound` and `PilotCheck`. `splitAcceptEvidence` proves the trace facts
`SplitAcceptEvidence` of an accepted check. `pilotSound` and `pilotCheck` are the two theorems of the
pilot, with the join `pilotJoinOut`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

omit [Fintype E] [DecidableEq E] in
/-- With no tuple position, the honest copies agree. So split copies give a positive count. -/
theorem splitCopies_sum_ne_zero (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x)
    (hsplit : ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    counts.sum ≠ 0 := by
  intro hzero
  apply hsplit
  intro k hk T i _ j _ _ _ g hg
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
    tupleAt_count K hx k, List.getD_eq_getElem _ _ (by rw [firstInput_length K hx] at hk; exact hk)] at hg
  rw [firstInput_length K hx] at hk
  have hle := List.le_sum_of_mem (List.getElem_mem hk)
  omega

/-- A program with only calls of `PRG` keeps `SoundCache` and `DigestSaltsCovered`. The new covers
are not larger than the old covers. -/
theorem onlyStreams_keeps (prims : Primitives) {α : Type} {oa : OracleComp (LocalSpec C) α}
    (h : RealNetworkE1b.OnlyStreams oa) {L : ℕ} {cache : HashCache C} {seen : Finset (Query C)}
    {keys : Finset HashOutput} {salts : Finset (List Bit)} (hc : SoundCache L cache seen keys)
    (hs : DigestSaltsCovered cache salts) (p : α × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims) oa).run cache)) :
    (∃ seen' : Finset (Query C), SoundCache L p.2 seen' keys ∧ seen'.card ≤ seen.card) ∧
      ∃ salts' : Finset (List Bit), DigestSaltsCovered p.2 salts' ∧ salts'.card ≤ salts.card := by
  refine ⟨?_, ?_⟩
  · simpa using S9a.soundCache_local prims oa 0 h.fills L cache seen keys hc p hp
  · simpa using localProgram_digest_covered prims oa DigestQuery (fun t ht => ht) 0 h.digest cache salts hs p hp

/-- The adversary `A` with the input type `Ib`. It has the state, the rounds and the replies of `A`, and
its start ignores the inputs. -/
def withInput {Ia L R : Type} (A : Adversary C E Ia L R) (Ib : Type) : Adversary C E Ib L R where
  State := A.State
  start _ z := A.start (fun _ => none) z
  round := A.round
  answer := A.answer

variable [SampleableType E]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The rounds of a phase read only the state, the rounds and the replies of the adversary. -/
theorem executeRounds_withInput {Ia Ib L R I O α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
      executeRounds localRoles D (withInput A Ib) F fuel st steps = executeRounds localRoles D A F fuel st steps
  | 0, _, _ => rfl
  | fuel + 1, st, steps => by
    simp only [executeRounds]
    split_ifs
    · rfl
    · exact bind_congr fun (r : A.State × (C.Party → Step C E (CallSpec I O) α) × _) =>
        executeRounds_withInput D A F fuel r.1 r.2.1

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A phase reads only the state, the rounds and the replies of the adversary. -/
theorem executePhase_withInput {Ia Ib L R I O α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α) :
    executePhase localRoles D (withInput A Ib) F fuel st p = executePhase localRoles D A F fuel st p := by
  unfold executePhase
  exact bind_congr fun steps => executeRounds_withInput D A F fuel st steps

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A run that ends with a test `f` gives `true` with the probability of the event `f` on the run. -/
theorem prEvent_bool (prims : Primitives) {β : Type} (oa : OracleComp (LocalSpec C) β) (f : β → Bool)
    (c : HashCache C) :
    Pr{let b ← (simulateQ (localAnswer prims) (oa >>= fun r => pure (f r))).run' c}[b = true] =
      Pr{let r ← (simulateQ (localAnswer prims) oa).run' c}[f r = true] := by
  rw [show (oa >>= fun r => pure (f r)) = f <$> oa from (map_eq_bind_pure_comp _ _ _).symm]
  simp [simulateQ_map, StateT.run'_eq, StateT.run_map]

omit [SampleableType E] in
/-- Two honest holders of a hidden term have the same filled history. -/
theorem tupleInputs_hiddenHist (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x) :
    ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      filledHistory K i (x i) T = filledHistory K j (x j) T := by
  intro T hT i j hi hj hiT hjT
  have hz : ∀ (a b : List (Tuple C)) (T : C.Term),
      a.map (fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) =
        b.map (fun τ => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) →
      a.map (·.mode) = b.map (·.mode) →
      a.map (fun τ => (τ.mode, vector τ.count (τ.z T))) = b.map (fun τ => (τ.mode, vector τ.count (τ.z T))) := by
    intro a b T h1 h2
    have h3 := congrArg (List.map fun p => p.2.2) h1
    simp only [List.map_map, Function.comp_def] at h3
    exact map_pair_eq a b (·.mode) (fun τ => vector τ.count (τ.z T)) h2 h3
  have e : ∀ l, filledHistory K i l T = filledHistory K j l T := fun l => by
    unfold filledHistory; simp [hiT, hjT]
  rw [e]
  exact filledHistory_congr K j _ _ T
    (hz _ _ T (tupleInputs_unknown_vectors K hx T hT i hiT j hjT hi hj) (hx.2.1 i j hi hj))

omit [Fintype E] [DecidableEq E] in
/-- With a positive count, the check of each honest operator is `startProg` (`check_startProg`). -/
theorem checkAt_startProg (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (counts : List ℕ) (x : C.Party → List (Tuple C))
    (L tg : ℕ) (hx : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) (hpos : counts.sum ≠ 0) :
    executePhase localRoles D A (checkFunctionalities K) fuel st (RealNetworkV3.checkAt K L tg x) =
      executePhase localRoles D A (checkFunctionalities K) fuel st
        (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
          (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), L, tg⟩) := by
  refine executePhase_congr _ _ _ _ _ _ _ fun i hi => ?_
  unfold RealNetworkV3.checkAt
  rw [check_startProg K i (x i) (by rw [hx i hi]; exact hpos), hx i hi]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The error of the hybrid step of one check with no call after the check is at most `pilotDigestError`
with a larger cover of the salts. -/
theorem c1Error_le_pilotDigestError (C : Committee) (step salts saltsBound count : ℕ) (h : salts ≤ saltsBound) :
    RealNetworkV3.c1Error C step 0 salts count ≤ pilotDigestError C step saltsBound count := by
  unfold RealNetworkV3.c1Error pilotDigestError
  simp only [add_zero]
  gcongr

/-- The sound bound of the check on drawn values with the known rows `knownE` and `knownB`, from a cache
with the covers `seen` and `salts`. The steps are `c1Named` with the accept event as the test and no
call after the check, `accept_eq` to the wrapper with no tails, and `checkSoundFrom` with that wrapper
as the adversary. -/
theorem c1Real_sound (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (counts : List ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput) (salts : Finset (List Bit))
    (seenBound saltsBound : ℕ) (hx : TupleInputs K counts D x) (hwrong : WrongTuple D x)
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (hc : SoundCache L cache seen keys) (hs : DigestSaltsCovered cache salts)
    (hseen : seen.card ≤ seenBound) (hsalts : salts.card ≤ saltsBound) :
    (Pr{let out ← (simulateQ (localAnswer prims)
        (RealNetworkC1s.c1Real K D (RealNetworkE1r.checkAdversary net) knownE knownB counts L tg x st)).run'
          cache}[∃ i, i ∉ D.1 ∧ out.2 i = some ()]).toReal ≤
      pilotSoundError (E := E) C counts.sum step seenBound keys.card saltsBound := by
  have hpos := wrongTuple_sum_ne_zero K hx hwrong
  let W := withInput (RealNetworkE1r.checkAdversary net) (List (Tuple C))
  have hreal : RealNetworkC1s.c1Real K D (RealNetworkE1r.checkAdversary net) knownE knownB counts L tg x st =
      RealNetworkC1s.c1Real K D W knownE knownB counts L tg x st := by
    unfold RealNetworkC1s.c1Real
    exact bind_congr fun tables =>
      (executePhase_withInput (Ib := List (Tuple C)) D (RealNetworkE1r.checkAdversary net) _ _ st _).symm
  rw [hreal]
  have hTV := RealNetworkE1i.c1Named prims K D W knownE knownB step hstep counts L tg x st hx.1
    (tupleInputs_hiddenHist K hx) cache salts hs (fun r => pure (decide (∃ i, i ∉ D.1 ∧ r.2 i = some ()))) 0
    (fun _ => isQueryBoundP_pure _ _ _)
  have habs := (abs_prEvent_toReal_sub_le_measureTVDist _ _ (fun b : Bool => b = true)
    (measurable_from_top)).trans hTV
  rw [prEvent_bool, prEvent_bool] at habs
  simp only [decide_eq_true_eq] at habs
  have hacc := TailErasure.accept_eq prims K D W knownE knownB L tg counts x st hx.1 cache True
  simp only [and_true] at hacc
  rw [hacc] at habs
  have hsound := checkSoundFrom prims K counts D
    (TailErasure.c1Erased K D W knownE knownB (RealNetworkV3.knownHist K D x)) x step
    (seenBound + checkRounds counts.sum * step) L tg ((st, ⟨RealNetworkV3.knownHist K D x, []⟩), 0) cache seen
    keys hx (TailErasure.c1Erased_round_counted K D W knownE knownB _ step hstep)
    (TailErasure.c1Erased_answer_counted K D W knownE knownB _ step hstep) hc (by omega) hagree hwrong
  rw [← checkAt_startProg K D _ _ _ counts x L tg hx.1 hpos] at hsound
  have hnonneg := add_nonneg
    (checkErrorOf_nonneg K (coins counts.sum) (halvings counts.sum) (seenBound + checkRounds counts.sum * step))
    (soundHashError_nonneg counts.sum (seenBound + checkRounds counts.sum * step + keys.card))
  have herased := ((ENNReal.toReal_le_toReal (prEvent_ne_top _) ENNReal.ofReal_ne_top).mpr hsound).trans_eq
    (ENNReal.toReal_ofReal hnonneg)
  have hdig := c1Error_le_pilotDigestError C step salts.card saltsBound counts.sum hsalts
  have hgap := (abs_sub_le_iff.mp habs).1
  unfold pilotSoundError
  refine (sub_le_iff_le_add.mp hgap).trans ?_
  rw [add_comm]
  exact add_le_add herased hdig

/-- `PilotSound` from the join in its output form `PilotJoinOut`. `pilotAccept_drawn_out` moves the run
from `streamWorld` to the known rows and `c1Real`. The reads of the known rows have only calls of `PRG`, so the cache after them
keeps the covers. Then `c1Real_sound` gives the bound. -/
theorem pilotSound_of_join (prims : Primitives) (K : Constants C E) (hjoin : ∀ D, PilotJoinOut prims K D) :
    PilotSound prims K := by
  intro D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts split
    hx hwrong hcopies hagree hfresh hcache
  have hpos := wrongTuple_sum_ne_zero K hx hwrong
  rw [pilotAccept_drawn_out prims K D (hjoin D) net keys prss counts x L tg st cache hidden hpos hx.1 hagree hfresh]
  have hnonneg : 0 ≤ pilotSoundError (E := E) C counts.sum step seen.card expansionKeys.card salts.card :=
    add_nonneg (add_nonneg (checkErrorOf_nonneg K _ _ _) (soundHashError_nonneg _ _))
      (by unfold pilotDigestError; positivity)
  apply ENNReal.toReal_le_of_le_ofReal hnonneg
  unfold pilotDrawn
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  rintro ⟨knownE, c1⟩ h1
  obtain ⟨⟨seen1, hc1, hseen1⟩, ⟨salts1, hs1, hsalts1⟩⟩ := onlyStreams_keeps prims
    (RealNetworkE1e.knownRowsE_only K D _ _ _ L counts.sum) hcache.1 hcache.2.1 _ h1
  apply prEvent_bind_le_of_forall_le_of_support
  rintro ⟨knownB, c2⟩ h2
  obtain ⟨⟨seen2, hc2, hseen2⟩, ⟨salts2, hs2, hsalts2⟩⟩ := onlyStreams_keeps prims
    (RealNetworkE1e.knownRowsB_only (E := E) D _ _ _ L counts.sum) hc1 hs1 _ h2
  rw [← StateT.run'_eq]
  exact (ENNReal.le_ofReal_iff_toReal_le (prEvent_ne_top _) hnonneg).mpr
    (c1Real_sound prims K D net step hstep knownE knownB counts x L tg st c2 seen2 expansionKeys salts2
      seen.card salts.card hx hwrong hcopies hc2 hs2 (hseen2.trans hseen1) (hsalts2.trans hsalts1))

/-- `PilotCheck` from the join in its output form `PilotJoinOut` and the trace facts
`SplitAcceptEvidence`. -/
theorem pilotCheck_of_join (prims : Primitives) (K : Constants C E) (hjoin : ∀ D, PilotJoinOut prims K D)
    (he : SplitAcceptEvidence prims K) : PilotCheck prims K :=
  pilotCheck_of_cases prims K (pilotSound_of_join prims K hjoin) (pilotSplit_of_evidence prims K he)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

section Grows

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- A step of `streamWorld` only adds cells to the hash cache and to the cache of the hidden streams. -/
theorem streamWorld_step_le (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (z : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((streamWorld prims D t).run s)) : s ≤ z.2 := by
  by_cases ht : FreeHiddenStream D t
  · rcases t with ((u | q | x) | p) | (u | q | x) <;> simp only [FreeHiddenStream] at ht
    simp only [streamWorld, ht, ↓reduceIte, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact Prod.mk_le_mk.mpr ⟨le_rfl, QueryImpl.withCaching_cache_le _ _ _ _ hr⟩
  · rw [streamWorld_apply_of_not prims D t ht, onHash_run] at hz
    rw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact Prod.mk_le_mk.mpr ⟨grows_worldAnswer prims t s.1 r hr, le_rfl⟩

/-- A run in `streamWorld` only adds cells to the two caches. -/
theorem streamWorld_le {α : Type} (oa : OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run s), s ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact (streamWorld_step_le prims D t s p hp).trans (ih p.1 p.2 z hz)

end Grows

section Evidence

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E)

/-- The trace facts of an accepted rest phase. From each start state, each run of the rests in
`streamWorld` with an honest accept gives histories that extend `filledHistory`, the history and
digest cells of each honest digest in the end cache, and equal honest digests of each term. -/
def RestEvidence : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (keys : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (x : C.Party → List (Tuple C)) (st : net.State)
    (outs : C.Party → Option ((E × E × E × Shares C E × Shares C E) × RunState C))
    (s : HashCache C × HiddenCache C),
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality 6 st
      fun i => (outs i).elim failure (pilotRest K keys prss x i))).run s),
      (∃ i, i ∉ D.1 ∧ z.1.2 i = some ()) →
      ∃ (hist : C.Party → C.Term → List Bit) (ds : C.Party → List HashOutput),
        (∀ a, a ∉ D.1 → ∀ T, ∃ rest, hist a T = filledHistory K a (x a) T ++ rest) ∧
        (∀ a, a ∉ D.1 → ∀ T, KnownTo D.1 T → a ∈ C.holders T → ∃ salt hv d,
          z.2.1 (.history (hist a T)) = some hv ∧ z.2.1 (.digest salt hv) = some d ∧
          (ds a)[C.terms.idxOf T]? = some d) ∧
        ∀ T a b, a ∉ D.1 → b ∉ D.1 → a ∈ C.holders T → b ∈ C.holders T →
          (ds a)[C.terms.idxOf T]? = (ds b)[C.terms.idxOf T]?

omit [Fintype E] [DecidableEq E] in
/-- The trace facts of the rest phase give `SplitAcceptEvidence`. `pilotRun_split` cuts the run before
the salts, and the run of the rests from each end of the heads gives the facts. -/
theorem splitAcceptEvidence_of_rest (h : RestEvidence prims K) : SplitAcceptEvidence prims K := by
  intro D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts split
    hx hsplit hagree hfresh hcache z hz hacc
  rw [pilotRun_split K D net keys prss counts x L tg st (splitCopies_sum_ne_zero K hx hsplit) hx.1,
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, -, hz⟩ := hz
  exact h D net keys prss x p.1.1 p.1.2 p.2 z hz hacc

end Evidence

section Start

variable {C : Committee} {E : Type}

attribute [local instance] inhabitedField

/-- The draw of the salts and then `compareDigests`. The draw makes local calls, then the digests are
local calls, and then the operator waits in the digest round. After the round it aborts unless the
digests agree. -/
theorem advance_salts_compareDigests {α : Type} (ctx : Context C) (f : Unit → RunM C E RealSpec α)
    (st : RunState C) :
    ∃ pre : OracleComp (LocalSpec C) (Shares C Bit),
      advance ((prssRandomness ctx bitCodec 2 256 >>= fun salts => compareDigests ctx salts.1 >>= f).run' st).run =
        pre >>= fun salts => liftComp (digestQuery ctx.self salts st.history) (LocalSpec C) >>= fun ds =>
          pure (.wait (digestOutbox ctx.self ds) (exchangeResume fun inbox =>
            require (DigestsAgree (E := E) ctx.self ds inbox) >>= fun _ =>
              (f ()).run' { st with label := st.label + 1 })) := by
  refine ⟨liftComp (C.terms.mapM fun T => if ctx.self ∈ C.holders T then
      (bitCodec (E := E)).draw (.term T) (ctx.prss.term T) st.label 2 256 else pure fun _ => 0) (LocalSpec C) >>= fun r =>
    liftComp (C.parties.mapM fun j => if h : j = ctx.self then pure fun _ => 0
      else (bitCodec (E := E)).draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) st.label 2 256) (LocalSpec C) >>=
      fun _ => pure fun T => r.getD (C.terms.idxOf T) fun _ => 0, ?_⟩
  simp only [prssRandomness, freshLabel, compareDigests, StateT.run'_eq, StateT.run_bind, StateT.run_modifyGet,
    StateT.run_lift, StateT.run_get, bind_assoc, pure_bind, map_bind]
  simp only [advance_oracleStep_bind, advance_exchange_bind]
  rfl

/-- The rest of a check starts with the draw of the salts and `compareDigests`. -/
theorem checkRestOf_salts [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι} (K : Constants C E)
    (ctx : Context C) (bb : CheckBuildingBlocks C E G) (v : E × E × E × Shares C E × Shares C E) :
    ∃ f : Unit → RunM C E G Unit,
      RealNetworkC1s.checkRestOf K ctx bb v = bb.randBits 256 >>= fun salts => compareDigests ctx salts.1 >>= f := by
  unfold RealNetworkC1s.checkRestOf
  exact ⟨_, rfl⟩

/-- The rest of operator `i` in the pilot under its guard is the draw of the salts and then
`compareDigests`. -/
theorem advance_pilotRest [Field E] [Algebra Bit E] (K : Constants C E) (keys : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (x : C.Party → List (Tuple C)) (i : C.Party)
    (r : (E × E × E × Shares C E × Shares C E) × RunState C) (h : HistoryExtends (filledHistory K i (x i)) r.2) :
    ∃ (pre : OracleComp (LocalSpec C) (Shares C Bit)) (f : Unit → RunM C E RealSpec Unit),
      advance (pilotRest K keys prss x i r).run =
        pre >>= fun salts => liftComp (digestQuery i salts r.2.history) (LocalSpec C) >>= fun ds =>
          pure (.wait (digestOutbox i ds) (exchangeResume fun inbox =>
            require (DigestsAgree (E := E) i ds inbox) >>= fun _ =>
              (f ()).run' { r.2 with label := r.2.label + 1 })) := by
  obtain ⟨f, hf⟩ := checkRestOf_salts K (pilotContext keys prss i)
    (realCheckBuildingBlocks K (pilotContext keys prss i)) r.1
  obtain ⟨pre, hpre⟩ := advance_salts_compareDigests (pilotContext keys prss i) f r.2
  refine ⟨pre, f, ?_⟩
  simp only [pilotRest, h, ↓reduceIte, hf]
  exact hpre

end Start

section Cells

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- `streamWorld` is the sum of its counted part and its free part. -/
theorem streamWorld_add :
    streamWorld prims D = (fun t => streamWorld prims D (.inl t)) + fun t => streamWorld prims D (.inr t) := by
  funext t
  rcases t with t | t <;> rfl

/-- A free query of `H` outside the domain of `Th` in `streamWorld` leaves its answer in the hash cache. -/
theorem streamWorld_hashQuery {q : Query C} (hq : ¬ IsFixed q) (s : HashCache C × HiddenCache C)
    (z : HashOutput × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C)))).run s)) :
    s ≤ z.2 ∧ z.2.1 q = some z.1 := by
  refine ⟨streamWorld_le prims D _ s z hz, ?_⟩
  rw [streamWorld_add, simulateQ_free, show liftComp (hashQuery q) (LocalSpec C) =
    (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))) : OracleComp (LocalSpec C) HashOutput) from rfl,
    simulateQ_query] at hz
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map] at hz
  obtain ⟨h, hc⟩ := s
  change z ∈ support ((onHash (hashAnswer prims q)).run (h, hc)) at hz
  rw [onHash_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact hashAnswer_cached prims hq h w hw

/-- The digests of the terms `Ts` in `streamWorld`. Each held term leaves its history cell and its
digest cell in the hash cache. It is `support_digestQuery_list` of `Proof/Check.lean` on the free copy
in `streamWorld`. -/
theorem streamWorld_digestList (i : C.Party) (salts : Shares C Bit) (h : C.Term → List Bit) :
    ∀ (Ts : List C.Term) (s : HashCache C × HiddenCache C) z,
      z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (Ts.mapM fun T => if i ∈ C.holders T then do
          hashQuery (C := C) (.digest (vector 256 (salts T)) (← hashQuery (.history (h T)))) else pure 0)
          (LocalSpec C)))).run s) →
      s ≤ z.2 ∧ ∃ hlen : z.1.length = Ts.length, ∀ m (hm : m < Ts.length),
        i ∈ C.holders Ts[m] → ∃ hh, z.2.1 (.history (h Ts[m])) = some hh ∧
          z.2.1 (.digest (vector 256 (salts Ts[m])) hh) = some (z.1[m]'(hlen ▸ hm)) := by
  intro Ts
  induction Ts with
  | nil =>
    intro s z hz
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, rfl, fun m hm => absurd hm (by simp)⟩
  | cons T Ts ih =>
    intro s z hz
    simp only [List.mapM_cons, liftComp_bind, free, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨d, s₁⟩, h₁, ⟨ds, s₂⟩, h₂, hz⟩ := hz
    simp only [liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    have hT : s ≤ s₁ ∧ (i ∈ C.holders T → ∃ hh, s₁.1 (.history (h T)) = some hh ∧
        s₁.1 (.digest (vector 256 (salts T)) hh) = some d) := by
      split_ifs at h₁ with hiT
      · simp only [liftComp_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h₁
        obtain ⟨⟨hh, s₀⟩, h₀, h₁⟩ := h₁
        have hq₀ : ¬ IsFixed (C := C) (.history (h T)) := by rintro ⟨_, h, _⟩; cases h
        have hq₁ : ¬ IsFixed (C := C) (.digest (vector 256 (salts T)) hh) := by rintro ⟨_, h, _⟩; cases h
        obtain ⟨hle₀, hc₀⟩ := streamWorld_hashQuery prims D hq₀ s _ h₀
        obtain ⟨hle₁, hc₁⟩ := streamWorld_hashQuery prims D hq₁ s₀ _ h₁
        exact ⟨hle₀.trans hle₁, fun _ => ⟨hh, hle₁.1 hc₀, hc₁⟩⟩
      · simp only [liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
        cases h₁
        exact ⟨le_rfl, fun h => absurd h hiT⟩
    obtain ⟨hle₁, hd₁⟩ := hT
    obtain ⟨hle₂, hlen, hds⟩ := ih s₁ _ h₂
    refine ⟨hle₁.trans hle₂, by simp [hlen], fun m hm hiT => ?_⟩
    cases m with
    | zero =>
      obtain ⟨hh, e1, e2⟩ := hd₁ hiT
      exact ⟨hh, hle₂.1 e1, hle₂.1 e2⟩
    | succ m => exact hds m (by simpa using hm) hiT

/-- The history cell and the digest cell of each term that operator `i` holds are in the cache `s`, and
`d` is the digest at the place of the term in `ds`. -/
def DigestCells (s : HashCache C) (i : C.Party) (h : C.Term → List Bit) (ds : List HashOutput) : Prop :=
  ∀ T, i ∈ C.holders T → ∃ salt hv d, s (.history (h T)) = some hv ∧ s (.digest salt hv) = some d ∧
    ds[C.terms.idxOf T]? = some d

theorem DigestCells.mono {s s' : HashCache C} {i : C.Party} {h : C.Term → List Bit} {ds : List HashOutput}
    (hc : DigestCells s i h ds) (hle : s ≤ s') : DigestCells s' i h ds := fun T hT => by
  obtain ⟨salt, hv, d, e1, e2, e3⟩ := hc T hT
  exact ⟨salt, hv, d, hle e1, hle e2, e3⟩

/-- The digests of operator `i` in `streamWorld` leave their cells in the hash cache. -/
theorem streamWorld_digestQuery (i : C.Party) (salts : Shares C Bit) (h : C.Term → List Bit)
    (s : HashCache C × HiddenCache C) z
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (digestQuery i salts h)
      (LocalSpec C)))).run s)) :
    s ≤ z.2 ∧ DigestCells z.2.1 i h z.1 := by
  obtain ⟨hle, hlen, hds⟩ := streamWorld_digestList prims D i salts h C.terms s z hz
  refine ⟨hle, fun T hT => ?_⟩
  have hidx : C.terms[C.terms.idxOf T]'(idxOf_terms_lt T) = T := List.getElem_idxOf _
  obtain ⟨hv, e1, e2⟩ := hds _ (idxOf_terms_lt T) (by rw [hidx]; exact hT)
  rw [hidx] at e1 e2
  exact ⟨_, hv, _, e1, e2, List.getElem?_eq_getElem _⟩

end Cells

section RestStart

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)
  (K : Constants C E)

attribute [local instance] inhabitedField

/-- A start step of the rest of operator `i` with the cache `s`. It is an abort, or it waits in the
digest round with digests `ds` of a history that extends `filledHistory`, whose cells are in `s`.
After the round it aborts on an abort frame and on digests that do not agree. -/
def RestStart (x : C.Party → List (Tuple C)) (i : C.Party) (step : Step C E RealSpec Unit)
    (s : HashCache C) : Prop :=
  step = .done none ∨ ∃ (h : C.Term → List Bit) (ds : List HashOutput)
    (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option Unit)),
    (∀ T, ∃ rest, h T = filledHistory K i (x i) T ++ rest) ∧ DigestCells s i h ds ∧
    step = .wait (digestOutbox i ds) k ∧
    ∀ inbox, ((C.parties.any fun j => Msg.isAbort (inbox j)) = true ∨ ¬ DigestsAgree (E := E) i ds inbox) →
      k inbox = pure none

theorem RestStart.mono {x : C.Party → List (Tuple C)} {i : C.Party} {step : Step C E RealSpec Unit}
    {s s' : HashCache C} (h : RestStart K x i step s) (hle : s ≤ s') : RestStart K x i step s' := by
  rcases h with h | ⟨hh, ds, k, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨hh, ds, k, h1, h2.mono hle, h3, h4⟩

/-- The start step of the rest of each honest operator in `streamWorld`. -/
theorem restStart (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (x : C.Party → List (Tuple C))
    (i : C.Party) (o : Option ((E × E × E × Shares C E × Shares C E) × RunState C))
    (s : HashCache C × HiddenCache C) z
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (free (advance (o.elim failure (pilotRest K keys prss x i)).run))).run s)) :
    s ≤ z.2 ∧ RestStart K x i z.1 z.2.1 := by
  refine ⟨streamWorld_le prims D _ s z hz, ?_⟩
  have habort : ∀ (p : PartyM C E RealSpec Unit), p = failure →
      z ∈ support ((simulateQ (streamWorld prims D) (free (advance p.run))).run s) → RestStart K x i z.1 z.2.1 := by
    rintro p rfl hz
    rw [advance_run_failure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  rcases o with _ | r
  · exact habort _ rfl hz
  by_cases hg : HistoryExtends (filledHistory K i (x i)) r.2
  swap
  · exact habort _ (by simp only [Option.elim, pilotRest, hg, ↓reduceIte]) hz
  obtain ⟨pre, f, hadv⟩ := advance_pilotRest K keys prss x i r hg
  simp only [Option.elim] at hz
  rw [hadv] at hz
  simp only [free, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p₁, -, p₂, h₂, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨-, hcells⟩ := streamWorld_digestQuery prims D i p₁.1 r.2.history p₁.2 p₂ h₂
  refine Or.inr ⟨r.2.history, p₂.1, _, hg, hcells, rfl, fun inbox hbad => ?_⟩
  unfold exchangeResume
  split_ifs with hab
  · rfl
  · rcases hbad with hbad | hbad
    · exact absurd hbad hab
    · simp only [require, hbad, ↓reduceIte]
      rfl

end RestStart

section Rounds

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

/-- Each step of a sequence in `streamWorld` has the property `P` of its own computation. -/
theorem streamWorld_sequenceFin {α : Type} {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α)
    (P : Fin n → α → HashCache C × HiddenCache C → Prop)
    (hf : ∀ j s, ∀ z ∈ support ((simulateQ (streamWorld prims D) (f j)).run s), P j z.1 z.2)
    (hP : ∀ j a s s', P j a s → s ≤ s' → P j a s') (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (OverPermutation.sequenceFin f)).run s),
      s ≤ z.2 ∧ ∀ j, P j (z.1 j) z.2 := by
  intro z hz
  rw [ThresholdLeanXmssSecurity.simulateQ_sequenceFin] at hz
  obtain ⟨hle, -, hP'⟩ := support_sequenceFin_inv (fun _ => True) _ P
    (fun j s' _ z' hz' => ⟨streamWorld_le prims D _ s' z' hz', trivial, hf j s' z' hz'⟩) hP s trivial z hz
  exact ⟨hle, hP'⟩

/-- A step of the network keeps each output. -/
theorem stepRound_done {I O L R Ia α : Type} (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α) (s : HashCache C × HiddenCache C) z
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D A F st steps)).run s))
    (i : C.Party) (o : Option α) (hi : steps i = .done o) : z.1.2.1 i = .done o := by
  unfold stepRound at hz
  split_ifs at hz
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, -, q, hq, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (streamWorld_sequenceFin prims D _ (fun j (a : Step C E (CallSpec I O) α) _ => ∀ o, steps j = .done o → a = .done o)
      (fun j s' z' hz' o' ho' => by
        simp only [ho', simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz'
        rw [hz'])
      (fun _ _ _ _ h _ => h) _ q hq).2 i o hi
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨⟨state, sent⟩, s₁⟩, -, q, hq, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (streamWorld_sequenceFin prims D _ (fun j (a : Step C E (CallSpec I O) α) _ => ∀ o, steps j = .done o → a = .done o)
      (fun j s' z' hz' o' ho' => by
        simp only [ho', simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz'
        rw [hz'])
      (fun _ _ _ _ h _ => h) _ q hq).2 i o hi

/-- The rounds of the network keep each output. -/
theorem executeRounds_done {I O L R Ia α : Type} (A : Adversary C E Ia L R) (F : Functionality C I O L R) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α) (s : HashCache C × HiddenCache C) z,
      z ∈ support ((simulateQ (streamWorld prims D) (executeRounds worldRoles D A F fuel st steps)).run s) →
      ∀ i o, steps i = .done o → z.1.2 i = o
  | 0, st, steps, s, z, hz, i, o, hi => by
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [hi, Step.output]
  | fuel + 1, st, steps, s, z, hz, i, o, hi => by
    rw [executeRounds] at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only [hi, Step.output]
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      exact executeRounds_done A F fuel _ _ _ z hz i o (stepRound_done prims D A F st steps s p hp i o hi)

end Rounds

section Accept

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)
  (K : Constants C E)

attribute [local instance] inhabitedField

/-- An honest accept after the digest round. Each honest operator waited in the round with its
digests, the accepting operator saw no abort frame, and the digests of the honest holders of each term
agree. -/
theorem rounds_accept (net : Adversary C E Unit PEmpty PEmpty) (x : C.Party → List (Tuple C)) (n : ℕ)
    (st : net.State) (steps : C.Party → Step C E RealSpec Unit) (c : HashCache C)
    (hstart : ∀ j, j ∉ D.1 → RestStart K x j (steps j) c) (s : HashCache C × HiddenCache C) z
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executeRounds worldRoles D net noFunctionality (n + 1) st steps)).run s))
    (i : C.Party) (hi : i ∉ D.1) (hacc : z.1.2 i = some ()) :
    ∃ (hist : C.Party → C.Term → List Bit) (ds : C.Party → List HashOutput),
      (∀ a, a ∉ D.1 → (∀ T, ∃ rest, hist a T = filledHistory K a (x a) T ++ rest) ∧ DigestCells c a (hist a) (ds a)) ∧
      ∀ T a b, a ∉ D.1 → b ∉ D.1 → a ∈ C.holders T → b ∈ C.holders T →
        (ds a)[C.terms.idxOf T]? = (ds b)[C.terms.idxOf T]? := by
  rw [executeRounds] at hz
  split_ifs at hz with hall
  · exfalso
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rcases hstart i hi with h | ⟨_, _, _, _, _, h, _⟩ <;> simp [h, Step.output] at hacc
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  unfold stepRound at hp
  split_ifs at hp with hcall
  · exfalso
    obtain ⟨j, hj, hc⟩ := hcall.1
    rcases hstart j hj with h | ⟨_, _, _, _, _, h, _⟩ <;> simp [h, Step.callInput] at hc
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨⟨⟨state, sent⟩, s₁⟩, -, q, hq, hp⟩ := hp
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  obtain ⟨-, hq'⟩ := streamWorld_sequenceFin prims D _ (fun j (a : Step C E RealSpec Unit) _ =>
      (∀ o, steps j = .done o → a = .done o) ∧ ∀ ob k, steps j = .wait ob k →
        k (fun k' => if k' ∈ D.1 then sent k' j else (steps k').delivered j) = pure none → a = .done none)
    (fun j s' z' hz' => by
      refine ⟨fun o ho => ?_, fun ob k hk hnone => ?_⟩
      · simp only [ho, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz'
        rw [hz']
      · simp only [hk] at hz'
        split_ifs at hz'
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz'
          rw [hz']
        · simp only [worldRoles, hnone, advance_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz'
          rw [hz'])
    (fun _ _ _ _ h _ => h) _ q hq
  have hout := executeRounds_done prims D net noFunctionality n state q.1 q.2 z hz
  have hi_ne : q.1 i ≠ .done none := fun h => by
    rw [hout i none h] at hacc
    cases hacc
  rcases hstart i hi with hdone | ⟨hhi, dsi, ki, hexti, hcellsi, hsi, hbadi⟩
  · exact absurd ((hq' i).1 none hdone) hi_ne
  have hab : (C.parties.any fun j => Msg.isAbort
      ((fun k' => if k' ∈ D.1 then sent k' i else (steps k').delivered i : Mail C E) j)) ≠ true :=
    fun h => hi_ne ((hq' i).2 _ _ hsi (hbadi _ (Or.inl h)))
  have hag : DigestsAgree (E := E) i dsi (fun k' => if k' ∈ D.1 then sent k' i else (steps k').delivered i) := by
    by_contra h
    exact hi_ne ((hq' i).2 _ _ hsi (hbadi _ (Or.inr h)))
  have hw : ∀ a, ∃ (h : C.Term → List Bit) (ds : List HashOutput), a ∉ D.1 →
      (∀ T, ∃ rest, h T = filledHistory K a (x a) T ++ rest) ∧ DigestCells c a h ds ∧
        ∃ k, steps a = .wait (digestOutbox a ds) k := by
    intro a
    by_cases ha : a ∈ D.1
    · exact ⟨fun _ => [], [], fun h => absurd ha h⟩
    rcases hstart a ha with hdone | ⟨hh, ds, k, hext, hcells, hs, -⟩
    · exfalso
      apply hab
      rw [List.any_eq_true]
      refine ⟨a, List.mem_finRange a, ?_⟩
      simp only [ha, ↓reduceIte, hdone, Step.delivered, Msg.isAbort]
    · exact ⟨hh, ds, fun _ => ⟨hext, hcells, k, hs⟩⟩
  choose hist ds hw using hw
  refine ⟨fun a => if a = i then hhi else hist a, fun a => if a = i then dsi else ds a, fun a ha => ?_,
    fun T a b ha hb haT hbT => ?_⟩
  · by_cases hai : a = i
    · subst hai
      simp only [↓reduceIte]
      exact ⟨hexti, hcellsi⟩
    · simp only [hai, ↓reduceIte]
      exact ⟨(hw a ha).1, (hw a ha).2.1⟩
  have hsel : ∀ a, a ∉ D.1 → (if a = i then dsi else Msg.hashesOf
      ((fun k' => if k' ∈ D.1 then sent k' i else (steps k').delivered i : Mail C E) a)) =
        if a = i then dsi else ds a := fun a ha => by
    by_cases hai : a = i
    · simp only [hai, ↓reduceIte]
    · obtain ⟨k, hk⟩ := (hw a ha).2.2
      simp only [hai, ↓reduceIte, ha, hk, Step.delivered, digestOutbox, Ne.symm hai, Msg.hashesOf]
  have h := (hag T a haT b hbT).1
  rw [hsel a ha, hsel b hb] at h
  exact h

end Accept

section Rest

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

/-- The rest phase gives `RestEvidence`. The start steps of the rests hold their digests and cells
(`restStart`), and an honest accept after the digest round gives the rest (`rounds_accept`). -/
theorem restEvidence : RestEvidence prims K := by
  intro D net keys prss x st outs s z hz ⟨i, hi, hacc⟩
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  unfold startSteps at hp
  obtain ⟨-, hstart⟩ := streamWorld_sequenceFin prims D _ (fun j (a : Step C E RealSpec Unit) s' =>
      j ∉ D.1 → RestStart K x j a s'.1)
    (fun j s' z' hz' hj => by
      simp only [hj, ↓reduceIte, worldRoles] at hz'
      exact (restStart prims D K keys prss x j (outs j) s' z' hz').2)
    (fun j a s₁ s₂ h hle hj => (h hj).mono K hle.1) s p hp
  obtain ⟨hist, ds, hcells, hsame⟩ := rounds_accept prims D K net x 5 st p.1 p.2.1 (fun j hj => hstart j hj)
    p.2 z hz i hi hacc
  have hle := (streamWorld_le prims D _ p.2 z hz).1
  refine ⟨hist, ds, fun a ha => (hcells a ha).1, fun a ha T _ haT => ?_, hsame⟩
  obtain ⟨salt, hv, d, e1, e2, e3⟩ := (hcells a ha).2 T haT
  exact ⟨salt, hv, d, hle e1, hle e2, e3⟩

/-- The trace facts of an accepted check with split copies hold. -/
theorem splitAcceptEvidence : SplitAcceptEvidence prims K :=
  splitAcceptEvidence_of_rest prims K (restEvidence prims K)

end Rest

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
  (prims : Primitives) (K : Constants C E)

/-- The pilot in the case where the honest copies of the tuples agree. -/
theorem pilotSound : PilotSound prims K :=
  pilotSound_of_join prims K (pilotJoinOut prims K)

/-- The pilot. An honest operator accepts the real check of tuples with a wrong tuple with probability at
most `pilotError`. -/
theorem pilotCheck : PilotCheck prims K :=
  pilotCheck_of_join prims K (pilotJoinOut prims K) (splitAcceptEvidence prims K)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSound_of_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSound_of_join

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotCheck_of_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotCheck_of_join

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.splitAcceptEvidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.splitAcceptEvidence

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSound

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotCheck
