import ThresholdLeanXmssSecurity.Proof.SigningFlat

/-!
# The eager grind on the flat run

This module gives step 1 of the plan in `SigningEagerGrind` on the flat run of `SigningFlat`.

## The hash form

* `HashLaw m M` says that `m` has the law of the hash form `M` against each continuation in hash form.
  The cache of the state is the cache of `mixedOracle`, and `Rest` is the rest of the state.
* `hashLaw_carry_logged` gives the hash form of a world call other than a programming query.
* `eagerWorld extra` runs the lazy calls of `extra` after each world call. `extra` reads the state
  before the call, the call and the state after the call. `hashLaw_eagerWorld` shows that the extra
  calls keep the law. This is `evalDist_mixed_run'_bind_const` of `SigningFlat`, the step of
  `evalDist_eagerMixed_run'`. `evalDist_eagerMixed_run'` itself does not apply, because its extra
  calls see only the input and the answer, not `bound e`.
* `hashLaw_simulateQ_world`, `hashLaw_flatWith` and `hashLaw_flatGame` lift the law to the flat run.

## The eager grind

* `grindExtra P ρ` runs the honest grind of `signCodeword` at each canonical base call of a key `e`
  (`BaseCall`), on the answer of the base input. The trigger reads only the carried state, so a
  later base call runs the grind again. `baseCall_once` gives that its base input is cached. That
  its trials are cached requires a separate invariant.
* `flatRun_eq_flatGame` writes `flatRun` as `flatGame` over `flatWorld`.
* `evalDist_flatEagerRun` shows that the flat eager run has the law of `flatRun` for the result, the
  count, the log and the carried state. `evalDist_flatEagerRun_logged` gives the law of `loggedRun`
  without the cache. The final cache differs.

## The R1 monitor

* `monitoredWorld` adds the pending-risk monitor of `SigningPartnerBound` to the eager world calls.
  Each logged call steps it as a query (`queryEntryStep`), on either copy, so no logged call
  installs a target. Each call of the grind at the base call steps it as a trial (`trialStep`).
* A fresh trial at an unsigned key is a sign attempt of leanVM. A valid digest installs the target
  and hits if it is pending. A trial on a seen input changes nothing. So a selection that the log
  holds before the base call installs nothing.
* A fresh trial at a signed key only marks its input as seen. This differs from the sign attempt of
  leanVM, which checks the target. In the first grind at a key the key is unsigned. A later grind
  at the key runs on the same base answer, so its trials are likely cached.
* `monitoredGame_forgets` shows that the monitor is write-only. `monitoredRun_forget` gives the
  flat eager run exactly.
* `trialFresh_risk_sum_le` shows that a trial costs nothing. It is the sign branch of
  `fresh_risk_sum_le` with `CappedEncodingMonitor.uniformDigest_sign_bonus_sum_le`.
  `monitoredOracle_run_risk_le` lifts it to a grind with `XmssSecurity.expectedFinal_le`.
* `PotStep` is the step of the potential in expectation, with the keyed calls of the log as cost.
  `potStep_monitoredGame` lifts it to the flat run.
* `r1Hit_bound` bounds the hit by `2^-128` for each bottom digest call in expectation, the bound of
  `bottomPartnerLogged_bound`. The keyed calls of the log transfer to `loggedRun` by
  `evalDist_flatEagerRun_logged`.

## The split

* `splitRun` adds a write-only flag to the monitor. `cachedTrial` raises it at a trial on a seen
  input with a valid digest at an unsigned key. `CachedSelection` is the flag.
* `split_r1Hit_bound` is `r1Hit_bound` on the split run.
* `R1Link` is the step-3 hypothesis. Its partner win reads the final cache of the eager run, which differs
  from the final cache of `loggedRun`.
* The link needs `P := x.1` and `ρ x` the honest openings. `SigningReleased.run_signCodeword_cached`
  shows that a trial calls `CacheView.encodingInput P e`, which `encodingInputLeafIndex? x.1` reads.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningFlatEagerProof

open LeanXmss ThresholdLeanXmss SigningFlatProof

section HashLaw

variable {C : Committee} (prims : Primitives) {σ : Type}

/-- The part of a flat state other than the cache, namely the count, the log and the carried state. -/
abbrev Rest (C : Committee) (σ : Type) := (ℕ × QueryLog (WorldSpec C)) × σ

/-- The flat state from the cache and the rest. -/
def ofRest (c : HashCache C) (r : Rest C σ) : SigningHitLaneProof.LoggedState C × σ := (((c, r.1.1), r.1.2), r.2)

/-- The rest of a flat state. -/
def restOf (p : SigningHitLaneProof.LoggedState C × σ) : Rest C σ := ((p.1.1.2, p.1.2), p.2)

/-- `m` has the law of the hash form `M` against each continuation in hash form. The continuation
reads the rest of the state, and it runs on the cache of the state. -/
def HashLaw {α : Type} (m : StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp α)
    (M : Rest C σ → OracleComp (HashSpec C) (α × Rest C σ)) : Prop :=
  ∀ (c : HashCache C) (r : Rest C σ) {β : Type} (K : α → Rest C σ → OracleComp (HashSpec C) β),
    𝒟[m.run (ofRest c r) >>= fun z => (simulateQ mixedOracle (K z.1 (restOf z.2))).run' z.2.1.1.1] =
      𝒟[(simulateQ mixedOracle (M r >>= fun z => K z.1 z.2)).run' c]

theorem hashLaw_pure {α : Type} (a : α) :
    HashLaw (pure a : StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp α) (fun r => pure (a, r)) := by
  intro c r β K
  simp only [StateT.run_pure, pure_bind]
  rfl

theorem hashLaw_bind {α γ : Type} {m : StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp α}
    {M : Rest C σ → OracleComp (HashSpec C) (α × Rest C σ)}
    {k : α → StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp γ}
    {Kf : α → Rest C σ → OracleComp (HashSpec C) (γ × Rest C σ)} (hm : HashLaw m M)
    (hk : ∀ a, HashLaw (k a) (Kf a)) : HashLaw (m >>= k) (fun r => M r >>= fun z => Kf z.1 z.2) := by
  intro c r β K
  rw [StateT.run_bind, bind_assoc]
  calc _ = 𝒟[m.run (ofRest c r) >>= fun z =>
          (simulateQ mixedOracle (Kf z.1 (restOf z.2) >>= fun y => K y.1 y.2)).run' z.2.1.1.1] :=
        OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun z => hk z.1 z.2.1.1.1 (restOf z.2) K
    _ = _ := by
        rw [hm c r (fun a r' => Kf a r' >>= fun y => K y.1 y.2), bind_assoc]

/-- `hashLaw_bind` with the hash form as a `StateT` computation. -/
theorem hashLaw_bindT {α γ : Type} {m : StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp α}
    {mt : StateT (Rest C σ) (OracleComp (HashSpec C)) α}
    {k : α → StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp γ}
    {kt : α → StateT (Rest C σ) (OracleComp (HashSpec C)) γ} (hm : HashLaw m mt.run)
    (hk : ∀ a, HashLaw (k a) (kt a).run) : HashLaw (m >>= k) (mt >>= kt).run :=
  hashLaw_bind hm hk

/-- One world call in hash form. It adds the cost and logs the call with its answer. -/
def worldHash (t : (WorldSpec C).Domain) (r : Rest C σ) :
    OracleComp (HashSpec C) ((WorldSpec C).Range t × Rest C σ) :=
  (fun a => (a, ((r.1.1 + SeedHitProof.signCost t, r.1.2.logQuery t a), r.2))) <$>
    simulateQ (localQuery prims) (SigningHitProof.worldLocalize t)

/-- A world call other than a programming query is a run of `mixedOracle` on the cache. -/
theorem carry_logged_run (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t) (c : HashCache C)
    (r : Rest C σ) :
    (carry (SigningCostProof.loggedImpl prims) t).run (ofRest c r) =
      (fun w => (w.1, ofRest w.2 ((r.1.1 + SeedHitProof.signCost t, r.1.2.logQuery t w.1), r.2))) <$>
        (simulateQ mixedOracle (simulateQ (localQuery prims) (SigningHitProof.worldLocalize t))).run c := by
  have hsign := signImpl_simulateQ prims (query t) (SigningHitProof.programFree_query t ht)
  erw [simulateQ_spec_query, simulateQ_spec_query] at hsign
  simp only [carry, SigningCostProof.loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount,
    StateT.run_mk, hsign, Functor.map_map]
  rfl

theorem hashLaw_carry_logged (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t) :
    HashLaw (σ := σ) (carry (SigningCostProof.loggedImpl prims) t) (worldHash prims t) := by
  intro c r β K
  rw [carry_logged_run prims t ht c r, bind_map_left, worldHash, bind_map_left, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind, map_bind]
  rfl

/-- The world calls with extra lazy calls after each call. The extra calls read the state before
the call, the call and the state after the call. They change only the cache. -/
def eagerWorld (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit) :
    QueryImpl (WorldSpec C) (StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp) :=
  fun t => StateT.mk fun p => (carry (SigningCostProof.loggedImpl prims) t).run p >>= fun z =>
    (fun q => (z.1, ofRest q.2 (restOf z.2))) <$>
      (simulateQ (randomOracle (spec := Query C →ₒ HashOutput)) (extra p t z.2)).run z.2.1.1.1

/-- The extra calls keep the law against each continuation in hash form. This is
`evalDist_mixed_run'_bind_const` after the call. -/
theorem hashLaw_eagerWorld (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit)
    (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t) :
    HashLaw (eagerWorld prims extra t) (worldHash prims t) := by
  intro c r β K
  simp only [eagerWorld, StateT.run_mk, bind_assoc, bind_map_left]
  calc _ = 𝒟[(carry (SigningCostProof.loggedImpl prims) t).run (ofRest c r) >>= fun z =>
          (simulateQ mixedOracle (K z.1 (restOf z.2))).run' z.2.1.1.1] :=
        OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun z =>
          evalDist_mixed_run'_bind_const _ _ _
    _ = _ := hashLaw_carry_logged prims t ht c r K

/-- The world calls in hash form, with the rest as state. -/
def worldTracker : QueryImpl (WorldSpec C) (StateT (Rest C σ) (OracleComp (HashSpec C))) :=
  fun t => StateT.mk (worldHash prims t)

/-- A run of world calls with no programming query has the law of its hash form. -/
theorem hashLaw_simulateQ_world
    (W : QueryImpl (WorldSpec C) (StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W t) (worldHash prims t)) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (h : SigningHitProof.ProgramFree oa) :
    HashLaw (simulateQ W oa) (fun r => (simulateQ (worldTracker prims) oa).run r) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using hashLaw_pure (C := C) (σ := σ) a
  | query_bind t k ih =>
    have hb := (isQueryBoundP_query_bind_iff SigningHitLaneProof.IsProgram t k 0).mp h
    have ht : ¬SigningHitLaneProof.IsProgram t := by simpa using hb.1
    have hk : ∀ u, SigningHitProof.ProgramFree (k u) := by
      simpa [SigningHitProof.ProgramFree, ht] using hb.2
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hbind := hashLaw_bind (hW t ht) fun u => ih u (hk u)
    simp only [StateT.run_bind, worldTracker, StateT.run_mk]
    exact hbind

end HashLaw

section Flat

variable {C : Committee} (prims : Primitives) {σ : Type} {ι : Type} {spec : OracleSpec ι}

/-- `flat` with a world handler that may read the carried state. -/
def flatWith {τ : Type} (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (W : QueryImpl (WorldSpec C) (StateT (τ × σ) ProbComp)) : QueryImpl spec (StateT (τ × σ) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1.1, (z.2.1, z.1.2))) <$> (simulateQ W ((outer t).run p.2)).run p

theorem flat_eq_flatWith (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C)))) :
    flat outer (SigningCostProof.loggedImpl prims) = flatWith outer (carry (SigningCostProof.loggedImpl prims)) :=
  rfl

/-- The calls of `outer` in hash form. -/
def outerTracker (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C)))) :
    QueryImpl spec (StateT (Rest C σ) (OracleComp (HashSpec C))) :=
  fun t => StateT.mk fun r => (fun z => (z.1.1, (z.2.1, z.1.2))) <$>
    (simulateQ (worldTracker prims) ((outer t).run r.2)).run r

theorem hashLaw_flatWith (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (hfree : ∀ t s, SigningHitProof.ProgramFree ((outer t).run s))
    (W : QueryImpl (WorldSpec C) (StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W t) (worldHash prims t)) (t : spec.Domain) :
    HashLaw (flatWith outer W t) (outerTracker prims outer t).run := by
  intro c r β K
  simp only [flatWith, outerTracker, StateT.run_mk, bind_map_left]
  exact hashLaw_simulateQ_world prims W hW _ (hfree t r.2) c r (fun y r' => K y.1 (r'.1, y.2))

/-- A run of a handler whose calls have the law of their hash form has the law of its hash form. -/
theorem hashLaw_simulateQ (V : QueryImpl spec (StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp))
    (F : QueryImpl spec (StateT (Rest C σ) (OracleComp (HashSpec C)))) (hV : ∀ t, HashLaw (V t) (F t).run)
    {α : Type} (oa : OracleComp spec α) : HashLaw (simulateQ V oa) (simulateQ F oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact hashLaw_pure (C := C) (σ := σ) a
  | query_bind t k ih =>
    have hbind := hashLaw_bind (hV t) fun u => ih u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact hbind

end Flat

section Game

variable {C : Committee} (prims : Primitives)

/-- The result of `finalRun`. -/
abbrev Result (C : Committee) := (Bool × Bool) × Option (TopTree × TsigState C × Forgery)

/-- The stages of `finalRun` over a world handler, a forger handler and a read of the carried
state. -/
def gameWith {m : Type → Type} [Monad m] (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (world : QueryImpl (WorldSpec C) m)
    (forger : Dealt C (OracleComp (WorldSpec C)) → QueryImpl (LocalSpec C + TsigSpec C) m)
    (carried : m (TsigState C × Bool)) : m (Result C) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let r ← simulateQ world (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa)) value x.1 emptyTop .top)
  match r with
  | some (.top top) =>
    let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
    let a ← simulateQ (forger dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)
    let s ← carried
    let w ← simulateQ world (SigningCoreProof.tsigFinish dealt (a, s.1))
    pure ((w.1, s.2), some (top, w.2.1, w.2.2))
  | _ => pure ((false, false), none)

/-- The read of the carried state. -/
def getCarried {τ σ : Type} : StateT (τ × σ) ProbComp σ :=
  StateT.mk fun p => pure (p.2, p)

/-- The flat run over a world handler that may read the carried state. -/
def flatGame (W : QueryImpl (WorldSpec C) (StateT (FlatState C) ProbComp)) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) : StateT (FlatState C) ProbComp (Result C) :=
  gameWith A x W (fun dealt => flatWith (SigningCoreProof.flaggedOracles x dealt) W) getCarried

/-- The flat run in hash form. -/
def gameHash (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (Rest C (TsigState C × Bool)) (OracleComp (HashSpec C)) (Result C) :=
  gameWith A x (worldTracker prims) (fun dealt => outerTracker prims (SigningCoreProof.flaggedOracles x dealt))
    (StateT.mk fun r => pure (r.2, r))

/-- The initial flat state. -/
def flatInit : FlatState C := (SigningHitLaneProof.loggedInit, (SigningCoreProof.tsigInit, false))

theorem flatRun_eq_flatGame (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    flatRun prims A x = (flatGame (flatWorld prims) A x).run flatInit := by
  unfold flatRun flatGame gameWith
  rw [StateT.run_bind]
  refine bind_congr fun z => ?_
  rcases z with ⟨_ | (top | tree), l⟩
  · rfl
  · simp [StateT.run_bind, getCarried, flatOracles, flat_eq_flatWith, flatWorld]
  · rfl

theorem hashLaw_getCarried {σ : Type} :
    HashLaw (C := C) (getCarried (σ := σ)) (fun r => pure (r.2, r)) := by
  intro c r β K
  simp only [getCarried, StateT.run_mk, pure_bind]
  rfl

set_option maxRecDepth 100000 in
/-- The flat run over a world handler with the law of the hash form has the law of `gameHash`. -/
theorem hashLaw_flatGame (W : QueryImpl (WorldSpec C) (StateT (FlatState C) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W t) (worldHash prims t)) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) : HashLaw (flatGame W A x) (gameHash prims A x).run := by
  unfold flatGame gameHash gameWith
  dsimp only
  have hsetup : SigningHitProof.ProgramFree (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  refine hashLaw_bindT (hashLaw_simulateQ_world prims W hW _ hsetup) fun r => ?_
  rcases r with _ | (top | tree)
  · exact hashLaw_pure _
  · refine hashLaw_bindT (hashLaw_simulateQ _ _
      (fun t => hashLaw_flatWith prims _ (SigningHitProof.programFree_flaggedOracles x top) W hW t) _) fun a => ?_
    refine hashLaw_bindT hashLaw_getCarried fun s => ?_
    refine hashLaw_bindT (hashLaw_simulateQ_world prims W hW _ (SigningHitProof.programFree_finish x top _))
      fun w => ?_
    exact hashLaw_pure _
  · exact hashLaw_pure _

/-- The law of the result and the rest of a computation with a hash form. -/
theorem evalDist_map_restOf {σ α : Type} {m : StateT (SigningHitLaneProof.LoggedState C × σ) ProbComp α}
    {M : Rest C σ → OracleComp (HashSpec C) (α × Rest C σ)} (hm : HashLaw m M) (c : HashCache C)
    (r : Rest C σ) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> m.run (ofRest c r)] = 𝒟[(simulateQ mixedOracle (M r)).run' c] := by
  have h := hm c r (fun a r' => pure (a, r'))
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, Prod.mk.eta, bind_pure] at h
  rw [map_eq_bind_pure_comp, StateT.run'_eq]
  exact h

/-- Two world handlers with the law of the hash form give flat runs with one law of the result and
the rest. -/
theorem evalDist_flatGame_eq (W W' : QueryImpl (WorldSpec C) (StateT (FlatState C) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W t) (worldHash prims t))
    (hW' : ∀ t, ¬SigningHitLaneProof.IsProgram t → HashLaw (W' t) (worldHash prims t)) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> (flatGame W A x).run flatInit] =
      𝒟[(fun z => (z.1, restOf z.2)) <$> (flatGame W' A x).run flatInit] :=
  (evalDist_map_restOf (hashLaw_flatGame prims W hW A x) ∅ ((0, []), (SigningCoreProof.tsigInit, false))).trans
    (evalDist_map_restOf (hashLaw_flatGame prims W' hW' A x) ∅ ((0, []), (SigningCoreProof.tsigInit, false))).symm

end Game

section Eager

variable {C : Committee} (prims : Primitives)

/-- The honest grind of `signCodeword` on the lazy `H`, from the answer of the base input. -/
def baseGrind (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput) :
    OracleComp (Query C →ₒ HashOutput) Unit :=
  (fun _ => ()) <$> simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
    (grind P bottomLayer e (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0)

open Classical in
/-- At a canonical base call of a key `e`, the grind at `e` on the answer of the call. `ρ e` is the
randomizer value of `e`. The trigger reads only the carried state, so a later base call runs the
grind on cached trials. -/
def grindExtra (P : PublicParameter) (ρ : KeyIndex → Digest) (p : FlatState C) (t : (WorldSpec C).Domain)
    (p' : FlatState C) : OracleComp (Query C →ₒ HashOutput) Unit :=
  if h : ∃ e, BaseCall P e (ρ e) p.2.1 t then
    match p.2.1.bound h.choose with
    | some message =>
      match p'.1.1.1 (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) with
      | some answer => baseGrind P h.choose message answer
      | none => pure ()
    | none => pure ()
  else pure ()

/-- The flat run with the eager grind at each canonical base call. -/
def flatEagerRun (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) : ProbComp (Result C × FlatState C) :=
  (flatGame (eagerWorld prims (grindExtra P ρ)) A x).run flatInit

/-- The flat eager run has the law of `flatRun` for the result, the count, the log and the carried
state. The final cache differs. -/
theorem evalDist_flatEagerRun (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> flatEagerRun prims P ρ A x] =
      𝒟[(fun z => (z.1, restOf z.2)) <$> flatRun prims A x] := by
  rw [flatRun_eq_flatGame]
  exact evalDist_flatGame_eq prims _ _ (hashLaw_eagerWorld prims _) (hashLaw_carry_logged prims) A x

/-- The flat eager run has the law of `loggedRun` for the result, the count and the log. -/
theorem evalDist_flatEagerRun_logged (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> flatEagerRun prims P ρ A x] =
      𝒟[(fun z => (z.1, z.2.1.2, z.2.2)) <$> SigningCostProof.loggedRun prims A x] := by
  have h := congrArg (fun d => (fun z : Result C × Rest C (TsigState C × Bool) => (z.1, z.2.1.1, z.2.1.2)) <$> d)
    (evalDist_flatEagerRun prims P ρ A x)
  simp only [← evalDist_map, Functor.map_map] at h
  rw [← flatRun_logged, Functor.map_map]
  exact h

end Eager

section Monitor

open SigningPartnerBoundProof ENNReal

variable {C : Committee}

/-- A fresh trial of a grind at the base call. At an unsigned key it acts as a sign attempt of
leanVM (`CappedEncodingMonitor.applyUniformSignAttemptMonitor`), so a valid digest installs the
target. At a signed key it only marks the input as seen. -/
def trialFresh (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) : Monitor :=
  match (keyOf input).bind m.state.signed with
  | some _ => ⟨insert input m.seen, m.state, m.hit⟩
  | none => m.fresh keyOf input digest true

open Classical in
/-- One call of `H` on `q` in a grind at the base call. A trial on a seen input changes nothing. -/
def trialStep (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor) (q : Query C)
    (output : HashOutput) : Monitor :=
  match q with
  | .hash input => if input ∈ m.seen then m else trialFresh keyOf m input (XmssSecurity.truncateHash output)
  | _ => m

theorem trialFresh_hit (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) (h : m.hit = true) :
    (trialFresh keyOf m input digest).hit = true := by
  unfold trialFresh
  split
  · exact h
  · exact m.fresh_hit keyOf input digest true h

theorem trialFresh_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) :
    (trialFresh keyOf m input digest).seen = insert input m.seen := by
  unfold trialFresh
  split
  · rfl
  · exact m.fresh_seen keyOf input digest true

/-- A fresh trial with a uniform digest costs nothing. Its pending risk pays its hit. This is the
sign branch of `fresh_risk_sum_le`, with `CappedEncodingMonitor.uniformDigest_sign_bonus_sum_le`. -/
theorem trialFresh_risk_sum_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) :
    ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
        (trialFresh keyOf m input digest).risk ≤ m.risk := by
  by_cases hm : m.hit = true
  · have hone : ∀ digest, (trialFresh keyOf m input digest).risk = m.risk := fun digest => by
      simp [Monitor.risk, trialFresh_hit keyOf m input digest hm, hm]
    simp only [hone, uniformDigest_sum_const, le_refl]
  rw [Bool.not_eq_true] at hm
  have hconst : ∀ (f : XmssSecurity.Digest → Monitor), (∀ digest, (f digest).risk = m.risk) →
      ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
        (f digest).risk ≤ m.risk := fun f hf => by
    simp only [hf, uniformDigest_sum_const, le_refl]
  cases hk : keyOf input with
  | none =>
    refine hconst _ fun digest => ?_
    simp only [trialFresh, hk, Option.bind_none, m.fresh_none keyOf input digest true hk]
    rfl
  | some e =>
    cases hs : m.state.signed e with
    | some target =>
      refine hconst _ fun digest => ?_
      simp only [trialFresh, hk, hs, Option.bind_some]
      rfl
    | none =>
      have hfresh : ∀ digest, trialFresh keyOf m input digest = m.fresh keyOf input digest true := fun digest => by
        simp only [trialFresh, hk, hs, Option.bind_some]
      simp only [hfresh, m.fresh_unsigned keyOf input _ true e hk hs, if_true]
      have hrisk : m.risk = XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state := by
        simp [Monitor.risk, hm]
      rw [hrisk]
      set R := XmssSecurity.CappedEncodingMonitor.State.pendingRisk m.state with hR
      set R0 := XmssSecurity.CappedEncodingMonitor.State.pendingRisk (m.state.install e 0) with hR0
      have hsplit : R0 + ((m.state.pending e).card : ℝ≥0∞) *
          (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ = R :=
        XmssSecurity.CappedEncodingMonitor.State.pendingRisk_install_add m.state e 0
      calc _ ≤ ∑ digest : XmssSecurity.Digest, Pr[= digest | ($ᵗ XmssSecurity.Digest : ProbComp XmssSecurity.Digest)] *
            (R0 + if XmssSecurity.TargetSum.ValidDigest digest then
              (if digest ∈ m.state.pending e then 1 else 0)
            else ((m.state.pending e).card : ℝ≥0∞) *
              (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹) := by
            gcongr with digest
            by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
            · by_cases hp : digest ∈ m.state.pending e
              · simp [hv, hp, Monitor.risk]
              · simp only [hv, hp, if_true, if_false, Monitor.risk, hm, Bool.false_or,
                  decide_false, Bool.false_eq_true, add_zero]
                rw [pendingRisk_install_eq m.state e digest 0]
            · simp only [hv, if_false, Monitor.risk, hm, Bool.false_eq_true]
              rw [hsplit]
        _ ≤ R0 + ((m.state.pending e).card : ℝ≥0∞) *
              (XmssSecurity.TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
            simp only [mul_add, Finset.sum_add_distrib, uniformDigest_sum_const]
            gcongr
            exact XmssSecurity.CappedEncodingMonitor.uniformDigest_sign_bonus_sum_le _
        _ = R := hsplit

/-- Every cached input of `H` is seen by the monitor. -/
def CacheSeen (cache : HashCache C) (m : Monitor) : Prop :=
  ∀ input, cache (.hash input) ≠ none → input ∈ m.seen

/-- The lazy `H` with the trial monitor of a grind at the base call. -/
def monitoredOracle (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C × Monitor) ProbComp) :=
  fun q => StateT.mk fun s => (fun w => (w.1, (w.2, trialStep keyOf s.2 q w.1))) <$>
    ((Query C →ₒ HashOutput).randomOracle q).run s.1

theorem trialStep_seen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (q : Query C) (output : HashOutput) : m.seen ⊆ (trialStep keyOf m q output).seen := by
  cases q with
  | hash input =>
    simp only [trialStep]
    split_ifs
    · exact le_rfl
    · rw [trialFresh_seen]
      exact Set.subset_insert _ _
  | _ => exact le_rfl

/-- One trial costs nothing if every cached input is seen. -/
theorem monitoredOracle_risk_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (q : Query C)
    (s : HashCache C × Monitor) (hcov : CacheSeen s.1 s.2) :
    ∑' r, Pr[= r | (monitoredOracle keyOf q).run s] * r.2.2.risk ≤ s.2.risk := by
  simp only [monitoredOracle, StateT.run_mk, tsum_probOutput_map_mul]
  cases q with
  | hash input =>
    by_cases hseen : input ∈ s.2.seen
    · refine tsum_probOutput_mul_le_of_const _ _ _ fun w _ => ?_
      simp only [trialStep, if_pos hseen, le_refl]
    have hnone : s.1 (.hash input) = none := by
      by_contra h
      exact hseen (hcov input h)
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hnone, tsum_probOutput_map_mul]
    simp only [trialStep, if_neg hseen]
    exact (le_of_eq (hashOutput_sum_truncate fun digest => (trialFresh keyOf s.2 input digest).risk)).trans
      (trialFresh_risk_sum_le keyOf s.2 input)
  | _ => exact tsum_probOutput_mul_le_of_const _ _ _ fun w _ => le_rfl

theorem monitoredOracle_cacheSeen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (q : Query C)
    (s : HashCache C × Monitor) (hcov : CacheSeen s.1 s.2) :
    ∀ r ∈ support ((monitoredOracle keyOf q).run s), CacheSeen r.2.1 r.2.2 := by
  intro r hr input hin
  simp only [monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  by_cases he : q = .hash input
  · subst he
    simp only [trialStep]
    split_ifs with hs
    · exact hs
    · rw [trialFresh_seen]
      exact Set.mem_insert _ _
  · have hc := randomOracle_cache_ne q s.1 w hw (.hash input) (Ne.symm he)
    exact trialStep_seen keyOf s.2 q w.1 (hcov input (hc ▸ hin))

/-- A grind at the base call costs nothing. This is `XmssSecurity.expectedFinal_le` with no cost. -/
theorem monitoredOracle_run_risk_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {β : Type}
    (ob : OracleComp (Query C →ₒ HashOutput) β) (s : HashCache C × Monitor) (hcov : CacheSeen s.1 s.2) :
    ∑' r, Pr[= r | (simulateQ (monitoredOracle keyOf) ob).run s] * r.2.2.risk ≤ s.2.risk := by
  have h := XmssSecurity.expectedFinal_le (monitoredOracle keyOf) (Inv := fun s => CacheSeen s.1 s.2)
    (fun q s hs r hr => monitoredOracle_cacheSeen keyOf q s hs r hr) (fun s => s.2.risk)
    (fun _ _ => 0 * 0) (fun q s hs => by simpa using monitoredOracle_risk_le keyOf q s hs) ob s hcov
  rw [XmssSecurity.expectedSimulatedCost_const_mul, zero_mul, add_zero] at h
  exact h

theorem monitoredOracle_run_cacheSeen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {β : Type}
    (ob : OracleComp (Query C →ₒ HashOutput) β) (s : HashCache C × Monitor) (hcov : CacheSeen s.1 s.2) :
    ∀ r ∈ support ((simulateQ (monitoredOracle keyOf) ob).run s), CacheSeen r.2.1 r.2.2 :=
  SeedHitProof.support_simulateQ_inv _ (fun s => CacheSeen s.1 s.2)
    (fun q s hs r hr => monitoredOracle_cacheSeen keyOf q s hs r hr) ob s hcov

/-- The monitor forgets to the lazy `H`. -/
theorem monitoredOracle_run_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {β : Type}
    (ob : OracleComp (Query C →ₒ HashOutput) β) (cache : HashCache C) (m : Monitor) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (monitoredOracle keyOf) ob).run (cache, m) =
      (simulateQ (randomOracle (spec := Query C →ₒ HashOutput)) ob).run cache :=
  SigningCoreProof.simulateQ_run_forget _ _ (fun q c b => by
    simp only [monitoredOracle, StateT.run_mk, Functor.map_map]
    exact id_map _) ob cache m

end Monitor

section Monitored

open SigningPartnerBoundProof ENNReal

variable {C : Committee} (prims : Primitives) {σ : Type}

/-- A logged call of `H` on either copy. The R1 monitor treats it as a query, so it never installs
a target. -/
def queryEntryStep (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor) :
    Option (XmssSecurity.HashInput × XmssSecurity.Digest × Bool) → Monitor
  | none => m
  | some entry => m.step keyOf (entry.1, entry.2.1, false)

/-- The eager world calls with the R1 monitor. A world call steps the monitor as a query, and the
extra calls step it as trials. -/
def monitoredWorld (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit) :
    QueryImpl (WorldSpec C) (StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp) :=
  fun t => StateT.mk fun p => (carry (SigningCostProof.loggedImpl prims) t).run (p.1.1, p.2) >>= fun z =>
    (fun y => (z.1, (((ofRest y.2.1 (restOf z.2)).1, y.2.2), (ofRest y.2.1 (restOf z.2)).2))) <$>
      (simulateQ (monitoredOracle keyOf) (extra (p.1.1, p.2) t z.2)).run
        (z.2.1.1.1, queryEntryStep keyOf p.1.2 (hashEntry ⟨t, z.1⟩))

/-- `m₁` forgets its monitor to `m₂`. -/
def Forgets {τ κ α : Type} (m₁ : StateT ((τ × κ) × σ) ProbComp α) (m₂ : StateT (τ × σ) ProbComp α) : Prop :=
  ∀ a b s, (fun z => (z.1, (z.2.1.1, z.2.2))) <$> m₁.run ((a, b), s) = m₂.run (a, s)

theorem monitoredWorld_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit)
    (t : (WorldSpec C).Domain) : Forgets (monitoredWorld prims keyOf extra t) (eagerWorld prims extra t) := by
  intro a b s
  simp only [monitoredWorld, eagerWorld, StateT.run_mk, map_bind, Functor.map_map]
  refine bind_congr fun z => ?_
  rw [← monitoredOracle_run_forget keyOf _ _ (queryEntryStep keyOf b (hashEntry ⟨t, z.1⟩)), Functor.map_map]

theorem forgets_pure {τ κ α : Type} (x : α) :
    Forgets (pure x : StateT ((τ × κ) × σ) ProbComp α) (pure x : StateT (τ × σ) ProbComp α) := by
  intro a b s
  simp

theorem forgets_bind {τ κ α β : Type} {m₁ : StateT ((τ × κ) × σ) ProbComp α} {m₂ : StateT (τ × σ) ProbComp α}
    {k₁ : α → StateT ((τ × κ) × σ) ProbComp β} {k₂ : α → StateT (τ × σ) ProbComp β} (hm : Forgets m₁ m₂)
    (hk : ∀ x, Forgets (k₁ x) (k₂ x)) : Forgets (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro a b s
  rw [StateT.run_bind, StateT.run_bind, ← hm a b s, map_bind, bind_map_left]
  exact bind_congr fun z => hk z.1 z.2.1.1 z.2.1.2 z.2.2

theorem forgets_simulateQ {τ κ ι α : Type} {spec : OracleSpec ι}
    (V₁ : QueryImpl spec (StateT ((τ × κ) × σ) ProbComp)) (V₂ : QueryImpl spec (StateT (τ × σ) ProbComp))
    (h : ∀ t, Forgets (V₁ t) (V₂ t)) (oa : OracleComp spec α) :
    Forgets (simulateQ V₁ oa) (simulateQ V₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact forgets_pure x
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact forgets_bind (h t) ih

theorem forgets_flatWith {τ κ ι : Type} {spec : OracleSpec ι} (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (W₁ : QueryImpl (WorldSpec C) (StateT ((τ × κ) × σ) ProbComp)) (W₂ : QueryImpl (WorldSpec C) (StateT (τ × σ) ProbComp))
    (h : ∀ t, Forgets (W₁ t) (W₂ t)) (t : spec.Domain) : Forgets (flatWith outer W₁ t) (flatWith outer W₂ t) := by
  intro a b s
  simp only [flatWith, StateT.run_mk, Functor.map_map]
  rw [← forgets_simulateQ W₁ W₂ h _ a b s, Functor.map_map]

theorem forgets_getCarried {τ κ : Type} :
    Forgets (getCarried : StateT ((τ × κ) × σ) ProbComp σ) (getCarried : StateT (τ × σ) ProbComp σ) := by
  intro a b s
  simp [getCarried]

/-- The flat eager run with the R1 monitor. -/
def monitoredGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT ((SigningHitLaneProof.LoggedState C × Monitor) × (TsigState C × Bool)) ProbComp (Result C) :=
  gameWith A x (monitoredWorld prims keyOf extra)
    (fun dealt => flatWith (SigningCoreProof.flaggedOracles x dealt) (monitoredWorld prims keyOf extra)) getCarried

theorem monitoredGame_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (monitoredGame prims keyOf extra A x) (flatGame (eagerWorld prims extra) A x) := by
  unfold monitoredGame flatGame gameWith
  dsimp only
  have hW := monitoredWorld_forgets prims keyOf extra
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

end Monitored

section Potential

open SigningPartnerBoundProof ENNReal

variable {C : Committee} (prims : Primitives) {σ : Type}

theorem tsum_le_of_support {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞) (h : ∀ z ∈ support mx, f z ≤ g z) :
    ∑' z, Pr[= z | mx] * f z ≤ ∑' z, Pr[= z | mx] * g z := by
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support mx
  · exact mul_le_mul_left' (h z hz) _
  · simp [probOutput_eq_zero_of_not_mem_support hz]

theorem tsum_eq_of_support {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞) (h : ∀ z ∈ support mx, f z = g z) :
    ∑' z, Pr[= z | mx] * f z = ∑' z, Pr[= z | mx] * g z :=
  le_antisymm (tsum_le_of_support mx f g fun z hz => (h z hz).le)
    (tsum_le_of_support mx g f fun z hz => (h z hz).ge)

theorem tsum_probOutput_mul_const_add {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    ∑' z, Pr[= z | mx] * (c + f z) = c + ∑' z, Pr[= z | mx] * f z := by
  simp only [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_eq_zero (mx := mx)), one_mul]

/-- The keyed calls of a log. -/
def logKeyed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (log : QueryLog (WorldSpec C)) : ℕ :=
  (log.map fun entry => keyedCost keyOf entry.1).sum

theorem logKeyed_logQuery (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (log : QueryLog (WorldSpec C)) (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) :
    logKeyed keyOf (log.logQuery t u) = logKeyed keyOf log + keyedCost keyOf t := by
  simp [logKeyed, QueryLog.logQuery, QueryLog.singleton]

/-- The pending-risk step of the R1 monitor. Each keyed call of the log pays `2^-128` in
expectation. The state keeps every cached input seen. -/
def PotStep (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {α : Type}
    (m : StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp α) : Prop :=
  ∀ p : (SigningHitLaneProof.LoggedState C × Monitor) × σ, CacheSeen p.1.1.1.1 p.1.2 →
    (∀ z ∈ support (m.run p), CacheSeen z.2.1.1.1.1 z.2.1.2 ∧
      logKeyed keyOf p.1.1.2 ≤ logKeyed keyOf z.2.1.1.2) ∧
    ∑' z, Pr[= z | m.run p] * z.2.1.2.risk ≤
      p.1.2.risk + (2 ^ 128 : ℝ≥0∞)⁻¹ *
        ∑' z, Pr[= z | m.run p] * ((logKeyed keyOf z.2.1.1.2 - logKeyed keyOf p.1.1.2 : ℕ) : ℝ≥0∞)

theorem potStep_pure (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {α : Type} (x : α) :
    PotStep (σ := σ) keyOf (pure x : StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp α) := by
  intro p hp
  refine ⟨fun z hz => ?_, ?_⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hp, le_rfl⟩
  · simp only [StateT.run_pure, tsum_probOutput_pure_mul]
    exact le_self_add

theorem potStep_bind (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {α β : Type}
    {m : StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp α}
    {k : α → StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp β}
    (hm : PotStep keyOf m) (hk : ∀ x, PotStep keyOf (k x)) : PotStep keyOf (m >>= k) := by
  intro p hp
  obtain ⟨hms, hmr⟩ := hm p hp
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨hy1, hy2⟩ := hms y hy
    obtain ⟨hz1, hz2⟩ := (hk y.1 y.2 hy1).1 z hz
    exact ⟨hz1, hy2.trans hz2⟩
  · set c : ℝ≥0∞ := (2 ^ 128 : ℝ≥0∞)⁻¹
    set κ := fun q : (SigningHitLaneProof.LoggedState C × Monitor) × σ => logKeyed keyOf q.1.1.2
    simp only [StateT.run_bind, tsum_probOutput_bind_mul]
    calc _ ≤ ∑' y, Pr[= y | m.run p] * (y.2.1.2.risk + c * ∑' z, Pr[= z | (k y.1).run y.2] *
            ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞)) :=
          tsum_le_of_support _ _ _ fun y hy => (hk y.1 y.2 (hms y hy).1).2
      _ = ∑' y, Pr[= y | m.run p] * y.2.1.2.risk + c * ∑' y, Pr[= y | m.run p] *
            ∑' z, Pr[= z | (k y.1).run y.2] * ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞) := by
          simp only [mul_add, ENNReal.tsum_add]
          congr 1
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun y => by ring
      _ ≤ p.1.2.risk + c * ∑' y, Pr[= y | m.run p] * ((κ y.2 - κ p : ℕ) : ℝ≥0∞) + c * ∑' y, Pr[= y | m.run p] *
            ∑' z, Pr[= z | (k y.1).run y.2] * ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞) := by
          gcongr
      _ = p.1.2.risk + c * ∑' y, Pr[= y | m.run p] * (((κ y.2 - κ p : ℕ) : ℝ≥0∞) +
            ∑' z, Pr[= z | (k y.1).run y.2] * ((κ z.2 - κ y.2 : ℕ) : ℝ≥0∞)) := by
          rw [add_assoc, ← mul_add, ← ENNReal.tsum_add]
          simp only [mul_add]
      _ = _ := by
          congr 2
          refine tsum_eq_of_support _ _ _ fun y hy => ?_
          rw [← tsum_probOutput_mul_const_add]
          refine tsum_eq_of_support _ _ _ fun z hz => ?_
          have h1 := (hms y hy).2
          have h2 := ((hk y.1 y.2 (hms y hy).1).1 z hz).2
          rw [← Nat.cast_add]
          congr 1
          change κ y.2 - κ p + (κ z.2 - κ y.2) = κ z.2 - κ p
          change κ p ≤ κ y.2 at h1
          change κ y.2 ≤ κ z.2 at h2
          omega

/-- A world call raises the risk of the R1 monitor by at most `2^-128` at an encoding input. This is
`logged_risk_le` with every logged call as a query. -/
theorem logged_query_risk_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (t : (WorldSpec C).Domain) (l : SigningHitLaneProof.LoggedState C) (m : Monitor) (hcov : CacheSeen l.1.1 m)
    (ht : ¬SigningHitLaneProof.IsProgram t) :
    ∑' z, Pr[= z | (SigningCostProof.loggedImpl prims t).run l] * (queryEntryStep keyOf m (hashEntry ⟨t, z.1⟩)).risk ≤
      m.risk + (2 ^ 128 : ℝ≥0∞)⁻¹ * (keyedCost keyOf t : ℝ≥0∞) := by
  simp only [SigningCostProof.loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    tsum_probOutput_map_mul]
  have hconst : ∀ {α : Type} (mx : ProbComp α) (F : α → ℝ≥0∞), (∀ w, F w = m.risk) →
      ∑' w, Pr[= w | mx] * F w ≤ m.risk + (2 ^ 128 : ℝ≥0∞)⁻¹ * (keyedCost keyOf t : ℝ≥0∞) :=
    fun mx F hF => (tsum_probOutput_mul_le_of_const mx F _ fun w _ => (hF w).le).trans le_self_add
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · exact hconst _ _ fun w => rfl
  · cases q
    all_goals exact randomOracle_risk_le keyOf _ false l.1.1 m hcov
  · exact hconst _ _ fun w => rfl
  · exact (ht trivial).elim
  · exact hconst _ _ fun w => rfl
  · cases q
    all_goals exact randomOracle_risk_le keyOf _ false l.1.1 m hcov
  · exact hconst _ _ fun w => rfl

/-- A world call keeps every cached input seen by the R1 monitor. This is `covered_step` with every
logged call as a query. -/
theorem logged_query_cacheSeen (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (t : (WorldSpec C).Domain) (l : SigningHitLaneProof.LoggedState C) (m : Monitor) (hcov : CacheSeen l.1.1 m)
    (ht : ¬SigningHitLaneProof.IsProgram t) (r : (WorldSpec C).Range t × SigningHitLaneProof.LoggedState C)
    (hr : r ∈ support ((SigningCostProof.loggedImpl prims t).run l)) :
    CacheSeen r.2.1.1 (queryEntryStep keyOf m (hashEntry ⟨t, r.1⟩)) := by
  obtain ⟨w, hw, h1, hcache, -⟩ := loggedImpl_support prims t l r hr
  intro input hin
  rw [hcache] at hin
  rw [h1]
  have hsub : ∀ entry, m.seen ⊆ (m.after keyOf entry).seen := by
    intro entry
    cases entry with
    | none => exact le_rfl
    | some entry => exact (Set.subset_insert _ _).trans (Monitor.step_seen keyOf _ entry)
  have hq : ∀ (q : Query C) (v : HashOutput),
      (v, w.2) ∈ support (((Query C →ₒ HashOutput).randomOracle q).run l.1.1) →
      input ∈ (m.after keyOf (queryEntry q v false)).seen := by
    intro q v hv
    by_cases he : q = .hash input
    · subst he
      exact Monitor.step_seen keyOf m (input, XmssSecurity.truncateHash v, false) (Set.mem_insert _ _)
    · have hc := randomOracle_cache_ne q l.1.1 (v, w.2) hv (.hash input) (Ne.symm he)
      exact hsub _ (hcov input (hc ▸ hin))
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change w ∈ support ((fun u => (u, l.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hw
    rw [support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact hcov input hin
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run l.1.1) at hw
    cases q
    all_goals exact hq _ w.1 hw
  · change w ∈ support ((prgAnswer prims p).run l.1.1) at hw
    simp only [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure] at hw
    obtain ⟨x, hx, hw⟩ := Set.mem_iUnion₂.1 hw
    have hw2 : w.2 = x.2 := congrArg Prod.snd (show w = _ from hw)
    have hc := randomOracle_cache_ne _ l.1.1 x hx (.hash input) (by simp)
    rw [hw2, hc] at hin
    exact hcov input hin
  · exact (ht trivial).elim
  · change w ∈ support ((fun u => (u, l.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hw
    rw [support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact hcov input hin
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run l.1.1) at hw
    cases q
    all_goals exact hq _ w.1 hw
  · change w ∈ support ((prgAnswer prims p).run l.1.1) at hw
    simp only [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure] at hw
    obtain ⟨x, hx, hw⟩ := Set.mem_iUnion₂.1 hw
    have hw2 : w.2 = x.2 := congrArg Prod.snd (show w = _ from hw)
    have hc := randomOracle_cache_ne _ l.1.1 x hx (.hash input) (by simp)
    rw [hw2, hc] at hin
    exact hcov input hin

/-- A world call of the R1 monitor pays `2^-128` for each keyed call, and its grind pays nothing. -/
theorem potStep_monitoredWorld (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit)
    (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t) :
    PotStep keyOf (monitoredWorld prims keyOf extra t) := by
  intro p hp
  have hcarry : ∀ z ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (p.1.1, p.2)),
      ∃ r ∈ support ((SigningCostProof.loggedImpl prims t).run p.1.1), z = (r.1, (r.2, p.2)) := by
    intro z hz
    simp only [carry, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact ⟨r, hr, rfl⟩
  have hfinal : ∀ z ∈ support ((monitoredWorld prims keyOf extra t).run p),
      CacheSeen z.2.1.1.1.1 z.2.1.2 ∧ logKeyed keyOf z.2.1.1.2 = logKeyed keyOf p.1.1.2 + keyedCost keyOf t := by
    intro z hz
    simp only [monitoredWorld, StateT.run_mk, mem_support_bind_iff, support_map, Set.mem_image] at hz
    obtain ⟨y, hy, v, hv, rfl⟩ := hz
    obtain ⟨r, hr, rfl⟩ := hcarry y hy
    refine ⟨monitoredOracle_run_cacheSeen keyOf _ _ (logged_query_cacheSeen prims keyOf t p.1.1 p.1.2 hp ht r hr) v hv,
      ?_⟩
    change logKeyed keyOf r.2.2 = _
    rw [SigningHitLaneProof.loggedImpl_log prims t p.1.1 r hr, logKeyed_logQuery]
  refine ⟨fun z hz => ⟨(hfinal z hz).1, (hfinal z hz).2 ▸ Nat.le_add_right _ _⟩, ?_⟩
  have hcost : ∑' z, Pr[= z | (monitoredWorld prims keyOf extra t).run p] *
      ((logKeyed keyOf z.2.1.1.2 - logKeyed keyOf p.1.1.2 : ℕ) : ℝ≥0∞) = (keyedCost keyOf t : ℝ≥0∞) := by
    rw [tsum_eq_of_support _ _ (fun _ => (keyedCost keyOf t : ℝ≥0∞) + 0) fun z hz => by
        rw [(hfinal z hz).2, Nat.add_sub_cancel_left, add_zero],
      tsum_probOutput_mul_const_add]
    simp
  rw [hcost]
  simp only [monitoredWorld, StateT.run_mk, tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
  calc _ ≤ ∑' y, Pr[= y | (carry (SigningCostProof.loggedImpl prims) t).run (p.1.1, p.2)] *
          (queryEntryStep keyOf p.1.2 (hashEntry ⟨t, y.1⟩)).risk := by
        refine tsum_le_of_support _ _ _ fun y hy => ?_
        obtain ⟨r, hr, rfl⟩ := hcarry y hy
        exact monitoredOracle_run_risk_le keyOf _ _
          (logged_query_cacheSeen prims keyOf t p.1.1 p.1.2 hp ht r hr)
    _ ≤ _ := by
        simp only [carry, StateT.run_mk, tsum_probOutput_map_mul]
        exact logged_query_risk_le prims keyOf t p.1.1 p.1.2 hp ht

theorem potStep_simulateQ_world (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (W : QueryImpl (WorldSpec C) (StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → PotStep keyOf (W t)) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (h : SigningHitProof.ProgramFree oa) : PotStep keyOf (simulateQ W oa) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x => exact potStep_pure keyOf x
  | query_bind t k ih =>
    have hb := (isQueryBoundP_query_bind_iff SigningHitLaneProof.IsProgram t k 0).mp h
    have ht : ¬SigningHitLaneProof.IsProgram t := by simpa using hb.1
    have hk : ∀ u, SigningHitProof.ProgramFree (k u) := by
      simpa [SigningHitProof.ProgramFree, ht] using hb.2
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact potStep_bind keyOf (hW t ht) fun u => ih u (hk u)

theorem potStep_simulateQ (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {ι : Type}
    {spec : OracleSpec ι}
    (V : QueryImpl spec (StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp))
    (hV : ∀ t, PotStep keyOf (V t)) {α : Type} (oa : OracleComp spec α) : PotStep keyOf (simulateQ V oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact potStep_pure keyOf x
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact potStep_bind keyOf (hV t) ih

theorem potStep_flatWith (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {ι : Type}
    {spec : OracleSpec ι} (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (hfree : ∀ t s, SigningHitProof.ProgramFree ((outer t).run s))
    (W : QueryImpl (WorldSpec C) (StateT ((SigningHitLaneProof.LoggedState C × Monitor) × σ) ProbComp))
    (hW : ∀ t, ¬SigningHitLaneProof.IsProgram t → PotStep keyOf (W t)) (t : spec.Domain) :
    PotStep keyOf (flatWith outer W t) := by
  intro p hp
  obtain ⟨hs, hr⟩ := potStep_simulateQ_world keyOf W hW _ (hfree t p.2) p hp
  simp only [flatWith, StateT.run_mk, support_map, Set.mem_image, tsum_probOutput_map_mul]
  refine ⟨?_, hr⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hs z hz

theorem potStep_getCarried (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    PotStep (C := C) keyOf (getCarried (σ := σ)) := by
  intro p hp
  simpa [getCarried] using potStep_pure (C := C) keyOf p.2 p hp

set_option maxRecDepth 100000 in
/-- The flat eager run with the R1 monitor pays `2^-128` for each keyed call. -/
theorem potStep_monitoredGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    PotStep keyOf (monitoredGame prims keyOf extra A x) := by
  unfold monitoredGame gameWith
  dsimp only
  have hW := potStep_monitoredWorld prims (σ := TsigState C × Bool) keyOf extra
  have hsetup : SigningHitProof.ProgramFree (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  refine potStep_bind keyOf (potStep_simulateQ_world keyOf _ hW _ hsetup) fun r => ?_
  rcases r with _ | (top | tree)
  · exact potStep_pure keyOf _
  · refine potStep_bind keyOf (potStep_simulateQ keyOf _
      (fun t => potStep_flatWith keyOf _ (SigningHitProof.programFree_flaggedOracles x top) _ hW t) _) fun a => ?_
    refine potStep_bind keyOf (potStep_getCarried keyOf) fun s => ?_
    refine potStep_bind keyOf (potStep_simulateQ_world keyOf _ hW _ (SigningHitProof.programFree_finish x top _))
      fun w => ?_
    exact potStep_pure keyOf _
  · exact potStep_pure keyOf _

end Potential

section Bound

open SigningPartnerBoundProof ENNReal

variable {C : Committee} (prims : Primitives)

/-- The initial state of the flat eager run with the R1 monitor. -/
def monitoredInit : (SigningHitLaneProof.LoggedState C × Monitor) × (TsigState C × Bool) :=
  ((SigningHitLaneProof.loggedInit, Monitor.empty), (SigningCoreProof.tsigInit, false))

/-- The flat eager run with the R1 monitor. -/
def monitoredRun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (Result C × (SigningHitLaneProof.LoggedState C × Monitor) × (TsigState C × Bool)) :=
  (monitoredGame prims keyOf (grindExtra P ρ) A x).run monitoredInit

/-- The hit of the R1 monitor. The grind at the base call installs the selected digest of a fresh
selection as the target of its key. A query at the key with a valid digest before the base call
is pending risk. -/
def R1Hit (z : Result C × (SigningHitLaneProof.LoggedState C × Monitor) × (TsigState C × Bool)) : Prop :=
  z.2.1.2.hit = true

theorem monitoredRun_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> monitoredRun prims keyOf P ρ A x = flatEagerRun prims P ρ A x :=
  monitoredGame_forgets prims keyOf (grindExtra P ρ) A x _ _ _

/-- The hit costs `2^-128` for each keyed call of the log in expectation. -/
theorem probEvent_r1Hit_le_logKeyed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[R1Hit | monitoredRun prims keyOf P ρ A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' z, Pr[= z | monitoredRun prims keyOf P ρ A x] *
        (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) := by
  classical
  have hinit : CacheSeen (monitoredInit (C := C)).1.1.1.1 (monitoredInit (C := C)).1.2 :=
    fun input h => (h rfl).elim
  have h := (potStep_monitoredGame prims keyOf (grindExtra P ρ) A x monitoredInit hinit).2
  have hrisk : (monitoredInit (C := C)).1.2.risk = 0 := by
    simp [monitoredInit, Monitor.risk, Monitor.empty, XmssSecurity.CappedEncodingMonitor.State.pendingRisk_empty]
  have hlog : logKeyed keyOf (monitoredInit (C := C)).1.1.2 = 0 := rfl
  rw [hrisk, zero_add, hlog] at h
  simp only [Nat.sub_zero] at h
  refine le_trans ?_ h
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun z => ?_
  split_ifs with hz
  · have hone : z.2.1.2.risk = 1 := by simp [Monitor.risk, show z.2.1.2.hit = true from hz]
    rw [hone, mul_one]
    exact le_rfl
  · exact bot_le

/-- The keyed calls of the log of the flat eager run have the law of those of `loggedRun`. -/
theorem expected_logKeyed_eq (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr[= z | monitoredRun prims keyOf P ρ A x] * (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) =
      ∑' z, Pr[= z | SigningCostProof.loggedRun prims A x] * (logKeyed keyOf z.2.2 : ℝ≥0∞) := by
  have h1 := tsum_probOutput_map_mul (monitoredRun prims keyOf P ρ A x) (fun z => (z.1, (z.2.1.1, z.2.2)))
    (fun y => (logKeyed keyOf y.2.1.2 : ℝ≥0∞))
  rw [monitoredRun_forget] at h1
  have h2 := tsum_probOutput_map_mul (flatEagerRun prims P ρ A x) (fun z => (z.1, z.2.1.1.2, z.2.1.2))
    (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have h3 := tsum_probOutput_map_mul (SigningCostProof.loggedRun prims A x) (fun z => (z.1, z.2.1.2, z.2.2))
    (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have hlaw := evalDist_flatEagerRun_logged prims P ρ A x
  rw [← h1, ← h3, ← h2]
  exact tsum_congr fun y => by rw [probOutput_congr rfl hlaw]

/-- The keyed calls of the log of `loggedRun` in expectation are the expected keyed cost. -/
theorem expected_logKeyed_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr[= z | SigningCostProof.loggedRun prims A x] * (logKeyed keyOf z.2.2 : ℝ≥0∞) ≤
      SigningGuessProof.sourceExpectedCost prims A x (keyedCost keyOf) := by
  have h := XmssSecurity.expectedFinal_le (SigningCostProof.loggedImpl prims) (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun s => (logKeyed keyOf s.2 : ℝ≥0∞)) (fun t _ => (keyedCost keyOf t : ℝ≥0∞))
    (fun t s _ => by
      rw [tsum_eq_of_support _ _ (fun _ => (logKeyed keyOf s.2 + keyedCost keyOf t : ℝ≥0∞) + 0) fun r hr => by
          rw [SigningHitLaneProof.loggedImpl_log prims t s r hr, logKeyed_logQuery, add_zero, Nat.cast_add],
        tsum_probOutput_mul_const_add]
      simp)
    (SigningDescentProof.finalRun A x) SigningHitLaneProof.loggedInit trivial
  have hzero : logKeyed keyOf (SigningHitLaneProof.loggedInit (C := C)).2 = 0 := rfl
  rw [hzero, Nat.cast_zero, zero_add] at h
  exact h

/-- The bound of R1. The hit of the R1 monitor on the flat eager run costs `2^-128` for each bottom
digest call, as `bottomPartnerLogged_bound`. -/
theorem r1Hit_bound (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    Pr[R1Hit | monitoredRun prims (XmssSecurity.encodingInputLeafIndex? x.1) P ρ A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine (probEvent_r1Hit_le_logKeyed prims _ P ρ A x).trans ?_
  rw [expected_logKeyed_eq]
  gcongr
  exact (expected_logKeyed_le prims _ A x).trans
    (SigningGuessProof.sourceExpectedCost_mono prims A x _ _ (keyedCost_le_bottomDigestCost x))

end Bound

section Split

open SigningPartnerBoundProof ENNReal

variable {C : Committee} (prims : Primitives) {σ : Type}

open Classical in
/-- A trial at an unsigned key whose input is seen and whose digest is valid. In the first grind
at a key this is a selection that the log holds before the base call, the split of R1. -/
def cachedTrial (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor) (q : Query C)
    (output : HashOutput) : Bool :=
  match q with
  | .hash input => decide (input ∈ m.seen ∧ ∃ e, keyOf input = some e ∧ m.state.signed e = none ∧
      XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash output))
  | _ => false

/-- `monitoredOracle` with a write-only flag for a cached trial. -/
def splitOracle (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    QueryImpl (Query C →ₒ HashOutput) (StateT ((HashCache C × Monitor) × Bool) ProbComp) :=
  fun q => StateT.mk fun s => (fun w => (w.1, (w.2, s.2 || cachedTrial keyOf s.1.2 q w.1))) <$>
    (monitoredOracle keyOf q).run s.1

theorem splitOracle_run_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {β : Type}
    (ob : OracleComp (Query C →ₒ HashOutput) β) (s : HashCache C × Monitor) (b : Bool) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (splitOracle keyOf) ob).run (s, b) =
      (simulateQ (monitoredOracle keyOf) ob).run s :=
  SigningCoreProof.simulateQ_run_forget _ _ (fun q c b => by
    simp only [splitOracle, StateT.run_mk, Functor.map_map]
    exact id_map _) ob s b

/-- `monitoredWorld` with the flag of a cached trial. -/
def splitWorld (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit) :
    QueryImpl (WorldSpec C) (StateT (((SigningHitLaneProof.LoggedState C × Monitor) × Bool) × σ) ProbComp) :=
  fun t => StateT.mk fun p => (carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1, p.2) >>= fun z =>
    (fun y => (z.1, ((((ofRest y.2.1.1 (restOf z.2)).1, y.2.1.2), y.2.2), (ofRest y.2.1.1 (restOf z.2)).2))) <$>
      (simulateQ (splitOracle keyOf) (extra (p.1.1.1, p.2) t z.2)).run
        ((z.2.1.1.1, queryEntryStep keyOf p.1.1.2 (hashEntry ⟨t, z.1⟩)), p.1.2)

theorem splitWorld_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : SigningHitLaneProof.LoggedState C × σ → (WorldSpec C).Domain →
      SigningHitLaneProof.LoggedState C × σ → OracleComp (Query C →ₒ HashOutput) Unit)
    (t : (WorldSpec C).Domain) : Forgets (splitWorld prims keyOf extra t) (monitoredWorld prims keyOf extra t) := by
  intro a b s
  simp only [splitWorld, monitoredWorld, StateT.run_mk, map_bind, Functor.map_map]
  refine bind_congr fun z => ?_
  rw [← splitOracle_run_forget keyOf _ _ b, Functor.map_map]

/-- The flat eager run with the R1 monitor and the flag of a cached trial. -/
def splitGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT (((SigningHitLaneProof.LoggedState C × Monitor) × Bool) × (TsigState C × Bool)) ProbComp (Result C) :=
  gameWith A x (splitWorld prims keyOf extra)
    (fun dealt => flatWith (SigningCoreProof.flaggedOracles x dealt) (splitWorld prims keyOf extra)) getCarried

theorem splitGame_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (splitGame prims keyOf extra A x) (monitoredGame prims keyOf extra A x) := by
  unfold splitGame monitoredGame gameWith
  dsimp only
  have hW := splitWorld_forgets prims keyOf extra
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

/-- The flat eager run with the R1 monitor and the flag of a cached trial. -/
def splitRun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (Result C × ((SigningHitLaneProof.LoggedState C × Monitor) × Bool) × (TsigState C × Bool)) :=
  (splitGame prims keyOf (grindExtra P ρ) A x).run ((monitoredInit.1, false), monitoredInit.2)

/-- The flag is write-only, so the split run gives `monitoredRun` exactly. -/
theorem splitRun_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> splitRun prims keyOf P ρ A x = monitoredRun prims keyOf P ρ A x :=
  splitGame_forgets prims keyOf (grindExtra P ρ) A x _ _ _

/-- The split of R1. A grind at a base call met a selection that the log holds before the call. -/
def CachedSelection (z : Result C × ((SigningHitLaneProof.LoggedState C × Monitor) × Bool) × (TsigState C × Bool)) :
    Prop :=
  z.2.1.2 = true

/-- Step 3 of R1, open. A bottom partner win with no cached selection raises the R1 monitor, unless
`ρ` comes from a commitment collision. `ρ x` must be the honest openings of `x`. The win reads the
final cache of the eager run. -/
def R1Link (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest) : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z,
    z ∈ support (splitRun prims (XmssSecurity.encodingInputLeafIndex? x.1) x.1 (ρ x) A x) →
    z.1.1 = (true, false) → SigningPartnerLinkProof.BottomPartnerCase prims x (z.1, z.2.1.1.1.1) →
    ¬CachedSelection z →
    z.2.1.1.2.hit = true ∨ SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1

/-- The bound of R1 on the split run. -/
theorem split_r1Hit_bound (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    Pr[fun z => z.2.1.1.2.hit = true | splitRun prims (XmssSecurity.encodingInputLeafIndex? x.1) P ρ A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine le_trans (le_of_eq ?_) (r1Hit_bound prims P ρ A x)
  rw [← splitRun_forget, probEvent_map]
  rfl

end Split

end SigningFlatEagerProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatEagerProof.evalDist_flatEagerRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatEagerProof.evalDist_flatEagerRun

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatEagerProof.evalDist_flatEagerRun_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatEagerProof.evalDist_flatEagerRun_logged

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatEagerProof.r1Hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatEagerProof.r1Hit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatEagerProof.monitoredRun_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatEagerProof.monitoredRun_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatEagerProof.split_r1Hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatEagerProof.split_r1Hit_bound
