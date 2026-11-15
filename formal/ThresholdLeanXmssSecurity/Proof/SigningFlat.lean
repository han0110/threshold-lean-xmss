import ThresholdLeanXmssSecurity.Proof.SigningEagerGrind
import ThresholdLeanXmssSecurity.Proof.SigningReleased

/-!
# The flat run of the signing game

One handler answers the calls of the forger and the world calls, so a potential can read `bound e`
at each call.

## The flat handler

* `flat outer inner` runs each call of `outer` with its world calls under `carry inner`. A world call
  carries the state of `outer` from the start of the call of `outer`.
* `flat_run` shows that the flat run is the layered run.
* `flatOracles` is `flat` of `flaggedOracles` over `loggedImpl`. Its state holds the cache, the count,
  the call log, the `TsigState` and the flag.
* `flatRun` runs `finalRun` with `flatWorld` for the setup and the finish, and with `flatOracles` for
  the forger. `flatRun_logged` gives `loggedRun` exactly.
* `flatJointRun` does the same for `verifyFinal` with `openingOracles`. `flatJointRun_eq` gives
  `jointRun` exactly.

In a call of `round1`, the world calls carry the state before the call, so `bound e` is still the
old value there. These calls are the `prf` and `mask` calls of `eval`, and none is a call of `.hash`.
No other signing oracle changes `bound` before its world calls.

## One canonical base call for each key

* `baseInput P e ρ st` is `randomizerInput P bottomLayer e ρ (bytesLE 32 m)` when `st.bound e = some m`.
* `BaseCall` is a call of `H` at this input, on the counted copy or on the free copy.
* `countImpl_hash_cached` shows that a call of `H` on either copy caches its input.

## The hash form and the eager grind

* `signingLocalAnswer_eq` shows that the local oracles are private sampling and one lazy `H`, then
  a fixed function. A `PRG` call is the `H` call on its stream key, then AES-128.
* `signImpl_simulateQ` shows that a run with no programming query is a run of `mixedOracle`. It uses
  `programFree_simulate_local` of `SigningHitProof`.
* The presample lemmas of leanVM have no private sampling. This module ports them to
  `mixedOracle`. A private sample commutes with the presample.

## The reuse of leanVM

`evalDist_mixed_run_eq_presample_of_cached` and `evalDist_mixed_run_eq_query_then_of_cached` port
`OracleComp.evalDist_randomOracle_run_eq_presample_of_cached` and
`OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached`
(`XmssSecurity/Proof/RandomOraclePresampling.lean`). `XmssSecurity.Seeded.evalDist_presample_fresh`
has private sampling, but only on the fixed domain `HashSpec` of leanVM.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningFlatProof

open HashSig LeanXmss ThresholdLeanXmss

section Compose

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ τ : Type}

/-- `inner` with a second part `σ` of the state that its calls carry unchanged. -/
def carry (inner : QueryImpl spec' (StateT τ ProbComp)) : QueryImpl spec' (StateT (τ × σ) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1, (z.2, p.2))) <$> (inner t).run p.1

/-- One handler for `outer` over `inner`. A call of `outer` runs its calls of `spec'` under `carry inner`,
which reads the state of `outer` at the start of the call. -/
def flat (outer : QueryImpl spec (StateT σ (OracleComp spec'))) (inner : QueryImpl spec' (StateT τ ProbComp)) :
    QueryImpl spec (StateT (τ × σ) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1.1, (z.2.1, z.1.2))) <$> (simulateQ (carry inner) ((outer t).run p.2)).run p

theorem carry_run (inner : QueryImpl spec' (StateT τ ProbComp)) {α : Type} (oa : OracleComp spec' α) (u : τ)
    (s : σ) :
    (simulateQ (carry inner) oa).run (u, s) = (fun z => (z.1, (z.2, s))) <$> (simulateQ inner oa).run u := by
  induction oa using OracleComp.inductionOn generalizing u with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, carry, StateT.run_mk, bind_map_left, map_bind, ih]

theorem carry_run_pair (inner : QueryImpl spec' (StateT τ ProbComp)) {α : Type} (oa : OracleComp spec' α)
    (p : τ × σ) :
    (simulateQ (carry inner) oa).run p = (fun z => (z.1, (z.2, p.2))) <$> (simulateQ inner oa).run p.1 :=
  carry_run inner oa p.1 p.2

/-- The flat run is the layered run. -/
theorem flat_run (outer : QueryImpl spec (StateT σ (OracleComp spec'))) (inner : QueryImpl spec' (StateT τ ProbComp))
    {α : Type} (oa : OracleComp spec α) (u : τ) (s : σ) :
    (fun z => ((z.1, z.2.2), z.2.1)) <$> (simulateQ (flat outer inner) oa).run (u, s) =
      (simulateQ inner ((simulateQ outer oa).run s)).run u := by
  induction oa using OracleComp.inductionOn generalizing u s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, flat, StateT.run_mk, carry_run, bind_map_left, map_bind, ih]

end Compose

section Run

variable {C : Committee} (prims : Primitives)

/-- The state of the flat run. It holds the hash cache, the count, the call log, the state of the
signing oracles and the flag. -/
abbrev FlatState (C : Committee) := SigningHitLaneProof.LoggedState C × (TsigState C × Bool)

/-- The world calls of the flat run. Each call carries the state of the signing oracles. -/
def flatWorld : QueryImpl (WorldSpec C) (StateT (FlatState C) ProbComp) :=
  carry (SigningCostProof.loggedImpl prims)

/-- The flat handler. It answers each call of the forger, a signing oracle or a world call, under
`flatWorld`. -/
def flatOracles (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (FlatState C) ProbComp) :=
  flat (SigningCoreProof.flaggedOracles x dealt) (SigningCostProof.loggedImpl prims)

/-- `finalRun` under one flat handler for each stage. -/
def flatRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × FlatState C) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let r ← (simulateQ (flatWorld prims) (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
    value x.1 emptyTop .top)).run (SigningHitLaneProof.loggedInit, (SigningCoreProof.tsigInit, false))
  match r.1 with
  | some (.top top) =>
    let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
    let f ← (fun z => ((z.1, z.2.2), z.2.1)) <$>
      (simulateQ (flatOracles prims x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run r.2
    let w ← (simulateQ (flatWorld prims) (SigningCoreProof.tsigFinish dealt (f.1.1, f.1.2.1))).run (f.2, f.1.2)
    pure (((w.1.1, f.1.2.2), some (top, w.1.2.1, w.1.2.2)), w.2)
  | _ => pure (((false, false), none), r.2)

/-- The flat run forgets the state of the signing oracles and gives `loggedRun` exactly. -/
theorem flatRun_logged (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, z.2.1)) <$> flatRun prims A x = SigningCostProof.loggedRun prims A x := by
  unfold flatRun SigningCostProof.loggedRun SigningDescentProof.finalRun
  dsimp only
  rw [simulateQ_bind, StateT.run_bind, flatWorld, carry_run, bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  rcases z with ⟨_ | (top | tree), l⟩
  · simp
  · dsimp only
    rw [flatOracles, flat_run, simulateQ_bind, StateT.run_bind, map_bind]
    refine bind_congr fun f => ?_
    simp [carry_run, Functor.map_map]
  · simp

/-- The state of the flat joint run. It adds the opened trees and the unreleased candidates of
`openingOracles`. -/
abbrev FlatJointState (C : Committee) :=
  SigningHitLaneProof.LoggedState C ×
    ((TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (SigningOpeningProof.HiddenKey × Digest))

/-- The flat handler over `openingOracles`. -/
def flatOpening (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (FlatJointState C) ProbComp) :=
  flat (SigningOpeningProof.openingOracles x dealt) (SigningCostProof.loggedImpl prims)

/-- `verifyFinal` under one flat handler for each stage. -/
def flatJointRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp ((((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) ×
      List (SigningOpeningProof.HiddenKey × Digest)) × SigningHitLaneProof.LoggedState C) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let r ← (simulateQ (SigningCostProof.loggedImpl prims) (referenceTree
    (fun oa => SigningSecurityProof.liftFree (tweakable oa)) value x.1 emptyTop .top)).run
      SigningHitLaneProof.loggedInit
  match r.1 with
  | some (.top top) =>
    let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
    let f ← (fun z => ((z.1, z.2.2), z.2.1)) <$>
      (simulateQ (flatOpening prims x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
        (r.2, ((SigningCoreProof.tsigInit, false), ∅, []))
    let w ← (simulateQ (SigningCostProof.loggedImpl prims)
      (SigningGuessLinkProof.tsigFinishLogged dealt f.1.2.2.1 (f.1.1, f.1.2.1.1))).run f.2
    pure ((((w.1.1.1, f.1.2.1.2), some (top, w.1.1.2)), f.1.2.2.2 ++ w.1.2), w.2)
  | _ => pure ((((false, false), none), []), r.2)

/-- The flat joint run is `jointRun` exactly. -/
theorem flatJointRun_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    flatJointRun prims A x = SigningUnchargedLoggedProof.jointRun prims A x := by
  unfold flatJointRun SigningUnchargedLoggedProof.jointRun SigningGuessLinkProof.verifyFinal
  dsimp only
  rw [simulateQ_bind, StateT.run_bind]
  refine bind_congr fun z => ?_
  rcases z with ⟨_ | (top | tree), l⟩
  · simp
  · dsimp only
    rw [flatOpening, flat_run, simulateQ_bind, StateT.run_bind]
    refine bind_congr fun f => ?_
    simp
  · simp

end Run

section Base

variable {C : Committee} (prims : Primitives)

/-- A call of `H` at `input`, on the counted copy or on the free copy. -/
def HashCallAt (input : HashInput) (t : (WorldSpec C).Domain) : Prop :=
  t = .inl (.inl (.inr (.inl (.hash input)))) ∨ t = .inr (.inr (.inl (.hash input)))

/-- The canonical base input of key `e` at the state `st`. It carries the bound message. -/
def baseInput (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (st : TsigState C) : Option HashInput :=
  (st.bound e).map fun message => randomizerInput P bottomLayer e ρ (littleEndianBytes 32 message)

/-- A canonical base call of key `e` at the state `st`. -/
def BaseCall (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (st : TsigState C) (t : (WorldSpec C).Domain) :
    Prop :=
  ∃ input, baseInput P e ρ st = some input ∧ HashCallAt input t

/-- A call of `H` on either copy caches its input. -/
theorem countImpl_hash_cached (input : HashInput) (t : (WorldSpec C).Domain) (ht : HashCallAt input t)
    (s : HashCache C × ℕ) (w : (WorldSpec C).Range t × HashCache C × ℕ)
    (hw : w ∈ support ((SigningCacheProof.countImpl prims t).run s)) : ∃ output, w.2.1 (.hash input) = some output := by
  rcases ht with rfl | rfl
  all_goals
    simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map,
      Set.mem_image] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact ⟨r.1, (randomOracle_support _ s.1 r hr).2.1⟩

end Base

section MixedEager

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- Private sampling and the lazy random oracle on `D →ₒ R`. -/
abbrev mixedOracle : QueryImpl (unifSpec + (D →ₒ R)) (StateT (D →ₒ R).QueryCache ProbComp) :=
  unifFwdImpl (D →ₒ R) + randomOracle (spec := D →ₒ R)

theorem mixed_run_inl {α : Type} (n : ℕ) (next : Fin (n + 1) → OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) :
    (simulateQ (mixedOracle (D := D) (R := R)) (liftM ((unifSpec + (D →ₒ R)).query (.inl n)) >>= next)).run cache =
      (liftM (unifSpec.query n) : ProbComp _) >>= fun u => (simulateQ mixedOracle (next u)).run cache := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp [mixedOracle, unifFwdImpl]

theorem mixed_run_inr {α : Type} (d : D) (next : R → OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) :
    (simulateQ (mixedOracle (D := D) (R := R)) (liftM ((unifSpec + (D →ₒ R)).query (.inr d)) >>= next)).run cache =
      (randomOracle (spec := D →ₒ R) d).run cache >>= fun r => (simulateQ mixedOracle (next r.1)).run r.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

/-- `OracleComp.evalDist_randomOracle_run_eq_presample_of_cached` of leanVM
(`XmssSecurity/Proof/RandomOraclePresampling.lean`) with private sampling. The hash steps follow
that proof. A private sample commutes with the presample. -/
theorem evalDist_mixed_run_eq_presample_of_cached {α : Type} (computation : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) (target : D) (habsent : cache target = none)
    (hcached : ∀ result ∈ support ((simulateQ mixedOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    (simulateQ mixedOracle computation).run cache =ᵈ
      (do
        let value ← $ᵗ R
        (simulateQ mixedOracle computation).run (cache.cacheQuery target value)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      exfalso
      obtain ⟨output, houtput⟩ := hcached (value, cache) (by simp)
      change cache target = some output at houtput
      rw [habsent] at houtput
      simp at houtput
  | query_bind input next ih =>
    rcases input with n | input
    · simp only [mixed_run_inl] at hcached ⊢
      have hnextCached : ∀ u, ∀ result ∈ support ((simulateQ mixedOracle (next u)).run cache),
          ∃ output, result.2 target = some output := by
        intro u result hresult
        apply hcached result
        rw [mem_support_bind_iff]
        exact ⟨u, by simp, hresult⟩
      refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
      exact EvalDistEq.bind_right _ fun u => ih u cache habsent (hnextCached u)
    · have hrun := fun initialCache => mixed_run_inr (D := D) (R := R) input next initialCache
      by_cases htarget : input = target
      · subst input
        rw [hrun, QueryImpl.withCaching_run_none _ habsent, map_eq_bind_pure_comp]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        refine EvalDistEq.bind_right _ fun sampled => ?_
        rw [hrun, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self cache target sampled), pure_bind]
      · cases hinput : cache input with
        | some answer =>
            rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
            have hnextCached : ∀ result ∈ support ((simulateQ mixedOracle (next answer)).run cache),
                ∃ output, result.2 target = some output := by
              intro result hresult
              apply hcached result
              rw [hrun, mem_support_bind_iff]
              refine ⟨(answer, cache), ?_, hresult⟩
              rw [QueryImpl.withCaching_run_some _ hinput]
              simp
            refine (ih answer cache habsent hnextCached).trans ?_
            refine EvalDistEq.bind_right _ fun sampled => ?_
            have hcachedInput : (cache.cacheQuery target sampled) input = some answer := by
              rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
              exact hinput
            rw [hrun, QueryImpl.withCaching_run_some _ hcachedInput, pure_bind]
        | none =>
            have htargetAfterInput : ∀ answer : R, (cache.cacheQuery input answer) target = none := by
              intro answer
              simpa [QueryCache.cacheQuery_of_ne, Ne.symm htarget] using habsent
            rw [hrun, QueryImpl.withCaching_run_none _ hinput, map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            have hnextCached : ∀ answer : R, ∀ result ∈ support
                ((simulateQ mixedOracle (next answer)).run (cache.cacheQuery input answer)),
                ∃ output, result.2 target = some output := by
              intro answer result hresult
              apply hcached result
              rw [hrun, mem_support_bind_iff]
              refine ⟨(answer, cache.cacheQuery input answer), ?_, hresult⟩
              rw [QueryImpl.withCaching_run_none _ hinput, support_map]
              exact ⟨answer, mem_support_uniformSample R, rfl⟩
            refine (EvalDistEq.bind_right _ fun answer =>
              ih answer (cache.cacheQuery input answer) (htargetAfterInput answer) (hnextCached answer)).trans ?_
            refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
            refine EvalDistEq.bind_right _ fun sampled => ?_
            have hnone : (cache.cacheQuery target sampled) input = none := by
              rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
              exact hinput
            rw [hrun, QueryImpl.withCaching_run_none _ hnone, map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            refine EvalDistEq.bind_right _ fun answer => ?_
            rw [QueryCache.cacheQuery_comm_of_ne cache htarget]

/-- `OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached` of leanVM with private sampling. -/
theorem evalDist_mixed_run_eq_query_then_of_cached {α : Type} (computation : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (hcached : ∀ result ∈ support ((simulateQ mixedOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    (simulateQ mixedOracle computation).run cache =ᵈ
      ((randomOracle (spec := D →ₒ R) target).run cache >>= fun queryResult =>
        (simulateQ mixedOracle computation).run queryResult.2) := by
  cases htarget : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ htarget, map_eq_bind_pure_comp]
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      exact evalDist_mixed_run_eq_presample_of_cached computation cache target htarget hcached
  | some output =>
      rw [QueryImpl.withCaching_run_some _ htarget, pure_bind]

/-- A query whose answer the rest does not use keeps the law of the rest, with private sampling. -/
theorem evalDist_mixed_run'_query_bind_const {α : Type} (target : D) (oa : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) :
    ((randomOracle (spec := D →ₒ R) target).run cache >>= fun q => (simulateQ mixedOracle oa).run' q.2) =ᵈ
      (simulateQ mixedOracle oa).run' cache := by
  set oa' : OracleComp (unifSpec + (D →ₒ R)) α :=
    oa >>= fun a => liftM ((unifSpec + (D →ₒ R)).query (.inr target)) >>= fun _ => pure a
  have hrun : ∀ c, (simulateQ mixedOracle oa').run c = (simulateQ mixedOracle oa).run c >>= fun r =>
      (randomOracle (spec := D →ₒ R) target).run r.2 >>= fun q => pure (r.1, q.2) := by
    intro c
    simp only [oa', simulateQ_bind, StateT.run_bind]
    refine bind_congr fun r => ?_
    rw [simulateQ_spec_query]
    simp only [simulateQ_pure, StateT.run_pure]
    rfl
  have hcached : ∀ c, ∀ result ∈ support ((simulateQ mixedOracle oa').run c),
      ∃ output, result.2 target = some output := by
    intro c result hres
    rw [hrun, mem_support_bind_iff] at hres
    obtain ⟨r, -, hres⟩ := hres
    rw [mem_support_bind_iff] at hres
    obtain ⟨q, hq, hres⟩ := hres
    simp only [support_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact SigningEagerGrindProof.randomOracle_run_cached target r.2 q hq
  have hforget : ∀ c, (simulateQ mixedOracle oa').run' c =ᵈ (simulateQ mixedOracle oa).run' c := by
    intro c
    have hconst : ∀ x : α × (D →ₒ R).QueryCache,
        ((fun x => x.1) <$> ((randomOracle (spec := D →ₒ R) target).run x.2 >>= fun q => pure (x.1, q.2))) =ᵈ
          (pure x.1 : ProbComp α) := by
      intro x
      rw [map_bind]
      simp only [map_pure]
      exact OracleComp.EvalDistEq.bind_const _ _
    rw [StateT.run'_eq, StateT.run'_eq, hrun, map_bind]
    refine (EvalDistEq.bind_right _ hconst).trans (EvalDistEq.of_eq ?_)
    simp [map_eq_bind_pure_comp]
  have hpre := evalDist_mixed_run_eq_query_then_of_cached oa' cache target (hcached cache)
  refine (EvalDistEq.bind_right ((randomOracle (spec := D →ₒ R) target).run cache)
    fun q => (hforget q.2).symm).trans ?_
  refine EvalDistEq.trans ?_ (hforget cache)
  rw [StateT.run'_eq]
  refine EvalDistEq.trans (EvalDistEq.of_eq ?_) (hpre.map Prod.fst).symm
  rw [map_bind]
  rfl

/-- A random oracle run whose answers the rest does not use keeps the law of the rest, with private
sampling in the rest. -/
theorem evalDist_mixed_run'_bind_const {α β : Type} (ob : OracleComp (D →ₒ R) β)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (cache : (D →ₒ R).QueryCache) :
    ((simulateQ randomOracle ob).run cache >>= fun r => (simulateQ mixedOracle oa).run' r.2) =ᵈ
      (simulateQ mixedOracle oa).run' cache := by
  induction ob using OracleComp.inductionOn generalizing cache with
  | pure b => simp
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    refine EvalDistEq.trans ?_ (evalDist_mixed_run'_query_bind_const t oa cache)
    exact EvalDistEq.bind_right _ fun q => ih q.1 q.2

end MixedEager

section HashForm

variable {C : Committee} (prims : Primitives)

/-- The oracles of the hash form, namely private sampling and `H`. -/
abbrev HashSpec (C : Committee) := unifSpec + (Query C →ₒ HashOutput)

/-- A local call as calls of `H`. A call of `PRG` is the call of `H` on its stream key, then the fixed
AES-128. -/
def localQuery : QueryImpl (LocalSpec C) (OracleComp (HashSpec C))
  | .inl n => query (spec := HashSpec C) (.inl n)
  | .inr (.inl q) => query (spec := HashSpec C) (.inr q)
  | .inr (.inr x) => (fun derived => prims.aes.eval (truncateHash derived) x.2.2) <$>
      query (spec := HashSpec C) (.inr (.streamKey x.2.1))

/-- The local oracles of the signing world are private sampling and one lazy random oracle `H`,
then a fixed function. -/
theorem signingLocalAnswer_eq :
    signingLocalAnswer (C := C) prims = mixedOracle ∘ₛ localQuery prims := by
  funext u
  rcases u with n | q | x
  · rfl
  · simp [localQuery, signingLocalAnswer]
  · simp [localQuery, signingLocalAnswer, prgAnswer, hashAnswer, map_eq_bind_pure_comp]

/-- A run of the signing world with no programming query is a run of one lazy random oracle `H`
with private sampling. -/
theorem signImpl_simulateQ {α : Type} (oa : OracleComp (WorldSpec C) α) (h : SigningHitProof.ProgramFree oa) :
    simulateQ (SeedHitProof.signImpl prims) oa =
      simulateQ mixedOracle (simulateQ (localQuery prims) (simulateQ SigningHitProof.worldLocalize oa)) := by
  rw [SigningHitProof.programFree_simulate_local (signingLocalAnswer prims) _ (fun _ => rfl) (fun _ => rfl) oa h,
    signingLocalAnswer_eq, QueryImpl.simulateQ_compose]

end HashForm

end SigningFlatProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.flatRun_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.flatRun_logged

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.flatJointRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.flatJointRun_eq
