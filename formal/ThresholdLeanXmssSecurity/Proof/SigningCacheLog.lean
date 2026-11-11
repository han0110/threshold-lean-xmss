import ThresholdLeanXmssSecurity.Proof.SigningFlatEager
import ThresholdLeanXmssSecurity.Proof.SigningGuardedFlag

/-!
# The cache of the flat run from the call log

## Step 1. The cache from the log

* `hashCall` reads a log entry as a call of `H` with its full answer, on either copy.
* `logCache log` is the first logged answer at each input of `H`.
* `Tracked q` says that `q` is not a stream key. A `PRG` call caches `H` at its stream key, and the
  log holds only the bit, so the log cannot give these points. Every point that a win reads (the
  encoding inputs, the chain inputs, the PRF entries and the commitment inputs) is tracked.
* `cacheFromLog_step` shows that each world call other than a programming query keeps
  `CacheFromLog`, the agreement of the cache with `logCache` at the tracked points.
* `loggedRun_cacheFromLog` and `flatRun_cacheFromLog` give it on every outcome, with
  `SigningHitProof.noProgramQuery`.
* `probEvent_flatRun_eq_flatEagerRun` moves each event that reads the cache only at tracked points
  from `flatRun` to the flat eager run, where it reads `logCache` of the log.

## The deviation of `trialFresh`

* `monitoredOracle_rerun` ports `randomOracle_rerun_largerCache_eq_pure_of_mem_support` of leanVM
  to the trial monitor. With every cached input seen, a rerun changes nothing.
* `baseGrind_rerun` applies it to a grind with a first run below the cache.
* `SignedWitness` asks for such a first run at each signed key. `monitoredWorld_signed_grind`
  shows that at a base call of signed keys the grind leaves the monitor at the query step of the
  call. So the signed branch of `trialFresh` is never reached.
* `SignedWitnessStep` is open. It says that each world call keeps `SignedWitness`.

## `R1Link`

`R1Link ρ` is false for each fixed `ρ`. The counterexample is at the end of this module.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningCacheLogProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningHitLaneProof

variable {C : Committee} (prims : Primitives)

section CacheFromLog

/-- A log entry as a call of `H` with its answer, on the counted copy or on the free copy. -/
def hashCall : (Σ t : (WorldSpec C).Domain, (WorldSpec C).Range t) → Option (Query C × HashOutput)
  | ⟨.inl (.inl (.inr (.inl q))), output⟩ => some (q, output)
  | ⟨.inr (.inr (.inl q)), output⟩ => some (q, output)
  | _ => none

/-- The first logged answer of `H` at each input. -/
def logCache (log : QueryLog (WorldSpec C)) : HashCache C :=
  fun q => ((log.filterMap hashCall).find? fun entry => entry.1 = q).map Prod.snd

/-- An input of `H` other than a stream key. -/
def Tracked (q : Query C) : Prop := ∀ key, q ≠ .streamKey key

/-- The cache agrees with the log at each tracked input. -/
def CacheFromLog (s : LoggedState C) : Prop :=
  ∀ q, Tracked q → s.1.1 q = logCache s.2 q

theorem tracked_hash (input : HashInput) : Tracked (.hash input : Query C) :=
  fun _ h => by cases h

theorem tracked_prf (seed : HashOutput) (point : Point) : Tracked (.prf seed point : Query C) :=
  fun _ h => by cases h

theorem logCache_logQuery (log : QueryLog (WorldSpec C)) (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t)
    (q : Query C) :
    logCache (log.logQuery t u) q =
      (logCache log q).or ((hashCall ⟨t, u⟩).bind fun entry => if entry.1 = q then some entry.2 else none) := by
  unfold logCache
  rw [QueryLog.logQuery, List.filterMap_append, List.find?_append, Option.map_or]
  cases h : hashCall ⟨t, u⟩ with
  | none => simp [QueryLog.singleton, h]
  | some entry =>
    by_cases he : entry.1 = q <;> simp [QueryLog.singleton, h, he]

/-- A call of `H` at `q` keeps `CacheFromLog`. -/
theorem cacheFromLog_hash (q : Query C) (s : LoggedState C) (hs : CacheFromLog s) (w : HashOutput × HashCache C)
    (hw : w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1)) (log : QueryLog (WorldSpec C))
    (hlog : ∀ q', logCache log q' = (logCache s.2 q').or (if q = q' then some w.1 else none)) :
    ∀ q', Tracked q' → w.2 q' = logCache log q' := by
  obtain ⟨hle, hself, hother⟩ := randomOracle_support q s.1.1 w hw
  intro q' hq'
  rw [hlog q', ← hs q' hq']
  by_cases he : q = q'
  · subst he
    rw [if_pos rfl, hself]
    cases hc : s.1.1 q with
    | none => rfl
    | some v =>
      have := hle hc
      rw [hself] at this
      rw [this]
      rfl
  · rw [if_neg he, hother q' (Ne.symm he)]
    cases s.1.1 q' <;> rfl

/-- Each world call other than a programming query keeps `CacheFromLog`. -/
theorem cacheFromLog_step (t : (WorldSpec C).Domain) (ht : ¬IsProgram t) (s : LoggedState C) (hs : CacheFromLog s)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((SigningCostProof.loggedImpl prims t).run s)) :
    CacheFromLog r.2 := by
  simp only [SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map,
    Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hunif : ∀ n (p : (unifSpec).Range n × HashCache C),
      p ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1) → p.2 = s.1.1 := by
    intro n p hp
    simp [unifFwdImpl] at hp
    obtain ⟨a, rfl⟩ := hp
    rfl
  have hprg : ∀ x (p : Bit × HashCache C), p ∈ support ((prgAnswer prims x).run s.1.1) →
      ∀ q', Tracked q' → p.2 q' = s.1.1 q' := by
    intro x p hp q' hq'
    unfold prgAnswer at hp
    rw [StateT.run_bind] at hp
    simp only [support_bind] at hp
    obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hp'
    exact (randomOracle_support _ s.1.1 p' hp').2.2 q' (hq' x.2.1)
  intro q' hq'
  rw [logCache_logQuery]
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change w ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1) at hw
    simp only [hashCall, Option.bind_none, Option.or_none]
    rw [hunif n w hw, hs q' hq']
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) at hw
    have h := cacheFromLog_hash q s hs w hw (s.2.logQuery _ w.1) (fun q'' => by rw [logCache_logQuery]; rfl) q' hq'
    rwa [logCache_logQuery] at h
  · change w ∈ support ((prgAnswer prims p).run s.1.1) at hw
    simp only [hashCall, Option.bind_none, Option.or_none]
    rw [hprg p w hw q' hq', hs q' hq']
  · exact (ht trivial).elim
  · change w ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1) at hw
    simp only [hashCall, Option.bind_none, Option.or_none]
    rw [hunif n w hw, hs q' hq']
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) at hw
    have h := cacheFromLog_hash q s hs w hw (s.2.logQuery _ w.1) (fun q'' => by rw [logCache_logQuery]; rfl) q' hq'
    rwa [logCache_logQuery] at h
  · change w ∈ support ((prgAnswer prims p).run s.1.1) at hw
    simp only [hashCall, Option.bind_none, Option.or_none]
    rw [hprg p w hw q' hq', hs q' hq']

set_option maxRecDepth 100000 in
/-- The cache of each outcome of `loggedRun` agrees with its log at each tracked input. -/
theorem loggedRun_cacheFromLog (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∀ z ∈ support (SigningCostProof.loggedRun prims A x), CacheFromLog z.2 := by
  intro z hz
  have hinv := SeedHitProof.support_simulateQ_inv (SigningCostProof.loggedImpl prims)
    (fun s => ¬Programmed s.2 → CacheFromLog s)
    (fun t s hs r hr hprog => by
      rw [loggedImpl_log prims t s r hr, programmed_logQuery, not_or] at hprog
      exact cacheFromLog_step prims t hprog.2 s (hs hprog.1) r hr) _ loggedInit
    (fun _ _ _ => by simp [loggedInit, logCache]) z hz
  exact hinv (ThresholdLeanXmssSecurity.noProgramQuery prims C A x z hz)

set_option maxRecDepth 100000 in
/-- The cache of each outcome of `flatRun` agrees with its log at each tracked input. -/
theorem flatRun_cacheFromLog (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∀ z ∈ support (flatRun prims A x), CacheFromLog z.2.1 := by
  intro z hz
  refine loggedRun_cacheFromLog prims A x (z.1, z.2.1) ?_
  rw [← flatRun_logged, support_map]
  exact ⟨z, hz, rfl⟩

end CacheFromLog

section Transfer

set_option maxRecDepth 100000 in
/-- An event that reads the cache only at tracked inputs has the same probability on `flatRun` and
on the flat eager run, where it reads `logCache` of the log. -/
theorem probEvent_flatRun_eq_flatEagerRun (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (E : Result C × HashCache C × Rest C (TsigState C × Bool) → Prop)
    (hE : ∀ r c c' rest, (∀ q, Tracked q → c q = c' q) → (E (r, c, rest) ↔ E (r, c', rest))) :
    Pr[fun z => E (z.1, z.2.1.1.1, restOf z.2) | flatRun prims A x] =
      Pr[fun z => E (z.1, logCache z.2.1.2, restOf z.2) | flatEagerRun prims P ρ A x] := by
  calc _ = Pr[fun z => E (z.1, logCache z.2.1.2, restOf z.2) | flatRun prims A x] :=
        probEvent_ext fun z hz => hE _ _ _ _ (flatRun_cacheFromLog prims A x z hz)
    _ = Pr[fun y => E (y.1, logCache y.2.1.2, y.2) | (fun z => (z.1, restOf z.2)) <$> flatRun prims A x] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun y => E (y.1, logCache y.2.1.2, y.2) |
          (fun z => (z.1, restOf z.2)) <$> flatEagerRun prims P ρ A x] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_flatEagerRun prims P ρ A x).symm
    _ = _ := by
        rw [probEvent_map]
        rfl

end Transfer

section Rerun

open SigningPartnerBoundProof

/-- A trial on a cached input is a no-op on the monitor when every cached input is seen. -/
theorem monitoredOracle_run_cached (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (q : Query C) (cache : HashCache C) (m : Monitor) (hcov : CacheSeen cache m) (output : HashOutput)
    (ho : cache q = some output) :
    (monitoredOracle keyOf q).run (cache, m) = pure (output, (cache, m)) := by
  simp only [monitoredOracle, StateT.run_mk, OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ ho,
    map_pure]
  cases q with
  | hash input =>
    have hseen : input ∈ m.seen := hcov input (by rw [ho]; exact Option.some_ne_none _)
    simp only [trialStep, if_pos hseen]
  | _ => rfl

/-- `XmssSecurity.Concrete.CacheReplay.randomOracle_rerun_largerCache_eq_pure_of_mem_support` of
leanVM (`XmssSecurity/Proof/CacheReplayEval.lean`) on the cache of `H`, with the trial monitor. A
rerun against an extension of the cache of a first run, with every cached input seen, changes
neither the cache nor the monitor. -/
theorem monitoredOracle_rerun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) {α : Type}
    (computation : OracleComp (Query C →ₒ HashOutput) α)
    (initialCache resultCache largerCache : HashCache C) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput)) computation).run initialCache))
    (hle : resultCache ≤ largerCache) (m : Monitor) (hcov : CacheSeen largerCache m) :
    (simulateQ (monitoredOracle keyOf) computation).run (largerCache, m) = pure (result, (largerCache, m)) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache largerCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, _hcache⟩ := hmem
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output := (randomOracle_support input initialCache _ hquery).2.1
      have hmiddleLe : middleCache ≤ resultCache :=
        SeedHitProof.support_simulateQ_inv (randomOracle (spec := Query C →ₒ HashOutput))
          (fun cache => middleCache ≤ cache)
          (fun q cache hcache r hr => hcache.trans (randomOracle_support q cache r hr).1)
          (next output) middleCache le_rfl _ hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        monitoredOracle_run_cached keyOf input largerCache m hcov output hlarger, pure_bind]
      exact ih output middleCache resultCache largerCache result hrest hle hcov

/-- The deviation of `trialFresh` is safe. A later grind at a key reruns the first grind on the same
base answer. Against any extension of the cache of the first grind, with every cached input seen,
it changes neither the cache nor the monitor, so it never reaches the signed branch of
`trialFresh`. -/
theorem baseGrind_rerun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (e : KeyIndex) (message : Message) (answer : HashOutput) (initial : HashCache C × Monitor)
    (first : Unit × (HashCache C × Monitor))
    (hfirst : first ∈ support ((simulateQ (monitoredOracle keyOf) (baseGrind P e message answer)).run initial))
    (cache : HashCache C) (hle : first.2.1 ≤ cache) (m : Monitor) (hcov : CacheSeen cache m) :
    (simulateQ (monitoredOracle keyOf) (baseGrind P e message answer)).run (cache, m) = pure ((), (cache, m)) := by
  have hmem : ((), first.2.1) ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (baseGrind P e message answer)).run initial.1) := by
    rw [← monitoredOracle_run_forget keyOf _ initial.1 initial.2, support_map]
    exact ⟨first, hfirst, rfl⟩
  exact monitoredOracle_rerun keyOf _ initial.1 first.2.1 cache () hmem hle m hcov

/-- Each signed key of the monitor has a bound message, a cached base answer, and a first grind on
them whose cache is below the cache of the state. -/
def SignedWitness (P : PublicParameter) (ρ : KeyIndex → Digest)
    (p : (LoggedState C × Monitor) × (TsigState C × Bool)) : Prop :=
  ∀ e, p.1.2.state.signed e ≠ none → ∃ message answer, p.2.1.bound e = some message ∧
    p.1.1.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = some answer ∧
    ∃ initial first, ((), first) ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (baseGrind P e message answer)).run initial) ∧ first ≤ p.1.1.1.1

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- A base call at signed keys. Its grind changes neither the cache nor the monitor, so the
monitor takes only the query step of the call. -/
theorem monitoredWorld_signed_grind (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain) (ht : ¬IsProgram t)
    (p : (LoggedState C × Monitor) × (TsigState C × Bool)) (hcov : CacheSeen p.1.1.1.1 p.1.2)
    (hwit : SignedWitness P ρ p)
    (hsigned : ∀ e, BaseCall P e (ρ e) p.2.1 t → p.1.2.state.signed e ≠ none)
    (r : (WorldSpec C).Range t × (LoggedState C × Monitor) × (TsigState C × Bool))
    (hr : r ∈ support ((monitoredWorld prims keyOf (grindExtra P ρ) t).run p)) :
    r.2.1.2 = queryEntryStep keyOf p.1.2 (hashEntry ⟨t, r.1⟩) := by
  simp only [monitoredWorld, carry, StateT.run_mk, support_bind, support_map, Set.mem_iUnion,
    Set.mem_image] at hr
  obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hr
  have hgrow : p.1.1.1.1 ≤ w.2.1.1 := by
    have hw2 := hw
    simp only [SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hw2
    obtain ⟨v, hv, hvw⟩ := hw2
    rw [← hvw]
    exact SigningCacheProof.countImpl_grows prims t p.1.1.1 v hv
  have hcov' := logged_query_cacheSeen prims keyOf t p.1.1 p.1.2 hcov ht w hw
  change y.2.2 = queryEntryStep keyOf p.1.2 (hashEntry ⟨t, w.1⟩)
  by_cases h : ∃ e, BaseCall P e (ρ e) p.2.1 t
  · obtain ⟨message, answer, hb, hans, initial, first, hmem, hle⟩ := hwit _ (hsigned _ h.choose_spec)
    have hans' : w.2.1.1 (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) =
        some answer := hgrow hans
    simp only [grindExtra, dif_pos h, hb, hans'] at hy
    rw [monitoredOracle_rerun keyOf _ initial first w.2.1.1 () hmem (hle.trans hgrow) _ hcov'] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    rw [hy]
  · simp only [grindExtra, dif_neg h, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    rw [hy]

/-- Open. Each world call of the monitored eager run keeps `SignedWitness`. A grind that installs
at a key `e` leaves its own run as the witness of `e`. This needs that each trial of the grind at
`e` is an encoding input of `e` for `keyOf`. -/
def SignedWitnessStep (P : PublicParameter) (ρ : KeyIndex → Digest) : Prop :=
  ∀ t, ¬IsProgram t → ∀ p : (LoggedState C × Monitor) × (TsigState C × Bool), CacheSeen p.1.1.1.1 p.1.2 →
    SignedWitness P ρ p →
    ∀ r ∈ support ((monitoredWorld prims (XmssSecurity.encodingInputLeafIndex? P) (grindExtra P ρ) t).run p),
      SignedWitness P ρ r.2

end Rerun

/-!
## `R1Link` is false for each fixed `ρ`

`R1Link ρ` of `SigningFlatEager` fixes the randomizer `ρ x e` before the run. The honest randomizer
of a run is `SigningGuessProof.cachedRandomizer x.2.1 cache e`, the XOR of the cached answers of
`H` at the PRF inputs `.prf (seeds T) (.randomizer bottomLayer e)`. These answers are uniform, so
the honest randomizer is not a function of `x`. `FinalState.selected` reads it from the cache.

A counterexample, for each `ρ` and some `x`. It is an argument on the support, not a Lean proof.

1. The forger runs one signing ceremony at a key `e` on a message `m`, then asks `H` at the
   encoding input of `e` for a pair `(m', r')` with `m' ≠ m`. It outputs a forgery at `e` on
   `(m', r')` with the released chain values.
2. Take a support point where the honest randomizer of `e` differs from `ρ x e`, where the answer
   at `(m', r')` has the encoding hash of the honest selection, and where no commitment collides.
3. No world call is a `BaseCall P e (ρ x e)`, so `grindExtra` runs no grind. No logged call
   installs a target, so `hit` stays false and `CachedSelection` is false.
4. The outcome is a win `(true, false)` with `BottomPartnerCase` and with no
   `AlternativeCommitment`. So the conclusion of `R1Link ρ` fails.

The trigger of `grindExtra` must read the randomizer from the cache of the state, for example
`cachedRandomizer x.2.1 p.1.1.1 e`, or `R1Link` must assume that `ρ x e` is that value.
-/

end SigningCacheLogProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningCacheLogProof.flatRun_cacheFromLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCacheLogProof.flatRun_cacheFromLog

/-- info: 'ThresholdLeanXmssSecurity.SigningCacheLogProof.probEvent_flatRun_eq_flatEagerRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCacheLogProof.probEvent_flatRun_eq_flatEagerRun

/-- info: 'ThresholdLeanXmssSecurity.SigningCacheLogProof.baseGrind_rerun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCacheLogProof.baseGrind_rerun

/-- info: 'ThresholdLeanXmssSecurity.SigningCacheLogProof.monitoredWorld_signed_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCacheLogProof.monitoredWorld_signed_grind
