import ThresholdLeanXmssSecurity.Proof.SigningEagerGrind
import ThresholdLeanXmssSecurity.Proof.SigningReleased

/-!
# The flat run of the signing game

This module gives change R3 of `SigningEagerGrind`. One handler answers the calls of the forger and
the world calls, so a potential can read `bound e` at each call.

## The flat handler

* `flat outer inner` runs each call of `outer` with its world calls under `carry inner`. A world call
  carries the state of `outer` from the start of the call of `outer`.
* `flat_run` shows that the flat run is the layered run.
* `flatOracles` is `flat` of `flaggedOracles` over `loggedImpl`. Its state holds the cache, the count,
  the call log, the `TsigState` and the flag.
* `flatRun` runs `finalRun` with `flatWorld` for the setup and the finish, and with `flatOracles` for
  the forger. `flatRun_logged` and `flatRun_exposed` give `loggedRun` and `exposedRun` exactly.
* `flatJointRun` does the same for `verifyFinal` with `openingOracles`. `flatJointRun_eq` gives
  `jointRun` exactly.

In a call of `round1`, the world calls carry the state before the call, so `bound e` is still the
old value there. These calls are the `prf` and `mask` calls of `eval`, and none is a call of `.hash`.
No other signing oracle changes `bound` before its world calls.

## One canonical base call for each key

* `baseInput P e ρ st` is `randomizerInput P bottomLayer e ρ (bytesLE 32 m)` when `st.bound e = some m`.
* `baseInput_grows` shows that the base input never changes, because `bound e` is write-once
  (`StateGrows`).
* `flatOracles_grows` and `flatWorld_run_grows` show that the flat state grows along the run.
* `flatWorld_keeps_baseCached` and `flatOracles_keeps_baseCached` make `BaseCached` an invariant.
* `baseCall_once` shows that after a canonical base call of `e`, each later canonical base call of
  `e` reads the cache and keeps it.

## The hash form and the eager grind

* `signingLocalAnswer_eq` shows that the local oracles are private sampling and one lazy `H`, then
  a fixed function. A `PRG` call is the `H` call on its stream key, then AES-128.
* `signImpl_simulateQ` shows that a run with no programming query is a run of `mixedOracle`. It uses
  `programFree_simulate_local` and `programFree_finalRun` of `SigningHitProof`.
* The eager lemmas of `SigningEagerGrind` have no private sampling. This module ports them to
  `mixedOracle`. A private sample commutes with the presample.
* `evalDist_eager_exposedRun` shows that the eager grind on `finalRun` has the law of the result and
  the count of `exposedRun`. The law does not hold for the final cache.

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

open LeanXmss ThresholdLeanXmss

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

/-- The flat run forgets the log and the state of the signing oracles and gives `exposedRun`. -/
theorem flatRun_exposed (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, z.2.1.1)) <$> flatRun prims A x = SigningDescentProof.exposedRun prims A x := by
  rw [← SigningCostProof.loggedRun_forget, ← flatRun_logged, Functor.map_map]

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
  (st.bound e).map fun message => randomizerInput P bottomLayer e ρ (bytesLE 32 message)

/-- A canonical base call of key `e` at the state `st`. -/
def BaseCall (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (st : TsigState C) (t : (WorldSpec C).Domain) :
    Prop :=
  ∃ input, baseInput P e ρ st = some input ∧ HashCallAt input t

/-- The canonical base input of key `e` is in the cache of the flat state. -/
def BaseCached (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (p : FlatState C) : Prop :=
  ∃ input, baseInput P e ρ p.2.1 = some input ∧ ∃ output, p.1.1.1 (.hash input) = some output

/-- The flat state grows. The state of the signing oracles grows and the cache only adds entries. -/
def FlatGrows (p p' : FlatState C) : Prop :=
  SigningSupportProof.StateGrows p.2.1 p'.2.1 ∧ p.1.1.1 ≤ p'.1.1.1

theorem flatGrows_refl (p : FlatState C) : FlatGrows p p :=
  ⟨SigningSupportProof.stateGrows_refl _, le_rfl⟩

theorem flatGrows_trans {p p' p'' : FlatState C} (h : FlatGrows p p') (h' : FlatGrows p' p'') :
    FlatGrows p p'' :=
  ⟨SigningSupportProof.stateGrows_trans h.1 h'.1, h.2.trans h'.2⟩

/-- `bound e` is write-once, so the canonical base input of a key never changes once it exists. -/
theorem baseInput_grows {P : PublicParameter} {e : KeyIndex} {ρ : Digest} {st st' : TsigState C}
    (h : SigningSupportProof.StateGrows st st') {input : HashInput} (hb : baseInput P e ρ st = some input) :
    baseInput P e ρ st' = some input := by
  obtain ⟨message, hm, rfl⟩ := Option.map_eq_some_iff.mp hb
  rw [baseInput, h.bound_eq hm]
  rfl

/-- Two canonical base calls of one key, the second at a grown state, call `H` at the same input. -/
theorem baseCall_unique {P : PublicParameter} {e : KeyIndex} {ρ : Digest} {st st' : TsigState C}
    (h : SigningSupportProof.StateGrows st st') {t t' : (WorldSpec C).Domain} (ht : BaseCall P e ρ st t)
    (ht' : BaseCall P e ρ st' t') : ∃ input, HashCallAt input t ∧ HashCallAt input t' := by
  obtain ⟨input, hb, hcall⟩ := ht
  obtain ⟨input', hb', hcall'⟩ := ht'
  rw [baseInput_grows h hb, Option.some.injEq] at hb'
  subst hb'
  exact ⟨input, hcall, hcall'⟩

theorem baseCached_grows {P : PublicParameter} {e : KeyIndex} {ρ : Digest} {p p' : FlatState C}
    (h : FlatGrows p p') (hp : BaseCached P e ρ p) : BaseCached P e ρ p' := by
  obtain ⟨input, hb, output, ho⟩ := hp
  exact ⟨input, baseInput_grows h.1 hb, output, h.2 ho⟩

theorem flatWorld_support (t : (WorldSpec C).Domain) (p : FlatState C) (z : (WorldSpec C).Range t × FlatState C)
    (hz : z ∈ support ((flatWorld prims t).run p)) :
    ∃ w ∈ support ((SigningCacheProof.countImpl prims t).run p.1.1), z.1 = w.1 ∧ z.2.1.1 = w.2 ∧ z.2.2 = p.2 := by
  simp only [flatWorld, carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, ⟨w, hw, rfl⟩, rfl⟩ := hz
  exact ⟨w, hw, rfl, rfl, rfl⟩

/-- A world call of the flat run keeps the state of the signing oracles and grows the cache. -/
theorem flatWorld_grows (t : (WorldSpec C).Domain) (p : FlatState C) (z : (WorldSpec C).Range t × FlatState C)
    (hz : z ∈ support ((flatWorld prims t).run p)) : FlatGrows p z.2 := by
  obtain ⟨w, hw, -, hcache, hst⟩ := flatWorld_support prims t p z hz
  refine ⟨hst ▸ SigningSupportProof.stateGrows_refl _, ?_⟩
  rw [hcache]
  exact SigningCacheProof.countImpl_grows prims t p.1.1 w hw

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

/-- A canonical base call caches the canonical base input. -/
theorem flatWorld_baseCached {P : PublicParameter} {e : KeyIndex} {ρ : Digest} (t : (WorldSpec C).Domain)
    (p : FlatState C) (ht : BaseCall P e ρ p.2.1 t) (z : (WorldSpec C).Range t × FlatState C)
    (hz : z ∈ support ((flatWorld prims t).run p)) : BaseCached P e ρ z.2 := by
  obtain ⟨w, hw, -, hcache, hst⟩ := flatWorld_support prims t p z hz
  obtain ⟨input, hb, hcall⟩ := ht
  obtain ⟨output, ho⟩ := countImpl_hash_cached prims input t hcall p.1.1 w hw
  exact ⟨input, hst ▸ hb, output, hcache ▸ ho⟩

/-- A run of `loggedImpl` grows the cache. -/
theorem logged_cache_grows {α : Type} (oa : OracleComp (WorldSpec C) α) (l : SigningHitLaneProof.LoggedState C) :
    ∀ z ∈ support ((simulateQ (SigningCostProof.loggedImpl prims) oa).run l), l.1.1 ≤ z.2.1.1 := by
  refine SeedHitProof.support_simulateQ_inv _ (fun l' => l.1.1 ≤ l'.1.1) (fun t l' hl' r hr => ?_) oa l le_rfl
  simp only [SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact hl'.trans (SigningCacheProof.countImpl_grows prims t l'.1 w hw)

/-- A call of the flat handler grows the flat state. -/
theorem flatOracles_step_grows (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (p : FlatState C)
    (z : (LocalSpec C + TsigSpec C).Range t × FlatState C) (hz : z ∈ support ((flatOracles prims x dealt t).run p)) :
    FlatGrows p z.2 := by
  simp only [flatOracles, flat, StateT.run_mk, carry_run_pair, Functor.map_map, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hflag : w.1 ∈ support ((SigningCoreProof.flaggedOracles x dealt t).run p.2) := by
    apply support_simulateQ_run'_subset (SigningCostProof.loggedImpl prims) _ p.1
    rw [StateT.run'_eq, support_map]
    exact ⟨w, hw, rfl⟩
  have hgame : (w.1.1, w.1.2.1) ∈ support ((SigningCoreProof.gameOracles dealt t).run p.2.1) := by
    rw [← SigningCoreProof.flaggedOracles_forget x dealt t p.2.1 p.2.2, support_map]
    exact ⟨w.1, hflag, rfl⟩
  exact ⟨SigningSupportProof.gameOracles_stateGrows dealt t p.2.1 _ hgame,
    logged_cache_grows prims _ p.1 w hw⟩

/-- A run of the flat handler grows the flat state. -/
theorem flatOracles_grows (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    {α : Type} (oa : OracleComp (LocalSpec C + TsigSpec C) α) (p : FlatState C) :
    ∀ z ∈ support ((simulateQ (flatOracles prims x dealt) oa).run p), FlatGrows p z.2 :=
  SeedHitProof.support_simulateQ_inv _ (FlatGrows p)
    (fun t p' hp' z hz => flatGrows_trans hp' (flatOracles_step_grows prims x dealt t p' z hz)) oa p
    (flatGrows_refl p)

/-- A run of the world calls of the flat run grows the flat state. -/
theorem flatWorld_run_grows {α : Type} (oa : OracleComp (WorldSpec C) α) (p : FlatState C) :
    ∀ z ∈ support ((simulateQ (flatWorld prims) oa).run p), FlatGrows p z.2 :=
  SeedHitProof.support_simulateQ_inv _ (FlatGrows p)
    (fun t p' hp' z hz => flatGrows_trans hp' (flatWorld_grows prims t p' z hz)) oa p (flatGrows_refl p)

/-- A canonical base call at a state where the canonical base input is cached calls `H` at a cached
input. -/
theorem baseCall_cached {P : PublicParameter} {e : KeyIndex} {ρ : Digest} {p : FlatState C}
    (hp : BaseCached P e ρ p) {t : (WorldSpec C).Domain} (ht : BaseCall P e ρ p.2.1 t) :
    ∃ input output, HashCallAt input t ∧ p.1.1.1 (.hash input) = some output := by
  obtain ⟨input, hb, output, ho⟩ := hp
  obtain ⟨input', hb', hcall⟩ := ht
  rw [hb, Option.some.injEq] at hb'
  subst hb'
  exact ⟨input, output, hcall, ho⟩

/-- A call of `H` at a cached input answers from the cache and keeps it. -/
theorem countImpl_hash_hit (input : HashInput) (t : (WorldSpec C).Domain) (ht : HashCallAt input t)
    (s : HashCache C × ℕ) (output : HashOutput) (ho : s.1 (.hash input) = some output) :
    ∀ w ∈ support ((SigningCacheProof.countImpl prims t).run s), w.2.1 = s.1 := by
  rcases ht with rfl | rfl
  all_goals
    intro w hw
    simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map,
      Set.mem_image] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    change r ∈ support (((Query C →ₒ HashOutput).randomOracle (.hash input)).run s.1) at hr
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ ho, support_pure] at hr
    exact congrArg Prod.snd (Set.mem_singleton_iff.mp hr)

/-- `BaseCached` is an invariant of each world call of the flat run. -/
theorem flatWorld_keeps_baseCached {P : PublicParameter} {e : KeyIndex} {ρ : Digest} (t : (WorldSpec C).Domain)
    (p : FlatState C) (hp : BaseCached P e ρ p) (z : (WorldSpec C).Range t × FlatState C)
    (hz : z ∈ support ((flatWorld prims t).run p)) : BaseCached P e ρ z.2 :=
  baseCached_grows (flatWorld_grows prims t p z hz) hp

/-- `BaseCached` is an invariant of each run of the flat handler. -/
theorem flatOracles_keeps_baseCached {P : PublicParameter} {e : KeyIndex} {ρ : Digest}
    (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (p : FlatState C) (hp : BaseCached P e ρ p) :
    ∀ z ∈ support ((simulateQ (flatOracles prims x dealt) oa).run p), BaseCached P e ρ z.2 :=
  fun z hz => baseCached_grows (flatOracles_grows prims x dealt oa p z hz) hp

/-- Only the first canonical base call of a key samples `H`. After a canonical base call of `e`, each
later canonical base call of `e` on the flat run reads the cache and keeps it. `bound e` is
write-once, and the canonical base input carries the bound message. -/
theorem baseCall_once {P : PublicParameter} {e : KeyIndex} {ρ : Digest} (t : (WorldSpec C).Domain) (p : FlatState C)
    (ht : BaseCall P e ρ p.2.1 t) (z : (WorldSpec C).Range t × FlatState C)
    (hz : z ∈ support ((flatWorld prims t).run p)) (p' : FlatState C) (hgrows : FlatGrows z.2 p')
    (t' : (WorldSpec C).Domain) (ht' : BaseCall P e ρ p'.2.1 t') (z' : (WorldSpec C).Range t' × FlatState C)
    (hz' : z' ∈ support ((flatWorld prims t').run p')) : z'.2.1.1.1 = p'.1.1.1 := by
  obtain ⟨input, output, hcall, ho⟩ :=
    baseCall_cached (baseCached_grows hgrows (flatWorld_baseCached prims t p ht z hz)) ht'
  obtain ⟨w, hw, -, hcache, -⟩ := flatWorld_support prims t' p' z' hz'
  rw [hcache]
  exact countImpl_hash_hit prims input t' hcall p'.1.1 output ho w hw

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
    𝒟[(simulateQ mixedOracle computation).run cache] =
      𝒟[do
        let value ← $ᵗ R
        (simulateQ mixedOracle computation).run (cache.cacheQuery target value)] := by
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
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun u => ih u cache habsent (hnextCached u)
    · have hrun := fun initialCache => mixed_run_inr (D := D) (R := R) input next initialCache
      by_cases htarget : input = target
      · subst input
        rw [hrun, QueryImpl.withCaching_run_none _ habsent, map_eq_bind_pure_comp]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro sampled
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
            calc
              𝒟[(simulateQ mixedOracle (next answer)).run cache] =
                  𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ mixedOracle (next answer)).run (cache.cacheQuery target sampled)] :=
                ih answer cache habsent hnextCached
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ mixedOracle
                      (liftM ((unifSpec + (D →ₒ R)).query (.inr input)) >>= next)).run
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hcachedInput : (cache.cacheQuery target sampled) input = some answer := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_some _ hcachedInput, pure_bind]
            rfl
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
            calc
              𝒟[$ᵗ R >>= fun answer =>
                  (simulateQ mixedOracle (next answer)).run (cache.cacheQuery input answer)] =
                  𝒟[$ᵗ R >>= fun answer => $ᵗ R >>= fun sampled =>
                      (simulateQ mixedOracle (next answer)).run
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                exact ih answer (cache.cacheQuery input answer) (htargetAfterInput answer) (hnextCached answer)
              _ = 𝒟[$ᵗ R >>= fun sampled => $ᵗ R >>= fun answer =>
                      (simulateQ mixedOracle (next answer)).run
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              _ = 𝒟[$ᵗ R >>= fun sampled => $ᵗ R >>= fun answer =>
                      (simulateQ mixedOracle (next answer)).run
                        ((cache.cacheQuery target sampled).cacheQuery input answer)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                rw [QueryCache.cacheQuery_comm_of_ne cache htarget]
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ mixedOracle
                      (liftM ((unifSpec + (D →ₒ R)).query (.inr input)) >>= next)).run
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hnone : (cache.cacheQuery target sampled) input = none := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_none _ hnone, map_eq_bind_pure_comp]
                simp only [Function.comp_apply, bind_assoc, pure_bind]
                rfl
            rfl

/-- `OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached` of leanVM with private sampling. -/
theorem evalDist_mixed_run_eq_query_then_of_cached {α : Type} (computation : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (hcached : ∀ result ∈ support ((simulateQ mixedOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    𝒟[(simulateQ mixedOracle computation).run cache] =
      𝒟[(randomOracle (spec := D →ₒ R) target).run cache >>= fun queryResult =>
        (simulateQ mixedOracle computation).run queryResult.2] := by
  cases htarget : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ htarget, map_eq_bind_pure_comp]
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      exact evalDist_mixed_run_eq_presample_of_cached computation cache target htarget hcached
  | some output =>
      rw [QueryImpl.withCaching_run_some _ htarget, pure_bind]

/-- `SigningEagerGrindProof.evalDist_run'_query_bind_const` with private sampling. -/
theorem evalDist_mixed_run'_query_bind_const {α : Type} (target : D) (oa : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : (D →ₒ R).QueryCache) :
    𝒟[(randomOracle (spec := D →ₒ R) target).run cache >>= fun q => (simulateQ mixedOracle oa).run' q.2] =
      𝒟[(simulateQ mixedOracle oa).run' cache] := by
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
  have hforget : ∀ c, 𝒟[(simulateQ mixedOracle oa').run' c] = 𝒟[(simulateQ mixedOracle oa).run' c] := by
    intro c
    have hconst : ∀ x : α × (D →ₒ R).QueryCache,
        𝒟[(fun x => x.1) <$> ((randomOracle (spec := D →ₒ R) target).run x.2 >>= fun q => pure (x.1, q.2))] =
          𝒟[(pure x.1 : ProbComp α)] := by
      intro x
      rw [map_bind]
      simp only [map_pure]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _
    rw [StateT.run'_eq, StateT.run'_eq, hrun, map_bind, evalDist_bind, evalDist_map]
    simp_rw [hconst]
    simp [map_eq_bind_pure_comp]
  have hpre := evalDist_mixed_run_eq_query_then_of_cached oa' cache target (hcached cache)
  calc _ = 𝒟[(randomOracle (spec := D →ₒ R) target).run cache >>= fun q =>
          (simulateQ mixedOracle oa').run' q.2] :=
        OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => (hforget q.2).symm
    _ = 𝒟[(simulateQ mixedOracle oa').run' cache] := by
        rw [StateT.run'_eq, evalDist_map, hpre, ← evalDist_map, map_bind]
        rfl
    _ = _ := hforget cache

/-- `SigningEagerGrindProof.evalDist_run'_bind_const` with private sampling in the rest. -/
theorem evalDist_mixed_run'_bind_const {α β : Type} (ob : OracleComp (D →ₒ R) β)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle ob).run cache >>= fun r => (simulateQ mixedOracle oa).run' r.2] =
      𝒟[(simulateQ mixedOracle oa).run' cache] := by
  induction ob using OracleComp.inductionOn generalizing cache with
  | pure b => simp
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      ← evalDist_mixed_run'_query_bind_const t oa cache]
    exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => ih q.1 q.2

/-- The eager grind with private sampling. -/
def eagerMixed (extra : D → R → OracleComp (D →ₒ R) Unit) :
    QueryImpl (unifSpec + (D →ₒ R)) (StateT (D →ₒ R).QueryCache ProbComp) :=
  unifFwdImpl (D →ₒ R) + SigningEagerGrindProof.eagerOracle extra

/-- The eager run with private sampling has the law of the lazy run. -/
theorem evalDist_eagerMixed_run' {α : Type} (extra : D → R → OracleComp (D →ₒ R) Unit)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (eagerMixed extra) oa).run' cache] = 𝒟[(simulateQ mixedOracle oa).run' cache] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp
  | query_bind t next ih =>
    have hstep : ∀ (I : QueryImpl (unifSpec + (D →ₒ R)) (StateT (D →ₒ R).QueryCache ProbComp)) c,
        (simulateQ I (liftM ((unifSpec + (D →ₒ R)).query t) >>= next)).run' c =
          (I t).run c >>= fun q => (simulateQ I (next q.1)).run' q.2 := by
      intro I c
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      rfl
    rw [hstep, hstep]
    rcases t with n | t
    · change 𝒟[(unifFwdImpl (D →ₒ R) n).run cache >>= _] = 𝒟[(unifFwdImpl (D →ₒ R) n).run cache >>= _]
      exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => ih q.1 q.2
    · change 𝒟[(SigningEagerGrindProof.eagerOracle extra t).run cache >>= _] =
        𝒟[(randomOracle (spec := D →ₒ R) t).run cache >>= _]
      cases hc : cache t with
      | some u =>
        have he : (SigningEagerGrindProof.eagerOracle extra t).run cache = pure (u, cache) := by
          simp only [SigningEagerGrindProof.eagerOracle, StateT.run_mk, hc]
        rw [he, QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind]
        exact ih u cache
      | none =>
        have he : (SigningEagerGrindProof.eagerOracle extra t).run cache =
            (randomOracle (spec := D →ₒ R) t).run cache >>= fun q =>
              (simulateQ randomOracle (extra t q.1)).run q.2 >>= fun r => pure (q.1, r.2) := by
          simp only [SigningEagerGrindProof.eagerOracle, StateT.run_mk, hc]
        rw [he, bind_assoc]
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => ?_
        simp only [bind_assoc, pure_bind]
        rw [← evalDist_mixed_run'_bind_const (extra t q.1) (next q.1) q.2, evalDist_bind, evalDist_bind]
        exact congrArg _ (funext fun r => ih q.1 r.2)

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

/-- The eager grind on a run of the signing world with no programming query has the law of the run. -/
theorem evalDist_eager_signImpl {α : Type} (extra : Query C → HashOutput → OracleComp (Query C →ₒ HashOutput) Unit)
    (oa : OracleComp (WorldSpec C) α) (h : SigningHitProof.ProgramFree oa) (cache : HashCache C) :
    𝒟[(simulateQ (eagerMixed extra) (simulateQ (localQuery prims) (simulateQ SigningHitProof.worldLocalize oa))).run'
        cache] = 𝒟[(simulateQ (SeedHitProof.signImpl prims) oa).run' cache] := by
  rw [signImpl_simulateQ prims oa h]
  exact evalDist_eagerMixed_run' extra _ cache

set_option maxRecDepth 100000 in
/-- The eager grind on `finalRun` has the law of the run of the signing world. -/
theorem evalDist_eager_finalRun (extra : Query C → HashOutput → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) :
    𝒟[(simulateQ (eagerMixed extra) (simulateQ (localQuery prims)
        (simulateQ SigningHitProof.worldLocalize (SigningDescentProof.finalRun A x)))).run' cache] =
      𝒟[(simulateQ (SeedHitProof.signImpl prims) (SigningDescentProof.finalRun A x)).run' cache] :=
  evalDist_eager_signImpl prims extra _ (SigningHitProof.programFree_finalRun A x) cache

/-- The count of the local calls as a state of the computation. -/
def localCounter : QueryImpl (LocalSpec C) (StateT ℕ (OracleComp (LocalSpec C))) :=
  fun u => StateT.mk fun n => (fun a => (a, n + SigningHitProof.localCost u)) <$> query (spec := LocalSpec C) u

theorem withLocalCount_eq_flat (I : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp)) :
    SigningHitProof.withLocalCount I = flat localCounter I := by
  funext u
  apply StateT.ext
  intro p
  simp [SigningHitProof.withLocalCount, flat, localCounter, carry, Functor.map_map]

/-- The eager grind on a counted run of the signing world with no programming query has the law of
the result and the count of the run. -/
theorem evalDist_eager_countImpl {α : Type}
    (extra : Query C → HashOutput → OracleComp (Query C →ₒ HashOutput) Unit)
    (oa : OracleComp (WorldSpec C) α) (h : SigningHitProof.ProgramFree oa) (cache : HashCache C) (n : ℕ) :
    𝒟[(simulateQ (eagerMixed extra) (simulateQ (localQuery prims)
        ((simulateQ localCounter (simulateQ SigningHitProof.worldLocalize oa)).run n))).run' cache] =
      𝒟[(fun z => (z.1, z.2.2)) <$> (simulateQ (SigningCacheProof.countImpl prims) oa).run (cache, n)] := by
  rw [evalDist_eagerMixed_run', SigningHitProof.programFree_count_local prims oa h, withLocalCount_eq_flat,
    signingLocalAnswer_eq, ← QueryImpl.simulateQ_compose, StateT.run'_eq, ← flat_run, Functor.map_map]

set_option maxRecDepth 100000 in
/-- The eager grind on `finalRun` has the law of the result and the count of `exposedRun`. -/
theorem evalDist_eager_exposedRun (extra : Query C → HashOutput → OracleComp (Query C →ₒ HashOutput) Unit)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(simulateQ (eagerMixed extra) (simulateQ (localQuery prims)
        ((simulateQ localCounter (simulateQ SigningHitProof.worldLocalize (SigningDescentProof.finalRun A x))).run
          0))).run' ∅] =
      𝒟[(fun z => (z.1, z.2.2)) <$> SigningDescentProof.exposedRun prims A x] :=
  evalDist_eager_countImpl prims extra _ (SigningHitProof.programFree_finalRun A x) ∅ 0

end HashForm

end SigningFlatProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.flatRun_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.flatRun_logged

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.flatRun_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.flatRun_exposed

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.flatJointRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.flatJointRun_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.baseCall_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.baseCall_once

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.flatOracles_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.flatOracles_grows

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.evalDist_eagerMixed_run'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.evalDist_eagerMixed_run'

/-- info: 'ThresholdLeanXmssSecurity.SigningFlatProof.evalDist_eager_exposedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningFlatProof.evalDist_eager_exposedRun
