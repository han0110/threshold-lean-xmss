import ThresholdLeanXmssSecurity.Proof.SigningLanes
import XmssSecurity.Proof.RandomOraclePresampling

/-!
# The budget check of the eager grind at the first base call

This module checks one candidate for the uncharged lane on paper, and it proves the law of an eager
handler for a plain lazy random oracle.

The check fails for the lane split as it is (`FreshSelection`, `bottomPartnerLogged_bound`,
`SigningOpeningProof.probEvent_le_of_capped`). The traces are below. The bottom rows pass only with
three changes R1, R2 and R3 of the split. The top-partner bound is a separate
hypothesis with or without them.

## The candidate

* The base call of a bottom key `e` is the first call of
  `randomizerInput P bottomLayer e ρ_e (bytesLE 32 m0)` after round 1 binds `m0` and releases `ρ_e`.
* At that call the hybrid runs the honest scan (`grind`, Scheme.lean) inside the handler. It caches
  each trial up to the selection. Later scan calls read the cache.
* The trials are not counted calls.

## The rules

* Each counted call has two units of `1 / N`, one in each lane (`signingHashError` is `q / 2^127`).
* `N = 2^128`, `K = |validDigests|` with `2^107 ≤ K ≤ 2^108`, and `v = K / N` with
  `2^-21 ≤ v ≤ 2^-20`.
* Lane C is the charged lane. Its output events are uniform at each call, so it is an expectation.
* Lane U is the uncharged lane.

## The three changes

* R1 moves the split of the bottom partner from `FreshSelection` (log order) to the event that the
  selected input is in the log before the base call. This event is a predicate of the log. Lane C
  then installs the selected digest at the base call of the eager run. The cost is a new monitor in
  place of `bottomPartnerLogged_bound`, which installs at the first fresh honest valid call. The
  risk is the transfer from the eager run to `loggedRun`, which needs the final cache (see below).
* R2 makes lane U one expectation over a capped hybrid that samples each opening `s e` at its
  release. Before the release `s e` is independent of the hybrid run, so an input-side call hits
  with probability `1 / N`. The lane 2 potential of leanVM adds to the same expectation, and each
  capped run makes at most `q` counted calls. The cost is an expectation form of
  `probEvent_le_of_capped`, which today gives the cap `q / N` for its own flag only. The risk is
  the support of the hybrid after a hit, which the cap handles as in `probEvent_le_of_capped`.
* R3 lets the potential read `bound e`. The world handler (`loggedImpl`) sees the cache and the log,
  not `st.bound`, and the adversary can call `randomizerInput P bottomLayer e ρ_e m` for many `m`
  after the release. The cost is one handler over the signing oracles and the world, with both
  states. The risk is the proof that the layered run equals the flat run.

## The table

Each row gives the unit of one counted call in each lane. "Spare" is a unit that no event uses.

| call | lane C | lane U |
| --- | --- | --- |
| commitment `(e, ρ')` | output `c_e` (`AlternativeCommitment`) | input `ρ' = s e` before the release |
| base shape `(lay, e, ρ', m)` | spare | input `ρ' = s e` before the release |
| canonical base call at `e` | none, the trials are free | none, it consumes the potential `Φ e / N` |
| bottom encoding at `e` before the base call | pending risk `1 / K` on a valid digest | lane 2 potential of leanVM (`f1`, `f2`, `f3`) |
| bottom encoding at `e` after the base call, fresh selection | meets the selected digest | none |
| bottom encoding at `e` after the base call, cached selection | none | `f4` of leanVM (`PostBad`) |
| encoding call on a cached trial | as a fresh call of the lazy run | as a fresh call of the lazy run |
| top encoding at `b` | `rawDomainCost anyTopDigestInput` | requires a top-partner estimate, see below |
| chain `(e, l, p, v)` or `(b, l, p, v)` | output chain target | input hidden value below the opened position |
| honest grind trial in round 2 | none, it reads the cache | none |

With R3 the base call is the only sign step of a key, so `leafIndices.Nodup` of
`Ghost.collision_le` holds.

## The top-partner bound

The third disjunct of `UnchargedFlag` is not covered by the table.

* `tree b` and `round2` at a key of tree `b` run `dealt.bottom b`, which is `referenceTree` on the
  bottom ceremony (Ideal.lean, Scheme.lean). So `¬ResolvedTopPartner` at `b` likely means that no
  query opened tree `b`. This step is not checked.
* `topOpened` is the digit of the canonical top encoding, also when tree `b` is never opened. So
  `chainTarget (.topChain b l p)` is `none` at that digit, and a forged value there that equals the
  hidden honest value does not raise `HiddenInputHit`.
* So the disjunct needs its own units on the top encoding calls at `b`. The top selection is fixed
  at the final verification. A fresh top selection meets an earlier top digest with the pending
  risk, one unit for each call. A cached top selection needs a call whose message is the hidden root
  of tree `b`, which costs about `1 / N` more for each call. Lane U has one unit on these calls, so
  the row is over by a term of order `q / N^2`.
* One fix extends the input-side flag to the digit of the canonical top encoding at a top key that
  no query opened. Then the forged value is an input hit of the chain row. This changes
  `HiddenInputHit`.

## The regression cases

* The commitment counterexample of `SigningGuessProof` (`M = 2^120`, `B = 2^90`,
  `q = M + 2^113`) passes with the table as it is. The branch `ρ' = ρ_e` is an input hit in lane U,
  at most `M / N`. The branch `ρ' ≠ ρ_e` is `AlternativeCommitment` in lane C, at most `M / N`. The
  `B` base calls with `ρ'` are not canonical.
* The stopped scan of `trueOpening_charge_gap`, followed by `q - T` encoding calls, passes only
  with R2. In the hybrid of R2 the scan does not see `ρ_e`, so lane U is `E[T_h + U_h] / N ≤ q / N`.
* Pre-queries then sign (leanVM lane 1) passes. `Q1` encoding calls at `e` give the pending set `P`.
  The fresh selection is uniform on the valid digests at the base call, so it meets `P` with
  probability `E|P| / K = Q1 / N`.
* Trace 1 of `SigningLanes` passes only with R1. The base call fixes the selection. The calls
  `b + 2i` in decreasing order read cached trials below the selection and meet the fixed digest
  above it, `1 / N` each. The hit of `P` is charged at the base call.
* Trace 2 of `SigningLanes` passes only with R3 and a port of the lane 2 proof. The `L = 2^23`
  cached invalid positions and `(m0, R)` are cached before the base call. The base is a fresh
  oracle answer, so it is uniform and independent of the cache
  (`XmssSecurity.evalDist_truncate_uniformHashOutput`). `Scan.selection_uniform_eq` gives the
  selection law `W / N` from a uniform base and any cache, and `signingAttemptLimit` and
  `randomizerAttemptLimit` are both `2^32`. `Ghost.collision_le` bounds lane 2 by the expected
  count of encoding calls. It needs a bridge from `Scheme.grind` to
  `precomputedSignBoundedAttempts`, which takes a leanVM `SecretKey`.

## The traces that fail without the changes

* Without R1, take Trace 2 of `SigningHybrid`. The adversary calls the base after round 1, and the
  eager grind selects a fresh `S`. Then the adversary calls `S` before round 2. On the log
  `FreshSelection` is false, so the hit of `P` is in lane U. A bottom encoding call at `e` before
  the base call then has three units. Lane C has its pending risk (`bottomPartnerLogged_bound`), and
  lane U has the pending risk of the front-run selection and the lane 2 potential.
* Without R2, the adversary flips a coin. On heads it makes `q` commitment calls before round 1. On
  tails it makes `q` encoding calls at `e`. The cap of `probEvent_le_of_capped` costs `q / N`, and
  `Ghost.collision_le` adds `E[U] / N = q / (2N)`. The sum is `1.5 · q / N`.
* Without R3, the adversary calls the base shape for `m1 ≠ m0` first after the release. A handler
  that grinds every message spends the sign step of `e` on `m1`. Then `leafIndices.Nodup` fails, and
  the potential no longer covers the selection of `m0`.

## The reuse of leanVM

`Ghost.collision_le` cannot be applied as it is. Its sign step is `Concrete.scheme.sign`, which
returns the signature and not the base, but the threshold adversary sees the base. The step lemmas
of `Scan/Phase.lean` (`f1_step` to `f4_step`) read only the state, so a port whose sign step also
returns the base can keep them.

## What this module proves

The lemmas are for a plain lazy random oracle `D →ₒ R`. The eager handler writes its trials into the
one cache, so the law holds for the result and not for the final cache.

* `evalDist_run'_bind_const` shows that a lazy subcomputation whose result the rest ignores does not
  change the law of the result. It uses `evalDist_randomOracle_run_eq_query_then_of_cached` of
  leanVM.
* `evalDist_eagerOracle_run'` shows that `eagerOracle` has the law of the lazy random oracle.
* `evalDist_eagerOracle_logged` gives the same law for the result and the log of the calls.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningEagerGrindProof

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- A lazy call of `target` leaves `target` in the cache. -/
theorem randomOracle_run_cached (target : D) (cache : (D →ₒ R).QueryCache) :
    ∀ r ∈ support ((randomOracle (spec := D →ₒ R) target).run cache), ∃ o, r.2 target = some o := by
  intro r hr
  cases hc : cache target with
  | none =>
    rw [QueryImpl.withCaching_run_none _ hc] at hr
    simp at hr
    obtain ⟨x, -, rfl⟩ := hr
    exact ⟨x, QueryCache.cacheQuery_self cache target x⟩
  | some o =>
    rw [QueryImpl.withCaching_run_some _ hc] at hr
    simp at hr
    subst hr
    exact ⟨o, hc⟩

/-- A lazy call whose answer the rest ignores leaves the law of the result unchanged. -/
theorem evalDist_run'_query_bind_const {α : Type} (target : D) (oa : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle (liftM ((D →ₒ R).query target) >>= fun _ => oa)).run' cache] =
      𝒟[(simulateQ randomOracle oa).run' cache] := by
  set oa' : OracleComp (D →ₒ R) α := oa >>= fun a => liftM ((D →ₒ R).query target) >>= fun _ => pure a
  have hrun : ∀ c, (simulateQ randomOracle oa').run c = (simulateQ randomOracle oa).run c >>= fun r =>
      (randomOracle (spec := D →ₒ R) target).run r.2 >>= fun q => pure (r.1, q.2) := by
    intro c
    simp only [oa', simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  have hcached : ∀ c, ∀ result ∈ support ((simulateQ randomOracle oa').run c),
      ∃ output, result.2 target = some output := by
    intro c result hres
    rw [hrun, mem_support_bind_iff] at hres
    obtain ⟨r, -, hres⟩ := hres
    rw [mem_support_bind_iff] at hres
    obtain ⟨q, hq, hres⟩ := hres
    simp only [support_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact randomOracle_run_cached target r.2 q hq
  have hforget : ∀ c, 𝒟[(simulateQ randomOracle oa').run' c] = 𝒟[(simulateQ randomOracle oa).run' c] := by
    intro c
    have hconst : ∀ x : α × (D →ₒ R).QueryCache,
        𝒟[(fun x => x.1) <$> ((randomOracle (spec := D →ₒ R) target).run x.2 >>= fun q => pure (x.1, q.2))] =
          𝒟[(pure x.1 : ProbComp α)] := by
      intro x
      rw [map_bind]
      simp only [map_pure]
      exact DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _
    rw [StateT.run'_eq, StateT.run'_eq, hrun, map_bind, evalDist_bind, evalDist_map]
    simp_rw [hconst]
    simp [map_eq_bind_pure_comp]
  have hleft : (simulateQ randomOracle (liftM ((D →ₒ R).query target) >>= fun _ => oa)).run' cache =
      (randomOracle (spec := D →ₒ R) target).run cache >>= fun q => (simulateQ randomOracle oa).run' q.2 := by
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rfl
  have hpre := evalDist_randomOracle_run_eq_query_then_of_cached oa' cache target (hcached cache)
  calc _ = 𝒟[(randomOracle (spec := D →ₒ R) target).run cache >>= fun q =>
          (simulateQ randomOracle oa').run' q.2] := by
        rw [hleft]
        exact DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => (hforget q.2).symm
    _ = 𝒟[(simulateQ randomOracle oa').run' cache] := by
        rw [StateT.run'_eq, evalDist_map, hpre, ← evalDist_map, map_bind]
        rfl
    _ = _ := hforget cache

theorem run'_query_bind {α : Type} (target : D) (next : R → OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) :
    (simulateQ randomOracle (liftM ((D →ₒ R).query target) >>= next)).run' cache =
      (randomOracle (spec := D →ₒ R) target).run cache >>= fun q =>
        (simulateQ randomOracle (next q.1)).run' q.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- A lazy subcomputation whose result the rest ignores leaves the law of the result unchanged. -/
theorem evalDist_run'_bind_const {α β : Type} (ob : OracleComp (D →ₒ R) β) (oa : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle (ob >>= fun _ => oa)).run' cache] =
      𝒟[(simulateQ randomOracle oa).run' cache] := by
  induction ob using OracleComp.inductionOn generalizing cache with
  | pure b => rw [pure_bind]
  | query_bind t next ih =>
    rw [bind_assoc, run'_query_bind, ← evalDist_run'_query_bind_const t oa cache, run'_query_bind]
    exact DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => ih q.1 q.2

/-- The eager grind. The first call of an input samples its answer `u` and then runs `extra input u`
on the same lazy oracle, so the trials of `extra` are cached at that call and are not results of the
computation. A later call reads the cache. -/
def eagerOracle (extra : D → R → OracleComp (D →ₒ R) Unit) :
    QueryImpl (D →ₒ R) (StateT (D →ₒ R).QueryCache ProbComp) :=
  fun input => StateT.mk fun cache => match cache input with
    | some u => pure (u, cache)
    | none => (randomOracle (spec := D →ₒ R) input).run cache >>= fun q =>
        (simulateQ randomOracle (extra input q.1)).run q.2 >>= fun r => pure (q.1, r.2)

/-- The eager run has the law of the lazy run. -/
theorem evalDist_eagerOracle_run' {α : Type} (extra : D → R → OracleComp (D →ₒ R) Unit)
    (oa : OracleComp (D →ₒ R) α) (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (eagerOracle extra) oa).run' cache] = 𝒟[(simulateQ randomOracle oa).run' cache] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp
  | query_bind t next ih =>
    have heager : (simulateQ (eagerOracle extra) (liftM ((D →ₒ R).query t) >>= next)).run' cache =
        (eagerOracle extra t).run cache >>= fun q => (simulateQ (eagerOracle extra) (next q.1)).run' q.2 := by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      rfl
    rw [heager, run'_query_bind]
    cases hc : cache t with
    | some u =>
      have he : (eagerOracle extra t).run cache = pure (u, cache) := by
        simp only [eagerOracle, StateT.run_mk, hc]
      rw [he, QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind]
      exact ih u cache
    | none =>
      have he : (eagerOracle extra t).run cache = (randomOracle (spec := D →ₒ R) t).run cache >>= fun q =>
          (simulateQ randomOracle (extra t q.1)).run q.2 >>= fun r => pure (q.1, r.2) := by
        simp only [eagerOracle, StateT.run_mk, hc]
      rw [he, bind_assoc]
      refine DeferredSampling.evalDist_bind_congr_left _ _ _ fun q => ?_
      simp only [bind_assoc, pure_bind]
      rw [← evalDist_run'_bind_const (extra t q.1) (next q.1) q.2, StateT.run'_eq, simulateQ_bind,
        StateT.run_bind, map_bind, evalDist_bind, evalDist_bind]
      exact congrArg _ (funext fun r => (ih q.1 r.2).trans (by rw [StateT.run'_eq]))

/-- The eager run has the law of the lazy run on the result and the log of the calls of the
computation. The trials of `extra` are not in the log. -/
theorem evalDist_eagerOracle_logged {α : Type} (extra : D → R → OracleComp (D →ₒ R) Unit)
    (oa : OracleComp (D →ₒ R) α) (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (eagerOracle extra) (simulateQ loggingOracle oa).run).run' cache] =
      𝒟[(simulateQ randomOracle (simulateQ loggingOracle oa).run).run' cache] :=
  evalDist_eagerOracle_run' extra _ cache

end SigningEagerGrindProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningEagerGrindProof.evalDist_eagerOracle_run'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningEagerGrindProof.evalDist_eagerOracle_run'

/--
info: 'ThresholdLeanXmssSecurity.SigningEagerGrindProof.evalDist_eagerOracle_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningEagerGrindProof.evalDist_eagerOracle_logged
