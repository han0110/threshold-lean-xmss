import ThresholdLeanXmssSecurity.Proof.SigningUnchargedLogged
import XmssSecurity.Proof.RandomOraclePresampling

/-!
# A cache fact of the lazy random oracle

This module holds `randomOracle_run_cached`. A lazy call of a plain random oracle `D →ₒ R` leaves
its input in the cache. `SigningFlatProof.evalDist_mixed_run'_query_bind_const` uses it.
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

end SigningEagerGrindProof

end ThresholdLeanXmssSecurity
