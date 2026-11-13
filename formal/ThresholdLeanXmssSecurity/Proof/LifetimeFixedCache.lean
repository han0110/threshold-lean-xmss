import ThresholdLeanXmssSecurity.Proof.Signing
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Erasing unused fixed-function cache entries

Fixed MPC hash inputs are answered by `Th` without consulting the cache. Erasing
their cache entries commutes with every random-oracle program, from any cache.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeFixedCache
attribute [local instance] Classical.propDecidable
variable {C : Committee}

def eraseFixed (c : HashCache C) : HashCache C :=
  fun q => if IsFixed q then none else c q

theorem eraseFixed_noMpc (c : HashCache C) : NoMpc (eraseFixed c) := by
  intro x hx
  simp [eraseFixed, IsFixed, hx]

theorem eraseFixed_le (c : HashCache C) : eraseFixed c ≤ c := by
  intro q v hv
  by_cases hq : IsFixed q
  · simp [eraseFixed, hq] at hv
  · simpa [eraseFixed, hq] using hv

theorem eraseFixed_cacheQuery (c : HashCache C) (q : Query C) (v : HashOutput)
    (hq : ¬ IsFixed q) :
    eraseFixed (c.cacheQuery q v) = (eraseFixed c).cacheQuery q v := by
  funext u
  by_cases hu : u = q
  · subst u
    simp [eraseFixed, hq]
  · simp only [eraseFixed, QueryCache.cacheQuery_of_ne _ _ hu]

theorem hashAnswer_eraseFixed (prims : Primitives) (q : Query C) (c : HashCache C) :
    Prod.map id eraseFixed <$> (hashAnswer prims q).run c =
      (hashAnswer prims q).run (eraseFixed c) := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm]
    simp
  · rw [hashAnswer_of_not_isFixed prims hq]
    have hc : eraseFixed c q = c q := by simp [eraseFixed, hq]
    cases h : c q with
    | some v =>
      rw [QueryImpl.withCaching_run_some _ h,
        QueryImpl.withCaching_run_some _ (hc.trans h)]
      simp
    | none =>
      rw [QueryImpl.withCaching_run_none _ h,
        QueryImpl.withCaching_run_none _ (hc.trans h)]
      simp only [Functor.map_map, Prod.map_apply, id_eq, eraseFixed_cacheQuery c q _ hq]

theorem roRun_eraseFixed (prims : Primitives) {α : Type} (p : OracleComp (RoSpec C) α)
    (c : HashCache C) :
    Prod.map id eraseFixed <$> roRun prims p c = roRun prims p (eraseFixed c) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro t s
  rcases t with q | x
  · exact hashAnswer_eraseFixed prims q s
  · change Prod.map id eraseFixed <$> (prgAnswer prims x).run s =
      (prgAnswer prims x).run (eraseFixed s)
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind]
    rw [← hashAnswer_eraseFixed prims (.streamKey x.2.1) s, bind_map_left]
    simp

end ThresholdLeanXmssSecurity.LifetimeFixedCache

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFixedCache.eraseFixed_noMpc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeFixedCache.eraseFixed_noMpc

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFixedCache.eraseFixed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeFixedCache.eraseFixed_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFixedCache.eraseFixed_cacheQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeFixedCache.eraseFixed_cacheQuery

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFixedCache.hashAnswer_eraseFixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeFixedCache.hashAnswer_eraseFixed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFixedCache.roRun_eraseFixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeFixedCache.roRun_eraseFixed
