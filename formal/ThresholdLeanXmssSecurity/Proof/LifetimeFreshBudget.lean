import ThresholdLeanXmssSecurity.Proof.LifetimeJointSim
import ThresholdLeanXmssSecurity.Proof.TreeSimHashFinish

/-!
# Fresh-query budgets after adaptive selection

A pathwise fresh-query certificate survives extension of the starting cache.
Every supported answer from the larger cache can be replayed from the smaller
one, retaining cache inclusion; a collision-free larger cache also certifies
the smaller cache. This is support transport, not conditioning a probability
inequality on selected metadata.

The pinned and current leanVM cache-replay files were searched. Their replay
theorems concern the concrete XMSS oracle and a completed larger cache; the
local-oracle step and fresh-budget transport below use the existing threshold
atom decomposition instead.

`selectedFresh_reached_small` and `selected_terminal_small` apply the existing
honest-point obligation to the actual selected program and prefix cache. Their
hypothesis is `TreeSimHashHonestBudget`. Given that hypothesis,
`selectedFreshBudget_iff_large` identifies `LifetimeJointSim.SelectedFreshBudget`
with its large-budget branch. The existing terminal-to-fresh theorem
uses a small coarse bound to ensure good completions, so it cannot establish
that branch merely by increasing its budget. A direct whole-run fresh-point
count, with the actual batch covers, is needed for that branch.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeFreshBudget

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

variable {C : Committee} (prims : Primitives)

/-- A supported answer can be replayed from a subcache, retaining inclusion. -/
theorem local_support_subcache (t : (LocalSpec C).Domain)
    (small large : HashCache C) (included : small ≤ large)
    (r : (LocalSpec C).Range t × HashCache C)
    (run : r ∈ support ((localAnswer prims t).run large)) :
    ∃ cache, (r.1, cache) ∈ support ((localAnswer prims t).run small) ∧ cache ≤ r.2 := by
  rcases isAtom_localAnswer prims t with ⟨p, hp⟩ | ⟨q, f, hf⟩
  · rw [hp] at run ⊢
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at run ⊢
    obtain ⟨u, hu, rfl⟩ := run
    exact ⟨small, ⟨u, hu, rfl⟩, included⟩
  · rw [hf, StateT.run_map, support_map] at run
    obtain ⟨u, hu, rfl⟩ := run
    obtain ⟨growth, present, other⟩ := randomOracle_support q large u hu
    have inserted : small.cacheQuery q u.1 ≤ u.2 := by
      intro a v ha
      by_cases he : a = q
      · subst a
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at ha
        subst v
        exact present
      · rw [QueryCache.cacheQuery_of_ne _ _ he] at ha
        exact growth (included ha)
    refine ⟨small.cacheQuery q u.1, ?_, inserted⟩
    rw [hf, StateT.run_map, support_map]
    refine ⟨(u.1, small.cacheQuery q u.1), ?_, rfl⟩
    cases hs : small q with
    | none =>
      simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs,
        support_map, Set.mem_image]
      exact ⟨u.1, mem_support_uniformSample HashOutput, rfl⟩
    | some v =>
      have eq : v = u.1 := Option.some.inj ((growth (included hs)).symm.trans present)
      subst v
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs]
      simp only [mem_support_pure_iff, Prod.mk.injEq, true_and]
      ext a
      by_cases he : a = q
      · subst a
        simp [hs]
      · rw [QueryCache.cacheQuery_of_ne _ _ he]

/-- Region collisions are preserved by extension of the public cache. -/
theorem collision_mono (P : Query C → Prop) {small large : HashCache C}
    (included : small ≤ large)
    (bad : CacheHasCollision (splitRegionCache P small)) :
    CacheHasCollision (splitRegionCache P large) := by
  obtain ⟨a, b, u, v, ne, ha, hb, eq⟩ := bad
  have lift (q : Query C) (h : HashOutput)
      (present : splitRegionCache P small q = some h) :
      splitRegionCache P large q = some h := by
    by_cases hp : P q
    · simpa only [splitRegionCache, if_pos hp] using
        included (by simpa only [splitRegionCache, if_pos hp] using present)
    · simp [splitRegionCache, hp] at present
  exact ⟨a, b, u, v, ne, lift a u ha, lift b v hb, eq⟩

/-- Extra cached inputs never increase a pathwise fresh-query budget. -/
theorem freshBudget_subcache (P : Query C → Prop) {α : Type}
    {p : OracleComp (LocalSpec C) α} {small : HashCache C} {n : ℕ}
    (budget : TreeSimHashFreshBudget prims P p small n)
    (large : HashCache C) (included : small ≤ large) :
    TreeSimHashFreshBudget prims P p large n := by
  induction budget generalizing large with
  | pure a small n => exact .pure a large n
  | query_bind t f small n positive next ih =>
    have fresh : TreeSimHashFresh P t large → TreeSimHashFresh P t small := by
      rintro ⟨q, hq, hp, absent⟩
      refine ⟨q, hq, hp, ?_⟩
      cases hs : small q with
      | none => rfl
      | some u => exact (by simpa [absent] using included hs)
    apply TreeSimHashFreshBudget.query_bind
    · exact fun h => positive (fresh h)
    · intro r run good
      obtain ⟨cache, replay, sub⟩ := local_support_subcache prims t small large included r run
      have h := ih (r.1, cache) replay (fun bad => good (collision_mono P sub bad)) r.2 sub
      apply h.mono prims P
      split_ifs with hs hl hl
      · rfl
      · omega
      · exact (hs (fresh hl)).elim
      · rfl

/-- Dropping a computed output field does not change the fresh-query budget. -/
theorem freshBudget_map (P : Query C → Prop) {α β : Type}
    (f : α → β) {p : OracleComp (LocalSpec C) α} {cache : HashCache C} {n : ℕ}
    (budget : TreeSimHashFreshBudget prims P p cache n) :
    TreeSimHashFreshBudget prims P (f <$> p) cache n := by
  induction budget with
  | pure a cache n => simpa only [map_pure] using TreeSimHashFreshBudget.pure (prims := prims) (P := P) (f a) cache n
  | query_bind t k cache n positive next ih =>
    rw [map_bind]
    exact .query_bind t _ cache n positive ih

theorem localLogged_erase {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    Prod.fst <$> treeSimLocalLogged p = p := by
  rw [treeSimLocalLogged, QueryImpl.fst_map_run_withTraceAppend]
  exact simulateQ_id' p

/-- The normalized log can be erased while preserving the private cache. -/
theorem normalized_erase (D : C.Coalition) {α : Type}
    (p : OracleComp (LocalSpec C + LocalSpec C) α) (hidden : HiddenCache C) :
    (fun r => (r.1.1, r.2)) <$>
      (simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run hidden =
      (simulateQ (treeSimHashLocal D) p).run hidden := by
  have h := congrArg (fun oa => (simulateQ (treeSimHashLocal D) oa).run hidden)
    (localLogged_erase p)
  simpa only [simulateQ_map, StateT.run_map] using h

/-- A fresh certificate bounds the actual terminal cache on every good run. -/
theorem freshBudget_terminal (P : Query C → Prop) {α : Type}
    {p : OracleComp (LocalSpec C) α} {cache : HashCache C} {n : ℕ}
    (budget : TreeSimHashFreshBudget prims P p cache n)
    (S : Finset (Query C)) (keys : TreeSimHashRegionKeys P cache S)
    (r : α × HashCache C) (run : r ∈ support ((simulateQ (localAnswer prims) p).run cache))
    (good : ¬ CacheHasCollision (splitRegionCache P r.2)) :
    SplitCacheBound (splitRegionCache P r.2) (S.card + n) := by
  induction budget generalizing S r with
  | pure a cache n =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact keys.bound.mono (Nat.le_add_right _ _)
  | query_bind t f cache n positive next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨mid, first, rest⟩ := run
    have midGood : ¬ CacheHasCollision (splitRegionCache P mid.2) :=
      fun bad => good (collision_mono P (treeSimHash_program_mono prims _ _ r rest) bad)
    obtain ⟨T, keyT, cardT⟩ := treeSimHash_region_keys_step prims P t cache S keys mid first
    have bound := ih mid first midGood T keyT r rest good
    have cost : (if TreeSimHashFresh P t cache then 1 else 0) ≤ n := by
      split_ifs with h
      · exact positive h
      · omega
    have eq : T.card + (n - if TreeSimHashFresh P t cache then 1 else 0) = S.card + n := by omega
    simpa only [eq] using bound

/-- The preceding terminal count also accepts a finite cover of the incoming cache. -/
theorem freshBudget_terminal_bound (P : Query C → Prop) {α : Type}
    {p : OracleComp (LocalSpec C) α} {cache : HashCache C} {n k : ℕ}
    (budget : TreeSimHashFreshBudget prims P p cache n)
    (initial : SplitCacheBound (splitRegionCache P cache) k)
    (r : α × HashCache C) (run : r ∈ support ((simulateQ (localAnswer prims) p).run cache))
    (good : ¬ CacheHasCollision (splitRegionCache P r.2)) :
    SplitCacheBound (splitRegionCache P r.2) (k + n) := by
  obtain ⟨V, size, cover⟩ := initial
  let S := V.filter (fun q => P q ∧ cache q ≠ none)
  have keys : TreeSimHashRegionKeys P cache S := by
    intro q
    simp only [S, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨cover q (by simpa [splitRegionCache, h.1] using h.2), h⟩⟩
  exact (freshBudget_terminal prims P budget S keys r run good).mono
    (Nat.add_le_add_right ((Finset.card_filter_le _ _).trans size) n)

section Ceremony

open LifetimeBridge LifetimeJointSim

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The fixed-input honest-point count already gives its exact fresh budget
from every cache in the small-budget range. No prefix-size premise is needed. -/
theorem selectedFresh_of_honest_small
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (hb : 0 < settings.batchSize) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (input : JointInput C) (dealt : DealtInputs D input.1) (q : ℕ)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (small : q + (treeSecrets circuits settings C input.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128)
    (cache : HashCache C) :
    TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      (selectedHash K circuits settings D A Z input) cache
      (q + (treeSecrets circuits settings C input.2.2.1 - 2 * prssKeyCount C)) := by
  rcases input with ⟨keys, top, tree, z⟩
  have terminal := treeSimHash_terminal_of_honest prims K circuits settings honest
    hb top tree D A keys z Z q dealt advBudget small
  have fresh := treeSimHash_terminal_fresh prims K circuits settings top tree D A keys z Z q
    advBudget small terminal
  have erased := freshBudget_map prims TreeSimHashBudgetDomain (fun r => (r.1.1, r.2)) fresh
  rw [treeSimHashProgram, normalized_erase] at erased
  exact freshBudget_subcache prims TreeSimHashBudgetDomain erased cache
    (fun _ _ absent => by simp at absent)

/-- The selected metadata and keys are the actual prefix output. Keygen
supplies dealt inputs support-wise, without a conditional distribution. -/
theorem selectedFresh_reached_small
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q : ℕ) (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (p : JointInput C × HashCache C) (reached : p ∈ support (jointPrefixRun prims pre))
    (small : q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128) :
    TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      (selectedHash K circuits settings D A Z p.1) p.2
      (q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C)) :=
  selectedFresh_of_honest_small prims K circuits settings honest hb D A Z p.1
    (jointPrefixRun_dealt prims D pre p.1 p.2 reached) q advBudget small p.2

/-- The terminal cache contains at most the prefix budget plus the selected
ceremony budget. Both the selected metadata and the incoming cache are retained. -/
theorem selected_terminal_small
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (p : JointInput C × HashCache C) (reached : p ∈ support (jointPrefixRun prims pre))
    (small : q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128)
    (r : (Bool × HiddenCache C) × HashCache C)
    (run : r ∈ support ((simulateQ (localAnswer prims)
      (selectedHash K circuits settings D A Z p.1)).run p.2))
    (good : ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2)) :
    SplitCacheBound (splitRegionCache TreeSimHashBudgetDomain r.2)
      (q0 + (q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C))) :=
  freshBudget_terminal_bound prims TreeSimHashBudgetDomain
    (selectedFresh_reached_small prims K circuits settings honest hb D pre A Z q advBudget p reached small)
    (prefix_cache_bound prims TreeSimHashBudgetDomain pre q0 preBudget p reached) r run good

/-- Exactly the portion of `SelectedFreshBudget` outside the range covered by
the existing honest-point premise. Its prefix, program and budget are unchanged. -/
def SelectedFreshLarge : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    ∀ p ∈ support (jointPrefixRun prims pre),
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain p.2) →
      2 ^ 128 ≤ q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C) →
      TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
        (selectedHash K circuits settings D A Z p.1) p.2
        (q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C))

/-- Conditional on A75, the original exact target is equivalent to its
large-budget branch. Neither premise is asserted as proved. -/
theorem selectedFreshBudget_iff_large
    (honest : TreeSimHashHonestBudget prims K circuits settings) :
    SelectedFreshBudget prims K circuits settings ↔ SelectedFreshLarge prims K circuits settings := by
  constructor
  · intro full hb D pre A Z q0 q preBudget advBudget p reached good _
    exact full hb D pre A Z q0 q preBudget advBudget p reached good
  · intro large hb D pre A Z q0 q preBudget advBudget p reached good
    by_cases small : q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C) < 2 ^ 128
    · exact selectedFresh_reached_small prims K circuits settings honest hb D pre A Z q advBudget p reached small
    · exact large hb D pre A Z q0 q preBudget advBudget p reached good (Nat.le_of_not_gt small)

end Ceremony

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFreshBudget.freshBudget_subcache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshBudget_subcache

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFreshBudget.freshBudget_terminal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshBudget_terminal_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFreshBudget.selectedFresh_reached_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedFresh_reached_small

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFreshBudget.selected_terminal_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_terminal_small

/-- info: 'ThresholdLeanXmssSecurity.LifetimeFreshBudget.selectedFreshBudget_iff_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedFreshBudget_iff_large

end ThresholdLeanXmssSecurity.LifetimeFreshBudget
