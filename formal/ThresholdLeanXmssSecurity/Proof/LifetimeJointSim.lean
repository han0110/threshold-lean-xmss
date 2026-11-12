import ThresholdLeanXmssSecurity.Proof.LifetimeJointHop
import ThresholdLeanXmssSecurity.Proof.TreeSaltGuard

/-!
# Collision accounting across adaptive ceremony selection

The selector and its cache remain in one distribution. A collision already
in that cache is charged once. A collision-free cache has at most `q0`
counted points, and the selected continuation has its own fresh-point budget.
The birthday estimate therefore averages the selected total squared budget;
it does not multiply a prefix error by the number of possible trees.

The pinned and current leanVM probability and cache modules were searched.
The threshold `treeSimHash_fresh_birthday_aux` already treats precisely the
regions and cached queries needed here, so it supplies the per-tail bound.

The component probability inequality is not itself a contextual coupling.
The contextual simulation interface is stated below; no conditioning
of the fixed-input component theorem is used.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeJointSim

open LifetimeBridge

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

variable {C : Committee} (prims : Primitives)

local instance : DecidableEq (JointInput C × HashCache C) := Classical.decEq _

/-- The same joint prefix has a bounded cache, even when its selected tree
depends on every answer in that cache. -/
theorem prefix_cache_bound (P : Query C → Prop) (pre : Selector C) (q0 : ℕ)
    (budget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (p : JointInput C × HashCache C) (hp : p ∈ support (jointPrefixRun prims pre)) :
    SplitCacheBound (splitRegionCache P p.2) q0 := by
  have empty : SplitCacheBound (splitRegionCache P (∅ : HashCache C)) 0 := by
    refine ⟨∅, by simp, ?_⟩
    intro q hq
    exact (hq (by simp [splitRegionCache])).elim
  simpa only [Nat.zero_add] using splitRegion_support_bound prims P (jointPrefix pre) q0
    (counted_splitRegionBound P budget) ∅ 0 empty p hp

/-- Prefix collisions are charged before inspecting the selected tree. -/
theorem prefix_collision_le (P : Query C → Prop) (pre : Selector C) (q0 : ℕ)
    (budget : IsQueryBoundP (jointPrefix pre) Counted q0) :
    (Pr[fun p => CacheHasCollision (splitRegionCache P p.2) |
      jointPrefixRun prims pre]).toReal ≤ splitRisk 0 q0 := by
  have h := splitRegion_birthday prims P (jointPrefix pre) q0
    (counted_splitRegionBound P budget)
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
  refine hr.trans ?_
  unfold splitRisk
  simp only [Nat.zero_add, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hq : q0 * (q0 - 1) ≤ q0 ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_left q0 (Nat.sub_le q0 1)
  exact_mod_cast hq

/-- A fresh-point certificate gives a birthday estimate from a fixed good
cache. Its contents may have been selected adaptively. -/
theorem tail_collision_le (P : Query C → Prop) {α : Type}
    (tail : OracleComp (LocalSpec C) α) (cache : HashCache C) (q0 n : ℕ)
    (budget : TreeSimHashFreshBudget prims P tail cache n)
    (good : ¬ CacheHasCollision (splitRegionCache P cache))
    (size : SplitCacheBound (splitRegionCache P cache) q0) :
    (Pr[fun r => CacheHasCollision (splitRegionCache P r.2) |
      (simulateQ (localAnswer prims) tail).run cache]).toReal ≤ splitRisk q0 n := by
  have finite : ∀ j ∈ Finset.range n, ((q0 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 ≠ ⊤ := by
    intros
    finiteness
  have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr finite)
    (treeSimHash_fresh_birthday_aux prims P budget q0 good size)
  rw [ENNReal.toReal_sum finite] at h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ← Finset.sum_div] at h
  refine h.trans ?_
  have sums : ∀ n : ℕ, 2 * (∑ j ∈ Finset.range n, ((q0 + j : ℕ) : ℝ)) ≤
      ((q0 + n : ℕ) : ℝ) ^ 2 - (q0 : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one] at *
      nlinarith
  unfold splitRisk
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256) (by positivity)).2
  nlinarith [sums n]

/-- Finite-support averaging on the complete prefix state, without requiring
the (infinite) type of oracle caches to be finite. -/
theorem prob_bind_eq_sum {α β : Type} [DecidableEq α]
    (draw : ProbComp α) (next : α → ProbComp β) (event : β → Prop) :
    (Pr[event | draw >>= next]).toReal =
      ∑ a ∈ finSupport draw, (Pr[= a | draw]).toReal * (Pr[event | next a]).toReal := by
  rw [probEvent_bind_eq_sum_finSupport, ENNReal.toReal_sum
    (fun _ _ => ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top)]
  simp only [ENNReal.toReal_mul]

set_option linter.constructorNameAsVariable false in
/-- Collision accounting for an adaptively selected continuation. The tail
certificate is required only on reached collision-free caches. -/
theorem joint_collision_le (P : Query C → Prop) {α : Type}
    (pre : Selector C) (q0 : ℕ) (n : Tree → ℕ)
    (tail : JointInput C → OracleComp (LocalSpec C) α)
    (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (tailBudget : ∀ p ∈ support (jointPrefixRun prims pre),
      ¬ CacheHasCollision (splitRegionCache P p.2) →
      TreeSimHashFreshBudget prims P (tail p.1) p.2 (n p.1.2.2.1)) :
    (Pr[fun r => CacheHasCollision (splitRegionCache P r.2) |
      jointPrefixRun prims pre >>= fun p =>
        (simulateQ (localAnswer prims) (tail p.1)).run p.2]).toReal ≤
      jointError prims pre (fun tree => splitRisk 0 (q0 + n tree)) := by
  classical
  let bad := fun p : JointInput C × HashCache C => CacheHasCollision (splitRegionCache P p.2)
  have pointwise (p : JointInput C × HashCache C) (hp : p ∈ finSupport (jointPrefixRun prims pre)) :
      (Pr[fun r => CacheHasCollision (splitRegionCache P r.2) |
        (simulateQ (localAnswer prims) (tail p.1)).run p.2]).toReal ≤
        (if bad p then 1 else 0) + splitRisk q0 (n p.1.2.2.1) := by
    have reached : p ∈ support (jointPrefixRun prims pre) := by
      with_reducible
        exact (mem_finSupport_iff_mem_support (jointPrefixRun prims pre) p).mp hp
    by_cases hb : bad p
    · rw [if_pos hb]
      have one : (Pr[fun r => CacheHasCollision (splitRegionCache P r.2) |
          (simulateQ (localAnswer prims) (tail p.1)).run p.2]).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
      exact one.trans (le_add_of_nonneg_right (splitRisk_nonneg _ _))
    · rw [if_neg hb, zero_add]
      exact tail_collision_le prims P (tail p.1) p.2 q0 _
        (tailBudget p reached hb) hb (prefix_cache_bound prims P pre q0 preBudget p reached)
  have prefixEvent : (Pr[bad | jointPrefixRun prims pre]).toReal =
      ∑ p ∈ finSupport (jointPrefixRun prims pre),
        (Pr[= p | jointPrefixRun prims pre]).toReal * (if bad p then 1 else 0) := by
    simpa only [bind_pure, probEvent_pure, apply_ite ENNReal.toReal, ENNReal.toReal_one,
      ENNReal.toReal_zero] using prob_bind_eq_sum (jointPrefixRun prims pre) (fun p => pure p) bad
  rw [prob_bind_eq_sum]
  calc _ ≤ ∑ p ∈ finSupport (jointPrefixRun prims pre),
        (Pr[= p | jointPrefixRun prims pre]).toReal *
          ((if bad p then 1 else 0) + splitRisk q0 (n p.1.2.2.1)) :=
      by
        with_reducible
          exact Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (pointwise p hp) ENNReal.toReal_nonneg
    _ = (Pr[bad | jointPrefixRun prims pre]).toReal +
        jointError prims pre (fun tree => splitRisk q0 (n tree)) := by
      rw [prefixEvent]
      simp only [jointError, selectedError, mul_add, Finset.sum_add_distrib]
    _ ≤ splitRisk 0 q0 + jointError prims pre (fun tree => splitRisk q0 (n tree)) := by
      dsimp only [bad]
      exact add_le_add (prefix_collision_le prims P pre q0 preBudget) le_rfl
    _ = jointError prims pre (fun tree => splitRisk 0 (q0 + n tree)) := by
      rw [← LifetimeJointHop.jointError_const prims pre (splitRisk 0 q0), ← jointError_add]
      congr 1
      funext tree
      simpa only [Nat.zero_add] using splitRisk_add 0 q0 (n tree)

section Ceremony

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The selected real ceremony in the existing nonprogramming language. -/
def selectedLocal (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    JointInput C → OracleComp (LocalSpec C + LocalSpec C) Bool
  | (keys, top, tree, z) => treeSimLocalRealGame K circuits settings top tree D A keys z Z

def jointLocal (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :=
  treeSimLocalRoles.adversary (jointPrefix pre) >>= selectedLocal K circuits settings D A Z

-- The local-role embedding used by `treeSim_localReal_eq` is private there.
set_option backward.isDefEq.respectTransparency false in
private theorem local_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimLocalWorld (treeSimLocalRoles.adversary p) = worldRoles.adversary p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query]
    change (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t))) >>=
      fun a => simulateQ treeSimLocalWorld (treeSimLocalRoles.adversary (k a))) = _
    rw [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
        fun a => worldRoles.adversary (k a) from rfl, adversary_query]
    simp only [ih]
    rfl

/-- This representation is the same complete game, including the selector. -/
theorem jointLocal_eq (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    simulateQ treeSimLocalWorld (jointLocal K circuits settings D pre A Z) =
      jointGame K circuits settings false D pre A Z := by
  simp only [jointLocal, jointGame, simulateQ_bind, local_adversary]
  apply bind_congr
  rintro ⟨keys, top, tree, z⟩
  exact treeSim_localReal_eq K circuits settings top tree D A keys z Z

/-- The tail retains its private stream cache while using the shared public cache. -/
def selectedHash (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (input : JointInput C) : OracleComp (LocalSpec C) (Bool × HiddenCache C) :=
  (simulateQ (treeSimHashLocal D) (selectedLocal K circuits settings D A Z input)).run ∅

/-- Joint cache normalization, retaining the whole selector rather than fixing
its output before the oracle is sampled. -/
theorem jointStream_cache (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    (simulateQ (streamWorld prims D) (jointGame K circuits settings false D pre A Z)).run
        (∅, ∅) =
      (fun r => (r.1.1, r.2, r.1.2)) <$>
        (jointPrefixRun prims pre >>= fun p =>
          (simulateQ (localAnswer prims) (selectedHash K circuits settings D A Z p.1)).run p.2) := by
  rw [jointGame, simulateQ_bind, treeSim_stream_adversary]
  simp only [StateT.run_bind, onHash, StateT.run_mk, jointPrefixRun, bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨⟨keys, top, tree, z⟩, cache⟩
  have h := congrArg (fun p => p.run (cache, (∅ : HiddenCache C)))
    (treeSimHashEvaluate_simulate prims D
      (treeSimLocalRealGame K circuits settings top tree D A keys z Z))
  simpa only [treeSim_localReal_eq, treeSimHashEvaluate, StateT.run_mk,
    selectedGame, Bool.false_eq_true, ↓reduceIte, selectedHash, selectedLocal] using h.symm

set_option linter.constructorNameAsVariable false in
/-- The birthday bound holds for collisions in the complete actual transcript,
including queries made before selection. Prefix/tail and tail/tail collisions
are both included. Only the fresh tail certificate is assumed. -/
theorem joint_logged_collision_le (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 : ℕ) (n : Tree → ℕ)
    (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (tailBudget : ∀ p ∈ support (jointPrefixRun prims pre),
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain p.2) →
      TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
        (selectedHash K circuits settings D A Z p.1) p.2 (n p.1.2.2.1)) :
    (Pr[fun r => TreeSimHashBudgetCollision r.2 |
      treeSimLoggedRun prims D (jointGame K circuits settings false D pre A Z)]).toReal ≤
      jointError prims pre (fun tree => splitRisk 0 (q0 + n tree)) := by
  have hcache :
      (Pr[fun r => CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2.1) |
        (simulateQ (streamWorld prims D)
          (jointGame K circuits settings false D pre A Z)).run (∅, ∅)]).toReal ≤
        jointError prims pre (fun tree => splitRisk 0 (q0 + n tree)) := by
    rw [jointStream_cache, probEvent_map]
    exact joint_collision_le prims TreeSimHashBudgetDomain pre q0 n
      (selectedHash K circuits settings D A Z) preBudget tailBudget
  have erase := congrArg
    (fun m => (Pr[fun r => CacheHasCollision
      (splitRegionCache TreeSimHashBudgetDomain r.2.1) | m]).toReal)
    (treeSimLoggedWorld_erase prims D
      (jointGame K circuits settings false D pre A Z) (∅, ∅) [])
  simp only [probEvent_map] at erase
  have hmono :
      Pr[fun r => TreeSimHashBudgetCollision r.2.2 |
        (simulateQ (treeSimLoggedWorld prims D)
          (jointGame K circuits settings false D pre A Z)).run ((∅, ∅), [])] ≤
      Pr[fun r => CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2.1.1) |
        (simulateQ (treeSimLoggedWorld prims D)
          (jointGame K circuits settings false D pre A Z)).run ((∅, ∅), [])] := by
    apply probEvent_mono
    intro r hr hbad
    rw [← jointLocal_eq K circuits settings D pre A Z] at hr
    have hc := treeSimHash_region_local_coherent prims TreeSimHashBudgetDomain
      treeSimHashBudgetDomain_not_fixed D (jointLocal K circuits settings D pre A Z)
      ((∅, ∅), []) r (by intro q h hq hh; simp [TreeSimHashAnswer] at hh) hr
    obtain ⟨a, b, h, ha, hb, hne, hah, hbh⟩ := hbad
    exact ⟨a, b, h, h, hne,
      by simpa only [splitRegionCache, if_pos ha] using hc a h ha hah,
      by simpa only [splitRegionCache, if_pos hb] using hc b h hb hbh, HEq.rfl⟩
  have h := (ENNReal.toReal_mono probEvent_ne_top hmono).trans (erase.trans_le hcache)
  simpa only [treeSimLoggedWorld_run, probEvent_map, List.nil_append,
    treeSimLoggedRun, StateT.run'_eq, probEvent_map, Function.comp_def] using h

/-- The exact contextual fresh-query certificate needed for the existing hash
budget. It is required on the actual reached cache, not on an empty cache
resampled after fixing the selected metadata. -/
def SelectedFreshBudget : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    ∀ p ∈ support (jointPrefixRun prims pre),
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain p.2) →
      TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
        (selectedHash K circuits settings D A Z p.1) p.2
        (q + (treeSecrets circuits settings C p.1.2.2.1 - 2 * prssKeyCount C))

/-- The collision part of the adaptive ceremony has the selected tree's
existing squared budget, with the D14 prefix budget included exactly once. -/
theorem joint_ceremony_collision_le
    (fresh : SelectedFreshBudget prims K circuits settings)
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    (Pr[fun r => TreeSimHashBudgetCollision r.2 |
      treeSimLoggedRun prims D (jointGame K circuits settings false D pre A Z)]).toReal ≤
      jointError prims pre (fun tree =>
        (((q0 + q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) /
          (2 * 2 ^ 256)) := by
  have h := joint_logged_collision_le prims K circuits settings D pre A Z q0
    (fun tree => q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C))
    preBudget (fresh hb D pre A Z q0 q preBudget advBudget)
  simpa only [splitRisk, Nat.zero_add, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    sub_zero, Nat.cast_pow, Nat.add_assoc] using h

/-!
The collision estimate above does not prove a simulator coupling, the check
estimate, or the salt estimates after selection. `TreeSimulationHop` bounds
fixed metadata and an empty initial cache. It does not expose those contextual
stages or `SelectedFreshBudget`. Conditioning on its input cannot create them.
In particular, `TreeSimStages` quantifies over `treeSimCommonPrefix` from the
empty cache; an adaptively reached prefix is not one of its premises. The next
proof step is to establish the actual terminal-cache count and round relations
from the reached state, preserving its earlier transcript.

The target is the original component implication. The D19
lifetime-game link is separate and is not asserted by this module.
-/
abbrev Remaining : Prop := JointSimulationFromComponent prims K circuits settings

end Ceremony

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSim.prefix_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_collision_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSim.joint_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_collision_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSim.jointStream_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointStream_cache

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSim.joint_logged_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_logged_collision_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSim.joint_ceremony_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_ceremony_collision_le

end ThresholdLeanXmssSecurity.LifetimeJointSim
