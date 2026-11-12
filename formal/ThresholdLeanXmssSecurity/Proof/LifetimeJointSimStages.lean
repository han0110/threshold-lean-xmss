import ThresholdLeanXmssSecurity.Proof.LifetimeFreshBudget
import ThresholdLeanXmssSecurity.Proof.TreeEvents3

/-!
# Contextual events after adaptive ceremony selection

The experiment retains selected metadata, the shared oracle cache, and the
complete real transcript. Small selected budgets use pathwise fresh-query
certificates; large selected budgets use the unit probability bound. Prefix
collisions are charged once before the selected bounds are averaged.

The private dealer runs after the selector, against its actual cache. Its
queries do not enter the real transcript. The equality of the projected real
distributions holds for each reached prefix state.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeJointSimStages

open LifetimeBridge LifetimeJointSim LifetimeFreshBudget

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

variable {C : Committee} (prims : Primitives)

local instance : DecidableEq (JointInput C × HashCache C) := Classical.decEq _

/-- The birthday charge when the selected tail is small; otherwise the unit bound. -/
def clippedRisk (q0 n : ℕ) : ℝ := if n < 2 ^ 128 then splitRisk q0 n else 1

theorem clippedRisk_nonneg (q0 n : ℕ) : 0 ≤ clippedRisk q0 n := by
  unfold clippedRisk
  split_ifs
  · exact splitRisk_nonneg _ _
  · positivity

set_option linter.constructorNameAsVariable false in
/-- Clipping concerns the selected tail and retains its actual starting cache. -/
theorem clipped_cache_bound {α : Type} (P : Query C → Prop)
    (pre : Selector C) (q0 : ℕ) (n : Tree → ℕ)
    (tail : JointInput C → OracleComp (LocalSpec C) α)
    (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (fresh : ∀ p ∈ support (jointPrefixRun prims pre),
      n p.1.2.2.1 < 2 ^ 128 →
      ¬ CacheHasCollision (splitRegionCache P p.2) →
      TreeSimHashFreshBudget prims P (tail p.1) p.2 (n p.1.2.2.1)) :
    (Pr[fun r => ¬ n r.1.2.2.1 < 2 ^ 128 ∨ CacheHasCollision (splitRegionCache P r.2.2) |
      jointPrefixRun prims pre >>= fun p =>
        (fun r => (p.1, r)) <$> (simulateQ (localAnswer prims) (tail p.1)).run p.2]).toReal ≤
      splitRisk 0 q0 + jointError prims pre (fun tree => clippedRisk q0 (n tree)) := by
  classical
  let bad := fun p : JointInput C × HashCache C => CacheHasCollision (splitRegionCache P p.2)
  have pointwise (p : JointInput C × HashCache C)
      (hp : p ∈ finSupport (jointPrefixRun prims pre)) :
      (Pr[fun r => ¬ n p.1.2.2.1 < 2 ^ 128 ∨ CacheHasCollision (splitRegionCache P r.2) |
        (simulateQ (localAnswer prims) (tail p.1)).run p.2]).toReal ≤
      (if bad p then 1 else 0) + clippedRisk q0 (n p.1.2.2.1) := by
    have reached : p ∈ support (jointPrefixRun prims pre) := by
      with_reducible
        exact (mem_finSupport_iff_mem_support (jointPrefixRun prims pre) p).mp hp
    have unit : (Pr[fun r => ¬ n p.1.2.2.1 < 2 ^ 128 ∨ CacheHasCollision (splitRegionCache P r.2) |
        (simulateQ (localAnswer prims) (tail p.1)).run p.2]).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
    by_cases small : n p.1.2.2.1 < 2 ^ 128
    · simp only [small, not_true_eq_false, false_or] at unit ⊢
      by_cases hb : bad p
      · rw [if_pos hb]
        exact unit.trans (le_add_of_nonneg_right (clippedRisk_nonneg _ _))
      · rw [if_neg hb, zero_add, clippedRisk, if_pos small]
        exact tail_collision_le prims P (tail p.1) p.2 q0 _ (fresh p reached small hb) hb
          (prefix_cache_bound prims P pre q0 preBudget p reached)
    · rw [clippedRisk, if_neg small]
      exact unit.trans (le_add_of_nonneg_left (by split_ifs <;> positivity))
  have prefixEvent : (Pr[bad | jointPrefixRun prims pre]).toReal =
      ∑ p ∈ finSupport (jointPrefixRun prims pre),
        (Pr[= p | jointPrefixRun prims pre]).toReal * (if bad p then 1 else 0) := by
    simpa only [bind_pure, probEvent_pure, apply_ite ENNReal.toReal, ENNReal.toReal_one,
      ENNReal.toReal_zero] using prob_bind_eq_sum (jointPrefixRun prims pre) (fun p => pure p) bad
  rw [prob_bind_eq_sum]
  simp only [probEvent_map, Function.comp_def]
  calc
    _ ≤ ∑ p ∈ finSupport (jointPrefixRun prims pre),
        (Pr[= p | jointPrefixRun prims pre]).toReal *
          ((if bad p then 1 else 0) + clippedRisk q0 (n p.1.2.2.1)) := by
      with_reducible
        exact Finset.sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_left (pointwise p hp) ENNReal.toReal_nonneg
    _ = (Pr[bad | jointPrefixRun prims pre]).toReal +
        jointError prims pre (fun tree => clippedRisk q0 (n tree)) := by
      rw [prefixEvent]
      simp only [jointError, selectedError, mul_add, Finset.sum_add_distrib]
    _ ≤ splitRisk 0 q0 + jointError prims pre (fun tree => clippedRisk q0 (n tree)) :=
      add_le_add (prefix_collision_le prims P pre q0 preBudget) le_rfl

section Ceremony

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Retain the selected input alongside the result of the original joint game. -/
def taggedGame (ideal : Bool) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (WorldSpec C) (JointInput C × Bool) := do
  let input ← worldRoles.adversary (jointPrefix pre)
  (fun b => (input, b)) <$> selectedGame K circuits settings ideal D A Z input

theorem taggedGame_erase (ideal : Bool) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    Prod.snd <$> taggedGame K circuits settings ideal D pre A Z =
      jointGame K circuits settings ideal D pre A Z := by
  simp only [taggedGame, jointGame, map_bind, Functor.map_map]
  apply bind_congr
  intro input
  exact id_map _

/-- The metadata, Boolean result, and complete counted/free transcript. -/
def trace (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :=
  treeSimLoggedRun prims D (taggedGame K circuits settings false D pre A Z)

theorem tagged_cache (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    (simulateQ (streamWorld prims D) (taggedGame K circuits settings false D pre A Z)).run (∅, ∅) =
      (fun r => ((r.1, r.2.1.1), r.2.2, r.2.1.2)) <$>
        (jointPrefixRun prims pre >>= fun p =>
          (fun r => (p.1, r)) <$>
            (simulateQ (localAnswer prims) (selectedHash K circuits settings D A Z p.1)).run p.2) := by
  rw [taggedGame, simulateQ_bind, treeSim_stream_adversary]
  simp only [StateT.run_bind, onHash, StateT.run_mk, jointPrefixRun, bind_map_left, map_bind,
    simulateQ_map, StateT.run_map, Functor.map_map]
  apply bind_congr
  rintro ⟨⟨keys, top, tree, z⟩, cache⟩
  have h := congrArg (fun p => p.run (cache, (∅ : HiddenCache C)))
    (treeSimHashEvaluate_simulate prims D
      (treeSimLocalRealGame K circuits settings top tree D A keys z Z))
  simp only [treeSim_localReal_eq, treeSimHashEvaluate, StateT.run_mk] at h
  simp only [selectedGame, selectedHash, selectedLocal, Bool.false_eq_true, ↓reduceIte, ← h,
    Functor.map_map]

set_option linter.constructorNameAsVariable false in
/-- The clipped collision estimate includes selector queries in the transcript. -/
theorem clipped_logged_bound (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 : ℕ) (n : Tree → ℕ)
    (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (fresh : ∀ p ∈ support (jointPrefixRun prims pre),
      n p.1.2.2.1 < 2 ^ 128 →
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain p.2) →
      TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
        (selectedHash K circuits settings D A Z p.1) p.2 (n p.1.2.2.1)) :
    (Pr[fun r => ¬ n r.1.1.2.2.1 < 2 ^ 128 ∨ TreeSimHashBudgetCollision r.2 |
      trace prims K circuits settings D pre A Z]).toReal ≤
      splitRisk 0 q0 + jointError prims pre (fun tree => clippedRisk q0 (n tree)) := by
  have cacheBound :
      (Pr[fun r => ¬ n r.1.1.2.2.1 < 2 ^ 128 ∨
        CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2.1) |
        (simulateQ (streamWorld prims D)
          (taggedGame K circuits settings false D pre A Z)).run (∅, ∅)]).toReal ≤
      splitRisk 0 q0 + jointError prims pre (fun tree => clippedRisk q0 (n tree)) := by
    rw [tagged_cache, probEvent_map]
    exact clipped_cache_bound prims TreeSimHashBudgetDomain pre q0 n
      (selectedHash K circuits settings D A Z) preBudget fresh
  have erase := congrArg (fun m => (Pr[fun r => ¬ n r.1.1.2.2.1 < 2 ^ 128 ∨
      CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2.1) | m]).toReal)
    (treeSimLoggedWorld_erase prims D
      (taggedGame K circuits settings false D pre A Z) (∅, ∅) [])
  simp only [probEvent_map] at erase
  have mono :
      Pr[fun r => ¬ n r.1.1.2.2.1 < 2 ^ 128 ∨ TreeSimHashBudgetCollision r.2.2 |
        (simulateQ (treeSimLoggedWorld prims D)
          (taggedGame K circuits settings false D pre A Z)).run ((∅, ∅), [])] ≤
      Pr[fun r => ¬ n r.1.1.2.2.1 < 2 ^ 128 ∨
        CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2.1.1) |
        (simulateQ (treeSimLoggedWorld prims D)
          (taggedGame K circuits settings false D pre A Z)).run ((∅, ∅), [])] := by
    apply probEvent_mono
    intro r hr event
    rcases event with large | bad
    · exact Or.inl large
    apply Or.inr
    have project : (r.1.2, r.2) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (jointGame K circuits settings false D pre A Z)).run ((∅, ∅), [])) := by
      rw [← taggedGame_erase K circuits settings false D pre A Z,
        simulateQ_map, StateT.run_map, support_map]
      exact ⟨r, hr, rfl⟩
    rw [← jointLocal_eq K circuits settings D pre A Z] at project
    have coherent := treeSimHash_region_local_coherent prims TreeSimHashBudgetDomain
      treeSimHashBudgetDomain_not_fixed D (LifetimeJointSim.jointLocal K circuits settings D pre A Z)
      ((∅, ∅), []) (r.1.2, r.2)
      (by intro q h hq hh; simp [TreeSimHashAnswer] at hh) project
    obtain ⟨a, b, h, ha, hb, ne, ah, bh⟩ := bad
    exact ⟨a, b, h, h, ne,
      by simpa only [splitRegionCache, if_pos ha] using coherent a h ha ah,
      by simpa only [splitRegionCache, if_pos hb] using coherent b h hb bh, HEq.rfl⟩
  have h := (ENNReal.toReal_mono probEvent_ne_top mono).trans (erase.trans_le cacheBound)
  simpa only [treeSimLoggedWorld_run, probEvent_map, List.nil_append,
    trace, treeSimLoggedRun, StateT.run'_eq, probEvent_map, Function.comp_def] using h

/-- The selected tail's public hash allowance. -/
def tailBudget (q : ℕ) (tree : Tree) : ℕ :=
  q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)

def saltGuessBudget (q : ℕ) (tree : Tree) : ℝ :=
  let H := treeBatches settings tree * (C.t * termCount C)
  2 * H * (q + H) / 2 ^ 256

def saltReuseBudget (tree : Tree) : ℝ :=
  ((treeBatches settings tree * termCount C : ℕ) : ℝ) ^ 2 / 2 ^ 257

theorem clipped_hash_arith (q0 q : ℕ) (tree : Tree) :
    splitRisk 0 q0 + clippedRisk q0 (tailBudget (C := C) circuits settings q tree) +
      (if tailBudget (C := C) circuits settings q tree < 2 ^ 128 then
        saltGuessBudget (C := C) settings (q0 + q) tree else 0) +
      (if tailBudget (C := C) circuits settings q tree < 2 ^ 128 then
        saltReuseBudget (C := C) settings tree else 0) ≤
      (((q0 + tailBudget (C := C) circuits settings q tree : ℕ) : ℝ) ^ 2) / 2 ^ 256 := by
  by_cases small : tailBudget (C := C) circuits settings q tree < 2 ^ 128
  · rw [clippedRisk, if_pos small, if_pos small, if_pos small]
    rw [show splitRisk 0 q0 + splitRisk q0 (tailBudget (C := C) circuits settings q tree) =
      (((q0 + tailBudget (C := C) circuits settings q tree : ℕ) : ℝ) ^ 2) / (2 * 2 ^ 256) by
        simp only [splitRisk, Nat.zero_add, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
        ring]
    apply treeSimHash_union2_arith _ _ _ _ (by positivity) (by positivity) (by positivity)
    have cap := treeSimHash_reuse_capacity (C := C) circuits settings tree
    exact_mod_cast (show q0 + q + 2 * (treeBatches settings tree * (C.t * termCount C)) +
      2 * (treeBatches settings tree * termCount C) ≤
      q0 + tailBudget (C := C) circuits settings q tree by unfold tailBudget; omega)
  · rw [clippedRisk, if_neg small, if_neg small, if_neg small, add_zero, add_zero]
    have unit := treeSimHash_unit_budget
      (tailBudget (C := C) circuits settings q tree) (Nat.le_of_not_gt small)
    refine (add_le_add (le_refl (splitRisk 0 q0)) unit).trans ?_
    unfold splitRisk
    simp only [Nat.zero_add, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
      Nat.cast_add, Nat.cast_pow] at unit ⊢
    have square : (q0 : ℝ) ^ 2 / 2 +
        (tailBudget (C := C) circuits settings q tree : ℝ) ^ 2 ≤
        ((q0 : ℝ) + tailBudget (C := C) circuits settings q tree) ^ 2 := by
      nlinarith [sq_nonneg (q0 : ℝ), mul_nonneg (Nat.cast_nonneg (α := ℝ) q0)
        (Nat.cast_nonneg (α := ℝ) (tailBudget (C := C) circuits settings q tree))]
    convert div_le_div_of_nonneg_right square (by positivity : (0 : ℝ) ≤ 2 ^ 256) using 1
    ring

theorem hash_union_clipped {α : Type} (D : C.Coalition) (p : ProbComp (α × TreeSimLog C))
    (small : α → Prop) :
    (Pr[fun r => TreeSimHashBad3 D r.2 | p]).toReal ≤
      (Pr[fun r => ¬ small r.1 ∨ TreeSimHashBudgetCollision r.2 | p]).toReal +
      (Pr[fun r => small r.1 ∧ ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal +
      (Pr[fun r => small r.1 ∧ ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | p]).toReal := by
  let B := fun r : α × TreeSimLog C => ¬ small r.1 ∨ TreeSimHashBudgetCollision r.2
  let G := fun r : α × TreeSimLog C => small r.1 ∧ ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2
  let U := fun r : α × TreeSimLog C => small r.1 ∧ ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2
  have event : Pr[fun r => TreeSimHashBad3 D r.2 | p] ≤ Pr[fun r => (B r ∨ G r) ∨ U r | p] := by
    apply probEvent_mono
    intro r _ bad
    by_cases hs : small r.1
    · by_cases hc : TreeSimHashBudgetCollision r.2
      · exact Or.inl (Or.inl (Or.inr hc))
      · rcases (treeSimHashBad3_iff D r.2).mp bad with collision | guess | reuse
        · exact (hc collision).elim
        · exact Or.inl (Or.inr ⟨hs, fun h => hc (treeSimHashBudgetCollision_of_collision _ h), guess⟩)
        · exact Or.inr ⟨hs, hc, reuse⟩
    · exact Or.inl (Or.inl (Or.inl hs))
  have sumBound := event.trans ((probEvent_or_le p (fun r => B r ∨ G r) U).trans
    (add_le_add (probEvent_or_le p B G) le_rfl))
  have finite : (Pr[B | p] + Pr[G | p] + Pr[U | p]) ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩, probEvent_ne_top⟩
  have h := ENNReal.toReal_mono finite sumBound
  simpa only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) probEvent_ne_top,
    ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] using h

/-- Guarded salt estimates on the complete joint transcript, restricted to
small selected tails. Prefix calls are included in the counted allowance. -/
def JointSaltBounds : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    (Pr[fun r => tailBudget (C := C) circuits settings q r.1.1.2.2.1 < 2 ^ 128 ∧
        ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 |
      trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => if tailBudget (C := C) circuits settings q tree < 2 ^ 128
        then saltGuessBudget (C := C) settings (q0 + q) tree else 0) ∧
    (Pr[fun r => tailBudget (C := C) circuits settings q r.1.1.2.2.1 < 2 ^ 128 ∧
        ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
      trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => if tailBudget (C := C) circuits settings q tree < 2 ^ 128
        then saltReuseBudget (C := C) settings tree else 0)

/-- The complete joint hash event fits the fixed squared allowance, using
only small-tail fresh certificates. -/
theorem joint_hash_bound
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salts : JointSaltBounds prims K circuits settings)
    (hb : 0 < settings.batchSize) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ) (preBudget : IsQueryBoundP (jointPrefix pre) Counted q0)
    (advBudget : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    (Pr[fun r => TreeSimHashBad3 D r.2 | trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree =>
        (((q0 + tailBudget (C := C) circuits settings q tree : ℕ) : ℝ) ^ 2) / 2 ^ 256) := by
  have collision := clipped_logged_bound prims K circuits settings D pre A Z q0
    (tailBudget (C := C) circuits settings q) preBudget (fun p hp small _ =>
      selectedFresh_reached_small prims K circuits settings honest hb D pre A Z q advBudget p hp small)
  obtain ⟨guess, reuse⟩ := salts hb D pre A Z q0 q preBudget advBudget
  have bound := (hash_union_clipped D (trace prims K circuits settings D pre A Z)
    (fun r => tailBudget (C := C) circuits settings q r.1.2.2.1 < 2 ^ 128)).trans
      (add_le_add (add_le_add collision guess) reuse)
  rw [← LifetimeJointHop.jointError_const prims pre (splitRisk 0 q0),
    ← jointError_add, ← jointError_add, ← jointError_add] at bound
  apply bound.trans
  unfold jointError
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left
    (clipped_hash_arith circuits settings q0 q p.1.2.2.1) ENNReal.toReal_nonneg

/-- The selector leaves its actual public/private cache and counted transcript. -/
def loggedPrefix (D : C.Coalition) (pre : Selector C) :=
  (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary (jointPrefix pre))).run ((∅, ∅), [])

theorem trace_split (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    trace prims K circuits settings D pre A Z = (do
      let p ← loggedPrefix prims D pre
      (fun r => ((p.1, r.1), r.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D)
          (selectedGame K circuits settings false D A Z p.1)).run p.2) := by
  simp only [trace, treeSimLoggedRun_eq_run, taggedGame, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, map_bind, Functor.map_map, loggedPrefix]

/-- A private, input-dependent dealer, followed by the original real continuation. -/
def ghost {β : Type} (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (dealer : JointInput C → OracleComp (LocalSpec C) β) := do
  let p ← loggedPrefix prims D pre
  let d ← (simulateQ (localAnswer prims) (dealer p.1)).run p.2.1.1
  let r ← (simulateQ (treeSimLoggedWorld prims D)
    (selectedGame K circuits settings false D A Z p.1)).run ((d.2, p.2.1.2), p.2.2)
  pure ((p.1, d.1), r.1, r.2.2)

/-- Erasing the private dealer preserves the selected input and the full real log. -/
theorem ghost_erase {β : Type} (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (dealer : JointInput C → OracleComp (LocalSpec C) β) :
    𝒟[(fun r => ((r.1.1, r.2.1), r.2.2)) <$>
      ghost prims K circuits settings D pre A Z dealer] =
      𝒟[trace prims K circuits settings D pre A Z] := by
  rw [trace_split]
  simp only [ghost, map_bind, bind_pure_comp]
  apply evalDist_bind_congr'
  intro p
  have h := treeSim_logged_padding prims D (dealer p.1)
    (selectedLocal K circuits settings D A Z p.1) p.2
  have local_eq : simulateQ treeSimLocalWorld (selectedLocal K circuits settings D A Z p.1) =
      selectedGame K circuits settings false D A Z p.1 := by
    rcases p.1 with ⟨keys, top, tree, z⟩
    exact treeSim_localReal_eq K circuits settings top tree D A keys z Z
  rw [local_eq] at h
  have mapped := congrArg (fun d => (fun r => ((p.1, r.1), r.2)) <$> d) h
  simpa only [← evalDist_map, map_bind, Functor.map_map] using mapped

/-- Actual initialization after the selecting prefix and private dealer. -/
def commonPrefix {β : Type} (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (dealer : JointInput C → OracleComp (LocalSpec C) β) := do
  let p ← loggedPrefix prims D pre
  let d ← (simulateQ (localAnswer prims) (dealer p.1)).run p.2.1.1
  let state ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.start (corruptInputs D p.1.1) p.1.2.2.2))).run ((d.2, p.2.1.2), p.2.2)
  pure ((p.1, d.1), state)

/-- Factor the selected real execution at the common dealer/start boundary. -/
theorem ghost_split {β : Type} (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (dealer : JointInput C → OracleComp (LocalSpec C) β) :
    ghost prims K circuits settings D pre A Z dealer = (do
      let p ← commonPrefix prims D pre A dealer
      (fun r => (p.1, r)) <$> treeSimRealFinish prims K circuits settings p.1.1.2.1 p.1.1.2.2.1
        D A p.1.1.1 Z p.2.1 p.2.2) := by
  simp only [ghost, commonPrefix, bind_assoc, pure_bind]
  apply bind_congr
  intro p
  apply bind_congr
  intro d
  rcases p.1 with ⟨keys, top, tree, z⟩
  simp only [selectedGame, Bool.false_eq_true, ↓reduceIte, treeRealGame, distinguish,
    realExecution, simulateQ_bind, StateT.run_bind, treeSimRealFinish, map_bind,
    bind_pure_comp, bind_assoc, Functor.map_map]

/-- The shared initialization contains no private-stream reads. -/
theorem commonPrefix_hidden {β : Type} (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (dealer : JointInput C → OracleComp (LocalSpec C) β)
    (p : (JointInput C × β) × (A.State × TreeSimState C))
    (reached : p ∈ support (commonPrefix prims D pre A dealer)) : p.2.2.1.2 = ∅ := by
  simp only [commonPrefix, mem_support_bind_iff, mem_support_pure_iff] at reached
  obtain ⟨before, prefixRun, d, _, state, startRun, rfl⟩ := reached
  have first := treeSim_local_private prims D (jointPrefix pre) ∅ ∅ [] before prefixRun
  have second := treeSim_local_private prims D
    (A.start (corruptInputs D before.1.1) before.1.2.2.2)
    d.2 before.2.1.2 before.2.2 state startRun
  exact second.trans first

/-- The actual dealer ceremony for the parameter and seeds retained by the selector. -/
def dealerProgram (parameter : JointInput C → PublicParameter)
    (seeds : JointInput C → C.Term → HashOutput) (input : JointInput C) :=
  liftComp (dealerCeremony circuits settings (parameter input) (seeds input)
    input.2.1 input.2.2.1) (LocalSpec C)

/-- The ideal phase starts from the public cache of the same common initialization. -/
def idealCommon (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput) := do
  let p ← commonPrefix prims D pre A (dealerProgram circuits settings parameter seeds)
  (treeSimIdealFinish prims K circuits settings p.1.1.2.1 p.1.1.2.2.1 D A
    (parameter p.1.1) (seeds p.1.1) Z p.2.1 p.1.2).run' p.2.2.1.1

/-- Shared ghost padding preserves the local stage-coupling conclusion. -/
theorem roundStages_padded (events : TreeSimEvents C E)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (hidden : s.1.2 = ∅)
    (certificates : ∃ padding : OracleComp (LocalSpec C) Unit,
      ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run s.1.1),
        Nonempty (TreeSimRoundStages prims K circuits settings events top tree D A
          parameter seeds pairs z Z dealt state ((r.2, s.1.2), s.2))) :
    RelTriple
      (treeSimRealFinish prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) Z state s)
      ((treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' s.1.1)
      (fun a b =>
        let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z a.2
        (flags.1 = true ∨ flags.2 = true) ∨ (a.1 = true ↔ b = true)) := by
  obtain ⟨padding, certificates⟩ := certificates
  apply relTriple_of_evalDist_eq_left
    (treeSimRealFinish_padding prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) Z state s padding).symm
  apply relTriple_of_evalDist_eq_right
    (treeSimIdealFinish_padding prims K circuits settings top tree D A
      parameter seeds Z state dealt s.1.1 padding)
  apply relTriple_bind (treeSim_relTriple_support (relTriple_refl _))
  intro r r' hr
  rcases hr with ⟨rfl, reached, _⟩
  obtain ⟨certificate⟩ := certificates r reached
  exact treeSimRoundStages_run prims K circuits settings events top tree D A parameter seeds pairs z Z
    dealt state ((r.2, s.1.2), s.2) hidden certificate

/-- Round-stage certificates compose over the actual joint common prefix. -/
theorem joint_roundStages_run (events : TreeSimEvents C E)
    (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput)
    (pairs : JointInput C → C.Pair → HashOutput)
    (valid : ∀ p ∈ support (commonPrefix prims D pre A (dealerProgram circuits settings parameter seeds)),
      p.1.1.1 = dealtKeys (parameter p.1.1) (seeds p.1.1) (pairs p.1.1))
    (stages : ∀ p ∈ support (commonPrefix prims D pre A (dealerProgram circuits settings parameter seeds)),
      ∃ padding : OracleComp (LocalSpec C) Unit,
      ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
        Nonempty (TreeSimRoundStages prims K circuits settings events p.1.1.2.1 p.1.1.2.2.1 D A
          (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) p.1.1.2.2.2 Z p.1.2 p.2.1
          ((r.2, p.2.2.1.2), p.2.2.2))) :
    RelTriple
      (ghost prims K circuits settings D pre A Z (dealerProgram circuits settings parameter seeds))
      (idealCommon prims K circuits settings D pre A Z parameter seeds)
      (fun a b =>
        let flags := events a.1.1.2.1 a.1.1.2.2.1 D A a.1.1.1 a.1.1.2.2.2 Z a.2.2
        (flags.1 = true ∨ flags.2 = true) ∨ (a.2.1 = true ↔ b = true)) := by
  rw [ghost_split]
  unfold idealCommon
  apply relTriple_bind (treeSim_relTriple_support (relTriple_refl _))
  intro p p' hp
  rcases hp with ⟨rfl, reached, _⟩
  have h := roundStages_padded prims K circuits settings events p.1.1.2.1 p.1.1.2.2.1 D A
    (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) p.1.1.2.2.2 Z p.1.2 p.2.1 p.2.2
    (commonPrefix_hidden prims D pre A _ p reached) (stages p reached)
  rw [← valid p reached] at h
  have mapped := relTriple_map
    (R := fun (a : (JointInput C × (Option TreeOutput × List (List (List Bit)))) ×
        (Bool × TreeSimLog C)) (b : Bool) =>
      let flags := events a.1.1.2.1 a.1.1.2.2.1 D A a.1.1.1 a.1.1.2.2.2 Z a.2.2
      (flags.1 = true ∨ flags.2 = true) ∨ (a.2.1 = true ↔ b = true))
    (f := fun r => (p.1, r)) (g := id) h
  simpa only [id_map] using mapped

/-- Cache-preserving normalization of the ideal ceremony, with a dealer-first prefix. -/
theorem ideal_from_cache (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux) (cache : HashCache C) :
    𝒟[(simulateQ (worldAnswer prims)
      (treeIdealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z)).run' cache] =
    𝒟[do
      let d ← (simulateQ (localAnswer prims)
        (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run cache
      let s ← (simulateQ (localAnswer prims)
        (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z)).run d.2
      (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z s.1 d.1).run' s.2] := by
  rw [treeSim_idealGame]
  have commute := (commutes_simulateQ (localAnswer prims)
    (fun t u => commutes_of_isAtom (isAtom_localAnswer prims t) (isAtom_localAnswer prims u))
    (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z)
    (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).bind
      (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z) cache
  have projected := congrArg (fun d => Prod.fst <$> d) commute
  simpa only [treeSimIdealRun, simulateQ_bind, TprfSecurityProof.simulateQ_adversary,
    simulateQ_free, StateT.run'_eq, StateT.run_bind, treeSimIdealFinish, StateT.run_mk,
    treeSimPhase_run, bind_map_left, map_bind, ← evalDist_map] using projected

theorem loggedPrefix_marginal (D : C.Coalition) (pre : Selector C) :
    (fun p => (p.1, p.2.1.1)) <$> loggedPrefix prims D pre = jointPrefixRun prims pre :=
  treeSimLoggedWorld_start prims D (jointPrefix pre) ∅ []

/-- Dealt-key validity is derived from the actual sampled prefix. -/
theorem loggedPrefix_dealt (D : C.Coalition) (pre : Selector C)
    (p : JointInput C × TreeSimState C) (reached : p ∈ support (loggedPrefix prims D pre)) :
    DealtInputs D p.1.1 := by
  apply jointPrefixRun_dealt prims D pre p.1 p.2.1.1
  rw [← loggedPrefix_marginal prims D pre, support_map]
  exact ⟨p, reached, rfl⟩

/-- One deterministic representation of the dealt keys for every supported
selector output; no new key sampling is introduced. -/
theorem dealtData_exists (D : C.Coalition) (pre : Selector C) :
    ∃ (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput)
      (pairs : JointInput C → C.Pair → HashOutput),
      ∀ p ∈ support (loggedPrefix prims D pre),
        p.1.1 = dealtKeys (parameter p.1) (seeds p.1) (pairs p.1) := by
  classical
  have witnesses (input : JointInput C) : ∃ parameter seeds pairs,
      (∃ state, (input, state) ∈ support (loggedPrefix prims D pre)) →
        input.1 = dealtKeys parameter seeds pairs := by
    by_cases reached : ∃ state, (input, state) ∈ support (loggedPrefix prims D pre)
    · obtain ⟨state, hstate⟩ := reached
      obtain ⟨parameter, seeds, pairs, keys⟩ := loggedPrefix_dealt prims D pre (input, state) hstate
      exact ⟨parameter, seeds, pairs, fun _ => funext keys⟩
    · exact ⟨0, fun _ => 0, fun _ => 0, fun h => (reached h).elim⟩
  choose parameter seeds pairs valid using witnesses
  exact ⟨parameter, seeds, pairs, fun p hp => valid p.1 ⟨p.2, hp⟩⟩

/-- The normalized ideal continuation is the original joint ideal experiment. -/
theorem idealCommon_eq (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput)
    (pairs : JointInput C → C.Pair → HashOutput)
    (valid : ∀ p ∈ support (loggedPrefix prims D pre),
      p.1.1 = dealtKeys (parameter p.1) (seeds p.1) (pairs p.1)) :
    𝒟[idealCommon prims K circuits settings D pre A Z parameter seeds] =
      𝒟[Prod.fst <$> runWorld prims (jointGame K circuits settings true D pre A Z)] := by
  rw [jointWorld_run, ← loggedPrefix_marginal prims D pre, bind_map_left]
  simp only [idealCommon, commonPrefix, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro p reached
  have hidden := treeSim_local_private prims D (jointPrefix pre) ∅ ∅ [] p reached
  rw [hidden]
  have startEq (d : (Option TreeOutput × List (List (List Bit))) × HashCache C) :
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (A.start (corruptInputs D p.1.1) p.1.2.2.2))).run ((d.2, ∅), p.2.2) >>=
        fun s => (treeSimIdealFinish prims K circuits settings p.1.2.1 p.1.2.2.1 D A
          (parameter p.1) (seeds p.1) Z s.1 d.1).run' s.2.1.1) =
      ((simulateQ (localAnswer prims) (A.start (corruptInputs D p.1.1) p.1.2.2.2)).run d.2 >>=
        fun s => (treeSimIdealFinish prims K circuits settings p.1.2.1 p.1.2.2.1 D A
          (parameter p.1) (seeds p.1) Z s.1 d.1).run' s.2) := by
    rw [← treeSimLoggedWorld_start prims D _ d.2 p.2.2, bind_map_left]
  simp only [startEq]
  change 𝒟[(simulateQ (localAnswer prims) (dealerProgram circuits settings parameter seeds p.1)).run p.2.1.1 >>=
      fun d => (simulateQ (localAnswer prims) (A.start (corruptInputs D p.1.1) p.1.2.2.2)).run d.2 >>=
      fun s => (treeSimIdealFinish prims K circuits settings p.1.2.1 p.1.2.2.1 D A
        (parameter p.1) (seeds p.1) Z s.1 d.1).run' s.2] = _
  have normalized := ideal_from_cache prims K circuits settings p.1.2.1 p.1.2.2.1 D A Z
    (parameter p.1) (seeds p.1) (pairs p.1) p.1.2.2.2 p.2.1.1
  rw [← valid p reached] at normalized
  simpa only [dealerProgram, selectedGame, ↓reduceIte] using normalized.symm

/-- The two event flags evaluated on the selected input and actual transcript. -/
def flags (events : TreeSimEvents C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (r : (JointInput C × Bool) × TreeSimLog C) :=
  events r.1.1.2.1 r.1.1.2.2.1 D A r.1.1.1 r.1.1.2.2.2 Z r.2

/-- Round certificates yield a coupling to the original joint ideal game. -/
theorem trace_coupling (events : TreeSimEvents C E)
    (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput)
    (pairs : JointInput C → C.Pair → HashOutput)
    (valid : ∀ p ∈ support (loggedPrefix prims D pre),
      p.1.1 = dealtKeys (parameter p.1) (seeds p.1) (pairs p.1))
    (stages : ∀ p ∈ support (commonPrefix prims D pre A (dealerProgram circuits settings parameter seeds)),
      ∃ padding : OracleComp (LocalSpec C) Unit,
      ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
        Nonempty (TreeSimRoundStages prims K circuits settings events p.1.1.2.1 p.1.1.2.2.1 D A
          (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) p.1.1.2.2.2 Z p.1.2 p.2.1
          ((r.2, p.2.2.1.2), p.2.2.2))) :
    RelTriple (trace prims K circuits settings D pre A Z)
      (Prod.fst <$> runWorld prims (jointGame K circuits settings true D pre A Z))
      (fun a b => ((flags events D A Z a).1 = true ∨ (flags events D A Z a).2 = true) ∨
        (a.1.2 = true ↔ b = true)) := by
  have validCommon : ∀ p ∈ support (commonPrefix prims D pre A
      (dealerProgram circuits settings parameter seeds)),
      p.1.1.1 = dealtKeys (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) := by
    intro p hp
    simp only [commonPrefix, mem_support_bind_iff, mem_support_pure_iff] at hp
    obtain ⟨before, hbefore, _, _, _, _, rfl⟩ := hp
    exact valid before hbefore
  have hc := joint_roundStages_run prims K circuits settings events D pre A Z
    parameter seeds pairs validCommon stages
  have mapped := relTriple_map
    (R := fun (a : (JointInput C × Bool) × TreeSimLog C) (b : Bool) =>
      ((flags events D A Z a).1 = true ∨ (flags events D A Z a).2 = true) ∨
        (a.1.2 = true ↔ b = true))
    (f := fun r : (JointInput C × (Option TreeOutput × List (List (List Bit)))) ×
      (Bool × TreeSimLog C) => ((r.1.1, r.2.1), r.2.2)) (g := id) hc
  simp only [id_map] at mapped
  with_reducible
    exact relTriple_of_evalDist_eq_right
      (idealCommon_eq prims K circuits settings D pre A Z parameter seeds pairs valid)
      (relTriple_of_evalDist_eq_left
        (ghost_erase prims K circuits settings D pre A Z
          (dealerProgram circuits settings parameter seeds)).symm mapped)

/-- Round certificates at the actual selector/dealer/start boundary, with
the selector-derived dealt-key representation retained. -/
def ContextualStages (events : Selector C → TreeSimEvents C E) : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q0 + q < 2 ^ 128 →
    ∃ (parameter : JointInput C → PublicParameter) (seeds : JointInput C → C.Term → HashOutput)
      (pairs : JointInput C → C.Pair → HashOutput),
      (∀ p ∈ support (loggedPrefix prims D pre),
        p.1.1 = dealtKeys (parameter p.1) (seeds p.1) (pairs p.1)) ∧
      ∀ p ∈ support (commonPrefix prims D pre A (dealerProgram circuits settings parameter seeds)),
        ∃ padding : OracleComp (LocalSpec C) Unit,
        ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
          Nonempty (TreeSimRoundStages prims K circuits settings (events pre) p.1.1.2.1 p.1.1.2.2.1 D A
            (parameter p.1.1) (seeds p.1.1) (pairs p.1.1) p.1.1.2.2.2 Z p.1.2 p.2.1
            ((r.2, p.2.2.1.2), p.2.2.2))

/-- The contextual check flag has the original check allowance at `q0 + q`. -/
def ContextualCheckBound (events : Selector C → TreeSimEvents C E) : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q0 + q < 2 ^ 128 →
    (Pr[fun r => (flags (events pre) D A Z r).2 = true |
      trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => treeCheckError (E := E) circuits settings tree (q0 + q))

theorem trace_acceptance (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    (Pr[fun r => r.1.2 = true | trace prims K circuits settings D pre A Z]).toReal =
      reductionIdeal prims D (jointGame K circuits settings false D pre A Z) := by
  have erase : (fun r => r.1.2) <$> trace prims K circuits settings D pre A Z =
      (simulateQ (streamWorld prims D) (jointGame K circuits settings false D pre A Z)).run' (∅, ∅) := by
    calc
      _ = Prod.snd <$> (Prod.fst <$> treeSimLoggedRun prims D
          (taggedGame K circuits settings false D pre A Z)) := by
        simp only [Functor.map_map, trace]
      _ = Prod.snd <$> (simulateQ (streamWorld prims D)
          (taggedGame K circuits settings false D pre A Z)).run' (∅, ∅) := by
        rw [treeSim_log_erase]
      _ = _ := by
        rw [← taggedGame_erase K circuits settings false D pre A Z]
        simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [reductionIdeal, prfIdealExp_prgReduction, ← erase, probOutput_map]

theorem jointError_mono (pre : Selector C) {e f : Tree → ℝ} (bound : ∀ tree, e tree ≤ f tree) :
    jointError prims pre e ≤ jointError prims pre f := by
  unfold jointError
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left (bound p.1.2.2.1) ENNReal.toReal_nonneg

include K in
theorem checkError_nonneg (tree : Tree) (q : ℕ) :
    0 ≤ treeCheckError (E := E) circuits settings tree q := by
  letI : Inhabited E := ⟨0⟩
  letI : SampleableType E := SampleableType.ofFintype E
  unfold treeCheckError
  exact mul_nonneg (Nat.cast_nonneg _) (checkErrorOf_nonneg K _ _ _)

/-- The joint simulation bridge with contextual round, check, and salt
certificates. The error and the one complete-run reduction are unchanged. -/
theorem jointSimulationFromComponent_of_contextual
    (events : Selector C → TreeSimEvents C E)
    (hashFlag : ∀ pre top tree D A x z Z log,
      (events pre top tree D A x z Z log).1 = decide (TreeSimHashBad3 D log))
    (stages : ContextualStages prims K circuits settings events)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salts : JointSaltBounds prims K circuits settings)
    (checks : ContextualCheckBound prims K circuits settings events) :
    JointSimulationFromComponent prims K circuits settings := by
  intro _ hb D pre A Z q0 q preBudget advBudget
  by_cases small : q0 + q < 2 ^ 128
  · obtain ⟨parameter, seeds, pairs, valid, certificates⟩ :=
      stages hb D pre A Z q0 q preBudget advBudget small
    have coupling := trace_coupling prims K circuits settings (events pre) D pre A Z
      parameter seeds pairs valid certificates
    have distance := treeSim_badUnion (trace prims K circuits settings D pre A Z)
      (Prod.fst <$> runWorld prims (jointGame K circuits settings true D pre A Z))
      (fun r => (flags (events pre) D A Z r).1 = true)
      (fun r => (flags (events pre) D A Z r).2 = true)
      (fun r => r.1.2 = true) (fun b => b = true) coupling
    rw [trace_acceptance] at distance
    simp only [probEvent_map, Function.comp_def] at distance
    have hash : (Pr[fun r => (flags (events pre) D A Z r).1 = true |
        trace prims K circuits settings D pre A Z]).toReal ≤
        jointError prims pre (fun tree => treeHashError circuits settings C tree (q0 + q) - keySplit C (q0 + q)) := by
      simp only [flags, hashFlag, decide_eq_true_eq]
      apply (joint_hash_bound prims K circuits settings honest salts hb D pre A Z q0 q preBudget advBudget).trans
      apply jointError_mono
      intro tree
      simpa only [tailBudget, Nat.add_assoc, Nat.cast_pow] using
        treeSim_hashBudget (C := C) circuits settings tree (q0 + q)
    have check := checks hb D pre A Z q0 q preBudget advBudget small
    apply distance.trans ((add_le_add hash check).trans ?_)
    rw [← jointError_add]
    apply le_of_eq
    congr 1
    funext tree
    ring
  · have unit : ∀ {α : Type} (p : ProbComp α) (event : α → Prop),
        0 ≤ (Pr[event | p]).toReal ∧ (Pr[event | p]).toReal ≤ 1 := by
      intro α p event
      exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)⟩
    have left := unit (PRFScheme.prfIdealExp
      (prgReduction prims D (jointGame K circuits settings false D pre A Z))) (fun b => b = true)
    have right := unit (runWorld prims (jointGame K circuits settings true D pre A Z)) (fun r => r.1 = true)
    have distance : |reductionIdeal prims D (jointGame K circuits settings false D pre A Z) -
        accepts prims (jointGame K circuits settings true D pre A Z)| ≤ 1 := by
      simp only [reductionIdeal, accepts, probEvent_eq_eq_probOutput] at left right ⊢
      rw [abs_le]
      constructor <;> linarith
    apply distance.trans
    rw [← LifetimeJointHop.jointError_const prims pre 1]
    apply jointError_mono
    intro tree
    have hash := treeSim_largeHashBudget (C := C) circuits settings tree (q0 + q) (Nat.le_of_not_gt small)
    have check := checkError_nonneg K circuits settings tree (q0 + q)
    linarith

end Ceremony

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSimStages.clipped_logged_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clipped_logged_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSimStages.joint_hash_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_hash_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSimStages.ghost_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ghost_erase

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSimStages.idealCommon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealCommon_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSimStages.trace_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSimStages.jointSimulationFromComponent_of_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSimulationFromComponent_of_contextual

end ThresholdLeanXmssSecurity.LifetimeJointSimStages
