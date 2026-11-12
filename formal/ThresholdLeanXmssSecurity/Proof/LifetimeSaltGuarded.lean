import ThresholdLeanXmssSecurity.Proof.TreeSaltPairsFinal
import ThresholdLeanXmssSecurity.Proof.TreeSaltPairsProof
import ThresholdLeanXmssSecurity.Proof.LifetimeContextual
import ThresholdLeanXmssSecurity.Proof.TreeAssembly

/-!
# The guess-guarded salt route after a counted prefix

The pair event of `PairBoundsGuardedFrom` adds two guards to the event of
`TreeSaltPairsFinal.PairBoundsFrom`. The tables, the split and the paired program are the same.

* Outside `TreeSimSaltGuess`. Both unions already charge the guess as a separate term:
  `treeSimHash_union_guess` (`TreeSaltPairsProof.lean`) for the tree hop and
  `hash_union_clipped_guess` below for the joint hop. The guess is charged once.
* For the least reuse pair (`TreeSaltLeastPairReuse`), as in `treeSaltStages_reuse_le_least`.

Each guarded event is contained in the unguarded one, so every summand keeps its bound and the
errors do not change.

* The tree hop is the original `TreeSimulationHop … (keySplit C)` through
  `TreeAssembly.treeSimulationHop_of_guardedPairs`.
* The joint hop is the original `JointSimulationFromComponent`. `JointSaltBoundsGuarded` is
  `JointSaltBounds` with the reuse event outside the guess. The guess conjunct and both budgets are
  unchanged.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeSaltGuarded

open LifetimeBridge LifetimeJointSim LifetimeFreshBudget LifetimeJointSimStages LifetimeJointSalt
  LifetimeSaltFrom
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Tables

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `TreeSaltPairsFinal.PairBoundsFrom` on the same fixed tables and paired program, for the
least reuse pair outside the salt guess. -/
def PairBoundsGuardedFrom : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (prefixState prims D pre),
    ∀ p ∈ support (treeSaltSetupFrom prims D A x z s.2),
    ∀ i j : ℕ, i < j →
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ ¬ TreeSimSaltGuess D r.2.2 ∧
          TreeSaltLeastPairReuse D
            (Fin.append
              (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2))
              (TreeSaltPairsFinal.enumerate
                (TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A r.1))) i j r.2.2 |
        (TreeSaltPairsFinal.splits prims K circuits settings top tree D A x Z p).paired] ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹

/-- The guarded fixed-table bounds follow from the unguarded ones. -/
theorem pairBoundsGuardedFrom_of_pairBoundsFrom
    (bounds : TreeSaltPairsFinal.PairBoundsFrom prims K circuits settings) :
    PairBoundsGuardedFrom prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i j hij
  refine le_trans (probEvent_mono ?_) (bounds hb top tree D A x z Z q hx hq hsmall pre s hs p hp i j hij)
  rintro r - ⟨hnc, -, -, hr⟩
  exact ⟨hnc, hr⟩

end Tables

section Pairs

variable {prims : Primitives} {K : Constants C E} {circuits : Circuits} {settings : Settings}

/-- `TreeSaltStagesPairsFrom` with the pair event of `TreeSaltStagesPairsGuarded`. -/
def TreeSaltStagesPairsGuardedFrom (splits : TreeSaltStageSplits prims K circuits settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α), ∀ s ∈ support (prefixState prims D pre),
    ∀ p ∈ support (treeSaltSetupFrom prims D A x z s.2),
    ∃ (n₁ : ℕ) (addr₁ : Fin n₁ → C.Term × HashOutput × ℕ)
      (n₂ : (splits top tree D A x Z p).View → ℕ)
      (addr₂ : (m : (splits top tree D A x Z p).View) → Fin (n₂ m) → C.Term × HashOutput × ℕ),
      TreeSaltStagesCover (splits top tree D A x Z p) (treeBatches settings tree * termCount C)
        n₁ addr₁ n₂ addr₂ ∧
      ∀ i j : ℕ, i < j →
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ ¬ TreeSimSaltGuess D r.2.2 ∧
            TreeSaltLeastPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2 |
          (splits top tree D A x Z p).paired] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

/-- The guarded certificate follows from the unguarded one on the same split. -/
theorem pairsGuardedFrom_of_pairsFrom (splits : TreeSaltStageSplits prims K circuits settings)
    (pairs : TreeSaltStagesPairsFrom splits) : TreeSaltStagesPairsGuardedFrom splits := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp
  obtain ⟨n₁, addr₁, n₂, addr₂, hcover, hpair⟩ := pairs hb top tree D A x z Z q hx hq hsmall pre s hs p hp
  refine ⟨n₁, addr₁, n₂, addr₂, hcover, fun i j hij => le_trans (probEvent_mono ?_) (hpair i j hij)⟩
  rintro r - ⟨hnc, -, -, hr⟩
  exact ⟨hnc, hr⟩

-- Copy of `LifetimeSaltFrom.pairs_of_from` (`LifetimeSaltFrom.lean`) for the guarded event.
/-- The empty prefix gives the guarded certificate of `TreeSaltPairsProof`. -/
theorem pairsGuarded_of_from (splits : TreeSaltStageSplits prims K circuits settings)
    (h : TreeSaltStagesPairsGuardedFrom splits) : TreeSaltStagesPairsGuarded splits := by
  intro hb top tree D A x z Z q hx hq hs p hp
  exact h hb top tree D A x z Z q hx hq hs (pure ()) (((), ((∅, ∅), [])))
    (by change _ ∈ support (pure _ : ProbComp _); simp) p (by simpa [treeSaltSetupFrom_empty] using hp)

end Pairs

-- Copy of `TreeSaltPairsFinal.pairs_from_of_bounds` (`TreeSaltPairsFinal.lean`); the tables and
-- `cover_from` are the same.
/-- The fixed tables of `TreeSaltPairsFinal.cover_from` give the guarded certificate. -/
theorem pairsGuarded_from_of_bounds (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (bounds : PairBoundsGuardedFrom prims K circuits settings) :
    TreeSaltStagesPairsGuardedFrom (TreeSaltPairsFinal.splits prims K circuits settings) := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp
  refine ⟨(TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card,
    TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2),
    (fun m => (TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A m).card),
    (fun m => TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A m)),
    TreeSaltPairsFinal.cover_from prims K circuits settings top tree D A x z Z hx pre s hs p hp, ?_⟩
  exact bounds hb top tree D A x z Z q hx hq hsmall pre s hs p hp

/-- The empty-prefix guarded certificate on the fixed split. -/
theorem pairsGuarded_of_bounds (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (bounds : PairBoundsGuardedFrom prims K circuits settings) :
    TreeSaltStagesPairsGuarded (TreeSaltPairsFinal.splits prims K circuits settings) :=
  pairsGuarded_of_from _ (pairsGuarded_from_of_bounds prims K circuits settings bounds)

/-- The original tree hop at `keySplit C` from the guarded fixed-table bounds. -/
theorem treeSimulationHop_of_pairBoundsGuarded (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (linked : TreeTwinLinkedGoal prims K circuits settings)
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings)
    (normalization : TreeRawSaltRepresentationProof.CeremonyOpaqueNormalization
      prims K circuits settings)
    (bounds : PairBoundsGuardedFrom prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  TreeAssembly.treeSimulationHop_of_guardedPairs prims K circuits settings linked sources
    normalization (TreeSaltPairsFinal.splits prims K circuits settings)
    (pairsGuarded_of_bounds prims K circuits settings bounds)

-- Copy of `LifetimeSaltFrom.reuse_from` (`LifetimeSaltFrom.lean`) with the guarded event and
-- `treeSaltStages_reuse_le_least` (`TreeSaltPairsProof.lean`).
/-- Guarded pair certificates after a prefix bound the guarded full-log reuse event. -/
theorem reuse_from_guarded (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (splits : TreeSaltStageSplits prims K circuits settings)
    (pairs : TreeSaltStagesPairsGuardedFrom splits) (hb : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hx : DealtInputs D x)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (hsmall : q < 2 ^ 128)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre)) :
    (Pr[fun r => ¬TreeSimHashBudgetCollision r.2.2 ∧ ¬TreeSimSaltGuess D r.2.2 ∧
        TreeSimSaltReuse D r.2.2 |
      (simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run s.2]).toReal ≤
      saltReuseBudget (C := C) settings tree := by
  have hle : Pr[fun r => ¬TreeSimHashBudgetCollision r.2 ∧ ¬TreeSimSaltGuess D r.2 ∧
      TreeSimSaltReuse D r.2 |
      (fun r => (r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run s.2] ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
    rw [treeSaltSetupFrom_split]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨n₁, addr₁, n₂, addr₂, hcover, hpair⟩ := pairs hb top tree D A x z Z q hx hq hsmall pre s hs p hp
    exact treeSaltStages_reuse_le_least (splits top tree D A x Z p) D hcover hpair
  rw [probEvent_map] at hle
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp [saltReuseBudget, ENNReal.toReal_div]

section Joint

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `JointSaltBounds` with the reuse event outside the salt guess. The guess conjunct and both
budgets are the same. -/
def JointSaltBoundsGuarded : Prop :=
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
        ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧ TreeSimSaltReuse D r.2 |
      trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre (fun tree => if tailBudget (C := C) circuits settings q tree < 2 ^ 128
        then saltReuseBudget (C := C) settings tree else 0)

/-- The guarded joint bounds follow from the unguarded ones. -/
theorem jointSaltBoundsGuarded_of_jointSaltBounds
    (salts : JointSaltBounds prims K circuits settings) :
    JointSaltBoundsGuarded prims K circuits settings := by
  intro hb D pre A Z q0 q hpre hadv
  obtain ⟨guess, reuse⟩ := salts hb D pre A Z q0 q hpre hadv
  refine ⟨guess, le_trans (ENNReal.toReal_mono probEvent_ne_top (probEvent_mono ?_)) reuse⟩
  rintro r - ⟨hs, hnc, -, hr⟩
  exact ⟨hs, hnc, hr⟩

-- Copy of `LifetimeSaltFrom.jointSaltBounds_of_from` (`LifetimeSaltFrom.lean`) with
-- `reuse_from_guarded` and the guarded reuse event.
/-- Start-state compiler and guarded pair certificates imply the guarded joint salt bounds. -/
theorem jointSaltBoundsGuarded_of_from
    (tables : StartTableBound (C := C) prims) (prefixes : PrefixSaltState (C := C) prims)
    (certificates : CeremonyCompilerCertificatesFrom prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairs : TreeSaltStagesPairsGuardedFrom splits) :
    JointSaltBoundsGuarded prims K circuits settings := by
  intro hb D pre A Z q0 q hpre hadv
  have bounds (p : JointInput C × TreeSimState C) (hp : p ∈ support (loggedPrefix prims D pre))
      (small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128) :
      (Pr[fun r => ¬TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 |
        continuation prims K circuits settings D A Z p]).toReal ≤
          saltGuessBudget (C := C) settings (q0 + q) p.1.2.2.1 ∧
      (Pr[fun r => ¬TreeSimHashBudgetCollision r.2 ∧ ¬TreeSimSaltGuess D r.2 ∧
          TreeSimSaltReuse D r.2 |
        continuation prims K circuits settings D A Z p]).toReal ≤
          saltReuseBudget (C := C) settings p.1.2.2.1 := by
    have hx := loggedPrefix_dealt prims D pre p hp
    have hs : p ∈ support (prefixState prims D (jointPrefix pre)) := hp
    obtain ⟨covered, length⟩ := prefixes D (jointPrefix pre) q0 hpre p hs
    have hq : q < 2 ^ 128 := lt_of_le_of_lt (Nat.le_add_right q _) small
    have hempty := loggedPrefix_private_empty prims D pre p hp
    have hstate : ((p.2.1.1, ∅), p.2.2) = p.2 := by
      rw [← hempty]
    have guess := guess_from prims K circuits settings tables certificates hb
      p.1.2.1 p.1.2.2.1 D A p.1.1 p.1.2.2.2 Z q0 q hx hadv hq
      (jointPrefix pre) p hs covered length
    rw [hstate] at guess
    have reuse := reuse_from_guarded prims K circuits settings splits pairs hb
      p.1.2.1 p.1.2.2.1 D A p.1.1 p.1.2.2.2 Z q hx hadv hq (jointPrefix pre) p hs
    simpa only [continuation, selectedGame, Bool.false_eq_true, if_false,
      probEvent_map, Function.comp_def] using And.intro guess reuse
  constructor
  · apply trace_event_le prims K circuits settings D pre A Z
      (fun input r => tailBudget (C := C) circuits settings q input.2.2.1 < 2 ^ 128 ∧
        ¬TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
    intro p hp
    by_cases small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128
    · simpa only [small, true_and, if_pos] using (bounds p hp small).1
    · simp only [small, false_and, if_false]
      rw [probEvent_False]
      exact le_refl 0
  · apply trace_event_le prims K circuits settings D pre A Z
      (fun input r => tailBudget (C := C) circuits settings q input.2.2.1 < 2 ^ 128 ∧
        ¬TreeSimHashBudgetCollision r.2 ∧ ¬TreeSimSaltGuess D r.2 ∧ TreeSimSaltReuse D r.2)
    intro p hp
    by_cases small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128
    · simpa only [small, true_and, if_pos] using (bounds p hp small).2
    · simp only [small, false_and, if_false]
      rw [probEvent_False]
      exact le_refl 0

/-- The guarded joint salt bounds from the guarded pair certificate alone. -/
theorem jointSaltBoundsGuarded_of_pairs
    (splits : TreeSaltStageSplits prims K circuits settings)
    (pairs : TreeSaltStagesPairsGuardedFrom splits) :
    JointSaltBoundsGuarded prims K circuits settings :=
  jointSaltBoundsGuarded_of_from prims K circuits settings (startTableBound prims)
    (prefixSaltState prims)
    (TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom prims K circuits settings)
    splits pairs

/-- The guarded joint salt bounds from the guarded fixed-table bounds alone. -/
theorem jointSaltBoundsGuarded_of_bounds
    (bounds : PairBoundsGuardedFrom prims K circuits settings) :
    JointSaltBoundsGuarded prims K circuits settings :=
  jointSaltBoundsGuarded_of_pairs prims K circuits settings
    (TreeSaltPairsFinal.splits prims K circuits settings)
    (pairsGuarded_from_of_bounds prims K circuits settings bounds)

end Joint

-- Copy of `LifetimeJointSimStages.hash_union_clipped` (`LifetimeJointSimStages.lean`). Under
-- `small` and outside the budget collision, the guess is split off first, as in
-- `treeSimHash_union_guess` (`TreeSaltPairsProof.lean`).
/-- The clipped union with the reuse term outside the salt guess. The first two terms are the
same as in `hash_union_clipped`. -/
theorem hash_union_clipped_guess {α : Type} (D : C.Coalition) (p : ProbComp (α × TreeSimLog C))
    (small : α → Prop) :
    (Pr[fun r => TreeSimHashBad3 D r.2 | p]).toReal ≤
      (Pr[fun r => ¬ small r.1 ∨ TreeSimHashBudgetCollision r.2 | p]).toReal +
      (Pr[fun r => small r.1 ∧ ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal +
      (Pr[fun r => small r.1 ∧ ¬ TreeSimHashBudgetCollision r.2 ∧ ¬ TreeSimSaltGuess D r.2 ∧
        TreeSimSaltReuse D r.2 | p]).toReal := by
  let B := fun r : α × TreeSimLog C => ¬ small r.1 ∨ TreeSimHashBudgetCollision r.2
  let G := fun r : α × TreeSimLog C => small r.1 ∧ ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2
  let U := fun r : α × TreeSimLog C => small r.1 ∧ ¬ TreeSimHashBudgetCollision r.2 ∧
    ¬ TreeSimSaltGuess D r.2 ∧ TreeSimSaltReuse D r.2
  have event : Pr[fun r => TreeSimHashBad3 D r.2 | p] ≤ Pr[fun r => (B r ∨ G r) ∨ U r | p] := by
    apply probEvent_mono
    intro r _ bad
    by_cases hs : small r.1
    · by_cases hc : TreeSimHashBudgetCollision r.2
      · exact Or.inl (Or.inl (Or.inr hc))
      have hnc : ¬ TreeSimHashCollision r.2 := fun h =>
        hc (treeSimHashBudgetCollision_of_collision _ h)
      by_cases hg : TreeSimSaltGuess D r.2
      · exact Or.inl (Or.inr ⟨hs, hnc, hg⟩)
      rcases (treeSimHashBad3_iff D r.2).mp bad with collision | guess | reuse
      · exact (hc collision).elim
      · exact (hg guess).elim
      · exact Or.inr ⟨hs, hc, hg, reuse⟩
    · exact Or.inl (Or.inl (Or.inl hs))
  have sumBound := event.trans ((probEvent_or_le p (fun r => B r ∨ G r) U).trans
    (add_le_add (probEvent_or_le p B G) le_rfl))
  have finite : (Pr[B | p] + Pr[G | p] + Pr[U | p]) ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩, probEvent_ne_top⟩
  have h := ENNReal.toReal_mono finite sumBound
  simpa only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) probEvent_ne_top,
    ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] using h

section Ceremony

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

-- Copy of `LifetimeJointSimStages.joint_hash_bound` (`LifetimeJointSimStages.lean`) with
-- `hash_union_clipped_guess`; the collision bound and `clipped_hash_arith` are unchanged.
/-- The complete joint hash event fits the same fixed squared allowance from the guarded salt
bounds. -/
theorem joint_hash_bound_guarded
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salts : JointSaltBoundsGuarded prims K circuits settings)
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
  have bound := (hash_union_clipped_guess D (trace prims K circuits settings D pre A Z)
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

-- Copy of `LifetimeJointSimStages.jointSimulationFromComponent_of_contextual`
-- (`LifetimeJointSimStages.lean`); only the hash step uses `joint_hash_bound_guarded`.
/-- The joint simulation bridge with contextual round and check certificates and the guarded
salt bounds. The error and the one complete-run reduction are unchanged. -/
theorem jointSimulationFromComponent_of_contextual_guarded
    (events : Selector C → TreeSimEvents C E)
    (hashFlag : ∀ pre top tree D A x z Z log,
      (events pre top tree D A x z Z log).1 = decide (TreeSimHashBad3 D log))
    (stages : ContextualStages prims K circuits settings events)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salts : JointSaltBoundsGuarded prims K circuits settings)
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
      apply (joint_hash_bound_guarded prims K circuits settings honest salts hb D pre A Z q0 q
        preBudget advBudget).trans
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

/-- `LifetimeContextual.jointSimulationFromComponent_of_linked_indexed` with the guarded salt
bounds. -/
theorem jointSimulationFromComponent_of_linked_indexed_guarded
    (linked : TreeTwinLinkedGoal prims K circuits settings)
    (checks : LifetimeContextual.IndexedCheckBounds prims K circuits settings)
    (salts : JointSaltBoundsGuarded prims K circuits settings) :
    JointSimulationFromComponent prims K circuits settings :=
  jointSimulationFromComponent_of_contextual_guarded prims K circuits settings
    (LifetimeContextual.events prims K circuits settings)
    (LifetimeContextual.hashFlag prims K circuits settings)
    (LifetimeContextual.contextualStages_of_linked prims K circuits settings linked)
    (treeSimHashHonestBudget K prims circuits settings) salts
    (LifetimeContextual.contextualCheckBound_of_indexed prims K circuits settings checks)

/-- The original joint simulation bound from the guarded fixed-table bounds. -/
theorem jointSimulationFromComponent_of_pairBoundsGuarded
    (linked : TreeTwinLinkedGoal prims K circuits settings)
    (checks : LifetimeContextual.IndexedCheckBounds prims K circuits settings)
    (bounds : PairBoundsGuardedFrom prims K circuits settings) :
    JointSimulationFromComponent prims K circuits settings :=
  jointSimulationFromComponent_of_linked_indexed_guarded prims K circuits settings linked checks
    (jointSaltBoundsGuarded_of_bounds prims K circuits settings bounds)

end Ceremony

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.pairBoundsGuardedFrom_of_pairBoundsFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairBoundsGuardedFrom_of_pairBoundsFrom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.pairsGuardedFrom_of_pairsFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairsGuardedFrom_of_pairsFrom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.pairsGuarded_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairsGuarded_of_from

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.pairsGuarded_from_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairsGuarded_from_of_bounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.pairsGuarded_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairsGuarded_of_bounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.treeSimulationHop_of_pairBoundsGuarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_pairBoundsGuarded

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.reuse_from_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reuse_from_guarded

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSaltBoundsGuarded_of_jointSaltBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSaltBoundsGuarded_of_jointSaltBounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSaltBoundsGuarded_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSaltBoundsGuarded_of_from

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSaltBoundsGuarded_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSaltBoundsGuarded_of_pairs

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSaltBoundsGuarded_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSaltBoundsGuarded_of_bounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.hash_union_clipped_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hash_union_clipped_guess

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.joint_hash_bound_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_hash_bound_guarded

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSimulationFromComponent_of_contextual_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSimulationFromComponent_of_contextual_guarded

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSimulationFromComponent_of_linked_indexed_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSimulationFromComponent_of_linked_indexed_guarded

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltGuarded.jointSimulationFromComponent_of_pairBoundsGuarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSimulationFromComponent_of_pairBoundsGuarded

end ThresholdLeanXmssSecurity.LifetimeSaltGuarded
