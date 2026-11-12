import ThresholdLeanXmssSecurity.Proof.LifetimeJointSimStages
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltRepresentation
import ThresholdLeanXmssSecurity.Proof.TreeCheckGuess

/-!
# Salt boundaries after adaptive selection

The selector executes before the ceremony's hidden salt draws. Its counted
queries, selected metadata and complete cache are retained by a boundary
compiler for the joint experiment. The compiler preserves query order and
abort behavior and never exposes a digest's raw salt through its response.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeJointSalt

open LifetimeBridge LifetimeJointSim LifetimeJointSimStages
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

local instance : DecidableEq (JointInput C × HashCache C) := Classical.decEq _
local instance : DecidableEq (JointInput C × TreeSimState C) := Classical.decEq _

theorem prefix_noSalt (D : C.Coalition) (t : (LocalSpec C).Domain) :
    NoSaltRead D (.inl (.inl t)) := trivial

/-- Each selector request remains an ordinary counted request. -/
def prefixQuery (D : C.Coalition) :
    QueryImpl (LocalSpec C) (OracleComp (BoundarySpec D)) := fun t =>
  liftM (OracleSpec.query (spec := BoundarySpec D) (.inr ⟨.inl (.inl t), prefix_noSalt D t⟩))

set_option backward.isDefEq.respectTransparency false in
/-- The boundary prefix has the exact original counted-world source. -/
theorem prefix_source (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (boundarySource (E := E) D) (simulateQ (prefixQuery D) p) =
      worldRoles.adversary p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, worldRoles_adversary_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, prefixQuery, boundarySource, ih,
      adversary_bind, adversary_query]

set_option backward.isDefEq.respectTransparency false in
/-- No selector branch can issue a simulator programming request. -/
theorem prefix_safe (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (simulateQ (prefixQuery D) p) (BoundaryProgramCall D) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    apply isQueryBoundP_bind (n := 0) (m := 0) _ (fun a _ => ih a)
    simp [prefixQuery, isQueryBoundP_query_iff, BoundaryProgramCall, AimedProgramCall]

/-- One fixed boundary program carries the selected input and real result. -/
def boundary (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) : OracleComp (BoundarySpec D) (JointInput C × Bool) := do
  let input ← simulateQ (prefixQuery D) (jointPrefix pre)
  (fun b => (input, b)) <$> ceremonyBoundary K circuits settings input.2.1 input.2.2.1 D A input.1 input.2.2.2 Z

/-- The entire adaptive experiment is the expansion of that same boundary. -/
theorem boundary_source (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) :
    simulateQ (boundarySource (E := E) D) (boundary K circuits settings D pre A Z) =
      taggedGame K circuits settings false D pre A Z := by
  unfold boundary taggedGame
  simp only [simulateQ_bind, prefix_source, simulateQ_map, ceremonyBoundary_source]
  rfl

theorem boundary_safe (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (boundary K circuits settings D pre A Z) (BoundaryProgramCall D) 0 := by
  unfold boundary
  apply isQueryBoundP_bind (n := 0) (m := 0) (prefix_safe D _) 
  intro input _
  rw [isQueryBoundP_map_iff]
  exact ceremonyBoundary_safe K circuits settings _ _ _ _ _ _ _

/-- The joint boundary retains both caches, the complete transcript and
selected metadata under the split-cache interpreter. -/
theorem boundary_run (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (taggedGame K circuits settings false D pre A Z)).run ((∅, ∅), [])] =
    𝒟[(fun r => (r.1, decodeState r.2)) <$>
      (simulateQ (boundarySplit prims D) (boundary K circuits settings D pre A Z)).run (((∅, ∅), []), ∅)] := by
  rw [← boundary_source K circuits settings D pre A Z]
  simpa only [decodeState_empty] using boundary_program_joint (E := E) prims D
    (boundary K circuits settings D pre A Z) (((∅, ∅), []), ∅)

/-- A selector cannot create any honest log entry, including a hidden salt bit. -/
theorem loggedPrefix_no_free (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (p : JointInput C × TreeSimState C) (hp : p ∈ support (loggedPrefix prims D pre)) :
    ∀ (t : (LocalSpec C).Domain) (v : (LocalSpec C).Range t),
      (⟨.inr t, v⟩ : (u : (WorldSpec C).Domain) × (WorldSpec C).Range u) ∉ p.2.2 := by
  apply logged_adversary_inv prims D
    (fun s => ∀ t v, (⟨.inr t, v⟩ : (u : (WorldSpec C).Domain) × (WorldSpec C).Range u) ∉ s.2)
    ?_ (jointPrefix pre) ((∅, ∅), []) (by simp) p hp
  intro t s hs r hr u v hv
  rw [logged_step_log prims D _ s r hr,
    List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hv
  · exact hs u v hv
  · cases hv

/-- The selected input is sampled before any private salt cache cell is drawn. -/
theorem loggedPrefix_private_empty (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (p : JointInput C × TreeSimState C) (hp : p ∈ support (loggedPrefix prims D pre)) :
    p.2.1.2 = ∅ :=
  treeSim_local_private prims D (jointPrefix pre) ∅ ∅ [] p hp

theorem loggedPrefix_no_hiddenSalt (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (p : JointInput C × TreeSimState C) (hp : p ∈ support (loggedPrefix prims D pre))
    (salt : List Bit) : ¬ TreeSimHiddenSalt D p.2.2 salt := by
  rintro ⟨_, T, key, label, _, bits⟩
  exact loggedPrefix_no_free prims D pre p hp _ _ (bits ⟨0, by norm_num⟩)

/-- The boundary law also retains the exact log observed by the two salt events. -/
theorem boundary_trace (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) :
    𝒟[trace prims K circuits settings D pre A Z] =
      𝒟[(fun r => (r.1, (decodeState r.2).2)) <$>
        (simulateQ (boundarySplit prims D) (boundary K circuits settings D pre A Z)).run (((∅, ∅), []), ∅)] := by
  have law := evalDist_map_eq_of_evalDist_eq
    (boundary_run prims K circuits settings D pre A Z) (fun r => (r.1, r.2.2))
  simpa only [trace, treeSimLoggedRun_eq_run, Functor.map_map, Function.comp_def] using law

/-- Finite-support expectation is unchanged by mapping its complete source. -/
theorem sum_map_probability {α β : Type} [DecidableEq α] [DecidableEq β] (draw : ProbComp α) (f : α → β) (cost : β → ℝ) :
    ∑ b ∈ finSupport (f <$> draw), (Pr[= b | f <$> draw]).toReal * cost b =
      ∑ a ∈ finSupport draw, (Pr[= a | draw]).toReal * cost (f a) := by
  classical
  have prob (b : β) : (Pr[= b | f <$> draw]).toReal =
      ∑ a ∈ finSupport draw, if b = f a then (Pr[= a | draw]).toReal else 0 := by
    rw [probOutput_map_eq_sum_finSupport_ite, ENNReal.toReal_sum]
    · simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    · intro a _
      split_ifs <;> simp [probOutput_ne_top]
  simp_rw [prob, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp [hba]
  · intro absent
    exact (absent (by rw [finSupport_map]; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩)).elim

/-- The full logged-prefix expectation is exactly the public-prefix error
expression, with the cache and selection still jointly distributed. -/
theorem jointError_logged (prims : Primitives) (D : C.Coalition) (pre : Selector C) (e : Tree → ℝ) :
    jointError prims pre e = ∑ p ∈ finSupport (loggedPrefix prims D pre),
      (Pr[= p | loggedPrefix prims D pre]).toReal * e p.1.2.2.1 := by
  classical
  unfold jointError
  rw [← loggedPrefix_marginal prims D pre]
  simpa only [selectedError] using sum_map_probability (loggedPrefix prims D pre)
    (fun p : JointInput C × TreeSimState C => (p.1, p.2.1.1))
    (fun p : JointInput C × HashCache C => e p.1.2.2.1)

/-- The actual continuation retains the prefix's complete transcript. -/
def continuation (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (p : JointInput C × TreeSimState C) :
    ProbComp (Bool × TreeSimLog C) :=
  (fun r => (r.1, r.2.2)) <$>
    (simulateQ (treeSimLoggedWorld prims D)
      (selectedGame K circuits settings false D A Z p.1)).run p.2

set_option linter.constructorNameAsVariable false in
/-- Conditional estimates are averaged over the actual retained prefix;
no fresh independent prefix is introduced. -/
theorem trace_event_le (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput)
    (event : JointInput C → Bool × TreeSimLog C → Prop) (e : Tree → ℝ)
    (bound : ∀ p ∈ support (loggedPrefix prims D pre),
      (Pr[event p.1 | continuation prims K circuits settings D A Z p]).toReal ≤ e p.1.2.2.1) :
    (Pr[fun r => event r.1.1 (r.1.2, r.2) | trace prims K circuits settings D pre A Z]).toReal ≤
      jointError prims pre e := by
  classical
  rw [trace_split, prob_bind_eq_sum, jointError_logged prims D pre]
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have reached : p ∈ support (loggedPrefix prims D pre) := by
    rwa [mem_finSupport_iff_mem_support] at hp
  have h := bound p reached
  simp only [continuation, probEvent_map, Function.comp_def] at h ⊢
  exact h

/-- The fixed ceremony boundary starts from the selector's actual state. -/
def continuationBoundary (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (p : JointInput C × TreeSimState C) :
    ProbComp (Bool × TreeSimLog C) :=
  (fun r => (r.1, (decodeState r.2).2)) <$>
    (simulateQ (boundarySplit prims D)
      (ceremonyBoundary K circuits settings p.1.2.1 p.1.2.2.1 D A p.1.1 p.1.2.2.2 Z)).run (p.2, ∅)

/-- The sampled selector state supplies the empty hidden cache needed by
this boundary; the public cache and all prefix entries remain in place. -/
theorem continuation_boundary (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (pre : Selector C) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (p : JointInput C × TreeSimState C)
    (hp : p ∈ support (loggedPrefix prims D pre)) :
    𝒟[continuation prims K circuits settings D A Z p] =
      𝒟[continuationBoundary prims K circuits settings D A Z p] := by
  have empty := loggedPrefix_private_empty prims D pre p hp
  have state : decodeState (p.2, (∅ : BlockCache C)) = p.2 := by
    rcases p with ⟨input, ⟨cache, hidden⟩, log⟩
    dsimp at empty ⊢
    subst hidden
    change ((cache, restore ∅ ∅), log) = ((cache, ∅), log)
    congr 2
    funext x
    cases h : saltAt x <;> simp [restore, h]
  have law := boundary_program_joint (E := E) prims D
    (ceremonyBoundary K circuits settings p.1.2.1 p.1.2.2.1 D A p.1.1 p.1.2.2.2 Z) (p.2, ∅)
  rw [state, ceremonyBoundary_source] at law
  have logged := evalDist_map_eq_of_evalDist_eq law (fun r => (r.1, r.2.2))
  simpa only [continuation, continuationBoundary, selectedGame, Functor.map_map,
    Function.comp_def, Bool.false_eq_true, if_false] using logged

/-- Executable salt normalization and an ordered two-stage address table
for one common continuation law. The table bounds are per distinct pair;
the raw decoder transports the guarded guess on that same retained log. -/
structure SaltData (prims : Primitives) (D : C.Coalition)
    (run : ProbComp (Bool × TreeSimLog C)) (H N q : ℕ) where
  Raw : Type
  program : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) Raw
  decode : TreeRawSaltOutcome C H Raw → Bool × TreeSimLog C
  privateBound : IsQueryBoundP program TreeSimHashSaltPrivate H
  charged : IsQueryBoundP program treeSimHashSaltTableCharged (q + H)
  law : 𝒟[run] = 𝒟[decode <$> treeRawSaltRun prims H program]
  guess : ∀ r ∈ support (treeRawSaltRun prims H program),
    ¬ TreeSimHashCollision (decode r).2 → TreeSimSaltGuess D (decode r).2 → TreeRawSaltHit r
  split : TreeSaltStageSplit run
  firstSize : ℕ
  first : Fin firstSize → C.Term × HashOutput × ℕ
  secondSize : split.View → ℕ
  second : (v : split.View) → Fin (secondSize v) → C.Term × HashOutput × ℕ
  cover : TreeSaltStagesCover split N firstSize first secondSize second
  pairs : ∀ i j : ℕ, i < j →
    Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧
      TreeSaltPairReuse D (Fin.append first (second r.1)) i j r.2.2 | split.paired] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹

/-- Quantitative salt estimates from the semantic data, without any
assumption about the probability of the full guess or reuse events. -/
theorem SaltData.bounds {prims : Primitives} {D : C.Coalition}
    {run : ProbComp (Bool × TreeSimLog C)} {H N q : ℕ}
    (data : SaltData prims D run H N q) (positive : 0 < H) :
    (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | run]).toReal ≤
      2 * (H : ℝ) * ((q + H : ℕ) : ℝ) / 2 ^ 256 ∧
    (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | run]).toReal ≤
      (N : ℝ) ^ 2 / 2 ^ 257 := by
  constructor
  · have law := OracleComp.probEvent_congr'
      (p := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
      (q := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
      (fun _ _ => Iff.rfl) data.law
    rw [law, probEvent_map]
    refine (ENNReal.toReal_mono probEvent_ne_top (probEvent_mono ?_)).trans
      (treeRawSalt_run_bound prims H q positive data.program data.charged)
    intro r hr h
    exact data.guess r hr h.1 h.2
  · have bound := treeSaltStages_reuse_le data.split D data.cover data.pairs
    have real := ENNReal.toReal_mono
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) bound
    simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, Nat.cast_pow] using real

/-- Salt normalization is required only after an actually reached selector
state and for a small selected tail. Counts include the original prefix.
The unguarded pair clause is essential: no additional no-guess guard is
inserted into the original reuse target. -/
def ContinuationSaltNormalization (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (q0 q : ℕ), IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    ∀ p ∈ support (loggedPrefix prims D pre),
      tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128 →
      Nonempty (SaltData prims D (continuationBoundary prims K circuits settings D A Z p)
        (treeBatches settings p.1.2.2.1 * (C.t * termCount C))
        (treeBatches settings p.1.2.2.1 * termCount C) (q0 + q))

/-- The fixed boundary normalization supplies the exact original pair of
joint salt bounds, averaged with the selected input and cache together. -/
theorem jointSaltBounds_of_normalization (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (normalization : ContinuationSaltNormalization prims K circuits settings) :
    JointSaltBounds prims K circuits settings := by
  intro hb D pre A Z q0 q hpre hadv
  have bounds (p : JointInput C × TreeSimState C)
      (hp : p ∈ support (loggedPrefix prims D pre))
      (small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128) :
      (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 |
        continuation prims K circuits settings D A Z p]).toReal ≤
          saltGuessBudget (C := C) settings (q0 + q) p.1.2.2.1 ∧
      (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
        continuation prims K circuits settings D A Z p]).toReal ≤
          saltReuseBudget (C := C) settings p.1.2.2.1 := by
    obtain ⟨data⟩ := normalization hb D pre A Z q0 q hpre hadv p hp small
    have result := data.bounds (treeRawSalt_capacity_pos settings hb _)
    have law := continuation_boundary prims K circuits settings D pre A Z p hp
    have guess := OracleComp.probEvent_congr'
      (p := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
      (q := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
      (fun _ _ => Iff.rfl) law
    have reuse := OracleComp.probEvent_congr'
      (p := fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2)
      (q := fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2)
      (fun _ _ => Iff.rfl) law
    rw [guess, reuse]
    simpa only [saltGuessBudget, saltReuseBudget, Nat.cast_mul, Nat.cast_add] using result
  constructor
  · apply trace_event_le prims K circuits settings D pre A Z
      (fun input r => tailBudget (C := C) circuits settings q input.2.2.1 < 2 ^ 128 ∧
        ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
    intro p hp
    by_cases small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128
    · simpa only [small, true_and, if_pos] using (bounds p hp small).1
    · simp only [small, false_and, if_false]
      rw [probEvent_False]
      exact le_refl 0
  · apply trace_event_le prims K circuits settings D pre A Z
      (fun input r => tailBudget (C := C) circuits settings q input.2.2.1 < 2 ^ 128 ∧
        ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2)
    intro p hp
    by_cases small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128
    · simpa only [small, true_and, if_pos] using (bounds p hp small).2
    · simp only [small, false_and, if_false]
      rw [probEvent_False]
      exact le_refl 0

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.boundary_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_run

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.loggedPrefix_no_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loggedPrefix_no_free

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.loggedPrefix_private_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loggedPrefix_private_empty

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.boundary_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_trace

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.sum_map_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_map_probability

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.jointError_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointError_logged

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.trace_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_event_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.continuation_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuation_boundary

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.SaltData.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SaltData.bounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointSalt.jointSaltBounds_of_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointSaltBounds_of_normalization

end ThresholdLeanXmssSecurity.LifetimeJointSalt
