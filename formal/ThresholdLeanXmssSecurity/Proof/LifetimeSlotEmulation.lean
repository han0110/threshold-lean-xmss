import ThresholdLeanXmssSecurity.Proof.LifetimeSlots

/-!
# Query counts of the dealer computations

Counts of the calls of `H` and `PRG` on every path (all answers), for the leanVM tree routines and
the clear evaluation of jobs. They bound a deterministic precomputation of `F_tree` tables, such as
the selector of `LifetimeSlots.slotInstance`.

* `QB oa n`: every path of `oa` makes at most `n` queries. It is irreducible, so a bound on a
  program with a numeral loop count does not unfold the program.
* leanVM routines: `tweakableHash_bound` (1), `merkleNode_bound` (`2 ^ (level + 1) - 1`),
  `grind_bound` (the attempt count), `chainWalk_bound` (the steps), `treeFold_bound` (the levels)
  and `layerRoot_bound` (`1 + (numChains * chainLength + 1 + layerHeight)`).
* Job points: `topJobs_points`, `bottomJobs_points` and `signJobs_points`.
* Clear evaluation: `tweakable_bound` keeps a count, `prfValue_bound` costs `C.terms.length` and
  `jobs_bound` costs the job points times `C.terms.length`.

The pinned and current leanVM proof directories have no per-routine query counts; the module uses
`isQueryBoundP_bind` and `isQueryBoundP_query_bind_iff` of VCVio.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeSlotEmulation

open LifetimeSlots LifetimeJointLink

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## Counting all queries -/

section Count

variable {ι : Type} {spec : OracleSpec ι}

/-- At most `n` queries on every path. -/
@[irreducible] def QB {α : Type} (oa : OracleComp spec α) (n : ℕ) : Prop :=
  IsQueryBoundP oa (fun _ => True) n

theorem qb_iff {α : Type} (oa : OracleComp spec α) (n : ℕ) :
    QB oa n ↔ IsQueryBoundP oa (fun _ => True) n := by unfold QB; rfl

theorem QB.mono {α : Type} {oa : OracleComp spec α} {n m : ℕ} (h : QB oa n) (hnm : n ≤ m) :
    QB oa m := (qb_iff _ _).2 (IsQueryBoundP.mono ((qb_iff _ _).1 h) hnm)

theorem QB.bind {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n m : ℕ}
    (h : QB oa n) (h' : ∀ x, QB (ob x) m) : QB (oa >>= ob) (n + m) :=
  (qb_iff _ _).2 (isQueryBoundP_bind ((qb_iff _ _).1 h) fun x _ => (qb_iff _ _).1 (h' x))

theorem QB.pure {α : Type} (a : α) (n : ℕ) : QB (pure a : OracleComp spec α) n :=
  (qb_iff _ _).2 (isQueryBoundP_pure _ _ _)

theorem QB.map {α β : Type} {oa : OracleComp spec α} {n : ℕ} (f : α → β) (h : QB oa n) :
    QB (f <$> oa) n := (qb_iff _ _).2 ((isQueryBoundP_map_iff oa f n).2 ((qb_iff _ _).1 h))

theorem QB.query (t : spec.Domain) : QB (liftM (OracleSpec.query t) : OracleComp spec _) 1 := by
  rw [show (liftM (OracleSpec.query t) : OracleComp spec _) =
    (liftM (OracleSpec.query t) >>= Pure.pure : OracleComp spec _) by rw [bind_pure]]
  rw [qb_iff, isQueryBoundP_query_bind_iff]
  exact ⟨.inr Nat.one_pos, fun _ => (qb_iff _ _).1 (QB.pure _ _)⟩

theorem QB.mapM_sum {α β : Type} (f : α → OracleComp spec β) (c : α → ℕ)
    (h : ∀ x, QB (f x) (c x)) : ∀ l : List α, QB (l.mapM f) (l.map c).sum
  | [] => by simpa using QB.pure ([] : List β) 0
  | x :: l => by
    simp only [List.mapM_cons, List.map_cons, List.sum_cons]
    exact ((h x).bind fun a => (QB.mapM_sum f c h l).bind fun bs => QB.pure (a :: bs) 0).mono
      (by omega)

theorem QB.mapM_const {α β : Type} (f : α → OracleComp spec β) (c : ℕ)
    (h : ∀ x, QB (f x) c) (l : List α) : QB (l.mapM f) (l.length * c) := by
  simpa [List.map_const', List.sum_replicate] using QB.mapM_sum f (fun _ => c) h l

theorem QB.sequenceFin {α : Type} (c : ℕ) :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α), (∀ i, QB (f i) c) →
      QB (Concrete.sequenceFin f) (n * c)
  | 0, f, _ => by simpa [Concrete.sequenceFin] using QB.pure (Fin.elim0 : Fin 0 → α) 0
  | n + 1, f, h => by
    simp only [Concrete.sequenceFin]
    refine ((h 0).bind fun _ => (QB.sequenceFin c (fun i : Fin n => f i.succ)
      fun i => h i.succ).bind fun _ => QB.pure _ 0).mono ?_
    rw [Nat.add_mul]
    omega

end Count

/-! ## The hash computations of leanVM -/

section Hash

abbrev HQ {α : Type} (oa : OracleComp HashSpec α) (n : ℕ) : Prop := QB oa n

theorem tweakableHash_bound (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    HQ (Concrete.tweakableHash (m := OracleComp HashSpec) parameter domain payload) 1 := by
  unfold Concrete.tweakableHash Concrete.oracleHash
  exact ((QB.query _).bind fun _ => QB.pure _ 0)

theorem merkleNode_bound (parameter : PublicParameter) (lay : Layer)
    (chainEnd : KeyIndex → ChainIndex → Digest) :
    ∀ level idx, HQ (merkleNode parameter lay chainEnd level idx) (2 ^ (level + 1) - 1)
  | 0, idx => by
    simp only [merkleNode, Concrete.leafHash]
    exact (tweakableHash_bound _ _ _).mono (by norm_num)
  | level + 1, idx => by
    simp only [merkleNode]
    refine ((merkleNode_bound parameter lay chainEnd level (2 * idx)).bind fun _ =>
      (merkleNode_bound parameter lay chainEnd level (2 * idx + 1)).bind fun _ =>
        tweakableHash_bound _ _ _).mono ?_
    have h1 : 1 ≤ 2 ^ (level + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (level + 1 + 1) = 2 * 2 ^ (level + 1) := by ring
    omega

theorem grind_bound (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomness) : ∀ attempts trial,
      HQ (grind parameter lay key message base attempts trial) attempts
  | 0, _ => by simpa [grind] using QB.pure (none : Option (Randomness × Encoding)) 0
  | attempts + 1, trial => by
    simp only [grind]
    refine ((tweakableHash_bound _ _ _).bind (m := attempts) fun d => ?_).mono (by omega)
    split
    · exact (QB.pure _ 0).mono (Nat.zero_le _)
    · exact grind_bound parameter lay key message base attempts (trial + 1)

theorem chainWalk_bound (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex) :
    ∀ start steps value, HQ (Concrete.chainWalk (m := OracleComp HashSpec) parameter lay key l start
      steps value) steps
  | _, 0, value => QB.pure _ 0
  | start, steps + 1, value => by
    simp only [Concrete.chainWalk]
    refine (chainWalk_bound parameter lay key l start steps value).bind fun _ => ?_
    split
    · exact tweakableHash_bound _ _ _
    · exact (QB.pure _ 0).mono (Nat.zero_le _)

theorem treeFold_bound (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : ℕ) : ∀ value,
    HQ (Concrete.treeFold (m := OracleComp HashSpec) parameter lay key path levels value) levels := by
  induction levels with
  | zero => intro value; exact QB.pure _ 0
  | succ levels ih =>
    intro value
    rw [Concrete.treeFold]
    refine (ih value).bind fun _ => ?_
    split <;> (dsimp only; split <;> exact tweakableHash_bound _ _ _)

theorem layerRoot_bound (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    HQ (Concrete.layerRoot (m := OracleComp HashSpec) parameter lay key message part)
      (1 + (numChains * chainLength + 1 + layerHeight)) := by
  unfold Concrete.layerRoot Concrete.otsLeaf Concrete.messageDigest
  refine (QB.bind (n := 1 + (numChains * chainLength + 1)) (m := layerHeight) ?_ fun r => ?_).mono
    (by omega)
  · refine (tweakableHash_bound _ _ _).bind fun d => ?_
    split
    · refine ((QB.sequenceFin chainLength _ fun l => ?_).bind fun _ =>
        (tweakableHash_bound _ _ _).bind fun _ => QB.pure _ 0).mono (by simp [numChains])
      unfold Concrete.recoverChain
      exact (chainWalk_bound _ _ _ _ _ _ _).mono (by omega)
    · exact (QB.pure _ 0).mono (Nat.zero_le _)
  · rcases r with _ | leaf
    · exact (QB.pure _ 0).mono (Nat.zero_le _)
    · show QB (Concrete.treeFold (m := OracleComp HashSpec) parameter lay key part.path layerHeight leaf >>=
        fun root => Pure.pure (some root)) layerHeight
      exact (treeFold_bound parameter lay key part.path layerHeight leaf).bind (m := 0) fun _ =>
        QB.pure _ 0

end Hash

/-! ## The calls of the tables of one tree -/

theorem sum_flatMap_replicate {α : Type} (l : List α) (n c : ℕ) :
    (l.flatMap fun _ => List.replicate n c).sum = l.length * (n * c) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, List.sum_replicate, ih]; ring
theorem topJobs_points : (topJobs.flatMap (·.points)).length = 2 ^ layerHeight * numChains := by
  simp only [topJobs, List.length_flatMap, List.map_flatMap, List.map_map, Function.comp_def,
    List.length_cons, List.length_nil, List.map_const', sum_flatMap_replicate, List.length_finRange]
  ring
theorem bottomJobs_points (b : Fin (2 ^ layerHeight)) :
    ((bottomJobs b).flatMap (·.points)).length = 2 ^ layerHeight * numChains * 3 + 2 ^ layerHeight + 1 := by
  simp only [bottomJobs, List.flatMap_append, List.length_append, List.length_flatMap, List.map_flatMap,
    List.map_map, Function.comp_def, List.length_cons, List.length_nil, List.map_const',
    sum_flatMap_replicate, List.length_finRange, List.sum_replicate, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  ring

theorem signJobs_points (b : Fin (2 ^ layerHeight)) (e : Encoding) :
    ((signJobs b e).flatMap (·.points)).length = numChains := by
  simp only [signJobs, List.length_flatMap, List.map_map, Function.comp_def, List.length_cons,
    List.length_nil, List.map_const', List.sum_replicate, List.length_finRange]
  ring

section Ro

theorem hashQuery_bound (q : Query C) : QB (hashQuery q) 1 := QB.query (spec := RoSpec C) (.inl q)

theorem tweakable_bound {α : Type} (oa : OracleComp HashSpec α) :
    ∀ n, QB oa n → QB (tweakable (C := C) oa) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; simpa only [tweakable, simulateQ_pure] using QB.pure (spec := RoSpec C) a n
  | query_bind t k ih =>
    intro n h
    rw [qb_iff, isQueryBoundP_query_bind_iff] at h
    have hn : 0 < n := h.1.resolve_left (by simp)
    have hk : ∀ u, QB (k u) (n - 1) := fun u => (qb_iff _ _).2 (by simpa using h.2 u)
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    exact ((hashQuery_bound (.hash t)).bind fun u => ih u (n - 1) (hk u)).mono (by omega)

theorem prfValue_bound (seeds : C.Term → HashOutput) (x : Point) :
    QB (prfValue seeds x) C.terms.length := by
  unfold prfValue
  exact ((QB.mapM_const _ 1 (fun T => (hashQuery_bound _).map _) C.terms).bind fun _ =>
    QB.pure _ 0).mono (by simp)

theorem evalJob_bound (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (job : Job) : QB (evalJob circuits parameter seeds job) (job.points.length * C.terms.length) := by
  unfold evalJob
  exact ((QB.mapM_const _ _ (fun x => prfValue_bound seeds x) job.points).bind fun _ =>
    QB.pure _ 0).mono (by simp)

theorem jobs_bound (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (jobs : List Job) :
    QB (jobs.mapM (evalJob circuits parameter seeds)) ((jobs.flatMap (·.points)).length * C.terms.length) := by
  refine (QB.mapM_sum _ _ (evalJob_bound circuits parameter seeds) jobs).mono (le_of_eq ?_)
  rw [List.length_flatMap, List.sum_map_mul_right]

end Ro

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.qb_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms qb_iff

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.QB.mapM_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QB.mapM_sum

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.QB.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QB.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.merkleNode_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms merkleNode_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.grind_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grind_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.chainWalk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainWalk_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.treeFold_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeFold_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.layerRoot_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layerRoot_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.topJobs_points' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topJobs_points

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.bottomJobs_points' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bottomJobs_points

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.signJobs_points' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signJobs_points

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.tweakable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tweakable_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.prfValue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfValue_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotEmulation.jobs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jobs_bound

end ThresholdLeanXmssSecurity.LifetimeSlotEmulation
