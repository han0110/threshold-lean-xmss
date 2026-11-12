import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkRecipe
import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenPrograms

/-!
Cache entries on any non-stream-key domain have a counted or free log answer.
The actual roles have zero programming queries, so unlogged programming writes
are excluded. Coverage starts at the empty setup cache and follows the fixed
A35 walk's actual selection and scheduler steps to every supported cut prefix.
The coin-key/expansion instance needs no liveness or label-agreement premise.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckSeenCovered
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000
set_option linter.constructorNameAsVariable false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives)

def CoveredOn (P : Query C → Prop) (cache : HashCache C) (log : TreeSimLog C) : Prop :=
  ∀ q h, P q → cache q = some h → TreeSimHashAnswer log q h

def TreeCheckSeenQuery : Query C → Prop
  | .coinKey .. | .expand .. => True
  | _ => False

theorem seen_not_streamKey (key) : ¬ TreeCheckSeenQuery (C := C) (.streamKey key) := by
  simp [TreeCheckSeenQuery]

variable {P : Query C → Prop} (exclude : ∀ key, ¬ P (.streamKey key))

-- Port of TreeSimCheck.lean:3552–3648. The hash entry proof is domain-free;
-- the local proof uses only streamKey exclusion.
theorem hash_entry (asked q : Query C) (cache : HashCache C)
    (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims asked).run cache)) (h : HashOutput)
    (entry : p.2 q = some h) :
    cache q = some h ∨ asked = q ∧ p.1 = h := by
  by_cases fixed : IsFixed asked
  · obtain ⟨input, rfl, hm⟩ := fixed
    rw [hashAnswer_of_isFixed prims hm] at hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact Or.inl entry
  · rw [hashAnswer_of_not_isFixed prims fixed] at hp
    obtain ⟨_, self, other⟩ := randomOracle_support asked cache p hp
    by_cases he : asked = q
    · subst q
      exact Or.inr ⟨rfl, Option.some.inj (self.symm.trans entry)⟩
    · exact Or.inl ((other q (Ne.symm he)) ▸ entry)

include exclude in
theorem local_entry (t : (LocalSpec C).Domain) (cache : HashCache C)
    (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run cache))
    (q : Query C) (h : HashOutput) (hq : P q) (entry : p.2 q = some h) :
    cache q = some h ∨
      (⟨t, p.1⟩ : (u : (LocalSpec C).Domain) × (LocalSpec C).Range u) =
        ⟨.inr (.inl q), h⟩ := by
  rcases t with n | asked | x
  · simp [localAnswer, unifFwdImpl] at hp
    obtain ⟨u, rfl⟩ := hp
    exact Or.inl entry
  · rcases hash_entry prims asked q cache p hp h entry with old | ⟨rfl, hh⟩
    · exact Or.inl old
    · exact Or.inr (by cases hh; rfl)
  · simp [localAnswer, prgAnswer] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rcases hash_entry prims (.streamKey x.2.1) q cache r hr h entry with old | ⟨he, _⟩
    · exact Or.inl old
    · subst q
      exact (exclude _ hq).elim

theorem CoveredOn.mono {cache : HashCache C} {a b : TreeSimLog C}
    (covered : CoveredOn P cache a) (hp : a <+: b) : CoveredOn P cache b := by
  intro q h hq he
  exact (covered q h hq he).imp (fun hh => hp.sublist.subset hh) (fun hh => hp.sublist.subset hh)

include exclude in
theorem counted_covered (D : C.Coalition)
    (t : (LocalSpec C).Domain) (s : TreeSimState C)
    (r : (LocalSpec C).Range t × TreeSimState C)
    (covered : CoveredOn P s.1.1 s.2)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl t))).run s)) :
    CoveredOn P r.2.1.1 r.2.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, streamWorld, onHash, support_map] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  obtain ⟨u, hu, rfl⟩ := hp
  intro q h hq he
  rcases local_entry prims exclude t s.1.1 u hu q h hq he with old | same
  · exact (covered.mono (List.prefix_append _ _)) q h hq old
  · apply Or.inr
    have eqworld := congrArg (fun a : (v : (LocalSpec C).Domain) × (LocalSpec C).Range v =>
      (⟨.inl (.inl a.1), a.2⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v)) same
    change (⟨.inl (.inl (.inr (.inl q))), h⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v) ∈ _
    rw [← eqworld]
    simp

include exclude in
set_option backward.isDefEq.respectTransparency false in
theorem free_covered (D : C.Coalition)
    (t : (LocalSpec C).Domain) (s : TreeSimState C)
    (r : (LocalSpec C).Range t × TreeSimState C)
    (covered : CoveredOn P s.1.1 s.2)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
    CoveredOn P r.2.1.1 r.2.2 := by
  have ordinary (t : (LocalSpec C).Domain)
      (hrun : streamWorld prims D (.inr t) = onHash (localAnswer prims t))
      (r : (LocalSpec C).Range t × TreeSimState C)
      (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
      CoveredOn P r.2.1.1 r.2.2 := by
    simp only [treeSimLoggedWorld, StateT.run_mk, hrun, onHash, support_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    obtain ⟨u, hu, rfl⟩ := hp
    intro q h hq he
    rcases local_entry prims exclude t s.1.1 u hu q h hq he with old | same
    · exact (covered.mono (List.prefix_append _ _)) q h hq old
    · apply Or.inl
      have eqworld := congrArg (fun a : (v : (LocalSpec C).Domain) × (LocalSpec C).Range v =>
        (⟨.inr a.1, a.2⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v)) same
      change (⟨.inr (.inr (.inl q)), h⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v) ∈ _
      rw [← eqworld]
      simp
  rcases t with n | q | x
  · exact ordinary _ rfl r hr
  · exact ordinary _ rfl r hr
  · by_cases hh : Hidden D x.1
    · simp only [treeSimLoggedWorld, StateT.run_mk, streamWorld, if_pos hh,
        support_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      obtain ⟨u, hu, rfl⟩ := hp
      exact covered.mono (List.prefix_append _ _)
    · exact ordinary _ (by simp only [streamWorld, if_neg hh]) r hr

open LifetimeKeygenHopProof (Programming)
open LifetimeKeygenPrograms (qb0_bind' free_quiet counted_quiet)

include exclude in
/-- Programming must be absent: its cache writes have no hash-answer log entry. -/
theorem run_covered {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (quiet : IsQueryBoundP p Programming 0) (s : TreeSimState C) (r : α × TreeSimState C)
    (covered : CoveredOn P s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    CoveredOn P r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact covered
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have ht : ¬ Programming t := quiet.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    apply ih mid.1 (by simpa only [if_neg ht] using quiet.2 mid.1) mid.2 r _ hr
    rcases t with (t | t) | t
    · exact counted_covered prims exclude D t s mid covered hmid
    · exact (ht trivial).elim
    · exact free_covered prims exclude D t s mid covered hmid

/-- WorldSpec version of A156's RolesQuiet, using the existing actual-copy bounds. -/
theorem worldRoles_quiet {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary p) Programming 0 ∧
      IsQueryBoundP (worldRoles.honest p) Programming 0 :=
  ⟨counted_quiet p, free_quiet p⟩

-- Port of LifetimeRunBoundary.startSteps_quietP and stepRound_quietP,
-- specializing the generic role argument to the actual worldRoles.
theorem startSteps_quiet {α : Type} (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (startSteps worldRoles D program) Programming 0 := by
  apply isQueryBoundP_sequenceFin
  intro i
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (worldRoles_quiet _).2

theorem stepRound_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) Programming 0 := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine qb0_bind' (counted_quiet _) fun r => qb0_bind' ?_ fun _ => isQueryBoundP_pure _ _ _
  apply isQueryBoundP_sequenceFin
  intro j
  cases steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | wait out resume =>
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact free_quiet _
  | call input _ => exact input.elim

theorem executeRounds_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps) Programming 0 := by
  induction fuel generalizing state steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ fuel ih =>
    rw [executeRounds]
    split
    · exact isQueryBoundP_pure _ _ _
    · exact qb0_bind' (stepRound_quiet D A state steps) fun r => ih r.1 r.2.1

theorem executePhase_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program) Programming 0 := by
  exact qb0_bind' (startSteps_quiet D program) fun steps =>
    executeRounds_quiet D A fuel state steps

include exclude in
theorem setup_covered (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z)) : CoveredOn P p.2.1.1 p.2.2 := by
  unfold treeSaltSetup at hp
  rw [mem_support_bind_iff] at hp
  obtain ⟨start, hs, hp⟩ := hp
  have covered : CoveredOn P start.2.1.1 start.2.2 :=
    run_covered prims exclude D _ (counted_quiet _) _ start (by
      intro q h _ he
      change (none : Option HashOutput) = some h at he
      cases he) hs
  apply run_covered prims exclude D _ (executePhase_quiet D A _ _ _) _ p covered
  simpa only [simulateQ_executePhase, treeSimRealRoles] using hp

open TreeCheckWalkDef TreeCheckWalkRecipe

/-- The signing-boundary selector also runs only free local computations. -/
theorem select_quiet {α : Type} {n : ℕ}
    (gate : Fin n → OracleComp (LocalSpec C) (Option α)) :
    IsQueryBoundP (select fun i => free (gate i)) Programming 0 := by
  induction n with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ n ih =>
    unfold select
    apply qb0_bind' (free_quiet _)
    intro result
    cases result with
    | some value => exact isQueryBoundP_pure _ _ _
    | none => exact (isQueryBoundP_map_iff _ _ _).2 (ih _)

include exclude in
theorem selectPending_covered {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (p r : Pending A) (covered : CoveredOn P p.world.1.1 p.world.2)
    (hr : r ∈ support (selectPending prims D A gate cont p)) :
    CoveredOn P r.world.1.1 r.world.2 := by
  simp only [selectPending, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨selected, hs, rfl⟩ := hr
  exact run_covered prims exclude D _ (select_quiet _) _ selected covered hs

include exclude in
theorem prepare_covered (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ) (p r : Pending A)
    (covered : CoveredOn P p.world.1.1 p.world.2)
    (hr : r ∈ support (prepare prims K D A circuits settings top tree x setup j p)) :
    CoveredOn P r.world.1.1 r.world.2 := by
  unfold prepare at hr
  cases tree with
  | top => simpa only [mem_support_pure_iff] using hr ▸ covered
  | bottom b =>
    dsimp only at hr
    split_ifs at hr
    · exact selectPending_covered prims exclude D A _ _ p r covered hr
    · simpa only [mem_support_pure_iff] using hr ▸ covered
    · simpa only [mem_support_pure_iff] using hr ▸ covered

include exclude in
theorem next_covered (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (fuel : ℕ) (p r : Pending A)
    (covered : CoveredOn P p.world.1.1 p.world.2)
    (hr : .inl r ∈ support (next prims D Z fuel p)) :
    CoveredOn P r.world.1.1 r.world.2 := by
  unfold next at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨started, hs, hr⟩ := hr
  have cov := run_covered prims exclude D _ (startSteps_quiet D p.program) _ started covered hs
  split_ifs at hr
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, impossible⟩ := hr
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at hr
    obtain ⟨reply, hr, rfl⟩ := hr
    exact run_covered prims exclude D _ (counted_quiet _) _ reply cov hr

include exclude in
/-- Full bounded walk, including the actual free signing-head selection. -/
theorem walk_covered (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (fuel : ℕ) (p : Pending A)
    (c : Decoded (decode prims K D A circuits settings top tree x setup j))
    (covered : CoveredOn P p.world.1.1 p.world.2)
    (hr : .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p)) :
    CoveredOn P c.1.1.world.1.1 c.1.1.world.2 := by
  induction fuel generalizing p with
  | zero =>
    simp only [TreeCheckWalkRecipe.walk, mem_support_bind_iff] at hr
    obtain ⟨current, hc, hr⟩ := hr
    have cov := prepare_covered prims exclude K D A circuits settings top tree x setup j
      {p with fuel := 0} current covered hc
    split_ifs at hr
    · simp only [mem_support_pure_iff, Sum.inl.injEq] at hr
      cases hr
      exact cov
    · simp only [support_map, Set.mem_image] at hr
      obtain ⟨_, _, impossible⟩ := hr
      cases impossible
  | succ fuel ih =>
    simp only [TreeCheckWalkRecipe.walk, mem_support_bind_iff] at hr
    obtain ⟨current, hc, hr⟩ := hr
    have cov := prepare_covered prims exclude K D A circuits settings top tree x setup j
      {p with fuel := fuel + 1} current covered hc
    split_ifs at hr
    · simp only [mem_support_pure_iff, Sum.inl.injEq] at hr
      cases hr
      exact cov
    · rw [mem_support_bind_iff] at hr
      obtain ⟨result, hn, hr⟩ := hr
      cases result with
      | inr terminal => simp only [mem_support_pure_iff] at hr; cases hr
      | inl pending => exact ih pending (next_covered prims exclude D A Z fuel current pending cov hn) hr

include exclude in
theorem boundary_pre_covered (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckTailBoundary A) (o : TreeCheckTailCheckpoint A)
    (covered : CoveredOn P b.batch.world.1.1 b.batch.world.2)
    (hr : o ∈ support (b.pre prims K circuits settings D)) : CoveredOn P o.2.1.1 o.2.2 := by
  unfold TreeCheckTailBoundary.pre at hr
  exact run_covered prims exclude D _ (executePhase_quiet D A _ _ _) _ o covered hr

include exclude in
/-- Every supported checkpoint of A35's fixed source has logged cache coverage.
No liveness, first-run restriction, or agreement premise is needed for coverage. -/
theorem sourceWalk_covered (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (c : Decoded (decode prims K D A circuits settings top tree x p.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : (Decoded (decode prims K D A circuits settings top tree x p.1.2 j) ×
        TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A) ∈ support
      ((sourceWalk prims K D A circuits settings top tree x j Z step p).cut prims K circuits settings D Z).pre) :
    CoveredOn P o.2.1.1 o.2.2 := by
  let W := sourceWalk prims K D A circuits settings top tree x j Z step p
  have hc : .inl c ∈ support W.pre := by
    with_reducible exact index_support prims D Z K circuits settings W c o run
  have ho : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (W := W) (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      (D := D) (Z := Z) (c := c) (o := o) run)
  dsimp only [W, TreeCheckWalkRecipe.sourceWalk] at hc
  have initcov : CoveredOn P (initial K circuits settings top tree x p).world.1.1
      (initial K circuits settings top tree x p).world.2 := by
    change CoveredOn P p.2.1.1 p.2.2
    exact setup_covered prims exclude D A x z p hp
  have cov : CoveredOn P c.1.1.world.1.1 c.1.1.world.2 := by
    with_reducible exact (walk_covered prims exclude K D A circuits settings top tree x p.1.2 j Z
      (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p)
      c initcov hc)
  apply boundary_pre_covered prims exclude K circuits settings D A (W.boundary c) o _ ho
  exact cov

include exclude in
/-- Exact coverage field on the unchanged A35 family, for any non-stream-key domain. -/
theorem walkCheckpoint_coveredOn (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun _ _ D _ _ _ Z _ _ _ _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre → CoveredOn P o.2.1.1 o.2.2 := by
  intro _ top tree D A x z Z q _ bounded _ j p hp c o run
  with_reducible exact sourceWalk_covered prims exclude K D A circuits settings top tree x z j Z _ p hp c o run

/-- Coin-key and expansion coverage at every supported pre-checkpoint. -/
theorem walkCheckpoint_seen_covered (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun _ _ D _ _ _ Z _ _ _ _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
          CoveredOn TreeCheckSeenQuery o.2.1.1 o.2.2 :=
  walkCheckpoint_coveredOn prims seen_not_streamKey K circuits settings

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSeenCovered.walkCheckpoint_coveredOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms walkCheckpoint_coveredOn

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckSeenCovered.walkCheckpoint_seen_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms walkCheckpoint_seen_covered

end TreeCheckSeenCovered
end ThresholdLeanXmssSecurity
