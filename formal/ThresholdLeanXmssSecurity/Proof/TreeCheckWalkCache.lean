import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkTransport
import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestLog

/-!
# Cache certificates for the fixed check walk

Coverage and the honest-query classifier give the original `SoundCache`
certificate at each first-run checkpoint. The full cache condition splits
into these checkpoints and the signing checkpoints of bottom trees.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckWalkCache

open TreeCheckWalkRecipe TreeCheckWalkTransport TreeCheckSeenCovered TreeCheckHonestLog
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
variable {C : Committee} {E : Type}

theorem counted_seen {log : TreeSimLog C} {q : Query C} {answer : HashOutput}
    (notFixed : ¬ IsFixed q)
    (entry : (⟨.inl (.inl (.inr (.inl q))), answer⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log) :
    q ∈ treeCheckCountedSeen log := by
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  refine ⟨_, entry, ?_⟩
  simp only [treeCheckCountedProjection, soundQueryProjection, if_neg notFixed]

/-- Honest coin labels precede the cutoff; all other relevant cached answers
come from the fixed counted-log projection. -/
theorem soundCache_of_covered_honest {cache : HashCache C} {log : TreeSimLog C}
    {cutoff label : ℕ} (covered : CoveredOn TreeCheckSeenCovered.TreeCheckSeenQuery cache log)
    (honest : HonestCheckLog cutoff cache log) (le : cutoff ≤ label) :
    SoundCache label cache (treeCheckCountedSeen log) (priorKeys label cache) := by
  constructor
  · intro tag next bits future cached
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp cached
    rcases covered _ answer trivial hanswer with free | counted
    · have early := honest.1 tag next bits answer free
      omega
    · exact counted_seen (by simp [IsFixed]) counted
  · intro key index cached
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp cached
    rcases covered _ answer trivial hanswer with free | counted
    · exact Or.inl (priorKeys_mono le (le_refl _) (honest.2 key index answer free))
    · exact Or.inr (counted_seen (by simp [IsFixed]) counted)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Every supported first-run checkpoint has the exact cache, counted log and
prior-key set of its own hybrid adapter. No liveness premise is needed. -/
theorem walkCheckpointCache_first :
    AtWalk prims K circuits settings fun _ tree D _ _ _ Z _ _ j _ W =>
      j.val < (firstChunks settings tree).length →
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        let hybrid := (W.cut prims K circuits settings D Z).hybrid (.inl (c, o))
        SoundCache hybrid.label hybrid.cache hybrid.seen hybrid.keys := by
  intro hb top tree D A x z Z q dealt bounded small j p hp first c o run
  have covered : CoveredOn TreeCheckSeenCovered.TreeCheckSeenQuery o.2.1.1 o.2.2 := by
    have result := walkCheckpoint_seen_covered prims K circuits settings
    unfold AtWalk at result
    with_reducible exact (result hb top tree D A x z Z q dealt bounded small j p hp c o run)
  have honest : HonestCheckLog
      (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
      o.2.1.1 o.2.2 := by
    have result := walkCheckpoint_honest prims K circuits settings
    unfold AtWalk at result
    with_reducible exact (result hb top tree D A x z Z q dealt bounded small j p hp first c o run)
  change SoundCache _ o.2.1.1 (treeCheckCountedSeen o.2.2) (priorKeys _ o.2.1.1)
  apply soundCache_of_covered_honest covered honest
  dsimp only [family, sourceWalk, TreeCheckTailWalk.cut, TreeCheckWalkDef.hybrid, seed, callerBatch]
  rw [TreeCheckWalkState.lockstepStart_first circuits settings tree _ _ _ first.le]
  omega

/-- The cache condition restricted to signing batches of bottom trees, including
the first signing batch. The family and all adapter fields are unchanged. -/
def WalkCheckpointCacheSigning : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    (∃ b, tree = .bottom b) → (firstChunks settings tree).length ≤ j.val →
      ∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
        (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
        ∀ c o, s = .inl (c, o) →
          SoundCache ((W.cut prims K circuits settings D Z).hybrid s).label
            ((W.cut prims K circuits settings D Z).hybrid s).cache
            ((W.cut prims K circuits settings D Z).hybrid s).seen
            ((W.cut prims K circuits settings D Z).hybrid s).keys

/-- Transport a checkpoint certificate through the cut-state equality before
instantiating the walk with a concrete ceremony program. -/
theorem cache_at {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckTailWalk A)
    (cached : ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
      let h := (W.cut prims K circuits settings D Z).hybrid (.inl (c, o))
      SoundCache h.label h.cache h.seen h.keys) :
    ∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
      ∀ c o, s = .inl (c, o) →
      let h := (W.cut prims K circuits settings D Z).hybrid s
      SoundCache h.label h.cache h.seen h.keys := by
  rintro s run c o rfl
  exact cached c o run

/-- The only cache cases outside the first run are bottom-tree signing batches. -/
theorem walkCheckpointCache_of_signing
    (signing : WalkCheckpointCacheSigning prims K circuits settings) :
    WalkCheckpointCache prims K circuits settings := by
  unfold WalkCheckpointCacheSigning AtWalk at signing
  intro hb top tree D A x z Z q dealt bounded small j p hp
  by_cases first : j.val < (firstChunks settings tree).length
  · have result := walkCheckpointCache_first prims K circuits settings
    unfold AtWalk at result
    have cached := cache_at prims K circuits settings Z
      (family prims K circuits settings top tree D A x Z q bounded j p)
      (result hb top tree D A x z Z q dealt bounded small j p hp first)
    intro s run live c o same
    with_reducible exact cached s run c o same
  · with_reducible apply signing hb top tree D A x z Z q dealt bounded small j p hp
    · cases tree with
      | bottom b => exact ⟨b, rfl⟩
      | top =>
          apply False.elim
          apply first
          simpa only [firstChunks, treeLockstepFirstJobs, treeBatches] using j.isLt
    · omega

end ThresholdLeanXmssSecurity.TreeCheckWalkCache

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCache.soundCache_of_covered_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCache.soundCache_of_covered_honest

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCache.walkCheckpointCache_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCache.walkCheckpointCache_first

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCache.walkCheckpointCache_of_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCache.walkCheckpointCache_of_signing
