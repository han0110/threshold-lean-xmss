import ThresholdLeanXmssSecurity.Proof.TreeCheckMaskExtraction
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkRecipe

/-!
# All-honest boundaries of the actual check walk

The empty coalition is `noCoalition`. At a live checkpoint every honest row
is present. Pending local opening tails can therefore be removed from an
allowed replay without changing its deliveries or the final cache used for
its shared-mask certificate.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks

open TreeCheckAllHonestProof TreeCheckMaskExtraction
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A coalition with no member is the canonical empty coalition. -/
theorem eq_noCoalition (D : C.Coalition) (empty : ¬ ∃ i, i ∈ D.1) : D = noCoalition := by
  apply Subtype.ext
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => empty ⟨i, hi⟩)

/-- An ordered sequence retains each individual allowed replay. -/
theorem allowed_sequence {ι α : Type} {S : OracleSpec.{0, 0} ι} {n : ℕ}
    (allowed : (t : S.Domain) → S.Range t → Prop)
    (f : Fin n → OracleComp S α) (out : Fin n → α)
    (run : TreeSimCheckAllowed allowed (Concrete.sequenceFin f) out) :
    ∀ i, TreeSimCheckAllowed allowed (f i) (out i) := by
  have expanded : TreeSimCheckAllowed allowed
      (Concrete.sequenceFin (fun i => f i >>= pure)) out := by simpa using run
  obtain ⟨values, each, rest⟩ := allowed_sequence_bind allowed f (fun _ a => pure a) out expanded
  rw [sequenceFin_pure] at rest
  rw [rest.pure_inv]
  exact each

/-- A failed operator remains failed after one honest-network step. -/
theorem honestStep_failed {α : Type}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (steps next : C.Party → Step C E RealSpec α) (i : C.Party)
    (failed : steps i = .done none)
    (run : TreeSimCheckAllowed allowed (honestStep noFunctionality PEmpty.elim steps) next) :
    next i = .done none := by
  unfold honestStep at run
  split_ifs at run
  · obtain ⟨outputs, _, run⟩ := run.bind_inv
    have each := allowed_sequence allowed _ next run i
    simp only [failed] at each
    exact each.pure_inv
  · have each := allowed_sequence allowed _ next run i
    simp only [failed] at each
    exact each.pure_inv

/-- Honest scheduling never restores an operator that already failed. -/
theorem honestRounds_failed {α : Type}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (fuel : ℕ) (steps : C.Party → Step C E RealSpec α)
    (out : C.Party → Option α) (i : C.Party) (failed : steps i = .done none)
    (run : TreeSimCheckAllowed allowed (honestRounds noFunctionality PEmpty.elim fuel steps) out) :
    out i = none := by
  induction fuel generalizing steps with
  | zero => simpa only [failed, Step.output] using congrFun run.pure_inv i
  | succ fuel ih =>
    simp only [honestRounds] at run
    split_ifs at run
    · simpa only [failed, Step.output] using congrFun run.pure_inv i
    · obtain ⟨next, hs, rest⟩ := run.bind_inv
      exact ih next (honestStep_failed allowed steps next i failed hs) rest

/-- A failed initial program cannot produce a present final row. -/
theorem honestRun_failed {α : Type}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (program : C.Party → PartyM C E RealSpec α) (fuel : ℕ)
    (out : C.Party → Option α) (i : C.Party) (failed : program i = failure)
    (run : TreeSimCheckAllowed allowed
      (honestStart program >>= honestRounds noFunctionality PEmpty.elim fuel) out) : out i = none := by
  obtain ⟨steps, hs, rest⟩ := run.bind_inv
  have each := allowed_sequence allowed _ steps hs i
  simp only [failed, advance_run_failure] at each
  exact honestRounds_failed allowed fuel steps out i each.pure_inv rest

/-- At a present checkpoint all pending local gates succeeded. Removing just
their queries preserves one joint replay against the same allowed answers. -/
theorem localPrelude_erase {α : Type}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (tail : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (program : C.Party → PartyM C E RealSpec α) (fuel : ℕ)
    (out : C.Party → Option α) (present : ∀ i, (out i).isSome)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => treeLockstepLocalPrelude (tail i) >>= fun _ => program i) >>=
        honestRounds noFunctionality PEmpty.elim fuel) out) :
    TreeSimCheckAllowed allowed
      (honestStart program >>= honestRounds noFunctionality PEmpty.elim fuel) out := by
  simp only [treeLockstepLocalPrelude, bind_assoc] at run
  obtain ⟨values, _, rest⟩ := honest_local_draw_replay allowed tail _ fuel out run
  have successful i : values i = some () := by
    cases hi : values i with
    | none =>
      have failed := honestRun_failed allowed _ fuel out i (by simp only [hi, failure_bind]) rest
      have hp := present i
      simp only [failed, Option.isSome_none, Bool.false_eq_true] at hp
    | some value => cases value; rfl
  simpa only [successful, pure_bind] using rest


set_option backward.isDefEq.respectTransparency false in
/-- The common-mask certificate applies to the actual batch with its interleaved
pending opening tails, whenever its saved rows are all present. -/
theorem tail_saved (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckTailBoundary A)
    (parameters : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (shared : SharedPrss b.batch.ctx) (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings noCoalition))
    (present : ∀ i, (o.1.2 i).isSome) :
    SavedByMasks K settings.mode (b.batch.jobs.map (circuits b.batch.parameter ·.kind))
      (fun i => (treeCheckPrefixData (o.1.2 i)).1)
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2) := by
  have positive : 0 < C.n := by
    have := C.one_le_t
    unfold Committee.n
    omega
  letI : Nonempty C.Party := ⟨⟨0, positive⟩⟩
  have replay := phase_erase A _ _ b.batch.state _ o.1
    (treeLockstep_logged_run_allowed prims noCoalition _ b.batch.world o run)
  have replay := localPrelude_erase _ b.tail _ (b.batch.rounds circuits settings) o.1.2 present replay
  simp only [treeSimCheckBatchPrefix, inputShares_fun, mapM_oracleStep, parameters] at replay
  let allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop :=
    fun t u => TreeLockstepWorldStreams prims noCoalition o.2.1 (.inr t) u
  let next : C.Party → MainInput C → PartyM C E RealSpec
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C) := fun i inputs => do
    let result ← (treeSimCheckBeforeVerify K (b.batch.ctx i) settings.mode
      (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) inputs).run
      ⟨fun _ => [], b.batch.initial.1, b.batch.initial.2⟩
    pure (inputs, result)
  obtain ⟨x, _, rest⟩ := honest_draw_replay allowed
    (fun i => b.batch.jobs.mapM (inputQuery (b.batch.ctx i))) next
    (b.batch.rounds circuits settings) o.1.2 replay
  dsimp only [next, allowed, TreeCheckBatchBoundary.rounds] at rest
  have certificate := beforeVerify_replay prims K o.2.1
    (fun t u => TreeLockstepWorldStreams prims noCoalition o.2.1 (.inr t) u)
    (fun _ _ h => h) b.batch.ctx shared settings.mode
    (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) x b.batch.initial.1
    (fun _ => ⟨fun _ => [], b.batch.initial.1, b.batch.initial.2⟩) (fun _ => rfl) o.1.2
  have extracted := certificate (by
    dsimp only [RealSpec, WorldSpec] at rest ⊢
    with_reducible_and_instances exact rest)
  rw [funext extracted.2.1]
  exact extracted.2.2

/-- An actual wrong opening cannot follow an all-honest batch with common keys,
including the pending local work preceding that batch. -/
theorem tail_no_wrong_opening (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckTailBoundary A)
    (parameters : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (shared : SharedPrss b.batch.ctx) (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings noCoalition))
    (present : ∀ i, (o.1.2 i).isSome)
    (opening : TreeCheckOpeningAt prims K circuits noCoalition A b.batch o) : False := by
  have self := shared.choose_spec.choose_spec.1
  have values : (fun i => (treeCheckPrefixData (o.1.2 i)).1) =
      batchInputs opening.hash opening.seeds b.batch.jobs := by
    funext i
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (present i)
    have h := b.dealer_inputs prims K circuits settings noCoalition self opening.seeds opening.seed
      o run opening.hash opening.rows i (by simp) data hd
    simpa only [hd, treeCheckPrefixData, Option.getD_some] using h
  have inputs : MainInputs (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) noCoalition
      (fun i => (treeCheckPrefixData (o.1.2 i)).1) := by
    rw [values]
    exact treeCheck_batchInputs_main noCoalition opening.hash opening.seeds circuits b.batch.parameter b.batch.jobs
  have accepted := SavedByMasks.verified K settings.mode _ _ inputs _
    (tail_saved prims K circuits settings A b parameters shared o run present)
  exact b.opening_reject prims K circuits settings noCoalition parameters self o run
    (fun i _ => present i) opening accepted

/-- The canonical source caller retains the common keys of its actual setup. -/
theorem source_shared (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : ℕ) (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims noCoalition A x z))
    (c : (TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x j Z step p).β) :
    SharedPrss ((TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x j Z step p).boundary c).batch.ctx := by
  have contexts := funext (TreeCheckWalkRecipe.sourceWalk_context prims K noCoalition A
    circuits settings top tree x j Z step p c)
  rw [contexts]
  exact saltSetup_shared_default prims A x z p hp (fun _ => ⟨fun _ => 0, fun _ => 0⟩)


/-- A live cut has present rows for all honest operators, including operators
that abort in its later continuation. -/
theorem live_present (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A) (c : W.β) (o : TreeCheckTailCheckpoint A)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings
      top tree D A x z j (.inl (c, o))) :
    ∀ i, i ∉ D.1 → (o.1.2 i).isSome := by
  obtain ⟨r, hr, bad, _⟩ := live
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, hout, _⟩ := bad.2
  exact treeCheckBatch_live prims K circuits D A Z (W.boundary c).batch o r hr
    ⟨i, (value, records), hout⟩

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
/-- The concrete source has no all-honest live checkpoint linked to its actual
indexed wrong opening. -/
theorem source_not_live_empty (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (index : Fin (treeBatches settings tree))
    (step : ℕ) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs noCoalition x)
    (hp : p ∈ support (treeSaltSetup prims noCoalition A x z))
    (opening : (TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x
      index.val Z step p).IndexedOpening prims K circuits settings top tree noCoalition A x z Z index)
    (c : (TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x
      index.val Z step p).β) (o : TreeCheckTailCheckpoint A)
    (hs : (.inl (c, o) : ((TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings
      top tree x index.val Z step p).cut prims K circuits settings noCoalition Z).σ) ∈ support
      ((TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x
        index.val Z step p).cut prims K circuits settings noCoalition Z).pre) :
    ¬ ((TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x
      index.val Z step p).cut prims K circuits settings noCoalition Z).Live prims K circuits settings
        top tree noCoalition A x z index (.inl (c, o)) := by
  let W := TreeCheckWalkRecipe.sourceWalk prims K noCoalition A circuits settings top tree x index.val Z step p
  intro live
  have parameters := (TreeCheckWalkRecipe.sourceWalk_split prims K noCoalition A circuits settings
    top tree x index.val Z step z p dealt hp).2 c
  have shared := source_shared prims K circuits settings top tree A x z index.val Z step p hp c
  have present := live_present prims K circuits settings top tree noCoalition A x z Z index W c o live
  have indexedOpening := W.opening_of_indexed prims K circuits settings top tree noCoalition A x z Z index opening
  unfold TreeCheckTailWalk.Opening at indexedOpening
  have opened : Nonempty (TreeCheckOpeningAt prims K circuits noCoalition A (W.boundary c).batch o) := by
    with_reducible
      exact indexedOpening c o hs live
  obtain ⟨proof⟩ := opened
  exact tail_no_wrong_opening prims K circuits settings A (W.boundary c) parameters shared o
    (by with_reducible exact TreeCheckTailWalk.mem_support_cut_pre (W := W) (D := noCoalition) (Z := Z) hs)
    (fun i => present i (by simp)) proof

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
/-- A live checkpoint of the fixed source with indexed opening provenance
has an actual corrupt participant. -/
theorem source_live_corrupt (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (index : Fin (treeBatches settings tree))
    (step : ℕ) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (hp : p ∈ support (treeSaltSetup prims D A x z))
    (opening : (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x
      index.val Z step p).IndexedOpening prims K circuits settings top tree D A x z Z index)
    (c : (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x index.val Z step p).β)
    (o : TreeCheckTailCheckpoint A)
    (hs : (.inl (c, o) : ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x
      index.val Z step p).cut prims K circuits settings D Z).σ) ∈ support
      ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x
        index.val Z step p).cut prims K circuits settings D Z).pre)
    (live : ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x
      index.val Z step p).cut prims K circuits settings D Z).Live prims K circuits settings
        top tree D A x z index (.inl (c, o))) : ∃ i, i ∈ D.1 := by
  by_contra empty
  obtain rfl := eq_noCoalition D empty
  have rejected := source_not_live_empty prims K circuits settings top tree A x z Z index step p dealt hp
  unfold Not at rejected
  with_reducible exact rejected opening c o hs live

/-- The numerical source position, without a separate corrupt-party premise. -/
def PrefixPositions (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) : Prop :=
  TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ bounded j _ W =>
    ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
        (.inl (c, o)) →
      Nonempty (TreeCheckPrefixPosition prims circuits settings D A x z Z
        (TreeCheckQueryBudget.ofBound bounded) ((W.cut prims K circuits settings D Z).count (.inl (c, o))) o)

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
/-- Indexed opening provenance supplies the corrupt-party half of the original
position clause for this same fixed source family. -/
theorem walkPositions_of_opening_positions (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (opening : TreeCheckWalkRecipe.WalkOpening prims K circuits settings)
    (positions : PrefixPositions prims K circuits settings) :
    TreeCheckWalkRecipe.WalkPositions prims K circuits settings := by
  dsimp only [PrefixPositions, TreeCheckWalkRecipe.WalkOpening, TreeCheckWalkRecipe.AtWalk] at positions opening
  intro hb top tree D A x z Z q dealt bounded small j p hp c o hs live
  constructor
  · with_reducible
      exact source_live_corrupt prims K circuits settings top tree D A x z Z j
        (TreeCheckQueryBudget.ofBound bounded).step p dealt hp
        (opening hb top tree D A x z Z q dealt bounded small j p hp) c o hs live
  · with_reducible
      exact positions hb top tree D A x z Z q dealt bounded small j p hp c o hs live


/-- Original source construction with numerical prefix positions only;
opening provenance also supplies the nonempty-coalition clause. -/
theorem sourceConstruction (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (bad : TreeCheckWalkRecipe.WalkBad prims K circuits settings)
    (opening : TreeCheckWalkRecipe.WalkOpening prims K circuits settings)
    (positions : PrefixPositions prims K circuits settings)
    (hybrid : TreeCheckWalkRecipe.WalkHybrid prims K circuits settings) :
    TreeCheckTailWalkSourceConstruction prims K circuits settings :=
  TreeCheckWalkRecipe.sourceConstruction_of_fields prims K circuits settings bad opening
    (walkPositions_of_opening_positions prims K circuits settings opening positions) hybrid

end ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.localPrelude_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.localPrelude_erase

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.tail_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.tail_saved

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.tail_no_wrong_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.tail_no_wrong_opening

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.source_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.source_shared

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.source_not_live_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.source_not_live_empty

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.source_live_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.source_live_corrupt

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.walkPositions_of_opening_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.walkPositions_of_opening_positions

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.sourceConstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestLinks.sourceConstruction
