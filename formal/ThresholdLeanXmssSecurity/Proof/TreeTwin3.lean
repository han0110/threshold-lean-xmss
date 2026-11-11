import ThresholdLeanXmssSecurity.Proof.TreeEvents3
import ThresholdLeanXmssSecurity.Proof.TreeTwinFields

/-!
# The twin relation with the budget collision

`TreeStagesRelation.lean` and `TreeTwinFields.lean` reduce `TreeSimStagesGoal2` to a twin relation
whose guard is `¬ TreeSimBad2`. This file copies that reduction to `TreeSimBad3`, the sticky
predicate of `treeSimEvents3`. Then the field `freeHit` has the guard `¬ TreeSimBad3`, and the
lockstep link `treeTwinDigestGoal3_of_lockstep` applies with no extra hypothesis.

* `treeStages_roundStages_of_reachable_relation3` is `treeStages_roundStages_of_reachable_relation2`
  with `TreeSimBad3`. The events2 version does not transfer by monotonicity. It needs its
  hypotheses under `¬ TreeSimBad2`, and a relation with `TreeSimBad3` gives them only under the
  stronger guard `¬ TreeSimBad3`.
* `treeSimStagesGoal3_of_relation` and `treeSimStagesGoal3_of_twinRelation` are the copies of the
  two assemblies. The target is `treeSimStagesGoal3_of_twinRelation`.
* `treeTwinStageCoreGoal3_of_core` moves the events2 fields `entry` and `next` to the new guard by
  monotonicity.
* `treeSimStagesGoal3_of_lockstep` gives `TreeSimStagesGoal3` from the lockstep goals and the
  fields `entry` and `next`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The core of `treeStages_badCore2` for `TreeSimBad3`. -/
def treeStages_badCore3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (bad : TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z s.2) :
    TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z dealt state s
      (fun t => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2) where
  Inv _ _ := False
  stage _ := .ceremony
  entry p hp := by
    have hpref : s.2 <+: p.2.2 := by
      apply treeSimLoggedWorld_prefix prims D
        (executePhase worldRoles D A noFunctionality 3 state
          (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))) s p
      simpa only [simulateQ_executePhase, treeSimRealRoles] using hp
    apply relTriple_of_support_left
    intro a ha b
    apply Or.inl
    exact treeSimBad3_mono prims K circuits settings top tree D A _ z
      (hpref.trans (treeSimLoggedWorld_prefix prims D _ p.2 a ha)) bad
  noSetup _ _ h := h.elim
  done _ _ h := h.elim
  outputEvidence _ _ h := h.elim
  peerBoundary _ _ _ h := h.elim
  collectorBoundary _ _ _ h := h.elim
  collectorNextBoundary _ _ _ h := h.elim
  rerandBoundary _ _ _ h := h.elim
  coinBoundary _ _ _ h := h.elim
  extendMultBoundary _ _ _ h := h.elim
  checkBoundary _ _ _ h := h.elim
  openingBoundary _ _ _ h := h.elim
  emptyOpeningBoundary _ _ _ h := h.elim
  ceremony _ _ _ h := h.elim

/-- The stages of `treeSimEvents3` from a round-indexed relation on reachable real
configurations, as `treeStages_roundStages_of_reachable_relation2` with `TreeSimBad3`. -/
def treeStages_roundStages_of_reachable_relation3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (R : ℕ → TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
      RelTriple
        ((simulateQ (treeSimLoggedWorld prims D)
          (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
        ((simulateQ (streamWorld prims D)
          (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
            (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
        (fun a b => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
          R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2)))
    (agree : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      a.1.1 = b.1.1 ∧ TreeStagesSwapCache D a.2 b.2 ∧
      (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
      (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome))
    (progress : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings)
    (next : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 →
      RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
        (fun u v => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
          R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))) :
    TreeSimRoundStages prims K circuits settings (treeSimEvents3 prims K circuits settings)
      top tree D A parameter seeds pairs z Z p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) where
  Bad t := TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2
  Inv a b := ∃ n, n + 3 ≤ ceremonyFuel circuits settings ∧
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a ∧ R n a b
  stage _ := .ceremony
  Q := TreeStagesSwapFinal D A p.1.1
  entry u hu := by
    apply relTriple_post_mono (treeSim_relTriple_support (entry u hu))
    intro a b hab
    rcases hab.1 with bad | rel
    · exact Or.inl bad
    · refine Or.inr ⟨0, ?_, ?_, rel⟩
      · unfold ceremonyFuel setupRounds
        omega
      · exact treeStages_reach_entry prims K circuits settings top tree D A _ _ _ u hu a hab.2.1
  noSetup _ _ _ _ := by intro h; cases h
  badPersistent _ _ hp := treeSimBad3_mono prims K circuits settings top tree D A _ z hp
  done a b hab good := by
    obtain ⟨n, _, reach, rel⟩ := hab
    exact (agree n a b rel reach good).2.2.1
  output a b hab good := by
    obtain ⟨n, bound, reach, rel⟩ := hab
    obtain ⟨state, cache, _, success⟩ := agree n a b rel reach good
    refine ⟨state, ?_, cache⟩
    exact treeStages_outputs_of_replay prims K circuits settings top tree D A parameter seeds pairs z p.1
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      (treeStages_reach_outputWitness prims K circuits settings top tree D A parameter seeds pairs z
        p hp padding r hr n bound a reach)
      (fun h => good (treeSimBad3_of_bad prims K circuits settings top tree D A _ z _ h))
      (treeStages_reach_corrupt prims K circuits settings top tree D A _ _ _ n a reach) success
  peerBoundary _ _ h := by cases h
  collectorBoundary _ _ h := by cases h
  collectorNextBoundary _ _ h := by cases h
  rerandBoundary _ _ h := by cases h
  coinBoundary _ _ h := by cases h
  extendMultBoundary _ _ h := by cases h
  checkBoundary _ _ h := by cases h
  openingBoundary _ _ h := by cases h
  emptyOpeningBoundary _ _ h := by cases h
  ceremony a b _ hab good active := by
    obtain ⟨n, bound, reach, rel⟩ := hab
    apply relTriple_post_mono (treeSim_relTriple_support (next n a b rel reach bound good active))
    intro u v huv
    rcases huv.1 with bad | rel'
    · exact Or.inl bad
    · exact Or.inr ⟨n + 1, progress n a b rel reach bound good active,
        treeStages_reach_step prims K circuits settings top tree D A _ _ _ n a reach active u huv.2.1, rel'⟩
  observeGood a b hab := by
    apply relTriple_post_mono (treeStages_observe_swapFinal prims D A Z p.1.1 a b hab)
    intro x y hx
    rcases hx with bad | eq
    · exact Or.inl (Or.inl (by simp [treeSimEvents3, TreeSimHashBad3, TreeSimHashBad2, bad]))
    · exact Or.inr (by rw [eq])
  badRecorded t ht := (treeSimEvents3_bad prims K circuits settings top tree D A _ z Z t.2).mpr ht

/-- `TreeStagesRelation2` with `TreeSimBad3`. It drives
`treeStages_roundStages_of_reachable_relation3`. -/
structure TreeStagesRelation3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) where
  R : ℕ → TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop
  entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))
  agree : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    a.1.1 = b.1.1 ∧ TreeStagesSwapCache D a.2 b.2 ∧
    (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome)
  progress : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings
  next : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun u v => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
    R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))

/-- `TreeSimStagesRelationGoal2` with `TreeSimBad3`. -/
def TreeSimStagesRelationGoal3 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    Nonempty (TreeStagesRelation3 prims K circuits settings top tree D A parameter seeds pairs z p r)

/-- The stages of `treeSimEvents3` from the good-prefix relation. Bad prefixes use
`treeStages_badCore3`. -/
theorem treeSimStagesGoal3_of_relation (relation : TreeSimStagesRelationGoal3 prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  by_cases bad : TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2
  · refine ⟨pure (), fun r hr => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨treeSimRoundCore_stages3 prims K circuits settings top tree D A parameter seeds pairs z Z
      p.1 p.2.1 _ (treeStages_badCore3 prims K circuits settings top tree D A parameter seeds pairs z
        p.1 p.2.1 p.2.2 bad)⟩
  · obtain ⟨padding, hpadding⟩ := relation hb top tree D A parameter seeds pairs z Z q hq hsmall p hp bad
    refine ⟨padding, fun r hr => ?_⟩
    obtain ⟨rel⟩ := hpadding r hr
    exact ⟨treeStages_roundStages_of_reachable_relation3 prims K circuits settings top tree D A
      parameter seeds pairs z Z p hp padding r hr rel.R rel.entry rel.agree rel.progress rel.next⟩

/-- `TreeStagesTwinRelation` with `TreeSimBad3`. -/
structure TreeStagesTwinRelation3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) where
  Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop
  stream : ∀ n δ a b, Req n δ a b → TreeSimStreamRel δ a.2 b.2
  entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    ∃ δ, Req 0 δ ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))
  agree : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    a.1.1 = b.1.1 ∧ (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome)
  progress : ∀ n a,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings
  freeHit : TreeTwinFreeHit3 prims K circuits settings top tree D A parameter seeds pairs z p r Req
  next : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
    ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
    Req (n + 1) δ' ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))

/-- The relation of the stages, as `TreeStagesTwinRelation.R`. -/
def TreeStagesTwinRelation3.R {top : TopTree} {tree : Tree} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {parameter : PublicParameter}
    {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput} {z : Aux}
    {p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C)}
    {r : Unit × HashCache C}
    (twin : TreeStagesTwinRelation3 prims K circuits settings top tree D A parameter seeds pairs z p r)
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) :
    Prop :=
  ∃ swaps δ, (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) ∧ twin.Req n δ (a.1, treeStagesTwin swaps a.2) b

/-- The relation of the stages from the equal-cache relation of the twins, as
`treeStages_relation_of_twin`. -/
def treeStages_relation_of_twin3 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C)
    (twin : TreeStagesTwinRelation3 prims K circuits settings top tree D A parameter seeds pairs z p r) :
    TreeStagesRelation3 prims K circuits settings top tree D A parameter seeds pairs z p r where
  R := twin.R
  entry u hu := by
    apply relTriple_post_mono (twin.entry u hu)
    rintro a b (bad | ⟨δ, req⟩)
    · exact Or.inl bad
    · exact Or.inr ⟨[], δ, fun x hx => by simp at hx, req⟩
  agree n a b rel reach good := by
    obtain ⟨swaps, δ, salts, req⟩ := rel
    obtain ⟨state, done, outputs⟩ := twin.agree n δ swaps a b reach good req
    obtain ⟨cache, hidden⟩ := twin.stream n δ _ b req
    exact ⟨state, Or.inr ⟨swaps, δ, salts, cache.symm, hidden⟩, done, outputs⟩
  progress n a _ _ reach bound good active := twin.progress n a reach bound good active
  next n a b rel reach bound good active := by
    obtain ⟨swaps, δ, salts, req⟩ := rel
    have real := treeSim_relTriple_support
      (treeStages_round_twin prims D A swaps a.1.1 a.1.2 a.2 salts)
    have real' := relTriple_post_mono real (R' := fun u v => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
        (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)) (by
      rintro u v ⟨(guess | hit) | good', hu, _⟩
      · exact Or.inl (treeSimBad3_of_bad2 prims K circuits settings top tree D A _ z _
          (Or.inl (Or.inl (Or.inr guess))))
      · exact Or.inl (twin.freeHit n δ swaps a b reach good salts req u hu hit)
      · exact Or.inr good')
    apply relTriple_post_mono (treeSim_relTriple_support (treeStages_twin_transfer swaps _ _ real'
      (twin.next n δ swaps a b reach bound good active salts req)))
    rintro u w ⟨(bad | bad | ⟨extra, δ', salts', req'⟩), hu, _⟩
    · exact Or.inl bad
    · exact Or.inl bad
    · have hpref : a.2.2 <+: u.2.2 := by
        apply treeSimLoggedWorld_prefix prims D (stepRound worldRoles D A noFunctionality a.1.1 a.1.2) a.2 u
        simpa only [simulateQ_stepRound, treeSimRealRoles] using hu
      refine Or.inr ⟨extra ++ swaps, δ', ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact salts' x hx
        · exact treeStages_hiddenSalt_mono D x.1 hpref (salts x hx)
      · rw [← treeStagesTwin_append]
        exact req'

/-- `TreeSimStagesTwinRelationGoal` with `TreeSimBad3`. -/
def TreeSimStagesTwinRelationGoal3 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    Nonempty (TreeStagesTwinRelation3 prims K circuits settings top tree D A parameter seeds pairs z p r)

/-- The target of this file. -/
theorem treeSimStagesGoal3_of_twinRelation
    (twin : TreeSimStagesTwinRelationGoal3 prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings := by
  apply treeSimStagesGoal3_of_relation
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := twin hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨rel⟩ := hpadding r hr
  exact ⟨treeStages_relation_of_twin3 prims K circuits settings top tree D A parameter seeds pairs z p r rel⟩

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop)

/-- The field `entry` of `TreeStagesTwinRelation3`. -/
def TreeTwinEntry3 : Prop :=
  ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    ∃ δ, Req 0 δ ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))

/-- The field `next` of `TreeStagesTwinRelation3`. -/
def TreeTwinNext3 : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
    ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
    Req (n + 1) δ' ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))

/-- The events2 field `entry` gives the field with `TreeSimBad3`. -/
theorem treeTwinEntry3_of_entry
    (entry : TreeTwinEntry prims K circuits settings top tree D A parameter seeds pairs z p r Req) :
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r Req :=
  fun u hu => relTriple_post_mono (entry u hu) (fun a _ h =>
    h.imp_left (treeSimBad3_of_bad2 prims K circuits settings top tree D A _ z a.2.2))

/-- The events2 field `next` gives the field with `TreeSimBad3`. The guard `¬ TreeSimBad3` implies
`¬ TreeSimBad2`. -/
theorem treeTwinNext3_of_next
    (next : TreeTwinNext prims K circuits settings top tree D A parameter seeds pairs z p r Req) :
    TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r Req :=
  fun n δ swaps a b reach bound good active salts req =>
    relTriple_post_mono
      (next n δ swaps a b reach bound
        (fun h => good (treeSimBad3_of_bad2 prims K circuits settings top tree D A _ z _ h))
        active salts req)
      (fun v _ h => h.imp_left (treeSimBad3_of_bad2 prims K circuits settings top tree D A _ z v.2.2))

end Fields

/-- `TreeTwinStageGoal` with `TreeSimBad3`. -/
def TreeTwinStageGoal3 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop,
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinFreeHit3 prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage)

/-- `TreeTwinStageGoal3` without the field `freeHit`. -/
def TreeTwinStageCoreGoal3 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop,
    TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinNext3 prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage)

/-- The events2 core goal gives the core goal with `TreeSimBad3`. -/
theorem treeTwinStageCoreGoal3_of_core
    (core : TreeTwinStageCoreGoal prims K circuits settings) :
    TreeTwinStageCoreGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := core hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
    (fun h => good (treeSimBad3_of_bad2 prims K circuits settings top tree D A _ z _ h))
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Stage, entry, next⟩ := hpadding r hr
  exact ⟨Stage, treeTwinEntry3_of_entry prims K circuits settings top tree D A parameter seeds pairs z p r _ entry,
    treeTwinNext3_of_next prims K circuits settings top tree D A parameter seeds pairs z p r _ next⟩

/-- The field `freeHit` of every stage relation from the program fact, as
`treeTwinStageGoal_of_digest`. -/
theorem treeTwinStageGoal3_of_digest
    (digest : TreeTwinDigestGoal3 prims K circuits settings)
    (core : TreeTwinStageCoreGoal3 prims K circuits settings) :
    TreeTwinStageGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := core hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Stage, entry, next⟩ := hpadding r hr
  exact ⟨Stage, entry, treeTwin_freeHit3 prims K circuits settings top tree D A parameter seeds pairs z p r _
    (digest hb top tree D A parameter seeds pairs z p hp padding r hr), next⟩

/-- The twin relation from the stage part. The fields `stream`, `agree` and `progress` are
proved here, as in `treeSimStagesTwinRelationGoal_of_fields`. -/
theorem treeSimStagesTwinRelationGoal3_of_fields
    (stage : TreeTwinStageGoal3 prims K circuits settings) :
    TreeSimStagesTwinRelationGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := stage hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Stage, entry, freeHit, next⟩ := hpadding r hr
  exact ⟨{
    Req := treeTwinReq D Stage
    stream := fun _ _ _ _ req => req.1
    entry := entry
    agree := fun _ _ _ _ _ _ _ req => ⟨req.2.1, req.2.2.1, req.2.2.2.1⟩
    progress := fun n a reach _ _ active =>
      treeTwin_progress prims K circuits settings top tree D A _ _ _ n a reach active
    freeHit := freeHit
    next := next }⟩

/-- `TreeSimStagesGoal3` from the stage part. -/
theorem treeSimStagesGoal3_of_twinFields
    (stage : TreeTwinStageGoal3 prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_twinRelation prims K circuits settings
    (treeSimStagesTwinRelationGoal3_of_fields prims K circuits settings stage)

/-- `TreeSimStagesGoal3` from the lockstep goals and the fields `entry` and `next`. The lockstep
gives the field `freeHit` through `treeTwinDigestGoal3_of_lockstep`. -/
theorem treeSimStagesGoal3_of_lockstep
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings)
    (core : TreeTwinStageCoreGoal3 prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_twinFields prims K circuits settings
    (treeTwinStageGoal3_of_digest prims K circuits settings
      (treeTwinDigestGoal3_of_lockstep prims K circuits settings lockstep draws) core)

/-- `treeSimStagesGoal3_of_lockstep` with the events2 fields `entry` and `next`. -/
theorem treeSimStagesGoal3_of_lockstep_core2
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings)
    (core : TreeTwinStageCoreGoal prims K circuits settings) :
    TreeSimStagesGoal3 prims K circuits settings :=
  treeSimStagesGoal3_of_lockstep prims K circuits settings lockstep draws
    (treeTwinStageCoreGoal3_of_core prims K circuits settings core)

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_relation

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_twinRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_twinRelation

/-- info: 'ThresholdLeanXmssSecurity.treeTwinStageCoreGoal3_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinStageCoreGoal3_of_core

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_twinFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_twinFields

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_lockstep

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal3_of_lockstep_core2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal3_of_lockstep_core2

end ThresholdLeanXmssSecurity
