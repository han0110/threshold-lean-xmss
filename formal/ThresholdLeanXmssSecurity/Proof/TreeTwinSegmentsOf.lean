import ThresholdLeanXmssSecurity.Proof.TreeEvents4

/-!
# The segment route with a general check flag

The definitions of this file are the definitions of `TreeTwin3.lean` and `TreeTwinSegments.lean` with
the bad event `TreeSimBadOf Wrong` in the place of `TreeSimBad3`.

* `CheckFlag.Covers` says that a wrong output of an honest operator gives the hash event or the
  check flag.
* `segStepAtOf_of_segStepAt` moves a step with the events `treeSimEvents3` to the events of a check
  flag that covers the wrong output.
* `treeSimFinishOf_of_segments` assembles the padded suffix from the segments, as
  `treeSimFinish_of_segments` does.
* `ceremonyCoupling_of_segmentsOf` gives the ceremony coupling of a monotone check flag that covers
  the wrong output, from the segment core of the same flag. It follows
  `treeSimCeremonyGoal3_of_segments`. On a bad prefix the flags hold on each real outcome, because
  each real outcome extends the prefix log.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeTwinSegmentsOf

open ThresholdLeanXmssSecurity ThresholdLeanXmssSecurity.TreeTwinSegment
  ThresholdLeanXmssSecurity.TreeEvents4

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A wrong output of an honest operator gives the hash event or the check flag. -/
def _root_.ThresholdLeanXmssSecurity.TreeEvents4.CheckFlag.Covers (Wrong : CheckFlag C E) : Prop :=
  ∀ top tree D (A : Adversary C E (Keys C) PEmpty PEmpty) x z (log : TreeSimLog C),
    TreeSimWrongOutput prims K circuits settings top tree D A x z log →
      TreeSimBadOf Wrong top tree D A x z log

/-- A check flag that covers the wrong output has the sticky predicate of `TreeSimBad`. -/
theorem treeSimBadOf_of_bad (Wrong : CheckFlag C E) (covers : Wrong.Covers prims K circuits settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (log : TreeSimLog C)
    (bad : TreeSimBad prims K circuits settings top tree D A x z log) :
    TreeSimBadOf Wrong top tree D A x z log := by
  rcases bad with hash | wrong
  · exact Or.inl (Or.inl (Or.inl hash))
  · exact covers top tree D A x z log wrong

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Bad : TreeSimLog C → Prop)
  (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop)

/-- `TreeTwinEntry3` with the bad event `Bad`. -/
def TwinEntryOf : Prop :=
  ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => Bad a.2.2 ∨ ∃ δ, Req 0 δ ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))

/-- `SegStepAt` with the bad event `Bad`. -/
def SegStepAtOf (k n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  n + k + 3 ≤ ceremonyFuel circuits settings ∧
  RelTriple
    ((executeSteps (treeSimRealRoles prims D) D A noFunctionality k a.1.1 a.1.2).run a.2)
    ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality k b.1.1 b.1.2).run b.2)
    (fun u v => Bad u.2.2 ∨ twinR D A Req (n + k) u v)

/-- `TreeTwinSegStep` with the bad event `Bad`. -/
def TwinSegStepOf : Prop :=
  ∀ n (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ Bad a.2.2 → ¬ AllDone D a.1.2 → twinR D A Req n a b →
    ∃ k, 0 < k ∧ SegStepAtOf prims circuits settings D A Bad Req k n a b

end Fields

/-- `TreeTwinSegCoreGoal3` with the bad event of the check flag `Wrong`. -/
def SegCoreGoalOf (Wrong : CheckFlag C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop,
    TwinEntryOf prims K circuits settings top tree D A parameter seeds pairs p r
      (TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z) (treeTwinReq D Stage) ∧
    TwinSegStepOf prims K circuits settings top tree D A parameter seeds pairs p r
      (TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z) (treeTwinReq D Stage)

/-- A proved step with the events `treeSimEvents3` is a step with the events of a check flag that
covers the wrong output. -/
theorem segStepAtOf_of_segStepAt (Wrong : CheckFlag C E)
    (covers : Wrong.Covers prims K circuits settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (k n : ℕ) (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (step : SegStepAt prims K circuits settings top tree D A parameter seeds pairs z Req k n a b) :
    SegStepAtOf prims circuits settings D A
      (TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z) Req k n a b := by
  refine ⟨step.1, relTriple_post_mono step.2 ?_⟩
  rintro u v (bad | rel)
  · rcases bad with hash | wrong
    · exact Or.inl (Or.inl hash)
    · exact Or.inl (covers top tree D A _ z u.2.2 wrong)
  · exact Or.inr rel

set_option backward.isDefEq.respectTransparency false in
/-- The full padded suffix from positive bounded segments of the actual runs, with the events of a
monotone check flag that covers the wrong output. -/
theorem treeSimFinishOf_of_segments (Wrong : CheckFlag C E) (mono : Wrong.Monotone)
    (covers : Wrong.Covers prims K circuits settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C)
    (Z : Distinguisher C A.State TreeOutput)
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (entry : TwinEntryOf prims K circuits settings top tree D A parameter seeds pairs p r
      (TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z) (treeTwinReq D Stage))
    (next : TwinSegStepOf prims K circuits settings top tree D A parameter seeds pairs p r
      (TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z) (treeTwinReq D Stage)) :
    RelTriple (treeSimRealFinish prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) Z p.2.1 ((r.2, p.2.2.1.2), p.2.2.2))
      ((treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1).run' r.2)
      (fun a b =>
        let flags := treeSimEventsOf Wrong top tree D A (dealtKeys parameter seeds pairs) z Z a.2
        (flags.1 = true ∨ flags.2 = true) ∨ (a.1 = true ↔ b = true)) := by
  let Bad : TreeSimState C → Prop := fun s =>
    TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z s.2
  let R : ℕ → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop := fun n a b =>
    n + 3 ≤ ceremonyFuel circuits settings ∧
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a ∧ twinR D A (treeTwinReq D Stage) n a b
  have sticky : ∀ st steps s, Bad s →
      ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality st steps).run s),
      Bad u.2 :=
    treeSim_round_bad prims D A Bad (fun _ _ h =>
      treeSimBadOf_mono Wrong mono top tree D A _ z h)
  have done : ∀ n a b, R n a b → ¬ Bad a.2 → (AllDone D a.1.2 ↔ AllDone D b.1.2) := by
    rintro n a b ⟨_, _, swaps, δ, salts, req⟩ _
    exact req.2.2.1
  have output : ∀ n a b, R n a b → ¬ Bad a.2 →
      TreeStagesSwapFinal D A p.1.1
        ((a.1.1, fun i => (a.1.2 i).output), a.2)
        ((b.1.1, fun i => (b.1.2 i).output), b.2) := by
    rintro n a b ⟨bound, reach, swaps, δ, salts, req⟩ good
    refine ⟨req.2.1, ?_, Or.inr ⟨swaps, δ, salts, req.1.1.symm, req.1.2⟩⟩
    exact treeStages_outputs_of_replay prims K circuits settings top tree D A parameter seeds pairs z p.1
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      (treeStages_reach_outputWitness prims K circuits settings top tree D A parameter seeds pairs z
        p hp padding r hr n bound a reach)
      (fun h => good (treeSimBadOf_of_bad prims K circuits settings Wrong covers top tree D A _ z _ h))
      (treeStages_reach_corrupt prims K circuits settings top tree D A _ _ _ n a reach) req.2.2.2.1
  have segment : ∀ n a b, n < ceremonyFuel circuits settings - 3 → R n a b →
      ¬ Bad a.2 → ¬ AllDone D a.1.2 → ∃ k, 0 < k ∧ n + k ≤ ceremonyFuel circuits settings - 3 ∧
      RelTriple
        ((executeSteps (treeSimRealRoles prims D) D A noFunctionality k a.1.1 a.1.2).run a.2)
        ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality k b.1.1 b.1.2).run b.2)
        (fun u v => Bad u.2 ∨ R (n + k) u v) := by
    rintro n a b _ ⟨bound, reach, req⟩ good active
    obtain ⟨k, positive, margin, step⟩ := next n a b reach bound good active req
    refine ⟨k, positive, by omega, ?_⟩
    apply relTriple_post_mono (treeSim_relTriple_support step)
    rintro u v ⟨bad | rel, hu, hv⟩
    · exact Or.inl bad
    · exact Or.inr ⟨margin,
        treeStages_reach_segment prims K circuits settings top tree D A parameter seeds pairs p r
          n k a u reach hu, rel⟩
  rw [treeSimRealFinish_rounds, treeSimIdealFinish_rounds]
  apply relTriple_bind (R := fun a b => Bad a.2 ∨ TreeStagesSwapFinal D A p.1.1 a b)
  · have real : (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree) =
        (fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs) i) :=
      funext (treeSim_real_cont K circuits settings top tree (dealtKeys parameter seeds pairs))
    have ideal : treeSimProgram K circuits settings D parameter
        (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2 top tree =
        (fun i => prssSetup i >>= treeSimIdealCont K circuits settings top tree D parameter
          (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2 i) :=
      funext (treeSim_ideal_cont K circuits settings top tree D parameter
        (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2)
    have hidden := treeSimCommonPrefix_hidden prims circuits settings top tree D A parameter seeds pairs z p hp
    have fuel : ceremonyFuel circuits settings = (ceremonyFuel circuits settings - 3) + 3 := by
      unfold ceremonyFuel setupRounds
      omega
    rw [real, ideal, ← hidden, fuel]
    apply treeSim_prssSetup_continuations prims D A p.2.1 _ _ _ _
      (fun a b => Bad a.2 ∨ R 0 a b)
    · intro u hu
      apply relTriple_post_mono (treeSim_relTriple_support (entry u hu))
      rintro a b ⟨bad | ⟨δ, req⟩, ha, hb⟩
      · exact Or.inl bad
      · refine Or.inr ⟨?_, ?_, [], δ, fun x hx => by simp at hx, req⟩
        · unfold ceremonyFuel setupRounds
          omega
        · exact treeStages_reach_entry prims K circuits settings top tree D A _ _ _ u hu a ha
    · intro a b hab
      simpa only [Nat.sub_zero] using
        relTriple_executeRounds_segments (treeSimRealRoles prims D) (treeSimIdealRoles prims D)
          D D A A noFunctionality noFunctionality Bad R (TreeStagesSwapFinal D A p.1.1)
          (ceremonyFuel circuits settings - 3) sticky done output segment
          (ceremonyFuel circuits settings - 3) 0 (Nat.sub_zero _) (Nat.zero_le _) a b hab
  · intro a b hab
    rcases hab with bad | rel
    · apply relTriple_of_support_left
      intro x hx _
      apply Or.inl
      apply (treeSimEventsOf_bad Wrong top tree D A _ z Z x.2).mpr
      exact treeSimBadOf_mono Wrong mono top tree D A _ z
        (treeSim_observe_prefix prims D A Z a x hx) bad
    · apply relTriple_post_mono (treeStages_observe_swapFinal prims D A Z p.1.1 a b rel)
      rintro x y (bad | eq)
      · exact Or.inl (Or.inl (by simp [treeSimEventsOf, TreeSimHashBad3, TreeSimHashBad2, bad]))
      · exact Or.inr (by rw [eq])

/-- The ceremony coupling of a check flag from the segment core of the same flag. -/
theorem ceremonyCoupling_of_segmentsOf (Wrong : CheckFlag C E)
    (mono : Wrong.Monotone) (covers : Wrong.Covers prims K circuits settings)
    (core : SegCoreGoalOf prims K circuits settings Wrong) :
    TreeSimCeremonyCoupling prims K circuits settings (treeSimEventsOf Wrong) := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  by_cases bad : TreeSimBadOf Wrong top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2
  · apply relTriple_of_support_left
    intro x hx _
    unfold treeSimRealFinish at hx
    rw [support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply Or.inl
    apply (treeSimEventsOf_bad Wrong top tree D A _ z Z _).mpr
    exact treeSimBadOf_mono Wrong mono top tree D A _ z
      (treeSimLoggedWorld_prefix prims D _ p.2.2 y hy) bad
  · obtain ⟨padding, hpadding⟩ := core hb top tree D A parameter seeds pairs z Z q hq hsmall p hp bad
    apply relTriple_of_evalDist_eq_left
      (treeSimRealFinish_padding prims K circuits settings top tree D A
        (dealtKeys parameter seeds pairs) Z p.2.1 p.2.2 padding).symm
    apply relTriple_of_evalDist_eq_right
      (treeSimIdealFinish_padding prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1 p.2.2.1.1 padding)
    apply relTriple_bind (treeSim_relTriple_support (relTriple_refl _))
    rintro r _ ⟨rfl, hr, _⟩
    obtain ⟨Stage, entry, next⟩ := hpadding r hr
    exact treeSimFinishOf_of_segments prims K circuits settings Wrong mono covers top tree D A
      parameter seeds pairs z p r Z hp padding hr Stage entry next

end ThresholdLeanXmssSecurity.TreeTwinSegmentsOf

open ThresholdLeanXmssSecurity.TreeTwinSegmentsOf

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegmentsOf.treeSimBadOf_of_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimBadOf_of_bad

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegmentsOf.segStepAtOf_of_segStepAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segStepAtOf_of_segStepAt

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegmentsOf.treeSimFinishOf_of_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimFinishOf_of_segments

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegmentsOf.ceremonyCoupling_of_segmentsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyCoupling_of_segmentsOf
