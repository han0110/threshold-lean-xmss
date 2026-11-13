import ThresholdLeanXmssSecurity.Proof.TreeTwinSegments
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltFinal
import ThresholdLeanXmssSecurity.Proof.TreeSaltLiteralTransport
import ThresholdLeanXmssSecurity.Proof.LifetimeSaltGuarded

/-!
# The tree simulation events with a general check flag

The check flag of `treeSimEvents3` is `TreeSimWrongOutput`. This file states the events for a check
flag `Wrong` on the log. The hash flag does not change, so the hash goal of `treeSimEvents3` stays
valid for each check flag.

* `hashBoundGoal3` is the hash goal of `treeSimEvents3` with no premise.
* `treeSimHashBound_of_goal3` moves the hash goal to the events `treeSimEventsOf Wrong`.
* `treeSimulationHop_of_wrong` gives the hop from the ceremony coupling and the check bound of the
  events `treeSimEventsOf Wrong`.
* `treeSimBadOf_mono` says that `TreeSimBadOf Wrong` only grows with the log when `Wrong` does.
* `treeSimEventsOf_bad` says that the two flags of `treeSimEventsOf Wrong` are `TreeSimBadOf Wrong`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeEvents4

open ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A check flag on the log of one real run. -/
abbrev CheckFlag (C : Committee) (E : Type) :=
  TopTree → Tree → C.Coalition → (A : Adversary C E (Keys C) PEmpty PEmpty) →
    (C.Party → Keys C) → Aux → TreeSimLog C → Prop

/-- The check flag only grows with the log. -/
def CheckFlag.Monotone (Wrong : CheckFlag C E) : Prop :=
  ∀ top tree D A x z (a b : TreeSimLog C), a <+: b → Wrong top tree D A x z a → Wrong top tree D A x z b

/-- The events with the hash flag of `treeSimEvents3` and the check flag `Wrong`. -/
def treeSimEventsOf (Wrong : CheckFlag C E) : TreeSimEvents C E := fun top tree D A x z _ log =>
  (decide (TreeSimHashBad3 D log), decide (¬ TreeSimHashBad3 D log ∧ Wrong top tree D A x z log))

/-- The sticky predicate of `treeSimEventsOf`. -/
def TreeSimBadOf (Wrong : CheckFlag C E) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) : Prop :=
  TreeSimHashBad3 D log ∨ Wrong top tree D A x z log

/-- `TreeSimBadOf Wrong` only grows with the log when `Wrong` only grows with the log. -/
theorem treeSimBadOf_mono (Wrong : CheckFlag C E) (mono : Wrong.Monotone)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSimBadOf Wrong top tree D A x z a → TreeSimBadOf Wrong top tree D A x z b :=
  Or.imp (treeSimHashBad3_mono D hab) (mono top tree D A x z a b hab)

/-- The two recorded flags of `treeSimEventsOf Wrong` are exactly the sticky predicate. -/
theorem treeSimEventsOf_bad (Wrong : CheckFlag C E) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    ((treeSimEventsOf Wrong top tree D A x z Z log).1 = true ∨
      (treeSimEventsOf Wrong top tree D A x z Z log).2 = true) ↔
      TreeSimBadOf Wrong top tree D A x z log := by
  simp only [treeSimEventsOf, decide_eq_true_eq, TreeSimBadOf]
  tauto

/-- The hash goal does not depend on the check flag. -/
theorem treeSimHashBound_of_goal3 (Wrong : CheckFlag C E)
    (hash : TreeSimHashBoundGoal3 prims K circuits settings) :
    TreeSimHashBound circuits settings
      (treeSimTrace prims K circuits settings (treeSimEventsOf Wrong)) := by
  intro hb top tree D A x z Z q hx hq hsmall
  have h := hash hb top tree D A x z Z q hx hq hsmall
  simpa only [treeSimTrace, probEvent_map, Function.comp_def, treeSimEvents3, treeSimEventsOf]
    using h

/-- The hash goal of `treeSimEvents3`, with no premise. The three closed inputs are the honest budget,
the raw salt estimate and the guarded pair bounds on the fixed split. -/
theorem hashBoundGoal3 : TreeSimHashBoundGoal3 prims K circuits settings :=
  treeSimHashBoundGoal3_of_guessGuarded
    (honest := treeSimHashHonestBudget K prims circuits settings)
    (salt := TreeRawSaltFinal.treeSimHashRawSaltEstimate prims K circuits settings)
    (reuse := treeSimSaltReuseGuessGuarded_of_pairs
      (splits := TreeSaltPairsFinal.splits prims K circuits settings)
      (pairBounds := LifetimeSaltGuarded.pairsGuarded_of_bounds prims K circuits settings
        (TreeSaltLiteralTransport.pairBoundsGuardedFrom prims K circuits settings)))

/-- The hop from the ceremony coupling and the check bound of one check flag `Wrong`. -/
theorem treeSimulationHop_of_wrong (Wrong : CheckFlag C E)
    (ceremony : TreeSimCeremonyCoupling prims K circuits settings (treeSimEventsOf Wrong))
    (check : TreeSimCheckBound circuits settings
      (treeSimTrace prims K circuits settings (treeSimEventsOf Wrong))) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  TreeTwinSegment.treeSimulationHop_of_ceremony prims K circuits settings (treeSimEventsOf Wrong)
    ceremony
    (treeSimHashBound_of_goal3 prims K circuits settings Wrong
      (hashBoundGoal3 prims K circuits settings))
    check

end ThresholdLeanXmssSecurity.TreeEvents4

open ThresholdLeanXmssSecurity.TreeEvents4

/-- info: 'ThresholdLeanXmssSecurity.TreeEvents4.treeSimBadOf_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimBadOf_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeEvents4.treeSimEventsOf_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimEventsOf_bad

/-- info: 'ThresholdLeanXmssSecurity.TreeEvents4.hashBoundGoal3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hashBoundGoal3

/-- info: 'ThresholdLeanXmssSecurity.TreeEvents4.treeSimulationHop_of_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_wrong
