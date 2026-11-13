import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame

/-! # The relation without the top clauses, and the post of a step inside a handler

- `SyncPre` is `SyncAt` without the top clauses. The setup holds it before the top tree exists.
  `syncAt_iff_pre` states that `SyncAt` is `SyncPre` and the top clauses.
- `ExtraOpen.retop` states that the clauses move to another top tree in a state with no stored tree.
- `InPost` is the post of a coupled step inside a handler, on the base source state.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Pre
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

section Open
variable (prims : Primitives) (x : Keys3 C) (s : HiddenKey → Digest)
  (rev : HiddenKey → Option Digest)

/-- In a state with no stored tree, no clause reads the top tree. -/
theorem ExtraOpen.retop (top top' : TopTree) (openRow : KeyIndex → ChainIndex → Prop)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (h : ExtraOpen prims x top s rev openRow a b) (hnone : ∀ bi, b.1.base.trees bi = none) :
    ExtraOpen prims x top' s rev openRow a b := by
  refine ⟨{ h.rest with storedRuns := ?_, startsTraced := ?_ }, h.prfSeen, h.bottomSeen⟩
  · intro bi tree ht
    have hst := h.rest.storedTrees bi
    rw [hnone bi] at hst
    rw [hst] at ht
    cases ht
  · intro e l d hd
    obtain ⟨tree, ht⟩ := h.rest.startsTreed e l (Finset.ne_empty_of_mem hd)
    rw [hnone] at ht
    cases ht

end Open

section Relation
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The relation inside a handler without the top clauses. The setup holds it before the top tree
exists. -/
def SyncPre (top : TopTree) (rev : HiddenKey → Option Digest)
    (openRow : KeyIndex → ChainIndex → Prop) (cCore cTime : Carried C)
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (b.1.base, b.2) ∧
    ExtraOpen prims x top s rev openRow (withCarried a cTime) b ∧ PadsFixed x pads b.2

/-- The relation inside a handler is the relation without the top clauses, and the top clauses. -/
theorem syncAt_iff_pre (top : TopTree) (rev : HiddenKey → Option Digest)
    (openRow : KeyIndex → ChainIndex → Prop) (cCore cTime : Carried C)
    (a : RealState C) (b : SourceStateO1 C × CompState C) :
    SyncAt prims x s pads u rest noise top rev openRow cCore cTime a b ↔
      SyncPre prims x s pads u rest noise top rev openRow cCore cTime a b ∧ TopO1 prims x top a b :=
  ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.2⟩, h.2.2.1⟩, fun h => ⟨h.1.1, h.1.2.1, h.2, h.1.2.2⟩⟩

/-- The post of a coupled step inside a handler, on the base source state. `rev'` gives the reveal
map after the step. The step keeps the recorded digits, the signing state, the stored trees, the
exposed trees and the candidates of the source, and the carried state of the real run. -/
def InPost (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C) {α β : Type}
    (rev' : (β × SourceState C) × CompState C → HiddenKey → Option Digest)
    (value : α → β → Prop) (ra : α × RealState C) (rb : (β × SourceState C) × CompState C) : Prop :=
  RealStop q ra.2 ∨ Stop rb.2 ∨
    (value ra.1 rb.1.1 ∧
      SyncAt prims x s pads u rest noise top (rev' rb) (fun _ _ => False) cCore cTime ra.2
        (⟨rb.1.2, b.1.starts⟩, rb.2) ∧
      rb.1.2.signing = b.1.base.signing ∧ rb.1.2.trees = b.1.base.trees ∧
      rb.1.2.exposed = b.1.base.exposed ∧ rb.1.2.candidates = b.1.base.candidates ∧
      rb.2.1.2 = false ∧ ra.2.1.2 = a.1.2 ∧ realLog a ≤ realLog ra.2)

end Relation

end ThresholdLeanXmssSecurity.SigningCompilerO1Pre

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pre.ExtraOpen.retop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pre.ExtraOpen.retop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Pre.syncAt_iff_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Pre.syncAt_iff_pre
