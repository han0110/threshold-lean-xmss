import ThresholdLeanXmssSecurity.Proof.TreeSimStagesFinish
import XmssSecurity.Proof.MarginalCoupling

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-!
## Salt reuse

Two hidden digest salts can be equal. The fixed event `treeSimEvents` does not
cover this case, so the hash event needs a new disjunct. The trace below is a
deduction from the frozen definitions. It is not a Lean refutation.

The digest input has no unique label of the batch.
* `Query.history` takes only the bits of the values (`Scheme.lean:198`), and
  `Query.digest` takes only the salt and the history hash (`Scheme.lean:200`).
  Neither takes a term or a batch.
* The tag `k` of the batch goes only into `Query.coinKey` (`Scheme.lean:660`).
* `record` appends to `RunState.history` (`Scheme.lean:471`), and
  `compareDigests` hashes this history (`Scheme.lean:575`).
* `ceremonyWith` starts each batch with the empty history
  `⟨fun _ => [], label, k⟩` (`Scheme.lean:1161`). So the history does not grow
  over the ceremony.

The run that the events miss goes as follows.
1. Batch 1 draws the salt `s` of a hidden term `T₀`, and batch 2 draws the
   same `s`. The labels differ, so these are two different PRG addresses, and
   each pair of draws is equal with probability `2^-256`.
2. The break needs the two history hashes of `T₀` to be equal in one run
   and different in the other. For example, if the real histories are equal,
   the real run asks the same `.digest s η` twice and gets the same digest
   `d`. If the ideal histories differ, the ideal run asks `.digest s η₁'` and
   `.digest s η₂'` and gets two different digests.
3. `TreeSimHashCollision` (`TreeSim.lean:1531`) needs two different queries
   with one answer. A repeated query is not a collision.
   `TreeSimSaltGuess` (`TreeSim.lean:1544`) needs a counted digest query, and
   the queries in step 2 are honest. So `TreeSimHashBad`
   (`TreeSim.lean:1550`) and `treeSimEvents` (`TreeSim.lean:1583`) do not
   hold.
4. The swaps `(s, η, η₁')` and `(s, η, η₂')` of `TreeStagesSwapRel` then share
   the key `(s, η)`, so no swap list relates the two final caches. A distinguisher
   that compares the two digests sees the difference.

The same break occurs when a hidden salt equals the salt of a known term that
an honest holder hashes in some batch. So the new disjunct is that a hidden salt
equals the salt of another honest digest draw.

This shows only that the swap route fails on these runs with the present
`TreeSimHashBad`. It does not show that `TreeSimStagesGoal` is false.

The extra term fits in the budget if the bound of the present events uses
at most `S'` honest region points. `TreeSimHashBoundGoal` is open, so this is
an assumption. Let `N` be the number of honest salt draws.
Each batch draws at most one salt for each term, so
`N ≤ treeBatches * termCount ≤ S'`, where
`S' = treeSecrets - 2 * prssKeyCount` (`Statement.lean:411`). The budget of
`TreeSimHashBound` (`TreeSim.lean:10130`) is `(q + S')² / 2^256`, which is
`treeHashError - keySplit` (`TreeSecurity.lean:41`). The present events need at
most `(q + S')² / 2^257` for the birthday collision and `q * N / 2^256` for the
salt guess. The salt collision needs at most `N² / 2^257`. The sum is at most
`((q + S')² + 2 q S' + S'²) / 2^257 ≤ (q + S')² / 2^256`.
-/

/-- Coupling composition in the relational form of `Relation.Comp`. -/
theorem treeCompose_relTriple_comp {α β γ : Type} {oa : ProbComp α} {ob : ProbComp β}
    {oc : ProbComp γ} {R : α → β → Prop} {S : β → γ → Prop}
    (hab : RelTriple oa ob R) (hbc : RelTriple ob oc S) :
    RelTriple oa oc (Relation.Comp R S) :=
  XmssSecurity.relTriple_trans_exists hab hbc

/-- Two real states whose public caches differ by hidden-salt digest swaps.
The private caches are equal. -/
def TreeStagesRealSwap (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    (a b : TreeSimState C) : Prop :=
  (∀ x ∈ swaps, TreeSimHiddenSalt D a.2 x.1) ∧ b.1.1 = treeStagesSwapAll swaps a.1.1 ∧
    b.1.2 = a.1.2

/-- A real run that is identical to a swapped real run until a salt guess,
composed with an equal-cache coupling of the swapped run and the ideal run,
gives a swap-related coupling. A bad event of the swapped run must transfer
to the real log. -/
theorem treeCompose_swapRel {X : Type} (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (δ : HiddenAddress C → Bit)
    (Bad Bad' : TreeSimLog C → Prop) (guess : ∀ log, TreeSimSaltGuess D log → Bad log)
    (transfer : ∀ u v : X × TreeSimState C, u.1 = v.1 → TreeStagesRealSwap D swaps u.2 v.2 →
      Bad' v.2.2 → Bad u.2.2)
    {oa ob : ProbComp (X × TreeSimState C)} {oc : ProbComp (X × (HashCache C × HiddenCache C))}
    (real : RelTriple oa ob (fun u v => TreeSimSaltGuess D u.2.2 ∨
      (u.1 = v.1 ∧ TreeStagesRealSwap D swaps u.2 v.2)))
    (equal : RelTriple ob oc (fun v w => Bad' v.2.2 ∨
      (v.1 = w.1 ∧ v.2.1.1 = w.2.1 ∧ TreeSimHiddenRel δ v.2.1.2 w.2.2))) :
    RelTriple oa oc (fun u w => Bad u.2.2 ∨ (u.1 = w.1 ∧ TreeStagesSwapRel D swaps δ u.2 w.2)) := by
  apply relTriple_post_mono (treeCompose_relTriple_comp real equal)
  rintro u w ⟨v, bad | ⟨same, salts, cache, hidden⟩, bad' | ⟨same', cache', hidden'⟩⟩
  · exact Or.inl (guess _ bad)
  · exact Or.inl (guess _ bad)
  · exact Or.inl (transfer u v same ⟨salts, cache, hidden⟩ bad')
  · refine Or.inr ⟨same.trans same', salts, cache'.symm.trans cache, ?_⟩
    rw [← hidden]
    exact hidden'

/-- info: 'ThresholdLeanXmssSecurity.treeCompose_relTriple_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeCompose_relTriple_comp

/-- info: 'ThresholdLeanXmssSecurity.treeCompose_swapRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeCompose_swapRel

end ThresholdLeanXmssSecurity
