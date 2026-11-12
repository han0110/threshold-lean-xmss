import ThresholdLeanXmssSecurity.Proof.TreeEvents3

/-!
# The setup branches of the guarded check route

`TreeSimCheckSetupBranches3` (`TreeEvents3`) splits the bad event of batch `j` on the event
`TreeCheckUncounted`. In this event, an honest operator opens a corrupt PRSS commitment with no
counted query of that point before the opening.

* `treeCheckCounted_of_cut` proves the counted branch from the cut `TreeCheckCountedCut` and
  `TreeLockstepRecordsAgreeGoal`.
* `treeSimCheckSetupBranches3_of_cut` gives `TreeSimCheckSetupBranches3` from these two and the
  uncounted branch `TreeCheckUncountedGuess`.

The two Props are hypotheses of the assembly.

* `TreeCheckUncountedGuess` needs the freshness of the first uncounted opening in the logged
  cache and the abort propagation of the PRSS echo exchange. Then one fresh answer of `H` meets a
  fixed value, with probability `2^-256`.
* `TreeCheckCountedCut` needs the split of the logged run at the check of batch `j`, the boundary
  invariants of `treeSimCheck_contextual` (`TupleInputs`, `SoundCache`, `TreeSimCheckPriorKeys`
  and the reject of `multVerifyLeak`), and the transport of the real check to the hybrid check.
  The common PRSS keys come from `prssEchoAccepted_agree` and `TreeAgreementSetupKeys`. The cut
  state must fix the jobs of batch `j` under the common encoding. If `q = 0`, then each corrupt
  commitment is uncounted. If the coalition is empty, no commitment pays a query and the honest
  tuples are correct, so the bound follows from the completeness of the honest ceremony, for
  each `q`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

section Branches

/-- A corrupt operator `j` commits to an honest operator `i` in the PRSS setup, and `i` opens the
commitment with no counted query of the same point before the opening. -/
def TreeCheckUncounted (D : C.Coalition) (log : TreeSimLog C) : Prop :=
  ∃ (before after : TreeSimLog C) (j i : C.Party) (reveal : List HashOutput) (h : HashOutput),
    log = before ++ ⟨.inr (.inr (.inl (.commit .prss j i reveal))), h⟩ :: after ∧
    j ∈ D.1 ∧ i ∉ D.1 ∧
    ∀ h', (⟨.inl (.inl (.inr (.inl (.commit .prss j i reveal)))), h'⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∉ before

/-- The fixed batch event of `TreeSimCheckSetupBranches3` on one logged run. -/
def TreeCheckBranchBad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree))
    (r : (Bool × (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) ×
      TreeSimLog C) : Prop :=
  ¬ TreeSimHashBudgetCollision r.2 ∧
    TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2

/-- The uncounted branch. The opening of the first uncounted commitment in a fixed order is a fresh
answer of `H`, and it must match the commitment that the adversary sent before. An honest operator
that rejects an opening aborts, and the next exchange stops every honest operator
(`treeSimCheck_exchange_round_abort`), so no batch record exists. -/
def TreeCheckUncountedGuess : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
            TreeCheckUncounted D r.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
          ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256)

/-- The counted branch, cut at the start of the check of batch `j`. The prefix `pre` ends at that
boundary, and `count s` is the tuple count of the batch at the cut state `s`.
* On a bad run after `s`, the chunk `j` of each common encoding of the honest records has the
  tuple count `count s`. So the cut state fixes the jobs of batch `j`.
* After each cut state, the bad event has at most the check error of `treeSimCheck_contextual`
  with `q - 1` queries. Each corrupt commitment to an honest operator is a counted query outside
  the coin domain, so it uses one of the `q` queries. If the coalition is empty, then the honest
  batch is correct, for each `q`. -/
def TreeCheckCountedCut : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∃ (σ : Type) (pre : ProbComp σ)
          (cont : σ → ProbComp ((Bool × (A.State ×
            (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C))
          (count : σ → ℕ),
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z) =
            pre >>= cont ∧
          (∀ s ∈ support pre, ∀ r ∈ support (cont s),
            TreeCheckBranchBad prims K circuits settings top tree D A x z j r →
            ¬ TreeCheckUncounted D r.2 →
            ∀ (parameter : PublicParameter) (enc : Encoding),
              (∀ i, i ∉ D.1 → ∀ value records, r.1.2.2 i = some (value, records) →
                TreeLockstepRecords circuits parameter (lockstepChunks settings enc tree) records) →
              ∀ i, i ∉ D.1 → tupleCount (((lockstepChunks settings enc tree).getD j.val []).map
                (circuits (x i).parameter ·.kind)) = count s) ∧
          ∀ s ∈ support pre,
            Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
                ¬ TreeCheckUncounted D r.2 | cont s] ≤
              ENNReal.ofReal (if q = 0 then 0 else
                checkErrorOf (E := E) (coins (count s)) (halvings (count s)) (q - 1))

/-- The counted branch of `TreeSimCheckSetupBranches3` from the cut. On a bad run, the honest
records follow one common encoding (`TreeLockstepRecordsAgreeGoal`), so the record of batch `j`
has the tuple count of the cut, and its check error lifts to the largest batch. -/
theorem treeCheckCounted_of_cut (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (cut : TreeCheckCountedCut prims K circuits settings)
    (hbatch : 0 < settings.batchSize) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hx : DealtInputs D x)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (hsmall : q < 2 ^ 128)
    (j : Fin (treeBatches settings tree)) :
    Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 |
      treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
      ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E)
        (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
        (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q - 1)) := by
  obtain ⟨σ, pre, cont, count, hrun, hcount, hbound⟩ :=
    cut hbatch top tree D A x z Z q hx hq hsmall j
  rw [hrun]
  apply probEvent_bind_le_of_forall_le
  intro s hs
  by_cases hex : ∃ r ∈ support (cont s), TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
      ¬ TreeCheckUncounted D r.2
  · obtain ⟨r, hr, hbad, hunc⟩ := hex
    have hsupport : r ∈ support (treeSimLoggedRun prims D
        (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)) := by
      rw [hrun, mem_support_bind_iff]
      exact ⟨s, hs, hr⟩
    obtain ⟨parameter', enc, hlock⟩ := agree hbatch top tree D A x z Z hx r hsupport hbad.1
    obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
      hxd, hi, hout, _, _, he, hj, _, _, href⟩ := hbad.2
    obtain ⟨prss, hrecords⟩ := href.records prims K circuits settings top tree D A parameter seeds
      pairs z r.2 hash i hi value records
    have hbmem : batch ∈ records := by simp [he]
    obtain ⟨hctx, hvalid⟩ := hrecords batch hbmem
    have hle := checkErrorOf_le_maxBatch K circuits settings hvalid
      (href.chunks prims K circuits settings top tree D A parameter seeds pairs z r.2 hash i hi
        value records batch hbmem) (le_refl (q - 1))
    have hjobs : batch.jobs = (lockstepChunks settings enc tree).getD j.val [] := by
      have hk : before.length < records.length := by simp [he]
      have hb : records[before.length] = batch := by simp [he]
      rw [hj, ← hb]
      exact ((hlock i hi value records hout).2 before.length hk).1
    have hparameter : batch.ctx.keys.parameter = (x i).parameter := by
      rw [hctx, hxd]
    have hsum := hcount s hs r hr hbad hunc parameter' enc hlock i hi
    rw [hvalid.count K circuits settings, hparameter, hjobs, hsum] at hle
    refine (hbound s hs).trans (ENNReal.ofReal_le_ofReal ?_)
    split_ifs
    · exact le_rfl
    · exact hle
  · rw [probEvent_eq_zero]
    · exact zero_le
    · intro r hr hbad
      exact hex ⟨r, hr, hbad⟩

/-- `TreeSimCheckSetupBranches3` with `uncounted` set to `TreeCheckUncounted`, from the common
encoding of the honest records (A9). -/
theorem treeSimCheckSetupBranches3_of_cut
    (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (guess : TreeCheckUncountedGuess prims K circuits settings)
    (cut : TreeCheckCountedCut prims K circuits settings) :
    TreeSimCheckSetupBranches3 prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j
  exact ⟨TreeCheckUncounted D, guess hbatch top tree D A x z Z q hx hq hsmall j,
    treeCheckCounted_of_cut prims K circuits settings agree cut hbatch top tree D A x z Z q hx hq hsmall j⟩

end Branches

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCounted_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCounted_of_cut

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckSetupBranches3_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckSetupBranches3_of_cut

end ThresholdLeanXmssSecurity
