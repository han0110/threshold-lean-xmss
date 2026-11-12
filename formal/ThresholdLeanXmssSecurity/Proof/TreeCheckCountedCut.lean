import ThresholdLeanXmssSecurity.Proof.TreeCheckNoCommit
import ThresholdLeanXmssSecurity.Proof.TreeSetupKeys
import ThresholdLeanXmssSecurity.Proof.TreeLockstepRun

/-!
# The counted branch of the guarded check, cut at batch `j`

This module works on `TreeCheckCountedCut` (`TreeCheckBranches`).

* `TreeCheckCountedCutData` is a cut of the audited logged run at the start of the check of batch
  `j`. At each cut state `s` it names one instance of the hybrid check of
  `treeSimCheck_contextual`.
* `TreeCheckCountedCutParts` says that a cut exists with the split, the jobs of batch `j`, the
  boundary invariants, the budget and the transport to the hybrid check. Each part is a named
  `Prop` on the same cut. A part about the bound holds only at a cut state with a counted bad
  continuation (`Live`).
* `treeCheckCountedCut_of_parts` proves `TreeCheckCountedCut` from these parts.
* `treeSimCheckSetupBranches3_of_parts` proves `TreeSimCheckSetupBranches3` from the parts and
  `TreeLockstepOpenedGoal`, with `treeCheckUncountedGuess` (`TreeCheckNoCommit`).

The parts specify the concrete cut of the audited ceremony at batch `j`.

* `Split` is the cut. `treeSimCheckBatchAudit_phase_split` cuts one batch phase, and the cut must
  lift it through the ceremony up to batch `j`.
* `Jobs` says that the cut state fixes the jobs of batch `j`.
* `Inputs`, `Queries`, `Cache`, `Prior` and `Reject` are the hypotheses of
  `treeSimCheck_contextual` at the cut state. `Inputs` needs the common PRSS keys of
  `treeAgreementSetupKeys`. `Queries` can take the round bound `step` of `IsQueryBounded`.
  `Reject` needs the link from an accepted check to a correct batch.
* `Budget` says that the corrupt commitment to an honest operator is one counted query outside the
  coin domain. So a live state has `q ≥ 1`, and the case `q = 0` has no live state. If the
  coalition is empty, then no state may be live, by the completeness of the honest batch.
* `Transport` moves the real check after the cut to the hybrid check.
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

/-- One instance of the hybrid check of `treeSimCheck_contextual`. -/
structure TreeCheckHybrid (C : Committee) (E : Type) [Field E] [Fintype E] [DecidableEq E]
    [Algebra Bit E] where
  counts : List ℕ
  adversary : CheckAdversary C E (List (Tuple C))
  tuples : C.Party → List (Tuple C)
  step : ℕ
  state : adversary.State
  tag : ℕ
  label : ℕ
  cache : HashCache C
  seen : Finset (Query C)
  keys : Finset HashOutput

/-- The event of `treeSimCheck_contextual` on the hybrid check. -/
def TreeCheckHybrid.event (D : C.Coalition) (h : TreeCheckHybrid C E) : ℝ≥0∞ :=
  letI : SampleableType E := SampleableType.ofFintype E
  Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
    (simulateQ (localAnswer prims)
      (executePhase localRoles D h.adversary (checkFunctionalities K) (checkRounds h.counts.sum)
        h.state (fun i => (check K (localContext i) (hybridCheckGadgets K i) (h.tuples i)).run'
          ⟨filledHistory K i (h.tuples i), h.label, h.tag⟩))).run h.cache]

/-- A cut of the audited logged run at the start of the check of batch `j`. The prefix `pre` ends
at that boundary. At each cut state `s`, `count s` is the tuple count of batch `j` and
`hybrid s` is the hybrid check after the cut. -/
structure TreeCheckCountedCutData (A : Adversary C E (Keys C) PEmpty PEmpty) where
  σ : Type
  pre : ProbComp σ
  cont : σ → ProbComp ((Bool × (A.State ×
    (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
  count : σ → ℕ
  hybrid : σ → TreeCheckHybrid C E

namespace TreeCheckCountedCutData

variable {prims K circuits settings}
variable {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
  {x : C.Party → Keys C} {z : Aux} {Z : Distinguisher C A.State TreeOutput} {q : ℕ}
  {j : Fin (treeBatches settings tree)}

variable (prims K circuits settings top tree D A x z Z q j)

/-- The cut state `s` has a counted bad continuation. -/
def Live (cut : TreeCheckCountedCutData A) (s : cut.σ) : Prop :=
  ∃ r ∈ support (cut.cont s), TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
    ¬ TreeCheckUncounted D r.2

/-- The logged run is the prefix up to the check of batch `j`, then the continuation. -/
def Split (cut : TreeCheckCountedCutData A) : Prop :=
  treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z) =
    cut.pre >>= cut.cont

/-- The cut state fixes the tuple count of chunk `j` of each common encoding of the honest records
on each counted bad continuation. It is the first clause of `TreeCheckCountedCut`. -/
def Jobs (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, ∀ r ∈ support (cut.cont s),
    TreeCheckBranchBad prims K circuits settings top tree D A x z j r →
    ¬ TreeCheckUncounted D r.2 →
    ∀ (parameter : PublicParameter) (enc : Encoding),
      (∀ i, i ∉ D.1 → ∀ value records, r.1.2.2 i = some (value, records) →
        TreeLockstepRecords circuits parameter (lockstepChunks settings enc tree) records) →
      ∀ i, i ∉ D.1 → tupleCount (((lockstepChunks settings enc tree).getD j.val []).map
        (circuits (x i).parameter ·.kind)) = cut.count s

/-- The hybrid tuples are valid inputs with the tuple count of the cut. -/
def Inputs (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    TupleInputs K (cut.hybrid s).counts D (cut.hybrid s).tuples ∧
      (cut.hybrid s).counts.sum = cut.count s

/-- Each round and each answer of the hybrid adversary makes at most `step` counted queries. -/
def Queries (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    (∀ state sent, IsQueryBoundP ((cut.hybrid s).adversary.round state sent) Counted
      (cut.hybrid s).step) ∧
    (∀ state l, IsQueryBoundP ((cut.hybrid s).adversary.answer state l) Counted
      (cut.hybrid s).step)

/-- The coin inputs and the expansions in the cache at the cut are in `seen` or under a known
key. -/
def Cache (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    SoundCache (cut.hybrid s).label (cut.hybrid s).cache (cut.hybrid s).seen (cut.hybrid s).keys

/-- Each honest expansion key comes from an earlier coin input in the cache at the cut. -/
def Prior (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    TreeSimCheckPriorKeys (cut.hybrid s).label (cut.hybrid s).cache (cut.hybrid s).keys

/-- The verification functionality rejects the honest tuples at a live cut state. -/
def Reject (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    ¬ (multVerifyLeak D
      (fun i => if i ∈ D.1 then none else some ((cut.hybrid s).tuples i))).2.2

/-- At a live cut state, the seen coin inputs and the hybrid queries leave one of the `q` queries
for the corrupt commitment to an honest operator. -/
def Budget (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    (cut.hybrid s).seen.card + (2 * halvings (cut.count s) + 5) * (cut.hybrid s).step + 1 ≤ q

/-- The real check after the cut is at most the hybrid check. -/
def Transport (cut : TreeCheckCountedCutData A) : Prop :=
  ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
    Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 | cut.cont s] ≤
      (cut.hybrid s).event prims K D

end TreeCheckCountedCutData

namespace TreeCheckCountedCutData

variable {prims K circuits settings}
variable {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
  {x : C.Party → Keys C} {z : Aux} {Z : Distinguisher C A.State TreeOutput} {q : ℕ}
  {j : Fin (treeBatches settings tree)}

/-- A live cut state has a nonzero tuple count. The honest records of the live run follow one
common encoding, so chunk `j` holds the jobs of the bad batch record, which has a wrong tuple. -/
theorem count_ne_zero (cut : TreeCheckCountedCutData A)
    (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (hbatch : 0 < settings.batchSize) (hx : DealtInputs D x)
    (hsplit : cut.Split prims K circuits settings top tree D A x z Z)
    (hjobs : cut.Jobs prims K circuits settings top tree D A x z j)
    (s : cut.σ) (hs : s ∈ support cut.pre)
    (hlive : cut.Live prims K circuits settings top tree D A x z j s) : cut.count s ≠ 0 := by
  obtain ⟨r, hr, hbad, hunc⟩ := hlive
  have hrun : r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)) := by
    rw [hsplit, mem_support_bind_iff]
    exact ⟨s, hs, hr⟩
  obtain ⟨parameter, enc, hlock⟩ := agree hbatch top tree D A x z Z hx r hrun hbad.1
  obtain ⟨_, parameter', seeds, pairs, i, value, records, hash, before, batch, after,
    hxd, hi, hout, _, _, he, hj, _, hwrong, href⟩ := hbad.2
  obtain ⟨prss, hrecords⟩ := href.records prims K circuits settings top tree D A parameter' seeds
    pairs z r.2 hash i hi value records
  have hbmem : batch ∈ records := by simp [he]
  obtain ⟨hctx, hvalid⟩ := hrecords batch hbmem
  have hchunk : batch.jobs = (lockstepChunks settings enc tree).getD j.val [] := by
    have hk : before.length < records.length := by simp [he]
    have hb : records[before.length] = batch := by simp [he]
    rw [hj, ← hb]
    exact ((hlock i hi value records hout).2 before.length hk).1
  have hparameter : (x i).parameter = batch.ctx.keys.parameter := by
    rw [hctx, hxd]
  have hp : batch.ctx.keys.parameter = parameter' := by rw [hctx]; rfl
  have hw : batch.outputs ≠ batch.jobs.map (fun job =>
      ThresholdLeanXmssSecurity.D prims hash (evalJob circuits batch.ctx.keys.parameter seeds job)) := by
    simpa only [hp] using hwrong
  rw [← hjobs s hs r hr hbad hunc parameter enc hlock i hi, hparameter, ← hchunk]
  exact hvalid.incorrect_count prims K circuits settings hash seeds hw

/-- The bound after each cut state. A state that is not live has no counted bad continuation. At a
live state, `Budget` gives `q ≥ 1`, and the transport and `treeSimCheck_contextual` with `q - 1`
queries give the check error of the cut tuple count. -/
theorem bound (cut : TreeCheckCountedCutData A)
    (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (hbatch : 0 < settings.batchSize) (hx : DealtInputs D x)
    (hsplit : cut.Split prims K circuits settings top tree D A x z Z)
    (hjobs : cut.Jobs prims K circuits settings top tree D A x z j)
    (hinputs : cut.Inputs prims K circuits settings top tree D A x z j)
    (hqueries : cut.Queries prims K circuits settings top tree D A x z j)
    (hcache : cut.Cache prims K circuits settings top tree D A x z j)
    (hprior : cut.Prior prims K circuits settings top tree D A x z j)
    (hreject : cut.Reject prims K circuits settings top tree D A x z j)
    (hbudget : cut.Budget prims K circuits settings top tree D A x z q j)
    (htransport : cut.Transport prims K circuits settings top tree D A x z j)
    (s : cut.σ) (hs : s ∈ support cut.pre) :
    Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 | cut.cont s] ≤
      ENNReal.ofReal (if q = 0 then 0 else
        checkErrorOf (E := E) (coins (cut.count s)) (halvings (cut.count s)) (q - 1)) := by
  by_cases hlive : cut.Live prims K circuits settings top tree D A x z j s
  · have hb := hbudget s hs hlive
    have hq : q ≠ 0 := by omega
    rw [if_neg hq]
    obtain ⟨htuples, hsum⟩ := hinputs s hs hlive
    obtain ⟨hr, ha⟩ := hqueries s hs hlive
    refine (htransport s hs hlive).trans ?_
    letI : SampleableType E := SampleableType.ofFintype E
    have h := treeSimCheck_contextual prims K (cut.hybrid s).counts D (cut.hybrid s).adversary
      (cut.hybrid s).tuples (cut.hybrid s).step (q - 1) (cut.hybrid s).state (cut.hybrid s).tag
      (cut.hybrid s).label (cut.hybrid s).cache (cut.hybrid s).seen (cut.hybrid s).keys htuples
      (hsum ▸ cut.count_ne_zero agree hbatch hx hsplit hjobs s hs hlive) hr ha (hcache s hs hlive) (hprior s hs hlive)
      (by rw [hsum]; omega) (hreject s hs hlive)
    refine h.trans_eq ?_
    rw [hsum]
  · rw [probEvent_eq_zero]
    · exact zero_le
    · intro r hr hbad
      exact hlive ⟨r, hr, hbad⟩

end TreeCheckCountedCutData

/-- A cut at the check of each batch exists with all its parts. -/
def TreeCheckCountedCutParts : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree), ∃ cut : TreeCheckCountedCutData A,
        cut.Split prims K circuits settings top tree D A x z Z ∧
        cut.Jobs prims K circuits settings top tree D A x z j ∧
        cut.Inputs prims K circuits settings top tree D A x z j ∧
        cut.Queries prims K circuits settings top tree D A x z j ∧
        cut.Cache prims K circuits settings top tree D A x z j ∧
        cut.Prior prims K circuits settings top tree D A x z j ∧
        cut.Reject prims K circuits settings top tree D A x z j ∧
        cut.Budget prims K circuits settings top tree D A x z q j ∧
        cut.Transport prims K circuits settings top tree D A x z j

/-- `TreeCheckCountedCut` from a cut with all its parts and the common encoding of the honest
records. -/
theorem treeCheckCountedCut_of_parts
    (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (parts : TreeCheckCountedCutParts prims K circuits settings) :
    TreeCheckCountedCut prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j
  obtain ⟨cut, hsplit, hjobs, hinputs, hqueries, hcache, hprior, hreject, hbudget, htransport⟩ :=
    parts hbatch top tree D A x z Z q hx hq hsmall j
  refine ⟨cut.σ, cut.pre, cut.cont, cut.count, hsplit, hjobs, fun s hs => ?_⟩
  exact cut.bound agree hbatch hx hsplit hjobs hinputs hqueries hcache hprior hreject hbudget htransport s hs

/-- `TreeSimCheckSetupBranches3` from the cut parts and the opening agreement of the honest
records. The uncounted branch is `treeCheckUncountedGuess`, and the common encoding of the honest
records is `treeLockstepRecordsAgree_of_opened`. -/
theorem treeSimCheckSetupBranches3_of_parts
    (opened : TreeLockstepOpenedGoal circuits prims K settings)
    (parts : TreeCheckCountedCutParts prims K circuits settings) :
    TreeSimCheckSetupBranches3 prims K circuits settings :=
  treeSimCheckSetupBranches3_of_cut prims K circuits settings
    (treeLockstepRecordsAgree_of_opened prims K circuits settings opened)
    (treeCheckUncountedGuess prims K circuits settings)
    (treeCheckCountedCut_of_parts prims K circuits settings
      (treeLockstepRecordsAgree_of_opened prims K circuits settings opened) parts)

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCut_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCut_of_parts

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckSetupBranches3_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckSetupBranches3_of_parts

end ThresholdLeanXmssSecurity
