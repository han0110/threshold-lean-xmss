import ThresholdLeanXmssSecurity.Proof.LifetimeIndexedCheck
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkHybrid
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedFinal

/-!
# Counted checks on the actual selected audit

`CountedCheckBounds` bounds the counted check event at each reached prefix
state of the joint audit. The bound at one prefix state uses the cut after
each setup state of the absorbed adversary. Each such setup state is a setup
state of the fixed-input audit, so `TreeCheckAfterSetupCutParts` applies there.
The fixed-input run bound of `TreeCheckCountedCutParts` is an average over the
prefix states, so it does not give a bound at one prefix state.

* `afterSetup_counted` bounds the counted event after one setup state by the
  check error of the largest batch.
* `setupFrom_absorbed` writes the setup of the absorbed adversary as the
  logged prefix followed by the setup from its retained state.
* `countedCheckBounds_of_afterSetup` gives `CountedCheckBounds` from
  `TreeCheckAfterSetupCutParts`.
* `countedCheckBounds_of_tailSources` gives it from
  `TreeCheckTailWalkSourceConstruction`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeCountedCheck

open LifetimeBridge LifetimeJointSimStages LifetimeContextual LifetimeIndexedCheck

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {C : Committee} (prims : Primitives)
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- At one cut state, the bound with the tuple count of the cut lifts to the
largest batch. The proof is the body of `treeCheckCounted_of_cut`
(`TreeCheckBranches.lean`) at one state. -/
theorem cutState_bound (agree : TreeLockstepRecordsAgreeGoal circuits prims K settings)
    (hbatch : 0 < settings.batchSize) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hx : DealtInputs D x)
    (j : Fin (treeBatches settings tree)) (cut : TreeCheckCountedCutData A)
    (hsplit : cut.Split prims K circuits settings top tree D A x z Z)
    (hcount : cut.Jobs prims K circuits settings top tree D A x z j)
    (s : cut.σ) (hs : s ∈ support cut.pre)
    (hbound : Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 | cut.cont s] ≤
      ENNReal.ofReal (if q = 0 then 0 else
        checkErrorOf (E := E) (coins (cut.count s)) (halvings (cut.count s)) (q - 1))) :
    Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 | cut.cont s] ≤
      ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E)
        (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
        (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q - 1)) := by
  by_cases hex : ∃ r ∈ support (cut.cont s), TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
      ¬ TreeCheckUncounted D r.2
  · obtain ⟨r, hr, hbad, hunc⟩ := hex
    have hsupport : r ∈ support (treeSimLoggedRun prims D
        (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)) := by
      rw [hsplit, mem_support_bind_iff]
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
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    split_ifs
    · exact le_rfl
    · exact hle
  · rw [probEvent_eq_zero]
    · exact zero_le
    · intro r hr hbad
      exact hex ⟨r, hr, hbad⟩

/-- After each reached setup state, the counted check event of batch `j` has
at most the check error of the largest batch with `q - 1` queries. -/
theorem afterSetup_counted (parts : TreeCheckAfterSetupCutParts prims K circuits settings)
    (hbatch : 0 < settings.batchSize) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hx : DealtInputs D x)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (hsmall : q < 2 ^ 128)
    (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z)) :
    Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 |
      treeCheckAfterSetup prims K circuits settings top tree D A x Z p] ≤
      ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E)
        (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
        (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q - 1)) := by
  have spec : ∀ p ∈ support (treeSaltSetup prims D A x z),
      TreeCheckAfterSetupCutAt prims K circuits settings top tree D A x z Z q j p
        (TreeCheckCountedCutData.afterSetup prims K circuits settings top tree D A x z Z q j p) :=
    fun p hp => TreeCheckCountedCutData.afterSetup_spec prims K circuits settings top tree D A x z
      Z q j p (parts hbatch top tree D A x z Z q hx hq hsmall j p hp)
  have mem := fun {p} {s} hs =>
    TreeCheckCountedCutData.mem_support_ofSetup prims K circuits settings top tree D A x z Z q j
      (p := p) (s := s) hs
  let cut := TreeCheckCountedCutData.ofSetup prims K circuits settings top tree D A x z Z q j
  have hsplit : cut.Split prims K circuits settings top tree D A x z Z :=
    TreeCheckCountedCutData.ofSetup_split prims K circuits settings top tree D A x z Z q j
  have hjobs : cut.Jobs prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.1 s (mem hs).2
  have hinputs : cut.Inputs prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.1 s (mem hs).2
  have hqueries : cut.Queries prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.1 s (mem hs).2
  have hcache : cut.Cache prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.1 s (mem hs).2
  have hprior : cut.Prior prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.1 s (mem hs).2
  have hreject : cut.Reject prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.2.1 s (mem hs).2
  have hbudget : cut.Budget prims K circuits settings top tree D A x z q j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.2.2.1 s (mem hs).2
  have htransport : cut.Transport prims K circuits settings top tree D A x z j := by
    rintro ⟨p, s⟩ hs
    exact (spec p (mem hs).1).2.2.2.2.2.2.2.2 s (mem hs).2
  rw [TreeCheckCountedCutData.afterSetup_split prims K circuits settings top tree D A x z Z q j p]
  refine probEvent_bind_le_of_forall_le fun s hs => ?_
  have hps : (⟨p, s⟩ : cut.σ) ∈ support cut.pre := by
    change _ ∈ support (treeSaltSetup prims D A x z >>= _)
    rw [mem_support_bind_iff]
    exact ⟨p, hp, by rw [support_map]; exact ⟨s, hs, rfl⟩⟩
  have agree := treeLockstepRecordsAgreeGoal prims K circuits settings
  exact cutState_bound prims K circuits settings agree hbatch top tree D A x
    z Z q hx j cut hsplit hjobs ⟨p, s⟩ hps
    (cut.bound agree hbatch hx hsplit hjobs hinputs hqueries hcache hprior
      hreject hbudget htransport ⟨p, s⟩ hps)

/-- The setup of the absorbed adversary is the logged prefix, then the setup
of the original adversary from the retained prefix state. -/
theorem setupFrom_absorbed (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z z' : Aux) :
    treeSaltSetup prims D (absorbed pre A z) x z' =
      loggedPrefix prims D pre >>= fun p => setupFrom prims D A x z p.2 := by
  unfold treeSaltSetup setupFrom loggedPrefix
  rw [absorbed_start]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, absorbed, executePhase_withPrefix]

/-- After a setup state, the absorbed adversary runs as the original
adversary, with the same full result and log. -/
theorem afterSetup_absorbed (top : TopTree) (tree : Tree) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    treeCheckAfterSetup prims K circuits settings top tree D (absorbed pre A z) x Z p =
      (fun out => (out.1, out.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D)
          (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2 := by
  rw [treeCheckAfterSetup_eq_audit]
  simp only [auditAfterProgram, absorbed, executeRounds_withPrefix]

/-- The per-setup-state cut gives the counted branch of the actual joint
audit, at the joint budget `q0 + q`. -/
theorem countedCheckBounds_of_afterSetup
    (parts : TreeCheckAfterSetupCutParts prims K circuits settings) :
    CountedCheckBounds prims K circuits settings := by
  intro hb D pre A Z q0 q prefixBudget adversaryBudget small j _
  apply selectedTrace_event_le
  intro p hp
  by_cases active : j < treeBatches settings p.1.2.2.1
  · rw [if_pos active]
    have bound : Pr[fun r =>
        IndexedBad prims K circuits settings D pre A j ((p.1, r.1), r.2.2) ∧
          ¬ TreeCheckUncounted D r.2.2 |
        (simulateQ (treeSimLoggedWorld prims D) (auditTail K circuits settings D A Z p.1)).run p.2] ≤
        ENNReal.ofReal (if q0 + q = 0 then 0 else checkErrorOf (E := E)
          (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q0 + q - 1)) := by
      dsimp only [auditTail]
      rw [audit_split]
      refine probEvent_bind_le_of_forall_le fun s hs => ?_
      have hs' : s ∈ support (treeSaltSetup prims D (absorbed pre A p.1.2.2.2) p.1.1 p.1.2.2.2) := by
        rw [setupFrom_absorbed]
        exact (mem_support_bind_iff _ _ _).mpr ⟨p, hp, hs⟩
      have tree := afterSetup_counted prims K circuits settings parts hb p.1.2.1 p.1.2.2.1 D
        (absorbed pre A p.1.2.2.2) p.1.1 p.1.2.2.2 Z (q0 + q) (loggedPrefix_dealt prims D pre p hp)
        (absorbed_bound pre A _ Z _ q0 q prefixBudget adversaryBudget) small ⟨j, active⟩ s hs'
      rw [afterSetup_absorbed] at tree
      erw [probEvent_map] at tree
      refine (probEvent_mono fun r _ bad => ?_).trans tree
      obtain ⟨⟨_, collision, indexed⟩, counted⟩ := bad
      exact ⟨⟨collision, indexed⟩, counted⟩
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top bound).trans_eq (ENNReal.toReal_ofReal ?_)
    split_ifs
    · exact le_rfl
    · letI : SampleableType E := SampleableType.ofFintype E
      exact checkErrorOf_nonneg K _ _ _
  · rw [if_neg active]
    have zero : Pr[fun r =>
        IndexedBad prims K circuits settings D pre A j ((p.1, r.1), r.2.2) ∧
          ¬ TreeCheckUncounted D r.2.2 |
        (simulateQ (treeSimLoggedWorld prims D) (auditTail K circuits settings D A Z p.1)).run p.2] = 0 :=
      probEvent_eq_zero fun _ _ bad => active bad.1.choose
    exact le_of_eq (congrArg ENNReal.toReal zero)

/-- The tail walk at each setup state gives the cut after that setup state. -/
theorem treeCheckAfterSetupCutParts_of_tailWalk
    (walk : TreeCheckTailWalkParts prims K circuits settings) :
    TreeCheckAfterSetupCutParts prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j p hp
  obtain ⟨W, parts⟩ := walk hbatch top tree D A x z Z q hx hq hsmall j p hp
  exact ⟨W.cut prims K circuits settings D Z, W.afterSetup prims K circuits settings parts⟩

/-- The source construction of the tail walk gives the counted branch of the
actual joint audit. -/
theorem countedCheckBounds_of_tailSources
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings) :
    CountedCheckBounds prims K circuits settings :=
  countedCheckBounds_of_afterSetup prims K circuits settings
    (treeCheckAfterSetupCutParts_of_tailWalk prims K circuits settings
      (treeCheckTailWalkParts_of_construction prims K circuits settings
        (treeCheckTailWalkConstruction_of_sources prims K circuits settings sources)))

/-- The source construction of the tail walk gives the indexed check bounds
of the actual joint audit. -/
theorem indexedCheckBounds_of_tailSources
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings) :
    IndexedCheckBounds prims K circuits settings :=
  indexedCheckBounds_of_counted prims K circuits settings
    (countedCheckBounds_of_tailSources prims K circuits settings sources)

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.cutState_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cutState_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.afterSetup_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterSetup_counted

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.setupFrom_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setupFrom_absorbed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.afterSetup_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterSetup_absorbed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.countedCheckBounds_of_afterSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countedCheckBounds_of_afterSetup

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.treeCheckAfterSetupCutParts_of_tailWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckAfterSetupCutParts_of_tailWalk

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.countedCheckBounds_of_tailSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countedCheckBounds_of_tailSources

/-- info: 'ThresholdLeanXmssSecurity.LifetimeCountedCheck.indexedCheckBounds_of_tailSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms indexedCheckBounds_of_tailSources

end ThresholdLeanXmssSecurity.LifetimeCountedCheck
