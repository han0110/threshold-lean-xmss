import ThresholdLeanXmssSecurity.Proof.TreeSimCheckFinish

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

/-- The job lists that a ceremony gives to `run`. -/
def CeremonyJobs (js : List Job) : Prop :=
  ∃ b enc, js = topJobs ∨ js = bottomJobs b ∨ js = signJobs b enc

/-- `ceremonyOutput_closed` for a property that `run` has only on the ceremony job lists. -/
theorem ceremonyOutput_closed_jobs {m : Type → Type} [Monad m] (P : ∀ {β : Type}, m β → Prop)
    (hpure : ∀ {β : Type} (b : β), P (pure b : m β))
    (hbind : ∀ {β γ : Type} (x : m β) (f : β → m γ), P x → (∀ b, P (f b)) → P (x >>= f))
    (lift : ∀ {β : Type}, OracleComp HashSpec β → m β) (hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), P (lift oa))
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit))))
    (hrun : ∀ js, CeremonyJobs js → P (run js))
    (top : TopTree) (tree : Tree) : P (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    refine hbind _ _ (hrun _ ⟨0, fun _ => digit 0, .inl rfl⟩) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · exact hbind _ _ (hlift _) fun _ => hpure _
  | bottom b =>
    refine hbind _ _ (hrun _ ⟨b, fun _ => digit 0, .inr (.inl rfl)⟩) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · refine hbind _ _ (hlift _) fun root => hbind _ _ (hlift _) fun base => hbind _ _ (hlift _) fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · exact hpure _
      · refine hbind _ _ (hrun _ ⟨b, encoding, .inr (.inr rfl)⟩) fun o' => ?_
        rcases o' with _ | values
        · exact hpure _
        · refine hbind _ _ (hlift _) fun path => hbind _ _ (hlift _) fun topRoot => ?_
          split <;> exact hpure _

theorem TreeSimCheckAuditAll.mapM_mem {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {good : W → Prop}
    (f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β) (xs : List α)
    (h : ∀ a ∈ xs, TreeSimCheckAuditAll allowed good (f a)) :
    TreeSimCheckAuditAll allowed good (xs.mapM f) := by
  induction xs with
  | nil => simpa only [List.mapM_nil] using TreeSimCheckAuditAll.pure allowed good ([] : List β)
  | cons a xs ih =>
    rw [List.mapM_cons]
    exact (h a (by simp)).bind (fun _ => (ih fun b hb => h b (by simp [hb])).bind
      (fun _ => .pure allowed good _))

theorem treeSimCheckBatchAudit_jobs
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) :
    TreeSimCheckAuditAll allowed (fun r => r.jobs = jobs)
      (treeSimCheckBatchAudit K circuits settings ctx jobs) := by
  intro initial value records final h r hr
  simp only [treeSimCheckBatchAudit, WriterT.run_mk, StateT.run_bind, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at h
  obtain ⟨inputs, _, hrest⟩ := h.option_bind_inv _ _ _
  obtain ⟨p, hp, he⟩ := hrest.option_bind_inv _ _ _
  have hrecs := congrArg (fun a => a.1.2) (Option.some.inj he.pure_inv)
  change records = [⟨ctx, jobs, initial, inputs, p.1.2.1, p.1.2.2, p.1.1, p.2⟩] at hrecs
  rw [hrecs, List.mem_singleton] at hr
  subst r
  rfl

/-- Every record of a ceremony checks one chunk of a ceremony job list. -/
theorem treeSimCheckCeremonyAuditBody_chunks
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree) :
    TreeSimCheckAuditAll allowed
      (fun r => ∃ js, CeremonyJobs js ∧ r.jobs ∈ chunks settings.batchSize js)
      (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree) := by
  unfold treeSimCheckCeremonyAuditBody
  apply ceremonyOutput_closed_jobs
    (m := WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)))
    (fun {α} (p : WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)) α) =>
      TreeSimCheckAuditAll allowed
        (fun r => ∃ js, CeremonyJobs js ∧ r.jobs ∈ chunks settings.batchSize js) p)
  · intro α a
    exact .pure _ _ a
  · intro α β p f hp hf
    exact hp.bind hf
  · intro α p
    exact .lift _ _ _
  · intro js hjs
    unfold batched
    refine (TreeSimCheckAuditAll.mapM_mem _ _ fun batch hbatch => ?_).bind (fun _ => .pure _ _ _)
    intro initial value records final h r hr
    exact ⟨js, hjs, (treeSimCheckBatchAudit_jobs K circuits settings allowed ctx batch
      initial value records final h r hr) ▸ hbatch⟩

theorem treeSimCheckAfterSetupAudit_chunks
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (h : TreeSimCheckAllowed allowed
      (treeSimCheckAfterSetupAudit K circuits settings ctx top tree).run (some (value, records))) :
    ∀ r ∈ records, ∃ js, CeremonyJobs js ∧ r.jobs ∈ chunks settings.batchSize js := by
  unfold treeSimCheckAfterSetupAudit at h
  obtain ⟨r, hr, hf⟩ := h.option_bind_inv _ _ _
  rcases r with ⟨_ | out, rs⟩
  · have he : some (value, records) = none := hf.pure_inv
    cases he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf.pure_inv)
    simp only [StateT.run'_eq] at hr
    obtain ⟨p, hp, he⟩ := hr.option_map_inv _ _ _
    rcases p with ⟨a, last⟩
    change a = (some value, records) at he
    subst a
    exact treeSimCheckCeremonyAuditBody_chunks K circuits settings allowed ctx top tree
      (0, 0) (some value) records last hp

/-- Every record of the reference replay checks one chunk of a ceremony job list. -/
theorem TreeSimCheckAuditedReference.chunks (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (log : TreeSimLog C) (hash : Query C → HashOutput) (i : C.Party) (hi : i ∉ D.1)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (ref : TreeSimCheckAuditedReference prims K circuits settings top tree D A parameter seeds pairs z
      log hash i value records) :
    ∀ r ∈ records, ∃ js, CeremonyJobs js ∧ r.jobs ∈ chunks settings.batchSize js := by
  obtain ⟨fuel, pref, audited, dealt, out, _, _, _, run, hv, _, _, hall⟩ := ref
  have hallowed : TreeSimCheckAllowed (fun t u => TreeSimCheckWorldHashes hash t u)
      (realExecution D A noFunctionality fuel
        (fun j keys => treeSimCheckCeremonyAudit K circuits settings j keys top tree)
        (dealtKeys parameter seeds pairs) z) audited := ⟨pref, run, hall⟩
  obtain ⟨state, _, hp⟩ := hallowed.bind_inv
  have hparty := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ audited hp
    i hi (value, records) hv
  unfold treeSimCheckCeremonyAudit at hparty
  obtain ⟨prss, _, hbody⟩ := hparty.option_bind_inv _ _ _
  exact treeSimCheckAfterSetupAudit_chunks K circuits settings _ _ top tree value records hbody

include K in
/-- The check error of one record is at most the check error of the largest batch. -/
theorem checkErrorOf_le_maxBatch
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {r : TreeSimCheckBatchRecord C} (valid : TreeSimCheckRecordValid K circuits settings allowed r)
    (hjobs : ∃ js, CeremonyJobs js ∧ r.jobs ∈ chunks settings.batchSize js) {q' q : ℕ} (hq : q' ≤ q) :
    checkErrorOf (E := E) (coins (r.tuples.map (·.count)).sum) (halvings (r.tuples.map (·.count)).sum) q' ≤
      checkErrorOf (E := E)
        (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
        (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q := by
  rw [valid.count K circuits settings]
  obtain ⟨js, ⟨b, enc, hjs⟩, hmem⟩ := hjobs
  have hcases : r.jobs ∈ chunks settings.batchSize topJobs ∨
      r.jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      r.jobs ∈ chunks settings.batchSize (signJobs b enc) := by
    rcases hjs with h | h | h
    · exact .inl (h ▸ hmem)
    · exact .inr (.inl (h ▸ hmem))
    · exact .inr (.inr (h ▸ hmem))
  exact checkErrorOf_mono K
    (measure_le_maxBatch circuits settings (fun jobs => coins (tupleCount jobs))
      r.ctx.keys.parameter b enc r.jobs hcases)
    (measure_le_maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))
      r.ctx.keys.parameter b enc r.jobs hcases) hq

/-- The record of a fixed indexed bad event is a real, nonempty check, and its check error with
any query bound `q' ≤ q` is at most the error of the largest batch with `q`. -/
theorem treeSimCheck_indexed_bad_lift (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree)) (log : TreeSimLog C)
    (actual : A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))
    (bad : TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j log actual) :
    ∃ i value records batch hash seeds,
      i ∉ D.1 ∧ actual.2 i = some (value, records) ∧ records[j.val]? = some batch ∧
      batch.ctx.self = i ∧ Good prims hash ∧
      TreeSimCheckRecordValid K circuits settings
        (treeSimCheckPartyAllowed (fun t u => TreeSimCheckWorldHashes hash (.inr t) u)) batch ∧
      batch.outputs ≠ batch.jobs.map (fun job =>
        ThresholdLeanXmssSecurity.D prims hash (evalJob circuits batch.ctx.keys.parameter seeds job)) ∧
      (batch.tuples.map (·.count)).sum ≠ 0 ∧
      ∀ q' q, q' ≤ q →
        checkErrorOf (E := E) (coins (batch.tuples.map (·.count)).sum)
          (halvings (batch.tuples.map (·.count)).sum) q' ≤
        checkErrorOf (E := E)
          (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q := by
  obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    _, hi, hout, _, hg, he, hj, _, hwrong, href⟩ := bad
  obtain ⟨prss, hrecords⟩ := href.records prims K circuits settings top tree D A parameter seeds pairs z
    log hash i hi value records
  have hbmem : batch ∈ records := by simp [he]
  obtain ⟨hctx, hvalid⟩ := hrecords batch hbmem
  have hp : batch.ctx.keys.parameter = parameter := by rw [hctx]; rfl
  have hw : batch.outputs ≠ batch.jobs.map (fun job =>
      ThresholdLeanXmssSecurity.D prims hash (evalJob circuits batch.ctx.keys.parameter seeds job)) := by
    simpa only [hp] using hwrong
  refine ⟨i, value, records, batch, hash, seeds, hi, hout, ?_, ?_, hg, hvalid, hw, ?_, ?_⟩
  · simp [he, hj]
  · rw [hctx]
  · rw [hvalid.count K circuits settings]
    exact hvalid.incorrect_count prims K circuits settings hash seeds hw
  · intro q' q hq
    exact checkErrorOf_le_maxBatch K circuits settings hvalid
      (href.chunks prims K circuits settings top tree D A parameter seeds pairs z log hash i hi
        value records batch hbmem) hq

include K in
/-- Accounting of the setup branch with `q ≥ 1`. The two `2^-256` terms fit in the coin term of
one query. -/
theorem checkErrorOf_setup_succ (d R q : ℕ) :
    2 * (2 : ℝ)⁻¹ ^ 256 + checkErrorOf (E := E) d R q ≤ checkErrorOf (E := E) d R (q + 1) := by
  have hE : (Fintype.card E : ℝ) = 2 ^ 192 := by rw [card_field K]; simp [elementBits]; norm_num
  have hkey : 2 * (2 : ℝ)⁻¹ ^ 256 ≤ ((R + 2 : ℕ) : ℝ) / (Fintype.card E : ℝ) := by
    rw [hE, inv_pow, le_div_iff₀ (by positivity)]
    have h2 : (2 : ℝ) ≤ ((R + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
    have h3 : 2 * ((2 : ℝ) ^ 256)⁻¹ * 2 ^ 192 ≤ 2 := by norm_num
    linarith
  unfold checkErrorOf
  have hsplit : (((R + 2) * (q + 1) : ℕ) : ℝ) / (Fintype.card E : ℝ) =
      (((R + 2) * q : ℕ) : ℝ) / (Fintype.card E : ℝ) + ((R + 2 : ℕ) : ℝ) / (Fintype.card E : ℝ) := by
    rw [← add_div]
    push_cast
    ring
  rw [hsplit]
  linarith

include K in
/-- Accounting of the setup branch with `q = 0`. -/
theorem checkErrorOf_setup_zero (d R : ℕ) :
    2 * (2 : ℝ)⁻¹ ^ 256 ≤ checkErrorOf (E := E) d R 0 := by
  have hE : (Fintype.card E : ℝ) = 2 ^ 192 := by rw [card_field K]; simp [elementBits]; norm_num
  have hpos : (0 : ℝ) < 2 ^ 192 - 2 := by norm_num
  have hkey : 2 * (2 : ℝ)⁻¹ ^ 256 ≤ ((d + 2 * (R + 1) : ℕ) : ℝ) / (Fintype.card E - 2 : ℝ) := by
    rw [hE, inv_pow, le_div_iff₀ hpos]
    have h2 : (2 : ℝ) ≤ ((d + 2 * (R + 1) : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    have h3 : 2 * ((2 : ℝ) ^ 256)⁻¹ * (2 ^ 192 - 2) ≤ 2 := by norm_num
    linarith
  unfold checkErrorOf
  simp only [mul_zero, Nat.cast_zero, zero_div, add_zero]
  exact hkey

include K in
/-- The setup accounting of `TreeSimCheckFinish`. The bad event splits on an event `uncounted`
(item 2, at most `2 * 2^-256`) and its complement (item 3, a check bound with `q - 1` queries,
empty when `q = 0`). The sum is at most `checkErrorOf d R q`. -/
theorem treeSimCheck_setup_accounting {α : Type} (p : ProbComp α) (bad uncounted : α → Prop)
    (d R q : ℕ)
    (hUncounted : Pr[fun r => bad r ∧ uncounted r | p] ≤ ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256))
    (hCounted : Pr[fun r => bad r ∧ ¬ uncounted r | p] ≤
      ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E) d R (q - 1))) :
    Pr[bad | p] ≤ ENNReal.ofReal (checkErrorOf (E := E) d R q) := by
  have hsplit : Pr[bad | p] ≤
      Pr[fun r => bad r ∧ uncounted r | p] + Pr[fun r => bad r ∧ ¬ uncounted r | p] := by
    refine (probEvent_mono'' fun r hr => ?_).trans (probEvent_or_le p _ _)
    by_cases hu : uncounted r
    · exact .inl ⟨hr, hu⟩
    · exact .inr ⟨hr, hu⟩
  refine hsplit.trans ((add_le_add hUncounted hCounted).trans ?_)
  have h0 : (0 : ℝ) ≤ 2 * (2 : ℝ)⁻¹ ^ 256 := by positivity
  rw [← ENNReal.ofReal_add h0 (by split_ifs; exacts [le_rfl, (letI : SampleableType E := SampleableType.ofFintype E; checkErrorOf_nonneg K _ _ _)])]
  apply ENNReal.ofReal_le_ofReal
  split_ifs with hq
  · subst hq
    simpa using checkErrorOf_setup_zero K d R
  · obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    simpa using checkErrorOf_setup_succ K d R q'

/-- The two setup branches of each fixed indexed batch event (items 2 and 3 of the accounting
in `TreeSimCheckFinish`). The event `uncounted` of a log says that some corrupt commitment to an
honest operator was not a counted query before its opening. -/
def TreeSimCheckSetupBranches : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree), ∃ uncounted : TreeSimLog C → Prop,
        Pr[fun r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 ∧
            uncounted r.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
          ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256) ∧
        Pr[fun r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 ∧
            ¬ uncounted r.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
          ENNReal.ofReal (if q = 0 then 0 else checkErrorOf (E := E)
            (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
            (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) (q - 1))

theorem treeSimCheckIndexedBounds_of_setupBranches
    (branches : TreeSimCheckSetupBranches prims K circuits settings) :
    TreeSimCheckIndexedBounds prims K circuits settings := by
  intro hbatch top tree D A x z Z q hx hq hsmall j
  obtain ⟨uncounted, h2, h3⟩ := branches hbatch top tree D A x z Z q hx hq hsmall j
  exact treeSimCheck_setup_accounting K _ _ (fun r => uncounted r.2) _ _ q h2 h3

theorem treeSimCheckBound_of_setupBranches
    (branches : TreeSimCheckSetupBranches prims K circuits settings) :
    TreeSimCheckBoundGoal prims K circuits settings :=
  treeSimCheckBoundFinal prims K circuits settings
    (treeSimCheckIndexedBounds_of_setupBranches prims K circuits settings branches)

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_indexed_bad_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheck_indexed_bad_lift

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_setup_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheck_setup_accounting

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBound_of_setupBranches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckBound_of_setupBranches

end ThresholdLeanXmssSecurity
