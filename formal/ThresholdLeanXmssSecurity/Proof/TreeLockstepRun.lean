import ThresholdLeanXmssSecurity.Proof.TreeLockstep

/-!
# Batch records on the audited logged run

The actual successful party execution supplies the audit-body witness required
by `treeLockstepRecords_audit`. This proves the schedule of each operator with
no collision guard. Agreement between operators must additionally preserve
their shared network execution and its opening checks.

`treeLockstepRecordsRun_first_common` aligns the jobs and labels of every common
first-run record. For a top tree this covers the whole ceremony. The exact
remaining obligation is `TreeLockstepOpenedGoal`, defined in `TreeLockstep`:
under its budget-collision guard, two successful honest operators' records at
the same index have equal outputs. Its proof still needs the common checked
sharing at the actual synchronized opening boundary. Per-party replay alone
does not supply this joint fact. `treeLockstep_bottom_encoding` identifies the
bottom-tree encoding from the first-run outputs and the shared hash answers.
Thus `treeLockstepRecordsAgree_of_opened` proves the full common schedule from
the unchanged `TreeLockstepOpenedGoal` alone.

The pinned and current leanVM proofs were searched for an audit-support bridge.
The threshold-specific replay lemmas already connect the scheduled network to
each party, so no XMSS helper is duplicated here.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A successful audited suffix has the schedule proved for its actual audit body. -/
theorem treeLockstep_afterSetup_records
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (h : TreeSimCheckAllowed allowed
      (treeSimCheckAfterSetupAudit K circuits settings ctx top tree).run (some (value, records))) :
    ∃ enc : Encoding,
      TreeLockstepRecords circuits ctx.keys.parameter (lockstepChunks settings enc tree) records := by
  unfold treeSimCheckAfterSetupAudit at h
  obtain ⟨r, hr, hf⟩ := h.option_bind_inv _ _ _
  rcases r with ⟨_ | out, rs⟩
  · have he : some (value, records) = none := hf.pure_inv
    cases he
  · have he := Prod.mk.inj (Option.some.inj hf.pure_inv)
    obtain ⟨rfl, rfl⟩ := he
    simp only [StateT.run'_eq] at hr
    obtain ⟨p, hp, he⟩ := hr.option_map_inv _ _ _
    rcases p with ⟨a, last⟩
    change a = (some value, records) at he
    subst a
    exact treeLockstepRecords_audit circuits K settings allowed ctx top tree
      (some value) records last hp

/-- Every successful honest output of the actual logged run follows one encoding's schedule. -/
theorem treeLockstepRecordsRun : TreeLockstepRecordsRunGoal circuits prims K settings := by
  intro top tree D A x z Z result run i hi value records out
  rcases result with ⟨⟨result, actual⟩, log⟩
  have replay := treeSimCheckReplay_logged prims D _ (result, actual) log run
  unfold treeSimCheckAuditedGame at replay
  obtain ⟨r, pre, tail, hr, ht, _⟩ := replay.bind_inv
  obtain ⟨b, mid, post, _, hp, _⟩ := ht.bind_inv
  cases hp
  have hallowed : TreeSimCheckAllowed (fun _ _ => True)
      (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun j keys => treeSimCheckCeremonyAudit K circuits settings j keys top tree) x z) actual :=
    ⟨pre, hr, by simp⟩
  obtain ⟨state, _, hphase⟩ := hallowed.bind_inv
  have hparty := treeSimCheck_phase_replay D A noFunctionality _ _ state _ actual hphase
    i hi (value, records) out
  unfold treeSimCheckCeremonyAudit at hparty
  obtain ⟨prss, _, hbody⟩ := hparty.option_bind_inv _ _ _
  exact treeLockstep_afterSetup_records K circuits settings _ ⟨i, x i, prss⟩ top tree value records hbody

/-- The jobs and labels already agree throughout the first run, with no hash guard. -/
theorem treeLockstepRecordsRun_first_common
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (hx : DealtInputs D x)
    (r : (Bool × (A.State × (C.Party → Option
      (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
    (hr : r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (vi vj : TreeOutput) (ri rj : List (TreeSimCheckBatchRecord C))
    (hoi : r.1.2.2 i = some (vi, ri)) (hoj : r.1.2.2 j = some (vj, rj))
    (k : ℕ) (hki : k < ri.length) (hkj : k < rj.length)
    (first : ∀ b, tree = .bottom b → k < (chunks settings.batchSize (bottomJobs b)).length) :
    ri[k].jobs = rj[k].jobs ∧ ri[k].start = rj[k].start := by
  obtain ⟨parameter, seeds, pairs, hx⟩ := hx
  obtain ⟨enci, hri⟩ := treeLockstepRecordsRun prims K circuits settings
    top tree D A x z Z r hr i hi vi ri hoi
  obtain ⟨encj, hrj⟩ := treeLockstepRecordsRun prims K circuits settings
    top tree D A x z Z r hr j hj vj rj hoj
  rw [hx i] at hri
  rw [hx j] at hrj
  exact treeLockstepRecords_common circuits settings parameter tree enci encj ri rj
    hri hrj k hki hkj (Or.inr first)

/-- A top ceremony has one common schedule without an opening-agreement premise. -/
theorem treeLockstepRecordsRun_top_agree
    (top : TopTree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (hx : DealtInputs D x)
    (r : (Bool × (A.State × (C.Party → Option
      (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
    (hr : r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top .top D A x z Z))) :
    ∃ (parameter : PublicParameter) (enc : Encoding), ∀ i, i ∉ D.1 → ∀ value records,
      r.1.2.2 i = some (value, records) →
      TreeLockstepRecords circuits parameter (lockstepChunks settings enc .top) records := by
  obtain ⟨parameter, seeds, pairs, hx⟩ := hx
  refine ⟨parameter, fun _ => digit 0, ?_⟩
  intro i hi value records hout
  obtain ⟨enc, hrec⟩ := treeLockstepRecordsRun prims K circuits settings
    top .top D A x z Z r hr i hi value records hout
  rw [hx i] at hrec
  exact hrec

private theorem lockstep_batch_outputs
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (value : Option (List (List Bit))) (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial).run
      (some ((value, records), final))) :
    ∃ r, records = [r] ∧ value = some r.outputs := by
  simp only [treeSimCheckBatchAudit, WriterT.run_mk, StateT.run_bind, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at h
  obtain ⟨inputs, _, hrest⟩ := h.option_bind_inv _ _ _
  obtain ⟨p, _, he⟩ := hrest.option_bind_inv _ _ _
  have he := Option.some.inj he.pure_inv
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj he |>.imp Prod.mk.inj id
  exact ⟨_, rfl, rfl⟩

private theorem lockstep_mapM_outputs
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (js : List (List Job)) (initial : ℕ × ℕ)
    (values : List (Option (List (List Bit)))) (records : List (TreeSimCheckBatchRecord C))
    (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((js.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial).run
      (some ((values, records), final))) :
    values = records.map (fun r => some r.outputs) := by
  induction js generalizing initial values records final with
  | nil =>
    simp only [List.mapM_nil, WriterT.run_pure, StateT.run_pure, OptionT.run_pure] at h
    have he := Option.some.inj h.pure_inv
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj he |>.imp Prod.mk.inj id
    rfl
  | cons jobs js ih =>
    simp only [List.mapM_cons, WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
    obtain ⟨p, hp, hrest⟩ := h.option_bind_inv _ _ _
    obtain ⟨q, hq, he⟩ := hrest.option_map_inv _ _ _
    obtain ⟨q', hq', he'⟩ := hq.option_bind_inv _ _ _
    have he'' := Option.some.inj he'.pure_inv
    subst he''
    obtain ⟨r, hr, hv⟩ := lockstep_batch_outputs K circuits settings allowed ctx jobs
      initial p.1.1 p.1.2 p.2 hp
    have ht := ih p.2 q'.1.1 q'.1.2 q'.2 hq'
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    simp [hr, hv, ht]

/-- A completed batched run returns precisely the concatenation of its recorded outputs. -/
theorem treeLockstep_batched_outputs
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (value : Option (List (List Bit))) (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs).run.run initial).run
      (some ((value, records), final))) :
    value = some ((records.map TreeSimCheckBatchRecord.outputs).flatten) := by
  simp only [batched, WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
  obtain ⟨p, hp, hrest⟩ := h.option_bind_inv _ _ _
  obtain ⟨q, hq, he⟩ := hrest.option_map_inv _ _ _
  have hq' := Option.some.inj hq.pure_inv
  subst hq'
  have hv := lockstep_mapM_outputs K circuits settings allowed ctx _ initial _ _ _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  rw [hv]
  simpa only [List.map_map, Function.comp_def, List.empty_eq, List.append_nil, List.nil_append] using
    foldlM_some_append (p.1.2.map TreeSimCheckBatchRecord.outputs) []

private theorem lockstep_lift_public {σ W α : Type}
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (q : OracleComp HashSpec α) (s : σ) (a : α) (recs : List W) (f : σ)
    (h : TreeSimCheckAllowed allowed
      (((liftM (StateT.lift (oracleStep (tweakable q)) : StateT σ (PartyM C E RealSpec) α) :
        WriterT (List W) (StateT σ (PartyM C E RealSpec)) α).run.run s).run) (some ((a, recs), f))) :
    a = ThresholdLeanXmssSecurity.D prims hash (tweakable q) := by
  simp only [WriterT.run_liftM, StateT.run_map, StateT.run_lift] at h
  obtain ⟨x, hx, he⟩ := h.option_map_inv _ _ _
  obtain ⟨y, hy, hp⟩ := hx.option_bind_inv _ _ _
  have hp' := Option.some.inj hp.pure_inv
  subst hp'
  have ha := (Prod.mk.inj (Prod.mk.inj he).1).1
  exact ha.symm.trans (treeSimCheck_public_replay prims allowed hash hhash q y hy)

/-- The bottom-tree encoding computed by the public code from the first-run outputs. -/
def treeLockstepBottomEncoding (hash : Query C → HashOutput) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : Encoding :=
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let chainEnd := fun (e : KeyIndex) (l : ChainIndex) =>
    digestAt (outputs.getD (keys.idxOf (e, l)) []) 2
  let root := ThresholdLeanXmssSecurity.D prims hash
    (tweakable (merkleNode parameter bottomLayer chainEnd layerHeight b.val))
  let message := bytesLE 16 root
  let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
  let base := ThresholdLeanXmssSecurity.D prims hash
    (tweakable (truncateHash <$> Concrete.oracleHash
      (randomizerInput parameter topLayer (topKey b) ρ message)))
  ((ThresholdLeanXmssSecurity.D prims hash (tweakable
    (grind parameter topLayer (topKey b) message base randomizerAttemptLimit 0))).map Prod.snd).getD
      (fun _ => digit 0)

/-- A successful bottom ceremony uses the encoding of its own first-run records. -/
theorem treeLockstep_bottom_encoding
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight)) (value : TreeOutput)
    (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((treeSimCheckCeremonyAuditBody K circuits settings ctx top (.bottom b)).run.run (0, 0)).run
      (some ((some value, records), final))) :
    let n := (chunks settings.batchSize (bottomJobs b)).length
    n ≤ records.length ∧ TreeLockstepRecords circuits ctx.keys.parameter
      (lockstepChunks settings (treeLockstepBottomEncoding prims hash ctx.keys.parameter b
        (((records.take n).map TreeSimCheckBatchRecord.outputs).flatten)) (.bottom b)) records := by
  unfold treeSimCheckCeremonyAuditBody ceremonyOutput at h
  dsimp only at h
  obtain ⟨o, w, mid, w', hfirst, hrest, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ h
  obtain ⟨hlen, hrec, hmid⟩ := lockstep_batched_audit circuits K settings allowed ctx _ 0 0 _ _ _ hfirst
  have ho := treeLockstep_batched_outputs K circuits settings allowed ctx _ (0, 0) _ _ _ hfirst
  subst o
  dsimp only at hrest
  obtain ⟨root, w₁, mid₁, w₁', h₁, hrest₁, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest
  have hroot := lockstep_lift_public prims allowed hash hhash _ _ _ _ _ h₁
  obtain ⟨rfl, rfl⟩ := lockstep_lift_inv _ _ _ _ _ h₁
  obtain ⟨base, w₂, mid₂, w₂', h₂, hrest₂, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest₁
  have hbase := lockstep_lift_public prims allowed hash hhash _ _ _ _ _ h₂
  obtain ⟨rfl, rfl⟩ := lockstep_lift_inv _ _ _ _ _ h₂
  obtain ⟨g, w₃, mid₃, w₃', h₃, hrest₃, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest₂
  have hgrind := lockstep_lift_public prims allowed hash hhash _ _ _ _ _ h₃
  obtain ⟨rfl, rfl⟩ := lockstep_lift_inv _ _ _ _ _ h₃
  simp only [List.nil_append]
  rcases g with _ | ⟨randomness, enc⟩
  · simp only [WriterT.run_pure, StateT.run_pure, OptionT.run_pure] at hrest₃
    have he := hrest₃.pure_inv
    cases he
  · dsimp only at hrest₃
    obtain ⟨o', w₄, mid₄, w₄', h₄, hrest₄, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest₃
    have hnil : w₄' = [] := by
      refine lockstep_noRecords ?_ _ _ _ _ hrest₄
      rcases o' with _ | values
      · exact .pure _ _ _
      · exact (TreeSimCheckAuditAll.lift _ _ _).bind fun _ =>
          (TreeSimCheckAuditAll.lift _ _ _).bind fun _ => by
            split_ifs <;> exact .pure _ _ _
    rw [hnil, List.append_nil]
    simp only [Nat.zero_add] at hrec hmid
    rw [hmid] at h₄
    obtain ⟨hlen₄, hrec₄, _⟩ := lockstep_batched_audit circuits K settings allowed ctx _ _ _ _ _ _ h₄
    have henc : treeLockstepBottomEncoding prims hash ctx.keys.parameter b
        (((w ++ w₄).take (chunks settings.batchSize (bottomJobs b)).length).map
          TreeSimCheckBatchRecord.outputs).flatten = enc := by
      rw [← hlen, List.take_left]
      unfold treeLockstepBottomEncoding
      dsimp only
      rw [← hroot, ← hbase, ← hgrind]
      rfl
    refine ⟨by simp only [List.length_append]; omega, ?_⟩
    rw [henc]
    exact treeLockstepRecords_append circuits ctx.keys.parameter _ _ w w₄ hlen hrec hlen₄.le hrec₄

private theorem lockstep_afterSetup_bottom_encoding
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (h : TreeSimCheckAllowed allowed
      (treeSimCheckAfterSetupAudit K circuits settings ctx top (.bottom b)).run (some (value, records))) :
    let n := (chunks settings.batchSize (bottomJobs b)).length
    n ≤ records.length ∧ TreeLockstepRecords circuits ctx.keys.parameter
      (lockstepChunks settings (treeLockstepBottomEncoding prims hash ctx.keys.parameter b
        (((records.take n).map TreeSimCheckBatchRecord.outputs).flatten)) (.bottom b)) records := by
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
    exact treeLockstep_bottom_encoding prims K circuits settings allowed hash hhash
      ctx top b value records last hp

/-- All successful party suffixes replay under one shared public hash function. -/
theorem treeLockstep_run_public
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (r : (Bool × (A.State × (C.Party → Option
      (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
    (hr : r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z))) :
    ∃ hash : Query C → HashOutput, ∀ i, i ∉ D.1 → ∀ value records,
      r.1.2.2 i = some (value, records) → ∃ prss,
        TreeSimCheckAllowed
          (treeSimCheckPartyAllowed (fun t u => TreeSimCheckWorldHashes hash (.inr t) u))
          (treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree).run
          (some (value, records)) := by
  rcases r with ⟨⟨result, actual⟩, log⟩
  have hc := hr
  simp only [treeSimLoggedRun, StateT.run'_eq, support_map, Set.mem_image] at hc
  obtain ⟨⟨a, cache⟩, hc, he⟩ := hc
  change a = ((result, actual), log) at he
  subst a
  have hall := (treeSimCheck_logged_hashes prims D _ (∅, ∅) (result, actual) log cache hc).2
  have replay := treeSimCheckReplay_logged prims D _ (result, actual) log hr
  unfold treeSimCheckAuditedGame at replay
  obtain ⟨r, pre, tail, hp, ht, hlog⟩ := replay.bind_inv
  obtain ⟨b, mid, post, _, he, _⟩ := ht.bind_inv
  cases he
  have hallowed : TreeSimCheckAllowed (fun t u => TreeSimCheckWorldHashes (hashOf prims cache.1) t u)
      (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun j keys => treeSimCheckCeremonyAudit K circuits settings j keys top tree) x z) actual :=
    ⟨pre, hp, fun t u hu => hall t u (hlog ▸ List.mem_append_left tail hu)⟩
  obtain ⟨state, _, hphase⟩ := hallowed.bind_inv
  refine ⟨hashOf prims cache.1, ?_⟩
  intro i hi value records hout
  have hparty := treeSimCheck_phase_replay D A noFunctionality _ _ state _ actual hphase
    i hi (value, records) hout
  unfold treeSimCheckCeremonyAudit at hparty
  obtain ⟨prss, _, hbody⟩ := hparty.option_bind_inv _ _ _
  exact ⟨prss, hbody⟩

/-- Opening agreement is the only remaining premise for the common full-ceremony schedule. -/
theorem treeLockstepRecordsAgree_of_opened
    (opened : TreeLockstepOpenedGoal circuits prims K settings) :
    TreeLockstepRecordsAgreeGoal circuits prims K settings := by
  intro hbatch top tree D A x z Z hx r hr good
  cases tree with
  | top => exact treeLockstepRecordsRun_top_agree prims K circuits settings top D A x z Z hx r hr
  | bottom b =>
    obtain ⟨hash, hparty⟩ := treeLockstep_run_public prims K circuits settings
      top (.bottom b) D A x z Z r hr
    obtain ⟨parameter, seeds, pairs, hx'⟩ := hx
    let n := (chunks settings.batchSize (bottomJobs b)).length
    have canonical : ∀ i, i ∉ D.1 → ∀ value records, r.1.2.2 i = some (value, records) →
        n ≤ records.length ∧ TreeLockstepRecords circuits parameter
          (lockstepChunks settings (treeLockstepBottomEncoding prims hash parameter b
            (((records.take n).map TreeSimCheckBatchRecord.outputs).flatten)) (.bottom b)) records := by
      intro i hi value records hout
      obtain ⟨prss, hbody⟩ := hparty i hi value records hout
      have h := lockstep_afterSetup_bottom_encoding prims K circuits settings _ hash
        (fun _ _ h => h) ⟨i, x i, prss⟩ top b value records hbody
      rw [hx' i] at h
      exact h
    by_cases existsOutput : ∃ i, i ∉ D.1 ∧ ∃ value records, r.1.2.2 i = some (value, records)
    · obtain ⟨i, hi, vi, ri, hoi⟩ := existsOutput
      have hni := (canonical i hi vi ri hoi).1
      refine ⟨parameter, treeLockstepBottomEncoding prims hash parameter b
        (((ri.take n).map TreeSimCheckBatchRecord.outputs).flatten), ?_⟩
      intro j hj vj rj hoj
      obtain ⟨hnj, hrec⟩ := canonical j hj vj rj hoj
      have he : (ri.take n).map TreeSimCheckBatchRecord.outputs =
          (rj.take n).map TreeSimCheckBatchRecord.outputs := by
        apply List.ext_getElem
        · simp only [List.length_map, List.length_take, Nat.min_eq_left hni, Nat.min_eq_left hnj]
        · intro k hki hkj
          have hk : k < n := by
            simpa only [List.length_map, List.length_take, Nat.min_eq_left hni] using hki
          simp only [List.getElem_map, List.getElem_take]
          exact opened hbatch top (.bottom b) D A x z Z ⟨parameter, seeds, pairs, hx'⟩
            r hr good i j hi hj vi ri vj rj hoi hoj
            k (hk.trans_le hni) (hk.trans_le hnj)
      rw [he]
      exact hrec
    · refine ⟨parameter, fun _ => digit 0, ?_⟩
      intro i hi value records hout
      exact (existsOutput ⟨i, hi, value, records, hout⟩).elim

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecordsRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecordsRun

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecordsRun_first_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecordsRun_first_common

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecordsRun_top_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecordsRun_top_agree

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_bottom_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_bottom_encoding

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecordsAgree_of_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecordsAgree_of_opened

end ThresholdLeanXmssSecurity
