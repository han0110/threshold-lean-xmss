import ThresholdLeanXmssSecurity.Proof.TreeTwinFields
import ThresholdLeanXmssSecurity.Proof.TreeAgreement

/-!
# The lockstep of the honest operators in the real tree run

The honest operators that did not abort run the same batches in the same rounds. The ghost is
the list of job chunks of the ceremony, `lockstepChunks settings enc tree`. The chunks of the
second run of a bottom tree depend on the encoding `enc` that the first run opens.

* `lockstepStart` is the label at the start of each batch, from `batchLabels`.
* `lockstepSaltLabel` is the label of the salts `Rand(ρ, 2)` of the check of each batch. Two
  checked batches have different salt labels (`lockstepSaltLabel_lt`).
* `TreeLockstepSalts` is the lockstep on the salt reads of a log.
* `TreeLockstepRecords` is the lockstep on the batch records of one operator.

The three consumer links are deterministic.

* `treeTwinDigestFresh_of_lockstep` gives the freshness half of `TreeTwinDigestDrawn`.
  `treeTwinDigestDrawn_of_lockstep` gives `TreeTwinDigestDrawn` from `TreeLockstepStagesGoal` and
  `TreeTwinDigestDrawsGoal` at a configuration with no budget collision.
* `treeAgreementSaltRun_of_lockstep` gives `TreeAgreementSaltRun` from `TreeLockstepSaltRunGoal`.
* `treeLockstepRecords_common` gives the common jobs, start label and tag at batch `k` for the
  check cut. The batch `k` must be in the first run, or the encodings must agree.

The schedule of one operator holds with no collision guard.

* `lockstepLabels_check` counts `checkLabels` labels in the check.
* `lockstep_batchAudit` shows that one batch moves the label by `batchLabels`.
* `treeLockstepRecords_audit` proves `TreeLockstepRecordsGoal`. The records of each complete
  audited ceremony follow the chunks of one encoding.

The interfaces are `TreeLockstepStagesGoal`, `TreeLockstepSaltRunGoal`,
`TreeLockstepRecordsAgreeGoal` and `TreeTwinDigestDrawsGoal`. The parts of the first three are
`TreeAgreementSetupKeys`, `TreeLockstepRecordsRunGoal` and `TreeLockstepOpenedGoal`, and the
timing that the honest operators run the same batch in the same round. No round is stated here.
The first three goals need the agreement of the honest operators on the opened outputs of the
first run. Two honest holders of a term do
not compare their copies in `openRep`, so this agreement needs the agreement on the term keys.
That needs no collision of two `.sharedKeys` inputs, which `TreeSimHashBudgetCollision` excludes
and `TreeSimBad2` and `TreeSimHashBad` do not.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The job chunks of a ceremony. A bottom tree has the chunks of its first run, then the chunks
of its second run for `encoding`. -/
def lockstepChunks (settings : Settings) (encoding : Encoding) : Tree → List (List Job)
  | .top => chunks settings.batchSize topJobs
  | .bottom b => chunks settings.batchSize (bottomJobs b) ++
      chunks settings.batchSize (signJobs b encoding)

private theorem chunks_length {α : Type} (size : ℕ) (items : List α) :
    (chunks size items).length = (items.length + size - 1) / size := by
  simp [chunks]

/-- The chunks count `treeBatches` for every encoding. -/
theorem lockstepChunks_length (settings : Settings) (encoding : Encoding) (tree : Tree) :
    (lockstepChunks settings encoding tree).length = treeBatches settings tree := by
  cases tree with
  | top => rfl
  | bottom b =>
    simp only [lockstepChunks, treeBatches, List.length_append, chunks_length, signJobs,
      List.length_map]

variable (circuits : Circuits)

/-- The label at the start of batch `k`. Each batch takes `batchLabels` labels. -/
def lockstepStart (parameter : PublicParameter) (js : List (List Job)) (k : ℕ) : ℕ :=
  ((js.take k).map (batchLabels circuits parameter)).sum

/-- The label of the salts `Rand(ρ, 2)` of the check of batch `k`. The batch takes one label for
each AND layer and one for `Rerand`. The check takes one for its first coin, two for each halving
step, and one for `randElements` and one for `extendMult` before `randBits`. -/
def lockstepSaltLabel (parameter : PublicParameter) (js : List (List Job)) (k : ℕ) : ℕ :=
  lockstepStart circuits parameter js k + depth ((js.getD k []).map (circuits parameter ·.kind)) + 1 +
    (2 * halvings (batchCount circuits parameter (js.getD k [])) + 3)

theorem lockstepStart_succ (parameter : PublicParameter) (js : List (List Job)) (k : ℕ)
    (hk : k < js.length) :
    lockstepStart circuits parameter js (k + 1) =
      lockstepStart circuits parameter js k + batchLabels circuits parameter (js.getD k []) := by
  simp only [lockstepStart, List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.toList_some, Option.getD_some, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem lockstepStart_cons (parameter : PublicParameter) (jobs : List Job) (js : List (List Job))
    (k : ℕ) :
    lockstepStart circuits parameter (jobs :: js) (k + 1) =
      batchLabels circuits parameter jobs + lockstepStart circuits parameter js k := by
  simp only [lockstepStart, List.take_succ_cons, List.map_cons, List.sum_cons]

theorem lockstepStart_mono (parameter : PublicParameter) (js : List (List Job)) {k k' : ℕ}
    (h : k ≤ k') : lockstepStart circuits parameter js k ≤ lockstepStart circuits parameter js k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold lockstepStart
  rw [List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem lockstepSaltLabel_lt_start (parameter : PublicParameter) (js : List (List Job)) (k : ℕ)
    (hk : k < js.length) (hcount : batchCount circuits parameter (js.getD k []) ≠ 0) :
    lockstepSaltLabel circuits parameter js k < lockstepStart circuits parameter js (k + 1) := by
  rw [lockstepStart_succ circuits parameter js k hk]
  have hc : checkLabels (batchCount circuits parameter (js.getD k [])) =
      2 * halvings (batchCount circuits parameter (js.getD k [])) + 5 := if_neg hcount
  unfold lockstepSaltLabel batchLabels
  rw [hc]
  omega

/-- The salt labels of two checks differ. -/
theorem lockstepSaltLabel_lt (parameter : PublicParameter) (js : List (List Job)) {k k' : ℕ}
    (hkk : k < k') (hk : k < js.length) (hcount : batchCount circuits parameter (js.getD k []) ≠ 0) :
    lockstepSaltLabel circuits parameter js k < lockstepSaltLabel circuits parameter js k' :=
  (lockstepSaltLabel_lt_start circuits parameter js k hk hcount).trans_le
    ((lockstepStart_mono circuits parameter js hkk).trans (by unfold lockstepSaltLabel; omega))

/-- The lockstep on the salt reads of a log. Each read of `Rand(ρ, 2)` of a term uses the common
key of the term and the salt label of a checked batch `k` with `lo ≤ k < hi`. -/
def TreeLockstepSalts (keys : C.Term → HashOutput) (parameter : PublicParameter)
    (js : List (List Job)) (lo hi : ℕ) (log : TreeSimLog C) : Prop :=
  ∀ (T : C.Term) (key : HashOutput) (label g : ℕ) (b : Bit),
    (⟨.inr (.inr (.inr (.term T, key, label, 2, g))), b⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
    key = keys T ∧ ∃ k, lo ≤ k ∧ k < hi ∧ k < js.length ∧
      batchCount circuits parameter (js.getD k []) ≠ 0 ∧
      label = lockstepSaltLabel circuits parameter js k

/-- The half of `TreeTwinDigestDrawn` that the lockstep gives. No hidden salt of the earlier log
`start` was drawn at the address of a salt that the round log `l` draws. -/
def TreeTwinDigestFresh (D : C.Coalition) (start l : TreeSimLog C) : Prop :=
  ∀ (T' : C.Term) (key' : HashOutput) (label' : ℕ) (salt : List Bit), (∀ g : Fin 256,
      (⟨.inr (.inr (.inr (.term T', key', label', 2, g.val))), salt.getD g.val 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l) →
    ∀ T key label, ¬ KnownTo D.1 T → (∀ g : Fin 256,
      (⟨.inr (.inr (.inr (.term T, key, label, 2, g.val))), salt.getD g.val 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ start) →
      (T, key, label) ≠ (T', key', label')

/-- The other half of `TreeTwinDigestDrawn`. Each honest digest call of the round log `l` hashes a
salt that `l` draws at one address. -/
def TreeTwinDigestDraws (l : TreeSimLog C) : Prop :=
  ∀ salt hist answer, (⟨.inr (.inr (.inl (.digest salt hist))), answer⟩ :
    (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
    ∃ T' key' label', ∀ g : Fin 256,
      (⟨.inr (.inr (.inr (.term T', key', label', 2, g.val))), salt.getD g.val 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l

theorem treeTwinDigestDrawn_of_draws_fresh (D : C.Coalition) (start l : TreeSimLog C)
    (draws : TreeTwinDigestDraws l) (fresh : TreeTwinDigestFresh D start l) :
    TreeTwinDigestDrawn D start l := by
  intro salt hist answer mem
  obtain ⟨T', key', label', hl⟩ := draws salt hist answer mem
  exact ⟨T', key', label', hl, fresh T' key' label' salt hl⟩

/-- The first consumer link. The salts of the earlier log lie at the batches below `k₀`, and the
salts of the round lie at the batches from `k₀`. The salt labels of two checks differ. -/
theorem treeTwinDigestFresh_of_lockstep (D : C.Coalition) (keys : C.Term → HashOutput)
    (parameter : PublicParameter) (js : List (List Job)) (k₀ : ℕ) (start l : TreeSimLog C)
    (before : TreeLockstepSalts circuits keys parameter js 0 k₀ start)
    (round : TreeLockstepSalts circuits keys parameter js k₀ js.length l) :
    TreeTwinDigestFresh D start l := by
  intro T' key' label' salt hl T key label _ hstart heq
  obtain ⟨-, k', hk', -, -, -, hlabel'⟩ := round T' key' label' 0 _ (hl ⟨0, by norm_num⟩)
  obtain ⟨-, k, -, hk, hklen, hcount, hlabel⟩ := before T key label 0 _ (hstart ⟨0, by norm_num⟩)
  have hlt := lockstepSaltLabel_lt circuits parameter js (hk.trans_le hk') hklen hcount
  simp only [Prod.mk.injEq] at heq
  omega

/-- The salt labels of all checked batches. -/
def lockstepSaltLabels (parameter : PublicParameter) (js : List (List Job)) : List ℕ :=
  (List.range js.length).map (lockstepSaltLabel circuits parameter js)

/-- The second consumer link. The lockstep over all batches gives `TreeAgreementLog`. -/
theorem treeAgreementLog_of_lockstep (keys : C.Term → HashOutput) (parameter : PublicParameter)
    (js : List (List Job)) (log : TreeSimLog C)
    (lockstep : TreeLockstepSalts circuits keys parameter js 0 js.length log) :
    TreeAgreementLog keys (lockstepSaltLabels circuits parameter js) log := by
  refine ⟨fun T key label g b mem => ?_⟩
  obtain ⟨hkey, k, -, hk, -, -, hlabel⟩ := lockstep T key label g b mem
  exact ⟨hkey, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hlabel.symm⟩⟩

/-- The first run of a bottom tree does not depend on the encoding. -/
theorem lockstepChunks_getD_first (settings : Settings) (enc enc' : Encoding) (tree : Tree) (k : ℕ)
    (hk : ∀ b, tree = .bottom b → k < (chunks settings.batchSize (bottomJobs b)).length) :
    (lockstepChunks settings enc tree).getD k [] = (lockstepChunks settings enc' tree).getD k [] := by
  cases tree with
  | top => rfl
  | bottom b =>
    simp only [lockstepChunks, List.getD_eq_getElem?_getD, List.getElem?_append_left (hk b rfl)]

theorem lockstepStart_first (settings : Settings) (parameter : PublicParameter) (enc enc' : Encoding)
    (tree : Tree) (k : ℕ)
    (hk : ∀ b, tree = .bottom b → k ≤ (chunks settings.batchSize (bottomJobs b)).length) :
    lockstepStart circuits parameter (lockstepChunks settings enc tree) k =
      lockstepStart circuits parameter (lockstepChunks settings enc' tree) k := by
  cases tree with
  | top => rfl
  | bottom b =>
    simp only [lockstepStart, lockstepChunks, List.take_append_of_le_length (hk b rfl)]

/-- The batch records of an operator follow the chunks `js`. Record `k` holds the jobs of chunk
`k`, and it starts at the label `lockstepStart k` with the tag `k`. -/
def TreeLockstepRecords (parameter : PublicParameter) (js : List (List Job))
    (records : List (TreeSimCheckBatchRecord C)) : Prop :=
  records.length ≤ js.length ∧ ∀ k (hk : k < records.length),
    records[k].jobs = js.getD k [] ∧ records[k].start = (lockstepStart circuits parameter js k, k)

theorem lockstepStart_append (parameter : PublicParameter) (js js' : List (List Job)) (k : ℕ) :
    lockstepStart circuits parameter (js ++ js') (js.length + k) =
      lockstepStart circuits parameter js js.length + lockstepStart circuits parameter js' k := by
  simp only [lockstepStart, List.take_append, List.take_length, List.map_append, List.sum_append,
    Nat.add_sub_cancel_left, List.take_of_length_le (Nat.le_add_right js.length k)]

/-- Records that follow `js` and then records that follow `js'` from the end of `js` follow
`js ++ js'`. -/
theorem treeLockstepRecords_append (parameter : PublicParameter) (js js' : List (List Job))
    (w w' : List (TreeSimCheckBatchRecord C)) (hlen : w.length = js.length)
    (hw : ∀ k (hk : k < w.length), w[k].jobs = js.getD k [] ∧
      w[k].start = (lockstepStart circuits parameter js k, k))
    (hlen' : w'.length ≤ js'.length)
    (hw' : ∀ k (hk : k < w'.length), w'[k].jobs = js'.getD k [] ∧
      w'[k].start = (lockstepStart circuits parameter js js.length +
        lockstepStart circuits parameter js' k, js.length + k)) :
    TreeLockstepRecords circuits parameter (js ++ js') (w ++ w') := by
  refine ⟨by simp only [List.length_append]; omega, fun k hk => ?_⟩
  by_cases hkw : k < w.length
  · rw [List.getElem_append_left hkw]
    obtain ⟨hj, hs⟩ := hw k hkw
    refine ⟨by rw [hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (hlen ▸ hkw)], ?_⟩
    rw [hs]
    have hmono : lockstepStart circuits parameter js k = lockstepStart circuits parameter (js ++ js') k := by
      simp only [lockstepStart, List.take_append_of_le_length (hlen ▸ hkw.le : k ≤ js.length)]
    rw [hmono]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hkw)
    have hj : j < w'.length := by simp only [List.length_append] at hk; omega
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    obtain ⟨hjobs, hs⟩ := hw' j hj
    refine ⟨?_, ?_⟩
    · rw [hjobs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hlen,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    · rw [hs, hlen, lockstepStart_append]

/-- The third consumer link. Two operators whose records follow the chunks of the encodings `enc`
and `enc'` have the same jobs, start label and tag at batch `k`, if the encodings agree or batch
`k` is in the first run. -/
theorem treeLockstepRecords_common (settings : Settings) (parameter : PublicParameter)
    (tree : Tree) (enc enc' : Encoding) (records records' : List (TreeSimCheckBatchRecord C))
    (h : TreeLockstepRecords circuits parameter (lockstepChunks settings enc tree) records)
    (h' : TreeLockstepRecords circuits parameter (lockstepChunks settings enc' tree) records')
    (k : ℕ) (hk : k < records.length) (hk' : k < records'.length)
    (same : enc = enc' ∨ ∀ b, tree = .bottom b → k < (chunks settings.batchSize (bottomJobs b)).length) :
    records[k].jobs = records'[k].jobs ∧ records[k].start = records'[k].start := by
  obtain ⟨hj, hs⟩ := h.2 k hk
  obtain ⟨hj', hs'⟩ := h'.2 k hk'
  rw [hj, hj', hs, hs']
  rcases same with rfl | hfirst
  · exact ⟨rfl, rfl⟩
  · exact ⟨lockstepChunks_getD_first settings enc enc' tree k hfirst,
      by rw [lockstepStart_first circuits settings parameter enc enc' tree k
        fun b hb => (hfirst b hb).le]⟩

section Labels

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)

/-- A program of a run moves the label by `n` on each complete run. -/
def LockstepLabels {α : Type} (n : ℕ) (p : RunM C E RealSpec α) : Prop :=
  ∀ st a final, some (a, final) ∈ support (p.run st).run → final.label = st.label + n

theorem LockstepLabels.pure {α : Type} (a : α) : LockstepLabels (C := C) (E := E) 0 (Pure.pure a) := by
  intro st b final h
  simp only [StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  rw [h.2]
  rfl

theorem LockstepLabels.bind {α β : Type} {m n : ℕ} {p : RunM C E RealSpec α}
    {k : α → RunM C E RealSpec β} (hp : LockstepLabels m p) (hk : ∀ a, LockstepLabels n (k a)) :
    LockstepLabels (m + n) (p >>= k) := by
  intro st b final h
  rw [StateT.run_bind] at h
  obtain ⟨⟨a, mid⟩, ha, hb⟩ := treeSimCheck_some_bind _ _ _ h
  rw [hk a mid b final hb, hp st a mid ha]
  omega

theorem LockstepLabels.le_bind {α β : Type} {m n N : ℕ} {p : RunM C E RealSpec α}
    {k : α → RunM C E RealSpec β} (hp : LockstepLabels m p) (hk : ∀ a, LockstepLabels n (k a))
    (hN : m + n = N) : LockstepLabels N (p >>= k) :=
  hN ▸ hp.bind hk

theorem LockstepLabels.lift {α : Type} (q : PartyM C E RealSpec α) :
    LockstepLabels (C := C) 0 (StateT.lift q : RunM C E RealSpec α) := by
  intro st a final h
  rw [StateT.run_lift] at h
  obtain ⟨b, _, hb⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
    Prod.mk.injEq] at hb
  rw [hb.2]
  rfl

theorem LockstepLabels.foldlM {α β : Type} (n : ℕ) (f : α → β → RunM C E RealSpec α)
    (hf : ∀ a b, LockstepLabels n (f a b)) (xs : List β) (a : α) :
    LockstepLabels (xs.length * n) (xs.foldlM f a) := by
  induction xs generalizing a with
  | nil => simpa only [List.foldlM_nil, List.length_nil, Nat.zero_mul] using LockstepLabels.pure a
  | cons b xs ih =>
    simp only [List.foldlM_cons, List.length_cons]
    exact (hf a b).le_bind (fun a' => ih a') (by ring)

theorem lockstepLabels_prssRandomness {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (idx count : ℕ) : LockstepLabels 1 (prssRandomness (G := RealSpec) ctx codec idx count) := by
  intro st a final h
  have hr := prssRandomness_run (G := RealSpec) ctx codec idx count pure st
  rw [bind_pure] at hr
  rw [hr] at h
  obtain ⟨o, _, ho⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq] at ho
  rw [ho.2]
  rfl

theorem lockstepLabels_reshare {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (rnd : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    LockstepLabels 0 (reshare (G := RealSpec) K ctx codec rnd v count) := by
  intro st a final h
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run] at h
  obtain ⟨inbox, _, he⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
    Prod.mk.injEq] at he
  rw [he.2]
  rfl

theorem lockstepLabels_extendMult (ctx : Context C) (products : List (Product C E)) :
    LockstepLabels 1 ((realCheckGadgets (G := RealSpec) K ctx).extendMult products) :=
  (lockstepLabels_prssRandomness ctx _ _ _).le_bind (fun _ => lockstepLabels_reshare K ctx _ _ _ _) rfl

theorem lockstepLabels_coin (ctx : Context C) (count : ℕ) :
    LockstepLabels 1 ((realCheckGadgets (G := RealSpec) K ctx).coin count) :=
  (lockstepLabels_prssRandomness ctx _ _ _).le_bind (fun _ =>
    (LockstepLabels.lift _).le_bind (fun _ => LockstepLabels.pure _) rfl) rfl

theorem lockstepLabels_coinKey (ctx : Context C) :
    LockstepLabels 1 (coinKey K (realCheckGadgets (G := RealSpec) K ctx)) := by
  intro st a final h
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind] at h
  obtain ⟨⟨values, mid⟩, hv, hk⟩ := treeSimCheck_some_bind _ _ _ h
  rw [LockstepLabels.lift _ mid a final hk, lockstepLabels_coin K ctx 1 st values mid hv]

theorem lockstepLabels_challenge (ctx : Context C) :
    LockstepLabels 1 (challenge K (realCheckGadgets (G := RealSpec) K ctx)) := by
  unfold challenge
  refine (lockstepLabels_coinKey K ctx).le_bind (n := 0) (fun key => ?_) rfl
  intro st a final h
  rw [StateT.run_bind] at h
  obtain ⟨⟨r, mid⟩, hr, hk⟩ := treeSimCheck_some_bind _ _ _ h
  have hmid := LockstepLabels.lift _ st r mid hr
  rcases r with _ | r
  · simp only [StateT.run_lift, failure_bind] at hk
    simp at hk
  · simp only [StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at hk
    rw [hk.2, hmid]

theorem lockstepLabels_compareDigests (ctx : Context C) (salts : Shares C Bit) :
    LockstepLabels 0 (compareDigests (E := E) (G := RealSpec) ctx salts) := by
  intro st a final h
  rw [compareDigests_run] at h
  obtain ⟨_, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨_, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨_, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  rw [h.2]
  rfl

/-- The check of a batch takes `checkLabels` labels. -/
theorem lockstepLabels_check (ctx : Context C) (tuples : List (Tuple C)) :
    LockstepLabels (checkLabels (tuples.map (·.count)).sum)
      (check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples) := by
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by
    unfold halvings
    omega
  unfold check
  dsimp only
  split_ifs with hzero
  · rw [hzero]
    exact LockstepLabels.pure _
  have hl : checkLabels (tuples.map (·.count)).sum = 2 * halvings (tuples.map (·.count)).sum + 5 := by
    unfold checkLabels
    rw [if_neg hzero]
  rw [hl]
  generalize halvings (tuples.map (·.count)).sum = h at hs ⊢
  refine LockstepLabels.le_bind (m := 0) (n := 2 * h + 5) (LockstepLabels.pure _)
    (fun _ => ?_) (by omega)
  refine LockstepLabels.le_bind (m := 1) (n := 2 * h + 4) (lockstepLabels_coinKey K ctx)
    (fun key => ?_) (by omega)
  refine LockstepLabels.le_bind (m := 0) (n := 2 * h + 4) (LockstepLabels.lift _)
    (fun τ => ?_) (by omega)
  refine LockstepLabels.le_bind (m := 0) (n := 2 * h + 4) (LockstepLabels.lift _)
    (fun _ => ?_) (by omega)
  refine LockstepLabels.le_bind (m := (List.range sliceBits).length * 2) (n := 2 * (h - sliceBits) + 4)
    (LockstepLabels.foldlM 2 _ (fun x j => LockstepLabels.le_bind (m := 1) (n := 1)
      (lockstepLabels_extendMult K ctx _) (fun t => LockstepLabels.le_bind (m := 1) (n := 0)
        (lockstepLabels_challenge K ctx) (fun r => LockstepLabels.pure _) rfl) rfl) _ _)
    (fun x => ?_) (by simp only [List.length_range]; omega)
  refine LockstepLabels.le_bind (m := (List.range (h - sliceBits)).length * 2) (n := 4)
    (LockstepLabels.foldlM 2 _ (fun x j => LockstepLabels.le_bind (m := 1) (n := 1)
      (lockstepLabels_extendMult K ctx _) (fun t => LockstepLabels.le_bind (m := 1) (n := 0)
        (lockstepLabels_challenge K ctx) (fun r => LockstepLabels.pure _) rfl) rfl) _ _)
    (fun y => ?_) (by simp only [List.length_range]; omega)
  refine LockstepLabels.le_bind (m := 1) (n := 3) (lockstepLabels_prssRandomness ctx _ _ _)
    (fun w => ?_) rfl
  refine LockstepLabels.le_bind (m := 1) (n := 2) (lockstepLabels_extendMult K ctx _)
    (fun q => ?_) rfl
  refine LockstepLabels.le_bind (m := 1) (n := 1) (lockstepLabels_prssRandomness ctx _ _ _)
    (fun salts => ?_) rfl
  refine LockstepLabels.le_bind (m := 0) (n := 1) (lockstepLabels_compareDigests ctx _)
    (fun _ => ?_) rfl
  refine LockstepLabels.le_bind (m := 1) (n := 0) (lockstepLabels_challenge K ctx)
    (fun r => ?_) rfl
  exact LockstepLabels.le_bind (m := 0) (n := 0) (LockstepLabels.lift _)
    (fun _ => LockstepLabels.lift _) rfl

end Labels

section Batch

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (settings : Settings)

/-- One audited batch writes one record with its jobs and its start, and it moves the label by
`batchLabels` and the tag by one. -/
theorem lockstep_batchAudit (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (value : Option (List (List Bit))) (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ)
    (h : some ((value, records), final) ∈
      support ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial).run) :
    ∃ r, records = [r] ∧ r.jobs = jobs ∧ r.start = initial ∧
      final = (initial.1 + batchLabels circuits ctx.keys.parameter jobs, initial.2 + 1) := by
  rw [treeSimCheckBatchAudit_run_prefix] at h
  obtain ⟨data, hd, hf⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨-, hlabel, -, -, -⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs initial data hd
  have hcount : (data.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    unfold treeSimCheckBatchPrefix at hd
    obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ hd
    obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
    have he' : data = (inputs, q) := by simpa only [OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] using he
    subst data
    exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs initial.1 initial.2 q.1 q.2 hq
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify at hf
  obtain ⟨res, hres, hpure⟩ := treeSimCheck_some_bind _ _ _ hf
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
    Prod.mk.injEq] at hpure
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hpure
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  obtain ⟨⟨u, fin⟩, hcheck, hrest⟩ := treeSimCheck_some_bind _ _ _ hres
  obtain ⟨opened, _, he⟩ := treeSimCheck_some_bind _ _ _ hrest
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at he
  subst res
  have hl := lockstepLabels_check K ctx data.2.1.2 data.2.2 u fin hcheck
  rw [hcount, hlabel] at hl
  simp only [Prod.mk.injEq, and_true]
  rw [hl]
  unfold batchLabels
  omega

theorem lockstep_mapM_audit
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (js : List (List Job)) (L t : ℕ) (values : List (Option (List (List Bit))))
    (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((js.mapM (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run (L, t)).run
      (some ((values, records), final))) :
    records.length = js.length ∧
      (∀ k (hk : k < records.length), records[k].jobs = js.getD k [] ∧
        records[k].start = (L + lockstepStart circuits ctx.keys.parameter js k, t + k)) ∧
      final = (L + lockstepStart circuits ctx.keys.parameter js js.length, t + js.length) := by
  induction js generalizing L t values records final with
  | nil =>
    simp only [List.mapM_nil, WriterT.run_pure, StateT.run_pure, OptionT.run_pure] at h
    have he := Option.some.inj h.pure_inv
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, rfl⟩ := he
    simp [lockstepStart]
  | cons jobs js ih =>
    simp only [List.mapM_cons, WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
    obtain ⟨p, hp, hrest⟩ := h.option_bind_inv _ _ _
    obtain ⟨q, hq, he⟩ := hrest.option_map_inv _ _ _
    obtain ⟨q', hq', he'⟩ := hq.option_bind_inv _ _ _
    have he'' := Option.some.inj he'.pure_inv
    subst he''
    obtain ⟨r, hr, hjobs, hstart, hfinal⟩ :=
      lockstep_batchAudit circuits K settings ctx jobs (L, t) p.1.1 p.1.2 p.2
        hp.choose_spec.1.mem_support
    rw [hfinal] at hq'
    obtain ⟨hlen, hrec, hfin⟩ := ih _ _ q'.1.1 q'.1.2 q'.2 hq'
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, rfl⟩ := he
    rw [hr, List.empty_eq, List.append_nil]
    refine ⟨by simp only [List.length_cons, List.singleton_append, hlen], fun k hk => ?_, ?_⟩
    · cases k with
      | zero => simp [hjobs, hstart, lockstepStart]
      | succ k =>
        simp only [List.singleton_append, List.getElem_cons_succ]
        have hk' : k < q'.1.2.length := by simpa using hk
        obtain ⟨hj, hs⟩ := hrec k hk'
        refine ⟨by simpa using hj, ?_⟩
        rw [hs, lockstepStart_cons]
        simp only [Prod.mk.injEq]
        omega
    · rw [hfin, List.length_cons, lockstepStart_cons]
      simp only [Prod.mk.injEq]
      omega

theorem lockstep_batched_audit
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) (L t : ℕ) (value : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((batched settings.batchSize (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)
        jobs).run.run (L, t)).run (some ((value, records), final))) :
    let js := chunks settings.batchSize jobs
    records.length = js.length ∧
      (∀ k (hk : k < records.length), records[k].jobs = js.getD k [] ∧
        records[k].start = (L + lockstepStart circuits ctx.keys.parameter js k, t + k)) ∧
      final = (L + lockstepStart circuits ctx.keys.parameter js js.length, t + js.length) := by
  simp only [batched, WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
  obtain ⟨p, hp, hrest⟩ := h.option_bind_inv _ _ _
  obtain ⟨q, hq, he⟩ := hrest.option_map_inv _ _ _
  have hq' := Option.some.inj hq.pure_inv
  subst hq'
  simp only [Prod.mk.injEq] at he
  obtain ⟨⟨-, rfl⟩, rfl⟩ := he
  simpa [List.empty_eq] using lockstep_mapM_audit circuits K settings allowed ctx _ L t _ _ _ hp

theorem lockstep_writer_bind_inv {σ W α β : Type}
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    (p : WriterT (List W) (StateT σ (PartyM C E RealSpec)) α)
    (k : α → WriterT (List W) (StateT σ (PartyM C E RealSpec)) β) (s : σ) (b : β) (recs : List W)
    (f : σ) (h : TreeSimCheckAllowed allowed ((p >>= k).run.run s).run (some ((b, recs), f))) :
    ∃ a w mid w', TreeSimCheckAllowed allowed (p.run.run s).run (some ((a, w), mid)) ∧
      TreeSimCheckAllowed allowed ((k a).run.run mid).run (some ((b, w'), f)) ∧ recs = w ++ w' := by
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
  obtain ⟨x, hx, hrest⟩ := h.option_bind_inv _ _ _
  obtain ⟨y, hy, he⟩ := hrest.option_map_inv _ _ _
  simp only [Prod.mk.injEq] at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  exact ⟨x.1.1, x.1.2, x.2, y.1.2, hx, hy, rfl⟩

theorem lockstep_noRecords {σ W α : Type}
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {p : WriterT (List W) (StateT σ (PartyM C E RealSpec)) α}
    (hp : TreeSimCheckAuditAll allowed (fun _ => False) p) (s : σ) (a : α) (recs : List W) (f : σ)
    (h : TreeSimCheckAllowed allowed (p.run.run s).run (some ((a, recs), f))) : recs = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun r hr => hp s a recs f h r hr

theorem lockstep_lift_inv {σ W α : Type}
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    (q : PartyM C E RealSpec α) (s : σ) (a : α) (recs : List W) (f : σ)
    (h : TreeSimCheckAllowed allowed
      (((liftM (StateT.lift q : StateT σ (PartyM C E RealSpec) α) :
        WriterT (List W) (StateT σ (PartyM C E RealSpec)) α).run.run s).run) (some ((a, recs), f))) :
    recs = [] ∧ f = s := by
  simp only [WriterT.run_liftM, StateT.run_map, StateT.run_lift] at h
  obtain ⟨x, hx, he⟩ := h.option_map_inv _ _ _
  obtain ⟨y, -, hy⟩ := hx.option_bind_inv _ _ _
  have hy' := Option.some.inj hy.pure_inv
  subst hy'
  simp only [Prod.mk.injEq] at he
  exact ⟨he.1.2.symm, he.2.symm⟩

end Batch

section Run

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (settings : Settings)

/-- The lockstep on the reachable configurations of `TreeTwinDigestGoal`. Without a budget
collision in the log so far, the salts of the log lie at the batches below some `k₀`, and the
salts that the next round draws lie at the batches from `k₀`. The encoding is the one of the
second run, and any encoding before it. -/
def TreeLockstepStagesGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∀ n (a : TreeSimConfig A (TreeSimState C)),
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimHashBudgetCollision a.2.2 →
      ∃ (keys : C.Term → HashOutput) (enc : Encoding) (k₀ : ℕ),
        TreeLockstepSalts circuits keys parameter (lockstepChunks settings enc tree) 0 k₀ a.2.2 ∧
        ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
        ∀ l, u.2.2 = a.2.2 ++ l →
          TreeLockstepSalts circuits keys parameter (lockstepChunks settings enc tree) k₀
            (lockstepChunks settings enc tree).length l

/-- The half `TreeTwinDigestDraws` of `TreeTwinDigestDrawnGoal`, which the lockstep does not give. -/
def TreeTwinDigestDrawsGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∀ n (a : TreeSimConfig A (TreeSimState C)),
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
    ∀ l, u.2.2 = a.2.2 ++ l → TreeTwinDigestDraws l

/-- The conclusion of `TreeTwinDigestDrawnGoal` at a configuration with no budget collision.
`TreeTwinDigestDrawnGoal` assumes only `¬ TreeSimBad2`, which does not exclude a collision of
two `.sharedKeys` inputs of the setup. -/
theorem treeTwinDigestDrawn_of_lockstep (hbatch : 0 < settings.batchSize)
    (lockstep : TreeLockstepStagesGoal circuits prims K settings)
    (draws : TreeTwinDigestDrawsGoal circuits prims K settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit)
    (r : Unit × HashCache C) (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a)
    (good : ¬ TreeSimHashBudgetCollision a.2.2)
    (u : (A.State × (C.Party → Step C E RealSpec TreeOutput) × (C.Party → C.Party → Option (Msg E))) ×
      TreeSimState C)
    (hu : u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2))
    (l : TreeSimLog C) (hl : u.2.2 = a.2.2 ++ l) :
    TreeTwinDigestDrawn D a.2.2 l := by
  obtain ⟨keys, enc, k₀, before, round⟩ :=
    lockstep hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach good
  exact treeTwinDigestDrawn_of_draws_fresh D a.2.2 l
    (draws hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach u hu l hl)
    (treeTwinDigestFresh_of_lockstep circuits D keys parameter _ k₀ a.2.2 l before (round u hu l hl))

/-- The lockstep on the logged run after the PRSS setup. The end of the setup fixes the common term
keys. Each run after it with no budget collision has its salts at the common keys and at the salt
labels of the chunks of one encoding. -/
def TreeLockstepSaltRunGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ keys : C.Term → HashOutput,
      ∀ r ∈ support (treeSaltAfterSetup prims K circuits settings top tree D A x Z p),
        ¬ TreeSimHashBudgetCollision r.2 →
        ∃ (parameter : PublicParameter) (enc : Encoding),
          TreeLockstepSalts circuits keys parameter (lockstepChunks settings enc tree) 0
            (lockstepChunks settings enc tree).length r.2

/-- The second consumer link on the run. -/
theorem treeAgreementSaltRun_of_lockstep (lockstep : TreeLockstepSaltRunGoal circuits prims K settings) :
    TreeAgreementSaltRun prims K circuits settings := by
  intro hbatch top tree D A x z Z hx p hp
  obtain ⟨keys, hkeys⟩ := lockstep hbatch top tree D A x z Z hx p hp
  refine ⟨keys, fun r hr good => ?_⟩
  obtain ⟨parameter, enc, hsalts⟩ := hkeys r hr good
  refine ⟨lockstepSaltLabels circuits parameter (lockstepChunks settings enc tree), ?_,
    treeAgreementLog_of_lockstep circuits keys parameter _ r.2 hsalts⟩
  simp only [lockstepSaltLabels, List.length_map, List.length_range, lockstepChunks_length, le_refl]

/-- The batch records of one operator follow the chunks of one encoding, on every complete run of
its audited ceremony. This is a fact of one operator, with no collision guard. -/
def TreeLockstepRecordsGoal : Prop :=
  ∀ (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree) (value : Option TreeOutput)
    (records : List (TreeSimCheckBatchRecord C)) (final : ℕ × ℕ),
    TreeSimCheckAllowed allowed
      ((treeSimCheckCeremonyAuditBody K circuits settings ctx top tree).run.run (0, 0)).run
      (some ((value, records), final)) →
    ∃ enc : Encoding,
      TreeLockstepRecords circuits ctx.keys.parameter (lockstepChunks settings enc tree) records

/-- The honest operators of an audited run with no budget collision have records that follow the
chunks of one common encoding. It needs `TreeLockstepRecordsRunGoal`, `TreeLockstepOpenedGoal`, and
that the encoding of the second run is a function of the opened outputs of the first run. -/
def TreeLockstepRecordsAgreeGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)),
    ¬ TreeSimHashBudgetCollision r.2 →
    ∃ (parameter : PublicParameter) (enc : Encoding), ∀ i, i ∉ D.1 → ∀ value records,
      r.1.2.2 i = some (value, records) →
      TreeLockstepRecords circuits parameter (lockstepChunks settings enc tree) records

/-- The bridge from `TreeLockstepRecordsGoal` to the audited logged run. Each honest operator with
an output has records that follow the chunks of one encoding. -/
def TreeLockstepRecordsRunGoal : Prop :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput),
    ∀ r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)),
    ∀ i, i ∉ D.1 → ∀ value records, r.1.2.2 i = some (value, records) →
      ∃ enc : Encoding, TreeLockstepRecords circuits (x i).parameter (lockstepChunks settings enc tree) records

/-- The honest operators of an audited run with no budget collision open the same outputs in each
batch that both record. -/
def TreeLockstepOpenedGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)),
    ¬ TreeSimHashBudgetCollision r.2 →
    ∀ i j, i ∉ D.1 → j ∉ D.1 → ∀ vi ri vj rj, r.1.2.2 i = some (vi, ri) → r.1.2.2 j = some (vj, rj) →
      ∀ k (hi : k < ri.length) (hj : k < rj.length), ri[k].outputs = rj[k].outputs

/-- The batch records of one operator follow the chunks of one encoding. -/
theorem treeLockstepRecords_audit : TreeLockstepRecordsGoal circuits K settings := by
  intro allowed ctx top tree value records final h
  unfold treeSimCheckCeremonyAuditBody ceremonyOutput at h
  cases tree with
  | top =>
    dsimp only at h
    obtain ⟨o, w, mid, w', hfirst, hrest, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ h
    have hnil : w' = [] := by
      refine lockstep_noRecords ?_ _ _ _ _ hrest
      rcases o with _ | outputs
      · exact .pure _ _ _
      · exact (TreeSimCheckAuditAll.lift _ _ _).bind fun _ => .pure _ _ _
    obtain ⟨hlen, hrec, -⟩ := lockstep_batched_audit circuits K settings allowed ctx _ 0 0 _ _ _ hfirst
    refine ⟨fun _ => digit 0, ?_, fun k hk => ?_⟩
    · simp only [hnil, List.append_nil, hlen, lockstepChunks, le_refl]
    · simp only [hnil, List.append_nil] at hk ⊢
      simpa only [Nat.zero_add, lockstepChunks] using hrec k hk
  | bottom b =>
    dsimp only at h
    obtain ⟨o, w, mid, w', hfirst, hrest, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ h
    obtain ⟨hlen, hrec, hmid⟩ := lockstep_batched_audit circuits K settings allowed ctx _ 0 0 _ _ _ hfirst
    simp only [Nat.zero_add] at hrec hmid
    have first : ∀ enc, w' = [] → ∃ enc' : Encoding,
        TreeLockstepRecords circuits ctx.keys.parameter (lockstepChunks settings enc' (.bottom b)) (w ++ w') :=
      fun enc hnil => ⟨enc, treeLockstepRecords_append circuits ctx.keys.parameter _ _ w w' hlen hrec
        (by simp [hnil]) (by simp [hnil])⟩
    rcases o with _ | outputs
    · exact first (fun _ => digit 0) (lockstep_noRecords (.pure _ _ _) _ _ _ _ hrest)
    dsimp only at hrest
    obtain ⟨root, w₁, mid₁, w₁', h₁, hrest₁, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest
    obtain ⟨rfl, rfl⟩ := lockstep_lift_inv _ _ _ _ _ h₁
    obtain ⟨base, w₂, mid₂, w₂', h₂, hrest₂, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest₁
    obtain ⟨rfl, rfl⟩ := lockstep_lift_inv _ _ _ _ _ h₂
    obtain ⟨g, w₃, mid₃, w₃', h₃, hrest₃, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest₂
    obtain ⟨rfl, rfl⟩ := lockstep_lift_inv _ _ _ _ _ h₃
    simp only [List.nil_append]
    rcases g with _ | ⟨randomness, enc⟩
    · exact first (fun _ => digit 0) (lockstep_noRecords (.pure _ _ _) _ _ _ _ hrest₃)
    dsimp only at hrest₃
    obtain ⟨o', w₄, mid₄, w₄', h₄, hrest₄, rfl⟩ := lockstep_writer_bind_inv _ _ _ _ _ _ hrest₃
    have hnil : w₄' = [] := by
      refine lockstep_noRecords ?_ _ _ _ _ hrest₄
      rcases o' with _ | values
      · exact .pure _ _ _
      · exact (TreeSimCheckAuditAll.lift _ _ _).bind fun _ =>
          (TreeSimCheckAuditAll.lift _ _ _).bind fun _ => by
            split_ifs
            · exact .pure _ _ _
            · exact .pure _ _ _
    rw [hmid] at h₄
    obtain ⟨hlen₄, hrec₄, -⟩ := lockstep_batched_audit circuits K settings allowed ctx _ _ _ _ _ _ h₄
    refine ⟨enc, ?_⟩
    rw [hnil, List.append_nil]
    exact treeLockstepRecords_append circuits ctx.keys.parameter _ _ w w₄ hlen hrec hlen₄.le hrec₄

end Run

/-- info: 'ThresholdLeanXmssSecurity.treeTwinDigestDrawn_of_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinDigestDrawn_of_lockstep

/-- info: 'ThresholdLeanXmssSecurity.treeAgreementSaltRun_of_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeAgreementSaltRun_of_lockstep

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecords_common' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecords_common

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecords_audit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecords_audit

end ThresholdLeanXmssSecurity
