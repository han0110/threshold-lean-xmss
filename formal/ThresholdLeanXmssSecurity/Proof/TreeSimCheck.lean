import ThresholdLeanXmssSecurity.Proof.TreeSim
import ThresholdLeanXmssSecurity.Proof.CheckSound

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

/-
Open target: treeSimCheckBoundClosed : TreeSimCheckBoundGoal prims K circuits settings.
treeSimCheck_contextual proves the full hybrid check bound from a shared cache,
including split histories, with checkErrorOf and no hash error. Its counted
prefix allowance is now (2 * halvings counts.sum + 5) * step.
treeSimCheckAuditedGame records the actual batch inputs, tuples, pre-check
RunState and outputs. Its erasure preserves the complete original world log.
treeSimWrongOutput_audited_first_index selects an incorrect emitted batch with
a correct prefix and index below treeBatches, after identifying the ghost
witness with the actual successful audited output by replay prefix uniqueness.
The reference retains both the ghost dealer and that same audited replay.
treeSimCheck_indexed_union proves the cover by fixed actual batch events.
treeSimCheckBatchAudit_phase_split exposes the joint pre-check boundary of
the actual batch, preserving all queries and ordered continuations.
treeSimCheckBeforeVerify_state and _joint derive its history, label, tag,
tuple counts and modes from the real circuit prefix.
treeSimCheckBatchAudit_replay_live now cuts the supplied joint execution log
into the prefix, restart, and suffix. Actual abort propagation proves that
every honest prefix succeeded whenever any continuation succeeds.
treeSimCheckBatchPrefix_joint derives every honest checkpoint's fields from
that same prefix, including the actual input-query portion of the batch.
TreeSimCheckAuditedReference.records derives the batch subexecution for every
emitted record. treeSimCheck_indexed_bad_checkpoint ties the indexed bad
record to that subexecution and proves its tuple-count sum is nonzero.
treeSimCheck_elementDraw_fresh decodes actual fresh hidden streams jointly
with both caches. treeSimCheck_coin_scheduled normalizes a complete rushing
Coin round, with arbitrary other term copies and arbitrary continuations.
Deferred sampling is now proved for arbitrary adaptive world programs:
treeSimCheck_world_presample_table retains the actual returned value and
final hash cache. treeSimCheck_world_unread_table removes consumed cache
positions using a zero-query bound. Named field rows normalize jointly,
including repeated honest-holder reads and the exact field-codec padding.
treeSimCheck_coin_fields_scheduled gives the actual rushing Coin round an
independent uniform public value, retaining aborts and the handler state.
TreeSimCheckRunFuture and treeSimCheckRunFuture_realCheck prove that the
entire real check uses increasing labels. treeSimCheck_rounds_unread carries
the resulting no-reread fact through the actual scheduler. Consequently,
treeSimCheck_real_check_first_fields normalizes the first Coin of the whole
real check, with no assumed draw distribution or no-reread premise. Its
concrete boundary premises are: common PRSS keys, cached visible AES keys,
a common label with TreeSimFutureEmpty, and positive honest tuple counts.
The next probabilistic steps are the later ExtendMult/randElements/randBits
transports, then the contextual GS20 induction. Common setup keys still must
be obtained or their failure handled within the fixed check allowance.
Closure still requires indexedBounds in treeSimCheckBound_of_indexedBounds.
The remaining probability argument must connect each indexed event to its
joint batch boundary, derive TupleInputs, stream freshness and the shared
cache/query-budget invariants, and transport the whole real check (including
ExtendMult and salted digests) to the contextual bound. The proved scheduler
split is an exact program equality; it is not that distributional transport.
In particular, absence of TreeSimHashBad does not itself assert setup-key
consistency: commit and sharedKeys are outside TreeSimHashDomain. This branch
must be handled within the fixed check allowance, not by adding a hash error.
No counterexample has been established.
-/

section Replay

/-- A complete sequence of query answers of the given program. -/
inductive TreeSimCheckReplay {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} :
    OracleComp spec α → List ((t : spec.Domain) × spec.Range t) → α → Prop
  | pure (a : α) : TreeSimCheckReplay (pure a) [] a
  | query (t : spec.Domain) (k : spec.Range t → OracleComp spec α)
      (u : spec.Range t) (log : List ((t : spec.Domain) × spec.Range t)) (a : α) :
      TreeSimCheckReplay (k u) log a →
      TreeSimCheckReplay (OracleComp.queryBind t k) (⟨t, u⟩ :: log) a

theorem treeSimCheckReplay_supported {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C)
    (a : α) (log : TreeSimLog C) (s' : HashCache C × HiddenCache C)
    (h : ((a, log), s') ∈ support
      ((simulateQ ((streamWorld prims D).withTraceAppend
        (fun t u => ([⟨t, u⟩] : TreeSimLog C))) p).run.run s)) :
    TreeSimCheckReplay p log a := by
  induction p using OracleComp.inductionOn generalizing s a log s' with
  | pure b =>
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact .pure _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query,
      QueryImpl.withTraceAppend_apply, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, StateT.run_bind, StateT.run_map,
      bind_map_left, pure_bind, bind_assoc, Functor.map_map,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨⟨u, next⟩, _, ⟨⟨b, tail⟩, final⟩, hb, he⟩ := h
    cases he
    exact .query t k u tail b (ih u next b tail final hb)

theorem TreeSimCheckReplay.prefix_unique {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {p : OracleComp spec α} {left right : List ((t : spec.Domain) × spec.Range t)}
    {a b : α} (ha : TreeSimCheckReplay p left a) (hb : TreeSimCheckReplay p right b)
    (hp : left <+: right) : a = b ∧ left = right := by
  induction ha generalizing right b with
  | pure a => cases hb; exact ⟨rfl, rfl⟩
  | query t k u log a h ih =>
    cases hb with
    | query _ _ v tail _ hv =>
      obtain ⟨rest, hrest⟩ := hp
      simp only [List.cons_append, List.cons.injEq, Sigma.mk.inj_iff,
        heq_eq_eq, true_and] at hrest
      obtain ⟨rfl, htail⟩ := hrest
      obtain ⟨rfl, rfl⟩ := ih hv ⟨rest, htail⟩
      exact ⟨rfl, rfl⟩

theorem TreeSimCheckReplay.common_prefix_unique {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {p : OracleComp spec α} {left right log : List ((t : spec.Domain) × spec.Range t)}
    {a b : α} (ha : TreeSimCheckReplay p left a) (hb : TreeSimCheckReplay p right b)
    (hl : left <+: log) (hr : right <+: log) : a = b ∧ left = right := by
  rcases List.prefix_or_prefix_of_prefix hl hr with h | h
  · exact ha.prefix_unique hb h
  · obtain ⟨hab, hlog⟩ := hb.prefix_unique ha h
    exact ⟨hab.symm, hlog.symm⟩

theorem TreeSimCheckReplay.bind_inv {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (p : OracleComp spec α) (k : α → OracleComp spec β)
    {log : List ((t : spec.Domain) × spec.Range t)} {b : β}
    (h : TreeSimCheckReplay (p >>= k) log b) :
    ∃ a pre post, TreeSimCheckReplay p pre a ∧ TreeSimCheckReplay (k a) post b ∧
      log = pre ++ post := by
  induction p using OracleComp.inductionOn generalizing log b with
  | pure a =>
    simp only [pure_bind] at h
    exact ⟨a, [], log, .pure a, h, rfl⟩
  | query_bind t f ih =>
    simp only [bind_assoc] at h
    change TreeSimCheckReplay (OracleComp.queryBind t (fun u => f u >>= k)) log b at h
    cases h with
    | query _ _ u tail _ ht =>
      obtain ⟨a, pre, post, hp, hk, rfl⟩ := ih u ht
      exact ⟨a, ⟨t, u⟩ :: pre, post, .query t f u pre a hp, hk, rfl⟩

theorem TreeSimCheckReplay.mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {p : OracleComp spec α} {log : List ((t : spec.Domain) × spec.Range t)} {a : α}
    (h : TreeSimCheckReplay p log a) : a ∈ support p := by
  induction h with
  | pure a => simp
  | query t k u log a h ih =>
    change a ∈ support (HasQuery.query t >>= k)
    simp only [support_bind, Set.mem_iUnion]
    exact ⟨u, by simp, ih⟩

theorem treeSimCheckReplay_of_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : OracleComp spec α) (a : α) (h : a ∈ support p) :
    ∃ log, TreeSimCheckReplay p log a := by
  induction p using OracleComp.inductionOn with
  | pure b =>
    have he : a = b := by simpa using h
    subst a
    exact ⟨[], .pure b⟩
  | query_bind t k ih =>
    obtain ⟨u, _, hu⟩ := (mem_support_bind_iff _ _ _).mp h
    obtain ⟨log, hr⟩ := ih u hu
    exact ⟨⟨t, u⟩ :: log, .query t k u log a hr⟩

theorem TreeSimCheckReplay.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {p : OracleComp spec α} {k : α → OracleComp spec β}
    {pre post : List ((t : spec.Domain) × spec.Range t)} {a : α} {b : β}
    (hp : TreeSimCheckReplay p pre a) (hk : TreeSimCheckReplay (k a) post b) :
    TreeSimCheckReplay (p >>= k) (pre ++ post) b := by
  induction hp with
  | pure a => simpa only [pure_bind, List.nil_append] using hk
  | query t f u log a hp ih =>
    change TreeSimCheckReplay (OracleComp.queryBind t (fun v => f v >>= k)) _ b
    exact .query t _ u _ b (ih hk)

/-- A complete replay whose answers satisfy the specified constraints. -/
def TreeSimCheckAllowed {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (p : OracleComp spec α) (a : α) : Prop :=
  ∃ log, TreeSimCheckReplay p log a ∧ ∀ t u, (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) ∈ log → allowed t u

theorem TreeSimCheckAllowed.pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (a : α) :
    TreeSimCheckAllowed allowed (Pure.pure a) a := ⟨[], .pure a, by simp⟩

theorem TreeSimCheckAllowed.bind_inv {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {p : OracleComp spec α}
    {f : α → OracleComp spec β} {b : β} (h : TreeSimCheckAllowed allowed (p >>= f) b) :
    ∃ a, TreeSimCheckAllowed allowed p a ∧ TreeSimCheckAllowed allowed (f a) b := by
  obtain ⟨log, hr, ha⟩ := h
  obtain ⟨a, pre, post, hp, hf, rfl⟩ := hr.bind_inv p f
  exact ⟨a, ⟨pre, hp, fun t u hu => ha t u (List.mem_append_left post hu)⟩,
    ⟨post, hf, fun t u hu => ha t u (List.mem_append_right pre hu)⟩⟩

theorem TreeSimCheckAllowed.option_bind_inv {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    (p : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β)
    (b : β) (h : TreeSimCheckAllowed allowed (p >>= f).run (some b)) :
    ∃ a, TreeSimCheckAllowed allowed p.run (some a) ∧
      TreeSimCheckAllowed allowed (f a).run (some b) := by
  obtain ⟨log, hr, ha⟩ := h
  simp only [OptionT.run_bind] at hr
  obtain ⟨a, pre, post, hp, hf, rfl⟩ := hr.bind_inv _ _
  cases a with
  | none => cases hf
  | some a =>
    exact ⟨a, ⟨pre, hp, fun t u hu => ha t u (List.mem_append_left post hu)⟩,
      ⟨post, hf, fun t u hu => ha t u (List.mem_append_right pre hu)⟩⟩

theorem TreeSimCheckAllowed.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    {p : OracleComp spec α} {f : α → OracleComp spec β} {a : α} {b : β}
    (hp : TreeSimCheckAllowed allowed p a) (hf : TreeSimCheckAllowed allowed (f a) b) :
    TreeSimCheckAllowed allowed (p >>= f) b := by
  obtain ⟨pre, hp, hap⟩ := hp
  obtain ⟨post, hf, haf⟩ := hf
  refine ⟨pre ++ post, hp.bind hf, ?_⟩
  intro t u hu
  exact (List.mem_append.mp hu).elim (hap t u) (haf t u)

theorem TreeSimCheckAllowed.option_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    {p : OptionT (OracleComp spec) α} {f : α → OptionT (OracleComp spec) β} {a : α} {b : β}
    (hp : TreeSimCheckAllowed allowed p.run (some a))
    (hf : TreeSimCheckAllowed allowed (f a).run (some b)) :
    TreeSimCheckAllowed allowed (p >>= f).run (some b) := by
  simp only [OptionT.run_bind]
  exact hp.bind hf

theorem TreeSimCheckAllowed.pure_inv {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {a b : α}
    (h : TreeSimCheckAllowed allowed (Pure.pure a) b) : b = a := by
  obtain ⟨_, hr, _⟩ := h
  cases hr
  rfl

theorem TreeSimCheckAllowed.query_inv {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} (t : spec.Domain)
    (u : spec.Range t) (h : TreeSimCheckAllowed allowed (OracleComp.lift (OracleSpec.query t)) u) :
    allowed t u := by
  obtain ⟨_, hr, ha⟩ := h
  cases hr with
  | query _ _ v log _ hr =>
    cases hr
    exact ha t v (by simp)

theorem TreeSimCheckAllowed.option_map_inv {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    (f : α → β) (p : OptionT (OracleComp spec) α) (b : β)
    (h : TreeSimCheckAllowed allowed (f <$> p).run (some b)) :
    ∃ a, TreeSimCheckAllowed allowed p.run (some a) ∧ f a = b := by
  rw [map_eq_bind_pure_comp] at h
  obtain ⟨a, ha, hb⟩ := h.option_bind_inv _ _ _
  exact ⟨a, ha, (Option.some.inj hb.pure_inv).symm⟩

theorem TreeSimCheckAllowed.query {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) (u : spec.Range t) (a : α)
    (hu : allowed t u) (hk : TreeSimCheckAllowed allowed (k u) a) :
    TreeSimCheckAllowed allowed (OracleComp.queryBind t k) a := by
  obtain ⟨log, hr, ha⟩ := hk
  refine ⟨⟨t, u⟩ :: log, .query t k u log a hr, ?_⟩
  intro t' u' hm
  rcases List.mem_cons.mp hm with he | he
  · cases he; exact hu
  · exact ha t' u' he

theorem TreeSimCheckAllowed.simulate_inv {ι κ : Type} {S : OracleSpec.{0, 0} ι}
    {T : OracleSpec.{0, 0} κ} {α : Type}
    (impl : QueryImpl S (OracleComp T))
    (allowed : (t : T.Domain) → T.Range t → Prop)
    (source : (t : S.Domain) → S.Range t → Prop)
    (query : ∀ t u, TreeSimCheckAllowed allowed (impl t) u → source t u)
    (p : OracleComp S α) (a : α)
    (h : TreeSimCheckAllowed allowed (simulateQ impl p) a) :
    TreeSimCheckAllowed source p a := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b =>
    obtain ⟨log, hr, _⟩ := h
    simp only [simulateQ_pure] at hr
    cases hr
    exact .pure source b
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query] at h
    obtain ⟨u, hu, hk⟩ := h.bind_inv
    obtain ⟨log, hr, ha⟩ := ih u a hk
    refine ⟨⟨t, u⟩ :: log, .query t k u log a hr, ?_⟩
    intro t' u' hmem
    rcases List.mem_cons.mp hmem with he | he
    · cases he
      exact query t u hu
    · exact ha t' u' he

/-- The first mismatch is a subexecution of this replay, with all earlier
results and all three log segments retained. -/
theorem TreeSimCheckReplay.mapM_first {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α β : Type} (f : α → OracleComp spec β) (expected : α → β)
    (xs : List α) (values : List β) (log : List ((t : spec.Domain) × spec.Range t))
    (h : TreeSimCheckReplay (xs.mapM f) log values)
    (hne : values ≠ xs.map expected) :
    ∃ before a after value tail pre mid post,
      xs = before ++ a :: after ∧
      values = before.map expected ++ value :: tail ∧ value ≠ expected a ∧
      TreeSimCheckReplay (before.mapM f) pre (before.map expected) ∧
      TreeSimCheckReplay (f a) mid value ∧
      TreeSimCheckReplay (after.mapM f) post tail ∧ log = pre ++ mid ++ post := by
  classical
  induction xs generalizing values log with
  | nil =>
    simp only [List.mapM_nil] at h
    cases h
    exact (hne rfl).elim
  | cons a xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨value, mid, rest, hv, ht, rfl⟩ := h.bind_inv (f a) _
    obtain ⟨tail, post, final, htail, hf, rfl⟩ := ht.bind_inv (xs.mapM f) _
    cases hf
    simp only [List.append_nil]
    rcases Classical.em (value = expected a) with he | he
    · have hn : tail ≠ xs.map expected := by
        intro ht
        exact hne (by simp only [List.map_cons, he, ht])
      obtain ⟨before, b, after, value', tail', pre', mid', post', hx, hy, hn,
        hp, hm, ht', hl⟩ := ih tail post htail hn
      refine ⟨a :: before, b, after, value', tail', mid ++ pre', mid', post',
        by simp only [List.cons_append, hx], ?_, hn, ?_, hm, ht', ?_⟩
      · simp only [List.map_cons, List.cons_append, he, hy]
      · simp only [List.mapM_cons, List.map_cons]
        apply hv.bind
        simpa only [he, List.append_nil] using
          (TreeSimCheckReplay.bind (k := fun tail => Pure.pure (value :: tail)) hp
            (.pure (value :: before.map expected)))
      · simp only [hl, List.append_assoc]
    · exact ⟨[], a, xs, value, tail, [], mid, post, rfl, rfl, he, .pure [], hv, htail, rfl⟩

end Replay

private theorem treeSimCheck_fold_success {α : Type} (batches : List (Option (List α)))
    (acc out : List α)
    (h : batches.foldlM (fun acc batch => batch.map (acc ++ ·)) acc = some out) :
    ∃ values : List (List α), batches = values.map some ∧ out = acc ++ values.flatten := by
  induction batches generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact ⟨[], rfl, by simpa using h.symm⟩
  | cons batch batches ih =>
    cases batch with
    | none => simp at h
    | some batch =>
      simp only [List.foldlM_cons, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨values, hv, ho⟩ := ih (acc ++ batch) h
      exact ⟨batch :: values, by simp only [List.map_cons, hv],
        by simpa only [List.flatten_cons, List.append_assoc] using ho⟩

/-- A successful incorrect batched run has a first successful incorrect batch
in this very replay. Its index is bounded by the number of scheduled batches. -/
theorem treeSimCheckReplay_batched_first {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (size : ℕ) (run : List Job → OracleComp spec (Option (List (List Bit))))
    (expected : List Job → List (List Bit)) (jobs : List Job)
    (out : List (List Bit)) (log : List ((t : spec.Domain) × spec.Range t))
    (h : TreeSimCheckReplay (batched size run jobs) log (some out))
    (hne : out ≠ ((chunks size jobs).map expected).flatten) :
    ∃ before batch after value tail pre mid post,
      chunks size jobs = before ++ batch :: after ∧
      before.length < (chunks size jobs).length ∧
      TreeSimCheckReplay (before.mapM run) pre (before.map (some ∘ expected)) ∧
      TreeSimCheckReplay (run batch) mid (some value) ∧ value ≠ expected batch ∧
      TreeSimCheckReplay (after.mapM run) post tail ∧ log = pre ++ mid ++ post := by
  unfold batched at h
  obtain ⟨values, pre, final, hv, hf, rfl⟩ := h.bind_inv _ _
  have ho := hf.mem_support
  simp only [support_pure, Set.mem_singleton_iff] at ho
  have hh : values.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some out := ho.symm
  obtain ⟨actual, ha, hout⟩ := treeSimCheck_fold_success values [] out hh
  have hn : values ≠ (chunks size jobs).map (some ∘ expected) := by
    intro he
    rw [he] at hh
    have heq := foldlM_some_append ((chunks size jobs).map expected) []
    simp only [List.map_map, Function.comp_def, List.nil_append] at heq
    simp only [Function.comp_def] at hh
    rw [heq] at hh
    exact hne (Option.some.inj hh).symm
  obtain ⟨before, batch, after, value, tail, pre', mid, post, hx, hy, hn, hp, hm, ht, hl⟩ :=
    hv.mapM_first run (some ∘ expected) _ _ _ hn
  have hmval : value ∈ actual.map some := by
    rw [← ha, hy]
    exact List.mem_append_right _ (List.mem_cons_self)
  obtain ⟨value', _, rfl⟩ := List.mem_map.mp hmval
  refine ⟨before, batch, after, value', tail, pre', mid, post, hx, ?_, hp, hm,
    fun he => hn (congrArg some he), ht, ?_⟩
  · rw [hx, List.length_append, List.length_cons]
    omega
  · rw [hh] at hf
    cases hf
    simpa only [List.append_nil] using hl

/-- First incorrect result through the actual state and abort transformers.
The prefix returns its correct results and the entry state of the failing
batch; every query in both witnesses is still constrained by `allowed`. -/
theorem treeSimCheck_state_mapM_first {ι α β σ : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop)
    (f : α → StateT σ (OptionT (OracleComp spec)) β) (expected : α → β)
    (xs : List α) (values : List β) (initial final : σ)
    (h : TreeSimCheckAllowed allowed ((xs.mapM f).run initial).run (some (values, final)))
    (hne : values ≠ xs.map expected) :
    ∃ before a after value tail entry next,
      xs = before ++ a :: after ∧ values = before.map expected ++ value :: tail ∧
      value ≠ expected a ∧
      TreeSimCheckAllowed allowed ((before.mapM f).run initial).run (some (before.map expected, entry)) ∧
      TreeSimCheckAllowed allowed ((f a).run entry).run (some (value, next)) ∧
      TreeSimCheckAllowed allowed ((after.mapM f).run next).run (some (tail, final)) := by
  induction xs generalizing values initial final with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, OptionT.run_pure] at h
    have he := Option.some.inj h.pure_inv
    exact (hne (congrArg Prod.fst he)).elim
  | cons a xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨head, hh, hrest⟩ := h.option_bind_inv _ _ _
    obtain ⟨tail, ht, he⟩ := hrest.option_bind_inv _ _ _
    have he := Option.some.inj he.pure_inv
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rcases Classical.em (head.1 = expected a) with heq | heq
    · have hn : tail.1 ≠ xs.map expected := by
        intro he
        exact hne (by simp only [List.map_cons, heq, he])
      obtain ⟨before, b, after, value, rest, entry, next, hx, hy, hn, hp, hm, hs⟩ :=
        ih tail.1 head.2 tail.2 ht hn
      refine ⟨a :: before, b, after, value, rest, entry, next,
        by simp only [List.cons_append, hx], ?_, hn, ?_, hm, hs⟩
      · simp only [List.map_cons, List.cons_append, heq, hy]
      · simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, List.map_cons]
        apply TreeSimCheckAllowed.option_bind hh
        apply TreeSimCheckAllowed.option_bind hp
        simpa only [heq, OptionT.run_pure] using
          (TreeSimCheckAllowed.pure allowed (some (head.1 :: before.map expected, entry)))
    · exact ⟨[], a, xs, head.1, tail.1, initial, head.2, rfl, rfl, heq,
        by simpa only [List.mapM_nil, List.map_nil, StateT.run_pure, OptionT.run_pure] using
          TreeSimCheckAllowed.pure allowed (some ([], initial)), hh, ht⟩

theorem treeSimCheck_state_batched_first {ι σ : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (size : ℕ)
    (run : List Job → StateT σ (OptionT (OracleComp spec)) (Option (List (List Bit))))
    (expected : List Job → List (List Bit)) (jobs : List Job)
    (out : List (List Bit)) (initial final : σ)
    (h : TreeSimCheckAllowed allowed ((batched size run jobs).run initial).run (some (some out, final)))
    (hne : out ≠ ((chunks size jobs).map expected).flatten) :
    ∃ before batch after value tail entry next,
      chunks size jobs = before ++ batch :: after ∧
      before.length < (chunks size jobs).length ∧
      TreeSimCheckAllowed allowed ((before.mapM run).run initial).run
        (some (before.map (some ∘ expected), entry)) ∧
      TreeSimCheckAllowed allowed ((run batch).run entry).run (some (some value, next)) ∧
      value ≠ expected batch ∧
      TreeSimCheckAllowed allowed ((after.mapM run).run next).run (some (tail, final)) := by
  unfold batched at h
  simp only [StateT.run_bind, StateT.run_pure] at h
  obtain ⟨values, hv, hf⟩ := h.option_bind_inv _ _ _
  have he := Option.some.inj hf.pure_inv
  have hh := (congrArg Prod.fst he).symm
  have hstate : final = values.2 := congrArg Prod.snd he
  obtain ⟨actual, ha, hout⟩ := treeSimCheck_fold_success values.1 [] out hh
  have hn : values.1 ≠ (chunks size jobs).map (some ∘ expected) := by
    intro he
    rw [he] at hh
    have heq := foldlM_some_append ((chunks size jobs).map expected) []
    simp only [List.map_map, Function.comp_def, List.nil_append] at heq
    simp only [Function.comp_def] at hh
    rw [heq] at hh
    exact hne (Option.some.inj hh).symm
  obtain ⟨before, batch, after, value, tail, entry, next, hx, hy, hn, hp, hm, ht⟩ :=
    treeSimCheck_state_mapM_first allowed run (some ∘ expected) _ _ initial values.2 hv hn
  have hmval : value ∈ actual.map some := by
    rw [← ha, hy]
    exact List.mem_append_right _ (List.mem_cons_self)
  obtain ⟨value', _, rfl⟩ := List.mem_map.mp hmval
  refine ⟨before, batch, after, value', tail, entry, next, hx, ?_, hp, hm,
    fun he => hn (congrArg some he), ?_⟩
  · rw [hx, List.length_append, List.length_cons]
    omega
  · simpa only [hstate] using ht

theorem treeSimCheck_state_mapM_some {ι α β σ : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop)
    (f : α → StateT σ (OptionT (OracleComp spec)) (Option β)) (xs : List α)
    (hsome : ∀ x ∈ xs, ∀ initial value final,
      TreeSimCheckAllowed allowed ((f x).run initial).run (some (value, final)) → value.isSome)
    (values : List (Option β)) (initial final : σ)
    (h : TreeSimCheckAllowed allowed ((xs.mapM f).run initial).run (some (values, final))) :
    ∃ outputs : List β, values = outputs.map some := by
  induction xs generalizing values initial final with
  | nil =>
    have he : some (values, final) = some ([], initial) := h.pure_inv
    exact ⟨[], congrArg Prod.fst (Option.some.inj he)⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨head, hh, hrest⟩ := h.option_bind_inv _ _ _
    obtain ⟨tail, ht, he⟩ := hrest.option_bind_inv _ _ _
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp (hsome x (by simp) _ _ _ hh)
    obtain ⟨outputs, ho⟩ := ih (fun y hy => hsome y (List.mem_cons_of_mem x hy)) tail.1 head.2 tail.2 ht
    refine ⟨out :: outputs, ?_⟩
    have hv := congrArg Prod.fst (Option.some.inj he.pure_inv)
    simpa only [List.map_cons, hout, ho] using hv

theorem treeSimCheck_state_batched_some {ι σ : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (size : ℕ)
    (f : List Job → StateT σ (OptionT (OracleComp spec)) (Option (List (List Bit))))
    (jobs : List Job)
    (hsome : ∀ batch ∈ chunks size jobs, ∀ initial value final,
      TreeSimCheckAllowed allowed ((f batch).run initial).run (some (value, final)) → value.isSome)
    (value : Option (List (List Bit))) (initial final : σ)
    (h : TreeSimCheckAllowed allowed ((batched size f jobs).run initial).run (some (value, final))) :
    ∃ outputs, value = some outputs := by
  simp only [batched, StateT.run_bind, StateT.run_pure] at h
  obtain ⟨p, hp, he⟩ := h.option_bind_inv _ _ _
  obtain ⟨outputs, ho⟩ := treeSimCheck_state_mapM_some allowed f (chunks size jobs) hsome _ _ _ hp
  have hv := congrArg Prod.fst (Option.some.inj he.pure_inv)
  refine ⟨outputs.flatten, ?_⟩
  simpa only [ho, foldlM_some_append, List.nil_append] using hv

/-- Tree assembly transports any relation preserved by pure and bind. The
reference and real run use the same adaptive signing jobs. -/
def TreeSimCheckRunJobs (tree : Tree) (jobs : List Job) : Prop :=
  match tree with
  | .top => jobs = topJobs
  | .bottom b => jobs = bottomJobs b ∨ ∃ encoding, jobs = signJobs b encoding

theorem treeSimCheck_ceremony_rel {m : Type → Type} [Monad m]
    (R : ∀ {α : Type}, m α → α → Prop)
    (hpure : ∀ {α : Type} (a : α), R (pure a) a)
    (hbind : ∀ {α β : Type} (p : m α) (a : α) (f : α → m β) (b : β),
      R p a → R (f a) b → R (p >>= f) b)
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (referenceLift : ∀ {α : Type}, OracleComp HashSpec α → α)
    (hlift : ∀ {α : Type} (p : OracleComp HashSpec α), R (lift p) (referenceLift p))
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit))))
    (referenceRun : List Job → Option (List (List Bit)))
    (top : TopTree) (tree : Tree)
    (hrun : ∀ jobs, TreeSimCheckRunJobs tree jobs → R (run jobs) (referenceRun jobs)) :
    R (ceremonyOutput lift parameter run top tree)
      (ceremonyOutput (m := Id) referenceLift parameter referenceRun top tree) := by
  cases tree with
  | top =>
    simp only [ceremonyOutput, id_bind_eq, id_pure_eq]
    refine hbind (run topJobs) (referenceRun topJobs) _ _ (hrun _ rfl) ?_
    cases he : referenceRun topJobs with
    | none => exact hpure _
    | some outputs => exact hbind _ _ _ _ (hlift _) (hpure _)
  | bottom b =>
    simp only [ceremonyOutput, id_bind_eq, id_pure_eq]
    refine hbind (run (bottomJobs b)) (referenceRun (bottomJobs b)) _ _ (hrun _ (Or.inl rfl)) ?_
    cases he : referenceRun (bottomJobs b) with
    | none => exact hpure _
    | some outputs =>
      dsimp only
      refine hbind _ _ _ _ (hlift _) (hbind _ _ _ _ (hlift _) (hbind _ _ _ _ (hlift _) ?_))
      generalize hegrind : referenceLift (grind _ _ _ _ _ _ _) = gr
      rcases gr with _ | ⟨randomness, encoding⟩
      · exact hpure _
      · dsimp only
        refine hbind (run (signJobs b encoding)) (referenceRun (signJobs b encoding)) _ _
          (hrun _ (Or.inr ⟨encoding, rfl⟩)) ?_
        cases he' : referenceRun (signJobs b encoding) with
        | none => exact hpure _
        | some values =>
          dsimp only
          refine hbind _ _ _ _ (hlift _) (hbind _ _ _ _ (hlift _) ?_)
          split <;> exact hpure _

def TreeSimCheckStateCorrect {ι σ α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (bad : Prop)
    (p : StateT σ (OptionT (OracleComp spec)) α) (expected : α) : Prop :=
  ∀ initial value final,
    TreeSimCheckAllowed allowed (p.run initial).run (some (value, final)) → value = expected ∨ bad

theorem TreeSimCheckStateCorrect.pure {ι σ α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (bad : Prop) (a : α) :
    TreeSimCheckStateCorrect (σ := σ) allowed bad (pure a) a := by
  intro initial value final h
  have he : some (value, final) = some (a, initial) := h.pure_inv
  exact Or.inl (congrArg Prod.fst (Option.some.inj he))

theorem TreeSimCheckStateCorrect.bind {ι σ α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {bad : Prop}
    {p : StateT σ (OptionT (OracleComp spec)) α}
    {f : α → StateT σ (OptionT (OracleComp spec)) β} {a : α} {b : β}
    (hp : TreeSimCheckStateCorrect allowed bad p a)
    (hf : TreeSimCheckStateCorrect allowed bad (f a) b) :
    TreeSimCheckStateCorrect allowed bad (p >>= f) b := by
  intro initial value final h
  simp only [StateT.run_bind] at h
  obtain ⟨mid, hm, ht⟩ := h.option_bind_inv _ _ _
  rcases hp initial mid.1 mid.2 hm with he | hb
  · exact hf mid.2 value final (he ▸ ht)
  · exact Or.inr hb

theorem TreeSimCheckStateCorrect.mapM {ι σ α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {bad : Prop}
    (f : α → StateT σ (OptionT (OracleComp spec)) β) (expected : α → β)
    (xs : List α) (hf : ∀ x ∈ xs, TreeSimCheckStateCorrect allowed bad (f x) (expected x)) :
    TreeSimCheckStateCorrect allowed bad (xs.mapM f) (xs.map expected) := by
  induction xs with
  | nil => exact .pure allowed bad []
  | cons x xs ih =>
    simp only [List.mapM_cons, List.map_cons]
    exact (hf x (by simp)).bind
      ((ih (fun y hy => hf y (List.mem_cons_of_mem x hy))).bind (.pure allowed bad _))

theorem TreeSimCheckStateCorrect.batched {ι σ : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {bad : Prop} (size : ℕ)
    (f : List Job → StateT σ (OptionT (OracleComp spec)) (Option (List (List Bit))))
    (expected : List Job → List (List Bit)) (jobs : List Job)
    (hf : ∀ batch ∈ chunks size jobs,
      TreeSimCheckStateCorrect allowed bad (f batch) (some (expected batch))) :
    TreeSimCheckStateCorrect allowed bad (batched size f jobs)
      (some (((chunks size jobs).map expected).flatten)) := by
  unfold ThresholdLeanXmss.batched
  apply (TreeSimCheckStateCorrect.mapM f (some ∘ expected) (chunks size jobs) hf).bind
  have he := foldlM_some_append ((chunks size jobs).map expected) []
  simp only [List.map_map, List.nil_append] at he
  rw [he]
  exact .pure allowed bad _

def treeSimCheckPartyAllowed {ι : Type} {G : OracleSpec ι}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop) :
    (t : (PartySpec C E G).Domain) → (PartySpec C E G).Range t → Prop
  | .inl (.inl t), u => allowed t u
  | .inl (.inr _), _ => True
  | .inr _, _ => True

def TreeSimCheckStepAllowed {ι α : Type} {G : OracleSpec ι}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (step : Step C E G α) (a : α) : Prop :=
  match step with
  | .done out => out = some a
  | .wait _ resume => ∃ inbox,
      TreeSimCheckAllowed (treeSimCheckPartyAllowed allowed) (resume inbox) (some a)
  | .call _ resume => ∃ reply,
      TreeSimCheckAllowed (treeSimCheckPartyAllowed allowed) (resume reply) (some a)

theorem treeSimCheck_advance_replay {ι α : Type} {G : OracleSpec ι}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (p : OracleComp (PartySpec C E G) (Option α)) (step : Step C E G α) (a : α)
    (h : TreeSimCheckAllowed allowed (advance p) step)
    (finish : TreeSimCheckStepAllowed allowed step a) :
    TreeSimCheckAllowed (treeSimCheckPartyAllowed allowed) p (some a) := by
  induction p using OracleComp.inductionOn generalizing step with
  | pure out =>
    have he := h.pure_inv
    subst step
    change out = some a at finish
    subst out
    exact .pure _ _
  | query_bind t k ih =>
    rcases t with (t | outbox) | input
    · change TreeSimCheckAllowed allowed
        ((OracleComp.lift (OracleSpec.query t)) >>= fun u => advance (k u)) step at h
      obtain ⟨u, hu, hk⟩ := h.bind_inv
      exact .query _ k u _ (hu.query_inv t u) (ih u step hk finish)
    · have he := h.pure_inv
      subst step
      obtain ⟨inbox, hi⟩ := finish
      exact .query _ k inbox _ trivial hi
    · have he := h.pure_inv
      subst step
      obtain ⟨reply, hr⟩ := finish
      exact .query _ k reply _ trivial hr

private theorem treeSimCheck_sequence_allowed {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α : Type} (allowed : (t : spec.Domain) → spec.Range t → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α) (x : Fin n → α),
    TreeSimCheckAllowed allowed (Concrete.sequenceFin f) x →
      ∀ i, TreeSimCheckAllowed allowed (f i) (x i)
  | 0, _, _, _, i => i.elim0
  | n + 1, f, x, hx, i => by
    simp only [Concrete.sequenceFin] at hx
    obtain ⟨a, ha, hrest⟩ := hx.bind_inv
    obtain ⟨t, htail, he⟩ := hrest.bind_inv
    have he := he.pure_inv
    subst x
    cases i using Fin.cases with
    | zero => exact ha
    | succ i => exact treeSimCheck_sequence_allowed allowed (fun i : Fin n => f i.succ) t htail i

private theorem treeSimCheck_free_allowed {α : Type}
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (p : OracleComp (LocalSpec C) α) (a : α)
    (h : TreeSimCheckAllowed allowed (free p) a) :
    TreeSimCheckAllowed (fun t u => allowed (.inr t) u) p a := by
  exact TreeSimCheckAllowed.simulate_inv
    (fun t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (Sum.inr t))) allowed _
    (fun t u hu => TreeSimCheckAllowed.query_inv (allowed := allowed) (Sum.inr t) u hu) p a h

theorem treeSimCheck_step_replay {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (r : A.State × (C.Party → Step C E (CallSpec I O) α) ×
      (C.Party → C.Party → Option (Msg E)))
    (h : TreeSimCheckAllowed allowed (stepRound worldRoles D A F state steps) r)
    (i : C.Party) (hi : i ∉ D.1) (a : α)
    (finish : TreeSimCheckStepAllowed (fun t u => allowed (.inr t) u) (r.2.1 i) a) :
    TreeSimCheckStepAllowed (fun t u => allowed (.inr t) u) (steps i) a := by
  unfold stepRound at h
  split_ifs at h with hc
  · obtain ⟨p, _, hrest⟩ := h.bind_inv
    obtain ⟨next, hn, he⟩ := hrest.bind_inv
    have he := he.pure_inv
    subst r
    have hn := treeSimCheck_sequence_allowed allowed _ next hn i
    cases hs : steps i with
    | done out =>
      simp only [hs] at hn
      simpa only [hn.pure_inv, hs] using finish
    | wait outbox resume =>
      simp only [hs] at hn
      simpa only [hn.pure_inv, hs] using finish
    | call input resume =>
      simp only [hs, if_neg hi] at hn
      exact ⟨p.2 i, treeSimCheck_advance_replay _ (resume (p.2 i)) (next i) a
        (treeSimCheck_free_allowed allowed _ _ hn) finish⟩
  · obtain ⟨p, _, hrest⟩ := h.bind_inv
    obtain ⟨next, hn, he⟩ := hrest.bind_inv
    have he := he.pure_inv
    subst r
    have hn := treeSimCheck_sequence_allowed allowed _ next hn i
    cases hs : steps i with
    | done out =>
      simp only [hs] at hn
      simpa only [hn.pure_inv, hs] using finish
    | wait outbox resume =>
      simp only [hs, if_neg hi] at hn
      exact ⟨_, treeSimCheck_advance_replay _ _ (next i) a
        (treeSimCheck_free_allowed allowed _ _ hn) finish⟩
    | call input resume =>
      simp only [hs] at hn
      have hf : (none : Option α) = some a := by
        simpa only [hn.pure_inv, TreeSimCheckStepAllowed] using finish
      cases hf

theorem treeSimCheck_rounds_replay {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (r : A.State × (C.Party → Option α))
    (h : TreeSimCheckAllowed allowed (executeRounds worldRoles D A F fuel state steps) r)
    (i : C.Party) (hi : i ∉ D.1) (a : α) (finish : r.2 i = some a) :
    TreeSimCheckStepAllowed (fun t u => allowed (.inr t) u) (steps i) a := by
  induction fuel generalizing state steps r with
  | zero =>
    have he := h.pure_inv
    subst r
    cases hs : steps i <;> simp_all [Step.output, TreeSimCheckStepAllowed]
  | succ fuel ih =>
    simp only [executeRounds] at h
    split_ifs at h with hd
    · have he := h.pure_inv
      subst r
      cases hs : steps i <;> simp_all [Step.output, TreeSimCheckStepAllowed]
    · obtain ⟨p, hp, hr⟩ := h.bind_inv
      exact treeSimCheck_step_replay D A F allowed state steps p hp i hi a
        (ih p.1 p.2.1 r hr finish)

theorem treeSimCheck_phase_replay {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α)
    (r : A.State × (C.Party → Option α))
    (h : TreeSimCheckAllowed allowed (executePhase worldRoles D A F fuel state program) r)
    (i : C.Party) (hi : i ∉ D.1) (a : α) (finish : r.2 i = some a) :
    TreeSimCheckAllowed (treeSimCheckPartyAllowed (fun t u => allowed (.inr t) u))
      (program i).run (some a) := by
  obtain ⟨steps, hs, hr⟩ := h.bind_inv
  have hs := treeSimCheck_sequence_allowed allowed _ steps hs i
  simp only [if_neg hi] at hs
  exact treeSimCheck_advance_replay _ _ (steps i) a
    (treeSimCheck_free_allowed allowed _ _ hs)
    (treeSimCheck_rounds_replay D A F allowed fuel state steps r hr i hi a finish)

theorem treeSimCheck_ceremony_body_replay
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) (value : TreeOutput)
    (h : TreeSimCheckAllowed allowed
      (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput).run (some value)) :
    ∃ prss final,
      TreeSimCheckAllowed allowed (prssSetup (E := E) (G := RealSpec) i).run (some prss) ∧
      TreeSimCheckAllowed allowed
        ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
          (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
          (batched settings.batchSize (ceremonyBatch K circuits settings ⟨i, keys, prss⟩)) top tree).run
            (0, 0)).run (some (some value, final)) := by
  rw [ceremony_eq_prssSetup_bind] at h
  obtain ⟨prss, hp, hb⟩ := h.option_bind_inv _ _ _
  unfold ceremonyAfterSetup at hb
  obtain ⟨out, ho, hf⟩ := hb.option_bind_inv _ _ _
  cases out with
  | none => have he := hf.pure_inv; cases he
  | some out =>
    have he := Option.some.inj hf.pure_inv
    subst out
    simp only [StateT.run'_eq] at ho
    obtain ⟨p, hp', he⟩ := ho.option_map_inv _ _ _
    exact ⟨prss, p.2, hp, by simpa only [← he] using hp'⟩

theorem treeSimCheck_ceremonyBatch_replay {ι : Type} {G : OracleSpec ι}
    (allowed : (t : (PartySpec C E G).Domain) → (PartySpec C E G).Range t → Prop)
    (ctx : Context C) (jobs : List Job) (initial final : ℕ × ℕ) (value : Option (List (List Bit)))
    (h : TreeSimCheckAllowed allowed
      ((ceremonyBatch (G := G) K circuits settings ctx jobs).run initial).run (some (value, final))) :
    ∃ inputs outputs state,
      value = some outputs ∧ final = (state.label, initial.2 + 1) ∧
      TreeSimCheckAllowed allowed (jobs.mapM (inputShares (E := E) (G := G) ctx)).run (some inputs) ∧
      TreeSimCheckAllowed allowed
        ((runJobs K (realRunGadgets K ctx settings.mode)
          (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run
            ⟨fun _ => [], initial.1, initial.2⟩).run (some (outputs, state)) := by
  simp only [ceremonyBatch, StateT.run_bind, StateT.run_get, StateT.run_lift,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at h
  obtain ⟨inputs, hi, hr⟩ := h.option_bind_inv _ _ _
  obtain ⟨result, hj, he⟩ := hr.option_bind_inv _ _ _
  have he := Option.some.inj he.pure_inv
  exact ⟨inputs, result.1, result.2, congrArg Prod.fst he, congrArg Prod.snd he, hi, hj⟩

private theorem treeSimCheck_sequence_support {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp spec α) (x : Fin n → α),
    x ∈ support (Concrete.sequenceFin f) → ∀ i, x i ∈ support (f i)
  | 0, _, _, _, i => i.elim0
  | n + 1, f, x, hx, i => by
    simp only [Concrete.sequenceFin, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hx
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    cases i using Fin.cases with
    | zero => exact ha
    | succ i => exact treeSimCheck_sequence_support (fun i : Fin n => f i.succ) t ht i

private theorem treeSimCheck_step_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (r : A.State × (C.Party → Step C E (CallSpec I O) α) ×
      (C.Party → C.Party → Option (Msg E)))
    (h : r ∈ support (stepRound worldRoles D A F state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : r.2.1 i = .done a := by
  classical
  unfold stepRound at h
  split_ifs at h with hc
  all_goals
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨p, _, next, hn, rfl⟩ := h
    have hh := treeSimCheck_sequence_support _ next hn i
    simpa only [hi, support_pure, Set.mem_singleton_iff] using hh

private theorem treeSimCheck_rounds_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (out : A.State × (C.Party → Option α))
    (h : out ∈ support (executeRounds worldRoles D A F fuel state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : out.2 i = a := by
  classical
  induction fuel generalizing state steps out with
  | zero =>
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at h
    subst out
    exact congrArg Step.output hi
  | succ fuel ih =>
    simp only [executeRounds] at h
    split_ifs at h with hd
    · cases h
      exact congrArg Step.output hi
    · simp only [support_bind, Set.mem_iUnion] at h
      obtain ⟨r, hr, ho⟩ := h
      exact ih r.1 r.2.1 out ho (treeSimCheck_step_done D A F state steps r hr i a hi)

theorem treeSimCheckReplay_rounds_mono {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel more : ℕ) (hf : fuel ≤ more) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (a b : A.State × (C.Party → Option α)) (left right log : TreeSimLog C)
    (ha : TreeSimCheckReplay (executeRounds worldRoles D A F fuel state steps) left a)
    (hb : TreeSimCheckReplay (executeRounds worldRoles D A F more state steps) right b)
    (hl : left <+: log) (hr : right <+: log) :
    ∀ i v, a.2 i = some v → b.2 i = some v := by
  classical
  induction fuel generalizing more state steps a b left right log with
  | zero =>
    simp only [executeRounds] at ha
    cases ha
    intro i v hi
    have hd : steps i = .done (some v) := by
      cases h : steps i <;> simp_all [Step.output]
    exact treeSimCheck_rounds_done D A F more state steps b hb.mem_support i (some v) hd
  | succ fuel ih =>
    obtain ⟨more, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : more ≠ 0)
    simp only [executeRounds] at ha hb
    split_ifs at ha hb with hd
    · cases ha
      cases hb
      exact fun _ _ h => h
    · obtain ⟨pa, preA, postA, hpa, hka, rfl⟩ := ha.bind_inv _ _
      obtain ⟨pb, preB, postB, hpb, hkb, rfl⟩ := hb.bind_inv _ _
      have hpreA : preA <+: log := (List.prefix_append preA postA).trans hl
      have hpreB : preB <+: log := (List.prefix_append preB postB).trans hr
      obtain ⟨rfl, rfl⟩ := hpa.common_prefix_unique hpb hpreA hpreB
      obtain ⟨tail, rfl⟩ := hpreA
      simp only [List.prefix_append_right_inj] at hl hr
      exact ih more (by omega) pa.1 pa.2.1 a b postA postB tail hka hkb hl hr

theorem treeSimCheckReplay_execution_mono {I O Ih Oh L R : Type}
    (D : C.Coalition) (A : Adversary C E I L R) (F : Functionality C Ih Oh L R)
    (fuel more : ℕ) (hf : fuel ≤ more)
    (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O) (x : C.Party → I) (z : Aux)
    (a b : A.State × (C.Party → Option O)) (left right log : TreeSimLog C)
    (ha : TreeSimCheckReplay (realExecution D A F fuel program x z) left a)
    (hb : TreeSimCheckReplay (realExecution D A F more program x z) right b)
    (hl : left <+: log) (hr : right <+: log) :
    ∀ i v, a.2 i = some v → b.2 i = some v := by
  unfold realExecution executePhase at ha hb
  obtain ⟨sa, preA, postA, hsa, hka, rfl⟩ := ha.bind_inv _ _
  obtain ⟨sb, preB, postB, hsb, hkb, rfl⟩ := hb.bind_inv _ _
  have hpreA : preA <+: log := (List.prefix_append preA postA).trans hl
  have hpreB : preB <+: log := (List.prefix_append preB postB).trans hr
  obtain ⟨rfl, rfl⟩ := hsa.common_prefix_unique hsb hpreA hpreB
  obtain ⟨tail, rfl⟩ := hpreA
  simp only [List.prefix_append_right_inj] at hl hr
  obtain ⟨stepsA, initA, restA, hstepsA, hrestA, rfl⟩ := hka.bind_inv _ _
  obtain ⟨stepsB, initB, restB, hstepsB, hrestB, rfl⟩ := hkb.bind_inv _ _
  have hinitA : initA <+: tail := (List.prefix_append initA restA).trans hl
  have hinitB : initB <+: tail := (List.prefix_append initB restB).trans hr
  obtain ⟨rfl, rfl⟩ := hstepsA.common_prefix_unique hstepsB hinitA hinitB
  obtain ⟨final, rfl⟩ := hinitA
  simp only [List.prefix_append_right_inj] at hl hr
  exact treeSimCheckReplay_rounds_mono D A F fuel more hf sa stepsA a b
    restA restB final hrestA hrestB hl hr

theorem treeSimCheckReplay_logged {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (a : α) (log : TreeSimLog C)
    (h : (a, log) ∈ support (treeSimLoggedRun prims D p)) :
    TreeSimCheckReplay p log a := by
  unfold treeSimLoggedRun at h
  simp only [StateT.run'_eq, support_map, Set.mem_image] at h
  obtain ⟨⟨⟨b, pref⟩, cache⟩, hb, he⟩ := h
  cases he
  exact treeSimCheckReplay_supported prims D p (∅, ∅) _ _ cache hb

theorem treeSimCheckReplay_ghost {α β : Type} (D : C.Coalition)
    (dealer : OracleComp (LocalSpec C) α) (p : OracleComp (WorldSpec C) β)
    (d : α) (b : β) (log : TreeSimLog C)
    (h : (d, (b, log)) ∈ support (treeSimGhostRun prims D dealer p)) :
    TreeSimCheckReplay p log b := by
  unfold treeSimGhostRun at h
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind,
    support_bind, support_map, Set.mem_iUnion, Set.mem_image, support_pure,
    Set.mem_singleton_iff, exists_eq_left] at h
  obtain ⟨⟨d', cache⟩, _, ⟨⟨b', pref⟩, final⟩, hb, he⟩ := h
  cases he
  exact treeSimCheckReplay_supported prims D p cache _ _ final hb

theorem treeSimOutputWitness_replay (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (out : A.State × (C.Party → Option TreeOutput)) (log : TreeSimLog C)
    (h : TreeSimOutputWitness prims K circuits settings top tree D A
      parameter seeds pairs z dealt out log) :
    ∃ fuel pref, fuel ≤ ceremonyFuel circuits settings ∧ pref <+: log ∧
      TreeSimCheckReplay
        (realExecution D A noFunctionality fuel
          (fun i keys => (ceremony K circuits settings i keys top tree :
            PartyM C E RealSpec TreeOutput)) (dealtKeys parameter seeds pairs) z) pref out := by
  obtain ⟨fuel, pref, hf, hp, hrun⟩ := h
  exact ⟨fuel, pref, hf, hp, treeSimCheckReplay_ghost prims D _ _ _ _ _ hrun⟩

theorem treeSimOutputWitness_actual_output (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (out actual : A.State × (C.Party → Option TreeOutput)) (pref log : TreeSimLog C)
    (witness : TreeSimOutputWitness prims K circuits settings top tree D A
      parameter seeds pairs z dealt out log)
    (run : TreeSimCheckReplay
      (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun i keys => (ceremony K circuits settings i keys top tree :
          PartyM C E RealSpec TreeOutput)) (dealtKeys parameter seeds pairs) z) pref actual)
    (hprefix : pref <+: log) :
    ∀ i v, out.2 i = some v → actual.2 i = some v := by
  obtain ⟨fuel, early, hf, hearly, replay⟩ :=
    treeSimOutputWitness_replay prims K circuits settings top tree D A
      parameter seeds pairs z dealt out log witness
  exact treeSimCheckReplay_execution_mono D A noFunctionality fuel _ hf _ _ z
    out actual early pref log replay run hearly hprefix

/-- The witness's accepted incorrect value is an output of the actual full
ceremony prefix of the logged game, before its distinguisher. -/
theorem treeSimWrongOutput_actual (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool) (log : TreeSimLog C)
    (run : (result, log) ∈ support
      (treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs dealt out actual pre post,
      x = dealtKeys parameter seeds pairs ∧
      TreeSimOutputWitness prims K circuits settings top tree D A
        parameter seeds pairs z dealt out log ∧
      TreeSimCheckReplay
        (realExecution D A noFunctionality (ceremonyFuel circuits settings)
          (fun i keys => (ceremony K circuits settings i keys top tree :
            PartyM C E RealSpec TreeOutput)) x z) pre actual ∧
      TreeSimCheckReplay (worldRoles.adversary (Z actual)) post result ∧
      log = pre ++ post ∧
      ∃ i, i ∉ D.1 ∧ (actual.2 i).isSome ∧ actual.2 i ≠ dealt.1 := by
  have replay := treeSimCheckReplay_logged prims D _ result log run
  unfold treeRealGame distinguish at replay
  obtain ⟨actual, pre, post, ha, hz, hlog⟩ := replay.bind_inv _ _
  obtain ⟨parameter, seeds, pairs, dealt, out, hx, witness, i, hi, hs, hwrong⟩ := wrong
  refine ⟨parameter, seeds, pairs, dealt, out, actual, pre, post,
    hx, witness, ha, hz, hlog, i, hi, ?_⟩
  obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp hs
  have hp : pre <+: log := hlog ▸ List.prefix_append pre post
  have same := treeSimOutputWitness_actual_output prims K circuits settings top tree D A
    parameter seeds pairs z dealt out actual pre log witness (hx ▸ ha) hp i value hv
  exact ⟨by simp [same], by simpa only [same, hv] using hwrong⟩

/-- An incorrect accepting party has a complete ceremony replay whose local
answers occur in the actual game log. This projection is derived from the
actual scheduler execution before inspecting its batches. -/
theorem treeSimWrongOutput_party_replay (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool) (log : TreeSimLog C)
    (run : (result, log) ∈ support
      (treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs dealt out i value partyLog,
      x = dealtKeys parameter seeds pairs ∧
      TreeSimOutputWitness prims K circuits settings top tree D A
        parameter seeds pairs z dealt out log ∧
      i ∉ D.1 ∧ some value ≠ dealt.1 ∧
      TreeSimCheckReplay (ceremony K circuits settings i (x i) top tree :
        PartyM C E RealSpec TreeOutput).run partyLog (some value) ∧
      ∀ (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t),
        (⟨.inl (.inl t), u⟩ : (t : (PartySpec C E RealSpec).Domain) ×
          (PartySpec C E RealSpec).Range t) ∈ partyLog →
        (⟨.inr t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log := by
  obtain ⟨parameter, seeds, pairs, dealt, out, actual, pre, post,
    hx, witness, replay, _, hlog, i, hi, hs, hw⟩ :=
    treeSimWrongOutput_actual prims K circuits settings top tree D A x z Z result log run wrong
  obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp hs
  have hr : TreeSimCheckAllowed
      (fun t u => (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log)
      (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun j keys => (ceremony K circuits settings j keys top tree :
          PartyM C E RealSpec TreeOutput)) x z) actual :=
    ⟨pre, replay, fun t u hu => hlog ▸ List.mem_append_left post hu⟩
  obtain ⟨state, _, phase⟩ := hr.bind_inv
  obtain ⟨partyLog, hp, ha⟩ := treeSimCheck_phase_replay D A noFunctionality _
    (ceremonyFuel circuits settings) state _ actual phase i hi value hv
  exact ⟨parameter, seeds, pairs, dealt, out, i, value, partyLog, hx, witness, hi,
    by simpa only [hv] using hw, hp, fun t u hu => ha (.inl (.inl t)) u hu⟩

private theorem treeSimCheck_hash_reply (q : Query C) (cache : HashCache C)
    (p : HashOutput × HashCache C) (hp : p ∈ support ((hashAnswer prims q).run cache))
    (final : HashCache C) (hgrow : p.2 ≤ final) : hashOf prims final q = p.1 := by
  by_cases hfix : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hfix
    rw [hashAnswer_of_isFixed prims hm] at hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    simp [hashOf, hm]
  · rw [hashAnswer_of_not_isFixed prims hfix] at hp
    have he := hgrow (randomOracle_support q cache p hp).2.1
    cases q <;> simp_all [hashOf, IsFixed]

def TreeSimCheckWorldHashes (h : Query C → HashOutput) :
    (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop
  | .inl (.inl (.inr (.inl q))), u => h q = u
  | .inr (.inr (.inl q)), u => h q = u
  | _, _ => True

private theorem treeSimCheck_world_hash_reply (D : C.Coalition)
    (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (p : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (hp : p ∈ support ((streamWorld prims D t).run s))
    (final : HashCache C) (hgrow : p.2.1 ≤ final) :
    TreeSimCheckWorldHashes (hashOf prims final) t p.1 := by
  rcases t with ((u | q | x) | query) | (u | q | x)
  all_goals try exact True.intro
  all_goals
    simp only [streamWorld, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      localAnswer, onHash, StateT.run_mk, support_map, Set.mem_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact treeSimCheck_hash_reply prims q s.1 r hr final hgrow

/-- All hash answers in a logged execution agree with its final cache,
including the public hash queries outside the check's collision region. -/
theorem treeSimCheck_logged_hashes {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C)
    (a : α) (log : TreeSimLog C) (s' : HashCache C × HiddenCache C)
    (h : ((a, log), s') ∈ support
      ((simulateQ ((streamWorld prims D).withTraceAppend
        (fun t u => ([⟨t, u⟩] : TreeSimLog C))) p).run.run s)) :
    s.1 ≤ s'.1 ∧ ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
      TreeSimCheckWorldHashes (hashOf prims s'.1) t u := by
  induction p using OracleComp.inductionOn generalizing s a log s' with
  | pure b =>
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨le_rfl, by simp⟩
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query,
      QueryImpl.withTraceAppend_apply, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, StateT.run_bind, StateT.run_map,
      bind_map_left, pure_bind, bind_assoc, Functor.map_map,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨⟨u, next⟩, hu, ⟨⟨b, tail⟩, final⟩, hb, he⟩ := h
    cases he
    obtain ⟨hgrow, hall⟩ := ih u next b tail final hb
    refine ⟨(treeSim_streamWorld_grows prims D t s (u, next) hu).trans hgrow, ?_⟩
    intro t' u' hm
    rcases List.mem_cons.mp hm with he | he
    · cases he
      exact treeSimCheck_world_hash_reply prims D t s (u, next) hu final.1 hgrow
    · exact hall t' u' he

private theorem treeSimCheck_hashOf_agrees_prefix (cache final : HashCache C)
    (hm : NoMpc cache) (hgrow : cache ≤ final) : Agrees (hashOf prims final) cache := by
  intro q v hq
  have he := hgrow hq
  cases q with
  | hash input =>
    have hn : ¬ MpcInput input := by
      intro hi
      rw [hm input hi] at hq
      cases hq
    simp [hashOf, hn, he]
  | _ => simp [hashOf, he]

/-- The ghost dealer and the logged execution share a single total hash
function. The dealer reference is therefore fixed by that same execution. -/
theorem treeSimCheck_ghost_hashes {α β : Type} (D : C.Coalition)
    (dealer : OracleComp (RoSpec C) α) (p : OracleComp (WorldSpec C) β)
    (d : α) (b : β) (log : TreeSimLog C)
    (h : (d, (b, log)) ∈ support
      (treeSimGhostRun prims D (liftComp dealer (LocalSpec C)) p)) :
    ∃ hash, Good prims hash ∧ d = ThresholdLeanXmssSecurity.D prims hash dealer ∧
      ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
        TreeSimCheckWorldHashes hash t u := by
  unfold treeSimGhostRun at h
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind,
    support_bind, support_map, Set.mem_iUnion, Set.mem_image, support_pure,
    Set.mem_singleton_iff, exists_eq_left] at h
  obtain ⟨⟨d', cache⟩, hd, ⟨⟨b', pref⟩, final⟩, hb, he⟩ := h
  cases he
  obtain ⟨hgrow, hlog⟩ := treeSimCheck_logged_hashes prims D p cache b log final hb
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hd
  obtain ⟨start, hs, he⟩ := hd
  cases he
  obtain ⟨_, hm, hh⟩ := localRun_support (liftComp dealer (LocalSpec C)) ∅ start hs
  let hash := hashOf prims final.1
  have hg : Good prims hash := good_hashOf prims final.1
  have ha : Agrees hash start.2 :=
    treeSimCheck_hashOf_agrees_prefix prims start.2 final.1 (hm noMpc_empty) hgrow
  have hv := hh hash hg ha
  rw [simulateQ_fixedLocal_liftComp] at hv
  exact ⟨hash, hg, by simpa using hv, hlog⟩

theorem treeSimCheck_witness_reference (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (out : A.State × (C.Party → Option TreeOutput)) (log : TreeSimLog C)
    (witness : TreeSimOutputWitness prims K circuits settings top tree D A
      parameter seeds pairs z dealt out log)
    (i : C.Party) (hi : i ∉ D.1) (value : TreeOutput) (hv : out.2 i = some value) :
    ∃ hash pref,
      Good prims hash ∧ pref <+: log ∧
      dealt.1 = ceremonyAt prims circuits parameter seeds hash top tree ∧
      TreeSimCheckAllowed (treeSimCheckPartyAllowed (fun t u =>
        TreeSimCheckWorldHashes hash (.inr t) u ∧
          (⟨.inr t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ pref))
        (ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree :
          PartyM C E RealSpec TreeOutput).run (some value) := by
  obtain ⟨fuel, pref, hf, hp, hs⟩ := witness
  obtain ⟨hash, hg, hd, hall⟩ := treeSimCheck_ghost_hashes prims D
    (dealerCeremony circuits settings parameter seeds top tree) _ dealt out pref hs
  have replay := treeSimCheckReplay_ghost prims D _ _ dealt out pref hs
  have hr : TreeSimCheckAllowed
      (fun t u => TreeSimCheckWorldHashes hash t u ∧
        (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ pref)
      (realExecution D A noFunctionality fuel
        (fun j keys => (ceremony K circuits settings j keys top tree :
          PartyM C E RealSpec TreeOutput)) (dealtKeys parameter seeds pairs) z) out :=
    ⟨pref, replay, fun t u hu => ⟨hall t u hu, hu⟩⟩
  obtain ⟨state, _, hphase⟩ := hr.bind_inv
  refine ⟨hash, pref, hg, hp, ?_, ?_⟩
  · rw [hd, D_dealerCeremony prims circuits settings parameter seeds hash top tree hbatch]
  · exact treeSimCheck_phase_replay D A noFunctionality _ fuel state _ out hphase i hi value hv

theorem treeSimCheck_public_replay {ι α : Type} {G : OracleSpec ι}
    (allowed : (t : (PartySpec C E G).Domain) → (PartySpec C E G).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (p : OracleComp HashSpec α) (a : α)
    (h : TreeSimCheckAllowed allowed (oracleStep (tweakable p) : PartyM C E G α).run (some a)) :
    a = D prims hash (tweakable p) := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b =>
    simp only [tweakable, simulateQ_pure, D_pure] at h ⊢
    have he : some a = some b := h.pure_inv
    exact Option.some.inj he
  | query_bind t k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query, oracleStep_bind] at h
    obtain ⟨v, hv, hk⟩ := h.option_bind_inv _ _ _
    have hq : TreeSimCheckAllowed allowed
        ((OracleComp.lift (OracleSpec.query (spec := PartySpec C E G)
          (.inl (.inl (.inr (.inl (.hash t))))))) >>= fun u => pure (some u)) (some v) := by
      exact hv
    obtain ⟨u, hu, he⟩ := hq.bind_inv
    have he := Option.some.inj he.pure_inv
    subst v
    have heq := hhash (.hash t) u (hu.query_inv _ _)
    simpa only [tweakable, simulateQ_bind, simulateQ_spec_query, D_bind, D_hashQuery, heq] using
      ih u a hk

/-- A first incorrect successful batch, retaining its correct prefix, the
entry and exit states, and its continuation under the same replay answers. -/
def TreeSimCheckFirstBatch
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (seeds : C.Term → HashOutput) (hash : Query C → HashOutput) (tree : Tree) : Prop :=
  let expected := fun jobs : List Job =>
    jobs.map (fun job => D prims hash (evalJob circuits ctx.keys.parameter seeds job))
  ∃ jobs before batch after outputs tail initial final entry next,
    TreeSimCheckRunJobs tree jobs ∧ chunks settings.batchSize jobs = before ++ batch :: after ∧
    before.length < (chunks settings.batchSize jobs).length ∧
    TreeSimCheckAllowed allowed
      ((before.mapM (ceremonyBatch K circuits settings ctx)).run initial).run
        (some (before.map (some ∘ expected), entry)) ∧
    TreeSimCheckAllowed allowed ((ceremonyBatch K circuits settings ctx batch).run entry).run
      (some (some outputs, next)) ∧ outputs ≠ expected batch ∧
    TreeSimCheckAllowed allowed
      ((after.mapM (ceremonyBatch K circuits settings ctx)).run next).run (some (tail, final))

/-- With public hash answers fixed by the shared cache, an incorrect tree
output requires an incorrect successful batch of one of that tree's runs. -/
theorem treeSimCheck_body_first_wrong_batch
    (hsize : 0 < settings.batchSize)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (ctx : Context C) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
    (value : TreeOutput) (final : ℕ × ℕ)
    (h : TreeSimCheckAllowed allowed
      ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree).run
          (0, 0)).run (some (some value, final)))
    (hne : some value ≠ ceremonyAt prims circuits ctx.keys.parameter seeds hash top tree) :
    TreeSimCheckFirstBatch prims K circuits settings allowed ctx seeds hash tree := by
  let expected := fun jobs : List Job =>
    jobs.map (fun job => D prims hash (evalJob circuits ctx.keys.parameter seeds job))
  let bad := TreeSimCheckFirstBatch prims K circuits settings allowed ctx seeds hash tree
  have hcorrect : TreeSimCheckStateCorrect allowed bad
      (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree)
      (ceremonyAt prims circuits ctx.keys.parameter seeds hash top tree) := by
    apply treeSimCheck_ceremony_rel (fun {α} => TreeSimCheckStateCorrect allowed bad)
      (fun a => TreeSimCheckStateCorrect.pure allowed bad a)
      (fun p a f b hp hf => hp.bind hf)
      (fun oa => StateT.lift (oracleStep (tweakable oa)))
      (fun oa => D prims hash (tweakable oa))
    · intro α p initial output last hr
      simp only [StateT.run_lift] at hr
      obtain ⟨a, ha, he⟩ := hr.option_map_inv _ _ _
      have hev : a = output := congrArg Prod.fst he
      exact Or.inl (hev ▸ treeSimCheck_public_replay prims allowed hash hhash p a ha)
    · intro jobs hj initial output last hr
      obtain ⟨outputs, he⟩ := treeSimCheck_state_batched_some allowed settings.batchSize
        (ceremonyBatch K circuits settings ctx) jobs
        (fun batch _ initial output last hb => by
          obtain ⟨_, outputs, _, he, _, _, _⟩ :=
            treeSimCheck_ceremonyBatch_replay K circuits settings allowed ctx batch initial last output hb
          simp only [he, Option.isSome_some]) output initial last hr
      subst output
      rcases Classical.em (outputs = expected jobs) with he | he
      · exact Or.inl (by simpa only [expected, evalRun_eq] using congrArg some he)
      · apply Or.inr
        have hn : outputs ≠ ((chunks settings.batchSize jobs).map expected).flatten := by
          simpa only [expected, flatten_chunks_map settings.batchSize hsize] using he
        obtain ⟨before, batch, after, value, tail, entry, next, hx, hi, hp, hb, hw, ht⟩ :=
          treeSimCheck_state_batched_first allowed settings.batchSize
            (ceremonyBatch K circuits settings ctx) expected jobs outputs initial last hr hn
        exact ⟨jobs, before, batch, after, value, tail, initial, last, entry, next,
          hj, hx, hi, hp, hb, hw, ht⟩
  exact (hcorrect (0, 0) (some value) final h).resolve_left hne

/-- The semantic wrong-output event reaches a first incorrect batch with
its reference hash and its local answers tied to the actual logged game.
The accepted value is first identified in the full scheduler replay. -/
theorem treeSimWrongOutput_first_batch (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool) (log : TreeSimLog C)
    (run : (result, log) ∈ support
      (treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs actual pre post i value hash pref prss,
      x = dealtKeys parameter seeds pairs ∧
      TreeSimCheckReplay
        (realExecution D A noFunctionality (ceremonyFuel circuits settings)
          (fun i keys => (ceremony K circuits settings i keys top tree :
            PartyM C E RealSpec TreeOutput)) x z) pre actual ∧
      log = pre ++ post ∧ i ∉ D.1 ∧ actual.2 i = some value ∧
      some value ≠ ceremonyAt prims circuits parameter seeds hash top tree ∧
      Good prims hash ∧ pref <+: log ∧
      TreeSimCheckFirstBatch prims K circuits settings
        (treeSimCheckPartyAllowed (fun t u => TreeSimCheckWorldHashes hash (.inr t) u ∧
          (⟨.inr t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ pref))
        ⟨i, x i, prss⟩ seeds hash tree := by
  have replay := treeSimCheckReplay_logged prims D _ result log run
  unfold treeRealGame distinguish at replay
  obtain ⟨actual, pre, post, ha, hz, hlog⟩ := replay.bind_inv _ _
  obtain ⟨parameter, seeds, pairs, dealt, out, hx, witness, i, hi, hs, hw⟩ := wrong
  obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp hs
  have hp : pre <+: log := hlog ▸ List.prefix_append pre post
  have same := treeSimOutputWitness_actual_output prims K circuits settings top tree D A
    parameter seeds pairs z dealt out actual pre log witness (hx ▸ ha) hp i value hv
  obtain ⟨hash, pref, hg, hpre, hd, hparty⟩ :=
    treeSimCheck_witness_reference prims K circuits settings hbatch top tree D A
      parameter seeds pairs z dealt out log witness i hi value hv
  obtain ⟨prss, final, _, hbody⟩ := treeSimCheck_ceremony_body_replay K circuits settings _
    i (dealtKeys parameter seeds pairs i) top tree value hparty
  have hwrong : some value ≠ ceremonyAt prims circuits parameter seeds hash top tree := by
    simpa only [hv, hd] using hw
  have hfirst := treeSimCheck_body_first_wrong_batch prims K circuits settings hbatch _ hash
    (fun q u hu => hu.1) ⟨i, dealtKeys parameter seeds pairs i, prss⟩ seeds top tree value final hbody hwrong
  refine ⟨parameter, seeds, pairs, actual, pre, post, i, value, hash, pref, prss,
    hx, ha, hlog, hi, same, hwrong, hg, hpre, ?_⟩
  simpa only [hx] using hfirst

section RecordedExecution

/-- A party transcript records network replies as well as local oracle replies.
Erasure below is an equality of scheduled programs, before choosing a handler. -/
def treeSimCheckRecord {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} :
    OracleComp spec α → OracleComp spec (α × List ((t : spec.Domain) × spec.Range t))
  | .pure a => pure (a, [])
  | .roll t k => do
      let u ← OracleComp.lift (OracleSpec.query t)
      let r ← treeSimCheckRecord (k u)
      pure (r.1, ⟨t, u⟩ :: r.2)

theorem treeSimCheckRecord_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (a : α) : treeSimCheckRecord (pure a : OracleComp spec α) = pure (a, []) := rfl

theorem treeSimCheckRecord_query {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    treeSimCheckRecord (OracleComp.lift (OracleSpec.query t) >>= k) =
      (OracleComp.lift (OracleSpec.query t) >>= fun u =>
        (fun r => (r.1, ⟨t, u⟩ :: r.2)) <$> treeSimCheckRecord (k u)) := rfl

theorem treeSimCheckRecord_erase {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : OracleComp spec α) : Prod.fst <$> treeSimCheckRecord p = p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimCheckRecord_query, map_bind, Functor.map_map, Function.comp_def]
    exact bind_congr ih

theorem treeSimCheckRecord_replay {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : OracleComp spec α) (r : α × List ((t : spec.Domain) × spec.Range t))
    (h : r ∈ support (treeSimCheckRecord p)) : TreeSimCheckReplay p r.2 r.1 := by
  induction p using OracleComp.inductionOn generalizing r with
  | pure a =>
    have he : r = (a, []) := by simpa only [treeSimCheckRecord_pure, support_pure,
      Set.mem_singleton_iff] using h
    subst r
    exact .pure a
  | query_bind t k ih =>
    simp only [treeSimCheckRecord_query, support_bind, Set.mem_iUnion, support_map,
      Set.mem_image] at h
    obtain ⟨u, _, v, hv, rfl⟩ := h
    exact .query t k u v.2 v.1 (ih u v hv)

def treeSimCheckRecordedParty {ι : Type} {G : OracleSpec ι} {α : Type}
    (p : PartyM C E G α) : PartyM C E G
      (α × List ((t : (PartySpec C E G).Domain) × (PartySpec C E G).Range t)) :=
  OptionT.mk ((fun r => r.1.map (fun a => (a, r.2))) <$> treeSimCheckRecord p.run)

theorem treeSimCheckRecordedParty_erase {ι : Type} {G : OracleSpec ι} {α : Type}
    (p : PartyM C E G α) : Prod.fst <$> treeSimCheckRecordedParty p = p := by
  apply OptionT.ext
  simp only [treeSimCheckRecordedParty, OptionT.run_map, OptionT.run_mk, Functor.map_map]
  have he : (fun r : Option α × List ((t : (PartySpec C E G).Domain) ×
      (PartySpec C E G).Range t) => (r.1.map (fun a => (a, r.2))).map Prod.fst) = Prod.fst := by
    funext r
    cases r.1 <;> rfl
  rw [he, treeSimCheckRecord_erase]

def treeSimCheckMapStep {ι : Type} {G : OracleSpec ι} {α β : Type} (f : α → β) :
    Step C E G α → Step C E G β
  | .done out => .done (out.map f)
  | .wait mail resume => .wait mail (fun inbox => Option.map f <$> resume inbox)
  | .call input resume => .call input (fun reply => Option.map f <$> resume reply)

theorem treeSimCheck_advance_map {ι : Type} {G : OracleSpec ι} {α β : Type}
    (f : α → β) (p : OracleComp (PartySpec C E G) (Option α)) :
    advance (Option.map f <$> p) = treeSimCheckMapStep f <$> advance p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with (t | mail) | input
    · simp only [map_bind]
      change (OracleComp.lift (OracleSpec.query t) >>= fun u =>
        advance (Option.map f <$> k u)) =
        treeSimCheckMapStep f <$> (OracleComp.lift (OracleSpec.query t) >>= fun u => advance (k u))
      rw [map_bind]
      exact bind_congr ih
    · rfl
    · rfl

@[simp] theorem treeSimCheckMapStep_outbox {ι : Type} {G : OracleSpec ι} {α β : Type}
    (f : α → β) (s : Step C E G α) :
    (treeSimCheckMapStep f s).outbox = s.outbox := by cases s <;> rfl

@[simp] theorem treeSimCheckMapStep_delivered {ι : Type} {G : OracleSpec ι} {α β : Type}
    (f : α → β) (s : Step C E G α) :
    (treeSimCheckMapStep f s).delivered = s.delivered := by
  cases s with
  | done o => cases o <;> rfl
  | wait _ _ => rfl
  | call _ _ => rfl

@[simp] theorem treeSimCheckMapStep_isDone {ι : Type} {G : OracleSpec ι} {α β : Type}
    (f : α → β) (s : Step C E G α) :
    (treeSimCheckMapStep f s).isDone = s.isDone := by cases s <;> rfl

@[simp] theorem treeSimCheckMapStep_output {ι : Type} {G : OracleSpec ι} {α β : Type}
    (f : α → β) (s : Step C E G α) :
    (treeSimCheckMapStep f s).output = s.output.map f := by cases s <;> rfl

theorem treeSimCheck_roundLocal_map {α β : Type} (f : α → β) (D : C.Coalition)
    (steps : C.Party → Step C E RealSpec α) (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (fun j => treeSimCheckMapStep f (steps j)) sent i =
      treeSimCheckMapStep f <$> roundLocal D steps sent i := by
  unfold roundLocal
  dsimp only
  cases hs : steps i with
  | done o => rfl
  | call input _ => exact input.elim
  | wait outbox resume =>
    rw [treeSimCheckMapStep]
    dsimp only
    split_ifs
    · rfl
    · simp only [treeSimCheckMapStep_delivered]
      exact treeSimCheck_advance_map f _

theorem treeSimCheck_stepRound_map {α β : Type} (f : α → β) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (fun i => treeSimCheckMapStep f (steps i)) =
      (fun r => (r.1, (fun i => treeSimCheckMapStep f (r.2.1 i)), r.2.2)) <$>
        stepRound worldRoles D A noFunctionality state steps := by
  rw [stepRound_real, stepRound_real]
  simp only [treeSimCheckMapStep_outbox, map_bind, map_pure]
  apply bind_congr
  rintro ⟨state', sent⟩
  have hs : Concrete.sequenceFin (roundLocal D (fun i => treeSimCheckMapStep f (steps i)) sent) =
      (fun row i => treeSimCheckMapStep f (row i)) <$>
        Concrete.sequenceFin (roundLocal D steps sent) := by
    change Concrete.sequenceFin (fun i => roundLocal D (fun j => treeSimCheckMapStep f (steps j)) sent i) = _
    simp only [treeSimCheck_roundLocal_map, map_eq_bind_pure_comp, Function.comp_def,
      sequenceFin_bind_pure]
  rw [hs]
  simp only [map_eq_bind_pure_comp, free_bind, free_pure, bind_assoc, pure_bind]
  rfl

theorem treeSimCheck_executeRounds_map {α β : Type} (f : α → β) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    executeRounds worldRoles D A noFunctionality fuel state
        (fun i => treeSimCheckMapStep f (steps i)) =
      (fun r => (r.1, fun i => (r.2 i).map f)) <$>
        executeRounds worldRoles D A noFunctionality fuel state steps := by
  induction fuel generalizing state steps with
  | zero => simp only [executeRounds, treeSimCheckMapStep_output, map_pure]
  | succ fuel ih =>
    simp only [executeRounds, treeSimCheckMapStep_isDone]
    split_ifs
    · simp only [treeSimCheckMapStep_output, map_pure]
    · rw [treeSimCheck_stepRound_map, map_bind]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      exact bind_congr fun r => ih r.1 r.2.1

theorem treeSimCheck_startSteps_map {α β : Type} (f : α → β) (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => f <$> program i) =
      (fun steps i => treeSimCheckMapStep f (steps i)) <$>
        startSteps worldRoles D program := by
  simp only [startSteps]
  have hl : ∀ i, (if i ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (f <$> program i).run)) =
      treeSimCheckMapStep f <$>
        (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, map_pure, treeSimCheckMapStep, Option.map_none]
    · simp only [if_neg hi, OptionT.run_map, treeSimCheck_advance_map, worldRoles]
      change free (treeSimCheckMapStep f <$> advance (program i).run) =
        treeSimCheckMapStep f <$> free (advance (program i).run)
      simp only [map_eq_bind_pure_comp, free_bind, free_pure, Function.comp_def]
  simp_rw [hl]
  simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]

theorem treeSimCheck_executePhase_map {α β : Type} (f : α → β) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality fuel state (fun i => f <$> program i) =
      (fun r => (r.1, fun i => (r.2 i).map f)) <$>
        executePhase worldRoles D A noFunctionality fuel state program := by
  rw [executePhase, executePhase, treeSimCheck_startSteps_map, map_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  exact bind_congr fun steps => treeSimCheck_executeRounds_map f D A fuel state steps

theorem treeSimCheckRecord_allowed {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (allowed : (t : spec.Domain) → spec.Range t → Prop)
    (p : OracleComp spec α) (r : α × List ((t : spec.Domain) × spec.Range t))
    (h : TreeSimCheckAllowed allowed (treeSimCheckRecord p) r) :
    TreeSimCheckReplay p r.2 r.1 ∧
      ∀ t u, (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) ∈ r.2 → allowed t u := by
  induction p using OracleComp.inductionOn generalizing r with
  | pure a =>
    rw [treeSimCheckRecord_pure] at h
    have he := h.pure_inv
    subst r
    exact ⟨.pure a, by simp⟩
  | query_bind t k ih =>
    simp only [treeSimCheckRecord_query, map_eq_bind_pure_comp] at h
    obtain ⟨u, hu, ht⟩ := h.bind_inv
    obtain ⟨v, hv, hf⟩ := ht.bind_inv
    have he := hf.pure_inv
    subst r
    obtain ⟨hr, ha⟩ := ih u v hv
    refine ⟨.query t k u v.2 v.1 hr, ?_⟩
    intro t' u' hm
    rcases List.mem_cons.mp hm with he | he
    · cases he
      exact TreeSimCheckAllowed.query_inv t u hu
    · exact ha t' u' he

theorem treeSimCheckRecordedParty_allowed {ι : Type} {G : OracleSpec ι} {α : Type}
    (allowed : (t : (PartySpec C E G).Domain) → (PartySpec C E G).Range t → Prop)
    (p : PartyM C E G α) (a : α)
    (log : List ((t : (PartySpec C E G).Domain) × (PartySpec C E G).Range t))
    (h : TreeSimCheckAllowed allowed (treeSimCheckRecordedParty p).run (some (a, log))) :
    TreeSimCheckReplay p.run log (some a) ∧
      ∀ t u, (⟨t, u⟩ : (t : (PartySpec C E G).Domain) × (PartySpec C E G).Range t) ∈ log → allowed t u := by
  simp only [treeSimCheckRecordedParty, OptionT.run_mk, map_eq_bind_pure_comp] at h
  obtain ⟨r, hr, he⟩ := h.bind_inv
  have he := he.pure_inv
  obtain ⟨hp, ha⟩ := treeSimCheckRecord_allowed allowed p.run r hr
  rcases r with ⟨_ | v, l⟩
  · cases he
  · have he : (v, l) = (a, log) := (Option.some.inj he).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨hp, ha⟩

theorem treeSimCheck_recorded_execution_erase {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → Keys C → PartyM C E RealSpec α) (x : C.Party → Keys C) (z : Aux) :
    (fun r => (r.1, fun i => (r.2 i).map Prod.fst)) <$>
      realExecution D A noFunctionality fuel
        (fun i keys => treeSimCheckRecordedParty (program i keys)) x z =
      realExecution D A noFunctionality fuel program x z := by
  simp only [realExecution, map_bind]
  apply bind_congr
  intro state
  rw [← treeSimCheck_executePhase_map]
  simp only [treeSimCheckRecordedParty_erase]

def treeSimCheckRecordedGame (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) := do
  let r ← realExecution D A noFunctionality (ceremonyFuel circuits settings)
    (fun i keys => treeSimCheckRecordedParty
      (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z
  let b ← worldRoles.adversary (Z (r.1, fun i => (r.2 i).map Prod.fst))
  pure (b, r)

theorem treeSimCheck_recorded_game_erase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Prod.fst <$> treeSimCheckRecordedGame K circuits settings top tree D A x z Z =
      treeRealGame K circuits settings top tree D A x z Z := by
  unfold treeSimCheckRecordedGame treeRealGame distinguish
  conv_rhs => rw [← treeSimCheck_recorded_execution_erase]
  simp only [map_bind, map_pure, bind_map_left, bind_pure_comp, Functor.map_map,
    Function.comp_def, id_map']

/-- Recording party replies preserves the complete world log, including all
queries of the distinguisher, under the actual PRSS handler. -/
theorem treeSimCheck_recorded_logged_erase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    (fun r => (r.1.1, r.2)) <$>
      treeSimLoggedRun prims D (treeSimCheckRecordedGame K circuits settings top tree D A x z Z) =
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z) := by
  rw [← treeSimCheck_recorded_game_erase]
  simp only [treeSimLoggedRun, simulateQ_map, WriterT.run_map, StateT.run'_eq,
    StateT.run_map, Functor.map_map]

end RecordedExecution

abbrev TreeSimCheckPartyLog (C : Committee) (E : Type) :=
  List ((t : (PartySpec C E RealSpec).Domain) × (PartySpec C E RealSpec).Range t)

theorem TreeSimCheckReplay.map {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {p : OracleComp spec α} {log : List ((t : spec.Domain) × spec.Range t)} {a : α}
    (h : TreeSimCheckReplay p log a) (f : α → β) :
    TreeSimCheckReplay (f <$> p) log (f a) := by
  simpa only [List.append_nil, map_eq_bind_pure_comp, Function.comp_def] using
    (h.bind (k := fun a => Pure.pure (f a)) (TreeSimCheckReplay.pure (f a)))

theorem TreeSimCheckReplay.map_inv {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {p : OracleComp spec α} {log : List ((t : spec.Domain) × spec.Range t)} {b : β}
    (f : α → β) (h : TreeSimCheckReplay (f <$> p) log b) :
    ∃ a, TreeSimCheckReplay p log a ∧ f a = b := by
  rw [map_eq_bind_pure_comp] at h
  obtain ⟨a, pre, post, hp, hf, he⟩ := h.bind_inv
  cases hf
  simp only [List.append_nil] at he
  subst log
  exact ⟨a, hp, rfl⟩

theorem treeSimCheck_recorded_execution_replay {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → Keys C → PartyM C E RealSpec α) (x : C.Party → Keys C) (z : Aux)
    (actual : A.State × (C.Party → Option (α × TreeSimCheckPartyLog C E)))
    (log : TreeSimLog C)
    (replay : TreeSimCheckReplay (realExecution D A noFunctionality fuel
      (fun i keys => treeSimCheckRecordedParty (program i keys)) x z) log actual)
    (i : C.Party) (hi : i ∉ D.1) (value : α) (transcript : TreeSimCheckPartyLog C E)
    (out : actual.2 i = some (value, transcript)) :
    TreeSimCheckReplay (program i (x i)).run transcript (some value) ∧
      ∀ t u, (⟨.inl (.inl t), u⟩ : (t : (PartySpec C E RealSpec).Domain) ×
        (PartySpec C E RealSpec).Range t) ∈ transcript →
        (⟨.inr t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log := by
  unfold realExecution at replay
  obtain ⟨state, start, phase, _, hs, hlog⟩ := replay.bind_inv
  have allowed : TreeSimCheckAllowed
      (fun t u => (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun j => treeSimCheckRecordedParty (program j (x j)))) actual := by
    refine ⟨phase, hs, ?_⟩
    intro t u hmem
    simp only [hlog, List.mem_append]
    exact Or.inr hmem
  have party := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ actual allowed
    i hi (value, transcript) out
  obtain ⟨hp, ha⟩ := treeSimCheckRecordedParty_allowed _ _ value transcript party
  exact ⟨hp, fun t u hm => ha (.inl (.inl t)) u hm⟩

/-- The successful party transcript in the annotated game is generated by
the actual scheduler. Its local answers also occur in the retained world log. -/
theorem treeSimCheck_recorded_party_replay (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool)
    (actual : A.State × (C.Party → Option (TreeOutput × TreeSimCheckPartyLog C E)))
    (log : TreeSimLog C)
    (run : ((result, actual), log) ∈ support (treeSimLoggedRun prims D
      (treeSimCheckRecordedGame K circuits settings top tree D A x z Z)))
    (i : C.Party) (hi : i ∉ D.1) (value : TreeOutput) (transcript : TreeSimCheckPartyLog C E)
    (out : actual.2 i = some (value, transcript)) :
    TreeSimCheckReplay
      (ceremony K circuits settings i (x i) top tree : PartyM C E RealSpec TreeOutput).run
      transcript (some value) ∧
      ∀ t u, (⟨.inl (.inl t), u⟩ : (t : (PartySpec C E RealSpec).Domain) ×
        (PartySpec C E RealSpec).Range t) ∈ transcript →
        (⟨.inr t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log := by
  have replay := treeSimCheckReplay_logged prims D _ (result, actual) log run
  unfold treeSimCheckRecordedGame at replay
  obtain ⟨r, pre, tail, hr, ht, hlog⟩ := replay.bind_inv
  obtain ⟨b, mid, post, _, hp, htail⟩ := ht.bind_inv
  cases hp
  unfold realExecution at hr
  obtain ⟨state, start, phase, _, hs, hpre⟩ := hr.bind_inv
  have allowed : TreeSimCheckAllowed
      (fun t u => (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log)
      (executePhase worldRoles D A noFunctionality (ceremonyFuel circuits settings) state
        (fun j => treeSimCheckRecordedParty
          (ceremony K circuits settings j (x j) top tree : PartyM C E RealSpec TreeOutput))) actual := by
    refine ⟨phase, hs, ?_⟩
    intro t u hmem
    simp only [hlog, hpre, List.mem_append]
    exact Or.inl (Or.inr hmem)
  have party := treeSimCheck_phase_replay D A noFunctionality _ _ state _ actual allowed
    i hi (value, transcript) out
  obtain ⟨hp, ha⟩ := treeSimCheckRecordedParty_allowed _ _ value transcript party
  exact ⟨hp, fun t u hm => ha (.inl (.inl t)) u hm⟩

/-- Lift the semantic witness to the recorded execution before inspecting a
batch. Prefix uniqueness fixes the entire successful party transcript, not
only its returned value or a set of permitted local answers. -/
theorem treeSimWrongOutput_recorded_reference (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool)
    (actual : A.State × (C.Party → Option (TreeOutput × TreeSimCheckPartyLog C E)))
    (log : TreeSimLog C)
    (run : ((result, actual), log) ∈ support (treeSimLoggedRun prims D
      (treeSimCheckRecordedGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs i value transcript hash pref,
      x = dealtKeys parameter seeds pairs ∧ i ∉ D.1 ∧
      actual.2 i = some (value, transcript) ∧
      TreeSimCheckReplay
        (ceremony K circuits settings i (x i) top tree : PartyM C E RealSpec TreeOutput).run
        transcript (some value) ∧
      some value ≠ ceremonyAt prims circuits parameter seeds hash top tree ∧
      Good prims hash ∧ pref <+: log ∧
      (∀ t u, (⟨.inl (.inl t), u⟩ : (t : (PartySpec C E RealSpec).Domain) ×
        (PartySpec C E RealSpec).Range t) ∈ transcript →
        TreeSimCheckWorldHashes hash (.inr t) u ∧
        (⟨.inr t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ pref) := by
  have replay := treeSimCheckReplay_logged prims D _ (result, actual) log run
  unfold treeSimCheckRecordedGame at replay
  obtain ⟨r, pre, tail, hr, ht, hlog⟩ := replay.bind_inv
  obtain ⟨b, mid, post, _, hp, _⟩ := ht.bind_inv
  cases hp
  obtain ⟨parameter, seeds, pairs, dealt, out, hx, witness, i, hi, hs, hw⟩ := wrong
  obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨fuel, pref, hf, hprefix, hghost⟩ := witness
  have early := treeSimCheckReplay_ghost prims D _ _ dealt out pref hghost
  rw [← treeSimCheck_recorded_execution_erase] at early
  obtain ⟨recorded, hearly, herase⟩ := early.map_inv _
  have hvalue : (recorded.2 i).map Prod.fst = some value := by
    have he := congrArg (fun r => r.2 i) herase
    exact he.trans hv
  obtain ⟨pair, hpair, hfst⟩ := Option.map_eq_some_iff.mp hvalue
  rcases pair with ⟨v, transcript⟩
  change v = value at hfst
  subst v
  have same := treeSimCheckReplay_execution_mono D A noFunctionality fuel
    (ceremonyFuel circuits settings) hf
    (fun j keys => treeSimCheckRecordedParty
      (ceremony K circuits settings j keys top tree : PartyM C E RealSpec TreeOutput))
    (dealtKeys parameter seeds pairs) z recorded actual pref pre log hearly (hx ▸ hr)
    hprefix (hlog ▸ List.prefix_append pre tail) i (value, transcript) hpair
  obtain ⟨party, answers⟩ := treeSimCheck_recorded_execution_replay D A fuel _
    (dealtKeys parameter seeds pairs) z recorded pref hearly i hi value transcript hpair
  obtain ⟨hash, hg, hd, hall⟩ := treeSimCheck_ghost_hashes prims D
    (dealerCeremony circuits settings parameter seeds top tree) _ dealt out pref hghost
  have href : dealt.1 = ceremonyAt prims circuits parameter seeds hash top tree := by
    rw [hd, D_dealerCeremony prims circuits settings parameter seeds hash top tree hbatch]
  refine ⟨parameter, seeds, pairs, i, value, transcript, hash, pref,
    hx, hi, same, ?_, ?_, hg, hprefix, ?_⟩
  · simpa only [hx] using party
  · simpa only [hv, href] using hw
  · intro t u hm
    exact ⟨hall (.inr t) u (answers t u hm), answers t u hm⟩

theorem treeSimWrongOutput_recorded_first_batch (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool)
    (actual : A.State × (C.Party → Option (TreeOutput × TreeSimCheckPartyLog C E)))
    (log : TreeSimLog C)
    (run : ((result, actual), log) ∈ support (treeSimLoggedRun prims D
      (treeSimCheckRecordedGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs i value transcript hash prss,
      x = dealtKeys parameter seeds pairs ∧ i ∉ D.1 ∧
      actual.2 i = some (value, transcript) ∧
      TreeSimCheckReplay
        (ceremony K circuits settings i (x i) top tree : PartyM C E RealSpec TreeOutput).run
        transcript (some value) ∧
      some value ≠ ceremonyAt prims circuits parameter seeds hash top tree ∧
      Good prims hash ∧
      TreeSimCheckFirstBatch prims K circuits settings
        (fun t u => (⟨t, u⟩ : (t : (PartySpec C E RealSpec).Domain) ×
          (PartySpec C E RealSpec).Range t) ∈ transcript)
        ⟨i, x i, prss⟩ seeds hash tree := by
  obtain ⟨parameter, seeds, pairs, i, value, transcript, hash, pref,
    hx, hi, hout, replay, hwrong, hg, _, answers⟩ :=
    treeSimWrongOutput_recorded_reference prims K circuits settings hbatch
      top tree D A x z Z result actual log run wrong
  let allowed := fun t u => (⟨t, u⟩ : (t : (PartySpec C E RealSpec).Domain) ×
    (PartySpec C E RealSpec).Range t) ∈ transcript
  have hparty : TreeSimCheckAllowed allowed
      (ceremony K circuits settings i (x i) top tree : PartyM C E RealSpec TreeOutput).run
        (some value) := ⟨transcript, replay, fun _ _ h => h⟩
  obtain ⟨prss, final, _, hbody⟩ := treeSimCheck_ceremony_body_replay K circuits settings allowed
    i (x i) top tree value hparty
  have hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u :=
    fun q u h => (answers (.inr (.inl q)) u h).1
  have hfirst := treeSimCheck_body_first_wrong_batch prims K circuits settings hbatch allowed hash
    hhash ⟨i, x i, prss⟩ seeds top tree value final hbody
    (by simpa only [hx, dealtKeys] using hwrong)
  exact ⟨parameter, seeds, pairs, i, value, transcript, hash, prss,
    hx, hi, hout, replay, hwrong, hg, hfirst⟩

def treeSimCheckFieldIndex (count : ℕ) :
    Fin count × Fin elementBits ≃ Fin (elementBits * count) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm count elementBits))

theorem treeSimCheckFieldIndex_val (count : ℕ) (g : Fin count) (b : Fin elementBits) :
    (treeSimCheckFieldIndex count (g, b)).val = elementBits * g.val + b.val := by
  simp [treeSimCheckFieldIndex, finProdFinEquiv, Nat.add_comm]

/-- `Constants.encode` is used only as a bijection. No linearity of the field
encoding or preservation of zero is assumed. -/
def treeSimCheckFieldTable (count : ℕ) :
    (Fin (elementBits * count) → Bit) ≃ (Fin count → E) where
  toFun bits g := K.encode.symm (fun b => bits (treeSimCheckFieldIndex count (g, b)))
  invFun vals j := K.encode (vals ((treeSimCheckFieldIndex count).symm j).1)
    ((treeSimCheckFieldIndex count).symm j).2
  left_inv bits := by
    funext j
    simp only [Equiv.apply_symm_apply]
    congr 1
    exact (treeSimCheckFieldIndex count).apply_symm_apply j
  right_inv vals := by
    funext g
    simp only [Equiv.symm_apply_apply]

def treeSimCheckFieldPad {count : ℕ} (vals : Fin count → E) : ℕ → E :=
  fun g => if h : g < count then vals ⟨g, h⟩ else K.encode.symm (fun _ => 0)

theorem treeSimCheck_field_decode (count : ℕ) (bits : Fin (elementBits * count) → Bit) :
    (fun g => K.encode.symm (fun b => (List.ofFn bits).getD (elementBits * g + b) 0)) =
      treeSimCheckFieldPad K (treeSimCheckFieldTable K count bits) := by
  funext g
  unfold treeSimCheckFieldPad
  split_ifs with hg
  · change K.encode.symm _ = K.encode.symm _
    apply congrArg K.encode.symm
    funext b
    have hb : elementBits * g + b.val < elementBits * count := by
      have h := (treeSimCheckFieldIndex count (⟨g, hg⟩, b)).isLt
      simpa only [treeSimCheckFieldIndex_val] using h
    simp only [treeSimCheckFieldTable, Equiv.coe_fn_mk, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dif_pos hb, Option.getD_some]
    congr 1
    apply Fin.ext
    exact (treeSimCheckFieldIndex_val count ⟨g, hg⟩ b).symm
  · apply congrArg K.encode.symm
    funext b
    have hb : ¬ elementBits * g + b.val < elementBits * count := by
      have hm := Nat.mul_le_mul_left elementBits (Nat.le_of_not_gt hg)
      omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hb,
      Option.getD_none]

theorem treeSimCheck_elementDraw_table (name : KeyName C) (key : HashOutput)
    (label idx count : ℕ) :
    free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)) =
      (fun bits => treeSimCheckFieldPad K (treeSimCheckFieldTable K count bits)) <$>
        hiddenDraws (fun g : Fin (elementBits * count) => ((name, key), label, idx, g.val)) := by
  simp only [elementCodec, liftComp_bind, liftComp_pure, free_bind, free_pure]
  rw [treeSim_prgBits_table]
  simp only [bind_map_left, bind_pure_comp, Functor.map_map, Function.comp_def,
    treeSimCheck_field_decode]
  congr 1
  funext bits
  exact treeSimCheck_field_decode K count bits

theorem treeSimCheck_elementDraw_fresh [SampleableType E] (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (hidden : Hidden D name)
    (label idx count : ℕ) (cache : HashCache C) (streams : HiddenCache C)
    (fresh : ∀ g : Fin (elementBits * count), streams ((name, key), label, idx, g.val) = none) :
    𝒟[(simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run
        (cache, streams)] =
      𝒟[(fun vals : Fin count → E => (treeSimCheckFieldPad K vals,
        (cache, cacheFin (fun g : Fin (elementBits * count) => ((name, key), label, idx, g.val))
          ((treeSimCheckFieldTable K count).symm vals) streams))) <$> ($ᵗ (Fin count → E))] := by
  let addr := fun g : Fin (elementBits * count) => ((name, key), label, idx, g.val)
  have hinj : Function.Injective addr := by
    intro a b he
    apply Fin.ext
    exact congrArg (fun x => x.2.2.2) he
  have hdraw := streamWorld_sequenceFin_fresh prims D addr hinj (fun _ => hidden)
    cache streams fresh
  rw [treeSimCheck_elementDraw_table]
  simp only [simulateQ_map, StateT.run_map, evalDist_map]
  rw [show 𝒟[(simulateQ (streamWorld prims D) (hiddenDraws addr)).run (cache, streams)] =
    𝒟[(fun vals => (vals, (cache, cacheFin addr vals streams))) <$>
      ($ᵗ (Fin (elementBits * count) → Bit))] from hdraw]
  rw [← evalDist_map, Functor.map_map]
  have hu := evalDist_map_bijective_uniform_cross (α := Fin (elementBits * count) → Bit)
    (treeSimCheckFieldTable K count) (treeSimCheckFieldTable K count).bijective
  rw [← hu]
  simp only [← evalDist_map, Functor.map_map, Function.comp_def, Equiv.symm_apply_apply]
  rfl

/-- The value fixed by the honest Coin shares, even if those shares do not
form a codeword. Such a malformed opening can only abort or return this value. -/
def treeSimCheckCoinValues (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) : Fin count → E := fun g =>
  interpolate K D.1 (fun j => conv K (localContext j) (rnd j).1 g) 0

theorem treeSimCheck_coin_arbitrary (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (sent : C.Party → C.Party → Option (Msg E))
    (i : C.Party) (hi : i ∉ D.1) :
    treeSimCoinOutput K D count rnd sent i = none ∨
      treeSimCoinOutput K D count rnd sent i =
        some (List.ofFn (treeSimCheckCoinValues K D count rnd)) := by
  let inbox : Mail C E := fun j =>
    if j ∈ D.1 then sent j i else coinOut K j count (rnd j) i
  let v := conv K (localContext i) (rnd i).1
  have hhonest : ∀ j, j ∉ D.1 → ∀ g < count,
      openShare (localContext i).self v inbox j g = conv K (localContext j) (rnd j).1 g := by
    intro j hj g hg
    simp only [openShare, inbox, hj, if_false, coinOut, openOut]
    split_ifs with hji hij
    · subst j
      rfl
    · exact absurd hij.symm hji
    · exact vector_getD _ _ g hg
  simp only [treeSimCoinOutput, if_neg hi]
  change coinRes K i count (rnd i) inbox = none ∨
    coinRes K i count (rnd i) inbox = some (List.ofFn (treeSimCheckCoinValues K D count rnd))
  unfold coinRes
  by_cases hab : anyAbort inbox = true
  · exact Or.inl (if_pos hab)
  rw [if_neg hab]
  unfold openRes
  split_ifs with hc
  · right
    simp only [Option.map_some, vector, List.ofFn_eq_map, Option.some.injEq]
    apply List.ext_getElem
    · simp
    · intro g hg₁ hg₂
      have hg : g < count := by simpa using hg₁
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange,
        treeSimCheckCoinValues]
      let P := Lagrange.interpolate (firstParties C) K.point (fun l => openShare i v inbox l g)
      have hPdeg : P.degree < C.t := by
        simpa only [card_firstParties] using
          (Lagrange.degree_interpolate_lt (r := fun l => openShare i v inbox l g)
            (K.point.injective.injOn (s := firstParties C)))
      have hP : P.natDegree ≤ C.t - 1 := by
        by_cases hz : P = 0
        · simp [hz]
        · rw [Polynomial.degree_eq_natDegree hz] at hPdeg
          have hn : P.natDegree < C.t := by exact_mod_cast hPdeg
          omega
      have he := interpolate_honest_polynomial K D P hP
        (fun j => conv K (localContext j) (rnd j).1 g) (fun j hj => by
          rw [← hhonest j hj g hg]
          exact (hc j g hg).trans (eval_interpolate_first K _ (K.point j)).symm) 0
      exact (eval_interpolate_first K _ 0).symm.trans he.symm
  · exact Or.inl rfl

def treeSimCheckCoinShift {count : ℕ} (T₀ : C.Term) (delta : Fin count → E)
    (rnd : C.Party → PrssOutput C E) : C.Party → PrssOutput C E := fun i =>
  (fun T g => (rnd i).1 T g +
    if i ∈ C.holders T ∧ T = T₀ then (if h : g < count then delta ⟨g, h⟩ else 0) else 0,
   (rnd i).2)

theorem treeSimCheck_coin_shift_conv {count : ℕ} (T₀ : C.Term) (delta : Fin count → E)
    (rnd : C.Party → PrssOutput C E) (i : C.Party) (g : Fin count) :
    conv K (localContext i) (treeSimCheckCoinShift T₀ delta rnd i).1 g =
      conv K (localContext i) (rnd i).1 g +
        conv K (localContext i) (fun T _ => if T = T₀ then delta g else 0) g := by
  simp only [treeSimCheckCoinShift, conv, mul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hh : i ∈ C.holders T := (Finset.mem_filter.mp hT).2
  simp only [hh, true_and, dif_pos g.isLt]

theorem treeSimCheck_coin_shift_values {count : ℕ} (D : C.Coalition)
    (T₀ : C.Term) (delta : Fin count → E) (rnd : C.Party → PrssOutput C E) :
    treeSimCheckCoinValues K D count (treeSimCheckCoinShift T₀ delta rnd) =
      treeSimCheckCoinValues K D count rnd + delta := by
  funext g
  simp only [treeSimCheckCoinValues, treeSimCheck_coin_shift_conv, Pi.add_apply]
  have hadd : ∀ a b : C.Party → E,
      interpolate K D.1 (fun i => a i + b i) 0 =
        interpolate K D.1 a 0 + interpolate K D.1 b 0 := by
    intro a b
    simp only [interpolate, mul_add, Finset.sum_add_distrib]
  rw [hadd]
  congr 1
  obtain ⟨P, hP, hP0, hPi⟩ := conv_poly K (fun T => if T = T₀ then delta g else 0)
  exact (interpolate_honest_polynomial K D P hP _ (fun i _ => hPi i) 0).trans
    (hP0.trans (by simp))

/-- A fresh common term makes the actual Coin opening a uniform public
value with selective abort, even when other term copies disagree. The
answer can retain both oracle caches and arbitrary surrounding state. -/
theorem treeSimCheck_coin_uniform [SampleableType E] {σ : Type} (D : C.Coalition)
    (count : ℕ) (T₀ : C.Term) (rnd : C.Party → PrssOutput C E)
    (answer : (Fin count → E) → (C.Party → C.Party → Option (Msg E)) →
      ProbComp (σ × (C.Party → C.Party → Option (Msg E)))) :
    𝒟[(do
      let delta ← $ᵗ (Fin count → E)
      let shifted := treeSimCheckCoinShift T₀ delta rnd
      let b ← answer delta (treeSimCoinView K D count shifted)
      pure (b.1, treeSimCoinOutput K D count shifted b.2) :
        ProbComp (σ × (C.Party → Option (List E))))] =
    𝒟[(do
      let vals ← $ᵗ (Fin count → E)
      let delta := vals - treeSimCheckCoinValues K D count rnd
      let shifted := treeSimCheckCoinShift T₀ delta rnd
      let b ← answer delta (treeSimCoinView K D count shifted)
      pure (b.1, fun i => (treeSimCoinOutput K D count shifted b.2 i).map
        (fun _ => List.ofFn vals)) : ProbComp (σ × (C.Party → Option (List E))))] := by
  let base := treeSimCheckCoinValues K D count rnd
  let k := fun delta : Fin count → E => do
    let shifted := treeSimCheckCoinShift T₀ delta rnd
    let b ← answer delta (treeSimCoinView K D count shifted)
    pure (b.1, treeSimCoinOutput K D count shifted b.2)
  have hshift : 𝒟[($ᵗ (Fin count → E)) >>= k] =
      𝒟[(do let vals ← $ᵗ (Fin count → E); k (vals - base))] := by
    have he := evalDist_map_bijective_uniform_cross (α := Fin count → E)
      (fun vals => vals - base) (by
        constructor
        · intro a b h
          simpa only [sub_add_cancel] using congrArg (fun x => x + base) h
        · intro b
          exact ⟨b + base, add_sub_cancel_right b base⟩)
    rw [evalDist_bind, ← he, ← evalDist_bind, bind_map_left]
  calc
    _ = 𝒟[(do let vals ← $ᵗ (Fin count → E); k (vals - base))] := hshift
    _ = _ := by
      apply evalDist_bind_congr_all
      intro vals
      apply evalDist_bind_congr_all
      intro b
      congr 2
      congr 1
      funext i
      change treeSimCoinOutput K D count (treeSimCheckCoinShift T₀ (vals - base) rnd) b.2 i =
        (treeSimCoinOutput K D count (treeSimCheckCoinShift T₀ (vals - base) rnd) b.2 i).map
          (fun _ => List.ofFn vals)
      by_cases hi : i ∈ D.1
      · simp [treeSimCoinOutput, hi]
      · rcases treeSimCheck_coin_arbitrary K D count
          (treeSimCheckCoinShift T₀ (vals - base) rnd) b.2 i hi with h | h
        · simp [h]
        · have hv : treeSimCheckCoinValues K D count
              (treeSimCheckCoinShift T₀ (vals - base) rnd) = vals := by
            rw [treeSimCheck_coin_shift_values]
            dsimp only [base]
            abel
          simp only [h, hv, Option.map_some]

theorem treeSimCheck_coin_shift_outputs (D : C.Coalition) (count : ℕ)
    (T₀ : C.Term) (rnd : C.Party → PrssOutput C E) (vals : Fin count → E)
    (sent : C.Party → C.Party → Option (Msg E)) :
    let shifted := treeSimCheckCoinShift T₀ (vals - treeSimCheckCoinValues K D count rnd) rnd
    treeSimCoinOutput K D count shifted sent = fun i =>
      (treeSimCoinOutput K D count shifted sent i).map (fun _ => List.ofFn vals) := by
  dsimp only
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinOutput, hi]
  · rcases treeSimCheck_coin_arbitrary K D count
      (treeSimCheckCoinShift T₀ (vals - treeSimCheckCoinValues K D count rnd) rnd) sent i hi with h | h
    · simp only [h, Option.map_none]
    · have hv : treeSimCheckCoinValues K D count
          (treeSimCheckCoinShift T₀ (vals - treeSimCheckCoinValues K D count rnd) rnd) = vals := by
        rw [treeSimCheck_coin_shift_values]
        abel
      simp only [h, hv, Option.map_some]

/-- Normalization of a complete scheduled Coin round, including the actual
rushing call, all continuations in driver order, and the final handler state.
The incoming state may retain the sampled field block in its private cache. -/
theorem treeSimCheck_coin_scheduled [SampleableType E] {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (count : ℕ) (T₀ : C.Term) (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (initial : (Fin count → E) → σ) :
    𝒟[(do
      let delta ← $ᵗ (Fin count → E)
      (simulateQ impl (stepRound worldRoles D A noFunctionality state
        (treeSimCoinWaiting K D count (treeSimCheckCoinShift T₀ delta rnd) st k))).run
          (initial delta))] =
    𝒟[(do
      let vals ← $ᵗ (Fin count → E)
      let delta := vals - treeSimCheckCoinValues K D count rnd
      let shifted := treeSimCheckCoinShift T₀ delta rnd
      let b ← (simulateQ impl (worldRoles.adversary
        (A.round state (treeSimCoinView K D count shifted)))).run (initial delta)
      let next ← (simulateQ impl (treeSimResumeAll k (fun i =>
        (treeSimCoinOutput K D count shifted b.1.2 i).map
          (fun _ => (List.ofFn vals, nextLabel (st i)))))).run b.2
      pure ((b.1.1, next.1, b.1.2), next.2))] := by
  let base := treeSimCheckCoinValues K D count rnd
  have hu := evalDist_map_bijective_uniform_cross (α := Fin count → E)
    (fun vals => vals - base) (by
      constructor
      · intro a b h
        simpa only [sub_add_cancel] using congrArg (fun x => x + base) h
      · intro b
        exact ⟨b + base, add_sub_cancel_right b base⟩)
  conv_lhs => rw [evalDist_bind, ← hu, ← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr_all
  intro vals
  simp only [treeSim_coin_round_factor, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  apply evalDist_bind_congr_all
  intro b
  have hout := treeSimCheck_coin_shift_outputs K D count T₀ rnd vals b.1.2
  have hm : (fun i => (treeSimCoinOutput K D count
        (treeSimCheckCoinShift T₀ (vals - base) rnd) b.1.2 i).map
          (fun xs => (xs, nextLabel (st i)))) =
      (fun i => (treeSimCoinOutput K D count
        (treeSimCheckCoinShift T₀ (vals - base) rnd) b.1.2 i).map
          (fun _ => (List.ofFn vals, nextLabel (st i)))) := by
    funext i
    have hi := congrFun hout i
    have he := congrArg (Option.map (fun xs => (xs, nextLabel (st i)))) hi
    simpa only [Option.map_map, Function.comp_def] using he
  rw [hm]

/-- A successful prefix uses exactly the displayed number of exchanges.
The local work after its last exchange is pure; aborts may happen earlier. -/
inductive TreeSimCheckTimed {α : Type} :
    ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | abort (n : ℕ) : TreeSimCheckTimed n (pure none)
  | done (a : α) : TreeSimCheckTimed 0 (pure (some a))
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, TreeSimCheckTimed (n + 1) (k r)) :
      TreeSimCheckTimed (n + 1) (.roll (.inl (.inl q)) k)
  | round (n : ℕ) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, TreeSimCheckTimed n (k r)) :
      TreeSimCheckTimed (n + 1) (.roll (.inl (.inr out)) k)

theorem TreeSimCheckTimed.zero {α : Type}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSimCheckTimed 0 p) :
    ∃ a, p = pure a := by
  cases h with
  | abort => exact ⟨none, rfl⟩
  | done a => exact ⟨some a, rfl⟩

theorem TreeSimCheckTimed.bind {α β : Type} {m n : ℕ}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : TreeSimCheckTimed m p.run) (hk : ∀ a, TreeSimCheckTimed n (k a).run) :
    TreeSimCheckTimed (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TreeSimCheckTimed (m + n)
    (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | abort m => simpa only [pure_bind, Option.elim_none] using TreeSimCheckTimed.abort (m + n)
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hk a
  | queryLocal m q f hf ih =>
    rw [Nat.add_right_comm m 1 n]
    change TreeSimCheckTimed (m + n + 1) (.roll (.inl (.inl q)) _)
    apply TreeSimCheckTimed.queryLocal
    intro r
    simpa only [Nat.add_right_comm m 1 n, OracleComp.bind_def] using ih r
  | round m out f hf ih =>
    rw [Nat.add_right_comm m 1 n]
    change TreeSimCheckTimed (m + n + 1) (.roll (.inl (.inr out)) _)
    exact TreeSimCheckTimed.round (m + n) out _ ih

/-- The complete local state at a synchronous prefix boundary. -/
def TreeSimCheckTimedStep {α : Type} (n : ℕ) (step : Step C E RealSpec α) : Prop :=
  match n, step with
  | 0, .done _ => True
  | _ + 1, .done out => out = none
  | 0, .wait _ _ => False
  | n + 1, .wait _ resume => ∀ inbox, TreeSimCheckTimed n (resume inbox)
  | _, .call input _ => input.elim

theorem TreeSimCheckTimed.advance_mem {α : Type} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSimCheckTimed n p) :
    ∀ step ∈ support (advance p), TreeSimCheckTimedStep n step := by
  induction h with
  | abort n =>
    intro step hs
    change step ∈ support (pure (.done none) : OracleComp (LocalSpec C) (Step C E RealSpec α)) at hs
    have he : step = .done none := by simpa using hs
    subst step
    cases n <;> simp [TreeSimCheckTimedStep]
  | done a =>
    intro step hs
    change step ∈ support (pure (.done (some a)) : OracleComp (LocalSpec C) (Step C E RealSpec α)) at hs
    have he : step = .done (some a) := by simpa using hs
    subst step
    trivial
  | queryLocal n q k h ih =>
    intro step hs
    obtain ⟨r, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hs
    exact ih r step hr
  | round n out k h ih =>
    intro step hs
    have he : step = .wait out k := by simpa [advance] using hs
    subst step
    exact h

theorem TreeSimCheckTimedStep.pending {α : Type} {n : ℕ} {step : Step C E RealSpec α}
    (h : TreeSimCheckTimedStep (n + 1) step) : step.output = none := by
  cases step with
  | done out => exact h
  | wait out resume => rfl
  | call input resume => exact input.elim

theorem TreeSimCheckTimed.suspend {α β : Type} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSimCheckTimed (n + 1) p)
    (k : α → PartyM C E RealSpec β) :
    advance p >>= continueStep k = suspendStep k <$> advance p := by
  rw [map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro step hs
  exact continueStep_pending k step (h.advance_mem step hs).pending

theorem TreeSimCheckTimedStep.final {α : Type} {step : Step C E RealSpec α}
    (h : TreeSimCheckTimedStep 0 step) : ∃ a, step = .done a := by
  cases step with
  | done a => exact ⟨a, rfl⟩
  | wait out resume => exact h.elim
  | call input resume => exact input.elim

theorem treeSimCheckTimed_start {α β : Type} (D : C.Coalition) (n : ℕ)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, TreeSimCheckTimed (n + 1) (p i).run) :
    startSteps worldRoles D (fun i => p i >>= k i) =
      (fun steps i => suspendStep (k i) (steps i)) <$> startSteps worldRoles D p := by
  exact startSteps_suspend D p k (fun i => (hp i).suspend (k i))

theorem treeSimCheck_support_free {α : Type} (p : OracleComp (LocalSpec C) α) :
    support (free p) ⊆ support p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [free_pure]; exact Set.Subset.rfl
  | query_bind q k ih =>
    rw [free_bind]
    intro a ha
    obtain ⟨r, _, hr⟩ := (mem_support_bind_iff _ _ _).mp ha
    exact (mem_support_bind_iff _ _ _).mpr ⟨r, by simp, ih r hr⟩

theorem treeSimCheckTimed_roundLocal {α : Type} (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (sent : C.Party → Mail C E)
    (hs : ∀ i, TreeSimCheckTimedStep (n + 1) (steps i)) :
    ∀ i next, next ∈ support (roundLocal D steps sent i) → TreeSimCheckTimedStep n next := by
  intro i next hn
  have h := hs i
  cases he : steps i with
  | done out =>
    have ho : out = none := by simpa only [he, TreeSimCheckTimedStep] using h
    subst out
    have hn' : next = .done none := by simpa only [roundLocal, he, support_pure,
      Set.mem_singleton_iff] using hn
    subst next
    cases n <;> simp [TreeSimCheckTimedStep]
  | call input resume => exact input.elim
  | wait out resume =>
    simp only [roundLocal, he] at hn
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, support_pure, Set.mem_singleton_iff] at hn
      subst next
      cases n <;> simp [TreeSimCheckTimedStep]
    · simp only [if_neg hi] at hn
      simp only [he, TreeSimCheckTimedStep] at h
      exact (h _).advance_mem next hn

theorem treeSimCheckTimed_round {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i, TreeSimCheckTimedStep (n + 1) (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps),
      ∀ i, TreeSimCheckTimedStep n (r.2.1 i) := by
  rw [stepRound_real]
  intro r hr
  obtain ⟨sent, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨next, hn, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have he : r = (sent.1, next, sent.2) := by simpa using hr
  subst r
  have hl := treeSimCheck_support_free _ hn
  intro i
  exact treeSimCheckTimed_roundLocal D n steps sent.2 hs i (next i)
    (mem_support_sequenceFin_oc _ _ hl i)

/-- Exact composition at a joint synchronous boundary. The left side runs
the continuations in the original scheduler; the right side exposes all
prefix outputs and the adversary state before starting those continuations. -/
theorem treeSimCheckTimed_rounds_split {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hs : ∀ i, TreeSimCheckTimedStep (n + 1) (steps i)) :
    executeRounds worldRoles D A noFunctionality (n + 1 + fuel) state
      (fun i => suspendStep (k i) (steps i)) = (do
      let p ← executeRounds worldRoles D A noFunctionality (n + 1) state steps
      let next ← free (Concrete.sequenceFin fun i => continueStep (k i) (.done (p.2 i)))
      executeRounds worldRoles D A noFunctionality fuel p.1 next) := by
  induction n generalizing state steps with
  | zero =>
    rw [Nat.zero_add, Nat.add_comm 1 fuel]
    apply executeRounds_suspend_finish D A fuel state steps k (fun i => (hs i).pending)
    intro i out resume he hi inbox
    have h : TreeSimCheckTimed 0 (resume inbox) := (he ▸ hs i) inbox
    obtain ⟨result, hr⟩ := h.zero
    exact ⟨result, by rw [hr]; rfl⟩
  | succ n ih =>
    rw [Nat.succ_add, executeRounds, executeRounds]
    simp only [suspendStep_isDone]
    split_ifs with hd
    · simp only [suspendStep_output, (fun i => (hs i).pending), pure_bind, continueStep,
        sequenceFin_pure, free_pure, executeRounds_all_none]
    · rw [stepRound_suspend D A state steps k (fun i => (hs i).pending)
        (fun i out resume he hi inbox => ((he ▸ hs i) inbox).suspend (k i))]
      simp only [bind_assoc, pure_bind]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro r hr
      exact ih r.1 r.2.1 (treeSimCheckTimed_round D A (n + 1) state steps hs r hr)

theorem treeSimCheckTimed_start_mem {α : Type} (D : C.Coalition) (n : ℕ)
    (p : C.Party → PartyM C E RealSpec α) (hp : ∀ i, TreeSimCheckTimed n (p i).run) :
    ∀ steps ∈ support (startSteps worldRoles D p), ∀ i, TreeSimCheckTimedStep n (steps i) := by
  intro steps hs i
  have hi := mem_support_sequenceFin_oc _ _ hs i
  by_cases hc : i ∈ D.1
  · have he : steps i = .done none := by simpa only [if_pos hc, support_pure,
      Set.mem_singleton_iff] using hi
    rw [he]
    cases n <;> simp [TreeSimCheckTimedStep]
  · simp only [if_neg hc, worldRoles] at hi
    exact (hp i).advance_mem _ (treeSimCheck_support_free _ hi)

theorem treeSimCheckTimed_phase_split {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, TreeSimCheckTimed (n + 1) (p i).run) :
    executePhase worldRoles D A noFunctionality (n + 1 + fuel) state (fun i => p i >>= k i) = (do
      let out ← executePhase worldRoles D A noFunctionality (n + 1) state p
      let next ← free (Concrete.sequenceFin fun i => continueStep (k i) (.done (out.2 i)))
      executeRounds worldRoles D A noFunctionality fuel out.1 next) := by
  simp only [executePhase, treeSimCheckTimed_start D n p k hp, bind_map_left, bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro steps hs
  exact treeSimCheckTimed_rounds_split D A n fuel state steps k
    (treeSimCheckTimed_start_mem D (n + 1) p hp steps hs)

set_option backward.isDefEq.respectTransparency false in
theorem TreeSimCheckTimed.local_bind {α β : Type} (n : ℕ) (p : OracleComp (LocalSpec C) α)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, TreeSimCheckTimed (n + 1) (k a).run) :
    TreeSimCheckTimed (n + 1) (localStep p >>= k).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM,
    bind_map_left, bind_assoc, pure_bind, Option.elim_some]
  change TreeSimCheckTimed (n + 1)
    (liftComp p (PartySpec C E RealSpec) >>= fun a => (k a).run)
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [liftComp_pure, pure_bind] using hk a
  | query_bind q f ih =>
    simp only [liftComp_bind, liftComp_query, bind_assoc]
    have hq : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
      rw [← liftM_query_local]
      rfl
    rw [hq]
    exact TreeSimCheckTimed.queryLocal n q _ ih

theorem TreeSimCheckTimed.oracle_bind {α β : Type} (n : ℕ) (p : OracleComp (RoSpec C) α)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, TreeSimCheckTimed (n + 1) (k a).run) :
    TreeSimCheckTimed (n + 1) (oracleStep p >>= k).run :=
  TreeSimCheckTimed.local_bind n (liftComp p _) k hk

set_option backward.isDefEq.respectTransparency false in
theorem TreeSimCheckTimed.exchange_bind {α : Type} (n : ℕ) (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, TreeSimCheckTimed n (k inbox).run) :
    TreeSimCheckTimed (n + 1) (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk,
      pure_bind, Option.elimM]
    apply bind_congr
    intro inbox
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  apply TreeSimCheckTimed.round
  intro inbox
  change TreeSimCheckTimed n (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact TreeSimCheckTimed.abort n
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

theorem treeSimCheckTimed_reshare {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (rnd : PrssOutput C R) (v : ℕ → R) (count : ℕ) (st : RunState C) :
    TreeSimCheckTimed 1 ((reshare (G := RealSpec) K ctx codec rnd v count).run st).run := by
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run]
  exact TreeSimCheckTimed.exchange_bind 0 _ _ (fun _ => .done _)

theorem treeSimCheckTimed_collector (ctx : Context C) (rnd : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) (st : RunState C) :
    TreeSimCheckTimed 2 ((reshareCollector (G := RealSpec) K ctx rnd v count).run st).run := by
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshareCollector_run]
  exact TreeSimCheckTimed.exchange_bind 1 _ _ (fun _ =>
    TreeSimCheckTimed.exchange_bind 0 _ _ (fun _ => .done _))

theorem treeSimCheckTimed_mult (ctx : Context C) (mode : ReshareMode)
    (x y : Shares C Bit) (count : ℕ) (st : RunState C) :
    TreeSimCheckTimed mode.rounds
      (((realRunGadgets (G := RealSpec) K ctx mode).mult x y count).run st).run := by
  change TreeSimCheckTimed mode.rounds
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshareWith K ctx mode rnd (mulRep K ctx x y) count).run st).run)
  rw [prssRandomness_run]
  cases mode with
  | peer =>
    exact TreeSimCheckTimed.oracle_bind 0 _ _ (fun rnd =>
      treeSimCheckTimed_reshare K ctx bitCodec rnd _ count _)
  | collector =>
    exact TreeSimCheckTimed.oracle_bind 1 _ _ (fun rnd =>
      treeSimCheckTimed_collector K ctx rnd _ count _)

theorem treeSimCheckTimed_rerand (ctx : Context C) (mode : ReshareMode)
    (v : Shares C Bit) (count : ℕ) (st : RunState C) :
    TreeSimCheckTimed 1 (((realRunGadgets (G := RealSpec) K ctx mode).rerand v count).run st).run := by
  change TreeSimCheckTimed 1
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count).run st).run)
  rw [prssRandomness_run]
  exact TreeSimCheckTimed.oracle_bind 0 _ _ (fun rnd =>
    treeSimCheckTimed_reshare K ctx bitCodec rnd _ count _)

theorem TreeSimCheckTimed.state_bind {σ α β : Type} (m n : ℕ)
    (p : StateT σ (PartyM C E RealSpec) α) (k : α → StateT σ (PartyM C E RealSpec) β)
    (hp : ∀ s, TreeSimCheckTimed m (p.run s).run)
    (hk : ∀ a s, TreeSimCheckTimed n ((k a).run s).run) (s : σ) :
    TreeSimCheckTimed (m + n) ((p >>= k).run s).run := by
  rw [StateT.run_bind]
  exact (hp s).bind (fun a => hk a.1 a.2)

theorem TreeSimCheckTimed.foldlM {σ α β : Type} (n : ℕ)
    (f : α → β → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a b s, TreeSimCheckTimed n ((f a b).run s).run) (xs : List β) (a : α) (s : σ) :
    TreeSimCheckTimed (xs.length * n) ((xs.foldlM f a).run s).run := by
  induction xs generalizing a s with
  | nil =>
    simp only [List.foldlM_nil, List.length_nil, Nat.zero_mul, StateT.run_pure, OptionT.run_pure]
    exact .done _
  | cons b xs ih =>
    simp only [List.foldlM_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_comm]
    exact TreeSimCheckTimed.state_bind n (xs.length * n) (f a b)
      (fun a => xs.foldlM f a) (hf a b) (fun a s => ih a s) s

theorem treeSimCheckTimed_layer (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (p : List (C.Term → List Bit) × List (Tuple C)) (layer : ℕ)
    (st : RunState C) :
    TreeSimCheckTimed mode.rounds
      ((layerBody K (realRunGadgets (G := RealSpec) K ctx mode) jobs p layer).run st).run := by
  unfold layerBody
  simp only [StateT.run_bind, StateT.run_pure]
  exact Nat.add_zero mode.rounds ▸
    (treeSimCheckTimed_mult K ctx mode _ _ _ st).bind (fun _ => .done _)

/-- The real batch prefix ends exactly where the actual tuple check begins. -/
def treeSimCheckBeforeVerify (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunM C E RealSpec (Shares C Bit × List (Tuple C)) := do
  let gadgets := realRunGadgets K ctx mode
  let p ← (List.range (depth jobs)).foldlM (layerBody K gadgets jobs) (inputs, [])
  let v' ← gadgets.rerand (outputShares K jobs p.1) (outputsOf jobs).length
  pure (v', p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩])

theorem treeSimCheckBeforeVerify_timed (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (st : RunState C) :
    TreeSimCheckTimed (depth jobs * mode.rounds + 1)
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run st).run := by
  apply TreeSimCheckTimed.state_bind
  · intro s
    simpa only [List.length_range] using
      TreeSimCheckTimed.foldlM mode.rounds (layerBody K (realRunGadgets K ctx mode) jobs)
        (fun p l s => treeSimCheckTimed_layer K ctx mode jobs p l s)
        (List.range (depth jobs)) (inputs, []) s
  · intro p s
    simp only [StateT.run_bind, StateT.run_pure]
    exact Nat.add_zero 1 ▸ (treeSimCheckTimed_rerand K ctx mode _ _ s).bind (fun _ => .done _)

def treeSimCheckRunJobs {ι : Type} {G : OracleSpec ι} (gadgets : RunGadgets C E G)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunM C E G (List (List Bit) × List (Tuple C) × RunState C) := do
  let p ← (List.range (depth jobs)).foldlM (layerBody K gadgets jobs) (inputs, [])
  let v' ← gadgets.rerand (outputShares K jobs p.1) (outputsOf jobs).length
  let tuples := p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩]
  let checkpoint ← get
  gadgets.verify tuples
  let opened ← gadgets.output v' (outputsOf jobs).length
  pure (assemble jobs opened, tuples, checkpoint)

theorem treeSimCheckRunJobs_erase {ι : Type} {G : OracleSpec ι} (gadgets : RunGadgets C E G)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    Prod.fst <$> treeSimCheckRunJobs K gadgets jobs inputs = runJobs K gadgets jobs inputs := by
  rw [treeSimCheckRunJobs, runJobs_eq, map_bind]
  apply bind_congr
  intro p
  simp only [tailBody, map_bind]
  apply bind_congr
  intro v
  funext s
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_map,
    pure_bind, map_bind, map_pure]
  rfl

theorem treeSimCheck_some_bind {ι α β : Type} {spec : OracleSpec ι}
    (p : OptionT (OracleComp spec) α) (k : α → OptionT (OracleComp spec) β) (b : β)
    (h : some b ∈ support (p >>= k).run) :
    ∃ a, some a ∈ support p.run ∧ some b ∈ support (k a).run := by
  rcases OptionT.mem_support_run_bind p k h with h | h
  · cases h.2
  · exact h

theorem treeSimCheck_record_history (mode : ReshareMode) (i : C.Party)
    (tuples : List (Tuple C)) (x y z : Shares C Bit) (count : ℕ) :
    recordMode (E := E) K mode i (filledHistory K i tuples) z count =
      filledHistory K i (tuples ++ [⟨x, y, z, count, mode⟩]) := by
  funext T
  simp only [recordMode, filledHistory, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, bitCodec, Function.comp_def]
  have hs (xs : List ℕ) : xs.flatMap (fun g => [z T g]) = xs.map (z T) := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]
  split_ifs <;> simp [hs]

theorem treeSimCheck_reshare_state (ctx : Context C) (mode : ReshareMode)
    (rnd : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) (st : RunState C)
    (z : Shares C Bit) (final : RunState C)
    (h : some (z, final) ∈ support ((reshareWith (G := RealSpec) K ctx mode rnd v count).run st).run) :
    final = ⟨recordMode K mode ctx.self st.history z count, st.label, st.tag⟩ := by
  cases mode with
  | peer =>
    change some (z, final) ∈ support ((reshare K ctx bitCodec rnd v count).run st).run at h
    rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run] at h
    obtain ⟨inbox, _, he⟩ := treeSimCheck_some_bind _ _ _ h
    simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    rfl
  | collector =>
    change some (z, final) ∈ support ((reshareCollector K ctx rnd v count).run st).run at h
    rw [show rnd = (rnd.1, rnd.2) from rfl, reshareCollector_run] at h
    obtain ⟨inbox, _, h⟩ := treeSimCheck_some_bind _ _ _ h
    obtain ⟨forward, _, he⟩ := treeSimCheck_some_bind _ _ _ h
    simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    rfl

theorem treeSimCheck_mult_state (ctx : Context C) (mode : ReshareMode)
    (x y : Shares C Bit) (count : ℕ) (st : RunState C) (z : Shares C Bit) (final : RunState C)
    (h : some (z, final) ∈ support
      (((realRunGadgets (G := RealSpec) K ctx mode).mult x y count).run st).run) :
    final = ⟨recordMode K mode ctx.self st.history z count, st.label + 1, st.tag⟩ := by
  change some (z, final) ∈ support
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshareWith K ctx mode rnd (mulRep K ctx x y) count).run st).run) at h
  rw [prssRandomness_run] at h
  obtain ⟨rnd, _, hr⟩ := treeSimCheck_some_bind _ _ _ h
  exact treeSimCheck_reshare_state K ctx mode rnd _ count (nextLabel st) z final hr

theorem treeSimCheck_rerand_state (ctx : Context C) (mode : ReshareMode)
    (v : Shares C Bit) (count : ℕ) (st : RunState C) (z : Shares C Bit) (final : RunState C)
    (h : some (z, final) ∈ support
      (((realRunGadgets (G := RealSpec) K ctx mode).rerand v count).run st).run) :
    final = ⟨recordMode K .peer ctx.self st.history z count, st.label + 1, st.tag⟩ := by
  change some (z, final) ∈ support
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count).run st).run) at h
  rw [prssRandomness_run] at h
  obtain ⟨rnd, _, hr⟩ := treeSimCheck_some_bind _ _ _ h
  exact treeSimCheck_reshare_state K ctx .peer rnd _ count (nextLabel st) z final hr

theorem treeSimCheck_layer_state (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (p : List (C.Term → List Bit) × List (Tuple C)) (layer : ℕ) (st : RunState C)
    (out : List (C.Term → List Bit) × List (Tuple C)) (final : RunState C)
    (history : st.history = filledHistory K ctx.self p.2)
    (h : some (out, final) ∈ support
      ((layerBody K (realRunGadgets (G := RealSpec) K ctx mode) jobs p layer).run st).run) :
    final.history = filledHistory K ctx.self out.2 ∧ final.label = st.label + 1 ∧
      final.tag = st.tag ∧
      out.2.map (·.count) = p.2.map (·.count) ++ [(gatesAt jobs layer).length] ∧
      out.2.map (·.mode) = p.2.map (·.mode) ++ [mode] := by
  simp only [layerBody, StateT.run_bind, StateT.run_pure] at h
  obtain ⟨⟨z, next⟩, hz, he⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  rw [treeSimCheck_mult_state K ctx mode _ _ _ st z final hz]
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · rw [history, treeSimCheck_record_history K mode ctx.self p.2
      (layerX K jobs layer p.1) (layerY K jobs layer p.1)]
    rfl
  · simp [realRunGadgets]
  · simp [realRunGadgets]

theorem treeSimCheck_layers_state (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (layers : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C)
    (out : List (C.Term → List Bit) × List (Tuple C)) (final : RunState C)
    (history : st.history = filledHistory K ctx.self p.2)
    (h : some (out, final) ∈ support
      ((layers.foldlM (layerBody K (realRunGadgets (G := RealSpec) K ctx mode) jobs) p).run st).run) :
    final.history = filledHistory K ctx.self out.2 ∧ final.label = st.label + layers.length ∧
      final.tag = st.tag ∧
      out.2.map (·.count) = p.2.map (·.count) ++ layers.map (fun l => (gatesAt jobs l).length) ∧
      out.2.map (·.mode) = p.2.map (·.mode) ++ layers.map (fun _ => mode) := by
  induction layers generalizing p st with
  | nil =>
    simp only [List.foldlM_nil, StateT.run_pure, OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨history, by simp, rfl, by simp, by simp⟩
  | cons l ls ih =>
    simp only [List.foldlM_cons, StateT.run_bind] at h
    obtain ⟨⟨p', st'⟩, hfirst, hrest⟩ := treeSimCheck_some_bind _ _ _ h
    obtain ⟨hh, hl, ht, hc, hm⟩ := treeSimCheck_layer_state K ctx mode jobs p l st p' st' history hfirst
    obtain ⟨hh', hl', ht', hc', hm'⟩ := ih p' st' hh hrest
    refine ⟨hh', ?_, ht'.trans ht, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · simp only [hc', hc, List.map_cons, List.append_assoc, List.singleton_append]
    · simp only [hm', hm, List.map_cons, List.append_assoc, List.singleton_append]

/-- Histories and labels at the reached check are derived from the actual
prefix, with no tuple or history certificate supplied as a premise. -/
theorem treeSimCheckBeforeVerify_state (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (label tag : ℕ)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (h : some (out, final) ∈ support
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run ⟨fun _ => [], label, tag⟩).run) :
    final.history = filledHistory K ctx.self out.2 ∧ final.label = label + depth jobs + 1 ∧
      final.tag = tag ∧
      out.2.map (·.count) =
        (List.range (depth jobs)).map (fun l => (gatesAt jobs l).length) ++ [(outputsOf jobs).length] ∧
      out.2.map (·.mode) = (List.range (depth jobs)).map (fun _ => mode) ++ [.peer] := by
  simp only [treeSimCheckBeforeVerify, StateT.run_bind, StateT.run_pure] at h
  obtain ⟨⟨p, st⟩, hp, h⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨⟨z, next⟩, hz, he⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
    Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  obtain ⟨hh, hl, ht, hc, hm⟩ := treeSimCheck_layers_state K ctx mode jobs
    (List.range (depth jobs)) (inputs, []) ⟨fun _ => [], label, tag⟩ p st
      (by funext T; simp [filledHistory]) hp
  rw [treeSimCheck_rerand_state K ctx mode _ _ st z final hz]
  refine ⟨?_, ?_, ht, ?_, ?_⟩
  · rw [hh, treeSimCheck_record_history K .peer ctx.self p.2 (outputShares K jobs p.1) (one K)]
  · simpa only [List.length_range] using congrArg (· + 1) hl
  · simp only [List.map_append, List.map_cons, List.map_nil, hc, List.nil_append]
  · simp only [List.map_append, List.map_cons, List.map_nil, hm, List.nil_append]

theorem treeSimCheckBeforeVerify_count (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (label tag : ℕ)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (h : some (out, final) ∈ support
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run ⟨fun _ => [], label, tag⟩).run) :
    (out.2.map (·.count)).sum = tupleCount jobs := by
  rw [(treeSimCheckBeforeVerify_state K ctx mode jobs inputs label tag out final h).2.2.2.1]
  simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact (tupleCount_eq jobs).symm

/-- These are joint reached states, obtained by the real scheduler rather
than by choosing independent local executions for the honest parties. -/
theorem treeSimCheckBeforeVerify_joint (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (mode : ReshareMode) (jobs : List Circuit) (inputs : C.Party → List (C.Term → List Bit))
    (label tag : ℕ)
    (r : A.State × (C.Party → Option ((Shares C Bit × List (Tuple C)) × RunState C)))
    (hr : r ∈ support (executePhase worldRoles D A noFunctionality fuel state
      (fun i => (treeSimCheckBeforeVerify K (ctx i) mode jobs (inputs i)).run ⟨fun _ => [], label, tag⟩))) :
    ∀ i, i ∉ D.1 → ∀ data, r.2 i = some data →
      data.2.history = filledHistory K i data.1.2 ∧ data.2.label = label + depth jobs + 1 ∧
        data.2.tag = tag ∧
        data.1.2.map (·.count) =
          (List.range (depth jobs)).map (fun l => (gatesAt jobs l).length) ++ [(outputsOf jobs).length] ∧
        data.1.2.map (·.mode) = (List.range (depth jobs)).map (fun _ => mode) ++ [.peer] := by
  obtain ⟨log, replay⟩ := treeSimCheckReplay_of_support _ r hr
  intro i hi data hd
  have hp := treeSimCheck_phase_replay D A noFunctionality (fun _ _ => True) fuel state _ r
    ⟨log, replay, fun _ _ _ => trivial⟩ i hi data hd
  obtain ⟨_, hp, _⟩ := hp
  simpa only [self i] using treeSimCheckBeforeVerify_state K (ctx i) mode jobs (inputs i)
    label tag data.1 data.2 hp.mem_support

/-- The actual check and output after the recorded prefix. -/
def treeSimCheckAfterVerify (ctx : Context C) (jobs : List Circuit)
    (p : (Shares C Bit × List (Tuple C)) × RunState C) :
    PartyM C E RealSpec ((List (List Bit) × List (Tuple C) × RunState C) × RunState C) := do
  let (_, final) ← (check K ctx (realCheckGadgets K ctx) p.1.2).run p.2
  let opened ← openRep K ctx p.1.1 (outputsOf jobs).length
  pure ((assemble jobs opened, p.1.2, p.2), final)

theorem treeSimCheckRunJobs_run_prefix (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (st : RunState C) :
    (treeSimCheckRunJobs K (realRunGadgets K ctx mode) jobs inputs).run st =
      (treeSimCheckBeforeVerify K ctx mode jobs inputs).run st >>= treeSimCheckAfterVerify K ctx jobs := by
  simp only [treeSimCheckRunJobs, treeSimCheckBeforeVerify, treeSimCheckAfterVerify,
    StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_lift, bind_assoc, pure_bind,
    realRunGadgets]

/-- An exact joint boundary for the real batch, with the original inputs,
tuples, histories, labels, adversarial state and ordered continuations. -/
theorem treeSimCheckRunJobs_phase_split {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : C.Party → List (C.Term → List Bit)) (st : C.Party → RunState C)
    (k : C.Party → ((List (List Bit) × List (Tuple C) × RunState C) × RunState C) →
      PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality (depth jobs * mode.rounds + 1 + fuel) state
      (fun i => (treeSimCheckRunJobs K (realRunGadgets K (ctx i) mode) jobs (inputs i)).run (st i) >>= k i) = (do
      let out ← executePhase worldRoles D A noFunctionality (depth jobs * mode.rounds + 1) state
        (fun i => (treeSimCheckBeforeVerify K (ctx i) mode jobs (inputs i)).run (st i))
      let next ← free (Concrete.sequenceFin fun i =>
        continueStep (fun p => treeSimCheckAfterVerify K (ctx i) jobs p >>= k i) (.done (out.2 i)))
      executeRounds worldRoles D A noFunctionality fuel out.1 next) := by
  simp only [treeSimCheckRunJobs_run_prefix, bind_assoc]
  exact treeSimCheckTimed_phase_split D A (depth jobs * mode.rounds) fuel state _ _
    (fun i => treeSimCheckBeforeVerify_timed K (ctx i) mode jobs (inputs i) (st i))

structure TreeSimCheckBatchRecord (C : Committee) where
  ctx : Context C
  jobs : List Job
  start : ℕ × ℕ
  inputs : List (C.Term → List Bit)
  tuples : List (Tuple C)
  checkpoint : RunState C
  outputs : List (List Bit)
  finish : RunState C

def treeSimCheckWriterErase {m : Type → Type} [Monad m] [LawfulMonad m] {W : Type} :
    WriterT (List W) m →ᵐ m where
  toFun _ p := Prod.fst <$> p.run
  toFun_pure' _ := by simp only [WriterT.run_pure, map_pure]
  toFun_bind' p k := by
    simp only [WriterT.run_bind, map_bind, map_pure, bind_map_left, Functor.map_map,
      Function.comp_def]

def treeSimCheckBatchAudit {ι : Type} {G : OracleSpec ι} (ctx : Context C) (jobs : List Job) :
    WriterT (List (TreeSimCheckBatchRecord C))
      (StateT (ℕ × ℕ) (PartyM C E G)) (Option (List (List Bit))) := WriterT.mk do
  let initial ← get
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let (result, final) ← StateT.lift ((treeSimCheckRunJobs K (realRunGadgets K ctx settings.mode)
    (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run ⟨fun _ => [], initial.1, initial.2⟩)
  set (final.label, initial.2 + 1)
  pure (some result.1, [⟨ctx, jobs, initial, inputs, result.2.1, result.2.2, result.1, final⟩])

theorem treeSimCheckTimed_inputs {α : Type} (ctx : Context C) (n : ℕ) (jobs : List Job)
    (k : List (C.Term → List Bit) → PartyM C E RealSpec α)
    (hk : ∀ inputs, TreeSimCheckTimed (n + 1) (k inputs).run) :
    TreeSimCheckTimed (n + 1) (jobs.mapM (inputShares ctx) >>= k).run := by
  induction jobs generalizing k with
  | nil => simpa only [List.mapM_nil, pure_bind] using hk []
  | cons job jobs ih =>
    simp only [List.mapM_cons, bind_assoc, inputShares, pure_bind]
    apply TreeSimCheckTimed.oracle_bind
    intro terms
    exact ih (fun inputs => k ((fun T => terms.getD (C.terms.idxOf T) []) :: inputs))
      (fun inputs => hk _)

/-- The ceremony's own PRF input queries and real circuit prefix, ending
before any check draw. This computation retains the inputs and checkpoint. -/
def treeSimCheckBatchPrefix (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyM C E RealSpec (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C) := do
  let inputs ← jobs.mapM (inputShares ctx)
  let p ← (treeSimCheckBeforeVerify K ctx settings.mode
    (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run ⟨fun _ => [], initial.1, initial.2⟩
  pure (inputs, p)

theorem treeSimCheckBatchPrefix_timed (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    TreeSimCheckTimed (depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1)
      (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run := by
  apply treeSimCheckTimed_inputs
  intro inputs
  exact Nat.add_zero _ ▸
    (treeSimCheckBeforeVerify_timed K ctx settings.mode _ inputs _).bind (fun _ => .done _)

def treeSimCheckBatchFinish (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (p : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C) :
    PartyM C E RealSpec ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) := do
  let r ← treeSimCheckAfterVerify K ctx (jobs.map (circuits ctx.keys.parameter ·.kind)) p.2
  pure ((some r.1.1, [⟨ctx, jobs, initial, p.1, r.1.2.1, r.1.2.2, r.1.1, r.2⟩]),
    (r.2.label, initial.2 + 1))

theorem treeSimCheckBatchAudit_run_prefix (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial =
      treeSimCheckBatchPrefix K circuits settings ctx jobs initial >>=
        treeSimCheckBatchFinish K circuits ctx jobs initial := by
  simp only [treeSimCheckBatchAudit, WriterT.run_mk, StateT.run_bind, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
    treeSimCheckRunJobs_run_prefix, treeSimCheckBatchPrefix, treeSimCheckBatchFinish]

theorem treeSimCheckBatchAudit_phase_split {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (parameter : PublicParameter)
    (hparameter : ∀ i, (ctx i).keys.parameter = parameter) (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality
      (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 + fuel) state
      (fun i => (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i) = (do
      let out ← executePhase worldRoles D A noFunctionality
        (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) state
        (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial)
      let next ← free (Concrete.sequenceFin fun i =>
        continueStep (fun p => treeSimCheckBatchFinish K circuits (ctx i) jobs initial p >>= k i)
          (.done (out.2 i)))
      executeRounds worldRoles D A noFunctionality fuel out.1 next) := by
  simp only [treeSimCheckBatchAudit_run_prefix, bind_assoc]
  apply treeSimCheckTimed_phase_split
  intro i
  simpa only [hparameter i] using treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial

theorem treeSimCheckBatchAudit_erase {ι : Type} {G : OracleSpec ι}
    (ctx : Context C) (jobs : List Job) :
    treeSimCheckWriterErase (treeSimCheckBatchAudit (G := G) K circuits settings ctx jobs) =
      ceremonyBatch K circuits settings ctx jobs := by
  change Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run = _
  simp only [treeSimCheckBatchAudit, WriterT.run_mk, map_bind, map_pure]
  unfold ceremonyBatch
  apply bind_congr
  rintro ⟨label, tag⟩
  apply bind_congr
  intro inputs
  have hrun := congrArg (fun p => p.run ⟨fun _ => [], label, tag⟩)
    (treeSimCheckRunJobs_erase K (realRunGadgets (G := G) K ctx settings.mode)
      (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs)
  simp only [StateT.run_map] at hrun
  conv_rhs => rw [← hrun]
  let action := (treeSimCheckRunJobs K (realRunGadgets (G := G) K ctx settings.mode)
    (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, tag⟩
  funext s
  change (do
    let a ← StateT.lift action
    set (a.2.label, tag + 1)
    pure (some a.1.1)).run s = (do
    let a ← StateT.lift ((fun p : (List (List Bit) × List (Tuple C) × RunState C) × RunState C =>
      (p.1.1, p.2)) <$> action)
    set (a.2.label, tag + 1)
    pure (some a.1)).run s
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
    bind_map_left, bind_assoc, pure_bind]

theorem treeSimCheckWriterErase_lift {m : Type → Type} [Monad m] [LawfulMonad m]
    {W α : Type} (p : m α) :
    treeSimCheckWriterErase (liftM p : WriterT (List W) m α) = p := by
  change Prod.fst <$> (liftM p : WriterT (List W) m α).run = p
  simp only [WriterT.run_liftM, Functor.map_map, Function.comp_def, id_map']

def treeSimCheckCeremonyAuditBody (ctx : Context C) (top : TopTree) (tree : Tree) :
    WriterT (List (TreeSimCheckBatchRecord C))
      (StateT (ℕ × ℕ) (PartyM C E RealSpec)) (Option TreeOutput) :=
  ceremonyOutput (fun {α} (oa : OracleComp HashSpec α) =>
    liftM (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) α)) ctx.keys.parameter
    (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx)) top tree

theorem treeSimCheckCeremonyAuditBody_erase (ctx : Context C) (top : TopTree) (tree : Tree) :
    treeSimCheckWriterErase (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree) =
      ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree := by
  unfold treeSimCheckCeremonyAuditBody
  rw [monadHom_ceremonyOutput]
  simp only [treeSimCheckWriterErase_lift, monadHom_batched, treeSimCheckBatchAudit_erase]

def treeSimCheckAfterSetupAudit (ctx : Context C) (top : TopTree) (tree : Tree) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) := do
  let (out, records) ← (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree).run.run' (0, 0)
  let some value := out | failure
  pure (value, records)

theorem treeSimCheckAfterSetupAudit_erase (ctx : Context C) (top : TopTree) (tree : Tree) :
    Prod.fst <$> treeSimCheckAfterSetupAudit K circuits settings ctx top tree =
      (ceremonyAfterSetup K circuits settings ctx top tree : PartyM C E RealSpec TreeOutput) := by
  have hb := congrArg (fun p => p.run' (0, 0))
    (treeSimCheckCeremonyAuditBody_erase K circuits settings ctx top tree)
  change ((Prod.fst <$> (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree).run).run'
    (0, 0)) = _ at hb
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map, Function.comp_def] at hb
  unfold treeSimCheckAfterSetupAudit ceremonyAfterSetup
  simp only [StateT.run'_eq]
  conv_rhs => rw [← hb]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨⟨out, records⟩, state⟩
  cases out <;> rfl

def treeSimCheckCeremonyAudit (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) := do
  let prss ← prssSetup i
  treeSimCheckAfterSetupAudit K circuits settings ⟨i, keys, prss⟩ top tree

theorem treeSimCheckCeremonyAudit_erase (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    Prod.fst <$> treeSimCheckCeremonyAudit K circuits settings i keys top tree =
      (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput) := by
  rw [treeSimCheckCeremonyAudit, ceremony_eq_prssSetup_bind, map_bind]
  exact bind_congr fun prss => treeSimCheckAfterSetupAudit_erase K circuits settings _ top tree

def TreeSimCheckAuditCorrect {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (good : W → Prop)
    (p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α) (expected : α) : Prop :=
  ∀ initial value records final,
    TreeSimCheckAllowed allowed ((p.run).run initial).run (some ((value, records), final)) →
    (∀ r ∈ records, good r) → value = expected

theorem TreeSimCheckAuditCorrect.pure {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (good : W → Prop) (a : α) :
    TreeSimCheckAuditCorrect (σ := σ) allowed good (pure a) a := by
  intro initial value records final h _
  simp only [WriterT.run_pure, StateT.run_pure, OptionT.run_pure] at h
  exact congrArg (fun r => r.1.1) (Option.some.inj h.pure_inv)

theorem TreeSimCheckAuditCorrect.bind {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {good : W → Prop}
    {p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α} {a : α}
    {f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β} {b : β}
    (hp : TreeSimCheckAuditCorrect allowed good p a)
    (hf : TreeSimCheckAuditCorrect allowed good (f a) b) :
    TreeSimCheckAuditCorrect allowed good (p >>= f) b := by
  intro initial value records final h hg
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
  obtain ⟨r, hr, ht⟩ := h.option_bind_inv _ _ _
  obtain ⟨s, hs, he⟩ := ht.option_map_inv _ _ _
  obtain ⟨hv, hfinal⟩ := Prod.mk.inj he
  obtain ⟨hvalue, hrecords⟩ := Prod.mk.inj hv
  have ha : r.1.1 = a := hp initial r.1.1 r.1.2 r.2 hr (fun w hw =>
    hg w (hrecords ▸ List.mem_append_left _ hw))
  have hb := hf r.2 s.1.1 s.1.2 s.2 (ha ▸ hs) (fun w hw =>
    hg w (hrecords ▸ List.mem_append_right _ hw))
  exact hvalue.symm.trans hb

theorem TreeSimCheckAuditCorrect.mapM {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {good : W → Prop}
    (f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β)
    (expected : α → β) (xs : List α)
    (h : ∀ x ∈ xs, TreeSimCheckAuditCorrect allowed good (f x) (expected x)) :
    TreeSimCheckAuditCorrect allowed good (xs.mapM f) (xs.map expected) := by
  induction xs with
  | nil => simpa using TreeSimCheckAuditCorrect.pure allowed good ([] : List β)
  | cons x xs ih =>
    simp only [List.mapM_cons, List.map_cons]
    apply (h x (by simp)).bind
    apply (ih (fun y hy => h y (by simp [hy]))).bind
    exact TreeSimCheckAuditCorrect.pure allowed good _

theorem TreeSimCheckAuditCorrect.batched {ι σ W : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {good : W → Prop}
    (size : ℕ) (run : List Job → WriterT (List W) (StateT σ (OptionT (OracleComp spec)))
      (Option (List (List Bit)))) (expected : List Job → List (List Bit)) (jobs : List Job)
    (h : ∀ batch ∈ chunks size jobs,
      TreeSimCheckAuditCorrect allowed good (run batch) (some (expected batch))) :
    TreeSimCheckAuditCorrect allowed good (batched size run jobs)
      (some (((chunks size jobs).map expected).flatten)) := by
  unfold ThresholdLeanXmss.batched
  apply (TreeSimCheckAuditCorrect.mapM run (some ∘ expected) _ h).bind
  have he := foldlM_some_append ((chunks size jobs).map expected) []
  simp only [List.map_map, List.nil_append] at he
  rw [he]
  exact .pure allowed good _

theorem treeSimCheckBatchAudit_correct
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (expected : List Job → List (List Bit)) (jobs : List Job) :
    TreeSimCheckAuditCorrect allowed (fun r : TreeSimCheckBatchRecord C => r.outputs = expected r.jobs)
      (treeSimCheckBatchAudit K circuits settings ctx jobs) (some (expected jobs)) := by
  intro initial value records final h hg
  simp only [treeSimCheckBatchAudit, WriterT.run_mk, StateT.run_bind, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at h
  obtain ⟨inputs, _, ht⟩ := h.option_bind_inv _ _ _
  obtain ⟨r, _, he⟩ := ht.option_bind_inv _ _ _
  have he := Option.some.inj he.pure_inv
  obtain ⟨hv, hfinal⟩ := Prod.mk.inj he
  obtain ⟨hvalue, hrecords⟩ := Prod.mk.inj hv
  have hr := hg _ (hrecords ▸ List.mem_cons_self)
  exact hvalue.trans (congrArg some hr)

theorem TreeSimCheckAuditCorrect.lift {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (good : W → Prop)
    (p : StateT σ (OptionT (OracleComp spec)) α) (expected : α)
    (hp : ∀ initial value final,
      TreeSimCheckAllowed allowed (p.run initial).run (some (value, final)) → value = expected) :
    TreeSimCheckAuditCorrect (σ := σ) allowed good (liftM p) expected := by
  intro initial value records final h _
  simp only [WriterT.run_liftM, StateT.run_map] at h
  obtain ⟨r, hr, he⟩ := h.option_map_inv _ _ _
  have hv : r.1 = value := congrArg (fun p => p.1.1) he
  exact hv.symm.trans (hp initial r.1 r.2 hr)

theorem treeSimCheckCeremonyAuditBody_correct (hsize : 0 < settings.batchSize)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (ctx : Context C) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    TreeSimCheckAuditCorrect allowed
      (fun r : TreeSimCheckBatchRecord C => r.outputs =
        r.jobs.map (fun job => D prims hash (evalJob circuits ctx.keys.parameter seeds job)))
      (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree)
      (ceremonyAt prims circuits ctx.keys.parameter seeds hash top tree) := by
  let expected := fun jobs : List Job =>
    jobs.map (fun job => D prims hash (evalJob circuits ctx.keys.parameter seeds job))
  let good := fun r : TreeSimCheckBatchRecord C => r.outputs = expected r.jobs
  apply treeSimCheck_ceremony_rel (fun {α} => TreeSimCheckAuditCorrect allowed good)
    (fun a => TreeSimCheckAuditCorrect.pure allowed good a)
    (fun p a f b hp hf => hp.bind hf)
    (fun {α} (oa : OracleComp HashSpec α) =>
      liftM (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) α))
    (fun oa => D prims hash (tweakable oa))
  · intro α p
    apply TreeSimCheckAuditCorrect.lift
    intro initial output final hr
    simp only [StateT.run_lift] at hr
    obtain ⟨a, ha, he⟩ := hr.option_map_inv _ _ _
    have hev : a = output := congrArg Prod.fst he
    exact hev.symm.trans (treeSimCheck_public_replay prims allowed hash hhash p a ha)
  · intro jobs _
    have h := TreeSimCheckAuditCorrect.batched settings.batchSize
      (treeSimCheckBatchAudit K circuits settings ctx) expected jobs
      (fun batch _ => treeSimCheckBatchAudit_correct K circuits settings allowed ctx expected batch)
    simpa only [expected, flatten_chunks_map settings.batchSize hsize, evalRun_eq] using h

/-- An incorrect successful audited ceremony contains an incorrect batch
record emitted by that same execution. This does not choose a replay of a
batch from a set of permitted network answers. -/
theorem treeSimCheckAfterSetupAudit_wrong_record (hsize : 0 < settings.batchSize)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (ctx : Context C) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (h : TreeSimCheckAllowed allowed
      (treeSimCheckAfterSetupAudit K circuits settings ctx top tree).run (some (value, records)))
    (wrong : some value ≠ ceremonyAt prims circuits ctx.keys.parameter seeds hash top tree) :
    ∃ r ∈ records, r.outputs ≠
      r.jobs.map (fun job => D prims hash (evalJob circuits ctx.keys.parameter seeds job)) := by
  by_contra! hall
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
    have hcorrect := treeSimCheckCeremonyAuditBody_correct prims K circuits settings hsize
      allowed hash hhash ctx seeds top tree (0, 0) (some value) records last hp hall
    exact wrong hcorrect

theorem treeSimCheck_audited_execution_erase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (x : C.Party → Keys C) (z : Aux) :
    (fun r => (r.1, fun i => (r.2 i).map Prod.fst)) <$>
      realExecution D A noFunctionality fuel
        (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree) x z =
      realExecution D A noFunctionality fuel
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z := by
  simp only [realExecution, map_bind]
  apply bind_congr
  intro state
  rw [← treeSimCheck_executePhase_map]
  simp only [treeSimCheckCeremonyAudit_erase]

def treeSimCheckAuditedGame (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) := do
  let r ← realExecution D A noFunctionality (ceremonyFuel circuits settings)
    (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree) x z
  let b ← worldRoles.adversary (Z (r.1, fun i => (r.2 i).map Prod.fst))
  pure (b, r)

theorem treeSimCheck_audited_game_erase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Prod.fst <$> treeSimCheckAuditedGame K circuits settings top tree D A x z Z =
      treeRealGame K circuits settings top tree D A x z Z := by
  unfold treeSimCheckAuditedGame treeRealGame distinguish
  conv_rhs => rw [← treeSimCheck_audited_execution_erase]
  simp only [map_bind, map_pure, bind_map_left, bind_pure_comp, Functor.map_map,
    Function.comp_def, id_map']

theorem treeSimCheck_audited_logged_erase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    (fun r => (r.1.1, r.2)) <$>
      treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z) =
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z) := by
  rw [← treeSimCheck_audited_game_erase]
  simp only [treeSimLoggedRun, simulateQ_map, WriterT.run_map, StateT.run'_eq,
    StateT.run_map, Functor.map_map]

private theorem treeSimCheck_list_first_bad {α : Type} (good : α → Prop)
    (xs : List α) (bad : ∃ x ∈ xs, ¬ good x) :
    ∃ before x after, xs = before ++ x :: after ∧ (∀ y ∈ before, good y) ∧ ¬ good x := by
  induction xs with
  | nil => simp at bad
  | cons x xs ih =>
    by_cases hx : good x
    · have htail : ∃ y ∈ xs, ¬ good y := by
        obtain ⟨y, hy, hb⟩ := bad
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hb hx).elim
        · exact ⟨y, hy, hb⟩
      obtain ⟨before, y, after, he, hg, hb⟩ := ih htail
      exact ⟨x :: before, y, after, by simp only [List.cons_append, he],
        by simpa only [List.forall_mem_cons] using And.intro hx hg, hb⟩
    · exact ⟨[], x, xs, rfl, by simp, hx⟩

/-- The reference hash is tied to the shared-cache ghost dealer and the
same successful audited prefix, including the party's actual batch records. -/
def TreeSimCheckAuditedReference (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (log : TreeSimLog C) (hash : Query C → HashOutput) (i : C.Party) (value : TreeOutput)
    (records : List (TreeSimCheckBatchRecord C)) : Prop :=
  ∃ fuel pref audited dealt out,
    fuel ≤ ceremonyFuel circuits settings ∧ pref <+: log ∧
    (dealt, (out, pref)) ∈ support (treeSimGhostRun prims D
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
      (realExecution D A noFunctionality fuel
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
        (dealtKeys parameter seeds pairs) z)) ∧
    TreeSimCheckReplay (realExecution D A noFunctionality fuel
      (fun i keys => treeSimCheckCeremonyAudit K circuits settings i keys top tree)
      (dealtKeys parameter seeds pairs) z) pref audited ∧
    audited.2 i = some (value, records) ∧ out.2 i = some value ∧
    dealt.1 = ceremonyAt prims circuits parameter seeds hash top tree ∧
    ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ pref →
      TreeSimCheckWorldHashes hash t u

/-- The first incorrect batch is selected from the records actually emitted
by the scheduled ceremony. The earlier ghost witness and the full execution
have the same successful audited output, including its complete batch list. -/
theorem treeSimWrongOutput_audited_first_batch (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool)
    (actual : A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))
    (log : TreeSimLog C)
    (run : ((result, actual), log) ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs i value records hash before batch after,
      x = dealtKeys parameter seeds pairs ∧ i ∉ D.1 ∧
      actual.2 i = some (value, records) ∧
      some value ≠ ceremonyAt prims circuits parameter seeds hash top tree ∧ Good prims hash ∧
      records = before ++ batch :: after ∧
      (∀ r ∈ before, r.outputs =
        r.jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job))) ∧
      batch.outputs ≠ batch.jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job)) ∧
      TreeSimCheckAuditedReference prims K circuits settings top tree D A parameter seeds pairs z
        log hash i value records := by
  have replay := treeSimCheckReplay_logged prims D _ (result, actual) log run
  unfold treeSimCheckAuditedGame at replay
  obtain ⟨r, pre, tail, hr, ht, hlog⟩ := replay.bind_inv
  obtain ⟨b, mid, post, _, hp, _⟩ := ht.bind_inv
  cases hp
  obtain ⟨parameter, seeds, pairs, dealt, out, hx, witness, i, hi, hs, hw⟩ := wrong
  obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨fuel, pref, hf, hprefix, hghost⟩ := witness
  have early := treeSimCheckReplay_ghost prims D _ _ dealt out pref hghost
  rw [← treeSimCheck_audited_execution_erase] at early
  obtain ⟨audited, hearly, herase⟩ := early.map_inv _
  have hvalue : (audited.2 i).map Prod.fst = some value := by
    have he := congrArg (fun r => r.2 i) herase
    exact he.trans hv
  obtain ⟨pair, hpair, hfst⟩ := Option.map_eq_some_iff.mp hvalue
  rcases pair with ⟨v, records⟩
  change v = value at hfst
  subst v
  have same := treeSimCheckReplay_execution_mono D A noFunctionality fuel
    (ceremonyFuel circuits settings) hf
    (fun j keys => treeSimCheckCeremonyAudit K circuits settings j keys top tree)
    (dealtKeys parameter seeds pairs) z audited actual pref pre log hearly (hx ▸ hr)
    hprefix (hlog ▸ List.prefix_append pre tail) i (value, records) hpair
  obtain ⟨hash, hg, hd, hall⟩ := treeSimCheck_ghost_hashes prims D
    (dealerCeremony circuits settings parameter seeds top tree) _ dealt out pref hghost
  have href : dealt.1 = ceremonyAt prims circuits parameter seeds hash top tree := by
    rw [hd, D_dealerCeremony prims circuits settings parameter seeds hash top tree hbatch]
  have hwrong : some value ≠ ceremonyAt prims circuits parameter seeds hash top tree := by
    simpa only [hv, href] using hw
  have hallowed : TreeSimCheckAllowed
      (fun t u => TreeSimCheckWorldHashes hash t u)
      (realExecution D A noFunctionality fuel
        (fun j keys => treeSimCheckCeremonyAudit K circuits settings j keys top tree)
        (dealtKeys parameter seeds pairs) z) audited := ⟨pref, hearly, hall⟩
  obtain ⟨state, _, hphase⟩ := hallowed.bind_inv
  have hparty := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ audited
    hphase i hi (value, records) hpair
  unfold treeSimCheckCeremonyAudit at hparty
  obtain ⟨prss, _, hbody⟩ := hparty.option_bind_inv _ _ _
  have bad := treeSimCheckAfterSetupAudit_wrong_record prims K circuits settings hbatch
    _ hash (fun q u h => h) ⟨i, dealtKeys parameter seeds pairs i, prss⟩ seeds top tree
    value records hbody hwrong
  obtain ⟨before, batch, after, he, hgprev, hb⟩ := treeSimCheck_list_first_bad
    (fun r : TreeSimCheckBatchRecord C => r.outputs =
      r.jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job))) records bad
  exact ⟨parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    hx, hi, same, hwrong, hg, he, hgprev, hb,
    fuel, pref, audited, dealt, out, hf, hprefix, hghost, hearly, hpair, hv, href, hall⟩

def TreeSimCheckAuditBound {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop)
    (p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α) (bound : ℕ) : Prop :=
  ∀ initial value records final,
    TreeSimCheckAllowed allowed (p.run.run initial).run (some ((value, records), final)) →
    records.length ≤ bound

theorem TreeSimCheckAuditBound.pure {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (a : α) (bound : ℕ) :
    TreeSimCheckAuditBound (σ := σ) (W := W) allowed (pure a) bound := by
  intro initial value records final h
  simp only [WriterT.run_pure, StateT.run_pure, OptionT.run_pure] at h
  have he := congrArg (fun r => r.1.2) (Option.some.inj h.pure_inv)
  change records = [] at he
  simp only [he, List.length_nil, Nat.zero_le]

theorem TreeSimCheckAuditBound.mono {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    {p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α} {a b : ℕ}
    (h : TreeSimCheckAuditBound allowed p a) (hle : a ≤ b) :
    TreeSimCheckAuditBound allowed p b := fun s v rs t hp => (h s v rs t hp).trans hle

theorem TreeSimCheckAuditBound.bind {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    {p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α}
    {f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β} {a b : ℕ}
    (hp : TreeSimCheckAuditBound allowed p a) (hf : ∀ x, TreeSimCheckAuditBound allowed (f x) b) :
    TreeSimCheckAuditBound allowed (p >>= f) (a + b) := by
  intro initial value records final h
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
  obtain ⟨r, hr, ht⟩ := h.option_bind_inv _ _ _
  obtain ⟨s, hs, he⟩ := ht.option_map_inv _ _ _
  have hrecords := congrArg (fun r => r.1.2) he
  change r.1.2 ++ s.1.2 = records at hrecords
  rw [← hrecords, List.length_append]
  exact Nat.add_le_add (hp initial r.1.1 r.1.2 r.2 hr) (hf r.1.1 r.2 s.1.1 s.1.2 s.2 hs)

theorem TreeSimCheckAuditBound.lift {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop)
    (p : StateT σ (OptionT (OracleComp spec)) α) :
    TreeSimCheckAuditBound (σ := σ) (W := W) allowed (liftM p) 0 := by
  intro initial value records final h
  simp only [WriterT.run_liftM, StateT.run_map] at h
  obtain ⟨r, hr, he⟩ := h.option_map_inv _ _ _
  have hv : ([] : List W) = records := congrArg (fun p => p.1.2) he
  simp only [← hv, List.length_nil, le_refl]

theorem TreeSimCheckAuditBound.mapM {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    (f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β) (xs : List α)
    (h : ∀ x ∈ xs, TreeSimCheckAuditBound allowed (f x) 1) :
    TreeSimCheckAuditBound allowed (xs.mapM f) xs.length := by
  induction xs with
  | nil => simpa using TreeSimCheckAuditBound.pure allowed ([] : List β) 0
  | cons x xs ih =>
    simp only [List.mapM_cons, List.length_cons]
    have htail : ∀ a, TreeSimCheckAuditBound allowed
        (do let as ← xs.mapM f; Pure.pure (a :: as)) xs.length := by
      intro a
      simpa only [Nat.add_zero] using
        (ih (fun y hy => h y (by simp [hy]))).bind
          (fun as => TreeSimCheckAuditBound.pure allowed (a :: as) 0)
    simpa only [Nat.add_comm] using (h x (by simp)).bind htail

theorem treeSimCheckBatchAudit_bound
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) :
    TreeSimCheckAuditBound allowed (treeSimCheckBatchAudit K circuits settings ctx jobs) 1 := by
  intro initial value records final h
  simp only [treeSimCheckBatchAudit, WriterT.run_mk, StateT.run_bind, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at h
  obtain ⟨inputs, _, ht⟩ := h.option_bind_inv _ _ _
  obtain ⟨r, _, he⟩ := ht.option_bind_inv _ _ _
  have he := congrArg (fun p => p.1.2) (Option.some.inj he.pure_inv)
  have hlen := congrArg List.length he
  dsimp only at hlen
  simpa only [List.length_singleton] using hlen.le

theorem treeSimCheck_batchedAudit_bound
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) :
    TreeSimCheckAuditBound allowed
      (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs)
      (chunks settings.batchSize jobs).length := by
  unfold batched
  simpa only [Nat.add_zero] using
    (TreeSimCheckAuditBound.mapM _ _ (fun batch _ =>
      treeSimCheckBatchAudit_bound K circuits settings allowed ctx batch)).bind
      (fun outputs => TreeSimCheckAuditBound.pure allowed
        (outputs.foldlM (fun acc batch => batch.map (acc ++ ·)) []) 0)

theorem TreeSimCheckAuditBound.lift_bind {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    (p : StateT σ (OptionT (OracleComp spec)) α)
    (f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β) (bound : ℕ)
    (hf : ∀ a, TreeSimCheckAuditBound allowed (f a) bound) :
    TreeSimCheckAuditBound allowed (liftM p >>= f) bound := by
  simpa only [Nat.zero_add] using (TreeSimCheckAuditBound.lift allowed p).bind hf

theorem TreeSimCheckAuditBound.bind_zero {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop}
    {p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α}
    {f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β} {bound : ℕ}
    (hp : TreeSimCheckAuditBound allowed p bound)
    (hf : ∀ x, TreeSimCheckAuditBound allowed (f x) 0) :
    TreeSimCheckAuditBound allowed (p >>= f) bound := by
  simpa only [Nat.add_zero] using hp.bind hf

theorem treeSimCheckCeremonyAuditBody_bound
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree) :
    TreeSimCheckAuditBound allowed (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree)
      (treeBatches settings tree) := by
  unfold treeSimCheckCeremonyAuditBody
  cases tree with
  | top =>
    simp only [ceremonyOutput, treeBatches]
    apply (treeSimCheck_batchedAudit_bound K circuits settings allowed ctx topJobs).bind_zero
    intro out
    cases out with
    | none => exact .pure allowed _ 0
    | some outputs =>
      apply TreeSimCheckAuditBound.lift_bind
      intro root
      exact .pure allowed _ 0
  | bottom b =>
    simp only [ceremonyOutput, treeBatches]
    apply (treeSimCheck_batchedAudit_bound K circuits settings allowed ctx (bottomJobs b)).bind
    intro out
    cases out with
    | none => exact .pure allowed _ _
    | some outputs =>
      apply TreeSimCheckAuditBound.lift_bind
      intro root
      apply TreeSimCheckAuditBound.lift_bind
      intro base
      apply TreeSimCheckAuditBound.lift_bind
      intro gr
      rcases gr with _ | ⟨randomness, encoding⟩
      · exact .pure allowed _ _
      · dsimp only
        have hb := treeSimCheck_batchedAudit_bound K circuits settings allowed ctx (signJobs b encoding)
        have hb' := hb.mono (Nat.le_of_eq (length_chunks_signJobs settings b b encoding (fun _ => digit 0)))
        apply hb'.bind_zero
        intro values
        cases values with
        | none => exact .pure allowed _ 0
        | some values =>
          apply TreeSimCheckAuditBound.lift_bind
          intro path
          apply TreeSimCheckAuditBound.lift_bind
          intro topRoot
          split <;> exact .pure allowed _ 0

theorem treeSimCheckAfterSetupAudit_bound
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (h : TreeSimCheckAllowed allowed
      (treeSimCheckAfterSetupAudit K circuits settings ctx top tree).run (some (value, records))) :
    records.length ≤ treeBatches settings tree := by
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
    exact treeSimCheckCeremonyAuditBody_bound K circuits settings allowed ctx top tree
      (0, 0) (some value) records last hp

theorem treeSimCheck_audited_output_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool)
    (actual : A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))
    (log : TreeSimLog C)
    (run : ((result, actual), log) ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (i : C.Party) (hi : i ∉ D.1) (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (out : actual.2 i = some (value, records)) : records.length ≤ treeBatches settings tree := by
  have replay := treeSimCheckReplay_logged prims D _ (result, actual) log run
  unfold treeSimCheckAuditedGame at replay
  obtain ⟨r, pre, tail, hr, ht, hlog⟩ := replay.bind_inv
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
  exact treeSimCheckAfterSetupAudit_bound K circuits settings _ ⟨i, x i, prss⟩ top tree value records hbody

theorem treeSimWrongOutput_audited_first_index (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (result : Bool)
    (actual : A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))
    (log : TreeSimLog C)
    (run : ((result, actual), log) ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (wrong : TreeSimWrongOutput prims K circuits settings top tree D A x z log) :
    ∃ parameter seeds pairs i value records hash, ∃ j : Fin (treeBatches settings tree), ∃ before batch after,
      x = dealtKeys parameter seeds pairs ∧ i ∉ D.1 ∧
      actual.2 i = some (value, records) ∧
      some value ≠ ceremonyAt prims circuits parameter seeds hash top tree ∧ Good prims hash ∧
      records = before ++ batch :: after ∧ j.val = before.length ∧
      (∀ r ∈ before, r.outputs = r.jobs.map
        (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job))) ∧
      batch.outputs ≠ batch.jobs.map
        (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job)) ∧
      TreeSimCheckAuditedReference prims K circuits settings top tree D A parameter seeds pairs z
        log hash i value records := by
  obtain ⟨parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    hx, hi, hout, hw, hg, he, hp, hb, href⟩ := treeSimWrongOutput_audited_first_batch
      prims K circuits settings hbatch top tree D A x z Z result actual log run wrong
  have hlen := treeSimCheck_audited_output_bound prims K circuits settings top tree D A x z Z
    result actual log run i hi value records hout
  have hidx : before.length < treeBatches settings tree := by
    rw [he, List.length_append, List.length_cons] at hlen
    omega
  exact ⟨parameter, seeds, pairs, i, value, records, hash, ⟨before.length, hidx⟩, before, batch, after,
    hx, hi, hout, hw, hg, he, rfl, hp, hb, href⟩

/-- The fixed first-incorrect-batch event on an actual audited run. The
dealer reference retains its common replay, not just an arbitrary total hash. -/
def TreeSimCheckIndexedBad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree)) (log : TreeSimLog C)
    (actual : A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) : Prop :=
  ¬ TreeSimHashBad D log ∧
  ∃ parameter seeds pairs i value records hash before batch after,
    x = dealtKeys parameter seeds pairs ∧ i ∉ D.1 ∧
    actual.2 i = some (value, records) ∧
    some value ≠ ceremonyAt prims circuits parameter seeds hash top tree ∧ Good prims hash ∧
    records = before ++ batch :: after ∧ j.val = before.length ∧
    (∀ r ∈ before, r.outputs = r.jobs.map
      (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job))) ∧
    batch.outputs ≠ batch.jobs.map
      (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job)) ∧
    TreeSimCheckAuditedReference prims K circuits settings top tree D A parameter seeds pairs z
      log hash i value records

theorem treeSimCheck_indexed_cover (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (r : (Bool × (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) × TreeSimLog C)
    (hr : r ∈ support (treeSimLoggedRun prims D
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)))
    (bad : ¬ TreeSimHashBad D r.2 ∧ TreeSimWrongOutput prims K circuits settings top tree D A x z r.2) :
    ∃ j, TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 := by
  obtain ⟨parameter, seeds, pairs, i, value, records, hash, j, before, batch, after, h⟩ :=
    treeSimWrongOutput_audited_first_index prims K circuits settings hbatch top tree D A x z Z
      r.1.1 r.1.2 r.2 hr bad.2
  exact ⟨j, bad.1, parameter, seeds, pairs, i, value, records, hash, before, batch, after, h⟩

private theorem treeSimCheck_union_prob {α : Type} (n : ℕ) (p : ProbComp α)
    (bad : α → Prop) (events : Fin n → α → Prop)
    (cover : ∀ r ∈ support p, bad r → ∃ j, events j r) :
    Pr[bad | p] ≤ ∑ j : Fin n, Pr[events j | p] := by
  calc
    _ ≤ Pr[fun r => ∃ j ∈ (Finset.univ : Finset (Fin n)), events j r | p] := by
      apply probEvent_mono
      intro r hr hb
      obtain ⟨j, hj⟩ := cover r hr hb
      exact ⟨j, Finset.mem_univ j, hj⟩
    _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ p events

/-- A union over batch indices only, after an exact erasure of the audited
execution. There is no union over scheduler rounds, parties or hash failures. -/
theorem treeSimCheck_indexed_union (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun r => ¬ TreeSimHashBad D r.2 ∧
      TreeSimWrongOutput prims K circuits settings top tree D A x z r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
    ∑ j : Fin (treeBatches settings tree),
      Pr[fun r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
        treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] := by
  have hu := treeSimCheck_union_prob (treeBatches settings tree)
    (treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z))
    (fun r => ¬ TreeSimHashBad D r.2 ∧ TreeSimWrongOutput prims K circuits settings top tree D A x z r.2)
    (fun j r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2)
    (treeSimCheck_indexed_cover prims K circuits settings hbatch top tree D A x z Z)
  have he := congrArg (fun p : ProbComp (Bool × TreeSimLog C) =>
    Pr[fun r => ¬ TreeSimHashBad D r.2 ∧
      TreeSimWrongOutput prims K circuits settings top tree D A x z r.2 | p])
    (treeSimCheck_audited_logged_erase prims K circuits settings top tree D A x z Z)
  simp only [probEvent_map, Function.comp_def] at he
  exact he.symm.le.trans hu

theorem treeSimCheck_hash_injective (D : C.Coalition) (log : TreeSimLog C)
    (good : ¬ TreeSimHashBad D log) (q r : Query C) (h : HashOutput)
    (hq : TreeSimHashDomain q) (hr : TreeSimHashDomain r)
    (qa : TreeSimHashAnswer log q h) (ra : TreeSimHashAnswer log r h) : q = r := by
  by_contra hne
  exact good (Or.inl ⟨q, r, h, hq, hr, hne, qa, ra⟩)

theorem treeSimCheck_good_prefix (D : C.Coalition) {pref log : TreeSimLog C}
    (hp : pref <+: log) (good : ¬ TreeSimHashBad D log) : ¬ TreeSimHashBad D pref :=
  fun bad => good (treeSimHashBad_mono D hp bad)

/-- A later coin cannot reuse an earlier logged coin key outside the fixed
hash event. This is a pointwise implication, not another collision estimate. -/
theorem treeSimCheck_coinKey_not_mem (D : C.Coalition) (log : TreeSimLog C)
    (good : ¬ TreeSimHashBad D log) (tag label : ℕ) (bits : List Bit)
    (key : HashOutput) (keys : Finset HashOutput)
    (old : ∀ k ∈ keys, ∃ tg lab bs, lab < label ∧
      TreeSimHashAnswer log (.coinKey tg lab bs) k)
    (current : TreeSimHashAnswer log (.coinKey tag label bits) key) : key ∉ keys := by
  intro hk
  obtain ⟨tg, lab, bs, hlt, hanswer⟩ := old key hk
  have heq := treeSimCheck_hash_injective D log good
    (.coinKey tg lab bs) (.coinKey tag label bits) key trivial trivial hanswer current
  have hlabel := (Query.coinKey.inj heq).2.1
  omega

/-- Every cached history, digest, copy, and coin key is backed by the actual
log. Dealer-only queries and stream-key derivations lie outside this region. -/
def TreeSimCheckCacheCovered (cache : HashCache C) (log : TreeSimLog C) : Prop :=
  ∀ q h, TreeSimHashDomain q → cache q = some h → TreeSimHashAnswer log q h

private theorem treeSimCheck_hash_entry (asked q : Query C) (cache : HashCache C)
    (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims asked).run cache)) (h : HashOutput)
    (hq : TreeSimHashDomain q) (entry : p.2 q = some h) :
    cache q = some h ∨ asked = q ∧ p.1 = h := by
  by_cases fixed : IsFixed asked
  · obtain ⟨input, rfl, hm⟩ := fixed
    rw [hashAnswer_of_isFixed prims hm] at hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact Or.inl entry
  · rw [hashAnswer_of_not_isFixed prims fixed] at hp
    obtain ⟨_, self, other⟩ := randomOracle_support asked cache p hp
    by_cases he : asked = q
    · subst q
      exact Or.inr ⟨rfl, Option.some.inj (self.symm.trans entry)⟩
    · exact Or.inl ((other q (Ne.symm he)) ▸ entry)

private theorem treeSimCheck_local_entry (t : (LocalSpec C).Domain) (cache : HashCache C)
    (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run cache))
    (q : Query C) (h : HashOutput) (hq : TreeSimHashDomain q) (entry : p.2 q = some h) :
    cache q = some h ∨
      (⟨t, p.1⟩ : (u : (LocalSpec C).Domain) × (LocalSpec C).Range u) =
        ⟨.inr (.inl q), h⟩ := by
  rcases t with n | asked | x
  · simp [localAnswer, unifFwdImpl] at hp
    obtain ⟨u, rfl⟩ := hp
    exact Or.inl entry
  · rcases treeSimCheck_hash_entry prims asked q cache p hp h hq entry with old | ⟨rfl, hh⟩
    · exact Or.inl old
    · exact Or.inr (by cases hh; rfl)
  · simp [localAnswer, prgAnswer] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rcases treeSimCheck_hash_entry prims (.streamKey x.2.1) q cache r hr h hq entry with old | ⟨he, _⟩
    · exact Or.inl old
    · subst q
      cases hq

theorem TreeSimCheckCacheCovered.mono {cache : HashCache C} {a b : TreeSimLog C}
    (covered : TreeSimCheckCacheCovered cache a) (hp : a <+: b) : TreeSimCheckCacheCovered cache b := by
  intro q h hq he
  exact (covered q h hq he).imp (fun hh => hp.sublist.subset hh) (fun hh => hp.sublist.subset hh)

private theorem treeSimCheck_counted_covered (D : C.Coalition)
    (t : (LocalSpec C).Domain) (s : TreeSimState C)
    (r : (LocalSpec C).Range t × TreeSimState C)
    (covered : TreeSimCheckCacheCovered s.1.1 s.2)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl t))).run s)) :
    TreeSimCheckCacheCovered r.2.1.1 r.2.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, streamWorld, onHash, support_map] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  obtain ⟨u, hu, rfl⟩ := hp
  intro q h hq he
  rcases treeSimCheck_local_entry prims t s.1.1 u hu q h hq he with old | same
  · exact (covered.mono (List.prefix_append _ _)) q h hq old
  · apply Or.inr
    have eqworld := congrArg (fun a : (v : (LocalSpec C).Domain) × (LocalSpec C).Range v =>
      (⟨.inl (.inl a.1), a.2⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v)) same
    change (⟨.inl (.inl (.inr (.inl q))), h⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v) ∈ _
    rw [← eqworld]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem treeSimCheck_free_covered (D : C.Coalition)
    (t : (LocalSpec C).Domain) (s : TreeSimState C)
    (r : (LocalSpec C).Range t × TreeSimState C)
    (covered : TreeSimCheckCacheCovered s.1.1 s.2)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
    TreeSimCheckCacheCovered r.2.1.1 r.2.2 := by
  have ordinary (t : (LocalSpec C).Domain)
      (hrun : streamWorld prims D (.inr t) = onHash (localAnswer prims t))
      (r : (LocalSpec C).Range t × TreeSimState C)
      (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
      TreeSimCheckCacheCovered r.2.1.1 r.2.2 := by
    simp only [treeSimLoggedWorld, StateT.run_mk, hrun, onHash, support_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    obtain ⟨u, hu, rfl⟩ := hp
    intro q h hq he
    rcases treeSimCheck_local_entry prims t s.1.1 u hu q h hq he with old | same
    · exact (covered.mono (List.prefix_append _ _)) q h hq old
    · apply Or.inl
      have eqworld := congrArg (fun a : (v : (LocalSpec C).Domain) × (LocalSpec C).Range v =>
        (⟨.inr a.1, a.2⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v)) same
      change (⟨.inr (.inr (.inl q)), h⟩ : (v : (WorldSpec C).Domain) × (WorldSpec C).Range v) ∈ _
      rw [← eqworld]
      simp
  rcases t with n | q | x
  · exact ordinary _ rfl r hr
  · exact ordinary _ rfl r hr
  · by_cases hh : Hidden D x.1
    · simp only [treeSimLoggedWorld, StateT.run_mk, streamWorld, if_pos hh,
        support_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      obtain ⟨u, hu, rfl⟩ := hp
      exact covered.mono (List.prefix_append _ _)
    · exact ordinary _ (by simp only [streamWorld, if_neg hh]) r hr

set_option backward.isDefEq.respectTransparency false in
theorem treeSimCheck_localRun_covered {α : Type} (D : C.Coalition)
    (p : OracleComp (LocalSpec C + LocalSpec C) α) (s : TreeSimState C)
    (r : α × TreeSimState C) (covered : TreeSimCheckCacheCovered s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld p)).run s)) :
    TreeSimCheckCacheCovered r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact covered
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    apply ih mid.1 mid.2 r _ hr
    cases t with
    | inl t =>
      simp only [treeSimLocalWorld, QueryImpl.add_apply_inl, simulateQ_spec_query] at hmid
      exact treeSimCheck_counted_covered prims D t s mid covered hmid
    | inr t =>
      simp only [treeSimLocalWorld, QueryImpl.add_apply_inr, simulateQ_spec_query] at hmid
      exact treeSimCheck_free_covered prims D t s mid covered hmid

/-- The actual instrumented real game needs no assumed cache coverage. -/
theorem treeSimCheck_realRun_covered (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (r : Bool × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeRealGame K circuits settings top tree D A x z Z)).run ((∅, ∅), []))) :
    TreeSimCheckCacheCovered r.2.1.1 r.2.2 := by
  rw [← treeSim_localReal_eq K circuits settings top tree D A x z Z] at hr
  apply treeSimCheck_localRun_covered prims D _ _ r _ hr
  intro q h _ he
  change (none : Option HashOutput) = some h at he
  cases he

theorem treeSimCheck_no_domain_collision (D : C.Coalition) (log : TreeSimLog C)
    (cache : HashCache C) (covered : TreeSimCheckCacheCovered cache log)
    (good : ¬ TreeSimHashBad D log) :
    ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain cache) := by
  classical
  rintro ⟨q, r, u, v, hne, hq, hr, huv⟩
  have huv' : u = v := eq_of_heq huv
  subst v
  have sq : TreeSimHashDomain q := by
    by_contra hn
    simp [splitRegionCache, hn] at hq
  have sr : TreeSimHashDomain r := by
    by_contra hn
    simp [splitRegionCache, hn] at hr
  exact hne (treeSimCheck_hash_injective D log good q r u sq sr
    (covered q u sq (by simpa [splitRegionCache, sq] using hq))
    (covered r u sr (by simpa [splitRegionCache, sr] using hr)))

theorem treeSimCheck_domain_collision_mono {cache next : HashCache C} (hle : cache ≤ next) :
    CacheHasCollision (splitRegionCache TreeSimHashDomain cache) →
      CacheHasCollision (splitRegionCache TreeSimHashDomain next) := by
  classical
  rintro ⟨q, r, u, v, hne, hq, hr, huv⟩
  have sq : TreeSimHashDomain q := by
    by_contra hn
    simp [splitRegionCache, hn] at hq
  have sr : TreeSimHashDomain r := by
    by_contra hn
    simp [splitRegionCache, hn] at hr
  refine ⟨q, r, u, v, hne, ?_, ?_, huv⟩
  · have he : cache q = some u := by simpa [splitRegionCache, sq] using hq
    simpa [splitRegionCache, sq] using hle he
  · have he : cache r = some v := by simpa [splitRegionCache, sr] using hr
    simpa [splitRegionCache, sr] using hle he

/-- Reusing an earlier honest coin key makes every later collision-free
continuation impossible. The conclusion retains the final cache. -/
theorem treeSimCheck_coin_collision_zero {α : Type}
    (p : OracleComp (LocalSpec C) α) (cache : HashCache C)
    (tag label oldTag oldLabel : ℕ) (bits oldBits : List Bit) (key : HashOutput)
    (hlt : oldLabel < label)
    (old : cache (.coinKey oldTag oldLabel oldBits) = some key)
    (current : cache (.coinKey tag label bits) = some key)
    (accept : α × HashCache C → Prop) :
    Pr[fun r => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain r.2) ∧ accept r |
      (simulateQ (localAnswer prims) p).run cache] = 0 := by
  have bad : CacheHasCollision (splitRegionCache TreeSimHashDomain cache) := by
    refine ⟨.coinKey oldTag oldLabel oldBits, .coinKey tag label bits, key, key,
      ?_, ?_, ?_, HEq.rfl⟩
    · intro he
      have hh := (Query.coinKey.inj he).2.1
      omega
    · simpa [splitRegionCache, TreeSimHashDomain] using old
    · simpa [splitRegionCache, TreeSimHashDomain] using current
  apply probEvent_eq_zero
  intro r hr ha
  exact ha.1 (treeSimCheck_domain_collision_mono
    ((grows_localAnswer prims).simulateQ p cache r hr) bad)

theorem treeSimCheck_no_collision (D : C.Coalition) (log : TreeSimLog C)
    (cache : HashCache C) (covered : TreeSimCheckCacheCovered cache log)
    (good : ¬ TreeSimHashBad D log) :
    ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache) := by
  classical
  rintro ⟨q, r, u, v, hne, hq, hr, huv⟩
  have huv' : u = v := eq_of_heq huv
  subst v
  have sq : SplitHashDomain q := by
    by_contra hn
    simp [splitRegionCache, hn] at hq
  have sr : SplitHashDomain r := by
    by_contra hn
    simp [splitRegionCache, hn] at hr
  have toDomain : ∀ q : Query C, SplitHashDomain q → TreeSimHashDomain q := by
    intro q
    cases q <;> simp [SplitHashDomain, TreeSimHashDomain]
  exact hne (treeSimCheck_hash_injective D log good q r u (toDomain q sq) (toDomain r sr)
    (covered q u (toDomain q sq) (by simpa [splitRegionCache, sq] using hq))
    (covered r u (toDomain r sr) (by simpa [splitRegionCache, sr] using hr)))

/-- Inconsistent known-term histories abort without any additional hash
probability charge once their actual cache is covered by the good log. -/
theorem treeSimCheck_split_abort (D : C.Coalition) (log : TreeSimLog C)
    (cache : HashCache C) (covered : TreeSimCheckCacheCovered cache log)
    (good : ¬ TreeSimHashBad D log) (hist : C.Party → C.Term → List Bit)
    (split : SplitHistories D hist) (ds : C.Party → List HashOutput)
    (hds : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → ∃ salt h d,
      cache (.history (hist i T)) = some h ∧ cache (.digest salt h) = some d ∧
      (ds i)[C.terms.idxOf T]? = some d)
    (sent : C.Party → Mail C E) (i : C.Party) : ¬ digestLive D ds sent i := by
  letI : SampleableType E := SampleableType.ofFintype E
  exact splitHistories_abort_region D hist split cache
    (treeSimCheck_no_collision D log cache covered good) ds hds sent i

/-- Equality on accepted branches retains the complete final public cache. -/
def TreeSimCheckAcceptedRun {α : Type} (accept : α → Prop)
    (a b : OracleComp (LocalSpec C) α) : Prop :=
  ∀ (cache : HashCache C) (event : α × HashCache C → Prop),
    (∀ r, event r → accept r.1) →
    Pr[event | (simulateQ (localAnswer prims) a).run cache] =
      Pr[event | (simulateQ (localAnswer prims) b).run cache]

theorem TreeSimCheckAcceptedRun.of_sameRun {α : Type} (accept : α → Prop)
    {a b : OracleComp (LocalSpec C) α} (h : SameRun prims a b) :
    TreeSimCheckAcceptedRun prims accept a b := by
  intro cache event _
  rw [probEvent_def, h cache, ← probEvent_def]

theorem TreeSimCheckAcceptedRun.trans {α : Type} {accept : α → Prop}
    {a b c : OracleComp (LocalSpec C) α}
    (hab : TreeSimCheckAcceptedRun prims accept a b)
    (hbc : TreeSimCheckAcceptedRun prims accept b c) :
    TreeSimCheckAcceptedRun prims accept a c := by
  intro cache event he
  exact (hab cache event he).trans (hbc cache event he)

theorem TreeSimCheckAcceptedRun.bind_right {α β : Type} (accept : β → Prop)
    (p : OracleComp (LocalSpec C) α) {f g : α → OracleComp (LocalSpec C) β}
    (h : ∀ a, TreeSimCheckAcceptedRun prims accept (f a) (g a)) :
    TreeSimCheckAcceptedRun prims accept (p >>= f) (p >>= g) := by
  intro cache event he
  simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro r
  rw [h r.1 r.2 event he]

/-- Extra queries on a wholly rejected branch do not affect any accepted
event, even if that event inspects the final cache. -/
theorem TreeSimCheckAcceptedRun.prefetch_rejected {α β : Type} (accept : α → Prop)
    (prefetch : OracleComp (LocalSpec C) β) (abort : OracleComp (LocalSpec C) α)
    (reject : ∀ cache r, r ∈ support ((simulateQ (localAnswer prims) abort).run cache) →
      ¬ accept r.1) :
    TreeSimCheckAcceptedRun prims accept abort (prefetch >>= fun _ => abort) := by
  intro cache event he
  have hz : ∀ cache, Pr[event | (simulateQ (localAnswer prims) abort).run cache] = 0 := by
    intro cache
    apply probEvent_eq_zero
    intro r hr hr'
    exact reject cache r hr (he r hr')
  rw [hz]
  simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum, hz, mul_zero,
    tsum_zero]

/-- Challenge normalization preserves cache-dependent events on every branch
where an honest operator accepts. -/
theorem treeSimCheck_afterChallenge [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (v : List E) (p : A.State × Finset C.Party) :
    TreeSimCheckAcceptedRun prims (fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some ())
      (executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)))
      (liftComp (challengeQuery K tag L v) (LocalSpec C) >>= soundChallengeNext K D A fuel hs g p) := by
  by_cases hp : ∃ i, i ∉ D.1 ∧ i ∈ p.2
  · exact TreeSimCheckAcceptedRun.of_sameRun prims _
      (executePhase_afterChallenge_common' prims K D A fuel p.1 hs tag L htag v p.2 hp g)
  · have he : executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterChallenge K (hs i) (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)) =
        pure (p.1, fun _ : C.Party => (none : Option Unit)) := by
      rw [executePhase_congr_honest D A _ _ p.1 _ (fun _ => failure), executePhase_failure]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ p.2) := fun h => hp ⟨i, h⟩
      simp [hn, afterChallenge]
    have hg : soundChallengeNext K D A fuel hs g p =
        fun _ => pure (p.1, fun _ : C.Party => (none : Option Unit)) :=
      funext (soundChallengeNext_missing K D A fuel hs g p hp)
    rw [he, hg]
    apply TreeSimCheckAcceptedRun.prefetch_rejected
    intro cache r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_challenge_normalize [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (live : C.Party → Prop) [DecidablePred live]
    (hall : ∀ i, i ∉ D.1 → live i) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit) :
    TreeSimCheckAcceptedRun prims (fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some ())
      (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
        (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i) else failure))
      (do
        let v ← liftComp ($ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then
          (none : Option ℕ) else some 1) → E)) (LocalSpec C)
        let r ← liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C)
        let p ← (leftAdversary (leftAdversary A)).answer st (List.ofFn v)
        soundChallengeNext K D A fuel hs g p r) := by
  rw [executePhase_challenge_live K D A fuel st live hs g, if_pos hall,
    runFunctionality_coin_local D (leftAdversary (leftAdversary A)) st _
      (by intro i hi; simp [hi])]
  simp only [bind_assoc, pure_bind]
  apply TreeSimCheckAcceptedRun.bind_right
  intro v
  have h₁ := TreeSimCheckAcceptedRun.bind_right prims
    (fun out : A.State × (C.Party → Option Unit) => ∃ i, i ∉ D.1 ∧ out.2 i = some ())
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (fun p => treeSimCheck_afterChallenge prims K D A fuel hs tag L htag g (List.ofFn v) p)
  have h₂ := TreeSimCheckAcceptedRun.of_sameRun prims
    (fun out : A.State × (C.Party → Option Unit) => ∃ i, i ∉ D.1 ∧ out.2 i = some ()) (sameRun_swap prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (liftComp (challengeQuery K tag L (List.ofFn v)) (LocalSpec C))
    (fun p r => soundChallengeNext K D A fuel hs g p r))
  simpa only [leftAdversary, bind_assoc, pure_bind] using h₁.trans prims h₂

/-- Initial-weight normalization preserves cache-dependent events on every branch
where an honest operator accepts. -/
theorem treeSimCheck_afterStart [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel d : ℕ) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (v : List E) (p : A.State × Finset C.Party) :
    TreeSimCheckAcceptedRun prims (fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some ())
      (executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)))
      (liftComp (startQuery K tag L v d) (LocalSpec C) >>= soundStartNext K D A fuel hs g p) := by
  by_cases hp : ∃ i, i ∉ D.1 ∧ i ∈ p.2
  · exact TreeSimCheckAcceptedRun.of_sameRun prims _
      (executePhase_afterStart_common prims K D A fuel d p.1 hs tag L htag v p.2 hp g)
  · have he : executePhase localRoles D A (checkFunctionalities K) fuel p.1
        (fun i => afterStart K (hs i) d (g i) (if i ∉ D.1 ∧ i ∈ p.2 then some v else none)) =
        pure (p.1, fun _ : C.Party => (none : Option Unit)) := by
      rw [executePhase_congr_honest D A _ _ p.1 _ (fun _ => failure), executePhase_failure]
      intro i hi
      have hn : ¬ (i ∉ D.1 ∧ i ∈ p.2) := fun h => hp ⟨i, h⟩
      simp [hn, afterStart]
    have hg : soundStartNext K D A fuel hs g p =
        fun _ => pure (p.1, fun _ : C.Party => (none : Option Unit)) :=
      funext (soundStartNext_missing K D A fuel hs g p hp)
    rw [he, hg]
    apply TreeSimCheckAcceptedRun.prefetch_rejected
    intro cache r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_start_normalize [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel d : ℕ) (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit) :
    TreeSimCheckAcceptedRun prims (fun out => ∃ i, i ∉ D.1 ∧ out.2 i = some ())
      (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
        (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= g i).run' (hs i)))
      (do
        let v ← liftComp ($ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then
          (none : Option ℕ) else some 1) → E)) (LocalSpec C)
        let r ← liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C)
        let p ← (leftAdversary (leftAdversary A)).answer st (List.ofFn v)
        soundStartNext K D A fuel hs g p r) := by
  rw [executePhase_start K D A fuel st hs d g,
    runFunctionality_coin_local D (leftAdversary (leftAdversary A)) st _
      (by intro i hi; simp [hi])]
  simp only [bind_assoc, pure_bind]
  apply TreeSimCheckAcceptedRun.bind_right
  intro v
  have h₁ := TreeSimCheckAcceptedRun.bind_right prims
    (fun out : A.State × (C.Party → Option Unit) => ∃ i, i ∉ D.1 ∧ out.2 i = some ())
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (fun p => treeSimCheck_afterStart prims K D A fuel d hs tag L htag g (List.ofFn v) p)
  have h₂ := TreeSimCheckAcceptedRun.of_sameRun prims
    (fun out : A.State × (C.Party → Option Unit) => ∃ i, i ∉ D.1 ∧ out.2 i = some ()) (sameRun_swap prims
    ((leftAdversary (leftAdversary A)).answer st (List.ofFn v))
    (liftComp (startQuery K tag L (List.ofFn v) d) (LocalSpec C))
    (fun p r => soundStartNext K D A fuel hs g p r))
  simpa only [leftAdversary, bind_assoc, pure_bind] using h₁.trans prims h₂

/-- A contextual challenge bound with collisions excluded by the continuation.
No birthday term is charged. `keys` covers all expansions already in the cache;
the counted-query guessing argument must establish that coverage at each use. -/
theorem treeSimCheck_challenge_good {β : Type} (tag label : ℕ) (coin : List E)
    (keys : Finset HashOutput) (cache : HashCache C)
    (hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ keys)
    (bad : E → Prop) (m : ℕ)
    (hcard : (Finset.univ.filter bad).card ≤ m)
    (cont : HashOutput → Option E × HashCache C → ProbComp β)
    (accept : β → Prop) (ε : ℝ≥0∞)
    (hcollision : ∀ key p, key ∈ keys → Pr[accept | cont key p] = 0)
    (hnext : ∀ key p,
      (∀ r, p.1 = some r → ¬ bad r) → Pr[accept | cont key p] ≤ ε) :
    Pr[accept | (do
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label
          (coin.flatMap fun v => List.ofFn (K.encode v)))) (LocalSpec C))).run cache
      let p ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key.1 challengeTries 0)).run key.2
      cont key.1 p)] ≤ m / (Fintype.card E - 2 : ℕ) + ε := by
  classical
  letI : SampleableType E := SampleableType.ofFintype E
  apply probEvent_bind_le_of_forall_le
  intro key hkey
  by_cases hc : key.1 ∈ keys
  · have hz : Pr[accept | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key.1 challengeTries 0)).run key.2 >>= cont key.1] ≤ 0 := by
      apply probEvent_bind_le_of_forall_le
      intro p _
      exact le_of_eq (hcollision key.1 p hc)
    exact hz.trans (bot_le)
  · have fresh : ∀ idx, key.2 (.expand key.1 idx) = none := by
      intro idx
      by_contra hn
      have hquery : ¬ IsFixed (C := C) (.coinKey tag label
          (coin.flatMap fun v => List.ofFn (K.encode v))) := by
        rintro ⟨_, h, _⟩
        cases h
      rw [simulateQ_localAnswer_liftComp] at hkey
      rcases support_hashQuery_entries prims hquery cache key hkey _ hn with h | h
      · exact hc (hexpand key.1 idx h)
      · cases h
    have hbad := probEvent_findChallenge_mem prims K key.1 (Finset.univ.filter bad)
      challengeTries 0 key.2 (fun idx _ => fresh idx)
    have bound : Pr[fun p => ∃ r, bad r ∧ p.1 = some r |
        (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
          (findChallenge K key.1 challengeTries 0)).run key.2] ≤
        m / (Fintype.card E - 2 : ℕ) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbad
      exact hbad.trans (by gcongr)
    have h := probEvent_bind_le_add
      (mx := (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key.1 challengeTries 0)).run key.2)
      (my := cont key.1) (p := fun p => ¬ ∃ r, bad r ∧ p.1 = some r)
      (q := fun out => ¬ accept out) (by simpa using bound)
      (fun p _ hp => by simpa using hnext key.1 p (fun r hr hb => hp ⟨r, hb, hr⟩))
    simpa using h

theorem treeSimCheck_findChallenge_good {β : Type} (key : HashOutput) (cache : HashCache C)
    (fresh : ∀ idx, cache (.expand key idx) = none)
    (bad : E → Prop) (m : ℕ) (hcard : (Finset.univ.filter bad).card ≤ m)
    (cont : Option E × HashCache C → ProbComp β) (accept : β → Prop) (ε : ℝ≥0∞)
    (hnext : ∀ p, p ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key challengeTries 0)).run cache) →
      (∀ r, p.1 = some r → ¬ bad r) → Pr[accept | cont p] ≤ ε) :
    Pr[accept | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (findChallenge K key challengeTries 0)).run cache >>= cont] ≤
      m / (Fintype.card E - 2 : ℕ) + ε := by
  letI : SampleableType E := SampleableType.ofFintype E
  have hb := probEvent_findChallenge_mem prims K key (Finset.univ.filter bad)
    challengeTries 0 cache (fun idx _ => fresh idx)
  have bound : Pr[fun p => ∃ r, bad r ∧ p.1 = some r |
      (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key challengeTries 0)).run cache] ≤
      m / (Fintype.card E - 2 : ℕ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hb.trans (by gcongr)
  have h := probEvent_bind_le_add
    (mx := (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (findChallenge K key challengeTries 0)).run cache)
    (my := cont) (p := fun p => ¬ ∃ r, bad r ∧ p.1 = some r)
    (q := fun out => ¬ accept out) (by simpa using bound)
    (fun p hs hp => by simpa using hnext p hs (fun r hr hb => hp ⟨r, hb, hr⟩))
  simpa using h

/-- Honest coin-key collisions are excluded, while adversarial expansion-key
guesses are charged separately. This distinction is required by the fixed event. -/
theorem treeSimCheck_challenge_guesses {β : Type} (tag label : ℕ) (coin : List E)
    (keys guesses : Finset HashOutput) (cache : HashCache C)
    (fresh : cache (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))) = none)
    (hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ keys ∨ key ∈ guesses)
    (bad : E → Prop) (m : ℕ) (hcard : (Finset.univ.filter bad).card ≤ m)
    (cont : HashOutput → Option E × HashCache C → ProbComp β)
    (accept : β → Prop) (ε : ℝ≥0∞)
    (hcollision : ∀ key p, key ∈ keys → Pr[accept | cont key p] = 0)
    (hnext : ∀ key p, (∀ r, p.1 = some r → ¬ bad r) → Pr[accept | cont key p] ≤ ε) :
    Pr[accept | (do
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label
          (coin.flatMap fun v => List.ofFn (K.encode v)))) (LocalSpec C))).run cache
      let p ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key.1 challengeTries 0)).run key.2
      cont key.1 p)] ≤ guesses.card / 2 ^ 256 + (m / (Fintype.card E - 2 : ℕ) + ε) := by
  letI : SampleableType E := SampleableType.ofFintype E
  have hquery : ¬ IsFixed (C := C) (.coinKey tag label
      (coin.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩
    cases h
  rw [simulateQ_localAnswer_liftComp]
  have hguess := probEvent_hash_fresh_mem prims hquery fresh guesses
  have h := probEvent_bind_le_add
    (mx := (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (hashQuery (.coinKey tag label (coin.flatMap fun v => List.ofFn (K.encode v))))).run cache)
    (my := fun key => (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (findChallenge K key.1 challengeTries 0)).run key.2 >>= cont key.1)
    (p := fun key => key.1 ∉ guesses) (q := fun out => ¬ accept out)
    (ε₂ := m / (Fintype.card E - 2 : ℕ) + ε) (by simpa using hguess)
    (fun key hkey hn => ?_)
  · simpa using h
  · simp only [not_not]
    by_cases hk : key.1 ∈ keys
    · apply probEvent_bind_le_of_forall_le
      intro p _
      rw [hcollision key.1 p hk]
      exact bot_le
    · apply treeSimCheck_findChallenge_good prims K key.1 key.2 _ bad m hcard (cont key.1) accept ε
        (fun p _ => hnext key.1 p)
      intro idx
      by_contra hne
      rcases support_hashQuery_entries prims hquery cache key hkey _ hne with he | he
      · exact (hexpand key.1 idx he).elim hk hn
      · cases he

def treeSimCheckCoinSeen (seen : Finset (Query C)) : Finset (Query C) :=
  seen.filter fun q => match q with | .coinKey .. => True | _ => False

def treeSimCheckExpandSeen (seen : Finset (Query C)) : Finset (Query C) :=
  seen.filter fun q => match q with | .expand .. => True | _ => False

theorem treeSimCheck_seen_card (seen : Finset (Query C)) :
    (treeSimCheckCoinSeen seen).card +
      ((treeSimCheckExpandSeen seen).image soundExpansionKey).card ≤ seen.card := by
  have hd : Disjoint (treeSimCheckCoinSeen seen) (treeSimCheckExpandSeen seen) := by
    apply Finset.disjoint_left.mpr
    intro q hc he
    cases q <;> simp_all [treeSimCheckCoinSeen, treeSimCheckExpandSeen]
  have hs : treeSimCheckCoinSeen seen ∪ treeSimCheckExpandSeen seen ⊆ seen := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (Finset.mem_filter.mp hq).1
    · exact (Finset.mem_filter.mp hq).1
  calc
    _ ≤ (treeSimCheckCoinSeen seen).card + (treeSimCheckExpandSeen seen).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = (treeSimCheckCoinSeen seen ∪ treeSimCheckExpandSeen seen).card :=
      (Finset.card_union_of_disjoint hd).symm
    _ ≤ _ := Finset.card_le_card hs

set_option maxRecDepth 2048 in
/-- The two kinds of counted guesses share the single `q / |E|` budget.
Earlier honest expansion keys are excluded pointwise by the fixed hash event. -/
theorem treeSimCheck_coin_contextual [SampleableType E] {β : Type}
    (tag label L : ℕ) (hL : L ≤ label) (cache : HashCache C)
    (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys)
    (bad : E → Prop) (m : ℕ) (hcard : (Finset.univ.filter bad).card ≤ m)
    (cont : E → HashOutput → Option E × HashCache C → ProbComp β)
    (accept : β → Prop) (ε : ℝ≥0∞)
    (hcollision : ∀ r key p, key ∈ keys → Pr[accept | cont r key p] = 0)
    (hnext : ∀ r key p, (∀ c, p.1 = some c → ¬ bad c) → Pr[accept | cont r key p] ≤ ε) :
    Pr[accept | (do
      let r ← $ᵗ E
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache
      let p ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key.1 challengeTries 0)).run key.2
      cont r key.1 p)] ≤
      seen.card / Fintype.card E + (m / (Fintype.card E - 2 : ℕ) + ε) := by
  let coins := treeSimCheckCoinSeen seen
  let expansions := (treeSimCheckExpandSeen seen).image soundExpansionKey
  have hguess := probEvent_uniform_injective_mem
    (fun r : E => Query.coinKey (C := C) tag label (List.ofFn (K.encode r)))
    (coin_input_injective K tag label) coins
  have h := probEvent_bind_le_add
    (mx := $ᵗ E)
    (my := fun r => do
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache
      let p ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (findChallenge K key.1 challengeTries 0)).run key.2
      cont r key.1 p)
    (p := fun r => Query.coinKey tag label (List.ofFn (K.encode r)) ∉ coins)
    (q := fun out => ¬ accept out)
    (ε₂ := expansions.card / 2 ^ 256 + (m / (Fintype.card E - 2 : ℕ) + ε))
    (by simpa using hguess) (fun r _ hr => ?_)
  · simp only [not_not] at h
    refine h.trans ?_
    have cardinal := treeSimCheck_seen_card seen
    have field_le : (Fintype.card E : ℝ≥0∞) ≤ 2 ^ 256 := by
      rw [card_field K]
      norm_num [elementBits]
    calc
      _ ≤ (coins.card : ℝ≥0∞) / Fintype.card E +
          (expansions.card / Fintype.card E + (m / (Fintype.card E - 2 : ℕ) + ε)) := by
        gcongr
      _ = ((coins.card + expansions.card : ℕ) : ℝ≥0∞) / Fintype.card E +
          (m / (Fintype.card E - 2 : ℕ) + ε) := by
        rw [Nat.cast_add, ENNReal.add_div]
        exact (add_assoc _ _ _).symm
      _ ≤ _ := by gcongr
  · simp only [not_not]
    have hfresh : cache (.coinKey tag label (List.ofFn (K.encode r))) = none := by
      apply hc.fresh tag label _ hL
      simpa only [coins, treeSimCheckCoinSeen, Finset.mem_filter, and_true] using hr
    have hexpand : ∀ key idx, cache (.expand key idx) ≠ none → key ∈ keys ∨ key ∈ expansions := by
      intro key idx hk
      rcases hc.2 key idx hk with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_image.mpr ⟨.expand key idx, by
          simpa [treeSimCheckExpandSeen] using h, rfl⟩)
    have hflat : [r].flatMap (fun v => List.ofFn (K.encode v)) = List.ofFn (K.encode r) := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hh := treeSimCheck_challenge_guesses prims K tag label [r] keys expansions cache
      (by rw [hflat]; exact hfresh) hexpand bad m hcard (cont r) accept ε (hcollision r) (hnext r)
    simpa only [hflat] using hh

set_option maxRecDepth 2048 in
/-- A uniform coin followed by an arbitrary expansion context. The context
rejects old honest keys, and only counted guesses consume the coin budget. -/
theorem treeSimCheck_coinKey_contextual [SampleableType E] {β : Type}
    (tag label L : ℕ) (hL : L ≤ label) (cache : HashCache C)
    (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys)
    (cont : E → HashOutput → HashCache C → ProbComp β)
    (accept : β → Prop) (δ : ℝ≥0∞)
    (hcollision : ∀ r key, key ∈ support ((simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r)))) (LocalSpec C))).run cache) →
      key.1 ∈ keys → Pr[accept | cont r key.1 key.2] = 0)
    (hnext : ∀ r key, key ∈ support ((simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r)))) (LocalSpec C))).run cache) →
      (∀ idx, key.2 (.expand key.1 idx) = none) → Pr[accept | cont r key.1 key.2] ≤ δ) :
    Pr[accept | (do
      let r ← $ᵗ E
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache
      cont r key.1 key.2)] ≤ seen.card / Fintype.card E + δ := by
  let coins := treeSimCheckCoinSeen seen
  let expansions := (treeSimCheckExpandSeen seen).image soundExpansionKey
  have hguess := probEvent_uniform_injective_mem
    (fun r : E => Query.coinKey (C := C) tag label (List.ofFn (K.encode r)))
    (coin_input_injective K tag label) coins
  have h := probEvent_bind_le_add (mx := $ᵗ E)
    (my := fun r => do
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache
      cont r key.1 key.2)
    (p := fun r => Query.coinKey tag label (List.ofFn (K.encode r)) ∉ coins)
    (q := fun out => ¬ accept out) (ε₂ := expansions.card / 2 ^ 256 + δ)
    (by simpa using hguess) (fun r _ hr => ?_)
  · simp only [not_not] at h
    refine h.trans ?_
    have cardinal := treeSimCheck_seen_card seen
    have field_le : (Fintype.card E : ℝ≥0∞) ≤ 2 ^ 256 := by
      rw [card_field K]
      norm_num [elementBits]
    calc
      _ ≤ (coins.card : ℝ≥0∞) / Fintype.card E +
          (expansions.card / Fintype.card E + δ) := by gcongr
      _ = ((coins.card + expansions.card : ℕ) : ℝ≥0∞) / Fintype.card E + δ := by
        rw [Nat.cast_add, ENNReal.add_div]
        exact (add_assoc _ _ _).symm
      _ ≤ _ := by gcongr
  · simp only [not_not]
    have fresh : cache (.coinKey tag label (List.ofFn (K.encode r))) = none := by
      apply hc.fresh tag label _ hL
      simpa only [coins, treeSimCheckCoinSeen, Finset.mem_filter, and_true] using hr
    have hquery : ¬ IsFixed (C := C) (.coinKey tag label (List.ofFn (K.encode r))) := by
      rintro ⟨_, he, _⟩
      cases he
    rw [simulateQ_localAnswer_liftComp]
    have hh := probEvent_bind_le_add
      (mx := (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (hashQuery (.coinKey tag label (List.ofFn (K.encode r))))).run cache)
      (my := fun key => cont r key.1 key.2)
      (p := fun key => key.1 ∉ expansions) (q := fun out => ¬ accept out) (ε₂ := δ)
      (by simpa using probEvent_hash_fresh_mem prims hquery fresh expansions)
      (fun key hkey hguess => ?_)
    · simpa using hh
    · simp only [not_not]
      have hkey' : key ∈ support ((simulateQ (localAnswer prims)
          (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r)))) (LocalSpec C))).run cache) := by
        simpa only [simulateQ_localAnswer_liftComp] using hkey
      by_cases hk : key.1 ∈ keys
      · rw [hcollision r key hkey' hk]
        exact bot_le
      · apply hnext r key hkey'
        intro idx
        by_contra he
        rcases support_hashQuery_entries prims hquery cache key hkey _ he with he | he
        · rcases hc.2 key.1 idx he with he | he
          · exact hk he
          · exact hguess (Finset.mem_image.mpr ⟨.expand key.1 idx, by
              simpa [treeSimCheckExpandSeen] using he, rfl⟩)
        · cases he

/-- Honest expansion keys are backed by earlier, persistent coin inputs. -/
def TreeSimCheckPriorKeys (L : ℕ) (cache : HashCache C) (keys : Finset HashOutput) : Prop :=
  ∀ key ∈ keys, ∃ tag label bits, label < L ∧ cache (.coinKey tag label bits) = some key

theorem TreeSimCheckPriorKeys.mono {L L' : ℕ} {cache next : HashCache C}
    {keys : Finset HashOutput} (prior : TreeSimCheckPriorKeys L cache keys)
    (hl : L ≤ L') (hc : cache ≤ next) : TreeSimCheckPriorKeys L' next keys := by
  intro key hk
  obtain ⟨tag, label, bits, hlt, he⟩ := prior key hk
  exact ⟨tag, label, bits, hlt.trans_le hl, hc he⟩

theorem TreeSimCheckPriorKeys.insert {L label tag : ℕ} {cache : HashCache C}
    {keys : Finset HashOutput} {bits : List Bit} {key : HashOutput}
    (prior : TreeSimCheckPriorKeys L cache keys) (hl : L ≤ label)
    (he : cache (.coinKey tag label bits) = some key) :
    TreeSimCheckPriorKeys (label + 1) cache (insert key keys) := by
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact ⟨tag, label, bits, by omega, he⟩
  · exact (prior.mono (by omega) le_rfl) k hk

/-- The old-key exclusion for an actual shared-cache continuation is proved
from its cached coin inputs; it is not an extra soundness hypothesis. -/
theorem treeSimCheck_coin_boundary [SampleableType E] {α : Type}
    (tag label L : ℕ) (hL : L ≤ label) (cache : HashCache C)
    (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (cont : E → HashOutput → OracleComp (LocalSpec C) α)
    (accept : α × HashCache C → Prop) (δ : ℝ≥0∞)
    (hnext : ∀ r key, key ∈ support ((simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache) →
      (∀ idx, key.2 (.expand key.1 idx) = none) →
      Pr[fun p => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p |
        (simulateQ (localAnswer prims) (cont r key.1)).run key.2] ≤ δ) :
    Pr[fun p => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p | (do
      let r ← $ᵗ E
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache
      (simulateQ (localAnswer prims) (cont r key.1)).run key.2)] ≤
      seen.card / Fintype.card E + δ := by
  apply treeSimCheck_coinKey_contextual prims K tag label L hL cache seen keys hc
    (fun r key cache' => (simulateQ (localAnswer prims) (cont r key)).run cache') _ δ _ hnext
  intro r key hkey hk
  obtain ⟨oldTag, oldLabel, oldBits, hlt, old⟩ := prior key.1 hk
  rw [simulateQ_localAnswer_liftComp] at hkey
  have hquery : ¬ IsFixed (C := C) (.coinKey tag label (List.ofFn (K.encode r))) := by
    rintro ⟨_, he, _⟩
    cases he
  obtain ⟨hgrows, hcurrent, _⟩ := support_hashQuery prims hquery cache key hkey
  exact treeSimCheck_coin_collision_zero prims (cont r key.1) key.2 tag label oldTag oldLabel
    (List.ofFn (K.encode r)) oldBits key.1 (hlt.trans_le hL) (hgrows old) hcurrent accept

private theorem treeSimCheck_cache_after_coin
    {L tag label : ℕ} {cache : HashCache C} {seen : Finset (Query C)} {keys : Finset HashOutput}
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (hL : L ≤ label) (v : List E) (key : HashOutput × HashCache C)
    (hkey : key ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (hashQuery (.coinKey tag label (v.flatMap fun r => List.ofFn (K.encode r))))).run cache))
    (next : HashCache C) (hgrows : key.2 ≤ next)
    (hentries : ∀ q, next q ≠ none → key.2 q ≠ none ∨ ∃ idx, q = .expand key.1 idx) :
    SoundCache (label + 1) next seen (insert key.1 keys) ∧
      TreeSimCheckPriorKeys (label + 1) next (insert key.1 keys) := by
  have hq : ¬ IsFixed (Query.coinKey (C := C) tag label (v.flatMap fun r => List.ofFn (K.encode r))) := by
    rintro ⟨_, he, _⟩
    cases he
  obtain ⟨hcache, hself, hk⟩ := support_hashQuery prims hq cache key hkey
  refine ⟨⟨?_, ?_⟩, (prior.mono le_rfl (hcache.trans hgrows)).insert hL (hgrows hself)⟩
  · intro tg lab bits hl hb
    rcases hentries _ hb with he | ⟨idx, he⟩
    · rcases hk _ he with he | he
      · exact hc.1 tg lab bits (by omega) he
      · have hh := (Query.coinKey.inj he).2.1
        omega
    · cases he
  · intro k idx hb
    rcases hentries _ hb with he | ⟨idx', he⟩
    · rcases hk _ he with he | he
      · exact (hc.2 k idx he).imp_left (Finset.mem_insert_of_mem)
      · cases he
    · have hh := (Query.expand.inj he).1
      exact Or.inl (hh ▸ Finset.mem_insert_self _ _)

/-- A whole challenge, including its continuing local computation. Its only
errors are the counted coin guess and the polynomial root set. -/
theorem treeSimCheck_challenge_boundary [SampleableType E] {α : Type}
    (tag L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (bad : E → Prop) (m : ℕ) (hcard : (Finset.univ.filter bad).card ≤ m)
    (cont : E → Option E → OracleComp (LocalSpec C) α)
    (accept : α × HashCache C → Prop) (ε : ℝ≥0∞)
    (hnone : ∀ r cache', Pr[fun p =>
      ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p |
        (simulateQ (localAnswer prims) (cont r none)).run cache'] = 0)
    (hnext : ∀ r c key cache', SoundCache (L + 1) cache' seen (insert key keys) →
      TreeSimCheckPriorKeys (L + 1) cache' (insert key keys) → ¬ bad c →
      Pr[fun p => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p |
        (simulateQ (localAnswer prims) (cont r (some c))).run cache'] ≤ ε) :
    Pr[fun p => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p | (do
      let r ← $ᵗ E
      let p ← (simulateQ (localAnswer prims)
        (liftComp (challengeQuery K tag L [r]) (LocalSpec C))).run cache
      (simulateQ (localAnswer prims) (cont r p.1)).run p.2)] ≤
      seen.card / Fintype.card E + (m / (Fintype.card E - 2 : ℕ) + ε) := by
  simp only [challengeQuery, liftComp_bind, simulateQ_bind, StateT.run_bind, bind_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hb := treeSimCheck_coin_boundary prims K tag L L le_rfl cache seen keys hc prior
    (fun r key => liftComp (findChallenge K key challengeTries 0) (LocalSpec C) >>= cont r)
    accept (m / (Fintype.card E - 2 : ℕ) + ε) ?_
  · simpa only [simulateQ_bind, StateT.run_bind, simulateQ_localAnswer_liftComp] using hb
  · intro r key hkey hfresh
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_localAnswer_liftComp]
    apply treeSimCheck_findChallenge_good prims K key.1 key.2 hfresh bad m hcard
      (fun p => (simulateQ (localAnswer prims) (cont r p.1)).run p.2) _ ε
    intro p hp hgood
    have hgrows : key.2 ≤ p.2 := (grows_localAnswer prims).simulateQ
      (liftComp (findChallenge K key.1 challengeTries 0) (LocalSpec C)) key.2 p
      (by simpa only [simulateQ_localAnswer_liftComp] using hp)
    have hh := treeSimCheck_cache_after_coin prims K hc prior (tag := tag) le_rfl [r] key
      (by simpa only [simulateQ_localAnswer_liftComp, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] using hkey) p.2 hgrows
      (support_findChallenge_entries prims K key.1 _ _ _ _ hp)
    cases he : p.1 with
    | none => rw [hnone]; exact bot_le
    | some c => simpa only [he] using hnext r c key.1 p.2 hh.1 hh.2 (hgood c he)

private theorem treeSimCheck_uniform_one [SampleableType E] {α : Type}
    (n : ℕ) (hn : n = 1) (cont : List E → ProbComp α) :
    𝒟[(do let v ← $ᵗ (Fin n → E); cont (List.ofFn v))] =
      𝒟[(do let r ← $ᵗ E; cont [r])] := by
  subst n
  have hb : Function.Bijective (fun r : E => fun _ : Fin 1 => r) := by
    constructor
    · intro x y he
      exact congrFun he 0
    · intro f
      refine ⟨f 0, ?_⟩
      funext i
      have he : i = 0 := Subsingleton.elim _ _
      rw [he]
  have he := evalDist_map_bijective_uniform_cross E (fun r : E => fun _ : Fin 1 => r) hb
  rw [evalDist_bind, ← he, ← evalDist_bind, bind_map_left]
  simp only [List.ofFn_const, List.replicate_one]

set_option maxHeartbeats 1000000 in
/-- Contextual soundness of one reached GS20 challenge phase. Unlike the
standalone bound, this keeps the collision-free final-cache event throughout. -/
theorem treeSimCheck_challenge_phase [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (bad : E → Prop) (m : ℕ) (hcard : (Finset.univ.filter bad).card ≤ m) (ε : ℝ≥0∞)
    (hnext : ∀ p r key cache' seen', SoundCache (L + 1) cache' seen' (insert key keys) →
      TreeSimCheckPriorKeys (L + 1) cache' (insert key keys) →
      seen'.card ≤ seen.card + step → ¬ bad r →
      Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
        ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
        (simulateQ (localAnswer prims) (soundChallengeNext K D A fuel hs g p (some r))).run cache'] ≤ ε) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
          (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i)
            else failure))).run cache] ≤
      seen.card / Fintype.card E + (m / (Fintype.card E - 2 : ℕ) + ε) := by
  rw [treeSimCheck_challenge_normalize prims K D A fuel st live hall hs tag L htag g cache _
    (fun r hr => hr.2)]
  let next := fun v : List E => do
    let p ← (simulateQ (localAnswer prims)
      (liftComp (challengeQuery K tag L v) (LocalSpec C))).run cache
    let ans ← (simulateQ (localAnswer prims)
      ((leftAdversary (leftAdversary A)).answer st v)).run p.2
    (simulateQ (localAnswer prims) (soundChallengeNext K D A fuel hs g ans.1 p.1)).run ans.2
  suffices hb : Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
    ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (do let v ← $ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then
        (none : Option ℕ) else some 1) → E); next (List.ofFn v))] ≤
      seen.card / Fintype.card E + (m / (Fintype.card E - 2 : ℕ) + ε) by
    simpa only [next, simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left] using hb
  rw [probEvent_def, treeSimCheck_uniform_one _ (firstInput_honest_const D 1) next, ← probEvent_def]
  dsimp only [next]
  have hb := treeSimCheck_challenge_boundary prims K tag L cache seen keys hc prior bad m hcard
    (fun v r => (leftAdversary (leftAdversary A)).answer st [v] >>=
      fun p => soundChallengeNext K D A fuel hs g p r)
    (fun out => ∃ i, i ∉ D.1 ∧ out.1.2 i = some ()) ε ?_ ?_
  · simpa only [simulateQ_bind, StateT.run_bind] using hb
  · intro v cache'
    apply probEvent_eq_zero
    intro out hout he
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hout
    obtain ⟨ans, _, hout⟩ := hout
    simp only [soundChallengeNext_none, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hout
    subst out
    simpa using he.2
  · intro v r key cache' hc' prior' hgood
    simp only [simulateQ_bind, StateT.run_bind]
    apply probEvent_bind_le_of_forall_le
    intro ans hans
    have hans' : ans ∈ support ((simulateQ (localAnswer prims)
        ((leftAdversary (leftAdversary A)).answer st [v])).run cache') := by
      simpa only [simulateQ_bind, StateT.run_bind] using hans
    obtain ⟨seen', hcache', hcard'⟩ := hc'.local prims
      ((leftAdversary (leftAdversary A)).answer st [v]) step
      (sound_coinReply_bound A step ha st _) ans hans'
    exact hnext ans.1 r key ans.2 seen' hcache'
      (prior'.mono le_rfl ((grows_localAnswer prims).simulateQ _ _ _ hans')) hcard' hgood

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_finalChallenge_phase [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 2) st
          (fun i => if live i then
            (finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)).run' (hs i)
            else failure))).run cache] ≤
      seen.card / Fintype.card E + 2 / (Fintype.card E - 2 : ℕ) := by
  classical
  let I := fun f : C.Party → E => interpolate K D.1 f 0
  let bad := fun r => r * (I d - I a * I b) + (1 + r) * (I q0 - I wa * I wb) +
    r * (1 + r) * (I q2 - (I wa + I a) * (I wb + I b)) = 0
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) ((fuel + 1) + 1) st
      (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= fun r =>
        StateT.lift (finalOpenProgram K i
          (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r))).run' (hs i)
        else failure))).run cache] ≤ _
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · have hcard : (Finset.univ.filter bad).card ≤ 2 :=
      final_residual_card_le_two (I a) (I b) (I d) (I q0 - I wa * I wb)
        (I q2 - (I wa + I a) * (I wb + I b)) hwrong
    simpa only [add_zero, Nat.cast_ofNat] using treeSimCheck_challenge_phase prims K D A
      (fuel + 1) step ha st live hall hs tag L htag _ cache seen keys hc prior bad 2
      (by convert hcard using 1; congr 2) 0 (by
        intro p r key cache' seen' hc' prior' hs' hgood
        by_cases hlive : ∃ i, i ∉ D.1 ∧ i ∈ p.2
        · apply le_of_eq
          apply probEvent_eq_zero
          intro out hout hout'
          apply hgood
          have houtput : out.1 ∈ support ((simulateQ (localAnswer prims)
              (soundChallengeNext K D A (fuel + 1) hs
                (fun i r => StateT.lift (finalOpenProgram K i
                  (finalOpenVector (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i) r)))
                p (some r))).run' cache') := by
            rw [StateT.run'_eq, support_map]
            exact ⟨out, hout, rfl⟩
          apply finalOpen_support_effective_root prims K D A fuel p.1 (· ∈ p.2) hlive
            wa wb a b d q0 q2 r cache' out.1
          · simp only [soundChallengeNext, StateT.run'_eq, StateT.run_lift,
              map_bind, map_pure, bind_pure] at houtput
            convert houtput using 1; congr 7
            funext i
            by_cases hi : i ∈ p.2 <;> simp [hi]
          · exact ⟨hout'.2.choose, hout'.2.choose_spec.2⟩
        · rw [soundChallengeNext_missing K D A _ _ _ p hlive]
          simp)
  · rw [executePhase_challenge_live, if_neg hall]
    simp

theorem treeSimCheck_prefix {α β : Type}
    (oa : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β)
    (step : ℕ) (hq : IsQueryBoundP oa Counted step)
    (L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (accept : β × HashCache C → Prop) (ε : ℝ≥0∞)
    (h : ∀ a cache' seen', SoundCache L cache' seen' keys →
      TreeSimCheckPriorKeys L cache' keys → seen'.card ≤ seen.card + step →
      Pr[accept | (simulateQ (localAnswer prims) (f a)).run cache'] ≤ ε) :
    Pr[accept | (simulateQ (localAnswer prims) (oa >>= f)).run cache] ≤ ε := by
  simp only [simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro p hp
  obtain ⟨seen', hc', hn⟩ := hc.local prims oa step hq p hp
  exact h p.1 p.2 seen' hc'
    (prior.mono le_rfl ((grows_localAnswer prims).simulateQ oa cache p hp)) hn

private theorem treeSimCheck_sample {α β : Type} [SampleableType α]
    (f : α → OracleComp (LocalSpec C) β) (cache : HashCache C)
    (accept : β × HashCache C → Prop) (ε : ℝ≥0∞)
    (h : ∀ a, Pr[accept | (simulateQ (localAnswer prims) (f a)).run cache] ≤ ε) :
    Pr[accept | (simulateQ (localAnswer prims) (liftComp ($ᵗ α) (LocalSpec C) >>= f)).run cache] ≤ ε := by
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  exact probEvent_bind_le_of_forall_le (fun a _ => h a)

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_digest_phase [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step q : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (salts : C.Party → Shares C Bit) (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (hq : seen.card + step ≤ q) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 3) st
          (fun i => (compareDigests (localContext i) (salts i) >>= fun _ =>
            finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)).run' (hs i)))).run cache] ≤
      q / Fintype.card E + 2 / (Fintype.card E - 2 : ℕ) := by
  have he := executePhase_digestColumns prims K D A (fuel + 3)
    st salts hs (fun i _ => finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i))
  rw [probEvent_def, he cache, ← probEvent_def]
  simp only [simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro ds hds
  have hc' := hc.digestColumns prims D salts (fun i => (hs i).history) ds hds
  have prior' := prior.mono le_rfl ((grows_localAnswer prims).simulateQ _ _ _ hds)
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) ((fuel + 2) + 1) st _)).run ds.2] ≤ _
  rw [executePhase_afterDigests_round]
  apply treeSimCheck_prefix prims _ _ step (hr st _) L ds.2 seen keys hc' prior'
  intro p cache' seen' hc'' prior'' hseen
  refine (treeSimCheck_finalChallenge_phase prims K D A fuel step ha p.1 _ hs tag L htag
    wa wb a b d q0 q2 hwrong cache' seen' keys hc'' prior'').trans ?_
  have hcard : seen'.card ≤ q := by omega
  gcongr

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_salt_phase [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step q : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (wa wb a b d q0 q2 : C.Party → E)
    (hwrong : interpolate K D.1 d 0 ≠ interpolate K D.1 a 0 * interpolate K D.1 b 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (hq : seen.card + 2 * step ≤ q) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 4) st
          (fun i => ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
            compareDigests (localContext i) salts.1 >>= fun _ =>
            finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i)).run' (hs i)))).run cache] ≤
      q / Fintype.card E + 2 / (Fintype.card E - 2 : ℕ) := by
  have he := executePhase_randBits_first prims K D A (fuel + 3)
    st 256 hs (fun i salts => compareDigests (localContext i) salts >>= fun _ =>
      finalAfterDigests K i (wa i) (wb i) (a i) (b i) (d i) (q0 i) (q2 i))
  rw [probEvent_def, he cache, ← probEvent_def]
  apply treeSimCheck_prefix prims _ _ step (saltReply_queryBound A st step ha) L cache seen keys hc prior
  intro p cache' seen' hc' prior' hseen
  apply treeSimCheck_sample prims
  intro fresh
  apply treeSimCheck_digest_phase prims K D A fuel step q hr ha p.1 _ tag (L + 1)
    (fun i hi => by simp [htag i hi]) _ wa wb a b d q0 q2 hwrong cache' seen' keys
    (hc'.mono_label (by omega)) (prior'.mono (by omega) le_rfl) (by omega)

set_option maxHeartbeats 1000000 in
/-- The full randomization segment, ending in an accepted scalar test, with
the collision event excluded rather than estimated. -/
theorem treeSimCheck_finalStep [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel step q : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (Av Bv : C.Party → ℕ → E) (V : C.Party → E)
    (hwrong : interpolate K D.1 V 0 ≠
      interpolate K D.1 (fun i => Av i 0) 0 * interpolate K D.1 (fun i => Bv i 0) 0)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (hq : seen.card + 4 * step ≤ q) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 6) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i)
            else failure))).run cache] ≤ q / Fintype.card E + 2 / (Fintype.card E - 2 : ℕ) := by
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · rw [executePhase_congr_honest D A _ _ st _
      (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i))
      (fun i hi => if_pos (hall i hi))]
    have he := finalStep_masks prims K D A (fuel + 4) st Av Bv V hs
    rw [probEvent_def, he cache, ← probEvent_def]
    apply treeSimCheck_prefix prims _ _ step (sound_maskReply_bound A step ha st) L cache seen keys hc prior
    intro p cache1 seen1 hc1 prior1 hn1
    apply treeSimCheck_prefix prims _ _ step (sound_extendReply_bound A step ha _ _) L cache1 seen1 keys hc1 prior1
    intro pa cache2 seen2 hc2 prior2 hn2
    apply treeSimCheck_sample prims
    intro w
    apply treeSimCheck_sample prims
    intro z
    by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
    · rw [finalMasked_all K D A _ _ _ _ _ _ _ _ _ _ _ _ _ hrec]
      exact treeSimCheck_salt_phase prims K D A fuel step q hr ha pa.1 _ tag (L + 2)
        (fun i hi => by simp [finalHs, finalState, htag i hi]) _ _ _ _ _ _ _ hwrong cache2 seen2 keys
        (hc2.mono_label (by omega)) (prior2.mono (by omega) le_rfl) (by omega)
    · rw [show fuel + 4 = (fuel + 3) + 1 by omega,
        finalMasked_missing K D A _ _ _ _ _ _ _ _ _ _ _ _ _ (by push Not at hrec; exact hrec)]
      simp
  · rw [show fuel + 6 = (fuel + 5) + 1 by omega,
      finalStep_missing K D A _ _ _ _ _ _ _ (by push Not at hall; exact hall)]
    simp

/-- The algebraic and counted-query error of one reached challenge. -/
def treeSimCheckError (F : Type) [Fintype F] (q m : ℕ) : ℝ≥0∞ :=
  q / Fintype.card F + m / (Fintype.card F - 2 : ℕ)

def TreeSimCheckHalvRest [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q width n j F : ℕ) : Prop :=
  ∀ (st : Ad.State) (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C) (tag L : ℕ),
    (∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L) →
    ∀ (A B : C.Party → ℕ → E) (V : C.Party → E),
    interpolate K D.1 V 0 ≠ ∑ k ∈ Finset.range (halvedLength^[j] width),
      interpolate K D.1 (fun i => A i k) 0 * interpolate K D.1 (fun i => B i k) 0 →
    ∀ (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    SoundCache L cache seen keys → TreeSimCheckPriorKeys L cache keys →
    seen.card + (2 * n + 4) * step ≤ q →
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if live i then (halvProg K width n j (A i) (B i) (V i) i).run' (hs i)
            else failure))).run cache] ≤ (n + 1 : ℕ) * treeSimCheckError E q 2

set_option maxHeartbeats 500000 in
theorem treeSimCheck_halvRest_zero [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q width fuel : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width) :
    TreeSimCheckHalvRest prims K D Ad step q width 0 (halvingSteps width) (fuel + 6) := by
  intro st live _ hs tag L htag A B V hwrong cache seen keys hc prior hq
  rw [iterate_halvingSteps width hw] at hwrong
  simp only [Finset.sum_range_one] at hwrong
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.cast_one, one_mul, halvProg_zero,
    treeSimCheckError, Nat.cast_ofNat] using
    treeSimCheck_finalStep prims K D Ad fuel step q hr ha st live hs tag L htag A B V hwrong cache seen keys hc prior hq

set_option maxHeartbeats 500000 in
theorem treeSimCheck_halvRest_succ [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q width n j F : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    (hIH : TreeSimCheckHalvRest prims K D Ad step q width n (j + 1) F) :
    TreeSimCheckHalvRest prims K D Ad step q width (n + 1) j (F + 1 + 1) := by
  intro st live _ hs tag L htag A B V hwrong cache seen keys hc prior hq
  by_cases hall : ∀ i, i ∉ D.1 → live i
  swap
  · rw [halvExtend_missing K D Ad _ st live hall hs width n j A B V]
    simp
  rw [halvExtend_local K D Ad _ st live hall hs width n j A B V]
  apply treeSimCheck_prefix prims _ _ step (sound_extendReply_bound Ad step ha _ _) L cache seen keys hc prior
  intro pa cache1 seen1 hc1 prior1 hn1
  apply treeSimCheck_sample prims
  intro fresh
  rw [halvAfter_form]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  swap
  · rw [executePhase_challenge_live, if_neg hrec]
    simp
  let q0 := fun i => conv K (localContext i)
    (halvOut K D (halvedLength^[j] width) A B pa fresh i) 0
  let q2 := fun i => conv K (localContext i)
    (halvOut K D (halvedLength^[j] width) A B pa fresh i) 1
  let bad := fun r : E =>
    interpolate K D.1 (fun i => q0 i + (V i + q2 i) * r + q2 i * r ^ 2) 0 =
      ∑ k ∈ Finset.range (halvedLength (halvedLength^[j] width)),
        interpolate K D.1 (fun i => halvFold (halvedLength^[j] width) r (A i) k) 0 *
        interpolate K D.1 (fun i => halvFold (halvedLength^[j] width) r (B i) k) 0
  have hcard : (Finset.univ.filter bad).card ≤ 2 := sound_halvFold_card K D _ A B V q0 q2 hwrong
  let hs1 : C.Party → RunState C := fun i =>
    ⟨recordHistory K i (hs i).history (halvOut K D (halvedLength^[j] width) A B pa fresh i) 2,
      (hs i).label + 1, (hs i).tag⟩
  let g := halvCont K width n j A B V (halvOut K D (halvedLength^[j] width) A B pa fresh)
  apply le_trans (treeSimCheck_challenge_phase prims K D Ad F step ha pa.1
    (fun i => i ∈ pa.2.2.2.2) hrec hs1 tag (L + 1)
    (fun i hi => by simp [hs1, htag i hi]) g cache1 seen1 keys (hc1.mono_label (by omega)) (prior1.mono (by omega) le_rfl)
    bad 2 (by convert hcard using 1; congr 2) ((n + 1 : ℕ) * treeSimCheckError E q 2) ?_) ?_
  · intro p r key cache' seen' hc' prior' hn' hgood
    unfold soundChallengeNext
    apply hIH p.1 (fun i => i ∈ p.2) _ tag ((L + 1) + 1)
      (fun i hi => by simp [hs1, htag i hi])
    · simpa only [Function.iterate_succ_apply'] using hgood
    · exact hc'
    · exact prior'
    · simp only [Nat.add_mul, Nat.mul_add] at hq ⊢
      omega
  · have hcard : seen1.card ≤ q := by
      simp only [Nat.add_mul, Nat.mul_add] at hq
      omega
    calc
      _ = (seen1.card / Fintype.card E + 2 / (Fintype.card E - 2 : ℕ)) +
          (n + 1 : ℕ) * treeSimCheckError E q 2 := by simp only [Nat.cast_ofNat, add_assoc]
      _ ≤ treeSimCheckError E q 2 + (n + 1 : ℕ) * treeSimCheckError E q 2 := by
        unfold treeSimCheckError
        simp only [Nat.cast_ofNat]
        gcongr
      _ = _ := by push_cast; ring



set_option maxHeartbeats 500000 in
theorem treeSimCheck_halvRest_all [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (step q width : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 1 ≤ width) :
    ∀ n j fuel, j + n = halvingSteps width →
      TreeSimCheckHalvRest prims K D Ad step q width n j (fuel + 2 * n + 6)
  | 0, j, fuel, hj => by
    have hj' : j = halvingSteps width := by omega
    subst j
    exact treeSimCheck_halvRest_zero prims K D Ad step q width fuel hr ha hw
  | n + 1, j, fuel, hj => by
    rw [show fuel + 2 * (n + 1) + 6 = (fuel + 2 * n + 6) + 1 + 1 by omega]
    exact treeSimCheck_halvRest_succ prims K D Ad step q width n j _ ha
      (treeSimCheck_halvRest_all prims K D Ad step q width hr ha hw n (j + 1) fuel (by omega))


def TreeSimCheckSliceRest [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q count n j F : ℕ) : Prop :=
  ∀ (st : Ad.State) (live : C.Party → Prop) [DecidablePred live]
    (hs : C.Party → RunState C) (tag L : ℕ),
    (∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L) →
    ∀ (xs ys : C.Party → Shares C E) (V : C.Party → E),
    interpolate K D.1 V 0 ≠ ∑ k ∈ Finset.range (sliceLen count j), sliceWeight τ count j k *
      interpolate K D.1 (fun i => conv K (localContext i) (xs i) k) 0 *
      interpolate K D.1 (fun i => conv K (localContext i) (ys i) k) 0 →
    ∀ (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    SoundCache L cache seen keys → TreeSimCheckPriorKeys L cache keys →
    seen.card + (2 * (n + halvingSteps (sliceWidth count)) + 4) * step ≤ q →
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D Ad (checkFunctionalities K) F st
          (fun i => if live i then (sliceProg K τ count n j (xs i) (ys i) (V i) i).run' (hs i)
            else failure))).run cache] ≤ (n + halvingSteps (sliceWidth count) + 1 : ℕ) * treeSimCheckError E q 2

set_option maxHeartbeats 500000 in
theorem treeSimCheck_sliceRest_zero [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q count fuel : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count) :
    TreeSimCheckSliceRest prims K D Ad τ step q count 0 sliceBits
      (fuel + 2 * halvingSteps (sliceWidth count) + 6) := by
  intro st live _ hs tag L htag xs ys V hwrong cache seen keys hc prior hq
  simp only [sliceLen, sliceWeight, Nat.sub_self, pow_zero, mul_one, coinProduct, Finset.range_zero,
    Finset.prod_empty, one_mul] at hwrong
  simp only [sliceProg_zero]
  simpa only [Nat.zero_add] using treeSimCheck_halvRest_all prims K D Ad step q (sliceWidth count) hr ha hw
    (halvingSteps (sliceWidth count)) 0 fuel (by omega) st live hs tag L htag
    (fun i => conv K (localContext i) (xs i)) (fun i => conv K (localContext i) (ys i)) V
    hwrong cache seen keys hc prior (by simpa only [Nat.zero_add] using hq)

set_option maxHeartbeats 500000 in
theorem treeSimCheck_sliceRest_succ [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q count n j F : ℕ)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step)
    (hw : 0 < sliceWidth count) (hj : j < sliceBits) (hτ : τ.getD (sliceBits - 1 - j) 0 ≠ 0)
    (hIH : TreeSimCheckSliceRest prims K D Ad τ step q count n (j + 1) F) :
    TreeSimCheckSliceRest prims K D Ad τ step q count (n + 1) j (F + 1 + 1) := by
  intro st live _ hs tag L htag xs ys V hwrong cache seen keys hc prior hq
  by_cases hall : ∀ i, i ∉ D.1 → live i
  swap
  · rw [sliceExtend_missing K D Ad _ st live hall hs τ count n j xs ys V]
    simp
  rw [sliceExtend_local K D Ad _ st live hall hs τ count n j xs ys V]
  apply treeSimCheck_prefix prims _ _ step (sound_extendReply_bound Ad step ha _ _) L cache seen keys hc prior
  intro pa cache1 seen1 hc1 prior1 hn1
  apply treeSimCheck_sample prims
  intro fresh
  rw [sliceAfter_form]
  by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
  swap
  · rw [executePhase_challenge_live, if_neg hrec]
    simp
  let q0 := fun i => conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 0
  let qInf := fun i => conv K (localContext i) (sliceOut K D τ count j xs ys pa fresh i) 1
  let bad := fun r : E =>
    interpolate K D.1 (fun i => sliceClaim τ j r (V i) (q0 i) (qInf i)) 0 =
      ∑ k ∈ Finset.range (sliceLen count (j + 1)), sliceWeight τ count (j + 1) k *
        interpolate K D.1 (fun i => conv K (localContext i) (sliceFold count j r (xs i)) k) 0 *
        interpolate K D.1 (fun i => conv K (localContext i) (sliceFold count j r (ys i)) k) 0
  have hcard : (Finset.univ.filter bad).card ≤ 2 := sound_sliceFold_card K D τ count j hw hj xs ys V q0 qInf hτ hwrong
  let hs1 : C.Party → RunState C := fun i =>
    ⟨recordHistory K i (hs i).history (sliceOut K D τ count j xs ys pa fresh i) 2,
      (hs i).label + 1, (hs i).tag⟩
  let g := sliceCont K τ count n j xs ys V (sliceOut K D τ count j xs ys pa fresh)
  apply le_trans (treeSimCheck_challenge_phase prims K D Ad F step ha pa.1
    (fun i => i ∈ pa.2.2.2.2) hrec hs1 tag (L + 1)
    (fun i hi => by simp [hs1, htag i hi]) g cache1 seen1 keys (hc1.mono_label (by omega)) (prior1.mono (by omega) le_rfl)
    bad 2 (by convert hcard using 1; congr 2)
    ((n + halvingSteps (sliceWidth count) + 1 : ℕ) * treeSimCheckError E q 2) ?_) ?_
  · intro p r key cache' seen' hc' prior' hn' hgood
    unfold soundChallengeNext
    apply hIH p.1 (fun i => i ∈ p.2) _ tag ((L + 1) + 1)
      (fun i hi => by simp [hs1, htag i hi])
    · exact hgood
    · exact hc'
    · exact prior'
    · simp only [Nat.add_mul, Nat.mul_add] at hq ⊢
      omega
  · have hcard : seen1.card ≤ q := by
      simp only [Nat.add_mul, Nat.mul_add] at hq
      omega
    calc
      _ = (seen1.card / Fintype.card E + 2 / (Fintype.card E - 2 : ℕ)) +
          (n + halvingSteps (sliceWidth count) + 1 : ℕ) * treeSimCheckError E q 2 := by
            simp only [Nat.cast_ofNat, add_assoc]
      _ ≤ treeSimCheckError E q 2 +
          (n + halvingSteps (sliceWidth count) + 1 : ℕ) * treeSimCheckError E q 2 := by
        unfold treeSimCheckError
        simp only [Nat.cast_ofNat]
        gcongr
      _ = _ := by push_cast; ring


set_option maxHeartbeats 500000 in
theorem treeSimCheck_sliceRest_all [SampleableType E] {Ia : Type} (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (step q count : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (Ad.round st sent) Counted step)
    (ha : ∀ st l, IsQueryBoundP (Ad.answer st l) Counted step) (hw : 0 < sliceWidth count)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0) :
    ∀ n j fuel, j + n = sliceBits → TreeSimCheckSliceRest prims K D Ad τ step q count n j
      (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6)
  | 0, j, fuel, hj => by
    have hj' : j = sliceBits := by omega
    subst j
    simpa only [Nat.zero_add] using treeSimCheck_sliceRest_zero prims K D Ad τ step q count fuel hr ha hw
  | n + 1, j, fuel, hj => by
    rw [show fuel + 2 * (n + 1 + halvingSteps (sliceWidth count)) + 6 =
      (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6) + 1 + 1 by omega]
    exact treeSimCheck_sliceRest_succ prims K D Ad τ step q count n j _ ha hw (by omega)
      (hτ _ (by omega))
      (treeSimCheck_sliceRest_all prims K D Ad τ step q count hr ha hw hτ n (j + 1) fuel (by omega))


theorem treeSimCheck_start_boundary [SampleableType E] {α : Type}
    (tag L d : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (bad : List E → Prop) (δ : ℝ≥0∞)
    (hbad : Pr[fun v : Fin d → E => bad (List.ofFn v) | $ᵗ (Fin d → E)] ≤ δ)
    (cont : E → List E → OracleComp (LocalSpec C) α)
    (accept : α × HashCache C → Prop) (ε : ℝ≥0∞)
    (hnext : ∀ r τ key cache', SoundCache (L + 1) cache' seen (insert key keys) →
      TreeSimCheckPriorKeys (L + 1) cache' (insert key keys) → ¬ bad τ →
      Pr[fun p => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p |
        (simulateQ (localAnswer prims) (cont r τ)).run cache'] ≤ ε) :
    Pr[fun p => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p | (do
      let r ← $ᵗ E
      let p ← (simulateQ (localAnswer prims)
        (liftComp (startQuery K tag L [r] d) (LocalSpec C))).run cache
      (simulateQ (localAnswer prims) (cont r p.1)).run p.2)] ≤
      seen.card / Fintype.card E + (δ + ε) := by
  simp only [startQuery, liftComp_bind, simulateQ_bind, StateT.run_bind, bind_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  let expandKey := fun key : HashOutput =>
    (List.range d).mapM fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)
  have hb := treeSimCheck_coin_boundary prims K tag L L le_rfl cache seen keys hc prior
    (fun r key => liftComp (expandKey key) (LocalSpec C) >>= cont r)
    accept (δ + ε) ?_
  · simpa only [expandKey, simulateQ_bind, StateT.run_bind, simulateQ_localAnswer_liftComp] using hb
  · intro r key hkey hfresh
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_localAnswer_liftComp]
    have he := sound_expand_uniform prims K key.1 d 0 key.2 (fun i _ => hfresh i)
    rw [← List.range_eq_range'] at he
    have hbad' : Pr[fun p => bad p.1 |
        (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (expandKey key.1)).run key.2] ≤ δ := by
      have hu : Pr[bad |
          (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (expandKey key.1)).run' key.2] ≤ δ := by
        rw [probEvent_def, he, ← probEvent_def, probEvent_map]
        exact hbad
      simpa only [StateT.run'_eq, probEvent_map, Function.comp_def] using hu
    have hh := probEvent_bind_le_add
      (mx := (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (expandKey key.1)).run key.2)
      (my := fun p => (simulateQ (localAnswer prims) (cont r p.1)).run p.2)
      (p := fun p => ¬ bad p.1)
      (q := fun p => ¬ (¬ CacheHasCollision (splitRegionCache TreeSimHashDomain p.2) ∧ accept p))
      (ε₂ := ε)
      (by simpa using hbad') (fun p hp hgood => ?_)
    · simpa only [not_not] using hh
    · simp only [not_not]
      have hgrows : key.2 ≤ p.2 := (grows_localAnswer prims).simulateQ
        (liftComp (expandKey key.1) (LocalSpec C)) key.2 p
        (by simpa only [simulateQ_localAnswer_liftComp] using hp)
      have hinv := treeSimCheck_cache_after_coin prims K hc prior (tag := tag) le_rfl [r] key
        (by simpa only [simulateQ_localAnswer_liftComp, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] using hkey) p.2 hgrows
        (support_expand_entries prims K key.1 _ _ _ hp)
      exact hnext r p.1 key.1 p.2 hinv.1 hinv.2 hgood

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_start_phase [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel step d : ℕ)
    (ha : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
    (st : A.State) (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → List E → RunM C E (CheckSpec C E) Unit)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (bad : List E → Prop) (δ : ℝ≥0∞)
    (hbad : Pr[fun v : Fin d → E => bad (List.ofFn v) | $ᵗ (Fin d → E)] ≤ δ) (ε : ℝ≥0∞)
    (hnext : ∀ p τ key cache' seen', SoundCache (L + 1) cache' seen' (insert key keys) →
      TreeSimCheckPriorKeys (L + 1) cache' (insert key keys) →
      seen'.card ≤ seen.card + step → ¬ bad τ →
      Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
        ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
        (simulateQ (localAnswer prims) (soundStartNext K D A fuel hs g p τ)).run cache'] ≤ ε) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
          (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key d) >>= g i).run' (hs i)))).run cache] ≤
      seen.card / Fintype.card E + (δ + ε) := by
  rw [treeSimCheck_start_normalize prims K D A fuel d st hs tag L htag g cache _ (fun r hr => hr.2)]
  let next := fun v : List E => do
    let p ← (simulateQ (localAnswer prims)
      (liftComp (startQuery K tag L v d) (LocalSpec C))).run cache
    let ans ← (simulateQ (localAnswer prims)
      ((leftAdversary (leftAdversary A)).answer st v)).run p.2
    (simulateQ (localAnswer prims) (soundStartNext K D A fuel hs g ans.1 p.1)).run ans.2
  suffices hb : Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
    ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (do let v ← $ᵗ (Fin (firstInput fun i : C.Party => if i ∈ D.1 then
        (none : Option ℕ) else some 1) → E); next (List.ofFn v))] ≤
      seen.card / Fintype.card E + (δ + ε) by
    simpa only [next, simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left] using hb
  rw [probEvent_def, treeSimCheck_uniform_one _ (firstInput_honest_const D 1) next, ← probEvent_def]
  dsimp only [next]
  have hb := treeSimCheck_start_boundary prims K tag L d cache seen keys hc prior bad δ hbad
    (fun v τ => (leftAdversary (leftAdversary A)).answer st [v] >>=
      fun p => soundStartNext K D A fuel hs g p τ)
    (fun out => ∃ i, i ∉ D.1 ∧ out.1.2 i = some ()) ε ?_
  · simpa only [simulateQ_bind, StateT.run_bind] using hb
  · intro v τ key cache' hc' prior' hgood
    simp only [simulateQ_bind, StateT.run_bind]
    apply probEvent_bind_le_of_forall_le
    intro ans hans
    have hans' : ans ∈ support ((simulateQ (localAnswer prims)
        ((leftAdversary (leftAdversary A)).answer st [v])).run cache') := by
      simpa only [simulateQ_bind, StateT.run_bind] using hans
    obtain ⟨seen', hcache', hcard'⟩ := hc'.local prims
      ((leftAdversary (leftAdversary A)).answer st [v]) step
      (sound_coinReply_bound A step ha st _) ans hans'
    exact hnext ans.1 τ key ans.2 seen' hcache'
      (prior'.mono le_rfl ((grows_localAnswer prims).simulateQ _ _ _ hans')) hcard' hgood

private theorem treeSimCheckError_ne_top (K : Constants C E) (q m : ℕ) : treeSimCheckError E q m ≠ ⊤ := by
  have hE : 2 < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  have h0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E ≠ 0)
  have h2 : ((Fintype.card E - 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E - 2 ≠ 0)
  unfold treeSimCheckError
  finiteness

private theorem treeSimCheckError_toReal (K : Constants C E) (q m : ℕ) :
    (treeSimCheckError E q m).toReal =
      (q : ℝ) / Fintype.card E + (m : ℝ) / (Fintype.card E - 2 : ℝ) := by
  have hE : 2 < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  have h0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E ≠ 0)
  have h2 : ((Fintype.card E - 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : Fintype.card E - 2 ≠ 0)
  unfold treeSimCheckError
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    Nat.cast_sub (by omega : 2 ≤ Fintype.card E), Nat.cast_ofNat]

theorem treeSimCheck_error_sum [SampleableType E] (K : Constants C E) (d R q : ℕ) :
    treeSimCheckError E q d + (R + 1 : ℕ) * treeSimCheckError E q 2 =
      ENNReal.ofReal (checkErrorOf (E := E) d R q) := by
  have hnonneg := checkErrorOf_nonneg K d R q
  apply (ENNReal.toReal_eq_toReal_iff' (by
    exact ENNReal.add_ne_top.mpr ⟨treeSimCheckError_ne_top K _ _,
      ENNReal.mul_ne_top (by simp) (treeSimCheckError_ne_top K _ _)⟩) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add (treeSimCheckError_ne_top K _ _)
      (ENNReal.mul_ne_top (by simp) (treeSimCheckError_ne_top K _ _)),
    ENNReal.toReal_mul, treeSimCheckError_toReal K, treeSimCheckError_toReal K,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hnonneg]
  unfold checkErrorOf
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- The complete GS20 check from an arbitrary shared cache and common label.
Only the fixed algebraic error is charged on collision-free accepted runs. -/
theorem treeSimCheck_roundInduction [SampleableType E]
    (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (step q : ℕ) (st : A.State)
    (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hx : TupleInputs K counts D x) (hpos : counts.sum ≠ 0)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (ha : ∀ state l, IsQueryBoundP (A.answer state l) Counted step)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (hb : seen.card + (2 * halvings counts.sum + 5) * step ≤ q)
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)))
    (hwrong : ∃ m < (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length,
      ∃ g < (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count,
        shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z g -
          shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x g *
            shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y g ≠ 0) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' (hs i)))).run cache] ≤
      ENNReal.ofReal (checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q) := by
  let F := 1 + 2 * (sliceBits + halvingSteps (sliceWidth counts.sum)) + 6
  let g : C.Party → List E → RunM C E (CheckSpec C E) Unit := fun i τ => do
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
    sliceProg K τ counts.sum sliceBits 0 (fun T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k)
      (liftedPart (x i) (·.y)) (conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0) i
  let bad := soundInitialBad K D counts.sum (fun i => liftedPart (x i) (·.x))
    (fun i => liftedPart (x i) (·.y)) (fun i => liftedPart (x i) (·.z))
  have hF : checkRounds counts.sum = F + 1 := by unfold F checkRounds halvings; omega
  rw [hF]
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) (F + 1) st
      (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key (coins counts.sum)) >>= g i).run'
        (hs i)))).run cache] ≤ _
  apply le_trans (treeSimCheck_start_phase prims K D A F step (coins counts.sum) ha st hs tag L
    htag g cache seen keys hc prior bad
    ((coins counts.sum : ℝ≥0∞) / (Fintype.card E - 2 : ℕ))
    (sound_initial_weights K counts D x hx hpos hagree hwrong)
    ((halvings counts.sum + 1 : ℕ) * treeSimCheckError E q 2) ?_) ?_
  · intro p τ key cache' seen' hc' prior' hn' hgood
    unfold soundStartNext
    simp only [g, require_bind_run']
    by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [if_pos hτ]
      apply treeSimCheck_sliceRest_all prims K D A τ step q counts.sum hr ha (sliceWidth_pos hpos) hτ
        sliceBits 0 1 (by omega) p.1 (fun i => i ∈ p.2)
        (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) tag (L + 1)
        (fun i hi => by simp [htag i hi])
      · exact hgood
      · exact hc'
      · exact prior'
      · simp only [checkRounds, halvings, Nat.add_mul, Nat.mul_add] at hb ⊢
        omega
    · simp only [if_neg hτ, ite_self, executePhase_failure]
      simp
  · have hcard : seen.card ≤ q := by omega
    calc
      _ ≤ treeSimCheckError E q (coins counts.sum) +
          (halvings counts.sum + 1 : ℕ) * treeSimCheckError E q 2 := by
        unfold treeSimCheckError
        rw [← add_assoc]
        gcongr
      _ = _ := treeSimCheck_error_sum K (coins counts.sum) (halvings counts.sum) q

private theorem treeSimCheck_split_region (cache : HashCache C)
    (hno : ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain cache)) :
    ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache) := by
  rintro ⟨q, r, u, v, hne, hq, hr, huv⟩
  have entry : ∀ q u, splitRegionCache SplitHashDomain cache q = some u →
      splitRegionCache TreeSimHashDomain cache q = some u := by
    intro q u he
    cases q <;> simp_all [splitRegionCache, SplitHashDomain, TreeSimHashDomain]
  exact hno ⟨q, r, u, v, hne, entry q u hq, entry r v hr, huv⟩

private theorem treeSimCheck_columns_evidence
    (D : C.Coalition) (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit) :
    ∀ (Ts : List C.Term) (cache : HashCache C) (p : (C.Party → List HashOutput) × HashCache C),
      p ∈ support ((simulateQ (localAnswer prims)
        (queryColumns (fun i T => honestDigestColumn D T salts hist i) Ts)).run cache) →
      ∀ (k : ℕ) T, Ts[k]? = some T → ∀ i, i ∉ D.1 → i ∈ C.holders T → ∃ h d,
        p.2 (.history (hist i T)) = some h ∧
        p.2 (.digest (vector 256 (salts i T)) h) = some d ∧ (p.1 i)[k]? = some d := by
  intro Ts
  induction Ts with
  | nil => intro cache p hp k T hk; simp at hk
  | cons T Ts ih =>
    intro cache p hp k U hk i hi hiU
    simp only [queryColumns, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
    obtain ⟨head, hhead, tail, htail, hp⟩ := hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst U
      obtain ⟨h, hh, hd⟩ := (split_column_support prims D T salts hist cache head hhead).2 i hi hiU
      have hgrows := (grows_localAnswer prims).simulateQ _ _ _ htail
      exact ⟨h, head.1 i, hgrows hh, hgrows hd, rfl⟩
    | succ k =>
      exact ih head.2 tail htail k U hk i hi hiU

set_option maxHeartbeats 1000000 in
/-- Split histories have zero accepted probability outside the fixed
collision region, for every adaptive continuation and starting cache. -/
theorem treeSimCheck_split_digest_zero [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (hs : C.Party → RunState C) (salts : C.Party → Shares C Bit)
    (split : SplitHistories D (fun i => (hs i).history))
    (next : C.Party → Unit → RunM C E (CheckSpec C E) Unit) (cache : HashCache C) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
          (fun i => (compareDigests (localContext i) (salts i) >>= next i).run' (hs i)))).run cache] = 0 := by
  have he := executePhase_digestColumns prims K D A (fuel + 1) st salts hs next
  rw [probEvent_def, he cache, ← probEvent_def]
  simp only [simulateQ_bind, StateT.run_bind]
  apply le_antisymm _ bot_le
  apply probEvent_bind_le_of_forall_le
  intro ds hds
  by_cases hbad : CacheHasCollision (splitRegionCache TreeSimHashDomain ds.2)
  · apply le_of_eq
    apply probEvent_eq_zero
    intro out hout ho
    exact ho.1 (treeSimCheck_domain_collision_mono
      ((grows_localAnswer prims).simulateQ _ _ _ hout) hbad)
  · have hstop : ∀ sent i, i ∉ D.1 → ¬ digestLive (E := E) D ds.1 sent i := by
      intro sent i hi
      apply splitHistories_abort_region D _ split ds.2 (treeSimCheck_split_region ds.2 hbad) ds.1 _ sent i
      intro j hj T _ hjT
      obtain ⟨h, d, hh, hd, he⟩ := treeSimCheck_columns_evidence prims D salts
        (fun i => (hs i).history) C.terms cache ds hds (C.terms.idxOf T) T
        (by rw [List.getElem?_eq_getElem (idxOf_terms_lt T), List.getElem_idxOf]) j hj hjT
      exact ⟨vector 256 (salts j T), h, d, hh, hd, he⟩
    rw [split_afterDigests_abort K D A fuel st ds.1 _ hstop]
    simp only [simulateQ_bind, StateT.run_bind]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    simp

private theorem treeSimCheck_all_prefix {α β : Type}
    (oa : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β)
    (cache : HashCache C) (accept : β × HashCache C → Prop) (ε : ℝ≥0∞)
    (h : ∀ a cache', Pr[accept | (simulateQ (localAnswer prims) (f a)).run cache'] ≤ ε) :
    Pr[accept | (simulateQ (localAnswer prims) (oa >>= f)).run cache] ≤ ε := by
  simp only [simulateQ_bind, StateT.run_bind]
  exact probEvent_bind_le_of_forall_le (fun p _ => h p.1 p.2)

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_split_salt_zero [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (hs : C.Party → RunState C) (split : SplitHistories D (fun i => (hs i).history))
    (next : C.Party → Unit → RunM C E (CheckSpec C E) Unit) (cache : HashCache C) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) ((fuel + 1) + 1) st
          (fun i => ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
            compareDigests (localContext i) salts.1 >>= next i).run' (hs i)))).run cache] = 0 := by
  have he := executePhase_randBits_first prims K D A (fuel + 1) st 256 hs
    (fun i salts => compareDigests (localContext i) salts >>= next i)
  rw [probEvent_def, he cache, ← probEvent_def]
  apply le_antisymm _ bot_le
  apply treeSimCheck_all_prefix prims
  intro p cache'
  apply treeSimCheck_sample prims
  intro fresh
  exact le_of_eq (treeSimCheck_split_digest_zero prims K D A fuel p.1
    (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) _ split next cache')

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_split_final_zero [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (live : C.Party → Prop) [DecidablePred live] (hs : C.Party → RunState C)
    (split : SplitHistories D (fun i => (hs i).history))
    (Av Bv : C.Party → ℕ → E) (V : C.Party → E) (cache : HashCache C) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 6) st
          (fun i => if live i then
            (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i)
            else failure))).run cache] = 0 := by
  by_cases hall : ∀ i, i ∉ D.1 → live i
  · rw [executePhase_congr_honest D A _ _ st _
      (fun i => (finalStep K (localContext i) (hybridCheckGadgets K i) (Av i, Bv i, V i)).run' (hs i))
      (fun i hi => if_pos (hall i hi))]
    have he := finalStep_masks prims K D A (fuel + 4) st Av Bv V hs
    rw [probEvent_def, he cache, ← probEvent_def]
    apply le_antisymm _ bot_le
    apply treeSimCheck_all_prefix prims
    intro p cache1
    apply treeSimCheck_all_prefix prims
    intro pa cache2
    apply treeSimCheck_sample prims
    intro w
    apply treeSimCheck_sample prims
    intro z
    by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
    · rw [finalMasked_all K D A _ _ _ _ _ _ _ _ _ _ _ _ _ hrec]
      apply le_of_eq
      apply treeSimCheck_split_salt_zero prims K D A (fuel + 2)
      exact split.record K D _ 2
    · rw [show fuel + 4 = (fuel + 3) + 1 by omega,
        finalMasked_missing K D A _ _ _ _ _ _ _ _ _ _ _ _ _ (by push Not at hrec; exact hrec)]
      simp
  · rw [show fuel + 6 = (fuel + 5) + 1 by omega,
      finalStep_missing K D A _ _ _ _ _ _ _ (by push Not at hall; exact hall)]
    simp

set_option maxHeartbeats 1000000 in
private theorem treeSimCheck_challenge_zero [SampleableType E] {Ia : Type} (D : C.Coalition)
    (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (live : C.Party → Prop) [DecidablePred live] (hall : ∀ i, i ∉ D.1 → live i)
    (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (g : C.Party → E → RunM C E (CheckSpec C E) Unit) (cache : HashCache C)
    (hnext : ∀ p r cache',
      Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
        ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
        (simulateQ (localAnswer prims) (soundChallengeNext K D A fuel hs g p (some r))).run cache'] = 0) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (fuel + 1) st
          (fun i => if live i then (challenge K (hybridCheckGadgets K i) >>= g i).run' (hs i)
            else failure))).run cache] = 0 := by
  rw [treeSimCheck_challenge_normalize prims K D A fuel st live hall hs tag L htag g cache _
    (fun r hr => hr.2)]
  apply le_antisymm _ bot_le
  apply treeSimCheck_all_prefix prims
  intro v cache1
  apply treeSimCheck_all_prefix prims
  intro r cache2
  apply treeSimCheck_all_prefix prims
  intro p cache3
  cases r with
  | none => simp [soundChallengeNext_none]
  | some r => exact le_of_eq (hnext p r cache3)

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_split_halv_zero [SampleableType E] {Ia : Type}
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (width : ℕ) :
    ∀ (n j fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live]
      (hs : C.Party → RunState C) (tag L : ℕ),
      (∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L) →
      SplitHistories D (fun i => (hs i).history) →
      ∀ (A B : C.Party → ℕ → E) (V : C.Party → E) (cache : HashCache C),
      Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
        ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
        (simulateQ (localAnswer prims)
          (executePhase localRoles D Ad (checkFunctionalities K) (fuel + 2 * n + 6) st
            (fun i => if live i then (halvProg K width n j (A i) (B i) (V i) i).run' (hs i)
              else failure))).run cache] = 0
  | 0, j, fuel, st, live, _, hs, tag, L, htag, split, A, B, V, cache => by
    simpa only [Nat.mul_zero, Nat.add_zero, halvProg_zero] using
      treeSimCheck_split_final_zero prims K D Ad fuel st live hs split A B V cache
  | n + 1, j, fuel, st, live, _, hs, tag, L, htag, split, A, B, V, cache => by
    rw [show fuel + 2 * (n + 1) + 6 = (fuel + 2 * n + 6) + 1 + 1 by omega]
    by_cases hall : ∀ i, i ∉ D.1 → live i
    swap
    · rw [halvExtend_missing K D Ad _ st live hall hs width n j A B V]
      simp
    rw [halvExtend_local K D Ad _ st live hall hs width n j A B V]
    apply le_antisymm _ bot_le
    apply treeSimCheck_all_prefix prims
    intro pa cache1
    apply treeSimCheck_sample prims
    intro fresh
    rw [halvAfter_form]
    by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
    swap
    · rw [executePhase_challenge_live, if_neg hrec]
      simp
    let hs1 : C.Party → RunState C := fun i =>
      ⟨recordHistory K i (hs i).history (halvOut K D (halvedLength^[j] width) A B pa fresh i) 2,
        (hs i).label + 1, (hs i).tag⟩
    apply le_of_eq
    apply treeSimCheck_challenge_zero prims K D Ad (fuel + 2 * n + 6) pa.1
      (fun i => i ∈ pa.2.2.2.2) hrec hs1 tag (L + 1)
      (fun i hi => by simp [hs1, htag i hi])
    intro p r cache'
    unfold soundChallengeNext
    apply treeSimCheck_split_halv_zero D Ad width n (j + 1) fuel
      p.1 (fun i => i ∈ p.2) _ tag ((L + 1) + 1)
      (fun i hi => by simp [hs1, htag i hi])
    exact split.record K D _ 2

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_split_slice_zero [SampleableType E] {Ia : Type}
    (D : C.Coalition) (Ad : CheckAdversary C E Ia) (τ : List E) (count : ℕ) :
    ∀ (n j fuel : ℕ) (st : Ad.State) (live : C.Party → Prop) [DecidablePred live]
      (hs : C.Party → RunState C) (tag L : ℕ),
      (∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L) →
      SplitHistories D (fun i => (hs i).history) →
      ∀ (xs ys : C.Party → Shares C E) (V : C.Party → E) (cache : HashCache C),
      Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
        ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
        (simulateQ (localAnswer prims)
          (executePhase localRoles D Ad (checkFunctionalities K)
            (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6) st
            (fun i => if live i then (sliceProg K τ count n j (xs i) (ys i) (V i) i).run' (hs i)
              else failure))).run cache] = 0
  | 0, j, fuel, st, live, _, hs, tag, L, htag, split, xs, ys, V, cache => by
    simp only [Nat.zero_add, sliceProg_zero]
    exact treeSimCheck_split_halv_zero prims K D Ad (sliceWidth count)
      (halvingSteps (sliceWidth count)) 0 fuel st live hs tag L htag split _ _ V cache
  | n + 1, j, fuel, st, live, _, hs, tag, L, htag, split, xs, ys, V, cache => by
    rw [show fuel + 2 * (n + 1 + halvingSteps (sliceWidth count)) + 6 =
      (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6) + 1 + 1 by omega]
    by_cases hall : ∀ i, i ∉ D.1 → live i
    swap
    · rw [sliceExtend_missing K D Ad _ st live hall hs τ count n j xs ys V]
      simp
    rw [sliceExtend_local K D Ad _ st live hall hs τ count n j xs ys V]
    apply le_antisymm _ bot_le
    apply treeSimCheck_all_prefix prims
    intro pa cache1
    apply treeSimCheck_sample prims
    intro fresh
    rw [sliceAfter_form]
    by_cases hrec : ∀ i, i ∉ D.1 → i ∈ pa.2.2.2.2
    swap
    · rw [executePhase_challenge_live, if_neg hrec]
      simp
    let hs1 : C.Party → RunState C := fun i =>
      ⟨recordHistory K i (hs i).history (sliceOut K D τ count j xs ys pa fresh i) 2,
        (hs i).label + 1, (hs i).tag⟩
    apply le_of_eq
    apply treeSimCheck_challenge_zero prims K D Ad
      (fuel + 2 * (n + halvingSteps (sliceWidth count)) + 6) pa.1
      (fun i => i ∈ pa.2.2.2.2) hrec hs1 tag (L + 1)
      (fun i hi => by simp [hs1, htag i hi])
    intro p r cache'
    unfold soundChallengeNext
    apply treeSimCheck_split_slice_zero D Ad τ count n (j + 1) fuel
      p.1 (fun i => i ∈ p.2) _ tag ((L + 1) + 1)
      (fun i hi => by simp [hs1, htag i hi])
    exact split.record K D _ 2

set_option maxHeartbeats 1000000 in
theorem treeSimCheck_split_start_zero [SampleableType E] {Ia : Type}
    (D : C.Coalition) (A : CheckAdversary C E Ia) (count : ℕ) (st : A.State)
    (hs : C.Party → RunState C) (tag L : ℕ)
    (htag : ∀ i, i ∉ D.1 → (hs i).tag = tag ∧ (hs i).label = L)
    (split : SplitHistories D (fun i => (hs i).history))
    (xs ys zs : C.Party → Shares C E) (cache : HashCache C) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds count) st
          (fun i => (startProg K count (xs i) (ys i) (zs i) i).run' (hs i)))).run cache] = 0 := by
  let F := 1 + 2 * (sliceBits + halvingSteps (sliceWidth count)) + 6
  let g : C.Party → List E → RunM C E (CheckSpec C E) Unit := fun i τ => do
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
    sliceProg K τ count sliceBits 0 (fun T k => wordWeightOf K τ count k * xs i T k)
      (ys i) (conv K (localContext i) (claimOf K τ count (zs i)) 0) i
  have hF : checkRounds count = F + 1 := by unfold F checkRounds halvings; omega
  rw [hF]
  change Pr[_ | (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) (F + 1) st
      (fun i => ((coinKey K (hybridCheckGadgets K i) >>= fun key => expand K key (coins count)) >>= g i).run'
        (hs i)))).run cache] = 0
  rw [treeSimCheck_start_normalize prims K D A F (coins count) st hs tag L htag g cache _
    (fun r hr => hr.2)]
  apply le_antisymm _ bot_le
  apply treeSimCheck_all_prefix prims
  intro v cache1
  apply treeSimCheck_all_prefix prims
  intro τ cache2
  apply treeSimCheck_all_prefix prims
  intro p cache3
  unfold soundStartNext
  simp only [g, require_bind_run']
  by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
  · simp only [if_pos hτ]
    apply le_of_eq
    exact treeSimCheck_split_slice_zero prims K D A τ count sliceBits 0 1 p.1
      (fun i => i ∈ p.2)
      (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) tag (L + 1)
      (fun i hi => by simp [htag i hi]) split _ _ _ cache3
  · simp only [if_neg hτ, ite_self, executePhase_failure]
    simp

set_option maxHeartbeats 1000000 in
/-- Contextual soundness for arbitrary valid tuples, including split copies.
The event records the final cache, so it can be restricted by the tree's fixed
hash event without paying a second hash error. -/
theorem treeSimCheck_contextual [SampleableType E]
    (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (step q : ℕ) (st : A.State)
    (tag L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hx : TupleInputs K counts D x) (hpos : counts.sum ≠ 0)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (ha : ∀ state l, IsQueryBoundP (A.answer state l) Counted step)
    (hc : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (hb : seen.card + (2 * halvings counts.sum + 5) * step ≤ q)
    (hreject : ¬ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some (x i))).2.2) :
    Pr[fun out => ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧
      ∃ i, i ∉ D.1 ∧ out.1.2 i = some () |
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (check K (localContext i) (hybridCheckGadgets K i) (x i)).run'
            ⟨filledHistory K i (x i), L, tag⟩))).run cache] ≤
      ENNReal.ofReal (checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q) := by
  rw [executePhase_congr_honest D A _ _ st _
    (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
      (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), L, tag⟩)
    (fun i hi => by rw [check_startProg K i (x i) (by rw [hx.1 i hi]; exact hpos), hx.1 i hi])]
  by_cases hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))
  · exact treeSimCheck_roundInduction prims K counts D A x step q st _ tag L
      (fun _ _ => ⟨rfl, rfl⟩) cache seen keys hx hpos hr ha hc prior hb hagree
      (multVerify_reject_wrong_tuple D _ hagree (Bool.eq_false_iff.mpr hreject))
  · rw [treeSimCheck_split_start_zero prims K D A counts.sum st _ tag L
      (fun _ _ => ⟨rfl, rfl⟩) (splitInit_histories K counts D x hx hagree)]
    exact bot_le

/-- Initial GS20 weights in a shared cache, with the same counted coin
budget as the later quadratic challenges and no collision term. -/
theorem treeSimCheck_start_contextual [SampleableType E] {β : Type}
    (tag label L d : ℕ) (hL : L ≤ label) (cache : HashCache C)
    (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hc : SoundCache L cache seen keys) (bad : List E → Prop) (δ : ℝ≥0∞)
    (hbad : Pr[fun v : Fin d → E => bad (List.ofFn v) | $ᵗ (Fin d → E)] ≤ δ)
    (cont : E → HashOutput → List E × HashCache C → ProbComp β)
    (accept : β → Prop) (ε : ℝ≥0∞)
    (hcollision : ∀ r key p, key ∈ keys → Pr[accept | cont r key p] = 0)
    (hnext : ∀ r key p, ¬ bad p.1 → Pr[accept | cont r key p] ≤ ε) :
    Pr[accept | (do
      let r ← $ᵗ E
      let key ← (simulateQ (localAnswer prims)
        (liftComp (hashQuery (C := C) (.coinKey tag label (List.ofFn (K.encode r))))
          (LocalSpec C))).run cache
      let p ← (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        ((List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand key.1 k))).run key.2
      cont r key.1 p)] ≤ seen.card / Fintype.card E + (δ + ε) := by
  apply treeSimCheck_coinKey_contextual prims K tag label L hL cache seen keys hc
    (fun r key cache' => (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      ((List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run cache' >>=
        cont r key) accept (δ + ε)
  · intro r key hkey hk
    apply le_antisymm _ bot_le
    apply probEvent_bind_le_of_forall_le
    intro p _
    exact le_of_eq (hcollision r key.1 p hk)
  · rintro r ⟨key, cache'⟩ hkey hfresh
    have he := sound_expand_uniform prims K key d 0 cache' (fun i _ => hfresh i)
    rw [← List.range_eq_range'] at he
    have hb : Pr[fun p => bad p.1 | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        ((List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run cache'] ≤ δ := by
      have hu : Pr[bad | (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
          ((List.range d).mapM fun k => elementOfHash K <$> hashQuery (.expand key k))).run' cache'] ≤ δ := by
        rw [probEvent_def, he, ← probEvent_def, probEvent_map]
        exact hbad
      simpa only [StateT.run'_eq, probEvent_map, Function.comp_def] using hu
    have hh := probEvent_bind_le_add (my := cont r key)
      (p := fun p => ¬ bad p.1) (q := fun out => ¬ accept out)
      (by simpa using hb) (fun p _ hp => by simpa using hnext r key p hp)
    simpa using hh

/-- The semantic cover and the batch union are discharged. Only the
probability estimate for each fixed actual indexed event remains here. -/
theorem treeSimCheckBound_of_indexedBounds
    (indexedBounds : 0 < settings.batchSize →
      ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
        (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
        (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
        DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
        ∀ j : Fin (treeBatches settings tree),
          Pr[fun r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
            treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
          ENNReal.ofReal (checkErrorOf (E := E)
            (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
            (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q)) :
    TreeSimCheckBoundGoal prims K circuits settings := by
  letI : SampleableType E := SampleableType.ofFintype E
  intro hbatch top tree D A x z Z q hx hq hsmall
  let ε := checkErrorOf (E := E)
    (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
    (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q
  have sumBound : (∑ j : Fin (treeBatches settings tree),
      Pr[fun r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
        treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)]) ≤
      (treeBatches settings tree : ℝ≥0∞) * ENNReal.ofReal ε := by
    calc
      _ ≤ ∑ _j : Fin (treeBatches settings tree), ENNReal.ofReal ε :=
        Finset.sum_le_sum (fun j _ => indexedBounds hbatch top tree D A x z Z q hx hq hsmall j)
      _ = _ := by simp
  have bound := (treeSimCheck_indexed_union prims K circuits settings hbatch top tree D A x z Z).trans sumBound
  have realBound := ENNReal.toReal_mono (by finiteness) bound
  simp only [treeSimTrace, probEvent_map, Function.comp_def, treeSimEvents, decide_eq_true_eq]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (checkErrorOf_nonneg K _ _ _), ε, treeCheckError] using realBound

/-- Assemble a contextual batch certificate without charging a hash error.
The two fields still to construct are inclusion of the fixed event in the
actual first-incorrect-batch events and the bound for each reached batch. -/
theorem treeSimCheckBound_of_batchCertificates
    (batchCertificates : 0 < settings.batchSize →
      ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
        (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
        (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
        DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
        ∃ events : Fin (treeBatches settings tree) → TreeSimLog C → Prop,
          (∀ r ∈ support (treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)),
            ¬ TreeSimHashBad D r.2 ∧ TreeSimWrongOutput prims K circuits settings top tree D A x z r.2 →
            ∃ j, events j r.2) ∧
          (∀ j, Pr[fun r => events j r.2 |
            treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
            ENNReal.ofReal (checkErrorOf (E := E)
              (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
              (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q))) :
    TreeSimCheckBoundGoal prims K circuits settings := by
  letI : SampleableType E := SampleableType.ofFintype E
  intro hbatch top tree D A x z Z q hx hq hsmall
  obtain ⟨events, cover, bound⟩ := batchCertificates hbatch top tree D A x z Z q hx hq hsmall
  let run := treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)
  let ε := checkErrorOf (E := E)
    (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
    (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q
  have union : Pr[fun r => ¬ TreeSimHashBad D r.2 ∧
      TreeSimWrongOutput prims K circuits settings top tree D A x z r.2 | run] ≤
      (treeBatches settings tree : ℝ≥0∞) * ENNReal.ofReal ε := by
    calc
      _ ≤ Pr[fun r => ∃ j ∈ (Finset.univ : Finset (Fin (treeBatches settings tree))), events j r.2 | run] := by
        apply probEvent_mono
        intro r hr hbad
        obtain ⟨j, hj⟩ := cover r hr hbad
        exact ⟨j, Finset.mem_univ j, hj⟩
      _ ≤ ∑ j : Fin (treeBatches settings tree), Pr[fun r => events j r.2 | run] :=
        probEvent_exists_finset_le_sum Finset.univ run (fun j r => events j r.2)
      _ ≤ ∑ _j : Fin (treeBatches settings tree), ENNReal.ofReal ε :=
        Finset.sum_le_sum (fun j _ => bound j)
      _ = _ := by simp
  simp only [treeSimTrace, probEvent_map,
    Function.comp_def, treeSimEvents, decide_eq_true_eq]
  have realBound := ENNReal.toReal_mono (by finiteness) union
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (checkErrorOf_nonneg K _ _ _), treeCheckError, run, ε] using realBound

/-- info: 'ThresholdLeanXmssSecurity.treeSimWrongOutput_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimWrongOutput_actual

/-- info: 'ThresholdLeanXmssSecurity.treeSimWrongOutput_first_batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimWrongOutput_first_batch

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_ghost_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_ghost_hashes

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_contextual

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_split_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_split_abort

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_challenge_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_challenge_good

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBound_of_batchCertificates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBound_of_batchCertificates

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_audited_logged_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_audited_logged_erase

/-- info: 'ThresholdLeanXmssSecurity.treeSimWrongOutput_audited_first_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimWrongOutput_audited_first_index

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_elementDraw_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_elementDraw_fresh

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_coin_scheduled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_coin_scheduled

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBatchAudit_phase_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBatchAudit_phase_split

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBeforeVerify_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBeforeVerify_joint

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_indexed_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_indexed_union

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBound_of_indexedBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBound_of_indexedBounds

/-- At the next exchange a previous honest abort is fatal. This property
also rules out completing successfully before that exchange. -/
def TreeSimCheckExchangeStep {α : Type} : Step C E RealSpec α → Prop
  | .done out => out = none
  | .wait _ resume => ∀ inbox j, Msg.isAbort (inbox j) = true →
      advance (resume inbox) = pure (.done none)
  | .call input _ => input.elim

def TreeSimCheckExchange {α : Type} (p : PartyM C E RealSpec α) : Prop :=
  ∀ step ∈ support (advance p.run), TreeSimCheckExchangeStep step

theorem TreeSimCheckExchangeStep.pending {α : Type} {step : Step C E RealSpec α}
    (h : TreeSimCheckExchangeStep step) : step.output = none := by
  cases step with
  | done out => exact h
  | wait out resume => rfl
  | call input resume => exact input.elim

theorem TreeSimCheckExchangeStep.continue {α β : Type}
    (k : α → PartyM C E RealSpec β) {step : Step C E RealSpec α}
    (h : TreeSimCheckExchangeStep step) :
    TreeSimCheckExchangeStep (suspendStep k step) := by
  cases step with
  | done out => rfl
  | wait out resume =>
    intro inbox j hj
    rw [advance_bind]
    change advance (resume inbox) >>= continueStep k = _
    rw [h inbox j hj, pure_bind]
    rfl
  | call input resume => exact input.elim

theorem TreeSimCheckExchange.bind {α β : Type} {p : PartyM C E RealSpec α}
    (h : TreeSimCheckExchange p) (k : α → PartyM C E RealSpec β) :
    TreeSimCheckExchange (p >>= k) := by
  intro step hs
  rw [advance_bind] at hs
  simp only [support_bind, Set.mem_iUnion] at hs
  obtain ⟨a, ha, hs⟩ := hs
  have hp := h a ha
  rw [continueStep_pending k a hp.pending] at hs
  have he : step = suspendStep k a := by simpa using hs
  exact he ▸ hp.continue k

theorem TreeSimCheckExchange.local_bind {α β : Type}
    (p : OracleComp (LocalSpec C) α) (k : α → PartyM C E RealSpec β)
    (h : ∀ a, TreeSimCheckExchange (k a)) :
    TreeSimCheckExchange (localStep p >>= k) := by
  intro step hs
  rw [advance_localStep_bind] at hs
  simp only [support_bind, Set.mem_iUnion] at hs
  obtain ⟨a, _, hs⟩ := hs
  exact h a step hs

theorem TreeSimCheckExchange.oracle_bind {α β : Type}
    (p : OracleComp (RoSpec C) α) (k : α → PartyM C E RealSpec β)
    (h : ∀ a, TreeSimCheckExchange (k a)) :
    TreeSimCheckExchange (oracleStep p >>= k) :=
  TreeSimCheckExchange.local_bind _ k h

theorem TreeSimCheckExchange.exchange_bind {α : Type}
    (out : Mail C E) (k : Mail C E → PartyM C E RealSpec α) :
    TreeSimCheckExchange (exchange out >>= k) := by
  intro step hs
  rw [advance_exchange_bind] at hs
  have he : step = .wait out (exchangeResume k) := by simpa using hs
  subst step
  intro inbox j hj
  apply advance_exchangeResume_abort k inbox j
  cases he : inbox j with
  | none => simp [he, Msg.isAbort] at hj
  | some m => cases m <;> simp_all [Msg.isAbort]

theorem treeSimCheck_openRep_exchange (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    TreeSimCheckExchange (openRep (G := RealSpec) K ctx v count) := by
  unfold openRep
  apply TreeSimCheckExchange.oracle_bind
  intro ds
  exact TreeSimCheckExchange.exchange_bind _ _

theorem treeSimCheck_realCoin_exchange (ctx : Context C) (count : ℕ) (st : RunState C) :
    TreeSimCheckExchange (((realCheckGadgets K ctx).coin count).run st) := by
  rw [realCoin_run]
  apply TreeSimCheckExchange.oracle_bind
  intro rnd
  unfold openSh
  rw [bind_assoc]
  exact TreeSimCheckExchange.exchange_bind _ _

/-- An honest abort at the joint boundary reaches every remaining exchange,
including a mixture of parties entering Coin and parties opening empty checks. -/
theorem treeSimCheck_exchange_round_abort {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, TreeSimCheckExchangeStep (steps i))
    (stopped : ∃ j, j ∉ D.1 ∧ steps j = .done none) :
    stepRound worldRoles D A noFunctionality state steps = (do
      let b ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none)
      pure (b.1, (fun _ => Step.done none), b.2)) := by
  rw [stepRound_real]
  apply bind_congr
  intro b
  have hl : ∀ i, roundLocal D steps b.2 i = pure (.done none) := by
    intro i
    have hi := hsteps i
    obtain ⟨j, hj, hjstep⟩ := stopped
    unfold roundLocal
    cases he : steps i with
    | done out =>
      have ho : out = none := by simpa only [he, TreeSimCheckExchangeStep] using hi
      subst out
      rfl
    | wait out resume =>
      split_ifs with hic
      · rfl
      · apply (show TreeSimCheckExchangeStep (.wait out resume) from he ▸ hi) _ j
        simp [hj, hjstep, Step.delivered, Msg.isAbort]
    | call input resume => exact input.elim
  rcases b with ⟨state', sent⟩
  dsimp only at hl ⊢
  rw [sequenceFin_congr_pure _ (fun _ => Step.done none) hl]
  simp only [free_pure, pure_bind]

set_option maxHeartbeats 1000000 in
theorem treeSimCheckAfterVerify_exchange (ctx : Context C) (jobs : List Circuit)
    (p : (Shares C Bit × List (Tuple C)) × RunState C) :
    TreeSimCheckExchange (treeSimCheckAfterVerify K ctx jobs p) := by
  unfold treeSimCheckAfterVerify check
  dsimp only
  split_ifs with hz
  · simp only [StateT.run_pure, pure_bind]
    exact (treeSimCheck_openRep_exchange K ctx p.1.1 _).bind _
  · simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    exact (treeSimCheck_realCoin_exchange K ctx 1 p.2).bind _

theorem treeSimCheck_exchange_rounds_abort {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, TreeSimCheckExchangeStep (steps i))
    (stopped : ∃ j, j ∉ D.1 ∧ steps j = .done none)
    (out : A.State × (C.Party → Option α))
    (hout : out ∈ support (executeRounds worldRoles D A noFunctionality fuel state steps)) :
    out.2 = fun _ => none := by
  have ho : (fun i => (steps i).output) = fun _ => none :=
    funext fun i => (hsteps i).pending
  cases fuel with
  | zero =>
    simpa only [executeRounds, ho, support_pure, Set.mem_singleton_iff] using
      congrArg Prod.snd (show out = (state, fun _ => none) by simpa [executeRounds, ho] using hout)
  | succ fuel =>
    rw [executeRounds] at hout
    split_ifs at hout with hd
    · have he : out = (state, fun _ => none) := by simpa [ho] using hout
      exact congrArg Prod.snd he
    · rw [treeSimCheck_exchange_round_abort D A state steps hsteps stopped] at hout
      simp only [bind_assoc, pure_bind, executeRounds_all_none,
        support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hout
      obtain ⟨b, _, he⟩ := hout
      exact congrArg Prod.snd he

theorem treeSimCheck_exchange_continuations_live {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (pref : C.Party → Option α) (k : C.Party → α → PartyM C E RealSpec β)
    (hk : ∀ i a, TreeSimCheckExchange (k i a))
    (next : C.Party → Step C E RealSpec β)
    (hn : next ∈ support (free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i)))))
    (out : A.State × (C.Party → Option β))
    (hout : out ∈ support (executeRounds worldRoles D A noFunctionality fuel state next))
    (accepted : ∃ i value, out.2 i = some value) :
    ∀ j, j ∉ D.1 → (pref j).isSome := by
  have hn' := treeSimCheck_support_free _ hn
  have hn_i := mem_support_sequenceFin_oc _ _ hn'
  have hnext : ∀ i, TreeSimCheckExchangeStep (next i) := by
    intro i
    have hi := hn_i i
    cases he : pref i with
    | none =>
      have hi' : next i = .done none := by simpa [he, continueStep] using hi
      simp [hi', TreeSimCheckExchangeStep]
    | some a => exact hk i a _ (by simpa only [he, continueStep] using hi)
  intro j hj
  cases he : pref j with
  | some a => rfl
  | none =>
    have hjn : next j = .done none := by
      simpa only [he, continueStep, support_pure, Set.mem_singleton_iff] using (hn_i j)
    have ho := treeSimCheck_exchange_rounds_abort D A fuel state next hnext ⟨j, hj, hjn⟩ out hout
    obtain ⟨i, value, hi⟩ := accepted
    simp only [ho] at hi
    cases hi

/-- A successful continuation certifies that every honest prefix completed
at the same scheduler boundary. Both the prefix and the remaining execution
are retained, rather than replacing them by independent local replays. -/
theorem treeSimCheckTimed_phase_live {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (hk : ∀ i a, TreeSimCheckExchange (k i a))
    (out : A.State × (C.Party → Option β))
    (hout : out ∈ support (executePhase worldRoles D A noFunctionality (n + 1 + fuel) state
      (fun i => p i >>= k i))) (accepted : ∃ i value, out.2 i = some value) :
    ∃ pref, pref ∈ support (executePhase worldRoles D A noFunctionality (n + 1) state p) ∧
      (∀ i, i ∉ D.1 → (pref.2 i).isSome) ∧
      ∃ next, next ∈ support (free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref.2 i)))) ∧
        out ∈ support (executeRounds worldRoles D A noFunctionality fuel pref.1 next) := by
  rw [treeSimCheckTimed_phase_split D A n fuel state p k hp] at hout
  simp only [support_bind, Set.mem_iUnion] at hout
  obtain ⟨pref, hpref, next, hn, ho⟩ := hout
  exact ⟨pref, hpref,
    treeSimCheck_exchange_continuations_live D A fuel pref.1 pref.2 k hk next hn out ho accepted,
    next, hn, ho⟩

/-- The cut is in the supplied execution log: the prefix, local restart,
and suffix partition that same replay, and acceptance forces every honest
prefix result to be present. -/
theorem treeSimCheckTimed_phase_replay_live {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (hk : ∀ i a, TreeSimCheckExchange (k i a))
    (log : TreeSimLog C) (out : A.State × (C.Party → Option β))
    (run : TreeSimCheckReplay (executePhase worldRoles D A noFunctionality (n + 1 + fuel) state
      (fun i => p i >>= k i)) log out) (accepted : ∃ i value, out.2 i = some value) :
    ∃ pref first next middle last,
      log = first ++ middle ++ last ∧
      TreeSimCheckReplay (executePhase worldRoles D A noFunctionality (n + 1) state p) first pref ∧
      (∀ i, i ∉ D.1 → (pref.2 i).isSome) ∧
      TreeSimCheckReplay (free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref.2 i)))) middle next ∧
      TreeSimCheckReplay (executeRounds worldRoles D A noFunctionality fuel pref.1 next) last out := by
  rw [treeSimCheckTimed_phase_split D A n fuel state p k hp] at run
  obtain ⟨pref, first, tail, hfirst, htail, he⟩ := run.bind_inv _ _
  obtain ⟨next, middle, last, hmiddle, hlast, ht⟩ := htail.bind_inv _ _
  refine ⟨pref, first, next, middle, last, ?_, hfirst, ?_, hmiddle, hlast⟩
  · simpa only [ht, List.append_assoc] using he
  · exact treeSimCheck_exchange_continuations_live D A fuel pref.1 pref.2 k hk next
      hmiddle.mem_support out hlast.mem_support accepted

theorem treeSimCheckBatchPrefix_state (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (h : some data ∈ support (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run) :
    let js := jobs.map (circuits ctx.keys.parameter ·.kind)
    data.2.2.history = filledHistory K ctx.self data.2.1.2 ∧
      data.2.2.label = initial.1 + depth js + 1 ∧ data.2.2.tag = initial.2 ∧
      data.2.1.2.map (·.count) =
        (List.range (depth js)).map (fun l => (gatesAt js l).length) ++ [(outputsOf js).length] ∧
      data.2.1.2.map (·.mode) = (List.range (depth js)).map (fun _ => settings.mode) ++ [.peer] := by
  unfold treeSimCheckBatchPrefix at h
  obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨p, hprefix, he⟩ := treeSimCheck_some_bind _ _ _ hrest
  have he' : data = (inputs, p) := by simpa only [OptionT.run_pure, support_pure,
    Set.mem_singleton_iff, Option.some.injEq] using he
  subst data
  exact treeSimCheckBeforeVerify_state K ctx settings.mode _ inputs initial.1 initial.2 p.1 p.2 hprefix

theorem treeSimCheckBatchAudit_replay_live {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (parameter : PublicParameter)
    (hparameter : ∀ i, (ctx i).keys.parameter = parameter) (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (log : TreeSimLog C) (out : A.State × (C.Party → Option α))
    (run : TreeSimCheckReplay (executePhase worldRoles D A noFunctionality
      (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 + fuel) state
      (fun i => (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i)) log out)
    (accepted : ∃ i value, out.2 i = some value) :
    ∃ pref first next middle last,
      log = first ++ middle ++ last ∧
      TreeSimCheckReplay (executePhase worldRoles D A noFunctionality
        (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) state
        (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial)) first pref ∧
      (∀ i, i ∉ D.1 → (pref.2 i).isSome) ∧
      TreeSimCheckReplay (free (Concrete.sequenceFin fun i => continueStep
        (fun p => treeSimCheckBatchFinish K circuits (ctx i) jobs initial p >>= k i)
        (.done (pref.2 i)))) middle next ∧
      TreeSimCheckReplay (executeRounds worldRoles D A noFunctionality fuel pref.1 next) last out := by
  simp only [treeSimCheckBatchAudit_run_prefix, bind_assoc] at run
  apply treeSimCheckTimed_phase_replay_live D A _ fuel state _ _ ?_ ?_ log out run accepted
  · intro i
    simpa only [hparameter i] using treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
  · intro i p
    unfold treeSimCheckBatchFinish
    rw [bind_assoc]
    exact (treeSimCheckAfterVerify_exchange K (ctx i) _ p.2).bind _

/-- All checkpoint fields come from the joint logged prefix, including the
actual PRF inputs; this is not a family of independently chosen local runs. -/
theorem treeSimCheckBatchPrefix_joint (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (hparameter : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (log : TreeSimLog C)
    (r : A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)))
    (run : TreeSimCheckReplay (executePhase worldRoles D A noFunctionality fuel state
      (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial)) log r)
    (live : ∀ i, i ∉ D.1 → (r.2 i).isSome) :
    let js := jobs.map (circuits parameter ·.kind)
    ∀ i, i ∉ D.1 → ∃ data, r.2 i = some data ∧
      data.2.2.history = filledHistory K i data.2.1.2 ∧
      data.2.2.label = initial.1 + depth js + 1 ∧ data.2.2.tag = initial.2 ∧
      data.2.1.2.map (·.count) =
        (List.range (depth js)).map (fun l => (gatesAt js l).length) ++ [(outputsOf js).length] ∧
      data.2.1.2.map (·.mode) = (List.range (depth js)).map (fun _ => settings.mode) ++ [.peer] := by
  intro js i hi
  obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (live i hi)
  have hp := treeSimCheck_phase_replay D A noFunctionality (fun _ _ => True) fuel state _ r
    ⟨log, run, fun _ _ _ => trivial⟩ i hi data hd
  obtain ⟨_, hp, _⟩ := hp
  refine ⟨data, hd, ?_⟩
  simpa only [self i, hparameter i] using
    treeSimCheckBatchPrefix_state K circuits settings (ctx i) jobs initial data hp.mem_support

/-- Every emitted record satisfies a property, on the supplied replay. -/
def TreeSimCheckAuditAll {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (good : W → Prop)
    (p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α) : Prop :=
  ∀ initial value records final,
    TreeSimCheckAllowed allowed (p.run.run initial).run (some ((value, records), final)) →
    ∀ r ∈ records, good r

theorem TreeSimCheckAuditAll.pure {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (good : W → Prop) (a : α) :
    TreeSimCheckAuditAll (σ := σ) allowed good (pure a) := by
  intro initial value records final h
  simp only [WriterT.run_pure, StateT.run_pure, OptionT.run_pure] at h
  have he := congrArg (fun r => r.1.2) (Option.some.inj h.pure_inv)
  change records = [] at he
  simp [he]

theorem TreeSimCheckAuditAll.bind {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {good : W → Prop}
    {p : WriterT (List W) (StateT σ (OptionT (OracleComp spec))) α}
    {f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β}
    (hp : TreeSimCheckAuditAll allowed good p) (hf : ∀ a, TreeSimCheckAuditAll allowed good (f a)) :
    TreeSimCheckAuditAll allowed good (p >>= f) := by
  intro initial value records final h r hr
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map] at h
  obtain ⟨a, ha, ht⟩ := h.option_bind_inv _ _ _
  obtain ⟨b, hb, he⟩ := ht.option_map_inv _ _ _
  have hrecords := congrArg (fun r => r.1.2) he
  change a.1.2 ++ b.1.2 = records at hrecords
  rw [← hrecords, List.mem_append] at hr
  rcases hr with hr | hr
  · exact hp initial a.1.1 a.1.2 a.2 ha r hr
  · exact hf a.1.1 a.2 b.1.1 b.1.2 b.2 hb r hr

theorem TreeSimCheckAuditAll.lift {ι σ W α : Type} {spec : OracleSpec.{0, 0} ι}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) (good : W → Prop)
    (p : StateT σ (OptionT (OracleComp spec)) α) :
    TreeSimCheckAuditAll (σ := σ) allowed good (liftM p) := by
  intro initial value records final h
  simp only [WriterT.run_liftM, StateT.run_map] at h
  obtain ⟨a, _, he⟩ := h.option_map_inv _ _ _
  have hr := congrArg (fun r => r.1.2) he
  change [] = records at hr
  simp [← hr]

theorem TreeSimCheckAuditAll.mapM {ι σ W α β : Type} {spec : OracleSpec.{0, 0} ι}
    {allowed : (t : spec.Domain) → spec.Range t → Prop} {good : W → Prop}
    (f : α → WriterT (List W) (StateT σ (OptionT (OracleComp spec))) β)
    (h : ∀ a, TreeSimCheckAuditAll allowed good (f a)) (xs : List α) :
    TreeSimCheckAuditAll allowed good (xs.mapM f) := by
  induction xs with
  | nil => simpa only [List.mapM_nil] using TreeSimCheckAuditAll.pure allowed good ([] : List β)
  | cons a xs ih =>
    rw [List.mapM_cons]
    exact (h a).bind (fun _ => ih.bind (fun _ => .pure allowed good _))

def TreeSimCheckRecordValid
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (r : TreeSimCheckBatchRecord C) : Prop :=
  TreeSimCheckAllowed allowed
    ((treeSimCheckRunJobs K (realRunGadgets K r.ctx settings.mode)
      (r.jobs.map (circuits r.ctx.keys.parameter ·.kind)) r.inputs).run
        ⟨fun _ => [], r.start.1, r.start.2⟩).run
    (some ((r.outputs, r.tuples, r.checkpoint), r.finish))

theorem treeSimCheckBatchAudit_records
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (jobs : List Job) :
    TreeSimCheckAuditAll allowed
      (fun r => r.ctx = ctx ∧ TreeSimCheckRecordValid K circuits settings allowed r)
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
  exact ⟨rfl, hp⟩

theorem treeSimCheckCeremonyAuditBody_records
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree) :
    TreeSimCheckAuditAll allowed
      (fun r => r.ctx = ctx ∧ TreeSimCheckRecordValid K circuits settings allowed r)
      (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree) := by
  unfold treeSimCheckCeremonyAuditBody
  apply ceremonyOutput_closed
    (m := WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)))
    (fun {α} (p : WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)) α) => TreeSimCheckAuditAll allowed
      (fun r => r.ctx = ctx ∧ TreeSimCheckRecordValid K circuits settings allowed r) p)
  · intro α a
    exact .pure _ _ a
  · intro α β p f hp hf
    exact hp.bind hf
  · intro α p
    exact .lift _ _ _
  · intro jobs
    unfold batched
    exact (TreeSimCheckAuditAll.mapM _
      (fun batch => treeSimCheckBatchAudit_records K circuits settings allowed ctx batch) _).bind
        (fun _ => .pure _ _ _)

theorem treeSimCheckAfterSetupAudit_records
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (ctx : Context C) (top : TopTree) (tree : Tree)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (h : TreeSimCheckAllowed allowed
      (treeSimCheckAfterSetupAudit K circuits settings ctx top tree).run (some (value, records))) :
    ∀ r ∈ records, r.ctx = ctx ∧ TreeSimCheckRecordValid K circuits settings allowed r := by
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
    exact treeSimCheckCeremonyAuditBody_records K circuits settings allowed ctx top tree
      (0, 0) (some value) records last hp

theorem TreeSimCheckAuditedReference.records (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (log : TreeSimLog C) (hash : Query C → HashOutput) (i : C.Party) (hi : i ∉ D.1)
    (value : TreeOutput) (records : List (TreeSimCheckBatchRecord C))
    (ref : TreeSimCheckAuditedReference prims K circuits settings top tree D A parameter seeds pairs z
      log hash i value records) :
    ∃ prss, ∀ r ∈ records,
      r.ctx = ⟨i, dealtKeys parameter seeds pairs i, prss⟩ ∧
      TreeSimCheckRecordValid K circuits settings
        (treeSimCheckPartyAllowed (fun t u => TreeSimCheckWorldHashes hash (.inr t) u)) r := by
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
  exact ⟨prss, treeSimCheckAfterSetupAudit_records K circuits settings _ _ top tree value records hbody⟩

theorem TreeSimCheckRecordValid.assembled
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {r : TreeSimCheckBatchRecord C} (h : TreeSimCheckRecordValid K circuits settings allowed r) :
    ∃ opened, r.outputs = assemble (r.jobs.map (circuits r.ctx.keys.parameter ·.kind)) opened := by
  unfold TreeSimCheckRecordValid at h
  rw [treeSimCheckRunJobs_run_prefix] at h
  obtain ⟨p, _, hafter⟩ := h.option_bind_inv _ _ _
  unfold treeSimCheckAfterVerify at hafter
  obtain ⟨checked, _, hopen⟩ := hafter.option_bind_inv _ _ _
  obtain ⟨opened, _, he⟩ := hopen.option_bind_inv _ _ _
  exact ⟨opened, congrArg (fun p => p.1.1) (Option.some.inj he.pure_inv)⟩

private theorem treeSimCheck_assemble_cons (j : Circuit) (js : List Circuit) (opened : ℕ → Bit) :
    assemble (j :: js) opened = vector j.outputs.length opened ::
      assemble js (fun g => opened (j.outputs.length + g)) := by
  unfold assemble
  rw [List.map_cons, List.zipIdx_cons, List.map_cons, List.zipIdx_succ, List.map_map]
  congr 1
  · simp
  · refine List.map_congr_left fun p _ => ?_
    simp [List.take_succ_cons, Nat.add_assoc]

theorem treeSimCheck_assemble_zero (jobs : List Circuit) (opened : ℕ → Bit)
    (h : ∀ j ∈ jobs, j.outputs = []) : assemble jobs opened = jobs.map (fun _ => []) := by
  induction jobs generalizing opened with
  | nil => rfl
  | cons j js ih =>
    rw [treeSimCheck_assemble_cons]
    simp only [h j (by simp), List.length_nil, vector, List.range_zero, List.map_nil, List.map_cons]
    congr 1
    exact ih _ (fun k hk => h k (by simp [hk]))

theorem treeSimCheck_tupleCount_zero_outputs (jobs : List Circuit) (h : tupleCount jobs = 0) :
    ∀ j ∈ jobs, j.outputs = [] := by
  have hz : (jobs.map (·.outputs.length)).sum = 0 := by unfold tupleCount at h; omega
  intro j hj
  have he : j.outputs.length = 0 :=
    List.sum_eq_zero_iff_forall_eq_nat.mp hz _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
  exact List.length_eq_zero_iff.mp he

theorem TreeSimCheckRecordValid.incorrect_count
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {r : TreeSimCheckBatchRecord C} (h : TreeSimCheckRecordValid K circuits settings allowed r)
    (hash : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (wrong : r.outputs ≠ r.jobs.map
      (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits r.ctx.keys.parameter seeds job))) :
    tupleCount (r.jobs.map (circuits r.ctx.keys.parameter ·.kind)) ≠ 0 := by
  intro hz
  obtain ⟨opened, ho⟩ := h.assembled K circuits settings
  have hempty := treeSimCheck_tupleCount_zero_outputs _ hz
  apply wrong
  rw [ho, treeSimCheck_assemble_zero _ opened hempty, List.map_map]
  apply List.map_congr_left
  intro job hj
  have hjout := hempty _ (List.mem_map.mpr ⟨job, hj, rfl⟩)
  simp only [evalJob, D_bind, D_pure, Circuit.eval, hjout, List.map_nil]
  rfl

theorem TreeSimCheckRecordValid.checkpoint
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {r : TreeSimCheckBatchRecord C} (h : TreeSimCheckRecordValid K circuits settings allowed r) :
    let js := r.jobs.map (circuits r.ctx.keys.parameter ·.kind)
    r.checkpoint.history = filledHistory K r.ctx.self r.tuples ∧
      r.checkpoint.label = r.start.1 + depth js + 1 ∧ r.checkpoint.tag = r.start.2 ∧
      r.tuples.map (·.count) =
        (List.range (depth js)).map (fun l => (gatesAt js l).length) ++ [(outputsOf js).length] ∧
      r.tuples.map (·.mode) = (List.range (depth js)).map (fun _ => settings.mode) ++ [.peer] := by
  unfold TreeSimCheckRecordValid at h
  rw [treeSimCheckRunJobs_run_prefix] at h
  obtain ⟨p, hp, hafter⟩ := h.option_bind_inv _ _ _
  unfold treeSimCheckAfterVerify at hafter
  obtain ⟨checked, _, hopen⟩ := hafter.option_bind_inv _ _ _
  obtain ⟨opened, _, he⟩ := hopen.option_bind_inv _ _ _
  have he' := Option.some.inj he.pure_inv
  have ht : r.tuples = p.1.2 := congrArg (fun a => a.1.2.1) he'
  have hs : r.checkpoint = p.2 := congrArg (fun a => a.1.2.2) he'
  obtain ⟨_, hp, _⟩ := hp
  simpa only [ht, hs] using treeSimCheckBeforeVerify_state K r.ctx settings.mode _ r.inputs
    r.start.1 r.start.2 p.1 p.2 hp.mem_support

theorem TreeSimCheckRecordValid.count
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {r : TreeSimCheckBatchRecord C} (h : TreeSimCheckRecordValid K circuits settings allowed r) :
    (r.tuples.map (·.count)).sum = tupleCount (r.jobs.map (circuits r.ctx.keys.parameter ·.kind)) := by
  rw [(h.checkpoint K circuits settings).2.2.2.1]
  simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact (tupleCount_eq _).symm

/-- The fixed indexed event supplies a real, nonempty check at that very
record index. In particular, an empty check cannot be the first bad batch. -/
theorem treeSimCheck_indexed_bad_checkpoint (top : TopTree) (tree : Tree) (D : C.Coalition)
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
      (batch.tuples.map (·.count)).sum ≠ 0 := by
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
  refine ⟨i, value, records, batch, hash, seeds, hi, hout, ?_, ?_, hg, hvalid, hw, ?_⟩
  · simp [he, hj]
  · rw [hctx]
  · rw [hvalid.count K circuits settings]
    exact hvalid.incorrect_count prims K circuits settings hash seeds hw

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBatchAudit_replay_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBatchAudit_replay_live

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBatchPrefix_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBatchPrefix_joint

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_indexed_bad_checkpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_indexed_bad_checkpoint

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBound_of_indexedBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckBound_of_indexedBounds

/-- Filling another oracle cell commutes with one lazy query. -/
theorem treeSimCheck_randomOracle_update {X R : Type} [DecidableEq X] [SampleableType R]
    (c : (X →ₒ R).QueryCache) (x y : X) (hne : x ≠ y) (v : R) :
    ((X →ₒ R).randomOracle x).run (c.cacheQuery y v) =
      (fun r : R × (X →ₒ R).QueryCache => (r.1, r.2.cacheQuery y v)) <$>
        ((X →ₒ R).randomOracle x).run c := by
  have hc : (c.cacheQuery y v) x = c x := QueryCache.cacheQuery_of_ne c v hne
  cases hx : c x with
  | some u =>
    rw [QueryImpl.withCaching_run_some _ (hc.trans hx),
      QueryImpl.withCaching_run_some _ hx, map_pure]
  | none =>
    rw [QueryImpl.withCaching_run_none _ (hc.trans hx),
      QueryImpl.withCaching_run_none _ hx, Functor.map_map]
    congr 1
    funext u
    congr 1
    exact (Function.update_comm hne (some u) (some v) c).symm

/-- A world query other than the selected hidden cell commutes with filling
that cell. The hash cache and the returned query answer are retained. -/
theorem treeSimCheck_world_update (D : C.Coalition) (a : HiddenAddress C)
    (t : (WorldSpec C).Domain)
    (hne : t ≠ .inr (.inr (.inr (a.1.1, a.1.2, a.2))))
    (h : HashCache C) (c : HiddenCache C) (v : Bit) :
    (streamWorld prims D t).run (h, c.cacheQuery a v) =
      (fun r => (r.1, r.2.1, r.2.2.cacheQuery a v)) <$>
        (streamWorld prims D t).run (h, c) := by
  rcases t with t | t
  · simp [streamWorld, onHash, Functor.map_map]
  · rcases t with n | q | x
    · simp [streamWorld, onHash, Functor.map_map]
    · simp [streamWorld, onHash, Functor.map_map]
    · by_cases hh : Hidden D x.1
      · simp only [streamWorld, hh, if_true, StateT.run_mk]
        rw [treeSimCheck_randomOracle_update c ((x.1, x.2.1), x.2.2) a
          (fun he => hne (by cases x; cases a; cases he; rfl)) v]
        simp only [Functor.map_map]
      · simp [streamWorld, hh, onHash, Functor.map_map]

/-- No other world query changes the selected hidden cell. -/
theorem treeSimCheck_world_other (D : C.Coalition) (a : HiddenAddress C)
    (t : (WorldSpec C).Domain)
    (hne : t ≠ .inr (.inr (.inr (a.1.1, a.1.2, a.2))))
    (h : HashCache C) (c : HiddenCache C)
    (r : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((streamWorld prims D t).run (h, c))) :
    r.2.2 a = c a := by
  rcases t with t | t
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    rfl
  · rcases t with n | q | x
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨u, _, rfl⟩ := hr
      rfl
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨u, _, rfl⟩ := hr
      rfl
    · apply treeSim_hiddenQuery_frame prims D ((x.1, x.2.1), x.2.2) a
        (fun he => hne (by cases x; cases a; cases he; rfl)) (h, c) r
      unfold hiddenQuery
      erw [simulateQ_spec_query]
      exact hr

/-- Deferred sampling for one hidden cell, valid for every adaptive world
program. It keeps the complete returned value (which may contain the real log)
and the final hash cache; only hidden cache occupancy is unobserved. -/
theorem treeSimCheck_world_presample {α : Type} (D : C.Coalition)
    (a : HiddenAddress C) (hidden : Hidden D a.1.1)
    (p : OracleComp (WorldSpec C) α) :
    ∀ (h : HashCache C) (c : HiddenCache C), c a = none →
      𝒟[(fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c)] =
        𝒟[(do
          let v ← $ᵗ Bit
          (fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
            (simulateQ (streamWorld prims D) p).run (h, c.cacheQuery a v))] := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro h c fresh
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ Bit) (by simp) (pure (x, h))).symm
  | query_bind t k ih =>
    intro h c fresh
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    by_cases ht : t = .inr (.inr (.inr (a.1.1, a.1.2, a.2)))
    · subst t
      simp only [streamWorld, hidden, if_true, StateT.run_mk]
      rw [QueryImpl.withCaching_run_none _ fresh]
      simp only [Functor.map_map, bind_map_left]
      apply evalDist_bind_congr_all
      intro v
      rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self c a v)]
      simp only [map_pure, pure_bind]
    · simp_rw [treeSimCheck_world_update prims D a t ht, bind_map_left]
      rw [← OracleComp.DeferredSampling.evalDist_bind_comm]
      apply evalDist_bind_congr
      intro r hr
      exact ih r.1 r.2.1 r.2.2 ((treeSimCheck_world_other prims D a t ht h c r hr).trans fresh)

theorem treeSimCheck_world_presample_sequence {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) :
    ∀ {n : ℕ} (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr)
      (hh : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C),
      (∀ i, c (addr i) = none) →
      𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c)] =
        𝒟[(do
          let vals ← Concrete.sequenceFin (fun _ : Fin n => ($ᵗ Bit))
          (fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
            (simulateQ (streamWorld prims D) p).run (h, cacheFin addr vals c))]
  | 0, addr, ha, hh, h, c, fresh => by simp [Concrete.sequenceFin, cacheFin]
  | n + 1, addr, ha, hh, h, c, fresh => by
    rw [treeSimCheck_world_presample prims D (addr 0) (hh 0) p h c (fresh 0)]
    simp only [Concrete.sequenceFin, bind_assoc, bind_map_left]
    apply evalDist_bind_congr_all
    intro v
    simpa only [pure_bind, cacheFin, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ] using
      treeSimCheck_world_presample_sequence D p (fun i : Fin n => addr i.succ)
        (ha.comp (Fin.succ_injective n)) (fun i => hh i.succ) h (c.cacheQuery (addr 0) v)
        (fun i => (QueryCache.cacheQuery_of_ne c v
          (fun he => Fin.succ_ne_zero i (ha he))).trans (fresh i.succ))

/-- A finite family of fresh hidden bits can be sampled jointly before an
arbitrary continuation. This is an equality of distributions of the actual
result and final hash cache, without any assumed continuation coupling. -/
theorem treeSimCheck_world_presample_table {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) {n : ℕ}
    (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr)
    (hh : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ i, c (addr i) = none) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (Fin n → Bit)
        (fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) p).run (h, cacheFin addr vals c))] := by
  rw [treeSimCheck_world_presample_sequence prims D p addr ha hh h c fresh,
    evalDist_bind, evalDist_sequenceFin_uniform, ← evalDist_bind]

/-- A continuation that never reads a cell cannot observe its occupancy or
value. This is a program equality and needs no freshness assumption. -/
theorem treeSimCheck_world_unread {α : Type} (D : C.Coalition)
    (a : HiddenAddress C) (p : OracleComp (WorldSpec C) α)
    (avoid : IsQueryBoundP p
      (fun t => t = .inr (.inr (.inr (a.1.1, a.1.2, a.2)))) 0) :
    ∀ (h : HashCache C) (c : HiddenCache C) (v : Bit),
      (fun r => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) p).run (h, c.cacheQuery a v) =
        (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c) := by
  induction p using OracleComp.inductionOn with
  | pure x => intros; simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at avoid
    have ht : t ≠ .inr (.inr (.inr (a.1.1, a.1.2, a.2))) := by
      simpa using avoid.1
    have hk (u) : IsQueryBoundP (k u)
        (fun t => t = .inr (.inr (.inr (a.1.1, a.1.2, a.2)))) 0 := by
      simpa only [if_neg ht] using avoid.2 u
    intro h c v
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [treeSimCheck_world_update prims D a t ht h c v, bind_map_left]
    exact bind_congr fun r => ih r.1 (hk r.1) r.2.1 r.2.2 v

/-- Once a whole PRSS block has been consumed, a continuation avoiding those
positions runs independently of its retained hidden-cache entries. -/
theorem treeSimCheck_world_unread_table {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) :
    ∀ {n : ℕ} (addr : Fin n → HiddenAddress C) (vals : Fin n → Bit)
      (avoid : ∀ i, IsQueryBoundP p
        (fun t => t = .inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))) 0)
      (h : HashCache C) (c : HiddenCache C),
      (fun r => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) p).run (h, cacheFin addr vals c) =
        (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c)
  | 0, addr, vals, avoid, h, c => rfl
  | n + 1, addr, vals, avoid, h, c => by
    rw [cacheFin, treeSimCheck_world_unread_table D p
      (fun i : Fin n => addr i.succ) (fun i => vals i.succ) (fun i => avoid i.succ),
      treeSimCheck_world_unread prims D (addr 0) p (avoid 0)]

/-- The actual field encoding transports an entire fresh PRSS block to
uniform field elements before an arbitrary world computation. -/
theorem treeSimCheck_world_presample_fields [SampleableType E] {α : Type}
    (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (name : KeyName C) (key : HashOutput) (hidden : Hidden D name)
    (label idx count : ℕ) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ g : Fin (elementBits * count), c ((name, key), label, idx, g.val) = none) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (Fin count → E)
        (fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) p).run
            (h, cacheFin (fun g : Fin (elementBits * count) => ((name, key), label, idx, g.val))
              ((treeSimCheckFieldTable K count).symm vals) c))] := by
  let addr := fun g : Fin (elementBits * count) => ((name, key), label, idx, g.val)
  have hinj : Function.Injective addr := by
    intro a b he
    apply Fin.ext
    exact congrArg (fun x => x.2.2.2) he
  rw [treeSimCheck_world_presample_table prims D p addr hinj (fun _ => hidden) h c fresh]
  have hu := evalDist_map_bijective_uniform_cross (α := Fin (elementBits * count) → Bit)
    (treeSimCheckFieldTable K count) (treeSimCheckFieldTable K count).bijective
  conv_rhs => rw [evalDist_bind, ← hu, ← evalDist_bind, bind_map_left]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- A concrete table-reading prefix followed by an adaptive continuation is
an independent uniform draw followed by that same continuation. Repeated
holder reads are permitted inside the prefix. -/
theorem treeSimCheck_world_read_table {α β : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (k : α → OracleComp (WorldSpec C) β)
    {n : ℕ} (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr)
    (hh : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ i, c (addr i) = none) (out : (Fin n → Bit) → α)
    (ready : ∀ vals, (simulateQ (streamWorld prims D) p).run (h, cacheFin addr vals c) =
      pure (out vals, (h, cacheFin addr vals c)))
    (avoid : ∀ vals i, IsQueryBoundP (k (out vals))
      (fun t => t = .inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))) 0) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) (p >>= k)).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (Fin n → Bit)
        (fun r : β × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) (k (out vals))).run (h, c))] := by
  rw [treeSimCheck_world_presample_table prims D (p >>= k) addr ha hh h c fresh]
  apply evalDist_bind_congr_all
  intro vals
  simp only [simulateQ_bind, StateT.run_bind, ready, pure_bind]
  rw [treeSimCheck_world_unread_table prims D (k (out vals)) addr vals (avoid vals)]

/-- The real field-codec call can be replaced by an independent uniform
vector in any continuation that has consumed this stream block. -/
theorem treeSimCheck_elementDraw_uniform [SampleableType E] {α : Type}
    (D : C.Coalition) (name : KeyName C) (key : HashOutput) (hidden : Hidden D name)
    (label idx count : ℕ) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ g : Fin (elementBits * count), c ((name, key), label, idx, g.val) = none)
    (k : (ℕ → E) → OracleComp (WorldSpec C) α)
    (avoid : ∀ vals : Fin count → E, ∀ g : Fin (elementBits * count),
      IsQueryBoundP (k (treeSimCheckFieldPad K vals))
        (fun t => t = .inr (.inr (.inr (name, key, label, idx, g.val)))) 0) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)) >>= k)).run
        (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (Fin count → E)
        (fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) (k (treeSimCheckFieldPad K vals))).run (h, c))] := by
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  rw [evalDist_bind, treeSimCheck_elementDraw_fresh prims K D name key hidden label idx count h c fresh,
    ← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr_all
  intro vals
  rw [treeSimCheck_world_unread_table prims D (k (treeSimCheckFieldPad K vals))
    (fun g : Fin (elementBits * count) => ((name, key), label, idx, g.val))
    ((treeSimCheckFieldTable K count).symm vals) (avoid vals)]

theorem treeSimCheck_sequenceFin_cached {σ α : Type} {n : ℕ}
    (p : Fin n → StateT σ ProbComp α) (out : Fin n → α) (s : σ)
    (ready : ∀ i, (p i).run s = pure (out i, s)) :
    (Concrete.sequenceFin p).run s = pure (out, s) := by
  induction n with
  | zero =>
    simp only [Concrete.sequenceFin, StateT.run_pure]
    congr 2
    exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure]
    rw [ready 0, pure_bind, ih (fun i : Fin n => p i.succ)
      (fun i => out i.succ) (fun i => ready i.succ), pure_bind]
    congr 2
    funext i
    cases i using Fin.cases <;> rfl

/-- All honest Coin entries read the same shared caches in the driver's
actual order. Each holder's complete PRSS row determines its waiting step. -/
theorem treeSimCheck_coin_start_ready {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (rnd : C.Party → PrssOutput C E) (s : HashCache C × HiddenCache C)
    (ready : ∀ i, i ∉ D.1 → (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw (ctx i) (elementCodec K) (st i).label 1 count) (LocalSpec C)))).run s =
        pure (rnd i, s)) :
    (simulateQ (streamWorld prims D) (startSteps worldRoles D
      (fun i => ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= k i))).run s =
        pure (treeSimCoinWaiting K D count rnd st k, s) := by
  unfold startSteps
  rw [simulateQ_sequenceFin]
  apply treeSimCheck_sequenceFin_cached
  intro i
  by_cases hi : i ∈ D.1
  · simp [hi, treeSimCoinWaiting]
  · simp only [if_neg hi]
    rw [treeSim_coin_start prims K D (ctx i) count (st i) (k i) (rnd i) s (ready i hi)]
    rw [treeSim_coinStep_context K (ctx i) (localContext i) (self i hi)]
    simp only [treeSimCoinWaiting, if_neg hi]

/-- Joint normalization of the real Coin entry and its complete continuation.
The sampled table is shared by every holder; the continuation may contain
the adversary's rushing call, all later checks, and the real logger. -/
theorem treeSimCheck_coin_entry_table {α β : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (next : (C.Party → Step C E RealSpec α) → OracleComp (WorldSpec C) β)
    {n : ℕ} (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr)
    (hh : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ i, c (addr i) = none)
    (rnd : (Fin n → Bit) → C.Party → PrssOutput C E)
    (ready : ∀ vals i, i ∉ D.1 → (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw (ctx i) (elementCodec K) (st i).label 1 count) (LocalSpec C)))).run
        (h, cacheFin addr vals c) = pure (rnd vals i, (h, cacheFin addr vals c)))
    (avoid : ∀ vals i, IsQueryBoundP (next (treeSimCoinWaiting K D count (rnd vals) st k))
      (fun t => t = .inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))) 0) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
      (startSteps worldRoles D
        (fun i => ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= k i) >>= next)).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (Fin n → Bit)
        (fun r : β × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D)
            (next (treeSimCoinWaiting K D count (rnd vals) st k))).run (h, c))] := by
  apply treeSimCheck_world_read_table prims D _ next addr ha hh h c fresh
    (fun vals => treeSimCoinWaiting K D count (rnd vals) st k) _ avoid
  intro vals
  exact treeSimCheck_coin_start_ready prims K D ctx self count st k (rnd vals)
    (h, cacheFin addr vals c) (ready vals)

/-- Decode a family of PRSS field blocks, without identifying their keys or
assuming any algebraic property of the encoding. -/
def treeSimCheckFieldRows (N : Type) (count : ℕ) :
    (N × Fin (elementBits * count) → Bit) ≃ (N → Fin count → E) :=
  (Equiv.curry N (Fin (elementBits * count)) Bit).trans
    (Equiv.arrowCongr (Equiv.refl N) (treeSimCheckFieldTable K count))

/-- Any distinct subset of positions in uniform field rows is a uniform bit
table. In particular unused known-key rows may be sampled and ignored. -/
theorem treeSimCheck_field_rows_uniform [SampleableType E] {N : Type} [Fintype N]
    (count : ℕ) {n : ℕ} (src : Fin n → N × Fin (elementBits * count))
    (hs : Function.Injective src) :
    𝒟[(fun vals : N → Fin count → E =>
      (treeSimCheckFieldRows K N count).symm vals ∘ src) <$> ($ᵗ (N → Fin count → E))] =
        𝒟[$ᵗ (Fin n → Bit)] := by
  have he := evalDist_map_bijective_uniform_cross (α := N → Fin count → E)
    (treeSimCheckFieldRows K N count).symm (treeSimCheckFieldRows K N count).symm.bijective
  have hp := evalDist_uniformSample_map_comp_injective (R := Bit) hs
  rw [bind_pure_comp] at hp
  calc
    _ = 𝒟[(fun bits => bits ∘ src) <$>
        ((treeSimCheckFieldRows K N count).symm <$> ($ᵗ (N → Fin count → E)))] := by
      simp only [Functor.map_map, Function.comp_def]
    _ = _ := by rw [evalDist_map, he, ← evalDist_map]; exact hp

/-- The full named field rows can be sampled before the actual world
program, although only the hidden subset occupies its stream cache. -/
theorem treeSimCheck_world_presample_field_rows [SampleableType E] {N α : Type} [Fintype N]
    (D : C.Coalition) (p : OracleComp (WorldSpec C) α) (count : ℕ)
    {n : ℕ} (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr)
    (src : Fin n → N × Fin (elementBits * count)) (hs : Function.Injective src)
    (hh : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ i, c (addr i) = none) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) p).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (N → Fin count → E)
        (fun r : α × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) p).run
            (h, cacheFin addr ((treeSimCheckFieldRows K N count).symm vals ∘ src) c))] := by
  rw [treeSimCheck_world_presample_table prims D p addr ha hh h c fresh,
    evalDist_bind, ← treeSimCheck_field_rows_uniform K count src hs,
    ← evalDist_bind, bind_map_left]

/-- A joint real PRSS prefix, including repeated reads by its honest holders,
normalizes to independent named field rows with an adaptive continuation. -/
theorem treeSimCheck_world_read_field_rows [SampleableType E] {N α β : Type} [Fintype N]
    (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (k : α → OracleComp (WorldSpec C) β) (count : ℕ)
    {n : ℕ} (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr)
    (src : Fin n → N × Fin (elementBits * count)) (hs : Function.Injective src)
    (hh : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C)
    (fresh : ∀ i, c (addr i) = none) (out : (N → Fin count → E) → α)
    (ready : ∀ vals, (simulateQ (streamWorld prims D) p).run
      (h, cacheFin addr ((treeSimCheckFieldRows K N count).symm vals ∘ src) c) =
      pure (out vals, (h, cacheFin addr ((treeSimCheckFieldRows K N count).symm vals ∘ src) c)))
    (avoid : ∀ vals i, IsQueryBoundP (k (out vals))
      (fun t => t = .inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))) 0) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) (p >>= k)).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (N → Fin count → E)
        (fun r : β × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) (k (out vals))).run (h, c))] := by
  rw [treeSimCheck_world_presample_field_rows prims K D (p >>= k) count addr ha src hs hh h c fresh]
  apply evalDist_bind_congr_all
  intro vals
  simp only [simulateQ_bind, StateT.run_bind, ready, pure_bind]
  rw [treeSimCheck_world_unread_table prims D (k (out vals)) addr
    ((treeSimCheckFieldRows K N count).symm vals ∘ src) (avoid vals)]

abbrev TreeSimCheckPrssIndex (D : C.Coalition) (count : ℕ) :=
  {name : KeyName C // Hidden D name} × Fin (elementBits * count)

def treeSimCheckPrssSource (D : C.Coalition) (count : ℕ) :
    Fin (Fintype.card (TreeSimCheckPrssIndex D count)) → KeyName C × Fin (elementBits * count) :=
  fun i => let a := (Fintype.equivFin (TreeSimCheckPrssIndex D count)).symm i
           (a.1.1, a.2)

theorem treeSimCheckPrssSource_injective (D : C.Coalition) (count : ℕ) :
    Function.Injective (treeSimCheckPrssSource D count) := by
  intro i j he
  apply (Fintype.equivFin (TreeSimCheckPrssIndex D count)).symm.injective
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst he
  · exact congrArg (fun a : KeyName C × Fin (elementBits * count) => a.2) he

def treeSimCheckPrssAddress (D : C.Coalition) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) : Fin (Fintype.card (TreeSimCheckPrssIndex D count)) → HiddenAddress C :=
  fun i => let a := treeSimCheckPrssSource D count i
           ((a.1, keys a.1), label, idx, a.2.val)

theorem treeSimCheckPrssAddress_injective (D : C.Coalition) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) : Function.Injective (treeSimCheckPrssAddress D keys label idx count) := by
  intro i j he
  apply treeSimCheckPrssSource_injective D count
  apply Prod.ext
  · exact congrArg (fun a => a.1.1) he
  · apply Fin.ext
    exact congrArg (fun a => a.2.2.2) he

theorem treeSimCheckPrssAddress_hidden (D : C.Coalition) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) (i : Fin (Fintype.card (TreeSimCheckPrssIndex D count))) :
    Hidden D (treeSimCheckPrssAddress D keys label idx count i).1.1 :=
  ((Fintype.equivFin (TreeSimCheckPrssIndex D count)).symm i).1.2

def treeSimCheckPrssCache (D : C.Coalition) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E) (c : HiddenCache C) : HiddenCache C :=
  cacheFin (treeSimCheckPrssAddress D keys label idx count)
    ((treeSimCheckFieldRows K (KeyName C) count).symm vals ∘ treeSimCheckPrssSource D count) c

/-- Every honest holder reads the same encoded field row at every position
of its hidden named stream. No setup-key entropy assumption is used here. -/
theorem treeSimCheckPrssCache_at (D : C.Coalition) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E) (c : HiddenCache C)
    (name : KeyName C) (hidden : Hidden D name) (g : Fin (elementBits * count)) :
    treeSimCheckPrssCache K D keys label idx count vals c ((name, keys name), label, idx, g.val) =
      some ((treeSimCheckFieldTable K count).symm (vals name) g) := by
  let i := Fintype.equivFin (TreeSimCheckPrssIndex D count) (⟨name, hidden⟩, g)
  have hs : treeSimCheckPrssSource D count i = (name, g) := by
    simp [treeSimCheckPrssSource, i]
  have ha : treeSimCheckPrssAddress D keys label idx count i =
      ((name, keys name), label, idx, g.val) := by
    simp only [treeSimCheckPrssAddress, hs]
  have hc := cacheFin_at (treeSimCheckPrssAddress D keys label idx count)
    (treeSimCheckPrssAddress_injective D keys label idx count)
    ((treeSimCheckFieldRows K (KeyName C) count).symm vals ∘ treeSimCheckPrssSource D count) c i
  rw [ha] at hc
  simp only [Function.comp_apply, hs] at hc
  exact hc

/-- Actual field reads from a populated hidden stream decode to the sampled
field row, including the codec's exact out-of-range padding. -/
theorem treeSimCheck_elementDraw_cached (D : C.Coalition) (name : KeyName C)
    (key : HashOutput) (hidden : Hidden D name) (label idx count : ℕ)
    (vals : Fin count → E) (h : HashCache C) (c : HiddenCache C)
    (ready : ∀ g : Fin (elementBits * count), c ((name, key), label, idx, g.val) =
      some ((treeSimCheckFieldTable K count).symm vals g)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run (h, c) =
        pure (treeSimCheckFieldPad K vals, (h, c)) := by
  rw [treeSimCheck_elementDraw_table]
  simp only [simulateQ_map, StateT.run_map]
  rw [treeSim_hiddenDraws_cached prims D _ (fun _ => hidden) _ h c ready,
    map_pure, Equiv.apply_symm_apply]

/-- Hidden rows are freshly sampled field values. Visible rows use the
actual cached AES key and the actual field decoder. -/
def treeSimCheckPrssRow (D : C.Coalition) (derived : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E) (name : KeyName C) : ℕ → E :=
  if Hidden D name then treeSimCheckFieldPad K (vals name)
  else treeSimElementBlock K count (fun g => prims.aes.eval (truncateHash (derived name)) (label, idx, g))

theorem treeSimCheck_fieldDraw_row (D : C.Coalition) (keys derived : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E) (h : HashCache C) (c : HiddenCache C)
    (name : KeyName C) (visible : ¬ Hidden D name → h (.streamKey (keys name)) = some (derived name)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name (keys name) label idx count) (LocalSpec C)))).run
        (h, treeSimCheckPrssCache K D keys label idx count vals c) =
      pure (treeSimCheckPrssRow prims K D derived label idx count vals name,
        (h, treeSimCheckPrssCache K D keys label idx count vals c)) := by
  by_cases hidden : Hidden D name
  · simp only [treeSimCheckPrssRow, if_pos hidden]
    exact treeSimCheck_elementDraw_cached prims K D name (keys name) hidden label idx count
      (vals name) h _ (treeSimCheckPrssCache_at K D keys label idx count vals c name hidden)
  · simp only [treeSimCheckPrssRow, if_neg hidden]
    apply treeSim_elementDraw_ready prims K D name (keys name) label idx count _ h _
    simp only [TreeSimStreamReady, if_neg hidden]
    exact ⟨derived name, visible hidden, fun _ _ => rfl⟩

def treeSimCheckPrssRows (D : C.Coalition) (derived : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E) (i : C.Party) : PrssOutput C E :=
  (fun T => if i ∈ C.holders T then treeSimCheckPrssRow prims K D derived label idx count vals (.term T)
      else fun _ => 0,
    fun j => if hj : j = i then fun _ => 0 else
      treeSimCheckPrssRow prims K D derived label idx count vals (.pair (C.pairOf i j (Ne.symm hj))))

/-- Concrete field tables and cached visible keys discharge the complete
real PRSS call; there is no whole-draw distribution premise. -/
theorem treeSimCheck_prssDraw_rows (D : C.Coalition) (keys derived : KeyName C → HashOutput)
    (ctx : Context C) (label idx count : ℕ) (vals : KeyName C → Fin count → E)
    (h : HashCache C) (c : HiddenCache C)
    (terms : ∀ T, ctx.self ∈ C.holders T → ctx.prss.term T = keys (.term T))
    (pairs : ∀ j (hj : j ≠ ctx.self), ctx.prss.pair j = keys (.pair (C.pairOf ctx.self j (Ne.symm hj))))
    (visible : ∀ name, name ≠ .parameter → ¬ Hidden D name →
      h (.streamKey (keys name)) = some (derived name)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run
        (h, treeSimCheckPrssCache K D keys label idx count vals c) =
      pure (treeSimCheckPrssRows prims K D derived label idx count vals ctx.self,
        (h, treeSimCheckPrssCache K D keys label idx count vals c)) := by
  let r := fun T => treeSimCheckPrssRow prims K D derived label idx count vals (.term T)
  let z := fun j => if hj : j = ctx.self then (fun _ => 0) else
    treeSimCheckPrssRow prims K D derived label idx count vals (.pair (C.pairOf ctx.self j (Ne.symm hj)))
  have he := treeSim_prssDraw_replay prims D ctx (elementCodec K) label idx count r z
    (h, treeSimCheckPrssCache K D keys label idx count vals c)
  have ht T (hT : ctx.self ∈ C.holders T) : (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw (.term T) (ctx.prss.term T) label idx count) (LocalSpec C)))).run
        (h, treeSimCheckPrssCache K D keys label idx count vals c) =
      pure (r T, (h, treeSimCheckPrssCache K D keys label idx count vals c)) := by
    rw [terms T hT]
    exact treeSimCheck_fieldDraw_row prims K D keys derived label idx count vals h c (.term T)
      (visible _ (by intro he; cases he))
  have hp j (hj : j ≠ ctx.self) : (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) label idx count) (LocalSpec C)))).run
        (h, treeSimCheckPrssCache K D keys label idx count vals c) =
      pure (z j, (h, treeSimCheckPrssCache K D keys label idx count vals c)) := by
    rw [pairs j hj]
    simp only [z, dif_neg hj]
    exact treeSimCheck_fieldDraw_row prims K D keys derived label idx count vals h c _
      (visible _ (by intro he; cases he))
  have result := he ht hp
  rw [result]
  congr 3
  funext j
  by_cases hj : j = ctx.self <;> simp [treeSimCheckPrssRows, z, hj]

/-- The actual joint Coin entry is a fresh family of independent field
rows. Known rows are the actual visible AES streams. Its complete adaptive
continuation and final hash cache are preserved. -/
theorem treeSimCheck_coin_entry_fields [SampleableType E] {α β : Type}
    (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (keys derived : KeyName C → HashOutput) (label count : ℕ)
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (next : (C.Party → Step C E RealSpec α) → OracleComp (WorldSpec C) β)
    (h : HashCache C) (c : HiddenCache C) (fresh : TreeSimFutureEmpty label c)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = keys (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = keys (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (visible : ∀ name, name ≠ .parameter → ¬ Hidden D name →
      h (.streamKey (keys name)) = some (derived name))
    (avoid : ∀ vals : KeyName C → Fin count → E,
      ∀ i : Fin (Fintype.card (TreeSimCheckPrssIndex D count)),
      IsQueryBoundP (next (treeSimCoinWaiting K D count
        (treeSimCheckPrssRows prims K D derived label 1 count vals) st k))
        (fun t => t = .inr (.inr (.inr
          ((treeSimCheckPrssAddress D keys label 1 count i).1.1,
           (treeSimCheckPrssAddress D keys label 1 count i).1.2,
           (treeSimCheckPrssAddress D keys label 1 count i).2)))) 0) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
      (startSteps worldRoles D
        (fun i => ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= k i) >>= next)).run (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        (fun r : β × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D)
            (next (treeSimCoinWaiting K D count
              (treeSimCheckPrssRows prims K D derived label 1 count vals) st k))).run (h, c))] := by
  apply treeSimCheck_world_read_field_rows prims K D _ next count
    (treeSimCheckPrssAddress D keys label 1 count)
    (treeSimCheckPrssAddress_injective D keys label 1 count)
    (treeSimCheckPrssSource D count) (treeSimCheckPrssSource_injective D count)
    (treeSimCheckPrssAddress_hidden D keys label 1 count) h c
    (fun i => fresh _ le_rfl) _ _ avoid
  intro vals
  apply treeSimCheck_coin_start_ready prims K D ctx self count st k
  intro i hi
  rw [labels i hi]
  have hr := treeSimCheck_prssDraw_rows prims K D keys derived (ctx i) label 1 count vals h c
    (terms i hi) (pairs i hi) visible
  simpa only [self i hi, treeSimCheckPrssCache] using hr

def treeSimCheckFieldShift {count : ℕ} (T : C.Term) (delta : Fin count → E) :
    KeyName C → Fin count → E := fun name g => if name = .term T then delta g else 0

theorem treeSimCheck_prssRows_shift (D : C.Coalition) (derived : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E)
    (T₀ : C.Term) (hidden : Hidden D (.term T₀)) (delta : Fin count → E) :
    treeSimCheckPrssRows prims K D derived label idx count (vals + treeSimCheckFieldShift T₀ delta) =
      treeSimCheckCoinShift T₀ delta (treeSimCheckPrssRows prims K D derived label idx count vals) := by
  have other (name : KeyName C) (hne : name ≠ .term T₀) :
      (vals + treeSimCheckFieldShift T₀ delta) name = vals name := by
    funext g
    simp [treeSimCheckFieldShift, hne]
  have row_other (name : KeyName C) (hne : name ≠ .term T₀) :
      treeSimCheckPrssRow prims K D derived label idx count
        (vals + treeSimCheckFieldShift T₀ delta) name =
      treeSimCheckPrssRow prims K D derived label idx count vals name := by
    simp only [treeSimCheckPrssRow, other name hne]
  funext i
  apply Prod.ext
  · funext T g
    by_cases hT : i ∈ C.holders T
    · by_cases he : T = T₀
      · subst T
        simp only [treeSimCheckPrssRows, treeSimCheckCoinShift, if_pos hT, true_and,
          and_self, if_true, treeSimCheckPrssRow, if_pos hidden]
        by_cases hg : g < count <;> simp [treeSimCheckFieldPad, treeSimCheckFieldShift, hg, hT]
      · have hn : KeyName.term T ≠ KeyName.term T₀ := fun h => he (KeyName.term.inj h)
        simp only [treeSimCheckPrssRows, treeSimCheckCoinShift, if_pos hT,
          he, and_false, if_false, add_zero, row_other _ hn]
    · simp [treeSimCheckPrssRows, treeSimCheckCoinShift, hT]
  · funext j
    by_cases hj : j = i
    · simp [treeSimCheckPrssRows, treeSimCheckCoinShift, hj]
    · simp only [treeSimCheckPrssRows, treeSimCheckCoinShift, dif_neg hj]
      exact row_other _ (by intro he; cases he)

/-- Translating one hidden row by an independent vector does not change the
joint distribution of the actual PRSS rows. The continuation is unrestricted. -/
theorem treeSimCheck_prssRows_random_shift [SampleableType E] {α : Type}
    (D : C.Coalition) (derived : KeyName C → HashOutput) (label idx count : ℕ)
    (T₀ : C.Term) (hidden : Hidden D (.term T₀))
    (next : (C.Party → PrssOutput C E) → ProbComp α) :
    𝒟[(do
      let vals ← $ᵗ (KeyName C → Fin count → E)
      next (treeSimCheckPrssRows prims K D derived label idx count vals))] =
      𝒟[(do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        let delta ← $ᵗ (Fin count → E)
        next (treeSimCheckCoinShift T₀ delta
          (treeSimCheckPrssRows prims K D derived label idx count vals)))] := by
  have hdelta (delta : Fin count → E) :
      𝒟[(do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        next (treeSimCheckCoinShift T₀ delta
          (treeSimCheckPrssRows prims K D derived label idx count vals)))] =
      𝒟[(do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        next (treeSimCheckPrssRows prims K D derived label idx count vals))] := by
    simp_rw [← treeSimCheck_prssRows_shift prims K D derived label idx count _ T₀ hidden delta]
    have hu := evalDist_map_bijective_uniform_cross
      (α := KeyName C → Fin count → E)
      (fun vals => vals + treeSimCheckFieldShift T₀ delta)
      (by
        constructor
        · intro a b he
          exact add_right_cancel he
        · intro b
          exact ⟨b - treeSimCheckFieldShift T₀ delta, sub_add_cancel _ _⟩)
    conv_rhs => rw [evalDist_bind, ← hu, ← evalDist_bind, bind_map_left]
  rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  symm
  calc
    _ = 𝒟[($ᵗ (Fin count → E)) >>= fun _ => do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        next (treeSimCheckPrssRows prims K D derived label idx count vals)] :=
      by apply evalDist_bind_congr_all; exact hdelta
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _

/-- One real rushing round driven by an ideal public Coin value. The
reconstructed rows determine exactly the same abort recipients and saved
continuations as the real checked opening. -/
def treeSimCheckCoinPublicRound {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (count : ℕ) (T₀ : C.Term) (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (s : σ) (vals : Fin count → E) :
    ProbComp ((A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × σ) := do
  let delta := vals - treeSimCheckCoinValues K D count rnd
  let shifted := treeSimCheckCoinShift T₀ delta rnd
  let b ← (simulateQ impl (worldRoles.adversary
    (A.round state (treeSimCoinView K D count shifted)))).run s
  let next ← (simulateQ impl (treeSimResumeAll k (fun i =>
    (treeSimCoinOutput K D count shifted b.1.2 i).map
      (fun _ => (List.ofFn vals, nextLabel (st i)))))).run b.2
  pure ((b.1.1, next.1, b.1.2), next.2)

/-- The actual Coin round after joint PRSS sampling has an independent
uniform public value, with selective abort and the same rushing call. -/
theorem treeSimCheck_coin_fields_scheduled [SampleableType E] {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (derived : KeyName C → HashOutput) (label count : ℕ)
    (T₀ : C.Term) (hidden : Hidden D (.term T₀))
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) (s : σ) :
    𝒟[(do
      let rows ← $ᵗ (KeyName C → Fin count → E)
      (simulateQ impl (stepRound worldRoles D A noFunctionality state
        (treeSimCoinWaiting K D count (treeSimCheckPrssRows prims K D derived label 1 count rows) st k))).run s)] =
      𝒟[(do
        let rows ← $ᵗ (KeyName C → Fin count → E)
        let vals ← $ᵗ (Fin count → E)
        treeSimCheckCoinPublicRound K impl D A state count T₀
          (treeSimCheckPrssRows prims K D derived label 1 count rows) st k s vals)] := by
  rw [treeSimCheck_prssRows_random_shift prims K D derived label 1 count T₀ hidden
    (fun rnd => (simulateQ impl (stepRound worldRoles D A noFunctionality state
      (treeSimCoinWaiting K D count rnd st k))).run s)]
  apply evalDist_bind_congr_all
  intro rows
  exact treeSimCheck_coin_scheduled K impl D A state count T₀
    (treeSimCheckPrssRows prims K D derived label 1 count rows) st k (fun _ => s)

def treeSimCheckWorldCell (a : HiddenAddress C) (t : (WorldSpec C).Domain) : Prop :=
  t = .inr (.inr (.inr (a.1.1, a.1.2, a.2)))

def treeSimCheckPartyCell (a : HiddenAddress C) (t : (PartySpec C E RealSpec).Domain) : Prop :=
  t = .inl (.inl (.inr (.inr (a.1.1, a.1.2, a.2))))

def TreeSimCheckStepUnread (a : HiddenAddress C) {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, IsQueryBoundP (resume inbox) (treeSimCheckPartyCell (E := E) a) 0
  | .call input _ => input.elim

/-- Counted adversarial queries never read the free hidden stream table. -/
theorem treeSimCheck_counted_unread {α : Type} (a : HiddenAddress C)
    (p : OracleComp (SimulatorSpec C) α) : IsQueryBoundP (counted p) (treeSimCheckWorldCell a) 0 := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    change IsQueryBoundP (pure x : OracleComp (WorldSpec C) α) (treeSimCheckWorldCell a) 0
    simp
  | query_bind t k ih =>
    rw [counted_bind]
    change IsQueryBoundP (OracleComp.lift ((WorldSpec C).query (.inl t)) >>= fun u => counted (k u))
      (treeSimCheckWorldCell a) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [treeSimCheckWorldCell]), fun u => by
      simpa only [treeSimCheckWorldCell, reduceCtorEq, if_false] using ih u⟩

/-- Advancing a party cannot reintroduce a hidden cell that its entire
remaining program avoids. The suspended continuation retains the same fact. -/
theorem treeSimCheck_advance_unread {α β : Type} (a : HiddenAddress C)
    (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (k : Step C E RealSpec α → OracleComp (WorldSpec C) β) :
    IsQueryBoundP p (treeSimCheckPartyCell (E := E) a) 0 →
    (∀ step, TreeSimCheckStepUnread a step → IsQueryBoundP (k step) (treeSimCheckWorldCell a) 0) →
    IsQueryBoundP (free (advance p) >>= k) (treeSimCheckWorldCell a) 0 := by
  induction p using OracleComp.inductionOn with
  | pure out =>
    intro hp hk
    simp only [advance_pure, free_pure, pure_bind]
    exact hk (.done out) trivial
  | query_bind t f ih =>
    intro hp hk
    rw [isQueryBoundP_query_bind_iff] at hp
    rcases t with (q | outbox) | input
    · rw [advance_query_bind, free_bind, bind_assoc]
      change IsQueryBoundP (OracleComp.lift ((WorldSpec C).query (.inr q)) >>= _)
        (treeSimCheckWorldCell a) 0
      rw [isQueryBoundP_query_bind_iff]
      have hq : ¬ treeSimCheckWorldCell a (.inr q) := by
        intro he
        apply hp.1.resolve_right (by omega)
        unfold treeSimCheckWorldCell at he
        cases he
        rfl
      refine ⟨Or.inl hq, ?_⟩
      intro u
      simp only [if_neg hq]
      apply ih u _ hk
      simpa only [treeSimCheckPartyCell, ite_self, Nat.zero_sub] using hp.2 u
    · change IsQueryBoundP (k (.wait outbox f)) (treeSimCheckWorldCell a) 0
      apply hk
      intro inbox
      simpa [treeSimCheckPartyCell] using hp.2 inbox
    · exact input.elim

/-- Sequential advancement retains the no-reread fact for every honest
continuation, without changing the scheduler's order. -/
theorem treeSimCheck_sequence_advance_unread {α β : Type} (a : HiddenAddress C) :
    ∀ {n : ℕ} (p : Fin n → OracleComp (PartySpec C E RealSpec) (Option α))
      (hp : ∀ i, IsQueryBoundP (p i) (treeSimCheckPartyCell (E := E) a) 0)
      (k : (Fin n → Step C E RealSpec α) → OracleComp (WorldSpec C) β),
      (∀ steps, (∀ i, TreeSimCheckStepUnread a (steps i)) →
        IsQueryBoundP (k steps) (treeSimCheckWorldCell a) 0) →
      IsQueryBoundP ((Concrete.sequenceFin fun i => free (advance (p i))) >>= k)
        (treeSimCheckWorldCell a) 0
  | 0, p, hp, k, hk => by
    simp only [Concrete.sequenceFin, pure_bind]
    exact hk _ (fun i => Fin.elim0 i)
  | n + 1, p, hp, k, hk => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    apply treeSimCheck_advance_unread a (p 0) _ (hp 0)
    intro first hfirst
    apply treeSimCheck_sequence_advance_unread a (fun i : Fin n => p i.succ) (fun i => hp i.succ)
    intro rest hrest
    apply hk
    intro i
    exact Fin.cases hfirst hrest i

theorem treeSimCheck_roundResume_unread {α : Type} (a : HiddenAddress C) (D : C.Coalition)
    (sent : C.Party → Mail C E) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i, TreeSimCheckStepUnread a (steps i)) (i : C.Party) :
    IsQueryBoundP (roundResume D sent steps i) (treeSimCheckPartyCell (E := E) a) 0 := by
  have hi := hs i
  unfold roundResume
  cases he : steps i with
  | done out => simp
  | call input resume => exact input.elim
  | wait out resume =>
    split_ifs
    · simp
    · exact (show ∀ inbox, IsQueryBoundP (resume inbox) (treeSimCheckPartyCell (E := E) a) 0 from
        by simpa only [he, TreeSimCheckStepUnread] using hi) _

theorem treeSimCheck_roundLocal_resume {α : Type} (D : C.Coalition)
    (sent : C.Party → Mail C E) (steps : C.Party → Step C E RealSpec α) (i : C.Party) :
    roundLocal D steps sent i = advance (roundResume D sent steps i) := by
  cases he : steps i with
  | done out => simp only [roundLocal, roundResume, he, advance_pure]
  | call input resume => exact input.elim
  | wait out resume => simp only [roundLocal, roundResume, he]; split_ifs <;> rfl

/-- The complete real scheduler preserves the no-reread condition. Its
adversary may make arbitrary counted queries and choose arbitrary replies. -/
theorem treeSimCheck_rounds_unread {α : Type} (a : HiddenAddress C) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) :
    ∀ (state : A.State) (steps : C.Party → Step C E RealSpec α),
      (∀ i, TreeSimCheckStepUnread a (steps i)) →
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps)
        (treeSimCheckWorldCell a) 0 := by
  induction fuel with
  | zero => intros; simp [executeRounds]
  | succ fuel ih =>
    intro state steps hs
    rw [executeRounds]
    split_ifs
    · simp
    · rw [stepRound_real]
      simp only [bind_assoc, pure_bind, free_sequenceFin]
      dsimp only [worldRoles]
      apply isQueryBoundP_bind (n := 0) (m := 0) (treeSimCheck_counted_unread a _)
      rintro ⟨state', sent⟩ _
      dsimp only
      simp_rw [treeSimCheck_roundLocal_resume]
      apply treeSimCheck_sequence_advance_unread a _
        (treeSimCheck_roundResume_unread a D sent steps hs)
      intro next hnext
      exact ih state' next hnext

/-- A complete phase can forget a previously consumed hidden block once
each actual honest program avoids its positions. -/
theorem treeSimCheck_phase_unread {α : Type} (a : HiddenAddress C) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ i, i ∉ D.1 → IsQueryBoundP (program i).run (treeSimCheckPartyCell (E := E) a) 0) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program)
      (treeSimCheckWorldCell a) 0 := by
  unfold executePhase startSteps
  have he i : (if i ∈ D.1 then pure (.done none) else worldRoles.honest (advance (program i).run)) =
      free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    by_cases hi : i ∈ D.1 <;> simp only [hi, if_true, if_false, advance_pure, free_pure]
    rfl
  simp_rw [he]
  apply treeSimCheck_sequence_advance_unread a
  · intro i
    split_ifs with hi
    · simp
    · exact hp i hi
  · intro steps hs
    exact treeSimCheck_rounds_unread a D A fuel state steps hs

/-- The Coin opening itself reads no PRSS positions after its entry. Only
the actual saved ceremony continuation needs the no-reread invariant. -/
theorem treeSimCheck_coin_waiting_unread {α : Type} (a : HiddenAddress C)
    (D : C.Coalition) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (hk : ∀ i, i ∉ D.1 → ∀ vals,
      IsQueryBoundP (k i (vals, nextLabel (st i))).run (treeSimCheckPartyCell (E := E) a) 0) :
    ∀ i, TreeSimCheckStepUnread a (treeSimCoinWaiting K D count rnd st k i) := by
  intro i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinWaiting, hi, TreeSimCheckStepUnread]
  · simp only [treeSimCoinWaiting, if_neg hi, treeSimCoinStep, TreeSimCheckStepUnread]
    intro inbox
    simp only [exchangeResume, require]
    split_ifs
    all_goals try simp only [OptionT.run_bind, OptionT.run_pure, OptionT.run_failure,
      pure_bind, Option.elimM, failure_bind, OptionT.run_mk]
    all_goals first | exact hk i hi _ | exact isQueryBoundP_pure _ _ _

/-- The no-reread premise of joint Coin sampling follows from the actual
saved party programs, throughout every remaining scheduler round. -/
theorem treeSimCheck_coin_rounds_unread {α : Type} (a : HiddenAddress C)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (fuel count : ℕ) (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (hk : ∀ i, i ∉ D.1 → ∀ vals,
      IsQueryBoundP (k i (vals, nextLabel (st i))).run (treeSimCheckPartyCell (E := E) a) 0) :
    IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state
      (treeSimCoinWaiting K D count rnd st k)) (treeSimCheckWorldCell a) 0 :=
  treeSimCheck_rounds_unread a D A fuel state _ (treeSimCheck_coin_waiting_unread K a D count rnd st k hk)

/-- A run never reads a prior stream label and never decreases its label.
The invariant concerns every raw answer branch, including aborts. -/
def TreeSimCheckRunFuture {α : Type} (p : RunM C E RealSpec α) : Prop :=
  (∀ (a : HiddenAddress C) (st : RunState C), a.2.1 < st.label →
    IsQueryBoundP (p.run st).run (treeSimCheckPartyCell (E := E) a) 0) ∧
  ∀ (st : RunState C) (v : α) (final : RunState C),
    some (v, final) ∈ support (p.run st).run → st.label ≤ final.label

theorem TreeSimCheckRunFuture.pure {α : Type} (v : α) :
    TreeSimCheckRunFuture (pure v : RunM C E RealSpec α) := by
  constructor
  · intros; simp
  · intro st w final hw
    have he : (w, final) = (v, st) := by simpa using hw
    exact le_of_eq (congrArg (fun p => p.2.label) he).symm

theorem TreeSimCheckRunFuture.bind {α β : Type}
    {p : RunM C E RealSpec α} {f : α → RunM C E RealSpec β}
    (hp : TreeSimCheckRunFuture p) (hf : ∀ v, TreeSimCheckRunFuture (f v)) :
    TreeSimCheckRunFuture (p >>= f) := by
  constructor
  · intro a st ha
    simp only [StateT.run_bind, OptionT.run_bind]
    apply isQueryBoundP_bind (n := 0) (m := 0) (hp.1 a st ha)
    intro out hout
    cases out with
    | none => simp [Option.elimM]
    | some pair =>
      exact (hf pair.1).1 a pair.2 (ha.trans_le (hp.2 st pair.1 pair.2 hout))
  · intro st v final hv
    simp only [StateT.run_bind] at hv
    obtain ⟨mid, hm, ht⟩ := treeSimCheck_some_bind _ _ _ hv
    exact (hp.2 st mid.1 mid.2 hm).trans ((hf mid.1).2 mid.2 v final ht)

theorem TreeSimCheckRunFuture.map {α β : Type} {p : RunM C E RealSpec α}
    (hp : TreeSimCheckRunFuture p) (f : α → β) : TreeSimCheckRunFuture (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact hp.bind fun _ => .pure _

theorem TreeSimCheckRunFuture.mapM {α β : Type} (xs : List α)
    (f : α → RunM C E RealSpec β) (hf : ∀ x ∈ xs, TreeSimCheckRunFuture (f x)) :
    TreeSimCheckRunFuture (xs.mapM f) := by
  induction xs with
  | nil => exact .pure []
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact (hf x (by simp)).bind fun _ =>
      (ih (fun y hy => hf y (by simp [hy]))).bind fun _ => .pure _

theorem TreeSimCheckRunFuture.foldlM {α β : Type} (xs : List α)
    (f : β → α → RunM C E RealSpec β)
    (hf : ∀ b x, x ∈ xs → TreeSimCheckRunFuture (f b x)) (initial : β) :
    TreeSimCheckRunFuture (xs.foldlM f initial) := by
  induction xs generalizing initial with
  | nil => exact .pure initial
  | cons x xs ih =>
    simp only [List.foldlM_cons]
    exact (hf initial x (by simp)).bind fun b => ih (fun b x hx => hf b x (by simp [hx])) b

theorem treeSimCheckRunFuture_lift {α : Type} (p : PartyM C E RealSpec α)
    (hp : ∀ a : HiddenAddress C, IsQueryBoundP p.run (treeSimCheckPartyCell (E := E) a) 0) :
    TreeSimCheckRunFuture (StateT.lift p) := by
  constructor
  · intro a st ha
    simp only [StateT.run_lift, OptionT.run_bind]
    apply isQueryBoundP_bind (n := 0) (m := 0) (hp a)
    intro out hout
    cases out <;> exact isQueryBoundP_pure _ _ _
  · intro st v final hv
    simp only [StateT.run_lift] at hv
    obtain ⟨out, hout, he⟩ := treeSimCheck_some_bind _ _ _ hv
    have he' : final = st := by
      have : (v, final) = (out, st) := by simpa using he
      exact congrArg Prod.snd this
    rw [he']

theorem treeSimCheckRunFuture_modifyGet {α : Type} (f : RunState C → α × RunState C)
    (hf : ∀ st, st.label ≤ (f st).2.label) :
    TreeSimCheckRunFuture (modifyGet f : RunM C E RealSpec α) := by
  constructor
  · intros; simp
  · intro st v final hv
    have he : (v, final) = f st := by simpa using hv
    rw [show final = (f st).2 from congrArg Prod.snd he]
    exact hf st

def treeSimCheckRoCell (a : HiddenAddress C) (t : (RoSpec C).Domain) : Prop :=
  t = .inr (a.1.1, a.1.2, a.2)

theorem treeSimCheck_oracleStep_unread {α : Type} (a : HiddenAddress C)
    (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p (treeSimCheckRoCell a) 0) :
    IsQueryBoundP (oracleStep p : PartyM C E RealSpec α).run (treeSimCheckPartyCell (E := E) a) 0 := by
  unfold oracleStep localStep
  change IsQueryBoundP (some <$> liftComp (liftComp p (LocalSpec C)) (PartySpec C E RealSpec)) _ 0
  rw [isQueryBoundP_map_iff]
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    simp only [liftComp_bind]
    have he : liftComp (liftComp (liftM ((RoSpec C).query t) : OracleComp (RoSpec C) _) (LocalSpec C))
        (PartySpec C E RealSpec) =
      (liftM ((PartySpec C E RealSpec).query (.inl (.inl (.inr t)))) : OracleComp (PartySpec C E RealSpec) _) := by
      rcases t with q | p <;> rfl
    rw [he]
    erw [isQueryBoundP_query_bind_iff]
    have hn : ¬ treeSimCheckRoCell a t := hp.1.resolve_right (by omega)
    constructor
    · simpa [treeSimCheckPartyCell, treeSimCheckRoCell] using hn
    · intro u
      simpa only [Nat.zero_sub, ite_self] using ih u (by simpa only [Nat.zero_sub, ite_self] using hp.2 u)

theorem treeSimCheck_prgBits_unread (a : HiddenAddress C) (name : KeyName C) (key : HashOutput)
    (label idx count : ℕ) (hne : label ≠ a.2.1) :
    IsQueryBoundP (prgBits name key label idx count) (treeSimCheckRoCell a) 0 := by
  unfold prgBits
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · have hm := queryBound_mapM (treeSimCheckRoCell a)
      (fun g => (query (spec := RoSpec C) (.inr (name, key, label, idx, g)) : OracleComp (RoSpec C) Bit))
      0 (List.range count) (fun g hg => ?_)
    · simpa using hm
    · change IsQueryBoundP (liftM ((RoSpec C).query (.inr (name, key, label, idx, g)))) _ 0
      rw [isQueryBoundP_query_iff]
      intro he
      have hi : (name, key, label, idx, g) = (a.1.1, a.1.2, a.2) := Sum.inr.inj he
      exact (hne (congrArg (fun x : PrgInput C => x.2.2.1) hi)).elim
  · intros; simp

theorem treeSimCheck_elementDraw_unread (a : HiddenAddress C) (name : KeyName C) (key : HashOutput)
    (label idx count : ℕ) (hne : label ≠ a.2.1) :
    IsQueryBoundP ((elementCodec K).draw name key label idx count) (treeSimCheckRoCell a) 0 := by
  dsimp only [elementCodec]
  apply isQueryBoundP_bind (n := 0) (m := 0) (treeSimCheck_prgBits_unread a name key label idx _ hne)
  intros; simp

theorem treeSimCheck_prssDraw_unread {R : Type} [Zero R] (a : HiddenAddress C)
    (ctx : Context C) (codec : Codec C E R) (label idx count : ℕ)
    (draw : ∀ name key, IsQueryBoundP (codec.draw name key label idx count) (treeSimCheckRoCell a) 0) :
    IsQueryBoundP (prssDraw ctx codec label idx count) (treeSimCheckRoCell a) 0 := by
  have ht : IsQueryBoundP (termDraws ctx codec label idx count) (treeSimCheckRoCell a) 0 := by
    unfold termDraws
    have hm := queryBound_mapM (treeSimCheckRoCell a)
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure (fun _ => 0)) 0 C.terms (fun T hT => ?_)
    · simpa using hm
    · split_ifs
      · exact draw _ _
      · simp
  have hp : IsQueryBoundP (pairDraws ctx codec label idx count) (treeSimCheckRoCell a) 0 := by
    unfold pairDraws
    have hm := queryBound_mapM (treeSimCheckRoCell a)
      (fun j => if hj : j = ctx.self then pure (fun _ => 0) else
        codec.draw (.pair (C.pairOf ctx.self j (Ne.symm hj))) (ctx.prss.pair j) label idx count)
      0 C.parties (fun j hj => ?_)
    · simpa using hm
    · split_ifs
      · simp
      · exact draw _ _
  unfold prssDraw
  apply isQueryBoundP_bind (n := 0) (m := 0) ht
  intro _ _
  apply isQueryBoundP_bind (n := 0) (m := 0) hp
  intros; simp

/-- Every real PRSS invocation reads only its current label and increments
that label. This holds for either codec and all possible returned values. -/
theorem treeSimCheckRunFuture_prss {R : Type} [Zero R]
    (ctx : Context C) (codec : Codec C E R) (idx count : ℕ)
    (draw : ∀ (a : HiddenAddress C) name key label, a.2.1 < label →
      IsQueryBoundP (codec.draw name key label idx count) (treeSimCheckRoCell a) 0) :
    TreeSimCheckRunFuture (prssRandomness (G := RealSpec) ctx codec idx count) := by
  constructor
  · intro a st ha
    rw [realRand_run]
    simp only [OptionT.run_bind]
    apply isQueryBoundP_bind (n := 0) (m := 0)
      (treeSimCheck_oracleStep_unread a _
        (treeSimCheck_prssDraw_unread a ctx codec st.label idx count (fun name key => draw a name key st.label ha)))
    intro out hout
    cases out <;> exact isQueryBoundP_pure _ _ _
  · intro st v final hv
    rw [realRand_run] at hv
    obtain ⟨rnd, hrnd, hfinal⟩ := treeSimCheck_some_bind _ _ _ hv
    have he : (v, final) = (rnd, nextLabel st) := by simpa using hfinal
    rw [show final = nextLabel st from congrArg Prod.snd he]
    simp [nextLabel]

theorem treeSimCheck_party_bind_unread {α β : Type} (a : HiddenAddress C)
    (p : PartyM C E RealSpec α) (f : α → PartyM C E RealSpec β)
    (hp : IsQueryBoundP p.run (treeSimCheckPartyCell (E := E) a) 0)
    (hf : ∀ v, IsQueryBoundP (f v).run (treeSimCheckPartyCell (E := E) a) 0) :
    IsQueryBoundP (p >>= f).run (treeSimCheckPartyCell (E := E) a) 0 := by
  simp only [OptionT.run_bind]
  apply isQueryBoundP_bind (n := 0) (m := 0) hp
  intro out hout
  cases out with
  | none => exact isQueryBoundP_pure _ _ _
  | some v => exact hf v

theorem treeSimCheck_require_unread (a : HiddenAddress C) (p : Prop) :
    IsQueryBoundP (require p : PartyM C E RealSpec Unit).run (treeSimCheckPartyCell (E := E) a) 0 := by
  unfold require
  split_ifs <;> exact isQueryBoundP_pure _ _ _

theorem treeSimCheck_exchange_unread (a : HiddenAddress C) (outbox : Mail C E) :
    IsQueryBoundP (exchange outbox : PartyM C E RealSpec (Mail C E)).run
      (treeSimCheckPartyCell (E := E) a) 0 := by
  unfold exchange
  apply treeSimCheck_party_bind_unread a
  · change IsQueryBoundP (some <$> (liftM ((PartySpec C E RealSpec).query (.inl (.inr outbox))))) _ 0
    rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    simp [treeSimCheckPartyCell]
  · intro inbox
    split_ifs <;> exact isQueryBoundP_pure _ _ _

theorem treeSimCheck_hash_unread (a : HiddenAddress C) (q : Query C) :
    IsQueryBoundP (hashQuery q) (treeSimCheckRoCell a) 0 := by
  change IsQueryBoundP (liftM ((RoSpec C).query (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [treeSimCheckRoCell]

theorem treeSimCheck_openSh_unread (a : HiddenAddress C) (ctx : Context C)
    (v : ℕ → E) (count : ℕ) :
    IsQueryBoundP (openSh K ctx v count : PartyM C E RealSpec (ℕ → E)).run
      (treeSimCheckPartyCell (E := E) a) 0 := by
  unfold openSh
  apply treeSimCheck_party_bind_unread a _ _ (treeSimCheck_exchange_unread a _)
  intro inbox
  apply treeSimCheck_party_bind_unread a _ _ (treeSimCheck_require_unread a _)
  intro _
  exact isQueryBoundP_pure _ _ _

theorem treeSimCheckRunFuture_get : TreeSimCheckRunFuture (get : RunM C E RealSpec (RunState C)) :=
  treeSimCheckRunFuture_modifyGet (fun st => (st, st)) (fun _ => le_rfl)

theorem treeSimCheckRunFuture_record {R : Type} (ctx : Context C) (codec : Codec C E R)
    (mode : ReshareMode) (z : Shares C R) (count : ℕ) :
    TreeSimCheckRunFuture (record (G := RealSpec) K ctx codec mode z count) := by
  unfold record
  apply treeSimCheckRunFuture_modifyGet
  intro st
  exact le_rfl

theorem treeSimCheckRunFuture_reshare {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    TreeSimCheckRunFuture (reshare (G := RealSpec) K ctx codec randomness v count) := by
  unfold reshare
  dsimp only
  apply TreeSimCheckRunFuture.bind (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_exchange_unread a _))
  intro inbox
  exact (treeSimCheckRunFuture_record K ctx codec .peer _ count).bind fun _ => .pure _

theorem treeSimCheckRunFuture_coinWith (ctx : Context C) (rnd : PrssOutput C E) (count : ℕ) :
    TreeSimCheckRunFuture (coinWith (G := RealSpec) K ctx rnd count) := by
  unfold coinWith
  exact (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_openSh_unread K a ctx _ count)).bind fun _ => .pure _

theorem treeSimCheckRunFuture_coin (ctx : Context C) (count : ℕ) :
    TreeSimCheckRunFuture ((realCheckGadgets (G := RealSpec) K ctx).coin count) := by
  unfold realCheckGadgets
  dsimp only
  apply TreeSimCheckRunFuture.bind (treeSimCheckRunFuture_prss ctx (elementCodec K) 1 count
    (fun a name key label hl => treeSimCheck_elementDraw_unread K a name key label 1 count (Ne.symm (ne_of_lt hl))))
  intro rnd
  exact treeSimCheckRunFuture_coinWith K ctx rnd count

theorem treeSimCheckRunFuture_extendMult (ctx : Context C) (products : List (Product C E)) :
    TreeSimCheckRunFuture ((realCheckGadgets (G := RealSpec) K ctx).extendMult products) := by
  unfold realCheckGadgets
  dsimp only
  apply TreeSimCheckRunFuture.bind (treeSimCheckRunFuture_prss ctx (elementCodec K) 0 products.length
    (fun a name key label hl => treeSimCheck_elementDraw_unread K a name key label 0 products.length (Ne.symm (ne_of_lt hl))))
  intro rnd
  exact treeSimCheckRunFuture_reshare K ctx (elementCodec K) rnd _ _

theorem treeSimCheck_ro_mapM_unread {α β : Type} (a : HiddenAddress C) (xs : List α)
    (f : α → OracleComp (RoSpec C) β)
    (hf : ∀ x ∈ xs, IsQueryBoundP (f x) (treeSimCheckRoCell a) 0) :
    IsQueryBoundP (xs.mapM f) (treeSimCheckRoCell a) 0 := by
  simpa only [Nat.mul_zero] using queryBound_mapM (treeSimCheckRoCell a) f 0 xs hf

theorem treeSimCheckRunFuture_oracle {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : ∀ a, IsQueryBoundP p (treeSimCheckRoCell a) 0) :
    TreeSimCheckRunFuture (StateT.lift (oracleStep p) : RunM C E RealSpec α) :=
  treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_oracleStep_unread a p (hp a))

theorem treeSimCheckRunFuture_coinKey (gadgets : CheckGadgets C E RealSpec)
    (hc : ∀ count, TreeSimCheckRunFuture (gadgets.coin count)) :
    TreeSimCheckRunFuture (coinKey K gadgets) := by
  unfold coinKey
  apply treeSimCheckRunFuture_get.bind
  intro st
  apply (hc 1).bind
  intro vals
  exact treeSimCheckRunFuture_oracle _ (fun a => treeSimCheck_hash_unread a _)

theorem treeSimCheckRunFuture_expand (key : HashOutput) (count : ℕ) :
    TreeSimCheckRunFuture (expand (G := RealSpec) K key count) := by
  unfold expand
  apply treeSimCheckRunFuture_oracle
  intro a
  apply treeSimCheck_ro_mapM_unread
  intro g hg
  rw [isQueryBoundP_map_iff]
  exact treeSimCheck_hash_unread a _

theorem treeSimCheck_findChallenge_unread (a : HiddenAddress C) (key : HashOutput) :
    ∀ tries index, IsQueryBoundP (findChallenge K key tries index) (treeSimCheckRoCell a) 0
  | 0, index => by simp [findChallenge]
  | tries + 1, index => by
    rw [findChallenge]
    apply isQueryBoundP_bind (n := 0) (m := 0) (treeSimCheck_hash_unread a _)
    intro value hvalue
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact treeSimCheck_findChallenge_unread a key tries (index + 1)

theorem treeSimCheckRunFuture_challenge (gadgets : CheckGadgets C E RealSpec)
    (hc : ∀ count, TreeSimCheckRunFuture (gadgets.coin count)) :
    TreeSimCheckRunFuture (challenge K gadgets) := by
  unfold challenge
  apply (treeSimCheckRunFuture_coinKey K gadgets hc).bind
  intro key
  apply (treeSimCheckRunFuture_oracle (findChallenge K key challengeTries 0)
    (fun a => treeSimCheck_findChallenge_unread K a key _ _)).bind
  intro value
  cases value with
  | none => exact treeSimCheckRunFuture_lift _ (fun _ => isQueryBoundP_pure _ _ _)
  | some value => exact .pure value

theorem treeSimCheckRunFuture_compareDigests (ctx : Context C) (salts : Shares C Bit) :
    TreeSimCheckRunFuture (compareDigests (E := E) (G := RealSpec) ctx salts) := by
  unfold compareDigests
  dsimp only
  apply treeSimCheckRunFuture_get.bind
  intro st
  apply TreeSimCheckRunFuture.bind
  · apply treeSimCheckRunFuture_oracle
    intro a
    apply treeSimCheck_ro_mapM_unread
    intro T hT
    split_ifs
    · apply isQueryBoundP_bind (n := 0) (m := 0) (treeSimCheck_hash_unread a _)
      intro _ _
      exact treeSimCheck_hash_unread a _
    · exact isQueryBoundP_pure _ _ _
  · intro digests
    apply (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_exchange_unread a _)).bind
    intro inbox
    exact treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_require_unread a _)

/-- Every stage of the GS20 check respects the increasing stream labels,
including the folds, randomization, digest comparison, and final opening. -/
theorem treeSimCheckRunFuture_check (ctx : Context C) (gadgets : CheckGadgets C E RealSpec)
    (tuples : List (Tuple C))
    (hc : ∀ n, TreeSimCheckRunFuture (gadgets.coin n))
    (hm : ∀ products, TreeSimCheckRunFuture (gadgets.extendMult products))
    (he : ∀ n, TreeSimCheckRunFuture (gadgets.randElements n))
    (hb : ∀ n, TreeSimCheckRunFuture (gadgets.randBits n)) :
    TreeSimCheckRunFuture (check K ctx gadgets tuples) := by
  unfold check
  dsimp only
  split_ifs
  · exact .pure ()
  · simp only [pure_bind]
    apply (treeSimCheckRunFuture_coinKey K gadgets hc).bind
    intro key
    apply (treeSimCheckRunFuture_expand K key _).bind
    intro tau
    apply (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_require_unread a _)).bind
    intro _
    apply TreeSimCheckRunFuture.bind
    · apply TreeSimCheckRunFuture.foldlM
      intro state j hj
      rcases state with ⟨xs, ys, claim⟩
      dsimp only
      apply (hm _).bind
      intro product
      apply (treeSimCheckRunFuture_challenge K gadgets hc).bind
      intro r
      exact .pure _
    · rintro ⟨xs, ys, claim⟩
      dsimp only
      apply TreeSimCheckRunFuture.bind
      · apply TreeSimCheckRunFuture.foldlM
        intro state j hj
        rcases state with ⟨av, bv, claim⟩
        dsimp only
        apply (hm _).bind
        intro product
        apply (treeSimCheckRunFuture_challenge K gadgets hc).bind
        intro r
        exact .pure _
      · rintro ⟨av, bv, claim⟩
        dsimp only
        apply (he 2).bind
        intro masks
        apply (hm _).bind
        intro product
        apply (hb 256).bind
        intro salts
        apply (treeSimCheckRunFuture_compareDigests ctx salts.1).bind
        intro _
        apply (treeSimCheckRunFuture_challenge K gadgets hc).bind
        intro r
        apply (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_openSh_unread K a ctx _ 3)).bind
        intro opened
        exact treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_require_unread a _)

theorem treeSimCheckRunFuture_realCheck (ctx : Context C) (tuples : List (Tuple C)) :
    TreeSimCheckRunFuture (check K ctx (realCheckGadgets K ctx) tuples) := by
  apply treeSimCheckRunFuture_check K ctx _ tuples
  · exact treeSimCheckRunFuture_coin K ctx
  · exact treeSimCheckRunFuture_extendMult K ctx
  · intro n
    exact treeSimCheckRunFuture_prss ctx (elementCodec K) 1 n
      (fun a name key label hl => treeSimCheck_elementDraw_unread K a name key label 1 n (Ne.symm (ne_of_lt hl)))
  · intro n
    exact treeSimCheckRunFuture_prss ctx bitCodec 2 n
      (fun a name key label hl => treeSimCheck_prgBits_unread a name key label 2 n (Ne.symm (ne_of_lt hl)))

theorem treeSimCheckRunFuture_sliceStep (ctx : Context C) (tau : List E) (count j : ℕ)
    (p : Shares C E × Shares C E × E) :
    TreeSimCheckRunFuture (sliceStep K ctx (realCheckGadgets K ctx) tau count p j) := by
  rcases p with ⟨xs, ys, claim⟩
  unfold sliceStep
  dsimp only
  apply (treeSimCheckRunFuture_extendMult K ctx _).bind
  intro products
  apply (treeSimCheckRunFuture_challenge K _ (treeSimCheckRunFuture_coin K ctx)).bind
  intro r
  exact .pure _

theorem treeSimCheckRunFuture_halvingStep (ctx : Context C) (width j : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) :
    TreeSimCheckRunFuture (halvingStep K ctx (realCheckGadgets K ctx) width p j) := by
  rcases p with ⟨av, bv, claim⟩
  unfold halvingStep
  dsimp only
  apply (treeSimCheckRunFuture_extendMult K ctx _).bind
  intro products
  apply (treeSimCheckRunFuture_challenge K _ (treeSimCheckRunFuture_coin K ctx)).bind
  intro r
  exact .pure _

theorem treeSimCheckRunFuture_finalStep (ctx : Context C) (p : (ℕ → E) × (ℕ → E) × E) :
    TreeSimCheckRunFuture (finalStep K ctx (realCheckGadgets K ctx) p) := by
  rcases p with ⟨av, bv, claim⟩
  unfold finalStep
  dsimp only
  apply TreeSimCheckRunFuture.bind
  · exact treeSimCheckRunFuture_prss ctx (elementCodec K) 1 2
      (fun a name key label hl => treeSimCheck_elementDraw_unread K a name key label 1 2 (Ne.symm (ne_of_lt hl)))
  · intro masks
    apply (treeSimCheckRunFuture_extendMult K ctx _).bind
    intro products
    apply TreeSimCheckRunFuture.bind
    · exact treeSimCheckRunFuture_prss ctx bitCodec 2 256
        (fun a name key label hl => treeSimCheck_prgBits_unread a name key label 2 256 (Ne.symm (ne_of_lt hl)))
    · intro salts
      apply (treeSimCheckRunFuture_compareDigests ctx salts.1).bind
      intro _
      apply (treeSimCheckRunFuture_challenge K _ (treeSimCheckRunFuture_coin K ctx)).bind
      intro r
      apply (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_openSh_unread K a ctx _ 3)).bind
      intro opened
      exact treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_require_unread a _)

/-- The real GS20 program after its first Coin, with the original absolute
label used only in the coin-key hash. -/
def treeSimCheckAfterCoin (ctx : Context C) (tuples : List (Tuple C))
    (tag label : ℕ) (values : List E) : RunM C E RealSpec Unit := do
  let key ← StateT.lift (oracleStep (hashQuery (.coinKey tag label
    (values.flatMap fun v => List.ofFn (K.encode v)))))
  let count := (tuples.map (·.count)).sum
  let tau ← expand K key (coins count)
  StateT.lift (require (∀ b < sliceBits, tau.getD b 0 ≠ 0))
  let p ← (List.range sliceBits).foldlM (sliceStep K ctx (realCheckGadgets K ctx) tau count)
    ((fun T g => wordWeightOf K tau count g * liftedPart tuples (·.x) T g), liftedPart tuples (·.y),
      conv K ctx (claimOf K tau count (liftedPart tuples (·.z))) 0)
  let p' ← (List.range (halvings count - sliceBits)).foldlM
    (halvingStep K ctx (realCheckGadgets K ctx) (sliceWidth count))
    (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
  finalStep K ctx (realCheckGadgets K ctx) p'

theorem treeSimCheck_first_coin (ctx : Context C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) (st : RunState C) :
    (check K ctx (realCheckGadgets K ctx) tuples).run st =
      ((realCheckGadgets K ctx).coin 1).run st >>= fun out =>
        (treeSimCheckAfterCoin K ctx tuples st.tag st.label out.1).run out.2 := by
  rw [check_eq K ctx (realCheckGadgets K ctx) tuples nonzero]
  simp only [coinKey, treeSimCheckAfterCoin, StateT.run_bind,
    StateT.run_get, StateT.run_lift, pure_bind, bind_assoc]

theorem treeSimCheckAfterCoin_future (ctx : Context C) (tuples : List (Tuple C))
    (tag label : ℕ) (values : List E) :
    TreeSimCheckRunFuture (treeSimCheckAfterCoin K ctx tuples tag label values) := by
  unfold treeSimCheckAfterCoin
  apply (treeSimCheckRunFuture_oracle _ (fun a => treeSimCheck_hash_unread a _)).bind
  intro key
  apply (treeSimCheckRunFuture_expand K key _).bind
  intro tau
  apply (treeSimCheckRunFuture_lift _ (fun a => treeSimCheck_require_unread a _)).bind
  intro _
  apply TreeSimCheckRunFuture.bind
  · exact TreeSimCheckRunFuture.foldlM _ _ (fun p j _ => treeSimCheckRunFuture_sliceStep K ctx tau _ j p) _
  · intro p
    apply TreeSimCheckRunFuture.bind
    · exact TreeSimCheckRunFuture.foldlM _ _ (fun p j _ => treeSimCheckRunFuture_halvingStep K ctx _ j p) _
    · exact treeSimCheckRunFuture_finalStep K ctx

def treeSimCheckFirstContinuation (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) (out : List E × RunState C) : PartyM C E RealSpec Unit :=
  (treeSimCheckAfterCoin K ctx tuples st.tag st.label out.1).run' out.2

theorem treeSimCheck_first_coin_run' (ctx : Context C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) (st : RunState C) :
    (check K ctx (realCheckGadgets K ctx) tuples).run' st =
      ((realCheckGadgets K ctx).coin 1).run st >>= treeSimCheckFirstContinuation K ctx tuples st := by
  rw [StateT.run'_eq, treeSimCheck_first_coin K ctx tuples nonzero st]
  simp only [treeSimCheckFirstContinuation, StateT.run'_eq, map_bind]
  rfl

theorem treeSimCheckFirstContinuation_unread (a : HiddenAddress C)
    (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C)
    (ha : a.2.1 ≤ st.label) (values : List E) :
    IsQueryBoundP (treeSimCheckFirstContinuation K ctx tuples st (values, nextLabel st)).run
      (treeSimCheckPartyCell (E := E) a) 0 := by
  have h := (treeSimCheckAfterCoin_future K ctx tuples st.tag st.label values).1 a (nextLabel st)
    (by simpa only [nextLabel] using Nat.lt_succ_of_le ha)
  simpa only [treeSimCheckFirstContinuation, StateT.run'_eq, OptionT.run_map,
    isQueryBoundP_map_iff] using h

/-- Exact distributional normalization at the first Coin of the complete
real check. Readiness and no-reread are proved from concrete setup keys,
cached AES keys, and the actual check program; no hybrid-check premise is
assumed. The final hash cache is retained for the fixed collision event. -/
theorem treeSimCheck_real_check_first_fields [SampleableType E]
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (fuel : ℕ) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (tuples : C.Party → List (Tuple C))
    (nonzero : ∀ i, i ∉ D.1 → ((tuples i).map (·.count)).sum ≠ 0)
    (keys derived : KeyName C → HashOutput) (label : ℕ)
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (h : HashCache C) (c : HiddenCache C) (fresh : TreeSimFutureEmpty label c)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = keys (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = keys (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (visible : ∀ name, name ≠ .parameter → ¬ Hidden D name →
      h (.streamKey (keys name)) = some (derived name)) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run' (st i)))).run (h, c)] =
      𝒟[(do
        let rows ← $ᵗ (KeyName C → Fin 1 → E)
        (fun r : (A.State × (C.Party → Option Unit)) × (HashCache C × HiddenCache C) => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D)
            (executeRounds worldRoles D A noFunctionality fuel state
              (treeSimCoinWaiting K D 1 (treeSimCheckPrssRows prims K D derived label 1 1 rows) st
                (fun i => treeSimCheckFirstContinuation K (ctx i) (tuples i) (st i))))).run (h, c))] := by
  have he : startSteps worldRoles D
      (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run' (st i)) =
      startSteps worldRoles D (fun i => ((realCheckGadgets K (ctx i)).coin 1).run (st i) >>=
        treeSimCheckFirstContinuation K (ctx i) (tuples i) (st i)) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi, treeSimCheck_first_coin_run' K (ctx i) (tuples i) (nonzero i hi) (st i)]
  unfold executePhase
  rw [he]
  apply treeSimCheck_coin_entry_fields prims K D ctx self keys derived label 1 st labels _ _ h c fresh terms pairs visible
  intro rows index
  have hnext := treeSimCheck_coin_rounds_unread K
    (treeSimCheckPrssAddress D keys label 1 1 index) D A state fuel 1
    (treeSimCheckPrssRows prims K D derived label 1 1 rows) st
    (fun i => treeSimCheckFirstContinuation K (ctx i) (tuples i) (st i)) (by
      intro i hi values
      apply treeSimCheckFirstContinuation_unread K _ (ctx i) (tuples i) (st i) _ values
      change label ≤ (st i).label
      rw [labels i hi])
  exact (isQueryBoundP_congr_pred
    (p := treeSimCheckWorldCell (treeSimCheckPrssAddress D keys label 1 1 index))
    (p' := fun t => t = .inr (.inr (.inr
      ((treeSimCheckPrssAddress D keys label 1 1 index).1.1,
       (treeSimCheckPrssAddress D keys label 1 1 index).1.2,
       (treeSimCheckPrssAddress D keys label 1 1 index).2))))
    (fun _ => Iff.rfl)).mp hnext

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_world_presample_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_world_presample_table
/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_coin_fields_scheduled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_coin_fields_scheduled
/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckRunFuture_realCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheckRunFuture_realCheck
/-- info: 'ThresholdLeanXmssSecurity.treeSimCheck_real_check_first_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCheck_real_check_first_fields

end ThresholdLeanXmssSecurity
