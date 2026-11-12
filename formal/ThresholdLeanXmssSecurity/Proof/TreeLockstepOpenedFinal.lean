import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedRest
import ThresholdLeanXmssSecurity.Proof.TreeLockstepEncoding
import ThresholdLeanXmssSecurity.Proof.TreeCheckCutParts

/-!
# Opening agreement in the original audited ceremony

`treeLockstepOpenedGoal` proves the exact `TreeLockstepOpenedGoal`, and
`treeLockstepRecordsAgreeGoal` derives its successful-record schedule corollary.
There is no additional premise for these two goals. The successful-record scope
does not claim coverage of aborted prefixes.

Actual joint batch cuts supply the contexts, absolute labels, counts, histories
and PRSS cache readiness. Synchronized opening continuations then use one common
output while preserving the entire supported result. Pending local gates retain
copy hashes and aborts in scheduler order. Induction through the batch lists and
the actual public selection fixes the second run's jobs. Setup agreement and
hash coherence come from the original execution and its retained log.

The pinned and current leanVM cache replay proofs were searched. Their concrete
hash-cache lemmas do not apply to the separate hidden-stream table; this module
reuses VCV's caching monotonicity and the existing logged-run replay instead.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- A stream answer is determined by its actual hidden entry or its public
derived AES key. This includes the absolute label and the stream index. -/
def TreeLockstepStreamAnswer (prims : Primitives) (D : C.Coalition)
    (s : HashCache C × HiddenCache C) (x : PrgInput C) (u : Bit) : Prop :=
  if Hidden D x.1 then s.2 ((x.1, x.2.1), x.2.2) = some u
  else ∃ derived, s.1 (.streamKey x.2.1) = some derived ∧
    u = prims.aes.eval (truncateHash derived) x.2.2

theorem treeLockstep_streamAnswer_mono (prims : Primitives) (D : C.Coalition)
    {s t : HashCache C × HiddenCache C} (hash : s.1 ≤ t.1) (hidden : s.2 ≤ t.2)
    {x : PrgInput C} {u : Bit} (h : TreeLockstepStreamAnswer prims D s x u) :
    TreeLockstepStreamAnswer prims D t x u := by
  unfold TreeLockstepStreamAnswer at h ⊢
  split_ifs at h ⊢ with hx
  · exact hidden h
  · obtain ⟨derived, cached, value⟩ := h
    exact ⟨derived, hash cached, value⟩

/-- Every world call preserves all already sampled hidden stream bits. -/
theorem treeLockstep_world_hidden_grows (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (r : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (run : r ∈ support ((streamWorld prims D t).run s)) : s.2 ≤ r.2.2 := by
  have onhash {α : Type} (m : StateT (HashCache C) ProbComp α)
      (r : α × (HashCache C × HiddenCache C))
      (h : r ∈ support ((onHash m).run s)) : s.2 ≤ r.2.2 := by
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at h
    obtain ⟨u, _, rfl⟩ := h
    exact le_rfl
  rcases t with ((u | q | x) | p) | (u | q | x)
  · exact onhash _ r run
  · exact onhash _ r run
  · exact onhash _ r run
  · exact onhash _ r run
  · exact onhash _ r run
  · exact onhash _ r run
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map] at run
      obtain ⟨u, hu, rfl⟩ := run
      exact QueryImpl.withCaching_cache_le uniformSampleImpl _ _ _ hu
    · simp only [streamWorld, if_neg hx] at run
      exact onhash _ r run

/-- The honest stream call supplies its value in the resulting caches. -/
theorem treeLockstep_world_stream_answer (prims : Primitives) (D : C.Coalition)
    (x : PrgInput C) (s : HashCache C × HiddenCache C)
    (r : Bit × (HashCache C × HiddenCache C))
    (run : r ∈ support ((streamWorld prims D (.inr (.inr (.inr x)))).run s)) :
    TreeLockstepStreamAnswer prims D r.2 x r.1 := by
  by_cases hx : Hidden D x.1
  · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map] at run
    obtain ⟨u, hu, rfl⟩ := run
    simp only [TreeLockstepStreamAnswer, if_pos hx]
    cases cached : s.2 ((x.1, x.2.1), x.2.2) with
    | none =>
      erw [QueryImpl.withCaching_run_none _ cached] at hu
      simp only [support_map, Set.mem_image] at hu
      obtain ⟨v, _, rfl⟩ := hu
      exact QueryCache.cacheQuery_self _ _ _
    | some v =>
      erw [QueryImpl.withCaching_run_some _ cached] at hu
      have he : u = (v, s.2) := by simpa using hu
      subst u
      exact cached
  · simp only [streamWorld, if_neg hx] at run
    change r ∈ support ((fun u : Bit × HashCache C => (u.1, u.2, s.2)) <$>
      (prgAnswer prims x).run s.1) at run
    rw [support_map] at run
    obtain ⟨u, hu, rfl⟩ := run
    unfold prgAnswer at hu
    rw [StateT.run_bind] at hu
    simp only [support_bind, Set.mem_iUnion] at hu
    obtain ⟨v, hv, hu⟩ := hu
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst u
    rw [hashAnswer_of_not_isFixed prims (by simp [IsFixed])] at hv
    simp only [TreeLockstepStreamAnswer, if_neg hx]
    exact ⟨v.1, (randomOracle_support _ _ v hv).2.1, rfl⟩

/-- Only honest stream queries are constrained here; public hash agreement
is supplied separately by `treeSimCheck_logged_hashes`. -/
def TreeLockstepWorldStreams (prims : Primitives) (D : C.Coalition)
    (s : HashCache C × HiddenCache C) :
    (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop
  | .inr (.inr (.inr x)), u => TreeLockstepStreamAnswer prims D s x u
  | _, _ => True

/-- All honest stream answers in one execution agree with its final caches.
No independent local supports or fresh resampling are introduced. -/
theorem treeLockstep_logged_streams {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C)
    (a : α) (log : TreeSimLog C) (final : HashCache C × HiddenCache C)
    (run : ((a, log), final) ∈ support
      ((simulateQ ((streamWorld prims D).withTraceAppend
        (fun t u => ([⟨t, u⟩] : TreeSimLog C))) p).run.run s)) :
    s.1 ≤ final.1 ∧ s.2 ≤ final.2 ∧
      ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
        TreeLockstepWorldStreams prims D final t u := by
  induction p using OracleComp.inductionOn generalizing s a log final with
  | pure b =>
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨le_rfl, le_rfl, by simp⟩
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query,
      QueryImpl.withTraceAppend_apply, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, StateT.run_bind, StateT.run_map,
      bind_map_left, pure_bind, bind_assoc, Functor.map_map,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image] at run
    obtain ⟨⟨u, next⟩, hu, ⟨⟨b, tail⟩, last⟩, hb, he⟩ := run
    cases he
    obtain ⟨hgrow, hhidden, hall⟩ := ih u next b tail last hb
    refine ⟨(treeSim_streamWorld_grows prims D t s (u, next) hu).trans hgrow,
      (treeLockstep_world_hidden_grows prims D t s (u, next) hu).trans hhidden, ?_⟩
    intro t' u' hm
    rcases List.mem_cons.mp hm with he | he
    · cases he
      rcases t with ((v | q | x) | query) | (v | q | x)
      all_goals try exact True.intro
      exact treeLockstep_streamAnswer_mono prims D hgrow hhidden
        (treeLockstep_world_stream_answer prims D x s (u, next) hu)
    · exact hall t' u' he

/-- The actual continuation of an arbitrary incoming log has one replay
whose stream answers are certified by this run's final caches. -/
theorem treeLockstep_logged_run_allowed {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    TreeSimCheckAllowed (TreeLockstepWorldStreams prims D r.2.1) p r.1 := by
  rw [treeSimLoggedWorld_run, support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact ⟨u.1.2, treeSimCheckReplay_supported prims D p s.1 u.1.1 u.1.2 u.2 hu,
    (treeLockstep_logged_streams prims D p s.1 u.1.1 u.1.2 u.2 hu).2.2⟩

private theorem treeLockstep_ro_allowed [Field E] [Algebra Bit E]
    {ι α : Type} {G : OracleSpec ι}
    (allowed : (t : (PartySpec C E G).Domain) → (PartySpec C E G).Range t → Prop)
    (p : OracleComp (RoSpec C) α) (a : α)
    (h : TreeSimCheckAllowed allowed (oracleStep p : PartyM C E G α).run (some a)) :
    TreeSimCheckAllowed (fun t u => allowed (.inl (.inl (.inr t))) u) p a := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b =>
    have he : some a = some b := h.pure_inv
    cases Option.some.inj he
    exact .pure _ b
  | query_bind t k ih =>
    rw [oracleStep_bind] at h
    obtain ⟨v, hv, hk⟩ := h.option_bind_inv _ _ _
    have query_eq : (oracleStep (OracleComp.lift (OracleSpec.query t)) : PartyM C E G _).run =
        ((OracleComp.lift (OracleSpec.query (spec := PartySpec C E G)
          (.inl (.inl (.inr t))))) >>= fun u => pure (some u)) := by
      cases t <;> rfl
    rw [query_eq] at hv
    obtain ⟨u, hu, he⟩ := hv.bind_inv
    have he := Option.some.inj he.pure_inv
    subst v
    exact .query t k u a (hu.query_inv _ _) (ih u a hk)

private theorem treeLockstep_allowed_mapM_get {ι α β : Type} {S : OracleSpec.{0, 0} ι}
    (allowed : (t : S.Domain) → S.Range t → Prop) (f : α → OracleComp S β)
    (xs : List α) (ys : List β) (h : TreeSimCheckAllowed allowed (xs.mapM f) ys) :
    ys.length = xs.length ∧ ∀ (n : ℕ) x, xs[n]? = some x →
      ∃ y, ys[n]? = some y ∧ TreeSimCheckAllowed allowed (f x) y := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := h.pure_inv
    subst ys
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, ht⟩ := h.bind_inv
    obtain ⟨tail, htail, he⟩ := ht.bind_inv
    have he : ys = y :: tail := he.pure_inv
    subst ys
    obtain ⟨length, each⟩ := ih tail htail
    refine ⟨by simp [length], ?_⟩
    intro n a ha
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      exact ⟨y, rfl, hy⟩
    | succ n => exact each n a ha

/-- A complete PRG replay names every finite stream answer in the supplied
shared caches; it also preserves the protocol's zero values past the count. -/
theorem treeLockstep_prg_stream_answers (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u → TreeLockstepStreamAnswer prims D cache x u)
    (name : KeyName C) (key : HashOutput) (label idx count : ℕ) (values : ℕ → Bit)
    (run : TreeSimCheckAllowed allowed (prgBits name key label idx count) values) :
    (∀ g < count, TreeLockstepStreamAnswer prims D cache (name, key, label, idx, g) (values g)) ∧
    (∀ g, count ≤ g → values g = 0) := by
  unfold prgBits at run
  obtain ⟨bits, hbits, he⟩ := run.bind_inv
  change List Bit at bits
  have he : values = fun g => bits.getD g 0 := he.pure_inv
  subst values
  obtain ⟨length, each⟩ := treeLockstep_allowed_mapM_get allowed _ (List.range count) bits hbits
  simp only [List.length_range] at length
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨b, hb, hq⟩ := each g g (by simp [hg])
    have hv : bits.getD g 0 = b := by simp [List.getD_eq_getElem?_getD, hb]
    change TreeLockstepStreamAnswer prims D cache (name, key, label, idx, g) (bits.getD g 0)
    rw [hv]
    exact streams _ _ (hq.query_inv _ _)
  · intro g hg
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : bits.length ≤ g)]

/-- Positive-width stream draws yield A49's exact readiness certificate.
For zero width a visible stream need not query its AES key at all. -/
theorem treeLockstep_stream_answers_ready (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C) (name : KeyName C) (key : HashOutput)
    (label idx count : ℕ) (values : ℕ → Bit) (nonzero : 0 < count)
    (answers : ∀ g < count,
      TreeLockstepStreamAnswer prims D cache (name, key, label, idx, g) (values g)) :
    TreeSimStreamReady prims D name key label idx count values cache.1 cache.2 := by
  unfold TreeSimStreamReady
  by_cases hidden : Hidden D name
  · simp only [if_pos hidden]
    intro g hg
    simpa only [TreeLockstepStreamAnswer, hidden, if_true] using answers g hg
  · simp only [if_neg hidden]
    have first := answers 0 nonzero
    simp only [TreeLockstepStreamAnswer, hidden, if_false] at first
    obtain ⟨derived, cached, _⟩ := first
    refine ⟨derived, cached, ?_⟩
    intro g hg
    have hg' := answers g hg
    simp only [TreeLockstepStreamAnswer, hidden, if_false] at hg'
    obtain ⟨other, cached', value⟩ := hg'
    have eq : other = derived := Option.some.inj (cached'.symm.trans cached)
    simpa only [eq] using value

section Prss
variable [Field E] [Algebra Bit E]

/-- The term component of an actual PRSS draw has the addresses and values
recorded by its own replay, including the selected party's holder test. -/
theorem treeLockstep_prss_stream_answers (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u → TreeLockstepStreamAnswer prims D cache x u)
    (ctx : Context C) (label idx count : ℕ) (rnd : PrssOutput C Bit)
    (run : TreeSimCheckAllowed allowed (prssDraw ctx (bitCodec (E := E)) label idx count) rnd) :
    ∀ T, ctx.self ∈ C.holders T → ∀ g < count,
      TreeLockstepStreamAnswer prims D cache (.term T, ctx.prss.term T, label, idx, g) (rnd.1 T g) := by
  unfold prssDraw at run
  obtain ⟨terms, hterms, hrest⟩ := run.bind_inv
  obtain ⟨pairs, _, he⟩ := hrest.bind_inv
  have he := he.pure_inv
  subst rnd
  intro T held g hg
  obtain ⟨_, each⟩ := treeLockstep_allowed_mapM_get allowed _ C.terms terms hterms
  obtain ⟨values, hvalues, hdraw⟩ := each (C.terms.idxOf T) T (List.getElem?_idxOf (mem_terms T))
  simp only [if_pos held] at hdraw
  have answer := (treeLockstep_prg_stream_answers prims D cache allowed streams
    (.term T) (ctx.prss.term T) label idx count values hdraw).1 g hg
  simpa only [List.getD_eq_getElem?_getD, hvalues, Option.getD_some] using answer

/-- This certificate is extracted from the real local PRSS program rather
than assumed for an independently selected mask. -/
theorem treeLockstep_prss_local_ready (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (streams : ∀ x u, allowed (.inl (.inl (.inr (.inr x)))) u →
      TreeLockstepStreamAnswer prims D cache x u)
    (ctx : Context C) (label idx count : ℕ) (nonzero : 0 < count) (rnd : PrssOutput C Bit)
    (run : TreeSimCheckAllowed allowed
      (oracleStep (prssDraw ctx (bitCodec (E := E)) label idx count) : PartyM C E RealSpec _).run (some rnd)) :
    ∀ T, ctx.self ∈ C.holders T →
      TreeSimStreamReady prims D (.term T) (ctx.prss.term T) label idx count (rnd.1 T) cache.1 cache.2 := by
  have ro := treeLockstep_ro_allowed allowed _ rnd run
  intro T held
  exact treeLockstep_stream_answers_ready prims D cache (.term T) (ctx.prss.term T)
    label idx count (rnd.1 T) nonzero
    (treeLockstep_prss_stream_answers prims D cache
      (fun t u => allowed (.inl (.inl (.inr t))) u) (fun x u h => streams x u h)
      ctx label idx count rnd ro T held)

end Prss

section Rerand
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- The last peer tuple uses the PRSS block at `label + depth jobs`, and
unfilled held copies are exactly the masks from that draw. -/
theorem treeLockstep_beforeVerify_ready (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (streams : ∀ x u, allowed (.inl (.inl (.inr (.inr x)))) u →
      TreeLockstepStreamAnswer prims D cache x u)
    (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) (label tag : ℕ)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (nonzero : 0 < (outputsOf jobs).length)
    (run : TreeSimCheckAllowed allowed
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run ⟨fun _ => [], label, tag⟩).run
      (some (out, final))) :
    ∃ masks : Shares C Bit,
      (∀ T, ctx.self ∈ C.holders T →
        TreeSimStreamReady prims D (.term T) (ctx.prss.term T) (label + depth jobs) 0
          (outputsOf jobs).length (masks T) cache.1 cache.2) ∧
      ∀ T g, ctx.self ∈ C.holders T → T ∉ filledTerms K → g < (outputsOf jobs).length →
        out.1 T g = masks T g := by
  simp only [treeSimCheckBeforeVerify, StateT.run_bind, StateT.run_pure] at run
  obtain ⟨⟨p, st⟩, hp, run⟩ := run.option_bind_inv _ _ _
  obtain ⟨⟨v, next⟩, hv, he⟩ := run.option_bind_inv _ _ _
  have he := Option.some.inj he.pure_inv
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have hst := treeSimCheck_layers_state K ctx mode jobs
    (List.range (depth jobs)) (inputs, []) ⟨fun _ => [], label, tag⟩ p st
    (by funext T; simp [filledHistory]) hp.choose_spec.1.mem_support
  have hlabel : st.label = label + depth jobs := by simpa using hst.2.1
  change TreeSimCheckAllowed allowed
    (((prssRandomness ctx bitCodec 0 (outputsOf jobs).length >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx (outputShares K jobs p.1)) (outputsOf jobs).length).run st).run)
    (some (v, final)) at hv
  rw [prssRandomness_run] at hv
  obtain ⟨rnd, hdraw, hshare⟩ := hv.option_bind_inv _ _ _
  have ready := treeLockstep_prss_local_ready prims D cache allowed streams ctx st.label 0
    (outputsOf jobs).length nonzero rnd hdraw
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run] at hshare
  obtain ⟨inbox, _, he⟩ := hshare.option_bind_inv _ _ _
  have he := Option.some.inj he.pure_inv
  have value := congrArg Prod.fst he
  refine ⟨rnd.1, ?_, ?_⟩
  · simpa only [hlabel] using ready
  · intro T g held unfilled inside
    rw [value]
    exact treeLockstep_reshare_unfilled K ctx rnd _ _ inbox T g held unfilled inside

/-- Every surviving checkpoint of this single joint prefix has its actual
rerandomization masks in the same final caches, at the common layer offset. -/
theorem treeLockstep_batchPrefix_ready (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (ctx : C.Party → Context C)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ)
    (prelude : C.Party → PartyM C E RealSpec Unit) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (nonzero : 0 < (outputsOf (jobs.map (circuits parameter ·.kind))).length)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => prelude i >>= fun _ => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial))).run s)) :
    ∀ i, i ∉ D.1 → ∀ data, r.1.2 i = some data → ∃ masks : Shares C Bit,
      (∀ T, (ctx i).self ∈ C.holders T →
        TreeSimStreamReady prims D (.term T) ((ctx i).prss.term T)
          (initial.1 + depth (jobs.map (circuits parameter ·.kind))) 0
          (outputsOf (jobs.map (circuits parameter ·.kind))).length (masks T) r.2.1.1 r.2.1.2) ∧
      ∀ T g, (ctx i).self ∈ C.holders T → T ∉ filledTerms K →
        g < (outputsOf (jobs.map (circuits parameter ·.kind))).length →
        data.2.1.1 T g = masks T g := by
  have replay := treeLockstep_logged_run_allowed prims D _ s r run
  intro i hi data hd
  have party := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ r.1 replay i hi data hd
  obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
  unfold treeSimCheckBatchPrefix at party
  obtain ⟨inputs, _, party⟩ := party.option_bind_inv _ _ _
  obtain ⟨p, hp, he⟩ := party.option_bind_inv _ _ _
  have he : data = (inputs, p) := Option.some.inj he.pure_inv
  subst data
  have streams : ∀ (x : PrgInput C) (u : Bit),
      treeSimCheckPartyAllowed (E := E) (G := RealSpec)
        (fun t u => TreeLockstepWorldStreams prims D r.2.1 (.inr t) u)
        (.inl (.inl (.inr (.inr x)))) u → TreeLockstepStreamAnswer prims D r.2.1 x u := by
    intro x u h
    exact h
  have hn : 0 < (outputsOf (jobs.map (circuits (ctx i).keys.parameter ·.kind))).length := by
    simpa only [parameters i] using nonzero
  rw [← parameters i]
  apply treeLockstep_beforeVerify_ready prims K D r.2.1
    (treeSimCheckPartyAllowed (E := E) (G := RealSpec)
      (fun t u => TreeLockstepWorldStreams prims D r.2.1 (.inr t) u))
    streams (ctx i) settings.mode (jobs.map (circuits (ctx i).keys.parameter ·.kind))
    inputs initial.1 initial.2 p.1 p.2 hn
  exact hp

end Rerand

section CheckedBatch
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

private theorem treeLockstep_worldPhase_congr {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p q : C.Party → PartyM C E RealSpec α) (same : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D A noFunctionality fuel state p =
      executePhase worldRoles D A noFunctionality fuel state q := by
  unfold executePhase
  congr 1
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · simp only [if_neg hi, same i hi]

/-- The actual joint circuit prefix and its accepted check determine all
held copies. The masks, tuple offsets and counts are conclusions of the
prefix; the only key premise is the setup's honest-key consistency. -/
theorem treeLockstep_batch_checked_held {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (prefixFuel checkFuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (jobs : List Job) (initial : ℕ × ℕ)
    (prelude : C.Party → PartyM C E RealSpec Unit) (s : TreeSimState C)
    (pref : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (data : C.Party → List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (selected : ∀ i, i ∉ D.1 → pref.1.2 i = some (data i))
    (prefixRun : pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality prefixFuel state
        (fun i => prelude i >>= fun _ => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial))).run s))
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (checked : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (2 * sliceBits + 2 * (halvings (tupleCount (jobs.map (circuits parameter ·.kind))) - sliceBits) +
          2 + (checkFuel + 1)) pref.1.1
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run
          (data i).2.2 >>= k i))).run pref.2))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∀ i T g, i ∉ D.1 → i ∈ C.holders T →
      g < (outputsOf (jobs.map (circuits parameter ·.kind))).length →
      (data i).2.1.1 T g = (data (refHolder D T)).2.1.1 T g := by
  let js := jobs.map (circuits parameter ·.kind)
  let counts := (List.range (depth js)).map (fun l => (gatesAt js l).length)
  let modes := (List.range (depth js)).map (fun _ => settings.mode)
  by_cases empty : (outputsOf js).length = 0
  · intro i T g _ _ hg
    change g < (outputsOf js).length at hg
    omega
  have nonzero : 0 < (outputsOf js).length := Nat.pos_of_ne_zero empty
  let honest : C.Party → C.Party := fun i => if i ∉ D.1 then i else refHolder D K.publicTerm
  have hh (i : C.Party) : honest i ∉ D.1 := by
    by_cases hi : i ∉ D.1
    · simpa only [honest, if_pos hi] using hi
    · simpa only [honest, if_neg hi] using (refHolder_spec D K.publicTerm).2
  have keep (i : C.Party) (hi : i ∉ D.1) : honest i = i := if_pos hi
  have live : ∀ i, i ∉ D.1 → (pref.1.2 i).isSome := by
    intro i hi
    rw [selected i hi]
    rfl
  have allowed := treeLockstep_logged_run_allowed prims D _ s pref prefixRun
  have shape' : ∀ i, ∃ before input,
      (data (honest i)).2.1.2 = before ++ [⟨input, one K, (data (honest i)).2.1.1,
        (outputsOf js).length, .peer⟩] ∧
      (data (honest i)).2.2.history = recordMode K .peer (honest i)
        (filledHistory K (honest i) before) (data (honest i)).2.1.1 (outputsOf js).length ∧
      before.map (·.count) = counts ∧ before.map (·.mode) = modes := by
    intro i
    have party := treeSimCheck_phase_replay D A noFunctionality _ prefixFuel state _ pref.1
      allowed (honest i) (hh i) (data (honest i)) (selected _ (hh i))
    obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
    unfold treeSimCheckBatchPrefix at party
    obtain ⟨inputs, _, party⟩ := party.option_bind_inv _ _ _
    obtain ⟨p, hp, he⟩ := party.option_bind_inv _ _ _
    have he : data (honest i) = (inputs, p) := Option.some.inj he.pure_inv
    obtain ⟨before, input, ht, history, hc, hm⟩ := treeLockstep_beforeVerify_rerand K
      (ctx (honest i)) settings.mode _ inputs initial.1 initial.2 p.1 p.2 hp.choose_spec.1.mem_support
    refine ⟨before, input, ?_⟩
    simpa only [he, parameters, self] using And.intro ht (And.intro history (And.intro hc hm))
  choose before input shape history count mode using shape'
  have ready := treeLockstep_batchPrefix_ready prims K circuits settings D A prefixFuel state ctx
    parameter parameters jobs initial prelude s pref nonzero prefixRun
  have ready' := fun i => ready (honest i) (hh i) (data (honest i)) (selected _ (hh i))
  choose masks ready unfilled using ready'
  let ctx' := fun i => ctx (honest i)
  let values := fun i => (data (honest i)).2.1.1
  let states := fun i => (data (honest i)).2.2
  have self' : ∀ i, i ∉ D.1 → (ctx' i).self = i := by
    intro i hi
    simp only [ctx', keep i hi, self i]
  have keys' : Consistent D (fun i T => (ctx' i).prss.term T) := by
    intro T i hiT j hjT hi hj
    simpa only [ctx', keep i hi, keep j hj] using keys T i hiT j hjT hi hj
  have fuel_eq : tupleCount js = counts.sum + (outputsOf js).length := by
    exact tupleCount_eq js
  have run' : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (2 * sliceBits + 2 * (halvings (counts.sum + (outputsOf js).length) - sliceBits) +
          2 + (checkFuel + 1)) pref.1.1
        (fun i => (check K (ctx' i) (realCheckGadgets K (ctx' i))
          (before i ++ [⟨input i, one K, values i, (outputsOf js).length, .peer⟩])).run
            (states i) >>= k i))).run pref.2) := by
    rw [← fuel_eq]
    rw [treeLockstep_worldPhase_congr D A _ pref.1.1 _
      (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run
        (data i).2.2 >>= k i)]
    · exact checked
    · intro i hi
      dsimp only [ctx', states, values]
      rw [← shape i, keep i hi]
  have held := treeLockstep_checked_rerand_held prims K D A checkFuel pref.1.1 ctx' self'
    before input values masks (outputsOf js).length counts modes count mode states
    (fun i hi => by simpa only [states, values, keep i hi] using history i)
    keys' (initial.1 + depth js) pref.2.1.1 pref.2.1.2
    (fun i T hi hiT _ => by
      apply ready i T
      simpa only [self, keep i hi] using hiT)
    (fun i T g hi hiT unfill hg => by
      apply unfilled i T g _ unfill hg
      simpa only [self, keep i hi] using hiT)
    k pref.2 r run' good accepted
  intro i T g hi hiT hg
  have h := held i T g hi hiT hg
  simpa only [values, keep i hi, keep _ (refHolder_spec D T).2] using h

/-- The original audited continuation after the tuple check. Its record
retains the prefix inputs and checkpoint and the actual opened outputs. -/
def treeLockstepBatchCheckCont {α : Type} (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (p : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α) (out : Unit × RunState C) : PartyM C E RealSpec α := do
  let opened ← openRep K ctx p.2.1.1 (outputsOf (jobs.map (circuits ctx.keys.parameter ·.kind))).length
  let value := assemble (jobs.map (circuits ctx.keys.parameter ·.kind)) opened
  k ((some value, [⟨ctx, jobs, initial, p.1, p.2.1.2, p.2.2, value, out.2⟩]),
    (out.2.label, initial.2 + 1))

theorem treeLockstep_batchFinish_check {α : Type} (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (p : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α) :
    treeSimCheckBatchFinish K circuits ctx jobs initial p >>= k =
      (check K ctx (realCheckGadgets K ctx) p.2.1.2).run p.2.2 >>=
        treeLockstepBatchCheckCont K circuits ctx jobs initial p k := by
  simp only [treeSimCheckBatchFinish, treeSimCheckAfterVerify, bind_assoc, pure_bind]
  rfl

-- The private A49 resume identity, with the same corrupted-slot condition.
private theorem treeLockstep_batch_resume {α β : Type} (D : C.Coalition)
    (k : C.Party → β → PartyM C E RealSpec α) (out : C.Party → Option β) (data : C.Party → β)
    (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (honest : ∀ i, i ∉ D.1 → out i = some (data i)) :
    free (Concrete.sequenceFin fun i => continueStep (k i) (.done (out i))) =
      startSteps worldRoles D (fun i => k i (data i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, continueStep, free_pure]
  · simp [hi, honest i hi, continueStep, worldRoles]

/-- A successful whole audited batch supplies its joint checkpoint and the
original remaining execution. Its saved copies agree without separate mask,
history or tuple-shape certificates. -/
theorem treeLockstep_batch_boundary_held {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 +
          (2 * sliceBits + 2 * (halvings (tupleCount (jobs.map (circuits parameter ·.kind))) - sliceBits) +
            2 + (fuel + 1))) state
        (fun i => (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (pref : (A.State × (C.Party → Option
        (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
      (data : C.Party → List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C),
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality
          (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1) state
          (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial))).run s) ∧
      (∀ i, i ∉ D.1 → pref.1.2 i = some (data i)) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality
          (2 * sliceBits + 2 * (halvings (tupleCount (jobs.map (circuits parameter ·.kind))) - sliceBits) +
            2 + (fuel + 1)) pref.1.1
          (fun i => treeSimCheckBatchFinish K circuits (ctx i) jobs initial (data i) >>= k i))).run pref.2) ∧
      ∀ i T g, i ∉ D.1 → i ∈ C.holders T →
        g < (outputsOf (jobs.map (circuits parameter ·.kind))).length →
        (data i).2.1.1 T g = (data (refHolder D T)).2.1.1 T g := by
  let rest := 2 * sliceBits + 2 * (halvings (tupleCount (jobs.map (circuits parameter ·.kind))) - sliceBits) +
    2 + (fuel + 1)
  let cont := fun i p => treeSimCheckBatchFinish K circuits (ctx i) jobs initial p >>= k i
  rw [treeSimCheckBatchAudit_phase_split K circuits settings D A rest state ctx parameter parameters
    jobs initial k] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨pref, hpref, next, hnext, htail⟩ := run
  have rawNext := treeLockstep_logged_run_allowed prims D _ pref.2 next hnext
  have rawTail := treeLockstep_logged_run_allowed prims D _ next.2 r htail
  have live := treeSimCheck_exchange_continuations_live D A rest pref.1.1 pref.1.2 cont
    (fun i p => by
      unfold cont treeSimCheckBatchFinish
      rw [bind_assoc]
      exact (treeSimCheckAfterVerify_exchange K (ctx i) _ p.2).bind _)
    next.1 rawNext.choose_spec.1.mem_support r.1 rawTail.choose_spec.1.mem_support accepted
  let data := fun i => (pref.1.2 i).getD ([], (0, []), ⟨fun _ => [], initial.1, initial.2⟩)
  have hd (i : C.Party) (hi : i ∉ D.1) : pref.1.2 i = some (data i) := by
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (live i hi)
    simp only [data, hp, Option.getD_some]
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A _ state
    (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial) s pref
    (by simpa only [simulateQ_executePhase] using hpref)
  have restart := treeLockstep_batch_resume D cont pref.1.2 data corrupt hd
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rest pref.1.1 (fun i => cont i (data i)))).run pref.2) := by
    unfold executePhase
    rw [← restart]
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨next, hnext, htail⟩
  refine ⟨pref, data, hpref, hd, suffix, ?_⟩
  apply treeLockstep_batch_checked_held prims K circuits settings D A _ fuel state ctx self parameter
    parameters keys jobs initial (fun _ => pure ()) s pref data hd hpref
    (fun i => treeLockstepBatchCheckCont K circuits (ctx i) jobs initial (data i) (k i)) r
  · simpa only [cont, treeLockstep_batchFinish_check] using suffix
  · exact good
  · exact accepted

end CheckedBatch

section ContinuedOpening
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

private theorem treeLockstep_good_subset {a b : TreeSimLog C} (h : a ⊆ b)
    (good : ¬ TreeSimHashBudgetCollision b) : ¬ TreeSimHashBudgetCollision a := by
  rintro ⟨q, q', u, hq, hq', ne, ha, hb⟩
  exact good ⟨q, q', u, hq, hq', ne,
    ha.imp (fun x => h x) (fun x => h x), hb.imp (fun x => h x) (fun x => h x)⟩

/-- Change one opening continuation without changing any reached state,
including when the opening or the continuation aborts. -/
theorem treeLockstep_open_local_canonical {α : Type} (D : C.Coalition)
    (live : C.Party → Bool) (jobs : List Circuit)
    (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T →
      g < (outputsOf jobs).length → v i T g = V T g)
    (ds : C.Party → List HashOutput)
    (k : C.Party → List (List Bit) → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) (s : TreeSimState C)
    (r : Step C E RealSpec α × TreeSimState C)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector (outputsOf jobs).length (v h T))) u)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live (outputsOf jobs).length v ds
        (fun i out => k i (assemble jobs out))) sent i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live (outputsOf jobs).length v ds
        (fun i _ => k i (assemble jobs (shareValue V)))) sent i))).run s) := by
  rw [treeLockstep_open_local_factor] at run ⊢
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run ⊢
  obtain ⟨⟨out, mid⟩, hhead, hrest⟩ := run
  refine ⟨(out, mid), hhead, ?_⟩
  cases out with
  | none => exact hrest
  | some out =>
    have hpref := (treeSimLoggedWorld_prefix prims D _ mid r hrest).subset
    have common := treeLockstep_open_head_value prims K D live (outputsOf jobs).length v V
      held ds sent i s mid out hashes hhead (treeLockstep_good_subset hpref good)
    have eq := treeLockstep_assemble_congr jobs out (shareValue V) common
    simpa only [treeSimResume, eq] using hrest

/-- A support-preserving change to sequential state computations keeps their
actual intermediate states; the terminal guard is pulled back along the run. -/
private theorem treeLockstep_sequence_canonical {σ α : Type} [Preorder σ]
    (base : σ) (Good : σ → Prop) (down : ∀ a b, a ≤ b → Good b → Good a) :
    ∀ {n : ℕ} (f g : Fin n → StateT σ ProbComp α)
      (_grow : ∀ i s, base ≤ s → ∀ r ∈ support ((f i).run s), s ≤ r.2)
      (_change : ∀ i s, base ≤ s → ∀ r ∈ support ((f i).run s), Good r.2 →
        r ∈ support ((g i).run s))
      (s : σ), base ≤ s → ∀ r ∈ support ((Concrete.sequenceFin f).run s),
      s ≤ r.2 ∧ (Good r.2 → r ∈ support ((Concrete.sequenceFin g).run s))
  | 0, f, g, _, _, s, hs, r, hr => by
    simp only [Concrete.sequenceFin, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨le_rfl, fun _ => by simp [Concrete.sequenceFin]⟩
  | n + 1, f, g, grow, change, s, hs, r, hr => by
    simp only [Concrete.sequenceFin, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨a, s₁⟩, h₁, ⟨as, s₂⟩, h₂, hp⟩ := hr
    simp only [StateT.run_pure, mem_support_pure_iff] at hp
    subst r
    have hs₁ := grow 0 s hs (a, s₁) h₁
    obtain ⟨hs₂, ht⟩ := treeLockstep_sequence_canonical base Good down
      (fun i : Fin n => f i.succ) (fun i => g i.succ)
      (fun i => grow i.succ) (fun i => change i.succ) s₁ (hs.trans hs₁) (as, s₂) h₂
    refine ⟨hs₁.trans hs₂, fun hg => ?_⟩
    simp only [Concrete.sequenceFin, StateT.run_bind, mem_support_bind_iff]
    exact ⟨(a, s₁), change 0 s hs _ h₁ (down s₁ s₂ hs₂ hg),
      (as, s₂), ht hg, by simp⟩

/-- Start an opening with its original continuation and actual self indices. -/
theorem treeLockstep_open_start_cont {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => openRep K (ctx i) (v i) count >>= k i) = (do
      let ds ← free (treeLockstepOpenHashes D (fun _ => true) count v)
      pure (treeSimOpenPartial K D (fun _ => true) count v ds k)) := by
  unfold startSteps treeLockstepOpenHashes
  rw [free_sequenceFin]
  have one : ∀ i : C.Party,
      (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest
        (advance ((openRep K (ctx i) (v i) count >>= k i).run))) = (do
      let ds ← free (if i ∉ D.1 ∧ true = true then
        liftComp (treeSimOpenCopyHashes count (v i)) (LocalSpec C) else pure [])
      pure (if i ∈ D.1 then .done none else treeSimOpenStep K i count (v i) ds (k i))) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_true, not_true_eq_false, false_and, if_false, free_pure, pure_bind]
    · simp only [hi, if_false, not_false_eq_true, true_and, if_true]
      simpa only [self i, map_eq_bind_pure_comp, Function.comp_def] using treeSim_open_entry K (ctx i) count (v i) (k i)
  simp_rw [one]
  rw [sequenceFin_bind_pure]
  rfl

/-- The first opening round keeps one adversary reply, ordered local
continuations, and the original scheduler tail. -/
theorem treeLockstep_open_phase_cont {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality (fuel + 1) state
      (fun i => openRep K (ctx i) (v i) count >>= k i) = (do
      let ds ← free (treeLockstepOpenHashes D (fun _ => true) count v)
      let b ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then treeSimOpenOut K i count (v i) (ds i) c else none)
      let steps ← free (Concrete.sequenceFin fun i => roundLocal D
        (treeSimOpenPartial K D (fun _ => true) count v ds k) b.2 i)
      executeRounds worldRoles D A noFunctionality fuel b.1 steps) := by
  unfold executePhase
  rw [treeLockstep_open_start_cont K D ctx self]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro ds
  have running : ¬ ∀ i, i ∉ D.1 →
      (treeSimOpenPartial K D (fun _ => true) count v ds k i).isDone := by
    intro h
    obtain ⟨i, hi⟩ := coalition_has_honest D
    simpa only [treeSimOpenPartial, if_neg hi, if_true, treeSimOpenStep, Step.isDone] using h i hi
  rw [executeRounds, if_neg running, stepRound_real]
  have view : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (treeSimOpenPartial K D (fun _ => true) count v ds k i).outbox c else none) =
      (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then treeSimOpenOut K i count (v i) (ds i) c else none) := by
    funext c i
    by_cases hi : i ∈ D.1 <;> simp [treeSimOpenPartial, treeSimOpenStep, Step.outbox, hi]
  rw [view]
  simp only [bind_assoc, pure_bind]

/-- Canonicalize all opened job outputs in one actual synchronized phase.
The conclusion retains the exact final adversary state, party results, caches
and log, including aborts and the entire original continuation. -/
theorem treeLockstep_open_phase_canonical {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (jobs : List Circuit) (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T →
      g < (outputsOf jobs).length → v i T g = V T g)
    (k : C.Party → List (List Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (ctx i) (v i) (outputsOf jobs).length >>=
          fun out => k i (assemble jobs out)))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (ctx i) (v i) (outputsOf jobs).length >>=
          fun _ => k i (assemble jobs (shareValue V))))).run s) := by
  rw [treeLockstep_open_phase_cont K D A fuel state ctx self] at run ⊢
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run ⊢
  obtain ⟨⟨ds, s₁⟩, hashes, ⟨b, s₂⟩, hadv, ⟨steps, s₃⟩, hlocal, tail⟩ := run
  refine ⟨(ds, s₁), hashes, (b, s₂), hadv, (steps, s₃), ?_, tail⟩
  have evidence := treeLockstep_open_hashes_logged prims D (fun _ => true)
    (outputsOf jobs).length v s (ds, s₁) hashes
  have grows := (treeSimLoggedWorld_prefix prims D _ s₁ (b, s₂) hadv).subset
  have good₃ := treeLockstep_good_subset
    (treeSimLoggedWorld_prefix prims D _ s₃ r tail).subset good
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [free_sequenceFin, simulateQ_sequenceFin] at hlocal ⊢
  refine (treeLockstep_sequence_canonical s₁
    (fun s : TreeSimState C => ¬ TreeSimHashBudgetCollision s.2)
    (fun _ _ h => treeLockstep_good_subset h) _ _ ?_ ?_ s₂ grows (steps, s₃) hlocal).2 good₃
  · intro i cache hcache next hn
    exact (treeSimLoggedWorld_prefix prims D _ cache next hn).subset
  · intro i cache hcache next hn hg
    apply treeLockstep_open_local_canonical prims K D (fun _ => true) jobs v V held ds k b.2
      i cache next ?_ hn hg
    intro h hh hl
    obtain ⟨hlen, hs⟩ := evidence h hh hl
    refine ⟨hlen, fun T => ?_⟩
    obtain ⟨u, hu, he⟩ := hs T
    exact ⟨u, hu, he.imp (fun x => hcache x) (fun x => hcache x)⟩

private theorem treeLockstep_timed_require {α : Type} (n : ℕ) (p : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : ∀ u, TreeSimCheckTimed n (k u).run) :
    TreeSimCheckTimed n (require p >>= k).run := by
  unfold require
  split_ifs
  · simpa only [pure_bind] using hk ()
  · exact .abort n

/-- The last scalar opening has only a pure test afterward, so the complete
nonempty check admits an exact synchronous cut. Empty checks use zero rounds. -/
theorem treeLockstep_check_timed (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) (nonzero : (tuples.map (·.count)).sum ≠ 0) :
    TreeSimCheckTimed
      (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 5)
      ((check K ctx (realCheckGadgets K ctx) tuples).run st).run := by
  rw [treeLockstep_check_eq K ctx tuples nonzero, StateT.run_bind]
  rw [show 2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 5 =
    (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 3) + 2 by omega]
  apply (treeLockstep_checkPrefix_timed K ctx tuples st).bind
  intro p
  unfold treeLockstepCheckSuffix
  simp only [StateT.run_bind, StateT.run_lift]
  apply treeLockstep_timed_challenge K ctx 0
  intro challenge
  unfold openSh
  simp only [bind_assoc]
  apply TreeSimCheckTimed.exchange_bind 0
  intro inbox
  apply treeLockstep_timed_require 0
  intro _
  simp only [pure_bind]
  apply treeLockstep_timed_require 0
  intro _
  exact .done _

/-- Extract a timed boundary from one successful joint execution. The next
exchange makes every honest prefix live, and the suffix retains its real
adversary state, cache and log. -/
theorem treeLockstep_timed_boundary {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec β)
    (k : C.Party → β → PartyM C E RealSpec α) (fallback : β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (exchange : ∀ i a, TreeSimCheckExchange (k i a))
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (n + 1 + fuel) state
        (fun i => p i >>= k i))).run s))
    (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (pref : (A.State × (C.Party → Option β)) × TreeSimState C) (data : C.Party → β),
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1) state p)).run s) ∧
      (∀ i, i ∉ D.1 → pref.1.2 i = some (data i)) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel pref.1.1
          (fun i => k i (data i)))).run pref.2) := by
  rw [treeSimCheckTimed_phase_split D A n fuel state p k timed] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨pref, hpref, next, hnext, htail⟩ := run
  have rawNext := treeLockstep_logged_run_allowed prims D _ pref.2 next hnext
  have rawTail := treeLockstep_logged_run_allowed prims D _ next.2 r htail
  have live := treeSimCheck_exchange_continuations_live D A fuel pref.1.1 pref.1.2 k
    exchange next.1 rawNext.choose_spec.1.mem_support r.1 rawTail.choose_spec.1.mem_support accepted
  let data := fun i => (pref.1.2 i).getD fallback
  have hd (i : C.Party) (hi : i ∉ D.1) : pref.1.2 i = some (data i) := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (live i hi)
    simp only [data, hv, Option.getD_some]
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A _ state p s pref
    (by simpa only [simulateQ_executePhase] using hpref)
  refine ⟨pref, data, hpref, hd, ?_⟩
  unfold executePhase
  rw [← treeLockstep_batch_resume D k pref.1.2 data corrupt hd]
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨next, hnext, htail⟩

/-- Canonicalize the opening after the actual whole check. The cut is
operational, and zero-count checks correctly consume no exchanges. -/
theorem treeLockstep_check_open_canonical {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (st : C.Party → RunState C) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count)
    (jobs : List Circuit) (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T →
      g < (outputsOf jobs).length → v i T g = V T g)
    (k : C.Party → (Unit × RunState C) → List (List Bit) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun out =>
          openRep K (ctx i) (v i) (outputsOf jobs).length >>= fun opened =>
            k i out (assemble jobs opened)))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun out =>
          openRep K (ctx i) (v i) (outputsOf jobs).length >>= fun _ =>
            k i out (assemble jobs (shareValue V))))).run s) := by
  by_cases zero : count = 0
  · have empty (i) : (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) =
        pure ((), st i) := by
      simp only [check, counts i, zero]
      rfl
    simp only [empty, pure_bind, zero, checkLabels, if_true, Nat.zero_add] at run ⊢
    exact treeLockstep_open_phase_canonical prims K D A fuel state ctx self jobs v V held
      (fun i => k i ((), st i)) s r run good
  · have labels : checkLabels count = 2 * halvings count + 5 := by
      simp only [checkLabels, if_neg zero]
    let n := 2 * halvings count + 4
    let p := fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
    let next := fun i out => openRep K (ctx i) (v i) (outputsOf jobs).length >>=
      fun opened => k i out (assemble jobs opened)
    let next' := fun i out => openRep K (ctx i) (v i) (outputsOf jobs).length >>=
      fun _ => k i out (assemble jobs (shareValue V))
    have timed (i) : TreeSimCheckTimed (n + 1) (p i).run := by
      have h := treeLockstep_check_timed K (ctx i) (tuples i) (st i) (by rw [counts i]; exact zero)
      have hs : sliceBits ≤ halvings count := by unfold halvings; omega
      convert h using 1
      rw [counts i]
      dsimp only [n]
      omega
    have runcut : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1 + (fuel + 1)) state
          (fun i => p i >>= next i))).run s) := by
      simpa only [p, next, n, labels] using run
    obtain ⟨pref, data, hpref, selected, hrest⟩ := treeLockstep_timed_boundary prims D A n
      (fuel + 1) state p next ((), ⟨fun _ => [], 0, 0⟩) timed
      (fun i out => by
        exact (treeSimCheck_openRep_exchange K (ctx i) _ _).bind _) s r runcut accepted
    have changed : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (fuel + 1) pref.1.1
          (fun i => next' i (data i)))).run pref.2) := by
      exact treeLockstep_open_phase_canonical prims K D A fuel pref.1.1 ctx self jobs v V held
        (fun i => k i (data i)) pref.2 r hrest good
    have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A _ state p s pref
      (by simpa only [simulateQ_executePhase] using hpref)
    rw [labels]
    change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (n + 1 + (fuel + 1)) state
        (fun i => p i >>= next' i))).run s)
    rw [treeSimCheckTimed_phase_split D A n (fuel + 1) state p next' timed]
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    refine ⟨pref, hpref, ?_⟩
    unfold executePhase at changed
    rw [← treeLockstep_batch_resume D next' pref.1.2 data corrupt selected] at changed
    simpa only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] using changed

end ContinuedOpening

section WholeBatch
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Pending local work from the preceding opening. It may abort, but a
successful prelude carries no new public choice into the following batch. -/
def treeLockstepLocalPrelude (gate : OracleComp (LocalSpec C) (Option Unit)) :
    PartyM C E RealSpec Unit := do
  let out ← localStep gate
  match out with
  | none => failure
  | some _ => pure ()

theorem treeLockstep_localPrelude_timed {α : Type} (gate : OracleComp (LocalSpec C) (Option Unit))
    (n : ℕ) (p : PartyM C E RealSpec α) (timed : TreeSimCheckTimed (n + 1) p.run) :
    TreeSimCheckTimed (n + 1) (treeLockstepLocalPrelude (E := E) gate >>= fun _ => p).run := by
  unfold treeLockstepLocalPrelude
  rw [bind_assoc]
  apply TreeSimCheckTimed.local_bind n
  intro out
  cases out with
  | none => exact .abort _
  | some u => simpa only [pure_bind] using timed

/-- Replace only the output value and its audited copies, retaining counters
and every other record field. -/
def treeLockstepCanonicalBatchResult (value : List (List Bit))
    (out : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))) :
    ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :=
  ((some value, out.1.2.map fun record => { record with outputs := value }), out.2)

/-- One actual successful audited batch fixes a common output for every
continuation. No tuple, history, PRSS-readiness or independent-prefix
certificate is assumed; those are extracted from this run. -/
theorem treeLockstep_batch_canonical {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 +
          (checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + (fuel + 1))) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ value : List (List Bit), r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds + 1 +
          (checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + (fuel + 1))) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>=
          fun out => k i (treeLockstepCanonicalBatchResult value out)))).run s) := by
  let js := jobs.map (circuits parameter ·.kind)
  let rest := checkLabels (tupleCount js) + (fuel + 1)
  let p := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial
  let next := fun i data => treeSimCheckBatchFinish K circuits (ctx i) jobs initial data >>= k i
  have run' : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (depth js * settings.mode.rounds + 1 + rest)
        state (fun i => p i >>= next i))).run s) := by
    simpa only [p, next, treeSimCheckBatchAudit_run_prefix, bind_assoc] using run
  have timed (i) : TreeSimCheckTimed (depth js * settings.mode.rounds + 1) (p i).run := by
    apply treeLockstep_localPrelude_timed
    simpa only [parameters i] using treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
  obtain ⟨pref, raw, hpref, hraw, htail⟩ := treeLockstep_timed_boundary prims D A
    (depth js * settings.mode.rounds) rest state p next
    ([], (0, []), ⟨fun _ => [], initial.1, initial.2⟩) timed
    (fun i data => by
      unfold next treeSimCheckBatchFinish
      rw [bind_assoc]
      exact (treeSimCheckAfterVerify_exchange K (ctx i) _ data.2).bind _) s r run' accepted
  let honest := fun i : C.Party => if i ∉ D.1 then i else refHolder D K.publicTerm
  have hh (i) : honest i ∉ D.1 := by
    by_cases hi : i ∉ D.1
    · simpa only [honest, if_pos hi] using hi
    · simpa only [honest, if_neg hi] using (refHolder_spec D K.publicTerm).2
  have keep (i) (hi : i ∉ D.1) : honest i = i := if_pos hi
  let data := fun i => raw (honest i)
  have selected (i) (hi : i ∉ D.1) : pref.1.2 i = some (data i) := by
    simpa only [data, keep i hi] using hraw i hi
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rest pref.1.1
        (fun i => next i (data i)))).run pref.2) := by
    rw [treeLockstep_worldPhase_congr D A rest pref.1.1 _ (fun i => next i (raw i))
      (fun i hi => by rw [show data i = raw i from congrArg raw (keep i hi)])]
    exact htail
  have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
  have counts (i) : (((data i).2.1.2).map (·.count)).sum = tupleCount js := by
    have party := treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed
      (honest i) (hh i) (raw (honest i)) (hraw _ (hh i))
    obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
    unfold treeSimCheckBatchPrefix at party
    obtain ⟨inputs, _, party⟩ := party.option_bind_inv _ _ _
    obtain ⟨result, hp, he⟩ := party.option_bind_inv _ _ _
    have he : data i = (inputs, result) := Option.some.inj he.pure_inv
    obtain ⟨before, input, hs, _, hc, _⟩ := treeLockstep_beforeVerify_rerand K
      (ctx (honest i)) settings.mode _ inputs initial.1 initial.2 result.1 result.2 hp.choose_spec.1.mem_support
    rw [he]
    dsimp only
    rw [hs, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, hc, parameters, tupleCount_eq]
  let V : Shares C Bit := fun T => (data (refHolder D T)).2.1.1 T
  have held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf js).length →
      (data i).2.1.1 T g = V T g := by
    by_cases zero : tupleCount js = 0
    · have width : (outputsOf js).length = 0 := by
        rw [tupleCount_eq] at zero
        omega
      intro i T g hi hT hg
      omega
    · have hf : rest = 2 * sliceBits + 2 * (halvings (tupleCount js) - sliceBits) +
          2 + ((fuel + 3) + 1) := by
        have hs : sliceBits ≤ halvings (tupleCount js) := by unfold halvings; omega
        simp only [rest, checkLabels, if_neg zero]
        omega
      apply treeLockstep_batch_checked_held prims K circuits settings D A _ (fuel + 3) state ctx
        self parameter parameters keys jobs initial (fun i => treeLockstepLocalPrelude (gate i))
        s pref data selected hpref
        (fun i => treeLockstepBatchCheckCont K circuits (ctx i) jobs initial (data i) (k i)) r
      · simpa only [next, treeLockstep_batchFinish_check, hf] using suffix
      · exact good
      · exact accepted
  let value := assemble js (shareValue V)
  let fixed := fun i out => k i (treeLockstepCanonicalBatchResult value out)
  have changed : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rest pref.1.1
        (fun i => treeSimCheckBatchFinish K circuits (ctx i) jobs initial (data i) >>= fixed i))).run pref.2) := by
    simp only [next, treeLockstep_batchFinish_check] at suffix ⊢
    unfold treeLockstepBatchCheckCont at suffix ⊢
    simp only [parameters] at suffix ⊢
    have hc := treeLockstep_check_open_canonical prims K D A fuel pref.1.1 ctx self
      (fun i => (data i).2.1.2) (fun i => (data i).2.2) (tupleCount js) counts js
      (fun i => (data i).2.1.1) V held
      (fun i out opened => k i ((some opened,
        [⟨ctx i, jobs, initial, (data i).1, (data i).2.1.2, (data i).2.2, opened, out.2⟩]),
        (out.2.label, initial.2 + 1))) pref.2 r (by exact suffix) good accepted
    simpa only [fixed, treeLockstepCanonicalBatchResult, List.map_cons, List.map_nil] using hc
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A _ state p s pref
    (by simpa only [simulateQ_executePhase] using hpref)
  refine ⟨value, ?_⟩
  simp only [treeSimCheckBatchAudit_run_prefix, bind_assoc]
  suffices joined : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (depth js * settings.mode.rounds + 1 + rest) state
      (fun i => p i >>= fun d => treeSimCheckBatchFinish K circuits (ctx i) jobs initial d >>= fixed i))).run s) by
    simpa only [p, fixed, bind_assoc] using joined
  rw [treeSimCheckTimed_phase_split D A (depth js * settings.mode.rounds) rest state p
    (fun i d => treeSimCheckBatchFinish K circuits (ctx i) jobs initial d >>= fixed i) timed]
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨pref, hpref, ?_⟩
  unfold executePhase at changed
  rw [← treeLockstep_batch_resume D
    (fun i d => treeSimCheckBatchFinish K circuits (ctx i) jobs initial d >>= fixed i)
    pref.1.2 data corrupt selected] at changed
  simpa only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] using changed

/-- The preceding opening's still-pending local checks, including their
hash queries and possible abort. -/
def treeLockstepOpenGate (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) : OracleComp (LocalSpec C) (Option Unit) :=
  Option.map (fun _ => ()) <$> liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)

/-- Opening checks and the next program's initial local work stay interleaved
in the original operator order. No hashes move across another operator. -/
theorem treeLockstep_open_round_preludes {α : Type} (D : C.Coalition)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k : C.Party → PartyM C E RealSpec α) :
    free (Concrete.sequenceFin fun i => roundLocal D
      (treeSimOpenPartial K D live count v ds (fun i _ => k i)) sent i) =
    startSteps worldRoles D (fun i =>
      treeLockstepLocalPrelude (treeLockstepOpenGate K D live count v ds sent i) >>= fun _ => k i) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, roundLocal, treeSimOpenPartial, free_pure]
  · rw [if_neg hi, treeLockstep_open_local_factor]
    unfold treeLockstepLocalPrelude treeLockstepOpenGate
    dsimp only
    rw [bind_assoc, advance_localStep_bind]
    change _ = free _
    simp only [map_eq_bind_pure_comp, Function.comp_def, free_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro out
    cases out <;> rfl

/-- After the opening's single adversary reply, the remaining execution is
an exact next phase with the pending copy checks as local preludes. -/
theorem treeLockstep_open_phase_preludes {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality (fuel + 1) state
      (fun i => openRep K (ctx i) (v i) count >>= fun _ => k i) = (do
      let ds ← free (treeLockstepOpenHashes D (fun _ => true) count v)
      let b ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then treeSimOpenOut K i count (v i) (ds i) c else none)
      executePhase worldRoles D A noFunctionality fuel b.1
        (fun i => treeLockstepLocalPrelude
          (treeLockstepOpenGate K D (fun _ => true) count v ds b.2 i) >>= fun _ => k i)) := by
  rw [treeLockstep_open_phase_cont K D A fuel state ctx self]
  apply bind_congr
  intro ds
  apply bind_congr
  intro b
  rw [treeLockstep_open_round_preludes]
  rfl

/-- The next phase starts before the pending opening heads, preserving
exactly the local query order of the actual network round. -/
theorem treeLockstep_open_pending_cut {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → PartyM C E RealSpec α) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (ctx i) (v i) count >>= fun _ => k i))).run s)) :
    ∃ (state' : A.State) (cache : TreeSimState C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => k i))).run cache) := by
  rw [treeLockstep_open_phase_preludes K D A fuel state ctx self] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨⟨ds, s₁⟩, _, ⟨b, s₂⟩, _, tail⟩ := run
  exact ⟨b.1, s₂, treeLockstepOpenGate K D (fun _ => true) count v ds b.2, tail⟩

/-- A canonicalized check/open tail supplies the next actual phase and each
honest check result. The local opening checks remain in the pending gates. -/
theorem treeLockstep_check_pending_cut {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (st : C.Party → RunState C) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count)
    (width : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (Unit × RunState C) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun checked =>
          openRep K (ctx i) (v i) width >>= fun _ => k i checked))).run s))
    (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (checked : C.Party → Unit × RunState C) (state' : A.State) (cache : TreeSimState C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, i ∉ D.1 → some (checked i) ∈ support
        ((check K (ctx i) (realCheckGadgets (G := RealSpec) K (ctx i)) (tuples i)).run (st i)).run) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => k i (checked i)))).run cache) := by
  by_cases zero : count = 0
  · have empty (i) : (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) =
        pure ((), st i) := by
      simp only [check, counts i, zero]
      rfl
    simp only [empty, pure_bind, zero, checkLabels, if_true, Nat.zero_add] at run
    obtain ⟨state', cache, gate, tail⟩ := treeLockstep_open_pending_cut prims K D A fuel state ctx self
      width v (fun i => k i ((), st i)) s r run
    refine ⟨(fun i => ((), st i)), state', cache, gate, ?_, tail⟩
    intro i hi
    simp only [empty, OptionT.run_pure, mem_support_pure_iff]
  · have labels : checkLabels count = 2 * halvings count + 5 := by
      simp only [checkLabels, if_neg zero]
    let n := 2 * halvings count + 4
    let p := fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
    let next := fun i out => openRep K (ctx i) (v i) width >>= fun _ => k i out
    have timed (i) : TreeSimCheckTimed (n + 1) (p i).run := by
      have h := treeLockstep_check_timed K (ctx i) (tuples i) (st i) (by rw [counts i]; exact zero)
      have hs : sliceBits ≤ halvings count := by unfold halvings; omega
      convert h using 1
      rw [counts i]
      dsimp only [n]
      omega
    have runcut : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1 + (fuel + 1)) state
          (fun i => p i >>= next i))).run s) := by
      simpa only [p, next, n, labels] using run
    obtain ⟨pref, checked, hpref, selected, hrest⟩ := treeLockstep_timed_boundary prims D A n
      (fuel + 1) state p next ((), ⟨fun _ => [], 0, 0⟩) timed
      (fun i out => (treeSimCheck_openRep_exchange K (ctx i) _ _).bind _) s r runcut accepted
    obtain ⟨state', cache, gate, tail⟩ := treeLockstep_open_pending_cut prims K D A fuel pref.1.1 ctx self
      width v (fun i => k i (checked i)) pref.2 r hrest
    refine ⟨checked, state', cache, gate, ?_, tail⟩
    intro i hi
    have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
    exact (treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed i hi
      (checked i) (selected i hi)).choose_spec.1.mem_support

/-- Advance a whole audited batch to the next phase without commuting its
final local hashes. The next counters and recorded output are common; the
pending local gates retain every possible abort. -/
theorem treeLockstep_batch_next {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs + fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (value : List (List Bit)) (records : C.Party → TreeSimCheckBatchRecord C)
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, (records i).outputs = value ∧ (records i).jobs = jobs ∧ (records i).start = initial) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i ((some value, [records i]),
              (initial.1 + batchLabels circuits parameter jobs, initial.2 + 1))))).run cache) := by
  let js := jobs.map (circuits parameter ·.kind)
  let rest := checkLabels (tupleCount js) + (fuel + 1)
  have rounds : batchRounds circuits settings.mode parameter jobs + fuel =
      depth js * settings.mode.rounds + 1 + rest := by
    unfold batchRounds batchCount rest js
    omega
  rw [rounds] at run
  obtain ⟨value, canonical⟩ := treeLockstep_batch_canonical prims K circuits settings D A fuel state
    ctx self parameter parameters keys gate jobs initial k s r run good accepted
  let fixed := fun i out => k i (treeLockstepCanonicalBatchResult value out)
  let p := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial
  let next := fun i data => treeSimCheckBatchFinish K circuits (ctx i) jobs initial data >>= fixed i
  have timed (i) : TreeSimCheckTimed (depth js * settings.mode.rounds + 1) (p i).run := by
    apply treeLockstep_localPrelude_timed
    simpa only [parameters i] using treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
  have cutrun : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (depth js * settings.mode.rounds + 1 + rest)
        state (fun i => p i >>= next i))).run s) := by
    simpa only [p, next, fixed, treeSimCheckBatchAudit_run_prefix, bind_assoc] using canonical
  obtain ⟨pref, raw, hpref, selectedRaw, suffixRaw⟩ := treeLockstep_timed_boundary prims D A
    (depth js * settings.mode.rounds) rest state p next
    ([], (0, []), ⟨fun _ => [], initial.1, initial.2⟩) timed
    (fun i data => by
      unfold next treeSimCheckBatchFinish
      rw [bind_assoc]
      exact (treeSimCheckAfterVerify_exchange K (ctx i) _ data.2).bind _) s r cutrun accepted
  let honest := fun i : C.Party => if i ∉ D.1 then i else refHolder D K.publicTerm
  have hh (i) : honest i ∉ D.1 := by
    by_cases hi : i ∉ D.1
    · simpa only [honest, if_pos hi] using hi
    · simpa only [honest, if_neg hi] using (refHolder_spec D K.publicTerm).2
  have keep (i) (hi : i ∉ D.1) : honest i = i := if_pos hi
  let data := fun i => raw (honest i)
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rest pref.1.1
        (fun i => next i (data i)))).run pref.2) := by
    rw [treeLockstep_worldPhase_congr D A rest pref.1.1 _ (fun i => next i (raw i))
      (fun i hi => by rw [show data i = raw i from congrArg raw (keep i hi)])]
    exact suffixRaw
  have metadata (i) : (data i).2.2.label = initial.1 + depth js + 1 ∧
      (data i).2.1.2.map (·.count) =
        (List.range (depth js)).map (fun l => (gatesAt js l).length) ++ [(outputsOf js).length] := by
    have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
    have party := treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed
      (honest i) (hh i) (raw (honest i)) (selectedRaw _ (hh i))
    obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
    have h := treeSimCheckBatchPrefix_state K circuits settings (ctx (honest i)) jobs initial
      (raw (honest i)) party.choose_spec.1.mem_support
    simpa only [parameters] using And.intro h.2.1 h.2.2.2.1
  have counts (i) : (((data i).2.1.2).map (·.count)).sum = tupleCount js := by
    rw [(metadata i).2, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, tupleCount_eq]
  have labels (i) : (data i).2.2.label = initial.1 + depth js + 1 := by
    exact (metadata i).1
  simp only [next, treeLockstep_batchFinish_check] at suffix
  unfold treeLockstepBatchCheckCont at suffix
  simp only [fixed, treeLockstepCanonicalBatchResult, List.map_cons, List.map_nil, parameters] at suffix
  let record := fun i (checked : Unit × RunState C) =>
    (⟨ctx i, jobs, initial, (data i).1, (data i).2.1.2, (data i).2.2, value, checked.2⟩ :
      TreeSimCheckBatchRecord C)
  let cont := fun i (checked : Unit × RunState C) =>
    k i ((some value, [record i checked]), (checked.2.label, initial.2 + 1))
  obtain ⟨checked, state', cache, gate', checkRuns, tail⟩ := treeLockstep_check_pending_cut prims K D A fuel
    pref.1.1 ctx self (fun i => (data i).2.1.2) (fun i => (data i).2.2) (tupleCount js) counts
    (outputsOf js).length (fun i => (data i).2.1.1) cont pref.2 r suffix accepted
  have finalLabel (i) (hi : i ∉ D.1) : (checked i).2.label = initial.1 + batchLabels circuits parameter jobs := by
    have h := lockstepLabels_check K (ctx i) (data i).2.1.2 (data i).2.2 (checked i).1 (checked i).2
      (checkRuns i hi)
    rw [counts i, labels i] at h
    unfold batchLabels batchCount
    dsimp only [js] at h
    omega
  refine ⟨value, (fun i => record i (checked i)), state', cache, gate', (fun i => ⟨rfl, rfl, rfl⟩), ?_⟩
  rw [treeLockstep_worldPhase_congr D A fuel state' _
    (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ => cont i (checked i)) ?_]
  · exact tail
  · intro i hi
    simp only [cont, finalLabel i hi]

private theorem treeLockstep_batches_cons (ctx : Context C) (jobs : List Job)
    (batches : List (List Job)) (initial : ℕ × ℕ) :
    (((jobs :: batches).mapM (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial) =
      (do
        let a ← (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial
        let b ← ((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run a.2)
        pure ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)) := by
  simp [List.mapM_cons, WriterT.run_bind, StateT.run_bind]

/-- Induction through an actual list of batches. The record-output list and
all returned job outputs are common, while the pending local work and
individual remaining record fields stay attached to their operators. -/
theorem treeLockstep_batches_next {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (batches : List (List Job)) (initial : ℕ × ℕ)
    (k : C.Party → ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        ((batches.map (batchRounds circuits settings.mode parameter)).sum + fuel) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run initial) >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (values : List (List (List Bit))) (records : C.Party → List (TreeSimCheckBatchRecord C))
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      values.length = batches.length ∧ (∀ i, (records i).map (·.outputs) = values) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i ((values.map some, records i),
              (initial.1 + (batches.map (batchLabels circuits parameter)).sum,
                initial.2 + batches.length))))).run cache) := by
  induction batches generalizing state gate initial k s with
  | nil =>
    refine ⟨[], (fun _ => []), state, s, gate, rfl, (fun _ => rfl), ?_⟩
    simpa [List.mapM_nil, WriterT.run_pure, StateT.run_pure] using run
  | cons jobs batches ih =>
    rw [show ((jobs :: batches).map (batchRounds circuits settings.mode parameter)).sum + fuel =
      batchRounds circuits settings.mode parameter jobs +
        ((batches.map (batchRounds circuits settings.mode parameter)).sum + fuel) by
          simp only [List.map_cons, List.sum_cons, Nat.add_assoc]] at run
    simp only [treeLockstep_batches_cons, bind_assoc, pure_bind] at run
    let cont := fun i (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) =>
      ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run a.2) >>= fun b =>
        k i ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)
    obtain ⟨value, heads, middle, cache₁, gates₁, hheads, tail₁⟩ :=
      treeLockstep_batch_next prims K circuits settings D A
        ((batches.map (batchRounds circuits settings.mode parameter)).sum + fuel) state ctx self
        parameter parameters keys gate jobs initial cont s r run good accepted
    let next := fun i (b : (List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) =>
      k i ((some value :: b.1.1, heads i :: b.1.2), b.2)
    have tailrun : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality
          ((batches.map (batchRounds circuits settings.mode parameter)).sum + fuel) middle
          (fun i => treeLockstepLocalPrelude (gates₁ i) >>= fun _ =>
            ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run
              (initial.1 + batchLabels circuits parameter jobs, initial.2 + 1)) >>= next i))).run cache₁) := by
      simpa only [cont, next, List.cons_append, List.nil_append] using tail₁
    obtain ⟨values, records, final, cache₂, gates₂, lengths, recorded, tail₂⟩ := ih middle gates₁
      (initial.1 + batchLabels circuits parameter jobs, initial.2 + 1) next cache₁ tailrun
    refine ⟨value :: values, (fun i => heads i :: records i), final, cache₂, gates₂,
      by simp only [List.length_cons, lengths], ?_, ?_⟩
    · intro i
      simp only [List.map_cons, (hheads i).1, recorded i]
    · simpa only [next, List.map_cons, List.sum_cons, List.length_cons, Nat.add_assoc,
        Nat.add_comm 1 batches.length] using tail₂

private theorem treeLockstep_batched_run (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    (batched settings.batchSize (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx) jobs).run.run initial =
      (do
        let a ← ((chunks settings.batchSize jobs).mapM
          (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial
        pure ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)) := by
  simp [batched]

/-- A complete first or second run gives one common flattened output while
retaining its common list of individual batch outputs. -/
theorem treeLockstep_batched_next {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (((chunks settings.batchSize jobs).map (batchRounds circuits settings.mode parameter)).sum + fuel) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i)) jobs).run.run initial >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (values : List (List (List Bit))) (records : C.Party → List (TreeSimCheckBatchRecord C))
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      values.length = (chunks settings.batchSize jobs).length ∧
      (∀ i, (records i).map (·.outputs) = values) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i ((some values.flatten, records i),
              (initial.1 + ((chunks settings.batchSize jobs).map (batchLabels circuits parameter)).sum,
                initial.2 + (chunks settings.batchSize jobs).length))))).run cache) := by
  simp only [treeLockstep_batched_run, bind_assoc, pure_bind] at run
  let next := fun i (a : (List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) =>
    k i ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)
  obtain ⟨values, records, state', cache, gate', lengths, recorded, tail⟩ :=
    treeLockstep_batches_next prims K circuits settings D A fuel state ctx self parameter parameters keys
      gate (chunks settings.batchSize jobs) initial next s r run good accepted
  refine ⟨values, records, state', cache, gate', lengths, recorded, ?_⟩
  simpa only [next, foldlM_some_append, List.nil_append] using tail

/-- Every query of this actual continuation occurs in its terminal log. -/
theorem treeLockstep_logged_allowed {α : Type} (D : C.Coalition)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 → allowed t u) :
    TreeSimCheckAllowed allowed p r.1 := by
  rw [treeSimLoggedWorld_run, support_map] at run
  obtain ⟨out, ho, rfl⟩ := run
  refine ⟨out.1.2, treeSimCheckReplay_supported prims D p s.1 out.1.1 out.1.2 out.2 ho, ?_⟩
  intro t u hu
  exact rows t u (List.mem_append_right s.2 hu)

/-- A local computation that can abort, with no network exchange. -/
def treeLockstepLocalOption {β : Type} (p : OracleComp (LocalSpec C) (Option β)) :
    PartyM C E RealSpec β := do
  let out ← localStep p
  match out with
  | none => failure
  | some b => pure b

private theorem treeLockstep_localOption_advance {α β : Type}
    (p : OracleComp (LocalSpec C) (Option β)) (k : β → PartyM C E RealSpec α) :
    free (advance (treeLockstepLocalOption p >>= k).run) = (do
      let out ← free p
      free (treeSimResume k out)) := by
  unfold treeLockstepLocalOption
  rw [bind_assoc, advance_localStep_bind, free_bind]
  apply bind_congr
  intro out
  cases out <;> rfl

private theorem treeLockstep_localOption_canonical {α β : Type} (D : C.Coalition)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (p : OracleComp (LocalSpec C) (Option β)) (value : β)
    (fixed : ∀ b, TreeSimCheckAllowed (fun t u => allowed (.inr t) u) p (some b) → b = value)
    (k : β → PartyM C E RealSpec α) (s : TreeSimState C)
    (r : Step C E RealSpec α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (advance (treeLockstepLocalOption p >>= k).run))).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 → allowed t u) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (advance (treeLockstepLocalOption p >>= fun _ => k value).run))).run s) := by
  rw [treeLockstep_localOption_advance] at run ⊢
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run ⊢
  obtain ⟨⟨out, mid⟩, hpre, hrest⟩ := run
  refine ⟨(out, mid), hpre, ?_⟩
  cases out with
  | none => exact hrest
  | some b =>
    have grows := (treeSimLoggedWorld_prefix prims D _ mid r hrest).subset
    have replay := treeLockstep_logged_allowed prims D allowed (free p) s (some b, mid) hpre
      (fun t u hu => rows t u (grows hu))
    have localReplay : TreeSimCheckAllowed (fun t u => allowed (.inr t) u) p (some b) := by
      exact TreeSimCheckAllowed.simulate_inv
        (fun t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t))) allowed _
        (fun t u hu => hu.query_inv _ _) p (some b) replay
    rw [← fixed b localReplay]
    exact hrest

/-- Fix a deterministic local prefix inside one actual phase without moving
its queries across other operators' work. -/
theorem treeLockstep_local_phase_canonical {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (p : C.Party → OracleComp (LocalSpec C) (Option β)) (value : β)
    (fixed : ∀ i, i ∉ D.1 → ∀ b,
      TreeSimCheckAllowed (fun t u => allowed (.inr t) u) (p i) (some b) → b = value)
    (k : C.Party → β → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalOption (p i) >>= k i))).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 → allowed t u) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalOption (p i) >>= fun _ => k i value))).run s) := by
  unfold executePhase at run ⊢
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run ⊢
  obtain ⟨steps, hsteps, tail⟩ := run
  refine ⟨steps, ?_, tail⟩
  let Good := fun s : TreeSimState C => ∀ t u,
    (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ s.2 → allowed t u
  have goodSteps : Good steps.2 := by
    intro t u hu
    exact rows t u ((treeSimLoggedWorld_prefix prims D _ steps.2 r tail).subset hu)
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  unfold startSteps at hsteps ⊢
  rw [simulateQ_sequenceFin] at hsteps ⊢
  refine (treeLockstep_sequence_canonical s Good
    (fun a b h hb t u hu => hb t u ((show a.2 ⊆ b.2 from h) hu)) _ _ ?_ ?_ s le_rfl steps hsteps).2 goodSteps
  · intro i cache hcache next hn
    exact (treeSimLoggedWorld_prefix prims D _ cache next hn).subset
  · intro i cache hcache next hn hg
    by_cases hi : i ∈ D.1
    · simpa only [if_pos hi] using hn
    · simp only [if_neg hi] at hn ⊢
      exact treeLockstep_localOption_canonical prims D allowed (p i) value (fixed i hi)
        (k i) cache next hn hg

/-- Public hash code is deterministic under one coherent set of logged
answers. The lift is the actual local oracle lift. -/
theorem treeLockstep_public_local_replay {β : Type} (hash : Query C → HashOutput)
    (p : OracleComp HashSpec β) (b : β)
    (run : TreeSimCheckAllowed (fun t u => TreeSimCheckWorldHashes hash (.inr t) u)
      (liftComp (tweakable (C := C) p) (LocalSpec C)) b) : b = D prims hash (tweakable p) := by
  induction p using OracleComp.inductionOn generalizing b with
  | pure a =>
    simpa only [tweakable, simulateQ_pure, liftComp_pure, D_pure] using run.pure_inv
  | query_bind q k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query, liftComp_bind] at run
    obtain ⟨u, hu, hk⟩ := run.bind_inv
    have qeq : liftComp (hashQuery (C := C) (.hash q)) (LocalSpec C) =
        OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl (.hash q)))) := rfl
    rw [qeq] at hu
    have he := hu.query_inv _ _
    change hash (.hash q) = u at he
    simpa only [tweakable, simulateQ_bind, simulateQ_spec_query, D_bind, D_hashQuery, he] using ih u b hk

/-- The first-run public selection as one unchanged hash computation. -/
def treeLockstepPublicChoiceCode (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) : OracleComp HashSpec (Option (Digest × Randomness × Encoding)) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let chainEnd := fun (e : KeyIndex) (l : ChainIndex) =>
    digestAt (outputs.getD (keys.idxOf (e, l)) []) 2
  let root ← merkleNode parameter bottomLayer chainEnd layerHeight b.val
  let message := bytesLE 16 root
  let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
  let base ← truncateHash <$> Concrete.oracleHash (randomizerInput parameter topLayer (topKey b) ρ message)
  let g ← grind parameter topLayer (topKey b) message base randomizerAttemptLimit 0
  pure (g.map fun r => (root, r))

theorem treeLockstep_publicChoice_code (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) :
    treeEncodingPublicChoice (C := C) (E := E) parameter b outputs =
      oracleStep (tweakable (treeLockstepPublicChoiceCode parameter b outputs)) := by
  simp only [treeEncodingPublicChoice, treeLockstepPublicChoiceCode, tweakable,
    simulateQ_bind, simulateQ_pure, oracleStep_bind, oracleStep_pure]

/-- Local work before a public computation, preserving its abort. -/
def treeLockstepPublicPrelude {β : Type} (gate : OracleComp (LocalSpec C) (Option Unit))
    (p : OracleComp HashSpec β) : OracleComp (LocalSpec C) (Option β) := do
  let out ← gate
  match out with
  | none => pure none
  | some _ => some <$> liftComp (tweakable (C := C) p) (LocalSpec C)

private theorem treeLockstep_publicPrelude_program {α β : Type}
    (gate : OracleComp (LocalSpec C) (Option Unit)) (p : OracleComp HashSpec β)
    (k : β → PartyM C E RealSpec α) :
    treeLockstepLocalOption (treeLockstepPublicPrelude gate p) >>= k =
      (treeLockstepLocalPrelude gate >>= fun _ => oracleStep (tweakable p) >>= k) := by
  apply OptionT.ext
  unfold treeLockstepLocalOption treeLockstepPublicPrelude treeLockstepLocalPrelude
  simp only [localStep, OptionT.run_bind, OptionT.lift, OptionT.run_mk, liftComp_bind,
    bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro out
  cases out with
  | none => simp [liftComp_pure]
  | some u =>
    simp [oracleStep, localStep, liftComp_map, OptionT.lift, pure_bind]

/-- The full public choice, rather than only its encoding, is fixed in an
actual phase. The complete result/cache/log and pending local queries stay. -/
theorem treeLockstep_public_phase_canonical {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (hash : Query C → HashOutput) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (p : OracleComp HashSpec β) (k : C.Party → β → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => oracleStep (tweakable p) >>= k i))).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes hash t u) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => oracleStep (tweakable p) >>=
          fun _ => k i (ThresholdLeanXmssSecurity.D prims hash (tweakable p))))).run s) := by
  simp_rw [← treeLockstep_publicPrelude_program] at run ⊢
  apply treeLockstep_local_phase_canonical prims D A fuel state (TreeSimCheckWorldHashes hash)
    (fun i => treeLockstepPublicPrelude (gate i) p) (ThresholdLeanXmssSecurity.D prims hash (tweakable p)) ?_ k s r run rows
  intro i hi b hb
  unfold treeLockstepPublicPrelude at hb
  obtain ⟨out, _, hb⟩ := hb.bind_inv
  cases out with
  | none => cases hb.pure_inv
  | some u =>
    rw [map_eq_bind_pure_comp] at hb
    obtain ⟨value, hp, he⟩ := hb.bind_inv
    have he := Option.some.inj he.pure_inv
    subst b
    exact treeLockstep_public_local_replay prims hash p value hp

private theorem treeLockstep_localOption_ignore {α β : Type}
    (p : OracleComp (LocalSpec C) (Option β)) (k : PartyM C E RealSpec α) :
    (treeLockstepLocalOption p >>= fun _ => k) =
      (treeLockstepLocalPrelude (Option.map (fun _ => ()) <$> p) >>= fun _ => k) := by
  apply OptionT.ext
  unfold treeLockstepLocalOption treeLockstepLocalPrelude
  simp only [localStep, OptionT.run_bind, OptionT.lift, OptionT.run_mk,
    liftComp_map, bind_map_left, bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro out
  cases out <;> rfl

/-- Retain the public computation as a pending local gate, then continue
with its uniquely fixed result. This is the between-runs boundary. -/
theorem treeLockstep_public_phase_gate {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (hash : Query C → HashOutput) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (p : OracleComp HashSpec β) (k : C.Party → β → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => oracleStep (tweakable p) >>= k i))).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes hash t u) :
    ∃ gate' : C.Party → OracleComp (LocalSpec C) (Option Unit),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i (ThresholdLeanXmssSecurity.D prims hash (tweakable p))))).run s) := by
  have changed := treeLockstep_public_phase_canonical prims D A fuel state hash gate p k s r run rows
  simp_rw [← treeLockstep_publicPrelude_program, treeLockstep_localOption_ignore] at changed
  exact ⟨_, changed⟩

/-- The unchanged local top-tree finish, retaining the batch records. -/
def treeLockstepTopFinish (parameter : PublicParameter) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) : PartyM C E RealSpec
      (TreeOutput × List (TreeSimCheckBatchRecord C)) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange numChains).map fun l => (topKey b, l)
  let chainEnd := fun (e : KeyIndex) (l : ChainIndex) => digestAt (outputs.getD (keys.idxOf (e, l)) []) 0
  let root ← oracleStep (tweakable (merkleNode parameter topLayer chainEnd layerHeight 0))
  pure (.top ⟨chainEnd, root⟩, records)

/-- The unchanged local verification after the second bottom run. -/
def treeLockstepBottomFinish (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (values : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C)) : PartyM C E RealSpec
      (TreeOutput × List (TreeSimCheckBatchRecord C)) := do
  let some values := values | failure
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
    let bits := outputs.getD (keys.idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)
  let commitment := fun (e : KeyIndex) => digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
  let path ← oracleStep (tweakable (merklePath parameter topLayer top.chainEnd (topKey b)))
  let signature : LayerSignature := ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← oracleStep (tweakable (Concrete.layerRoot parameter topLayer (topKey b) (bytesLE 16 root) signature))
  if topRoot ≠ some top.root then failure else
    pure (.bottom ⟨cpk, commitment, root, signature⟩, records)

def treeLockstepFirstJobs : Tree → List Job
  | .top => topJobs
  | .bottom b => bottomJobs b

/-- The actual audited continuation after the first batched run. -/
def treeLockstepFirstRest (ctx : Context C) (top : TopTree) (tree : Tree)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :
    PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)) := do
  let some outputs := a.1.1 | failure
  match tree with
  | .top => treeLockstepTopFinish ctx.keys.parameter outputs a.1.2
  | .bottom b =>
    let chosen ← oracleStep (tweakable (treeLockstepPublicChoiceCode ctx.keys.parameter b outputs))
    let some (root, randomness, enc) := chosen | failure
    let result ← (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx)
      (signJobs b enc)).run.run a.2
    treeLockstepBottomFinish ctx.keys.parameter top b outputs root randomness result.1.1
      (a.1.2 ++ result.1.2)


/-- Run the remaining audit, retaining its earlier records and rejecting a
missing ceremony result. -/
def treeLockstepAuditFinish {β : Type}
    (p : WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)) (Option β))
    (initial : ℕ × ℕ) (prior : List (TreeSimCheckBatchRecord C)) :
    PartyM C E RealSpec (β × List (TreeSimCheckBatchRecord C)) := do
  let a ← p.run.run initial
  match a.1.1 with
  | none => failure
  | some value => pure (value, prior ++ a.1.2)

private theorem treeLockstep_auditFinish_bind {α β : Type}
    (p : WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)) α)
    (f : α → WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)) (Option β))
    (initial : ℕ × ℕ) (prior : List (TreeSimCheckBatchRecord C)) :
    treeLockstepAuditFinish (p >>= f) initial prior = (do
      let a ← p.run.run initial
      treeLockstepAuditFinish (f a.1.1) a.2 (prior ++ a.1.2)) := by
  unfold treeLockstepAuditFinish
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, bind_assoc, bind_map_left]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  cases b.1.1 <;> simp [List.append_assoc]

private theorem treeLockstep_auditFinish_pure {β : Type} (out : Option β)
    (initial : ℕ × ℕ) (prior : List (TreeSimCheckBatchRecord C)) :
    treeLockstepAuditFinish (E := E) (pure out) initial prior =
      match out with
      | none => failure
      | some value => pure (value, prior) := by
  cases out <;> simp [treeLockstepAuditFinish]

private theorem treeLockstep_auditFinish_lift {α β : Type} (p : PartyM C E RealSpec α)
    (f : α → WriterT (List (TreeSimCheckBatchRecord C)) (StateT (ℕ × ℕ) (PartyM C E RealSpec)) (Option β))
    (initial : ℕ × ℕ) (prior : List (TreeSimCheckBatchRecord C)) :
    treeLockstepAuditFinish ((liftM (StateT.lift p : StateT (ℕ × ℕ) (PartyM C E RealSpec) α)) >>= f) initial prior =
      (p >>= fun a => treeLockstepAuditFinish (f a) initial prior) := by
  rw [treeLockstep_auditFinish_bind]
  simp [WriterT.run_liftM, StateT.run_lift]

private theorem treeLockstep_afterSetup_finish (ctx : Context C) (top : TopTree) (tree : Tree) :
    treeSimCheckAfterSetupAudit K circuits settings ctx top tree =
      treeLockstepAuditFinish (treeSimCheckCeremonyAuditBody K circuits settings ctx top tree) (0, 0) [] := by
  simp only [treeSimCheckAfterSetupAudit, treeLockstepAuditFinish, StateT.run'_eq, bind_map_left, List.nil_append]
  apply bind_congr
  rintro ⟨⟨out, records⟩, final⟩
  cases out <;> rfl

/-- Factor the audit syntax with generic writer laws, leaving concrete
circuits and public hash computations unexpanded. -/
theorem treeLockstep_afterSetup_first (ctx : Context C) (top : TopTree) (tree : Tree) :
    treeSimCheckAfterSetupAudit K circuits settings ctx top tree =
      ((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx)
        (treeLockstepFirstJobs tree)).run.run (0, 0) >>= treeLockstepFirstRest K circuits settings ctx top tree) := by
  rw [treeLockstep_afterSetup_finish]
  cases tree with
  | top =>
    unfold treeSimCheckCeremonyAuditBody ceremonyOutput treeLockstepFirstJobs treeLockstepFirstRest
    rw [treeLockstep_auditFinish_bind]
    apply bind_congr
    rintro ⟨⟨out, records⟩, final⟩
    cases out with
    | none => exact treeLockstep_auditFinish_pure _ _ _
    | some outputs =>
      dsimp only
      rw [treeLockstep_auditFinish_lift]
      simp only [treeLockstep_auditFinish_pure, List.nil_append]
      rfl
  | bottom b =>
    unfold treeSimCheckCeremonyAuditBody ceremonyOutput treeLockstepFirstJobs treeLockstepFirstRest
    rw [treeLockstep_auditFinish_bind]
    apply bind_congr
    rintro ⟨⟨out, records⟩, final⟩
    cases out with
    | none => exact treeLockstep_auditFinish_pure _ _ _
    | some outputs =>
      dsimp only
      rw [treeLockstep_auditFinish_lift]
      simp_rw [← treeLockstep_publicChoice_code]
      unfold treeEncodingPublicChoice
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro root
      rw [treeLockstep_auditFinish_lift]
      apply bind_congr
      intro base
      rw [treeLockstep_auditFinish_lift]
      apply bind_congr
      intro chosen
      cases chosen with
      | none => exact treeLockstep_auditFinish_pure _ _ _
      | some chosen =>
        rcases chosen with ⟨randomness, enc⟩
        dsimp only
        rw [treeLockstep_auditFinish_bind]
        apply bind_congr
        rintro ⟨⟨out, next⟩, final'⟩
        cases out with
        | none => exact treeLockstep_auditFinish_pure _ _ _
        | some values =>
          dsimp only
          rw [treeLockstep_auditFinish_lift]
          unfold treeLockstepBottomFinish
          dsimp only
          apply bind_congr
          intro path
          rw [treeLockstep_auditFinish_lift]
          apply bind_congr
          intro topRoot
          split_ifs <;> simp only [treeLockstep_auditFinish_pure, List.nil_append]

private theorem treeLockstep_finish_bind_support {α β : Type}
    (p : PartyM C E RealSpec α) (k : α → PartyM C E RealSpec β) (out : β)
    (run : some out ∈ support (p >>= k).run) :
    ∃ a, some a ∈ support p.run ∧ some out ∈ support (k a).run := by
  rw [OptionT.run_bind] at run
  obtain ⟨a, ha, run⟩ := (mem_support_bind_iff _ _ _).mp run
  cases a with
  | none => simp at run
  | some a => exact ⟨a, ha, run⟩

set_option linter.constructorNameAsVariable false in
/-- A successful local top finish retains exactly its input audit records. -/
theorem treeLockstep_topFinish_records (parameter : PublicParameter)
    (outputs : List (List Bit)) (records : List (TreeSimCheckBatchRecord C))
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C))
    (run : some actual ∈ support (treeLockstepTopFinish (E := E) parameter outputs records).run) :
    actual.2 = records := by
  dsimp only [treeLockstepTopFinish] at run
  obtain ⟨root, _, run⟩ := by
    with_reducible exact treeLockstep_finish_bind_support (α := Digest) _ _ actual run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq] at run
  exact congrArg Prod.snd run

/-- A successful local bottom finish retains exactly its input audit records,
including when its earlier batched result was represented by an arbitrary option. -/
theorem treeLockstep_bottomFinish_records (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (values : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C))
    (actual : TreeOutput × List (TreeSimCheckBatchRecord C))
    (run : some actual ∈ support
      (treeLockstepBottomFinish (E := E) parameter top b outputs root randomness values records).run) :
    actual.2 = records := by
  cases values with
  | none => simp [treeLockstepBottomFinish] at run
  | some values =>
    dsimp only [treeLockstepBottomFinish] at run
    obtain ⟨path, _, run⟩ := treeLockstep_finish_bind_support _ _ actual run
    obtain ⟨topRoot, _, run⟩ := treeLockstep_finish_bind_support _ _ actual run
    split_ifs at run
    · simp at run
    · simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq] at run
      exact congrArg Prod.snd run

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_topFinish_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_topFinish_records

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_bottomFinish_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_bottomFinish_records


end WholeBatch

section SetupContexts

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Complete absent setup rows with common held-term keys and a rejecting
local gate. Present honest rows keep their actual context. This changes no
started computation and supplies globally uniform public parameters. -/
theorem treeLockstep_setup_contexts (D : C.Coalition) (x : C.Party → Keys C)
    (parameter : PublicParameter) (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (setup : C.Party → Option (PrssKeys C)) (corrupt : ∀ i, i ∈ D.1 → setup i = none)
    (agreement : ∀ i j ki kj, setup i = some ki → setup j = some kj →
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T)
    (top : TopTree) (tree : Tree) :
    ∃ (ctx : C.Party → Context C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, (ctx i).self = i) ∧
      (∀ i, (ctx i).keys.parameter = parameter) ∧
      Consistent D (fun i T => (ctx i).prss.term T) ∧
      free (Concrete.sequenceFin fun i => continueStep
        (fun pi => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, pi⟩ top tree)
        (.done (setup i))) =
      startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
        treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree) := by
  have shared : ∀ T : C.Term, ∃ key : HashOutput, ∀ i pi,
      i ∉ D.1 → setup i = some pi → i ∈ C.holders T → pi.term T = key := by
    intro T
    by_cases present : ∃ i pi, i ∉ D.1 ∧ setup i = some pi ∧ i ∈ C.holders T
    · obtain ⟨i, pi, hi, hpi, held⟩ := present
      exact ⟨pi.term T, fun j pj _ hpj hj => agreement j i pj pi hpj hpi T hj held⟩
    · exact ⟨0, fun i pi hi hpi held => (present ⟨i, pi, hi, hpi, held⟩).elim⟩
  choose commonTerm common using shared
  let fallback : PrssKeys C := ⟨commonTerm, fun _ => 0⟩
  let ctx : C.Party → Context C := fun i =>
    ⟨i, { x i with parameter := parameter }, (setup i).getD fallback⟩
  let gate : C.Party → OracleComp (LocalSpec C) (Option Unit) :=
    fun i => pure ((setup i).map fun _ => ())
  have held (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (hT : i ∈ C.holders T) :
      (ctx i).prss.term T = commonTerm T := by
    cases hpi : setup i with
    | none => simp only [ctx, hpi, Option.getD_none, fallback]
    | some pi =>
      simpa only [ctx, hpi, Option.getD_some] using common T i pi hi hpi hT
  have actual (i : C.Party) (hi : i ∉ D.1) (pi : PrssKeys C) (hpi : setup i = some pi) :
      ctx i = ⟨i, x i, pi⟩ := by
    dsimp only [ctx]
    rw [hpi, Option.getD_some, ← parameters i hi]
  refine ⟨ctx, gate, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro T i hi j hj honestI honestJ
    exact (held i honestI T hi).trans (held j honestJ T hj).symm
  · unfold startSteps
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, corrupt i hi, continueStep, free_pure]
    · rw [if_neg hi]
      cases hpi : setup i with
      | none =>
        simp [gate, hpi, continueStep, treeLockstepLocalPrelude, localStep, advance_pure, free_pure]
      | some pi =>
        simp [gate, hpi, continueStep, treeLockstepLocalPrelude, localStep, worldRoles,
          actual i hi pi hpi]

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_setup_contexts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_setup_contexts

end SetupContexts


section CeremonyAgreement
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

private theorem treeLockstep_phase_success {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)) (p : C.Party → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => p i))).run s))
    (i : C.Party) (hi : i ∉ D.1) (a : α) (out : r.1.2 i = some a) :
    some a ∈ support (p i).run := by
  have allowed := treeLockstep_logged_run_allowed prims D _ s r run
  have localRun := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ r.1 allowed i hi a out
  obtain ⟨_, _, rest⟩ := localRun.option_bind_inv _ _ _
  exact rest.choose_spec.1.mem_support

set_option maxHeartbeats 600000 in
set_option linter.constructorNameAsVariable false in
/-- One actual post-setup ceremony fixes every successful honest record's
opened outputs. Both runs and the public selection preserve that same result. -/
theorem treeLockstep_afterSetup_opened (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)) (top : TopTree) (tree : Tree)
    (hash : Query C → HashOutput) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes hash t u)
    (accepted : ∃ i, i ∉ D.1 ∧ ∃ a, r.1.2 i = some a) :
    ∃ values : List (List (List Bit)), ∀ i, i ∉ D.1 → ∀ a, r.1.2 i = some a →
      a.2.map (·.outputs) = values := by
  have anyAccepted : ∃ i a, r.1.2 i = some a := by
    obtain ⟨i, _, a, h⟩ := accepted
    exact ⟨i, a, h⟩
  simp only [treeLockstep_afterSetup_first] at run
  let M := maxBatch circuits settings (runRounds settings.mode)
  let N := ceremonyBatches settings * M
  cases tree with
  | top =>
    let js := chunks settings.batchSize topJobs
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    have hx : X ≤ N :=
      (chunks_rounds_le circuits settings parameter 0 (fun _ => digit 0) js
        (fun _ hj => Or.inl hj)).trans
        (Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings .top))
    have fuel : N = X + (N - X) := by omega
    change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality N state _)).run s) at run
    rw [fuel] at run
    obtain ⟨values, records, state', cache, gate', _, recorded, tail⟩ :=
      treeLockstep_batched_next prims K circuits settings D A (N-X) state ctx self parameter parameters
        keys gate topJobs (0,0) (fun i => treeLockstepFirstRest K circuits settings (ctx i) top .top)
        s r run good anyAccepted
    simp only [treeLockstepFirstRest, parameters] at tail
    refine ⟨values, ?_⟩
    intro i hi a out
    have h := by
      with_reducible exact (treeLockstep_phase_success prims D A (N-X) state' gate'
        (fun i => treeLockstepTopFinish parameter values.flatten (records i)) cache r tail i hi a out)
    have he : a.2 = records i := by
      with_reducible exact (treeLockstep_topFinish_records (E := E) parameter values.flatten (records i) a h)
    rw [he]
    exact recorded i
  | bottom b =>
    let js := chunks settings.batchSize (bottomJobs b)
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    let B := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length
    let Y := B * M
    have hX : X ≤ js.length * M := chunks_rounds_le circuits settings parameter b
      (fun _ => digit 0) js (fun _ hj => Or.inr (Or.inl hj))
    have hY (enc : Encoding) : ((chunks settings.batchSize (signJobs b enc)).map
        (batchRounds circuits settings.mode parameter)).sum ≤ Y := by
      have h := chunks_rounds_le circuits settings parameter b enc
        (chunks settings.batchSize (signJobs b enc)) (fun _ hj => Or.inr (Or.inr hj))
      rw [length_chunks_signJobs settings b b enc (fun _ => digit 0)] at h
      exact h
    have hXY : X + Y ≤ N := by
      calc X + Y ≤ js.length * M + B * M := add_le_add hX le_rfl
        _ = treeBatches settings (.bottom b) * M := by
          change js.length * M + B * M = (js.length + B) * M
          ring
        _ ≤ N := Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings (.bottom b))
    have fuel : N = X + (N-X) := by omega
    change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality N state _)).run s) at run
    rw [fuel] at run
    obtain ⟨values, records, state', cache, gate', _, recorded, tail⟩ :=
      treeLockstep_batched_next prims K circuits settings D A (N-X) state ctx self parameter parameters
        keys gate (bottomJobs b) (0,0)
        (fun i => treeLockstepFirstRest K circuits settings (ctx i) top (.bottom b))
        s r run good anyAccepted
    simp only [treeLockstepFirstRest, parameters] at tail
    obtain ⟨gate'', fixed⟩ := treeLockstep_public_phase_gate prims D A (N-X) state' hash gate'
      (treeLockstepPublicChoiceCode parameter b values.flatten) _ cache r tail rows
    cases choice : ThresholdLeanXmssSecurity.D prims hash
        (tweakable (treeLockstepPublicChoiceCode parameter b values.flatten)) with
    | none =>
      simp only [choice] at fixed
      obtain ⟨i, hi, a, out⟩ := accepted
      have h := treeLockstep_phase_success prims D A (N-X) state' gate''
        (fun _ => failure) cache r fixed i hi a out
      simp [failure, OptionT.fail] at h
    | some selected =>
      obtain ⟨root, randomness, enc⟩ := selected
      simp only [choice] at fixed
      let Z := ((chunks settings.batchSize (signJobs b enc)).map
        (batchRounds circuits settings.mode parameter)).sum
      have enough : Z ≤ N-X := by have h := hY enc; omega
      have fuel' : N-X = Z + (N-X-Z) := by omega
      rw [fuel'] at fixed
      obtain ⟨values', records', state'', cache', gateFinal, _, recorded', tail'⟩ :=
        treeLockstep_batched_next prims K circuits settings D A (N-X-Z) state' ctx self parameter
          parameters keys gate'' (signJobs b enc) _ _ cache r fixed good anyAccepted
      refine ⟨values ++ values', ?_⟩
      intro i hi a out
      have h := treeLockstep_phase_success prims D A (N-X-Z) state'' gateFinal
        (fun i => treeLockstepBottomFinish parameter top b values.flatten root randomness
          (some values'.flatten) (records i ++ records' i)) cache' r tail' i hi a out
      rw [treeLockstep_bottomFinish_records (E := E) parameter top b values.flatten root randomness
        (some values'.flatten) (records i ++ records' i) a h, List.map_append, recorded i, recorded' i]


set_option linter.constructorNameAsVariable false in
/-- The original audited-run opening obligation, with no residual premise. -/
theorem treeLockstepOpenedGoal : TreeLockstepOpenedGoal circuits prims K settings := by
  intro _ top tree D A x z Z dealt r hr good i j hi hj vi ri vj rj oi oj k hki hkj
  rcases r with ⟨⟨result, actual⟩, log⟩
  have hc := hr
  simp only [treeSimLoggedRun, StateT.run'_eq, support_map, Set.mem_image] at hc
  obtain ⟨⟨a, finalCache⟩, hc, he⟩ := hc
  change a = ((result, actual), log) at he
  subst a
  have hall := (treeSimCheck_logged_hashes prims D _ (∅, ∅) (result, actual) log finalCache hc).2
  rw [treeCheckSetup_split] at hr
  obtain ⟨setup, hs, rest⟩ := (mem_support_bind_iff _ _ _).mp hr
  simp only [treeCheckAfterSetup, mem_support_bind_iff, mem_support_pure_iff] at rest
  obtain ⟨next, hn, out, ho, answer, ha, he⟩ := rest
  cases he
  have lastPrefix := treeSimLoggedWorld_prefix prims D _ out.2 answer ha
  have midPrefix := by
    with_reducible exact (treeSimLoggedWorld_prefix prims D _ next.2 out ho)
  have firstPrefix := by
    with_reducible exact (treeSimLoggedWorld_prefix prims D _ setup.2 next hn)
  have goodOut := treeLockstep_good_subset lastPrefix.subset good
  have goodSetup := treeLockstep_good_subset (firstPrefix.trans (midPrefix.trans lastPrefix)).subset good
  have agree := treeAgreementSetupKeys (E := E) prims D A x z setup hs goodSetup
  have corrupt : ∀ p, p ∈ D.1 → setup.1.2 p = none := by
    have hs' := hs
    simp only [treeSaltSetup, mem_support_bind_iff] at hs'
    obtain ⟨start, _, hs'⟩ := hs'
    exact treeSetup_corrupt_none prims D A start.1 start.2 setup hs'
  obtain ⟨parameter, seeds, pairs, dealt⟩ := dealt
  have parameters : ∀ p, p ∉ D.1 → (x p).parameter = parameter := by
    intro p _
    rw [dealt p]
    rfl
  obtain ⟨ctx, gate, self, uniform, keys, start⟩ := treeLockstep_setup_contexts K circuits settings D x
    parameter parameters setup.1.2 corrupt agree top tree
  have phase : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) setup.1.1
        (fun p => treeLockstepLocalPrelude (gate p) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx p) top tree))).run setup.2) := by
    unfold executePhase
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    with_reducible refine ⟨next, ?_, ho⟩
    rw [← start]
    exact hn
  obtain ⟨values, records⟩ := treeLockstep_afterSetup_opened prims K circuits settings D A setup.1.1
    ctx self parameter uniform keys gate top tree (hashOf prims finalCache.1) setup.2 out phase goodOut
    (fun t u h => hall t u (lastPrefix.subset h)) ⟨i, hi, (vi, ri), oi⟩
  have maps : ri.map (·.outputs) = rj.map (·.outputs) :=
    (records i hi (vi, ri) oi).trans (records j hj (vj, rj) oj).symm
  have atIndex := congrArg (fun xs => xs[k]?) maps
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hki, List.getElem?_eq_getElem hkj,
    Option.map_some, Option.some.injEq] using atIndex

/-- Successful audited records now have the common full-ceremony schedule. -/
theorem treeLockstepRecordsAgreeGoal : TreeLockstepRecordsAgreeGoal circuits prims K settings :=
  treeLockstepRecordsAgree_of_opened prims K circuits settings
    (treeLockstepOpenedGoal prims K circuits settings)

end CeremonyAgreement


/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_logged_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_logged_streams

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batchPrefix_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batchPrefix_ready

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batch_boundary_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batch_boundary_held

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_open_phase_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_open_phase_canonical

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_check_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_check_timed

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_check_open_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_check_open_canonical

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batch_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batch_canonical

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batch_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batch_next

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batches_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batches_next

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batched_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batched_next

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_public_phase_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_public_phase_gate

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_afterSetup_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_afterSetup_first

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_afterSetup_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_afterSetup_opened

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepOpenedGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepOpenedGoal

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepRecordsAgreeGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepRecordsAgreeGoal

end ThresholdLeanXmssSecurity
