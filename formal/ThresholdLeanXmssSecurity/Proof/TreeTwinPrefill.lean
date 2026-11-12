import ThresholdLeanXmssSecurity.Proof.TreeSimCheck
import ThresholdLeanXmssSecurity.Proof.TreeSimStages
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedFinal

/-!
# Prefilling hidden stream cells that are read

A hidden cell can be sampled before an adaptive world computation when every
supported execution reads it. The equality retains the complete result, log and caches.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section

namespace ThresholdLeanXmssSecurity.TreeTwinPrefill

attribute [local instance] Classical.propDecidable
variable {C : Committee} (prims : Primitives)

/-- Full-state form of TreeSimCheck's one-cell presampling induction. -/
theorem treeSim_prefill_stream {α : Type} (D : C.Coalition) (x : HiddenAddress C)
    (hidden : Hidden D x.1.1) (m : OracleComp (WorldSpec C) α) :
    ∀ (b : HashCache C × HiddenCache C), b.2 x = none →
      (∀ u ∈ support ((simulateQ (streamWorld prims D) m).run b), u.2.2 x ≠ none) →
      evalDist ((simulateQ (streamWorld prims D) m).run b) =
        evalDist (do
          let v ← ($ᵗ Bit : ProbComp Bit)
          (simulateQ (streamWorld prims D) m).run (b.1, b.2.cacheQuery x v)) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
      intro b fresh read
      exact False.elim (read (a, b) (by simp) fresh)
  | query_bind t k ih =>
      intro b fresh read
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at read ⊢
      by_cases ht : t = .inr (.inr (.inr (x.1.1, x.1.2, x.2)))
      · subst t
        simp only [streamWorld, hidden, if_true, StateT.run_mk]
        rw [QueryImpl.withCaching_run_none _ fresh]
        simp only [bind_map_left]
        apply evalDist_bind_congr_all
        intro v
        rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self b.2 x v)]
        simp only [pure_bind]
      · simp_rw [treeSimCheck_world_update prims D x t ht, bind_map_left]
        rw [← OracleComp.DeferredSampling.evalDist_bind_comm]
        apply evalDist_bind_congr
        intro r hr
        apply ih r.1 r.2 ((treeSimCheck_world_other prims D x t ht b.1 b.2 r hr).trans fresh)
        intro u hu
        exact read u ((mem_support_bind_iff _ _ _).2 ⟨r, hr, hu⟩)

/-- Filling a different hidden cell commutes with an actual logged query. -/
theorem logged_update (D : C.Coalition) (x : HiddenAddress C) (t : (WorldSpec C).Domain)
    (hne : t ≠ .inr (.inr (.inr (x.1.1, x.1.2, x.2)))) (s : TreeSimState C) (v : Bit) :
    (treeSimLoggedWorld prims D t).run ((s.1.1, s.1.2.cacheQuery x v), s.2) =
      (fun r => (r.1, (r.2.1.1, r.2.1.2.cacheQuery x v), r.2.2)) <$>
        (treeSimLoggedWorld prims D t).run s := by
  simp only [treeSimLoggedWorld, StateT.run_mk,
    treeSimCheck_world_update prims D x t hne, Functor.map_map]

/-- A different logged query preserves the selected hidden cell. -/
theorem logged_other (D : C.Coalition) (x : HiddenAddress C) (t : (WorldSpec C).Domain)
    (hne : t ≠ .inr (.inr (.inr (x.1.1, x.1.2, x.2)))) (s : TreeSimState C)
    (r : (WorldSpec C).Range t × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D t).run s)) : r.2.1.2 x = s.1.2 x := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact treeSimCheck_world_other prims D x t hne s.1.1 s.1.2 u hu

/-- Prefilling a cell read on every supported execution keeps the whole logged outcome. -/
theorem treeSim_prefill_logged {α : Type} (D : C.Coalition) (x : HiddenAddress C)
    (hidden : Hidden D x.1.1) (m : OracleComp (WorldSpec C) α) :
    ∀ (a : TreeSimState C), a.1.2 x = none →
      (∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run a), u.2.1.2 x ≠ none) →
      evalDist ((simulateQ (treeSimLoggedWorld prims D) m).run a) =
        evalDist (do
          let v ← ($ᵗ Bit : ProbComp Bit)
          (simulateQ (treeSimLoggedWorld prims D) m).run ((a.1.1, a.1.2.cacheQuery x v), a.2)) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
      intro s fresh read
      exact False.elim (read (a, s) (by simp) fresh)
  | query_bind t k ih =>
      intro s fresh read
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at read ⊢
      by_cases ht : t = .inr (.inr (.inr (x.1.1, x.1.2, x.2)))
      · subst t
        simp only [treeSimLoggedWorld, streamWorld, hidden, if_true, StateT.run_mk]
        rw [QueryImpl.withCaching_run_none _ fresh]
        simp only [Functor.map_map, bind_map_left]
        apply evalDist_bind_congr_all
        intro v
        rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self s.1.2 x v)]
        simp only [pure_bind]
      · simp_rw [logged_update prims D x t ht, bind_map_left]
        rw [← OracleComp.DeferredSampling.evalDist_bind_comm]
        apply evalDist_bind_congr
        intro r hr
        apply ih r.1 r.2 ((logged_other prims D x t ht s r hr).trans fresh)
        intro u hu
        exact read u ((mem_support_bind_iff _ _ _).2 ⟨r, hr, hu⟩)

/-- Every outcome from a fixed prefilling is an outcome of the original read-complete run. -/
theorem prefill_supported {α : Type} (D : C.Coalition) (x : HiddenAddress C)
    (hidden : Hidden D x.1.1) (m : OracleComp (WorldSpec C) α) (s : TreeSimState C)
    (fresh : s.1.2 x = none)
    (read : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run s), u.2.1.2 x ≠ none)
    (v : Bit) (u : α × TreeSimState C)
    (hu : u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run
      ((s.1.1, s.1.2.cacheQuery x v), s.2))) :
    u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run s) := by
  have he := treeSim_prefill_logged prims D x hidden m s fresh read
  rw [mem_support_iff, probOutput_def, he, ← probOutput_def, ← mem_support_iff]
  exact (mem_support_bind_iff _ _ _).2 ⟨v, by simp, hu⟩

/-- Sequential finite prefilling, retaining both caches and the complete log. -/
theorem prefill_sequence {α : Type} (D : C.Coalition) (m : OracleComp (WorldSpec C) α) :
    ∀ {n : ℕ} (addr : Fin n → HiddenAddress C) (inj : Function.Injective addr)
      (hidden : ∀ i, Hidden D (addr i).1.1) (h : HashCache C) (c : HiddenCache C) (log : TreeSimLog C),
      (∀ i, c (addr i) = none) →
      (∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run ((h, c), log)),
        ∀ i, u.2.1.2 (addr i) ≠ none) →
      evalDist ((simulateQ (treeSimLoggedWorld prims D) m).run ((h, c), log)) =
        evalDist (do
          let vals ← Concrete.sequenceFin (fun _ : Fin n => ($ᵗ Bit))
          (simulateQ (treeSimLoggedWorld prims D) m).run ((h, cacheFin addr vals c), log))
  | 0, addr, inj, hidden, h, c, log, fresh, read => by simp [Concrete.sequenceFin, cacheFin]
  | n + 1, addr, inj, hidden, h, c, log, fresh, read => by
    rw [treeSim_prefill_logged prims D (addr 0) (hidden 0) m ((h, c), log) (fresh 0)
      (fun u hu => read u hu 0)]
    simp only [Concrete.sequenceFin, bind_assoc]
    apply evalDist_bind_congr_all
    intro v
    have hf : ∀ i : Fin n, (c.cacheQuery (addr 0) v) (addr i.succ) = none := fun i =>
      (QueryCache.cacheQuery_of_ne c v (fun he => Fin.succ_ne_zero i (inj he))).trans (fresh i.succ)
    have hr : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run
        ((h, c.cacheQuery (addr 0) v), log)), ∀ i : Fin n, u.2.1.2 (addr i.succ) ≠ none := by
      intro u hu i
      exact read u (prefill_supported prims D (addr 0) (hidden 0) m ((h, c), log) (fresh 0)
        (fun u hu => read u hu 0) v u hu) i.succ
    simpa only [pure_bind, cacheFin, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ] using
      prefill_sequence D m (fun i : Fin n => addr i.succ)
        (inj.comp (Fin.succ_injective n)) (fun i => hidden i.succ) h (c.cacheQuery (addr 0) v) log hf hr

/-- Joint uniform prefilling of a finite family that every supported run reads. -/
theorem treeSim_prefill_logged_table {α : Type} (D : C.Coalition) {n : ℕ}
    (addr : Fin n → HiddenAddress C) (inj : Function.Injective addr)
    (hidden : ∀ i, Hidden D (addr i).1.1) (m : OracleComp (WorldSpec C) α)
    (h : HashCache C) (c : HiddenCache C) (log : TreeSimLog C)
    (fresh : ∀ i, c (addr i) = none)
    (read : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) m).run ((h, c), log)),
      ∀ i, u.2.1.2 (addr i) ≠ none) :
    evalDist ((simulateQ (treeSimLoggedWorld prims D) m).run ((h, c), log)) =
      evalDist (do
        let table ← ($ᵗ (Fin n → Bit) : ProbComp (Fin n → Bit))
        (simulateQ (treeSimLoggedWorld prims D) m).run ((h, cacheFin addr table c), log)) := by
  rw [prefill_sequence prims D m addr inj hidden h c log fresh read,
    evalDist_bind, evalDist_sequenceFin_uniform, ← evalDist_bind]

/-- Project the replay of the actual free hash/PRG copy to its source queries. -/
theorem free_ro_allowed {α : Type}
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (p : OracleComp (RoSpec C) α) (a : α)
    (h : TreeSimCheckAllowed allowed (free (liftComp p (LocalSpec C))) a) :
    TreeSimCheckAllowed (fun t u => allowed (.inr (.inr t)) u) p a := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b =>
      simp only [liftComp_pure, free_pure] at h
      cases h.pure_inv
      exact .pure _ _
  | query_bind t k ih =>
      simp only [liftComp_bind, free_bind] at h
      obtain ⟨u, hu, hk⟩ := h.bind_inv
      refine .query t k u a ?_ (ih u a hk)
      exact hu.query_inv (spec := WorldSpec C) (.inr (.inr t)) u

section ReadSupport

-- Port of private TreeLockstepOpenedFinal.treeLockstep_allowed_mapM_get (196–222).
private theorem allowed_mapM_get {ι α β : Type} {S : OracleSpec.{0, 0} ι}
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


variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- Every bit of a hidden field block is present in the caches certifying its replay. -/
theorem element_read_allowed (D : C.Coalition) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u → TreeLockstepStreamAnswer prims D cache x u)
    (name : KeyName C) (hidden : Hidden D name) (key : HashOutput) (label idx count : ℕ)
    (values : ℕ → E)
    (run : TreeSimCheckAllowed allowed ((elementCodec K).draw name key label idx count) values) :
    ∀ g < elementBits * count, cache.2 ((name, key), label, idx, g) ≠ none := by
  obtain ⟨bits, hb, _⟩ := run.bind_inv
  have answers := (treeLockstep_prg_stream_answers prims D cache allowed streams
    name key label idx (elementBits * count) bits hb).1
  intro g hg
  have he := answers g hg
  simp only [TreeLockstepStreamAnswer, hidden, if_true] at he
  rw [he]
  exact Option.some_ne_none _

/-- An accepting PRSS invocation draws every bit of each held hidden term,
even when followed by an arbitrary adaptive world continuation. -/
theorem prss_terms_read {α : Type} (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (k : PrssOutput C E → OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)) >>= k)).run s)) :
    ∀ T, ctx.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g < elementBits * count, r.2.1.2 ((.term T, ctx.prss.term T), label, idx, g) ≠ none := by
  obtain ⟨rnd, hdraw, _⟩ := (treeLockstep_logged_run_allowed prims D _ s r run).bind_inv
  have hr := free_ro_allowed (TreeLockstepWorldStreams prims D r.2.1) _ rnd hdraw
  unfold prssDraw at hr
  obtain ⟨terms, hterms, _⟩ := hr.bind_inv
  intro T held hidden
  obtain ⟨_, each⟩ := allowed_mapM_get _ _ C.terms terms hterms
  obtain ⟨values, _, hv⟩ := each (C.terms.idxOf T) T (List.getElem?_idxOf (mem_terms T))
  simp only [if_pos held] at hv
  exact element_read_allowed prims K D r.2.1 _ (fun _ _ h => h)
    (.term T) hidden (ctx.prss.term T) label idx count values hv

/-- Non-self hidden pair streams are read by the same invocation. -/
theorem prss_pairs_read {α : Type} (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (k : PrssOutput C E → OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)) >>= k)).run s)) :
    ∀ j (ne : j ≠ ctx.self), Hidden D (.pair (C.pairOf ctx.self j ne.symm)) →
      ∀ g < elementBits * count,
        r.2.1.2 ((.pair (C.pairOf ctx.self j ne.symm), ctx.prss.pair j), label, idx, g) ≠ none := by
  obtain ⟨rnd, hdraw, _⟩ := (treeLockstep_logged_run_allowed prims D _ s r run).bind_inv
  have hr := free_ro_allowed (TreeLockstepWorldStreams prims D r.2.1) _ rnd hdraw
  unfold prssDraw at hr
  obtain ⟨terms, _, hrest⟩ := hr.bind_inv
  obtain ⟨pairs, hpairs, _⟩ := hrest.bind_inv
  intro j ne hidden
  obtain ⟨_, each⟩ := allowed_mapM_get _ _ C.parties pairs hpairs
  obtain ⟨values, _, hv⟩ := each (C.parties.idxOf j) j (List.getElem?_idxOf (by simp [Committee.parties] : j ∈ C.parties))
  simp only [dif_neg ne] at hv
  exact element_read_allowed prims K D r.2.1 _ (fun _ _ h => h)
    (.pair (C.pairOf ctx.self j ne.symm)) hidden (ctx.prss.pair j) label idx count values hv

/-- The same held-term read certificate in the unlogged stream world. -/
theorem prss_terms_read_stream {α : Type} (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (k : PrssOutput C E → OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C)
    (r : α × (HashCache C × HiddenCache C))
    (run : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)) >>= k)).run s)) :
    ∀ T, ctx.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g < elementBits * count, r.2.2 ((.term T, ctx.prss.term T), label, idx, g) ≠ none := by
  rw [← treeSimLoggedWorld_erase prims D _ s [], support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact prss_terms_read prims K D ctx label idx count k (s, []) u hu

/-- The same non-self pair read certificate in the unlogged stream world. -/
theorem prss_pairs_read_stream {α : Type} (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (k : PrssOutput C E → OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C)
    (r : α × (HashCache C × HiddenCache C))
    (run : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)) >>= k)).run s)) :
    ∀ j (ne : j ≠ ctx.self), Hidden D (.pair (C.pairOf ctx.self j ne.symm)) →
      ∀ g < elementBits * count,
        r.2.2 ((.pair (C.pairOf ctx.self j ne.symm), ctx.prss.pair j), label, idx, g) ≠ none := by
  rw [← treeSimLoggedWorld_erase prims D _ s [], support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact prss_pairs_read prims K D ctx label idx count k (s, []) u hu

end ReadSupport

section TwoRegions

open OracleComp.ProgramLogic.Relational
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- Encoded field blocks at two labels, with one frame outside their union. -/
structure TwoFieldCaches (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ : ℕ)
    (δ₀ : KeyName C → Fin n₀ → E) (δ₁ : KeyName C → Fin n₁ → E)
    (base₁ base₂ c₁ c₂ : HiddenCache C) : Prop where
  first : TreeStagesFieldBlock K D l₀ i₀ n₀ δ₀ c₁ c₂
  second : TreeStagesFieldBlock K D l₁ i₁ n₁ δ₁ c₁ c₂
  frame₁ : ∀ x, ¬ TreeStagesFieldRegion D l₀ i₀ n₀ x →
    ¬ TreeStagesFieldRegion D l₁ i₁ n₁ x → c₁ x = base₁ x
  frame₂ : ∀ x, ¬ TreeStagesFieldRegion D l₀ i₀ n₀ x →
    ¬ TreeStagesFieldRegion D l₁ i₁ n₁ x → c₂ x = base₂ x

variable {K} {D : C.Coalition} {l₀ i₀ n₀ l₁ i₁ n₁ : ℕ}
variable {δ₀ : KeyName C → Fin n₀ → E} {δ₁ : KeyName C → Fin n₁ → E}
variable {base₁ base₂ c₁ c₂ d₁ d₂ : HiddenCache C}

theorem TwoFieldCaches.symm (h : TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ c₁ c₂) :
    TwoFieldCaches K D l₁ i₁ n₁ l₀ i₀ n₀ δ₁ δ₀ base₁ base₂ c₁ c₂ :=
  ⟨h.second, h.first, fun x a b => h.frame₁ x b a, fun x a b => h.frame₂ x b a⟩

/-- A draw in the second region preserves the blocks of the first region. -/
theorem TwoFieldCaches.advance_second
    (h : TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ c₁ c₂)
    (sep : l₀ ≠ l₁) (hnew : TreeStagesFieldCaches K D l₁ i₁ n₁ δ₁ c₁ c₂ d₁ d₂) :
    TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ d₁ d₂ := by
  refine ⟨?_, hnew.blocks, ?_, ?_⟩
  · intro name key hh
    have outside (g : Fin (n₀ * elementBits)) :
        ¬ TreeStagesFieldRegion D l₁ i₁ n₁ ((name, key), l₀, i₀, g.val) :=
      fun hx => sep hx.2.1
    have h₁ := fun g => hnew.frame₁ ((name, key), l₀, i₀, g.val) (outside g)
    have h₂ := fun g => hnew.frame₂ ((name, key), l₀, i₀, g.val) (outside g)
    change _ ∨ _
    simp only [h₁, h₂]
    exact h.first name key hh
  · intro x hx₀ hx₁
    exact (hnew.frame₁ x hx₁).trans (h.frame₁ x hx₀ hx₁)
  · intro x hx₀ hx₁
    exact (hnew.frame₂ x hx₁).trans (h.frame₂ x hx₀ hx₁)

/-- Freshness at both labels initializes the two-region invariant. -/
theorem twoFieldCaches_initial (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ : ℕ)
    (δ₀ : KeyName C → Fin n₀ → E) (δ₁ : KeyName C → Fin n₁ → E) (c₁ c₂ : HiddenCache C)
    (f₀₁ : TreeSimFutureEmpty l₀ c₁) (f₀₂ : TreeSimFutureEmpty l₀ c₂)
    (f₁₁ : TreeSimFutureEmpty l₁ c₁) (f₁₂ : TreeSimFutureEmpty l₁ c₂) :
    TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ c₁ c₂ c₁ c₂ :=
  ⟨(treeStages_fieldCaches_initial K D l₀ i₀ n₀ δ₀ c₁ c₂ f₀₁ f₀₂).blocks,
   (treeStages_fieldCaches_initial K D l₁ i₁ n₁ δ₁ c₁ c₂ f₁₁ f₁₂).blocks,
   fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Exact public-cache agreement together with both encoded field regions. -/
def TwoFieldRel (K : Constants C E) (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ : ℕ)
    (δ₀ : KeyName C → Fin n₀ → E) (δ₁ : KeyName C → Fin n₁ → E)
    (base₁ base₂ : HiddenCache C) (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  a.1.1 = b.1 ∧ TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ a.1.2 b.2

/-- The existing block coupling preserves the complete two-region invariant. -/
theorem twoFieldDraws_second (sep : l₀ ≠ l₁)
    (visible : ∀ name, ¬ Hidden D name → δ₁ name = 0) :
    TreeStagesFieldDraws prims K D l₁ i₁ n₁ δ₁
      (TwoFieldRel K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂) := by
  intro name key a b hab
  have hc : TreeStagesFieldCaches K D l₁ i₁ n₁ δ₁ a.1.2 b.2 a.1.2 b.2 :=
    ⟨hab.2.second, fun _ _ => rfl, fun _ _ => rfl⟩
  apply relTriple_post_mono
    (treeStages_fieldDraws_closed prims K D l₁ i₁ n₁ δ₁ visible a.1.2 b.2 name key a b ⟨hab.1, hc⟩)
  intro u v huv
  exact ⟨huv.1, huv.2.1, hab.2.advance_second sep huv.2.2⟩

/-- The same invariant is preserved when the first region is drawn. -/
theorem twoFieldDraws_first (sep : l₀ ≠ l₁)
    (visible : ∀ name, ¬ Hidden D name → δ₀ name = 0) :
    TreeStagesFieldDraws prims K D l₀ i₀ n₀ δ₀
      (TwoFieldRel K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂) := by
  intro name key a b hab
  apply relTriple_post_mono
    (twoFieldDraws_second prims sep.symm visible name key a b ⟨hab.1, hab.2.symm⟩)
  intro u v huv
  exact ⟨huv.1, huv.2.1, huv.2.2.symm⟩

/-- A complete PRSS traversal preserves both field regions, including repeated holders. -/
theorem twoFieldPrss_second (sep : l₀ ≠ l₁)
    (visible : ∀ name, ¬ Hidden D name → δ₁ name = 0) (ctx : Context C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hab : TwoFieldRel K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) l₁ i₁ n₁) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) l₁ i₁ n₁) (LocalSpec C)))).run b)
      (fun u v => v.1 = u.1 + treeStagesPrssFieldShift ctx n₁ δ₁ ∧
        TwoFieldRel K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ u.2 v.2) :=
  treeStages_prss_field_shift prims K D ctx l₁ i₁ n₁ δ₁ _
    (twoFieldDraws_second prims sep visible) a b hab

/-- The corresponding traversal at the first label preserves the same invariant. -/
theorem twoFieldPrss_first (sep : l₀ ≠ l₁)
    (visible : ∀ name, ¬ Hidden D name → δ₀ name = 0) (ctx : Context C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hab : TwoFieldRel K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) l₀ i₀ n₀) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) l₀ i₀ n₀) (LocalSpec C)))).run b)
      (fun u v => v.1 = u.1 + treeStagesPrssFieldShift ctx n₀ δ₀ ∧
        TwoFieldRel K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ u.2 v.2) :=
  treeStages_prss_field_shift prims K D ctx l₀ i₀ n₀ δ₀ _
    (twoFieldDraws_first prims sep visible) a b hab

end TwoRegions

end ThresholdLeanXmssSecurity.TreeTwinPrefill

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.treeSim_prefill_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.treeSim_prefill_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.treeSim_prefill_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.treeSim_prefill_logged

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.treeSim_prefill_logged_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.treeSim_prefill_logged_table

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_terms_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_terms_read

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_pairs_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_pairs_read

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_terms_read_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_terms_read_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_pairs_read_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.prss_pairs_read_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldDraws_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldDraws_second

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldDraws_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldDraws_first

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldPrss_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldPrss_second

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldPrss_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinPrefill.twoFieldPrss_first
