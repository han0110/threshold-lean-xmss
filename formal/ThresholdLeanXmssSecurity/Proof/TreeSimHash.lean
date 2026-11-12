import ThresholdLeanXmssSecurity.Proof.TreeSim

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Auxiliary birthday region. Setup commitments and echoes establish agreement;
derived PRSS keys and stream-key points are still excluded. -/
def TreeSimHashBudgetDomain : Query C → Prop
  | .commit .. | .sharedKeys .. => True
  | q => TreeSimHashDomain q

theorem treeSimHash_domain_budget (q : Query C) (h : TreeSimHashDomain q) :
    TreeSimHashBudgetDomain q := by
  cases q <;> simp_all [TreeSimHashBudgetDomain, TreeSimHashDomain]

theorem treeSimHash_budget_excludes_paid (phase : Phase) (kind : KeyKind)
    (parts : List HashOutput) (key : HashOutput) :
    ¬ TreeSimHashBudgetDomain (Query.derive (C := C) phase kind parts) ∧
      ¬ TreeSimHashBudgetDomain (Query.streamKey (C := C) key) := by
  simp [TreeSimHashBudgetDomain, TreeSimHashDomain]

theorem treeSimHash_parties_le_terms : C.n ≤ termCount C := by
  have he : C.n / 2 = C.t - 1 := by
    have := C.one_le_t
    unfold Committee.n
    omega
  simpa only [Nat.choose_one_right, he, termCount] using Nat.choose_le_middle 1 C.n

/-- Even the raw three setup hash passes fit the setup allowance. -/
theorem treeSimHash_setup_capacity : 3 * C.n ^ 2 ≤
    C.n * (termCount C + C.n) + C.n ^ 2 := by
  have h := Nat.mul_le_mul_left C.n (treeSimHash_parties_le_terms (C := C))
  nlinarith

/-- Evaluate private hidden-stream sampling in the local language, retaining its cache. -/
def treeSimHashLocal (D : C.Coalition) :
    QueryImpl (LocalSpec C + LocalSpec C)
      (StateT (HiddenCache C) (OracleComp (LocalSpec C))) := fun t =>
  match t with
  | .inl t => StateT.lift (OracleComp.lift (OracleSpec.query t))
  | .inr (.inr (.inr x)) =>
      if Hidden D x.1 then StateT.mk fun cache =>
        liftComp (((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle
          ((x.1, x.2.1), x.2.2)).run cache) (LocalSpec C)
      else StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x))))
  | .inr t => StateT.lift (OracleComp.lift (OracleSpec.query t))

/-- Interpret the two caches without dropping either one. -/
def treeSimHashEvaluate (prims : Primitives) {α : Type}
    (p : StateT (HiddenCache C) (OracleComp (LocalSpec C)) α) :
    StateT (HashCache C × HiddenCache C) ProbComp α :=
  StateT.mk fun cache => (fun r => (r.1.1, r.2, r.1.2)) <$>
    (simulateQ (localAnswer prims) (p.run cache.2)).run cache.1

theorem treeSimHashEvaluate_pure (prims : Primitives) {α : Type} (a : α) :
    treeSimHashEvaluate prims (C := C) (pure a) = pure a := by
  apply StateT.ext
  intro cache
  simp [treeSimHashEvaluate]

theorem treeSimHashEvaluate_bind (prims : Primitives) {α β : Type}
    (p : StateT (HiddenCache C) (OracleComp (LocalSpec C)) α)
    (k : α → StateT (HiddenCache C) (OracleComp (LocalSpec C)) β) :
    treeSimHashEvaluate prims (p >>= k) =
      treeSimHashEvaluate prims p >>= fun a => treeSimHashEvaluate prims (k a) := by
  apply StateT.ext
  intro cache
  simp [treeSimHashEvaluate, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

theorem treeSimHashEvaluate_lift (prims : Primitives) {α : Type}
    (p : OracleComp (LocalSpec C) α) :
    treeSimHashEvaluate prims (StateT.lift p) = onHash (simulateQ (localAnswer prims) p) := by
  apply StateT.ext
  intro cache
  simp [treeSimHashEvaluate, StateT.run_lift, onHash, Functor.map_map]

theorem treeSimHashEvaluate_query (prims : Primitives) (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) :
    treeSimHashEvaluate prims (treeSimHashLocal D t) =
      simulateQ (streamWorld prims D) (treeSimLocalWorld t) := by
  rcases t with t | (t | q | x)
  · simp [treeSimHashLocal, treeSimLocalWorld, treeSimHashEvaluate_lift,
      streamWorld, QueryImpl.add_apply_inl]
    rfl
  · simp [treeSimHashLocal, treeSimLocalWorld, treeSimHashEvaluate_lift, streamWorld]
  · simp [treeSimHashLocal, treeSimLocalWorld, treeSimHashEvaluate_lift, streamWorld]
  · by_cases hx : Hidden D x.1
    · apply StateT.ext
      intro cache
      simp only [treeSimHashLocal, if_pos hx, treeSimHashEvaluate, StateT.run_mk]
      change (fun r : (Bit × HiddenCache C) × HashCache C => (r.1.1, r.2, r.1.2)) <$>
        (simulateQ (localAnswer prims) (liftComp
          (((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle
            ((x.1, x.2.1), x.2.2)).run cache.2) (LocalSpec C))).run cache.1 = _
      rw [run_liftComp_prob]
      simp [treeSimLocalWorld, streamWorld, hx, Functor.map_map]
    · simp [treeSimHashLocal, treeSimLocalWorld, treeSimHashEvaluate_lift, streamWorld, hx]

/-- Exact normalization of any nonprogramming execution, with both initial caches. -/
theorem treeSimHashEvaluate_simulate (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    treeSimHashEvaluate prims (simulateQ (treeSimHashLocal D) p) =
      simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [treeSimHashEvaluate_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, treeSimHashEvaluate_bind,
      treeSimHashEvaluate_query, ih]

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHashLocalLogged_run (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    (simulateQ ((streamWorld prims D).withTraceAppend
      (fun t u => ([⟨t, u⟩] : TreeSimLog C))) (simulateQ treeSimLocalWorld p)).run =
      simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld (treeSimLocalLogged p)) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [treeSimLocalLogged, WriterT.run_pure]
  | query_bind t k ih =>
    rcases t with t | t
    all_goals
      simp only [treeSimLocalLogged, simulateQ_bind, simulateQ_spec_query,
        treeSimLocalWorld, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        QueryImpl.withTraceAppend_apply, WriterT.run_bind,
        WriterT.run_liftM, WriterT.run_tell, pure_bind, bind_assoc,
        simulateQ_map, bind_map_left, Functor.map_map]
      apply bind_congr
      intro u
      congr 1
      exact ih u

/-- The actual log, normalized into local queries, preserves the shared cache. -/
theorem treeSimHash_logged (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    treeSimLoggedRun prims D (simulateQ treeSimLocalWorld p) =
      Prod.fst <$> (simulateQ (localAnswer prims)
        ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run ∅)).run' ∅ := by
  unfold treeSimLoggedRun
  rw [treeSimHashLocalLogged_run, ← treeSimHashEvaluate_simulate]
  simp [treeSimHashEvaluate, StateT.run'_eq, Functor.map_map]

/-!
Target: `treeSimHashBoundClosed : TreeSimHashBoundGoal prims K circuits settings`.
The terminal route takes `TreeSimHashTerminalBudget` and `TreeSimHashRawSaltEstimate`.
`treeSimHashBound_of_terminal` assembles these interface hypotheses.
The coarse region count applies to the actual normalized ceremony, retaining
both shared caches and excluding the already-paid PRSS points. It is at most
N², where N is the target budget. When N < 2^128, every good prefix has a good
completion; a final-cache bound therefore supplies the fresh-point certificate.
The earlier `TreeSimHashCeremonyBudget` / `TreeSimHashSaltEstimate` route is an alternative assembly. The large-budget estimate has no additional premise.

For terminal-cache induction, `treeSimHash_coin_points` needs
no prior Shamir validity. `treeSimHash_open_all_outputs` needs consistency only
on hidden terms, supplied locally by the final rerandomization in
`treeSimHash_rerand_hidden`. A whole-ceremony certificate must connect partial-abort prefixes and a common
public batch shape to the actual execution.

For salts, `treeSimHash_salt_table_bound` proves the union estimate for an
arbitrary adaptive opaque-block program, including interleaved public queries,
repeated blocks, and accidental salt collisions, with one shared hash cache.
Its bound is H*n/2^256 for H independently sampled opaque blocks and at most n
private or public digest queries. `treeSimHash_digest_column_rows_hit_bound`
also normalizes an actual holder column without history agreement. The salt interface requires the actual-ceremony representation by opaque blocks indexed by their shared
PRSS address; assigning an independent salt to each holder would be incorrect.
The local sampling connection is exact: `treeSimHash_salt_block_randomOracle`
identifies a completed real PRG block with a cached random-oracle salt read.
`treeSimHash_prssBits_logged_complete` and `treeSimHash_prssElements_complete`
preserve complete blocks through the real PRSS traversals. The combined salt
and digest entry is exposed by `treeSimHash_salt_digest_entry`.
`treeSimHash_lazy_address_bound` supplies the raw coefficient 2*H*n/2^256
for an opaque address program, via finite allocation and deferred sampling.
The whole-ceremony salt bridge must normalize the whole ceremony into that program,
preserve the actual counted-query/hidden-salt event, and establish its bounds.
-/

/-- A cache containing the logged answers also contains every logged region collision. -/
theorem treeSimHashCollision_cache (log : TreeSimLog C) (cache : HashCache C)
    (answers : ∀ q h, TreeSimHashDomain q → TreeSimHashAnswer log q h → cache q = some h)
    (bad : TreeSimHashCollision log) :
    CacheHasCollision (splitRegionCache TreeSimHashDomain cache) := by
  rcases bad with ⟨q, r, h, hq, hr, hne, hqh, hrh⟩
  exact ⟨q, r, h, h, hne,
    by simpa [splitRegionCache, hq] using answers q h hq hqh,
    by simpa [splitRegionCache, hr] using answers r h hr hrh, HEq.rfl⟩

/-- The fixed collision region suffices for the copy checks. -/
theorem treeSimHash_copy_region_good (cache : HashCache C)
    (good : ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain cache)) :
    ¬ MainCopyCollision cache := by
  rintro ⟨a, b, h, hab, ha, hb⟩
  apply good
  refine ⟨.copy a, .copy b, h, h, fun he => hab (Query.copy.inj he), ?_, ?_, HEq.rfl⟩
  · simpa only [splitRegionCache, TreeSimHashDomain, if_true] using ha
  · simpa only [splitRegionCache, TreeSimHashDomain, if_true] using hb

/-- Nonprogramming local calls only extend the hash cache. -/
theorem treeSimHash_local_mono (prims : Primitives) (t : (LocalSpec C).Domain)
    (cache : HashCache C) (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) : cache ≤ r.2 := by
  rcases isAtom_localAnswer prims t with ⟨p, hp⟩ | ⟨q, g, hq⟩
  · rw [hp] at hr
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    exact le_refl _
  · rw [hq, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    exact (randomOracle_support q cache u hu).1

def TreeSimHashCoherent (cache : HashCache C) (log : TreeSimLog C) : Prop :=
  ∀ q h, TreeSimHashDomain q → TreeSimHashAnswer log q h → cache q = some h

theorem TreeSimHashCoherent.mono {cache next : HashCache C} {log : TreeSimLog C}
    (h : TreeSimHashCoherent cache log) (hle : cache ≤ next) :
    TreeSimHashCoherent next log := fun q u hq hu => hle (h q u hq hu)

theorem TreeSimHashCoherent.append {cache : HashCache C} {a b : TreeSimLog C}
    (ha : TreeSimHashCoherent cache a) (hb : TreeSimHashCoherent cache b) :
    TreeSimHashCoherent cache (a ++ b) := by
  intro q u hq hu
  rcases hu with hu | hu <;> rcases List.mem_append.mp hu with hu | hu
  · exact ha q u hq (Or.inl hu)
  · exact hb q u hq (Or.inl hu)
  · exact ha q u hq (Or.inr hu)
  · exact hb q u hq (Or.inr hu)

theorem treeSimHash_local_log (prims : Primitives) (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) (cache : HashCache C × HiddenCache C)
    (r : (LocalSpec C + LocalSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimLocalWorld t)).run cache)) :
    cache.1 ≤ r.2.1 ∧ TreeSimHashCoherent r.2.1 (treeSimLocalLog t r.1) := by
  rcases t with (t | q | x) | (t | q | x)
  case inr.inr.inr =>
    by_cases hx : Hidden D x.1
    · simp [treeSimLocalWorld, streamWorld, onHash, hx] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      refine ⟨le_refl _, ?_⟩
      intro q h hq ha
      simp [TreeSimHashAnswer, treeSimLocalLog] at ha
    · simp [treeSimLocalWorld, streamWorld, onHash, hx] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      refine ⟨treeSimHash_local_mono prims (.inr (.inr x)) cache.1 _ hu, ?_⟩
      intro q h hq ha
      simp [TreeSimHashAnswer, treeSimLocalLog] at ha
  all_goals
    simp [treeSimLocalWorld, streamWorld, onHash] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    refine ⟨?_, ?_⟩
    · first
      | exact treeSimHash_local_mono prims (.inl t) cache.1 _ hu
      | exact treeSimHash_local_mono prims (.inr (.inl q)) cache.1 _ hu
      | exact treeSimHash_local_mono prims (.inr (.inr x)) cache.1 _ hu
    intro q' h hq' ha
    simp only [TreeSimHashAnswer, treeSimLocalLog, List.mem_singleton] at ha
    rcases ha with he | he <;> cases he
  all_goals
    exact hashAnswer_cached prims (by rintro ⟨input, rfl, _⟩; exact hq') cache.1 u hu

theorem treeSimHash_logged_step (prims : Primitives) (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) (s : TreeSimState C) :
    (simulateQ (treeSimLoggedWorld prims D) (treeSimLocalWorld t)).run s =
      (fun r => (r.1, r.2, s.2 ++ treeSimLocalLog t r.1)) <$>
        (simulateQ (streamWorld prims D) (treeSimLocalWorld t)).run s.1 := by
  rcases t with t | t <;>
    simp [treeSimLoggedWorld, treeSimLocalWorld, treeSimLocalLog]

/-- Logged answers remain in the shared hash cache throughout the actual run. -/
theorem treeSimHash_local_coherent (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hc : TreeSimHashCoherent s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld p)).run s)) :
    TreeSimHashCoherent r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    apply ih mid.1 mid.2 r _ hr
    rw [treeSimHash_logged_step, support_map] at hmid
    obtain ⟨u, hu, rfl⟩ := hmid
    have hs := treeSimHash_local_log prims D t s.1 u hu
    exact (hc.mono hs.1).append hs.2

theorem treeSimHash_state_normalize (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (hash : HashCache C) (hidden : HiddenCache C) :
    (simulateQ (treeSimLoggedWorld prims D) (simulateQ treeSimLocalWorld p)).run
      ((hash, hidden), []) =
      (fun r => (r.1.1.1, (r.2, r.1.2), r.1.1.2)) <$>
        (simulateQ (localAnswer prims)
          ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run hidden)).run hash := by
  rw [treeSimLoggedWorld_run, treeSimHashLocalLogged_run, ← treeSimHashEvaluate_simulate]
  simp [treeSimHashEvaluate, Functor.map_map]

theorem treeSimHash_normalized_coherent (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (hash : HashCache C) (hidden : HiddenCache C)
    (r : ((α × TreeSimLog C) × HiddenCache C) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run hidden)).run hash)) :
    TreeSimHashCoherent r.2 r.1.1.2 := by
  apply treeSimHash_local_coherent prims D p ((hash, hidden), [])
    (r.1.1.1, (r.2, r.1.2), r.1.1.2)
  · intro q h hq hh
    simpa [TreeSimHashAnswer] using hh
  · rw [treeSimHash_state_normalize, support_map]
    exact ⟨r, hr, rfl⟩

/-- A cached query retains the exact continuation and shared cache. -/
theorem treeSimHash_cached_step {α : Type} (q : Query C)
    (f : HashOutput → StateT (HashCache C) ProbComp α) (cache : HashCache C)
    (u : HashOutput) (hit : cache q = some u) :
    (((Query C →ₒ HashOutput).randomOracle q) >>= f).run cache = (f u).run cache := by
  simp only [StateT.run_bind, OracleSpec.randomOracle,
    QueryImpl.withCaching_run_some _ hit, pure_bind]

/-- Exact finite support of the selected part of the shared cache. -/
def TreeSimHashRegionKeys (P : Query C → Prop) (cache : HashCache C)
    (S : Finset (Query C)) : Prop := ∀ q, q ∈ S ↔ P q ∧ cache q ≠ none

theorem TreeSimHashRegionKeys.bound {P : Query C → Prop} {cache : HashCache C}
    {S : Finset (Query C)} (h : TreeSimHashRegionKeys P cache S) :
    SplitCacheBound (splitRegionCache P cache) S.card := by
  refine ⟨S, le_rfl, fun q hq => (h q).mpr ?_⟩
  by_cases hp : P q
  · exact ⟨hp, by simpa [splitRegionCache, hp] using hq⟩
  · simp [splitRegionCache, hp] at hq

theorem TreeSimHashRegionKeys.le_bound {P : Query C → Prop} {cache next : HashCache C}
    {S : Finset (Query C)} {N : ℕ} (h : TreeSimHashRegionKeys P cache S)
    (hle : cache ≤ next) (hb : SplitCacheBound (splitRegionCache P next) N) : S.card ≤ N := by
  obtain ⟨V, hv, hV⟩ := hb
  apply (Finset.card_le_card (t := V) ?_).trans hv
  intro q hq
  obtain ⟨hp, hc⟩ := (h q).mp hq
  apply hV q
  cases he : cache q with
  | none => exact (hc he).elim
  | some u => simp [splitRegionCache, hp, hle he]

/-- The birthday step with zero cost for repeated region inputs. -/
theorem treeSimHash_fresh_step {α : Type} (P : Query C → Prop) (q : Query C)
    (f : HashOutput → StateT (HashCache C) ProbComp α) (cache : HashCache C) (k : ℕ)
    (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (hk : SplitCacheBound (splitRegionCache P cache) k) (ε : ℝ≥0∞)
    (hf : ∀ u s, ¬ CacheHasCollision (splitRegionCache P s) →
      SplitCacheBound (splitRegionCache P s)
        (k + if P q ∧ cache q = none then 1 else 0) →
      Pr[fun z => CacheHasCollision (splitRegionCache P z.2) | (f u).run s] ≤ ε) :
    Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (((Query C →ₒ HashOutput).randomOracle q) >>= f).run cache] ≤
      (if P q ∧ cache q = none then (k : ℝ≥0∞) / 2 ^ 256 else 0) + ε := by
  cases hit : cache q with
  | none =>
    simpa only [and_true] using splitRegion_random_bind P q f cache k hno hk ε
      (by simpa only [hit, and_true] using hf)
  | some u =>
    simpa only [treeSimHash_cached_step q f cache u hit, Option.some_ne_none,
      and_false, ite_false, zero_add] using hf u cache hno
        (by simpa only [hit, Option.some_ne_none, and_false, ite_false, Nat.add_zero] using hk)

/-- A support-aware fresh step, suitable for adaptive executions with cached answers. -/
theorem treeSimHash_fresh_step_support {α : Type} (P : Query C → Prop) (q : Query C)
    (f : HashOutput → StateT (HashCache C) ProbComp α) (cache : HashCache C) (k : ℕ)
    (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (hk : SplitCacheBound (splitRegionCache P cache) k) (ε : ℝ≥0∞)
    (hf : ∀ u s, (u, s) ∈ support (((Query C →ₒ HashOutput).randomOracle q).run cache) →
      ¬ CacheHasCollision (splitRegionCache P s) →
      SplitCacheBound (splitRegionCache P s)
        (k + if P q ∧ cache q = none then 1 else 0) →
      Pr[fun z => CacheHasCollision (splitRegionCache P z.2) | (f u).run s] ≤ ε) :
    Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (((Query C →ₒ HashOutput).randomOracle q) >>= f).run cache] ≤
      (if P q ∧ cache q = none then (k : ℝ≥0∞) / 2 ^ 256 else 0) + ε := by
  cases hit : cache q with
  | some u =>
    simpa only [treeSimHash_cached_step q f cache u hit, Option.some_ne_none,
      and_false, ite_false, zero_add] using hf u cache
        (by simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hit,
          mem_support_pure_iff]) hno
        (by simpa only [hit, Option.some_ne_none, and_false, ite_false, Nat.add_zero] using hk)
  | none =>
    have hs : ∀ u : HashOutput, (u, cache.cacheQuery q u) ∈
        support (((Query C →ₒ HashOutput).randomOracle q).run cache) := by
      intro u
      simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hit,
        support_map, Set.mem_image]
      exact ⟨u, mem_support_uniformSample HashOutput, rfl⟩
    rw [StateT.run_bind, OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ hit, bind_map_left]
    by_cases hq : P q
    · simp only [hq, hit, and_self, ite_true] at hf ⊢
      have h := probEvent_bind_le_add
        (mx := ($ᵗ HashOutput)) (my := fun u => (f u).run (cache.cacheQuery q u))
        (p := fun u => ¬ CacheHasCollision (splitRegionCache P (cache.cacheQuery q u)))
        (q := fun z => ¬ CacheHasCollision (splitRegionCache P z.2))
        (ε₁ := (k : ℝ≥0∞) / 2 ^ 256) (ε₂ := ε)
        (by simpa only [not_not, splitRegionCache_insert P cache q _ hq]
          using splitHash_insert_birthday (splitRegionCache P cache) q k hno hk)
        (by
          intro u _ hu
          simp only [not_not]
          exact hf u _ (hs u) hu (by
            rw [splitRegionCache_insert P cache q u hq]
            exact hk.insert q u))
      simpa only [not_not, uniformSampleImpl] using h
    · simp only [hq, false_and, ite_false, Nat.add_zero, zero_add] at hf ⊢
      exact probEvent_bind_le_of_forall_le (fun u _ => hf u _ (hs u)
        (by simpa only [splitRegionCache_insert_irrelevant P cache q u hq] using hno)
        (by simpa only [splitRegionCache_insert_irrelevant P cache q u hq] using hk))

/-- A local operation creates a fresh point in the selected region. -/
def TreeSimHashFresh (P : Query C → Prop) (t : (LocalSpec C).Domain)
    (cache : HashCache C) : Prop :=
  ∃ q, splitLocalHashInput t = some q ∧ P q ∧ cache q = none

/-- A pathwise budget up to the first collision. Cache hits cost zero, and
only supported continuations with a collision-free cache require a certificate. -/
inductive TreeSimHashFreshBudget (prims : Primitives) (P : Query C → Prop) :
    {α : Type} → OracleComp (LocalSpec C) α → HashCache C → ℕ → Prop
  | pure {α : Type} (a : α) (cache : HashCache C) (n : ℕ) :
      TreeSimHashFreshBudget prims P (pure a) cache n
  | query_bind {α : Type} (t : (LocalSpec C).Domain)
      (f : (LocalSpec C).Range t → OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
      (positive : TreeSimHashFresh P t cache → 0 < n)
      (next : ∀ r ∈ support ((localAnswer prims t).run cache),
        ¬ CacheHasCollision (splitRegionCache P r.2) →
        TreeSimHashFreshBudget prims P (f r.1) r.2
          (n - if TreeSimHashFresh P t cache then 1 else 0)) :
      TreeSimHashFreshBudget prims P
        (OracleComp.lift (OracleSpec.query t) >>= f) cache n

theorem TreeSimHashFreshBudget.mono (prims : Primitives) (P : Query C → Prop)
    {α : Type} {p : OracleComp (LocalSpec C) α} {cache : HashCache C} {n m : ℕ}
    (h : TreeSimHashFreshBudget prims P p cache n) (hnm : n ≤ m) :
    TreeSimHashFreshBudget prims P p cache m := by
  induction h generalizing m with
  | pure a cache n => exact .pure a cache m
  | query_bind t f cache n hp hn ih =>
    apply TreeSimHashFreshBudget.query_bind t f cache m
    · intro ht
      exact lt_of_lt_of_le (hp ht) hnm
    · intro r hr hno
      exact ih r hr hno (Nat.sub_le_sub_right hnm _)

/-- A syntactic region budget suffices for adversarial queries; cached calls can only reduce it. -/
theorem treeSimHash_fresh_of_queryBound (prims : Primitives) (P : Query C → Prop)
    {α : Type} (p : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
    (h : IsQueryBoundP p (SplitRegionCounted P) n) :
    TreeSimHashFreshBudget prims P p cache n := by
  induction p using OracleComp.inductionOn generalizing n cache with
  | pure a => exact .pure a cache n
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have hc : TreeSimHashFresh P t cache → SplitRegionCounted P t := by
      rintro ⟨q, hq, hp, _⟩
      exact ⟨q, hq, hp⟩
    apply TreeSimHashFreshBudget.query_bind t f cache n
    · intro ht
      exact h.1.resolve_left (not_not.mpr (hc ht))
    · intro r _ _
      apply (ih r.1 r.2 _ (h.2 r.1)).mono prims P
      split_ifs with hcount hfresh hfresh
      · exact le_refl _
      · omega
      · exact (hcount (hc hfresh)).elim
      · exact le_refl _

/-- A local step adds exactly one selected key precisely when it is fresh. -/
theorem treeSimHash_region_keys_step (prims : Primitives) (P : Query C → Prop)
    (t : (LocalSpec C).Domain) (cache : HashCache C) (S : Finset (Query C))
    (keys : TreeSimHashRegionKeys P cache S)
    (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) :
    ∃ S', TreeSimHashRegionKeys P r.2 S' ∧
      S'.card = S.card + if TreeSimHashFresh P t cache then 1 else 0 := by
  cases hi : splitLocalHashInput t with
  | none =>
    obtain ⟨p, hp⟩ := splitLocalHashInput_none prims t hi
    rw [hp] at hr
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    refine ⟨S, keys, ?_⟩
    simp [TreeSimHashFresh, hi]
  | some q =>
    obtain ⟨f, hf⟩ := splitLocalHashInput_some prims t q hi
    rw [hf, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    obtain ⟨_, hq, hother⟩ := randomOracle_support q cache u hu
    have fresh : TreeSimHashFresh P t cache ↔ P q ∧ cache q = none := by
      simp [TreeSimHashFresh, hi]
    by_cases hp : P q
    · refine ⟨insert q S, ?_, ?_⟩
      · intro a
        by_cases ha : a = q
        · subst a
          simp [hp, hq]
        · simpa [ha, hother a ha] using keys a
      · by_cases hc : cache q = none
        · have hnot : q ∉ S := fun hs => (keys q).mp hs |>.2 hc
          simp [Finset.card_insert_of_notMem hnot, fresh, hp, hc]
        · have hmem : q ∈ S := (keys q).mpr ⟨hp, hc⟩
          simp [Finset.insert_eq_of_mem hmem, fresh, hp, hc]
    · refine ⟨S, ?_, ?_⟩
      · intro a
        by_cases ha : a = q
        · subst a
          simpa [hp] using keys q
        · simpa [hother a ha] using keys a
      · simp [fresh, hp]

/-- Before the region exhausts the hash range, every local call has a supported
collision-free answer, including calls outside the charged region. -/
theorem treeSimHash_good_step (prims : Primitives) (P : Query C → Prop)
    (t : (LocalSpec C).Domain) (cache : HashCache C) (S : Finset (Query C))
    (keys : TreeSimHashRegionKeys P cache S)
    (good : ¬ CacheHasCollision (splitRegionCache P cache)) (small : S.card < 2 ^ 256) :
    ∃ r ∈ support ((localAnswer prims t).run cache),
      ¬ CacheHasCollision (splitRegionCache P r.2) := by
  cases hi : splitLocalHashInput t with
  | none =>
    obtain ⟨p, hp⟩ := splitLocalHashInput_none prims t hi
    have hne : (support p).Nonempty := by
      by_contra hn
      have he := (probFailure_eq_one_iff_not_nonempty p).mpr hn
      simpa using he
    obtain ⟨u, hu⟩ := hne
    refine ⟨(u, cache), ?_, good⟩
    rw [hp]
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image]
    exact ⟨u, hu, rfl⟩
  | some q =>
    obtain ⟨f, hf⟩ := splitLocalHashInput_some prims t q hi
    cases hc : cache q with
    | some u =>
      refine ⟨(f u, cache), ?_, good⟩
      rw [hf, StateT.run_map, OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc]
      simp
    | none =>
      have supported (u : HashOutput) : (f u, cache.cacheQuery q u) ∈
          support ((localAnswer prims t).run cache) := by
        simp only [hf, StateT.run_map, OracleSpec.randomOracle,
          QueryImpl.withCaching_run_none _ hc, Functor.map_map, support_map, Set.mem_image]
        exact ⟨u, mem_support_uniformSample HashOutput, rfl⟩
      by_cases hp : P q
      · let V := S.image (fun a => (cache a).getD 0)
        have card : V.card < Fintype.card HashOutput := by
          have hashcard : Fintype.card HashOutput = 2 ^ 256 := by
            unfold HashOutput hashOutputBits
            exact card_bitVec 256
          rw [hashcard]
          exact lt_of_le_of_lt Finset.card_image_le small
        have absent : ∃ u : HashOutput, u ∉ V := by
          by_contra hn
          push_neg at hn
          have hle := Finset.card_le_card (show Finset.univ ⊆ V from fun u _ => hn u)
          simp only [Finset.card_univ] at hle
          exact (Nat.not_lt_of_le hle) card
        obtain ⟨u, hu⟩ := absent
        refine ⟨(f u, cache.cacheQuery q u), supported u, ?_⟩
        rw [splitRegionCache_insert P cache q u hp]
        intro bad
        obtain ⟨a, ha⟩ := splitHash_insert_collision _ q u good bad
        have haP : P a := by by_contra hn; simp [splitRegionCache, hn] at ha
        have hac : cache a = some u := by simpa [splitRegionCache, haP] using ha
        exact hu (Finset.mem_image.mpr ⟨a, (keys a).mpr ⟨haP, by simp [hac]⟩,
          by simp [hac]⟩)
      · refine ⟨(f 0, cache.cacheQuery q 0), supported 0, ?_⟩
        change ¬ CacheHasCollision (splitRegionCache P (cache.cacheQuery q 0))
        rw [splitRegionCache_insert_irrelevant P cache q 0 hp]
        exact good

/-- The shared cache grows through an arbitrary local continuation. -/
theorem treeSimHash_program_mono (prims : Primitives) {α : Type}
    (p : OracleComp (LocalSpec C) α) (cache : HashCache C) (r : α × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) p).run cache)) : cache ≤ r.2 := by
  induction p using OracleComp.inductionOn generalizing cache with
  | pure a =>
    simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using hr
      |> fun he => he ▸ le_rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, hr⟩ := hr
    exact (treeSimHash_local_mono prims t cache a ha).trans (ih a.1 a.2 hr)

/-- A coarse query bound below the hash-range size ensures a collision-free
completion of every supported good prefix. The bound need not be tight. -/
theorem treeSimHash_good_completion (prims : Primitives) (P : Query C → Prop) {α : Type}
    (p : OracleComp (LocalSpec C) α) (cache : HashCache C) (S : Finset (Query C)) (n : ℕ)
    (keys : TreeSimHashRegionKeys P cache S)
    (good : ¬ CacheHasCollision (splitRegionCache P cache))
    (coarse : IsQueryBoundP p (SplitRegionCounted P) n) (small : S.card + n < 2 ^ 256) :
    ∃ r ∈ support ((simulateQ (localAnswer prims) p).run cache),
      ¬ CacheHasCollision (splitRegionCache P r.2) := by
  induction p using OracleComp.inductionOn generalizing cache S n with
  | pure a => exact ⟨(a, cache), by simp, good⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at coarse
    obtain ⟨a, ha, hgood⟩ := treeSimHash_good_step prims P t cache S keys good (by omega)
    obtain ⟨S', hkeys, hcard⟩ := treeSimHash_region_keys_step prims P t cache S keys a ha
    have hn : (if SplitRegionCounted P t then 1 else 0) ≤ n := by
      split_ifs with ht
      · have := coarse.1.resolve_left (not_not.mpr ht)
        omega
      · omega
    have hcost : (if TreeSimHashFresh P t cache then 1 else 0) ≤
        (if SplitRegionCounted P t then 1 else 0) := by
      by_cases hf : TreeSimHashFresh P t cache
      · obtain ⟨q, hq, hp, _⟩ := hf
        rw [if_pos (show SplitRegionCounted P t from ⟨q, hq, hp⟩)]
        split_ifs <;> omega
      · simp [hf]
    have hs : S'.card + (if SplitRegionCounted P t then n - 1 else n) < 2 ^ 256 := by
      by_cases ht : SplitRegionCounted P t
      · simp only [if_pos ht] at hn hcost ⊢
        omega
      · simp only [if_neg ht] at hn hcost ⊢
        omega
    obtain ⟨r, hr, hgr⟩ := ih a.1 a.2 S' _ hkeys hgood (coarse.2 a.1) hs
    refine ⟨r, ?_, hgr⟩
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    exact ⟨a, ha, hr⟩

/-- A bound on complete good runs suffices for the adaptive fresh-point budget
when a coarse query bound guarantees good completions. No per-call remaining
budget needs to be carried by the protocol's execution invariant. -/
theorem treeSimHash_fresh_of_terminal_bound (prims : Primitives) (P : Query C → Prop)
    {α : Type} (p : OracleComp (LocalSpec C) α) (cache : HashCache C)
    (S : Finset (Query C)) (N n : ℕ) (keys : TreeSimHashRegionKeys P cache S)
    (good : ¬ CacheHasCollision (splitRegionCache P cache))
    (coarse : IsQueryBoundP p (SplitRegionCounted P) n) (small : S.card + n < 2 ^ 256)
    (terminal : ∀ r ∈ support ((simulateQ (localAnswer prims) p).run cache),
      ¬ CacheHasCollision (splitRegionCache P r.2) → SplitCacheBound (splitRegionCache P r.2) N) :
    TreeSimHashFreshBudget prims P p cache (N - S.card) := by
  induction p using OracleComp.inductionOn generalizing cache S n with
  | pure a => exact .pure a cache _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at coarse
    have hcount : (if SplitRegionCounted P t then 1 else 0) ≤ n := by
      split_ifs with ht
      · have := coarse.1.resolve_left (not_not.mpr ht)
        omega
      · omega
    have hcost : (if TreeSimHashFresh P t cache then 1 else 0) ≤
        (if SplitRegionCounted P t then 1 else 0) := by
      by_cases hf : TreeSimHashFresh P t cache
      · have counted : SplitRegionCounted P t := by
          obtain ⟨q, hq, hp, _⟩ := hf
          exact ⟨q, hq, hp⟩
        simp [hf, counted]
      · simp [hf]
    have nextSmall (S' : Finset (Query C))
        (hc : S'.card = S.card + if TreeSimHashFresh P t cache then 1 else 0) :
        S'.card + (if SplitRegionCounted P t then n - 1 else n) < 2 ^ 256 := by
      by_cases ht : SplitRegionCounted P t
      · simp only [if_pos ht] at hcount hcost ⊢
        omega
      · simp only [if_neg ht] at hcount hcost ⊢
        omega
    have finish (a : (LocalSpec C).Range t × HashCache C)
        (ha : a ∈ support ((localAnswer prims t).run cache))
        (r : α × HashCache C) (hr : r ∈ support ((simulateQ (localAnswer prims) (k a.1)).run a.2))
        (hgr : ¬ CacheHasCollision (splitRegionCache P r.2)) :
        SplitCacheBound (splitRegionCache P r.2) N := by
      apply terminal r _ hgr
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨a, ha, hr⟩
    apply TreeSimHashFreshBudget.query_bind
    · intro fresh
      obtain ⟨a, ha, hga⟩ := treeSimHash_good_step prims P t cache S keys good (by omega)
      obtain ⟨S', hkeys, hcard⟩ := treeSimHash_region_keys_step prims P t cache S keys a ha
      obtain ⟨r, hr, hgr⟩ := treeSimHash_good_completion prims P (k a.1) a.2 S' _
        hkeys hga (coarse.2 a.1) (nextSmall S' hcard)
      have leN := hkeys.le_bound (treeSimHash_program_mono prims (k a.1) a.2 r hr) (finish a ha r hr hgr)
      simp only [if_pos fresh] at hcard
      omega
    · intro a ha hga
      obtain ⟨S', hkeys, hcard⟩ := treeSimHash_region_keys_step prims P t cache S keys a ha
      have hb := ih a.1 a.2 S' _ hkeys hga (coarse.2 a.1) (nextSmall S' hcard) (finish a ha)
      convert hb using 1
      omega

/-- Composition retains the actual shared cache and only uses supported, good continuations. -/
theorem TreeSimHashFreshBudget.bind (prims : Primitives) (P : Query C → Prop)
    {α β : Type} {p : OracleComp (LocalSpec C) α} {f : α → OracleComp (LocalSpec C) β}
    {cache : HashCache C} {n m : ℕ} (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (h : TreeSimHashFreshBudget prims P p cache n)
    (hf : ∀ r ∈ support ((simulateQ (localAnswer prims) p).run cache),
      ¬ CacheHasCollision (splitRegionCache P r.2) →
      TreeSimHashFreshBudget prims P (f r.1) r.2 m) :
    TreeSimHashFreshBudget prims P (p >>= f) cache (n + m) := by
  induction h with
  | pure a cache n =>
    simpa only [pure_bind] using
      (hf (a, cache) (by simp) hno).mono prims P (Nat.le_add_left m n)
  | query_bind t k cache n hp hn ih =>
    rw [bind_assoc]
    apply TreeSimHashFreshBudget.query_bind t _ cache (n + m)
    · intro ht
      exact lt_of_lt_of_le (hp ht) (Nat.le_add_right n m)
    · intro r hr hnr
      have hc := ih r hr hnr hnr (fun u hu hnu => hf u (by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨r, hr, hu⟩) hnu)
      convert hc using 1
      split_ifs with ht
      · have := hp ht
        omega
      · omega

/-- A queried random-oracle input is present in the shared cache afterwards. -/
theorem treeSimHash_local_present (prims : Primitives) (t : (LocalSpec C).Domain)
    (q : Query C) (ht : splitLocalHashInput t = some q) (cache : HashCache C)
    (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) : r.2 q ≠ none := by
  obtain ⟨f, hf⟩ := splitLocalHashInput_some prims t q ht
  rw [hf, StateT.run_map, support_map] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  have h := randomOracle_support q cache u hu
  rw [h.2.1]
  exact Option.some_ne_none _

def treeSimHashMissing (S : Finset (Query C)) (cache : HashCache C) : Finset (Query C) :=
  S.filter (fun q => cache q = none)

theorem treeSimHash_missing_mono (S : Finset (Query C)) {a b : HashCache C}
    (hab : a ≤ b) : treeSimHashMissing S b ⊆ treeSimHashMissing S a := by
  intro q hq
  obtain ⟨hq, hb⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨hq, ?_⟩
  cases ha : a q with
  | none => rfl
  | some u => have := hab ha; simp_all

/-- A finite point cover pays once per input, regardless of how often holders repeat it. -/
theorem treeSimHash_fresh_of_cover (prims : Primitives) (P : Query C → Prop)
    {α : Type} (p : OracleComp (LocalSpec C) α) (S : Finset (Query C))
    (cache : HashCache C)
    (h : IsQueryBoundP p (SplitRegionCounted (fun q => P q ∧ q ∉ S)) 0) :
    TreeSimHashFreshBudget prims P p cache (treeSimHashMissing S cache).card := by
  induction p using OracleComp.inductionOn generalizing cache with
  | pure a => exact .pure a cache _
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ SplitRegionCounted (fun q => P q ∧ q ∉ S) t := h.1.resolve_right (by omega)
    have hc : ∀ q, splitLocalHashInput t = some q → P q → q ∈ S := by
      intro q hq hp
      by_contra hs
      exact ht ⟨q, hq, hp, hs⟩
    have hf : ∀ q, splitLocalHashInput t = some q → P q → cache q = none →
        q ∈ treeSimHashMissing S cache := by
      intro q hq hp hz
      exact Finset.mem_filter.mpr ⟨hc q hq hp, hz⟩
    apply TreeSimHashFreshBudget.query_bind t f cache _
    · rintro ⟨q, hq, hp, hz⟩
      exact Finset.card_pos.mpr ⟨q, hf q hq hp hz⟩
    · intro r hr _
      have hn : IsQueryBoundP (f r.1) (SplitRegionCounted (fun q => P q ∧ q ∉ S)) 0 := by
        simpa only [if_neg ht] using h.2 r.1
      apply (ih r.1 r.2 hn).mono prims P
      have hm := treeSimHash_missing_mono S (treeSimHash_local_mono prims t cache r hr)
      split_ifs with fresh
      · obtain ⟨q, hq, hp, hz⟩ := fresh
        have hqS := hf q hq hp hz
        have hsub : treeSimHashMissing S r.2 ⊆ (treeSimHashMissing S cache).erase q := by
          intro a ha
          apply Finset.mem_erase.mpr
          refine ⟨?_, hm ha⟩
          intro he
          subst a
          exact treeSimHash_local_present prims t q hq cache r hr (Finset.mem_filter.mp ha).2
        exact (Finset.card_le_card hsub).trans_eq (Finset.card_erase_of_mem hqS)
      · simpa only [Nat.sub_zero] using Finset.card_le_card hm

theorem treeSimHash_lift_ro_region (P : Query C → Prop)
    {α : Type} {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => SplitRegionCounted P (.inr t)) n) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (SplitRegionCounted P) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftComp_bind]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr t)) >>=
      fun u => liftComp (k u) (LocalSpec C)) (SplitRegionCounted P) n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- The concrete hash loop uses the finite cover with its original shared cache. -/
theorem treeSimHash_hashes_fresh (prims : Primitives) (P : Query C → Prop)
    (qs : List (Query C)) (S : Finset (Query C))
    (cover : ∀ q ∈ qs, P q → q ∈ S) (cache : HashCache C) :
    TreeSimHashFreshBudget prims P (liftComp (qs.mapM hashQuery) (LocalSpec C))
      cache (treeSimHashMissing S cache).card := by
  apply treeSimHash_fresh_of_cover
  apply treeSimHash_lift_ro_region
  have h := queryBound_mapM
    (fun t => SplitRegionCounted (fun q => P q ∧ q ∉ S) (.inr t)) hashQuery 0 qs
    (fun q hq => ?_)
  · simpa only [Nat.mul_zero] using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
    rw [isQueryBoundP_query_iff]
    rintro ⟨r, hr, hp, hnot⟩
    by_cases hfixed : IsFixed q
    · simp [splitLocalHashInput, hfixed] at hr
    · simp only [splitLocalHashInput, if_neg hfixed, Option.some.injEq] at hr
      subst r
      exact (hnot (cover q hq hp)).elim

/-- A birthday bound charging distinct region points, with no charge for cache hits. -/
theorem treeSimHash_fresh_birthday_aux (prims : Primitives) (P : Query C → Prop)
    {α : Type} {oa : OracleComp (LocalSpec C) α} {cache : HashCache C} {n : ℕ}
    (budget : TreeSimHashFreshBudget prims P oa cache n) :
    ∀ k, ¬ CacheHasCollision (splitRegionCache P cache) →
      SplitCacheBound (splitRegionCache P cache) k →
      Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
        (simulateQ (localAnswer prims) oa).run cache] ≤
        ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  induction budget with
  | pure a cache n =>
    intro k hno _
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hno, if_false, zero_le]
  | query_bind t f cache n positive next ih =>
    intro k hno hk
    change Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (localAnswer prims t >>= fun u => simulateQ (localAnswer prims) (f u)).run cache] ≤ _
    cases he : splitLocalHashInput t with
    | none =>
      obtain ⟨p, hp⟩ := splitLocalHashInput_none prims t he
      have hfresh : ¬ TreeSimHashFresh P t cache := by simp [TreeSimHashFresh, he]
      simp only [hp, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine probEvent_bind_le_of_forall_le (fun u hu => ?_)
      simpa only [hfresh, ite_false, Nat.sub_zero] using
        ih (u, cache) (by simpa [hp, StateT.run_lift] using hu) hno k hno hk
    | some q =>
      obtain ⟨g, hg⟩ := splitLocalHashInput_some prims t q he
      have fresh : TreeSimHashFresh P t cache ↔ P q ∧ cache q = none := by
        simp [TreeSimHashFresh, he]
      have hs : ∀ u s, (u, s) ∈ support (((Query C →ₒ HashOutput).randomOracle q).run cache) →
          (g u, s) ∈ support ((localAnswer prims t).run cache) := by
        intro u s hu
        rw [hg, StateT.run_map, support_map]
        exact ⟨(u, s), hu, rfl⟩
      rw [hg, bind_map_left]
      by_cases hfresh : P q ∧ cache q = none
      · have hn : 0 < n := positive (fresh.mpr hfresh)
        have hsum : (k : ℝ≥0∞) / 2 ^ 256 +
            ∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 =
            ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          conv_rhs => rw [show n = (n - 1) + 1 from by omega]
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [show k + 1 + j = k + (j + 1) by omega]
        have h := treeSimHash_fresh_step_support P q
          (fun u => simulateQ (localAnswer prims) (f (g u))) cache k hno hk
          (∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256)
          (by
            intro u s hu hno' hk'
            simpa only [if_pos (fresh.mpr hfresh)] using
              ih (g u, s) (hs u s hu) hno' (k + 1) hno'
                (by simpa only [if_pos hfresh] using hk'))
        simpa only [if_pos hfresh, hsum] using h
      · have hn : ¬ TreeSimHashFresh P t cache := fun h => hfresh (fresh.mp h)
        have h := treeSimHash_fresh_step_support P q
          (fun u => simulateQ (localAnswer prims) (f (g u))) cache k hno hk
          (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256)
          (by
            intro u s hu hno' hk'
            simpa only [if_neg hn, Nat.sub_zero] using
              ih (g u, s) (hs u s hu) hno' k hno'
                (by simpa only [if_neg hfresh, Nat.add_zero] using hk'))
        simpa only [if_neg hfresh, zero_add] using h

theorem treeSimHash_fresh_birthday (prims : Primitives) (P : Query C → Prop)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ)
    (budget : TreeSimHashFreshBudget prims P oa ∅ n) :
    Pr[fun z => CacheHasCollision (splitRegionCache P z.2) |
      (simulateQ (localAnswer prims) oa).run ∅] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * 2 ^ 256) := by
  have hempty : splitRegionCache P (∅ : HashCache C) = ∅ := by
    funext q
    simp [splitRegionCache]
  have h := treeSimHash_fresh_birthday_aux prims P budget 0
    (by rw [hempty]; rintro ⟨a, b, u, v, _, ha, _, _⟩; simp at ha)
    (by rw [hempty]; exact ⟨∅, by simp, fun t ht => (ht rfl).elim⟩)
  simp only [Nat.zero_add, div_eq_mul_inv] at h
  exact h.trans_eq (ENNReal.gauss_sum_inv_eq n (2 ^ 256))

/-- A fresh-point budget for the normalized actual trace bounds its fixed collision event. -/
theorem treeSimHash_logged_birthday (prims : Primitives) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ)
    (budget : TreeSimHashFreshBudget prims TreeSimHashDomain
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run ∅) ∅ n) :
    Pr[fun r => TreeSimHashCollision r.2 |
      treeSimLoggedRun prims D (simulateQ treeSimLocalWorld p)] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * 2 ^ 256) := by
  rw [treeSimHash_logged, probEvent_map, StateT.run'_eq, probEvent_map]
  refine le_trans ?_ (treeSimHash_fresh_birthday prims TreeSimHashDomain _ n budget)
  apply probEvent_mono
  intro r hr hbad
  exact treeSimHashCollision_cache _ _
    (treeSimHash_normalized_coherent prims D p ∅ ∅ r hr) hbad

/-- An auxiliary region may stop earlier while still bounding the fixed logged collision. -/
theorem treeSimHash_logged_birthday_region (prims : Primitives) (D : C.Coalition)
    (P : Query C → Prop) (contains : ∀ q, TreeSimHashDomain q → P q)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ)
    (budget : TreeSimHashFreshBudget prims P
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run ∅) ∅ n) :
    Pr[fun r => TreeSimHashCollision r.2 |
      treeSimLoggedRun prims D (simulateQ treeSimLocalWorld p)] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * 2 ^ 256) := by
  rw [treeSimHash_logged, probEvent_map, StateT.run'_eq, probEvent_map]
  refine le_trans ?_ (treeSimHash_fresh_birthday prims P _ n budget)
  apply probEvent_mono
  intro r hr hbad
  have hc := treeSimHash_normalized_coherent prims D p ∅ ∅ r hr
  obtain ⟨a, b, h, ha, hb, hne, hah, hbh⟩ := hbad
  exact ⟨a, b, h, h, hne,
    by simpa only [splitRegionCache, if_pos (contains a ha)] using hc a h ha hah,
    by simpa only [splitRegionCache, if_pos (contains b hb)] using hc b h hb hbh, HEq.rfl⟩

/-- The fixed hash event has just these two probability contributions. -/
theorem treeSimHash_union {α : Type} (D : C.Coalition)
    (p : ProbComp (α × TreeSimLog C)) :
    (Pr[fun r => TreeSimHashBad D r.2 | p]).toReal ≤
      (Pr[fun r => TreeSimHashCollision r.2 | p]).toReal +
      (Pr[fun r => TreeSimSaltGuess D r.2 | p]).toReal := by
  have h := probEvent_or_le p (fun r => TreeSimHashCollision r.2)
    (fun r => TreeSimSaltGuess D r.2)
  simpa only [TreeSimHashBad, ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] using
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) h

/-- The birthday half and the salt guesses fit the stated square budget. -/
theorem treeSimHash_union_arith (q s : ℕ) :
    ((q + s : ℕ) : ℝ) ^ 2 / (2 * 2 ^ 256) + (q * s : ℕ) / (2 : ℝ) ^ 256 ≤
      ((q + s : ℕ) : ℝ) ^ 2 / 2 ^ 256 := by
  rw [div_mul_eq_div_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast
  nlinarith [sq_nonneg (q : ℝ), sq_nonneg (s : ℝ)]

/-- Salt guesses need only be charged outside the collision event. -/
theorem treeSimHash_union_clean {α : Type} (D : C.Coalition)
    (p : ProbComp (α × TreeSimLog C)) :
    (Pr[fun r => TreeSimHashBad D r.2 | p]).toReal ≤
      (Pr[fun r => TreeSimHashCollision r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
    (probEvent_or_le (mx := p) (fun r => TreeSimHashCollision r.2)
      (fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2))
  simpa [or_and_left, Classical.em, TreeSimHashBad,
    ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] using h

theorem treeSimHash_union_clean_arith (N H : ℝ) (hN : 0 ≤ N) (hH : 4 * H ≤ N) :
    N ^ 2 / (2 * 2 ^ 256) + 2 * H * N / 2 ^ 256 ≤ N ^ 2 / 2 ^ 256 := by
  calc
    _ = (N ^ 2 + (4 * H) * N) / (2 * 2 ^ 256) := by ring
    _ ≤ (N ^ 2 + N * N) / (2 * 2 ^ 256) :=
      div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hH hN))
        (by positivity)
    _ = _ := by ring

/-- Counting repeated salt uses still fits the square once the query budget is retained. -/
theorem treeSimHash_union_raw_arith (N q H : ℝ) (hq : 0 ≤ q) (hH : 0 ≤ H)
    (hbudget : q + 2 * H ≤ N) :
    N ^ 2 / (2 * 2 ^ 256) + 2 * H * (q + H) / 2 ^ 256 ≤ N ^ 2 / 2 ^ 256 := by
  have hN : 0 ≤ N := by linarith
  have hs : (q + 2 * H) ^ 2 ≤ N ^ 2 := by nlinarith
  have hc : 4 * H * (q + H) ≤ N ^ 2 := by nlinarith [sq_nonneg q]
  calc
    _ = (N ^ 2 + 4 * H * (q + H)) / (2 * 2 ^ 256) := by ring
    _ ≤ (N ^ 2 + N ^ 2) / (2 * 2 ^ 256) :=
      div_le_div_of_nonneg_right (add_le_add le_rfl hc) (by positivity)
    _ = _ := by ring

abbrev TreeSimHashSaltBlock (C : Committee) := C.Term × HashOutput × ℕ

def treeSimHashSaltAddress (b : TreeSimHashSaltBlock C) (g : Fin 256) : HiddenAddress C :=
  ((.term b.1, b.2.1), b.2.2, 2, g.val)

theorem treeSimHash_salt_address_injective (b : TreeSimHashSaltBlock C) :
    Function.Injective (treeSimHashSaltAddress b) := by
  intro i j he
  exact Fin.ext (congrArg (fun x => x.2.2.2) he)

theorem treeSimHash_salt_address_block {a b : TreeSimHashSaltBlock C} {g h : Fin 256}
    (he : treeSimHashSaltAddress a g = treeSimHashSaltAddress b h) : a = b := by
  rcases a with ⟨T, key, label⟩
  rcases b with ⟨T', key', label'⟩
  simpa only [treeSimHashSaltAddress, Prod.mk.injEq, KeyName.term.injEq, true_and, and_assoc] using
    And.intro (congrArg (fun x => x.1) he) (congrArg (fun x => x.2.1) he)

/-- Atomic salt reads preserve this invariant even when their labels are reused. -/
def TreeSimHashSaltBlocksComplete (cache : HiddenCache C) : Prop :=
  ∀ b : TreeSimHashSaltBlock C,
    (∀ g, cache (treeSimHashSaltAddress b g) = none) ∨
      ∃ vals : Fin 256 → Bit, ∀ g, cache (treeSimHashSaltAddress b g) = some (vals g)

theorem treeSimHash_salt_blocks_empty : TreeSimHashSaltBlocksComplete (∅ : HiddenCache C) := by
  intro b
  exact Or.inl (fun _ => rfl)

theorem treeSimHash_salt_blocks_install (cache : HiddenCache C)
    (hc : TreeSimHashSaltBlocksComplete cache) (b : TreeSimHashSaltBlock C) (vals : Fin 256 → Bit) :
    TreeSimHashSaltBlocksComplete (cacheFin (treeSimHashSaltAddress b) vals cache) := by
  intro a
  by_cases hab : a = b
  · subst a
    exact Or.inr ⟨vals, cacheFin_at _ (treeSimHash_salt_address_injective b) vals cache⟩
  · have he (g : Fin 256) : cacheFin (treeSimHashSaltAddress b) vals cache (treeSimHashSaltAddress a g) =
        cache (treeSimHashSaltAddress a g) :=
      cacheFin_of_not_mem _ vals cache _ (fun _ h => hab (treeSimHash_salt_address_block h))
    simpa only [he] using hc a

/-- A fresh actual salt draw is a uniform block jointly with its exact shared
cache, private cache and log. This is the real `Rand(_,2)` stream, not a new draw. -/
theorem treeSimHash_salt_block_fresh (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬ KnownTo D.1 b.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (fresh : ∀ g, streams (treeSimHashSaltAddress b g) = none) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C)))).run
        ((cache, streams), log)] =
      𝒟[(fun vals : Fin 256 → Bit => ((fun g => (List.ofFn vals).getD g 0),
        (cache, cacheFin (treeSimHashSaltAddress b) vals streams),
        log ++ treeSimHiddenLog (treeSimHashSaltAddress b) vals)) <$> ($ᵗ (Fin 256 → Bit))] := by
  have hh : ∀ g, Hidden D (treeSimHashSaltAddress b g).1.1 := fun _ => hidden
  have he := streamWorld_sequenceFin_fresh prims D (treeSimHashSaltAddress b)
    (treeSimHash_salt_address_injective b) hh cache streams fresh
  rw [treeSim_prgBits_table, simulateQ_map, StateT.run_map, treeSim_hiddenDraws_log]
  simp only [evalDist_map]
  rw [show 𝒟[(simulateQ (streamWorld prims D)
      (hiddenDraws (fun g : Fin 256 => ((.term b.1, b.2.1), b.2.2, 2, g.val)))).run (cache, streams)] =
      𝒟[(fun vals => (vals, (cache, cacheFin (treeSimHashSaltAddress b) vals streams))) <$>
        ($ᵗ (Fin 256 → Bit))] from he]
  simp only [← evalDist_map, Functor.map_map, Function.comp_def]
  rfl

theorem treeSimHash_salt_block_logged (D : C.Coalition) (b : TreeSimHashSaltBlock C)
    (hidden : ¬ KnownTo D.1 b.1) (vals : Fin 256 → Bit) (log : TreeSimLog C) :
    TreeSimHiddenSalt D (log ++ treeSimHiddenLog (treeSimHashSaltAddress b) vals) (List.ofFn vals) := by
  refine ⟨List.length_ofFn, b.1, b.2.1, b.2.2, hidden, ?_⟩
  intro g
  apply List.mem_append_right
  simp only [treeSimHiddenLog, List.mem_ofFn]
  refine ⟨g, ?_⟩
  simp only [treeSimHashSaltAddress, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, dif_pos g.isLt, Option.getD_some]

set_option maxRecDepth 4096 in
/-- Every completed real salt read leaves a complete block and records exactly
the salt returned. A repeated address uses the original cached block. -/
theorem treeSimHash_salt_block_support (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬ KnownTo D.1 b.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams)
    (r : (ℕ → Bit) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C)))).run
        ((cache, streams), log))) :
    ∃ vals : Fin 256 → Bit,
      r.1 = (fun g => (List.ofFn vals).getD g 0) ∧ r.2.1.1 = cache ∧
      (∀ g, r.2.1.2 (treeSimHashSaltAddress b g) = some (vals g)) ∧
      TreeSimHashSaltBlocksComplete r.2.1.2 ∧
      r.2.2 = log ++ treeSimHiddenLog (treeSimHashSaltAddress b) vals ∧
      TreeSimHiddenSalt D r.2.2 (List.ofFn vals) := by
  rcases complete b with fresh | ⟨vals, cached⟩
  · have he := treeSimHash_salt_block_fresh prims D b hidden cache streams log fresh
    rw [mem_support_iff_of_evalDist_eq he, support_map, Set.mem_image] at hr
    obtain ⟨vals, _, rfl⟩ := hr
    exact ⟨vals, rfl, rfl, cacheFin_at _ (treeSimHash_salt_address_injective b) vals streams,
      treeSimHash_salt_blocks_install streams complete b vals, rfl,
      treeSimHash_salt_block_logged D b hidden vals log⟩
  · rw [treeSim_prgBits_cached_logged prims D (.term b.1) hidden b.2.1 b.2.2 2 256 vals
      cache streams log cached, mem_support_pure_iff] at hr
    subst r
    exact ⟨vals, rfl, rfl, cached, complete, rfl, treeSimHash_salt_block_logged D b hidden vals log⟩

/-- View the complete bit blocks as one cached random oracle of 256-bit salts. -/
def treeSimHashSaltLookup (streams : HiddenCache C) :
    (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).QueryCache := fun b =>
  (streams (treeSimHashSaltAddress b 0)).map fun _ =>
    fun g => (streams (treeSimHashSaltAddress b g)).getD 0

theorem treeSimHash_salt_lookup_none (streams : HiddenCache C) (b : TreeSimHashSaltBlock C)
    (fresh : ∀ g, streams (treeSimHashSaltAddress b g) = none) :
    treeSimHashSaltLookup streams b = none := by
  simp only [treeSimHashSaltLookup, fresh, Option.map_none]

theorem treeSimHash_salt_lookup_some (streams : HiddenCache C) (b : TreeSimHashSaltBlock C)
    (vals : Fin 256 → Bit) (cached : ∀ g, streams (treeSimHashSaltAddress b g) = some (vals g)) :
    treeSimHashSaltLookup streams b = some vals := by
  simp only [treeSimHashSaltLookup, cached, Option.map_some, Option.getD_some]

set_option maxRecDepth 4096 in
theorem treeSimHash_salt_lookup_install (streams : HiddenCache C) (b : TreeSimHashSaltBlock C)
    (vals : Fin 256 → Bit) :
    treeSimHashSaltLookup (cacheFin (treeSimHashSaltAddress b) vals streams) =
      (treeSimHashSaltLookup streams).cacheQuery b vals := by
  funext a
  by_cases hab : a = b
  · subst a
    rw [QueryCache.cacheQuery_self]
    exact treeSimHash_salt_lookup_some _ b vals
      (cacheFin_at _ (treeSimHash_salt_address_injective b) vals streams)
  · rw [QueryCache.cacheQuery_of_ne _ _ hab]
    have hf (g : Fin 256) := cacheFin_of_not_mem (treeSimHashSaltAddress b) vals streams
      (treeSimHashSaltAddress a g) (fun _ h => hab (treeSimHash_salt_address_block h))
    simp only [treeSimHashSaltLookup, hf]

set_option maxRecDepth 4096 in
/-- The actual logged PRG block implements one lazy random-oracle salt read,
including rereads under shared keys and labels. -/
theorem treeSimHash_salt_block_randomOracle (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬ KnownTo D.1 b.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) :
    𝒟[(fun r => ((fun g : Fin 256 => r.1 g.val), treeSimHashSaltLookup r.2.1.2)) <$>
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C)))).run
          ((cache, streams), log))] =
      𝒟[((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run
        (treeSimHashSaltLookup streams)] := by
  rcases complete b with fresh | ⟨vals, cached⟩
  · rw [evalDist_map, treeSimHash_salt_block_fresh prims D b hidden cache streams log fresh,
      ← evalDist_map, Functor.map_map]
    rw [QueryImpl.withCaching_run_none _ (treeSimHash_salt_lookup_none streams b fresh)]
    apply congrArg (fun f : (Fin 256 → Bit) →
      (Fin 256 → Bit) × (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).QueryCache =>
        𝒟[f <$> ($ᵗ (Fin 256 → Bit))])
    funext vals
    apply Prod.ext
    · funext g
      simp only [Function.comp_def, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        dif_pos g.isLt, Option.getD_some]
    · exact treeSimHash_salt_lookup_install streams b vals
  · rw [treeSim_prgBits_cached_logged prims D (.term b.1) hidden b.2.1 b.2.2 2 256 vals
      cache streams log cached, map_pure]
    rw [QueryImpl.withCaching_run_some _ (treeSimHash_salt_lookup_some streams b vals cached)]
    apply congrArg (fun vals : Fin 256 → Bit =>
      𝒟[(pure (vals, treeSimHashSaltLookup streams) :
        ProbComp ((Fin 256 → Bit) × (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).QueryCache))])
    funext g
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos g.isLt, Option.getD_some]

/-- Support invariants compose through the actual stateful traversals. -/
theorem treeSimHash_state_mapM_invariant {ι α σ : Type}
    (P : σ → Prop) (f : ι → StateT σ ProbComp α) (xs : List ι)
    (step : ∀ i ∈ xs, ∀ s r, P s → r ∈ support ((f i).run s) → P r.2)
    (s : σ) (hs : P s) (r : List α × σ)
    (hr : r ∈ support ((xs.mapM f).run s)) : P r.2 := by
  induction xs generalizing s r with
  | nil =>
    have he : r = ([], s) := by simpa using hr
    simpa only [he] using hs
  | cons i xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact ih (fun j hj => step j (List.mem_cons_of_mem i hj)) u.2
      (step i (List.mem_cons_self ..) s u hs hu) v hv

theorem treeSimHash_state_sequenceFin_invariant {α σ : Type} {n : ℕ}
    (P : σ → Prop) (f : Fin n → StateT σ ProbComp α)
    (step : ∀ i s r, P s → r ∈ support ((f i).run s) → P r.2)
    (s : σ) (hs : P s) (r : (Fin n → α) × σ)
    (hr : r ∈ support ((Concrete.sequenceFin f).run s)) : P r.2 := by
  induction n generalizing s with
  | zero =>
    have he : r = (Fin.elim0, s) := by simpa [Concrete.sequenceFin] using hr
    simpa only [he] using hs
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact ih (fun i => f i.succ) (fun i => step i.succ) u.2 (step 0 s u hs hu) v hv

/-- Reads outside the term-salt addresses preserve every complete salt block. -/
theorem treeSimHash_prgBits_salt_frame (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label idx count : ℕ)
    (separate : ∀ b : TreeSimHashSaltBlock C, ∀ g : Fin 256, ∀ j : Fin count,
      treeSimHashSaltAddress b g ≠ ((name, key), label, idx, j.val))
    (s : HashCache C × HiddenCache C) (r : (ℕ → Bit) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key label idx count) (LocalSpec C)))).run s)) :
    ∀ b g, r.2.2 (treeSimHashSaltAddress b g) = s.2 (treeSimHashSaltAddress b g) := by
  rw [treeSim_prgBits_table] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  intro b g
  simp only [hiddenDraws, simulateQ_sequenceFin] at hu
  apply treeSimHash_state_sequenceFin_invariant
    (fun t : HashCache C × HiddenCache C =>
      t.2 (treeSimHashSaltAddress b g) = s.2 (treeSimHashSaltAddress b g)) _ _ s rfl u hu
  intro j t v ht hv
  exact (treeSim_hiddenQuery_frame prims D _ _ (separate b g j) t v hv).trans ht

theorem treeSimHash_visibleQuery_cache (prims : Primitives) (D : C.Coalition)
    (x : HiddenAddress C) (visible : ¬ Hidden D x.1.1)
    (s : HashCache C × HiddenCache C) (r : Bit × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (hiddenQuery x)).run s)) :
    r.2.2 = s.2 := by
  unfold hiddenQuery at hr
  erw [simulateQ_spec_query] at hr
  simp only [streamWorld, visible, if_false, onHash] at hr
  change r ∈ support ((fun u : Bit × HashCache C => (u.1, u.2, s.2)) <$>
    (localAnswer prims (.inr (.inr (x.1.1, x.1.2, x.2)))).run s.1) at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨u, _, rfl⟩ := hr
  rfl

theorem treeSimHash_prgBits_visible_cache (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (visible : ¬ Hidden D name) (key : HashOutput) (label idx count : ℕ)
    (s : HashCache C × HiddenCache C) (r : (ℕ → Bit) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key label idx count) (LocalSpec C)))).run s)) :
    r.2.2 = s.2 := by
  rw [treeSim_prgBits_table] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  simp only [hiddenDraws, simulateQ_sequenceFin] at hu
  apply treeSimHash_state_sequenceFin_invariant
    (fun t : HashCache C × HiddenCache C => t.2 = s.2) _ _ s rfl u hu
  intro j t v ht hv
  exact (treeSimHash_visibleQuery_cache prims D _ visible t v hv).trans ht

/-- The concrete PRG calls used by the ceremony never leave a partial salt.
Indices zero and one and all pair streams preserve term-salt entries. -/
theorem treeSimHash_prgBits_complete (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label idx count : ℕ)
    (size : idx = 2 → count = 256)
    (s : HashCache C × HiddenCache C) (complete : TreeSimHashSaltBlocksComplete s.2)
    (r : (ℕ → Bit) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key label idx count) (LocalSpec C)))).run s)) :
    TreeSimHashSaltBlocksComplete r.2.2 := by
  by_cases hidden : Hidden D name
  · by_cases hi : idx = 2
    · subst idx
      have hn := size rfl
      subst count
      cases name with
      | parameter => exact False.elim hidden
      | term T =>
        have he := treeSimLoggedWorld_erase prims D
          (free (liftComp (prgBits (.term T) key label 2 256) (LocalSpec C))) s []
        rw [← he, support_map, Set.mem_image] at hr
        obtain ⟨u, hu, rfl⟩ := hr
        obtain ⟨vals, _, _, _, hc, _⟩ := treeSimHash_salt_block_support prims D
          (T, key, label) hidden s.1 s.2 [] complete u hu
        exact hc
      | pair p =>
        have hf := treeSimHash_prgBits_salt_frame prims D (.pair p) key label 2 256
          (by intro b g j h
              have hh : KeyName.term b.1 = KeyName.pair p := congrArg (fun x => x.1.1) h
              cases hh) s r hr
        intro b
        simpa only [hf] using complete b
    · have hf := treeSimHash_prgBits_salt_frame prims D name key label idx count
        (by intro b g j h; exact hi (congrArg (fun x => x.2.2.1) h).symm) s r hr
      intro b
      simpa only [hf] using complete b
  · rw [treeSimHash_prgBits_visible_cache prims D name hidden key label idx count s r hr]
    exact complete

variable {E : Type} [Field E] [Algebra Bit E]

theorem treeSimHash_mapM_ro {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (impl : QueryImpl (WorldSpec C) m) (xs : List α) (f : α → OracleComp (RoSpec C) β) :
    simulateQ impl (free (liftComp (xs.mapM f) (LocalSpec C))) =
      xs.mapM (fun x => simulateQ impl (free (liftComp (f x) (LocalSpec C)))) := by
  rw [keygen_liftComp_mapM]
  unfold free
  erw [simulateQ_list_mapM, simulateQ_list_mapM]

/-- The real term and pair traversals preserve any invariant of completed draws. -/
theorem treeSimHash_prssDraw_invariant {R : Type} [Zero R]
    (prims : Primitives) (D : C.Coalition) (codec : Codec C E R)
    (ctx : Context C) (label idx count : ℕ) (P : HashCache C × HiddenCache C → Prop)
    (draw : ∀ name key s r, P s → r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (codec.draw name key label idx count) (LocalSpec C)))).run s) → P r.2)
    (s : HashCache C × HiddenCache C) (hs : P s)
    (r : PrssOutput C R × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx codec label idx count) (LocalSpec C)))).run s)) :
    P r.2 := by
  have term : ∀ t u, P t → u ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (termDraws ctx codec label idx count) (LocalSpec C)))).run t) → P u.2 := by
    intro t u ht hu
    unfold termDraws at hu
    rw [treeSimHash_mapM_ro] at hu
    apply treeSimHash_state_mapM_invariant P _ _ _ t ht u hu
    intro T _ a b ha hb
    by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held] at hb
      exact draw _ _ a b ha hb
    · simp [held, liftComp_pure, free_pure] at hb
      subst b
      exact ha
  have pair : ∀ t u, P t → u ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (pairDraws ctx codec label idx count) (LocalSpec C)))).run t) → P u.2 := by
    intro t u ht hu
    unfold pairDraws at hu
    rw [treeSimHash_mapM_ro] at hu
    apply treeSimHash_state_mapM_invariant P _ _ _ t ht u hu
    intro j _ a b ha hb
    by_cases hj : j = ctx.self
    · simp [hj, liftComp_pure, free_pure] at hb
      subst b
      exact ha
    · simp only [dif_neg hj] at hb
      exact draw _ _ a b ha hb
  unfold prssDraw at hr
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, v, hv, rfl⟩ := hr
  exact pair u.2 v (term s u hs hu) hv

theorem treeSimHash_prssBits_complete (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label idx count : ℕ) (size : idx = 2 → count = 256)
    (s : HashCache C × HiddenCache C) (complete : TreeSimHashSaltBlocksComplete s.2)
    (r : PrssOutput C Bit × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) label idx count) (LocalSpec C)))).run s)) :
    TreeSimHashSaltBlocksComplete r.2.2 :=
  treeSimHash_prssDraw_invariant prims D bitCodec ctx label idx count
    (fun t => TreeSimHashSaltBlocksComplete t.2)
    (fun name key s r hs hr => treeSimHash_prgBits_complete prims D name key label idx count
      size s hs r hr) s complete r hr

theorem treeSimHash_prssElements_complete (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (ctx : Context C) (label idx count : ℕ) (idx_ne : idx ≠ 2)
    (s : HashCache C × HiddenCache C) (complete : TreeSimHashSaltBlocksComplete s.2)
    (r : PrssOutput C E × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run s)) :
    TreeSimHashSaltBlocksComplete r.2.2 := by
  apply treeSimHash_prssDraw_invariant prims D (elementCodec K) ctx label idx count
    (fun t => TreeSimHashSaltBlocksComplete t.2) _ s complete r hr
  intro name key a b ha hb
  simp only [elementCodec, liftComp_bind, liftComp_pure, free_bind, free_pure,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
    Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hb
  obtain ⟨u, hu, rfl⟩ := hb
  exact treeSimHash_prgBits_complete prims D name key label idx _
    (fun h => False.elim (idx_ne h)) a ha u hu

theorem treeSimHash_prssBits_logged_complete (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label idx count : ℕ) (size : idx = 2 → count = 256)
    (s : TreeSimState C) (complete : TreeSimHashSaltBlocksComplete s.1.2)
    (r : PrssOutput C Bit × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) label idx count) (LocalSpec C)))).run s)) :
    TreeSimHashSaltBlocksComplete r.2.1.2 := by
  apply treeSimHash_prssBits_complete (E := E) prims D ctx label idx count size s.1 complete (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- The salt draw and digest pass form one local entry before the next exchange. -/
def treeSimHashSaltDigestDraw (ctx : Context C) (st : RunState C) :
    OracleComp (RoSpec C) (List HashOutput) := do
  let rnd ← prssDraw ctx (bitCodec (E := E)) st.label 2 256
  digestQuery ctx.self rnd.1 st.history

theorem treeSimHash_salt_digest_entry (K : Constants C E) {α : Type}
    (ctx : Context C) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α) :
    worldRoles.honest (advance ((((prssRandomness ctx bitCodec 2 256 >>= fun rnd =>
      compareDigests ctx rnd.1).run st >>= k).run))) =
      (fun ds => treeSimCheckStep K (.digests (fun _ => ds)) ctx.self (k ((), nextLabel st))) <$>
        free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st) (LocalSpec C)) := by
  rw [prssRandomness_run, bind_assoc]
  simp only [worldRoles, advance_oracleStep_bind, free_bind, treeSimHashSaltDigestDraw,
    liftComp_bind, map_bind]
  apply bind_congr
  intro rnd
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq _
  exact treeSim_digest_entry K ctx rnd.1 (nextLabel st) k

section SaltProbability

variable {ι σ α : Type} {S : OracleSpec ι}

/-- Any salt-independent adaptive oracle has the projected-query salt bound. -/
theorem treeSimHash_projected_salt_bound (impl : QueryImpl S (StateT σ ProbComp))
    (project : ι → Option (List Bit)) (oa : OracleComp S α)
    (s : σ) (charged : ι → Prop) [DecidablePred charged]
    (hproject : ∀ t,(project t).isSome → charged t)
    (q : ℕ) (hq : IsQueryBoundP oa charged q) :
    Pr[fun z : α × σ × Bool => z.2.2=true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries impl (fun t => decide (project t = some (List.ofFn salt)))) oa).run (s,false))] ≤
      (q : ℝ≥0∞)/2^256 := by
  let raw := (simulateQ (projectQueries impl project) oa).run (s,[])
  let trace := (fun z : α × σ × List (List Bit) => z.2.2) <$> raw
  have ht : ∀ l ∈ support trace,l.length ≤ q := by
    intro l hl
    simp only [trace,support_map,Set.mem_image] at hl
    obtain ⟨z,hz,rfl⟩ := hl
    simpa using projectQueries_length impl charged project
      hproject hq s [] hz
  have hb := independent_salt_trace_bound trace q ht
  have hp : ∀ salt : Fin 256 → Bit,
      Pr[fun z : α × σ × Bool => z.2.2=true |
        (simulateQ (flagQueries impl (fun t => decide (project t = some (List.ofFn salt)))) oa).run (s,false)] =
      Pr[fun l => List.ofFn salt ∈ l | trace] := by
    intro salt
    have he := projectQueries_flag impl project (List.ofFn salt) oa s []
    simp only [List.not_mem_nil,decide_false] at he
    have he' : (simulateQ (flagQueries impl
        (fun t => decide (project t=some (List.ofFn salt)))) oa).run (s,false) =
        (fun z : α × σ × List (List Bit) => (z.1,(z.2.1,decide (List.ofFn salt ∈ z.2.2)))) <$> raw := by
      convert he.symm using 1 <;> congr
      · funext t
        by_cases h : project t=some (List.ofFn salt) <;> simp only [h,decide_true,decide_false]
      · funext z
        by_cases h : List.ofFn salt ∈ z.2.2 <;> simp only [h,decide_true,decide_false]
    rw [he',probEvent_map]
    simp only [trace,probEvent_map,Function.comp_def,decide_eq_true_eq]
  have he : Pr[fun z : α × σ × Bool => z.2.2=true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries impl (fun t => decide (project t = some (List.ofFn salt)))) oa).run (s,false))] =
      Pr[fun p : List (List Bit) × (Fin 256 → Bit) => List.ofFn p.2 ∈ p.1 | (do
        let l ← trace; let salt ← $ᵗ (Fin 256 → Bit); pure (l,salt))] := by
    simp only [probEvent_bind_eq_tsum,hp,probEvent_pure]
    simp only [probEvent_eq_tsum_ite]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro l
    apply tsum_congr
    intro salt
    split_ifs <;> simp [mul_comm]

  rw [he]
  exact hb

theorem treeSimHash_flag_true (impl : QueryImpl S (StateT σ ProbComp))
    (bad : ι → Bool) (p : OracleComp S α) (s : σ) :
    Pr[fun r : α × σ × Bool => r.2.2 = true |
      (simulateQ (flagQueries impl bad) p).run (s, true)] = 1 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      flagQueries_run, bind_map_left, Bool.true_or]
    simp only [probEvent_bind_eq_tsum, ih, mul_one]
    simp

theorem treeSimHash_flag_mono (impl : QueryImpl S (StateT σ ProbComp))
    (bad₁ bad₂ : ι → Bool) (hbad : ∀ t, bad₁ t = true → bad₂ t = true)
    (p : OracleComp S α) (s : σ) (b₁ b₂ : Bool) (hb : b₁ = true → b₂ = true) :
    Pr[fun r : α × σ × Bool => r.2.2 = true |
      (simulateQ (flagQueries impl bad₁) p).run (s, b₁)] ≤
    Pr[fun r : α × σ × Bool => r.2.2 = true |
      (simulateQ (flagQueries impl bad₂) p).run (s, b₂)] := by
  induction p using OracleComp.inductionOn generalizing s b₁ b₂ with
  | pure a => cases b₁ <;> cases b₂ <;> simp_all
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, flagQueries_run, bind_map_left]
    apply probEvent_bind_mono
    intro r _
    apply ih r.1 r.2
    simp only [Bool.or_eq_true]
    exact fun h => h.imp hb (hbad t)

/-- Oracle changes at flagged inputs preserve the probability of the first flag. -/
theorem treeSimHash_first_hit_eq
    (impl₁ impl₂ : QueryImpl S (StateT σ ProbComp)) (bad : ι → Bool)
    (heq : ∀ t s, bad t = false → (impl₁ t).run s = (impl₂ t).run s)
    (p : OracleComp S α) (s : σ) :
    Pr[fun r : α × σ × Bool => r.2.2 = true |
      (simulateQ (flagQueries impl₁ bad) p).run (s, false)] =
    Pr[fun r : α × σ × Bool => r.2.2 = true |
      (simulateQ (flagQueries impl₂ bad) p).run (s, false)] := by
  have step : ∀ t s u s',
      Pr[= (u, (s', false)) | (flagQueries impl₁ bad t).run (s, false)] =
      Pr[= (u, (s', false)) | (flagQueries impl₂ bad t).run (s, false)] := by
    intro t s u s'
    cases hb : bad t with
    | false => simp only [flagQueries_run, heq t s hb]
    | true =>
      have hz (impl : QueryImpl S (StateT σ ProbComp)) :
          Pr[= (u, (s', false)) | (flagQueries impl bad t).run (s, false)] = 0 := by
        apply probOutput_eq_zero_of_not_mem_support
        simp [flagQueries_run, hb]
      rw [hz impl₁, hz impl₂]
  have sticky (impl : QueryImpl S (StateT σ ProbComp)) (p : OracleComp S α)
      (s s' : σ) (a : α) :
      Pr[= (a, (s', false)) | (simulateQ (flagQueries impl bad) p).run (s, true)] = 0 :=
    probOutput_simulateQ_run_eq_zero_of_bad (flagQueries impl bad) (fun r => r.2 = true)
      (flagQueries_mono impl bad) p (s, true) rfl a (s', false) Bool.false_ne_true
  have good : ∀ (p : OracleComp S α) s a s',
      Pr[= (a, (s', false)) | (simulateQ (flagQueries impl₁ bad) p).run (s, false)] =
      Pr[= (a, (s', false)) | (simulateQ (flagQueries impl₂ bad) p).run (s, false)] := by
    intro p
    induction p using OracleComp.inductionOn with
    | pure a => intros; rfl
    | query_bind t k ih =>
      intro s a s'
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      apply tsum_congr
      rintro ⟨u, s'', b⟩
      cases b with
      | false => rw [step t s u s'', ih u s'' a s']
      | true => rw [sticky impl₁, sticky impl₂, mul_zero, mul_zero]
  have not_hit :
      Pr[fun r : α × σ × Bool => ¬r.2.2 = true |
        (simulateQ (flagQueries impl₁ bad) p).run (s, false)] =
      Pr[fun r : α × σ × Bool => ¬r.2.2 = true |
        (simulateQ (flagQueries impl₂ bad) p).run (s, false)] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    apply tsum_congr
    rintro ⟨a, s', b⟩
    cases b <;> simp only [Bool.false_eq_true, not_false_eq_true, ite_true,
      not_true_eq_false, ite_false]
    exact good p s a s'
  have h₁ := probEvent_compl ((simulateQ (flagQueries impl₁ bad) p).run (s, false))
    (fun r : α × σ × Bool => r.2.2 = true)
  have h₂ := probEvent_compl ((simulateQ (flagQueries impl₂ bad) p).run (s, false))
    (fun r : α × σ × Bool => r.2.2 = true)
  simp only [probFailure_eq_zero, tsub_zero] at h₁ h₂
  rw [not_hit] at h₁
  exact (ENNReal.add_left_inj probEvent_ne_top).mp (h₁.trans h₂.symm)

/-- Programming is compatible with the salt-guess monitor, including its final flag. -/
theorem treeSimHash_programmed_flag (prims : Primitives) (salt : List Bit)
    (h d : HashOutput) (p : OracleComp (LocalSpec C) α) (cache : HashCache C) (b : Bool) :
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) p).run
      (cache.cacheQuery (.digest salt h) d, b) =
      (fun r => (r.1, r.2.1.cacheQuery (.digest salt h) d, r.2.2)) <$>
        (simulateQ (flagQueries (patchedDigestLocal prims salt h d) (digestSaltHit salt)) p).run
          (cache, b) := by
  induction p using OracleComp.inductionOn generalizing cache b with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, flagQueries_run,
      localAnswer_digest_programmed, bind_map_left, map_bind, Functor.map_map]
    apply bind_congr
    intro r
    exact ih r.1 r.2 _

theorem treeSimHash_programmed_hit_eq (prims : Primitives) (salt : List Bit)
    (h d : HashOutput) (p : OracleComp (LocalSpec C) α) (cache : HashCache C) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) p).run
        (cache.cacheQuery (.digest salt h) d, false)] =
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) p).run (cache, false)] := by
  rw [treeSimHash_programmed_flag, probEvent_map]
  apply (treeSimHash_first_hit_eq (localAnswer prims) (patchedDigestLocal prims salt h d)
    (digestSaltHit salt) ?_ p cache).symm
  intro t s ht
  rcases t with n | q | x
  · rfl
  · have hq : q ≠ .digest salt h := by intro hq; subst q; simp [digestSaltHit] at ht
    change (hashAnswer prims q).run s = (patchedDigestHash prims salt h d q).run s
    simp [patchedDigestHash, hq]
  · rfl

/-- A planted hidden digest does not increase the first-guess probability. -/
theorem treeSimHash_programmed_salt_bound (prims : Primitives) (cache : HashCache C)
    (h d : (Fin 256 → Bit) → HashOutput) (p : OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : IsQueryBoundP p DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) p).run
        (cache.cacheQuery (.digest (List.ofFn salt) (h salt)) (d salt), false))] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have hb := digestSaltFlag_boundP prims p cache DigestQuery (fun _ ht => ht) q hq
  rw [probEvent_bind_eq_tsum] at hb ⊢
  simpa only [treeSimHash_programmed_hit_eq] using hb

/-- Install the rows for one salt without replacing the shared dealer cache. -/
def treeSimHashPlantSalt (cache : HashCache C) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) : HashCache C :=
  rows.foldl (fun cache row => cache.cacheQuery (.digest salt row.1) row.2) cache

/-- All holders may install rows for the same hidden salt in the shared cache. -/
theorem treeSimHash_planted_rows_hit_eq (prims : Primitives) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) (p : OracleComp (LocalSpec C) α) (cache : HashCache C) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) p).run
        (treeSimHashPlantSalt cache salt rows, false)] =
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) p).run (cache, false)] := by
  induction rows generalizing cache with
  | nil => rfl
  | cons row rows ih =>
    change Pr[_ | (simulateQ (flagQueries (localAnswer prims) (digestSaltHit salt)) p).run
      (treeSimHashPlantSalt (cache.cacheQuery (.digest salt row.1) row.2) salt rows, false)] = _
    rw [ih, treeSimHash_programmed_hit_eq]

/-- The salt bound charges a shared block once, irrespective of its number of holders. -/
theorem treeSimHash_planted_rows_bound (prims : Primitives) (cache : HashCache C)
    (rows : (Fin 256 → Bit) → List (HashOutput × HashOutput))
    (p : OracleComp (LocalSpec C) α) (q : ℕ) (hq : IsQueryBoundP p DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) p).run
        (treeSimHashPlantSalt cache (List.ofFn salt) (rows salt), false))] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have hb := digestSaltFlag_boundP prims p cache DigestQuery (fun _ ht => ht) q hq
  rw [probEvent_bind_eq_tsum] at hb ⊢
  simpa only [treeSimHash_planted_rows_hit_eq] using hb

/-- Replacing a continuation only on an exceptional input costs that input's probability. -/
theorem treeSimHash_exception_bound {β γ : Type} (p : ProbComp β)
    (f g : β → ProbComp γ) (bad : β → Prop) (event : γ → Prop)
    (heq : ∀ b, ¬ bad b → f b = g b) :
    Pr[event | p >>= f] ≤ Pr[bad | p] + Pr[event | p >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite,
    ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro b
  by_cases hb : bad b
  · simp only [hb, ite_true]
    exact (mul_le_of_le_one_right zero_le probEvent_le_one).trans (le_self_add)
  · simp only [hb, ite_false, zero_add, heq b hb]
    exact le_rfl

/-- One hidden salted digest, with its previous guesses and its monitored continuation. -/
theorem treeSimHash_salted_hit_bound (prims : Primitives) (cache : HashCache C)
    (history : List Bit) (h : HashOutput) (hh : cache (.history history) = some h)
    (seen : Finset (List Bit))
    (hf : ∀ salt : Fin 256 → Bit, List.ofFn salt ∉ seen →
      cache (.digest (List.ofFn salt) h) = none)
    (k : HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ d, IsQueryBoundP (k d) DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      let r ← (saltedDigestAnswer prims (List.ofFn salt) history).run cache
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
        (r.2, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let actual := fun salt : Fin 256 → Bit => do
    let r ← (saltedDigestAnswer prims (List.ofFn salt) history).run cache
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
      (r.2, decide (List.ofFn salt ∈ seen))
  let planted := fun salt : Fin 256 → Bit => do
    let d ← $ᵗ HashOutput
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k d)).run
      (cache.cacheQuery (.digest (List.ofFn salt) h) d, false)
  have heq : ∀ salt, List.ofFn salt ∉ seen → actual salt = planted salt := by
    intro salt hs
    dsimp only [actual, planted]
    rw [saltedDigestAnswer_fresh prims cache (List.ofFn salt) history h hh (hf salt hs)]
    simp only [bind_map_left, hs, decide_false]
  have hb := treeSimHash_exception_bound ($ᵗ (Fin 256 → Bit)) actual planted
    (fun salt => List.ofFn salt ∈ seen) (fun r => r.2.2 = true) heq
  have hs := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
    List.ofFn_injective seen
  have hp : Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      ($ᵗ (Fin 256 → Bit)) >>= planted] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
    change Pr[_ | (do let salt ← $ᵗ (Fin 256 → Bit); let d ← $ᵗ HashOutput; _)] ≤ _
    rw [probEvent_bind_bind_swap ($ᵗ (Fin 256 → Bit)) ($ᵗ HashOutput)]
    apply probEvent_bind_le_of_forall_le
    intro d _
    exact treeSimHash_programmed_salt_bound prims cache (fun _ => h) (fun _ => d) (k d) q (hq d)
  refine hb.trans ((add_le_add hs hp).trans_eq ?_)
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add, ENNReal.add_div]

/-- The first-guess estimate also permits an uncached history. -/
theorem treeSimHash_salted_history_hit_bound (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (history : List Bit) (k : HashOutput → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ d, IsQueryBoundP (k d) DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      let r ← (saltedDigestAnswer prims (List.ofFn salt) history).run cache
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
        (r.2, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  simp only [saltedDigestAnswer, StateT.run_bind, bind_assoc]
  rw [probEvent_bind_bind_swap ($ᵗ (Fin 256 → Bit)) ((hashAnswer prims (.history history)).run cache)]
  apply probEvent_bind_le_of_forall_le
  intro r hr
  have hn : ¬ IsFixed (Query.history (C := C) history) := by rintro ⟨_, he, _⟩; cases he
  have hh := hashAnswer_cached prims hn cache r hr
  have hs := history_preserves_digestSalts prims cache seen hc history r hr
  have bound := treeSimHash_salted_hit_bound prims r.2 history r.1 hh seen
    (fun salt hnot => by
      by_contra hne
      exact hnot (hs (List.ofFn salt) r.1 hne)) k q hq
  simpa only [saltedDigestAnswer, StateT.run_bind, hashAnswer_run_cached prims hn hh,
    pure_bind] using bound

/-- First-guess bound for an actual honest digest column, including all holders and
the cache left by earlier columns. The monitor begins after the honest column. -/
theorem treeSimHash_digest_column_hit_bound (prims : Primitives) (D : C.Coalition)
    (T : C.Term) (cache : HashCache C) (seen : Finset (List Bit))
    (hc : DigestSaltsCovered cache seen)
    (salts : (Fin 256 → Bit) → C.Party → Shares C Bit)
    (histories : C.Party → C.Term → List Bit) (history : List Bit)
    (hs : ∀ salt i, i ∉ D.1 → i ∈ C.holders T →
      vector 256 (salts salt i T) = List.ofFn salt)
    (hh : ∀ i, i ∉ D.1 → i ∈ C.holders T → histories i T = history)
    (k : (C.Party → HashOutput) → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ row, IsQueryBoundP (k row) DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      let r ← (simulateQ (localAnswer prims)
        (Concrete.sequenceFin (honestDigestColumn D T (salts salt) histories))).run cache
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
        (r.2, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have he : ∀ salt : Fin 256 → Bit,
      Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
        let r ← (simulateQ (localAnswer prims)
          (Concrete.sequenceFin (honestDigestColumn D T (salts salt) histories))).run cache
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
          (r.2, decide (List.ofFn salt ∈ seen)))] =
      Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
        let r ← (saltedDigestAnswer prims (List.ofFn salt) history).run cache
        (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt)))
          (k (digestColumnValues D T r.1))).run (r.2, decide (List.ofFn salt ∈ seen)))] := by
    intro salt
    have hsame := honestDigestColumn_common D prims T (salts salt) histories
      (List.ofFn salt) history (hs salt) hh cache
    rw [probEvent_def, evalDist_bind, hsame]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      simulate_oneDigestQuery, evalDist_bind, evalDist_pure, pure_bind, digestColumnValues]
    simp only [bind_assoc, pure_bind]
    rw [probEvent_def, evalDist_bind]
    rfl
  have bound := treeSimHash_salted_history_hit_bound prims cache seen hc history
    (fun d => k (digestColumnValues D T d)) q (fun d => hq _)
  rw [probEvent_bind_eq_tsum] at bound ⊢
  simpa only [he] using bound

/-- Rows are stored newest first, with the same lookup convention as `List.lookup`. -/
def treeSimHashRowCache (cache : HashCache C) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) : HashCache C :=
  rows.foldr (fun row cache => cache.cacheQuery (.digest salt row.1) row.2) cache

theorem treeSimHashRowCache_plant (cache : HashCache C) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) :
    treeSimHashRowCache cache salt rows = treeSimHashPlantSalt cache salt rows.reverse := by
  simp [treeSimHashRowCache, treeSimHashPlantSalt, List.foldl_reverse]

theorem treeSimHashRowCache_digest (cache : HashCache C) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) (h : HashOutput) :
    treeSimHashRowCache cache salt rows (.digest salt h) =
      (rows.lookup h).orElse (fun _ => cache (.digest salt h)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨h', d⟩
    by_cases he : h = h'
    · subst h'
      simp [treeSimHashRowCache, List.lookup_cons]
    · simpa [treeSimHashRowCache, QueryCache.cacheQuery, List.lookup_cons, he,
        beq_eq_false_iff_ne.mpr he] using ih

/-- History queries commute with the complete planted slice, including duplicate rows. -/
theorem treeSimHashRowCache_history (prims : Primitives) (cache : HashCache C)
    (salt history : List Bit) (rows : List (HashOutput × HashOutput)) :
    (hashAnswer prims (.history history)).run (treeSimHashRowCache cache salt rows) =
      (fun r => (r.1, treeSimHashRowCache r.2 salt rows)) <$>
        (hashAnswer prims (.history history)).run cache := by
  induction rows with
  | nil => simp [treeSimHashRowCache]
  | cons row rows ih =>
    simp only [treeSimHashRowCache, List.foldr_cons]
    simp only [treeSimHashRowCache] at ih
    rw [hashAnswer_cacheQuery_other prims _ _ _ _ (by simp)]
    rw [ih]
    simp only [Functor.map_map, Function.comp_def]

theorem treeSimHashRowCache_local (prims : Primitives) (cache : HashCache C)
    (salt : List Bit) (rows : List (HashOutput × HashOutput))
    (t : (LocalSpec C).Domain) (ht : digestSaltHit salt t = false) :
    (localAnswer prims t).run (treeSimHashRowCache cache salt rows) =
      (fun r => (r.1, treeSimHashRowCache r.2 salt rows)) <$>
        (localAnswer prims t).run cache := by
  induction rows with
  | nil => simp [treeSimHashRowCache]
  | cons row rows ih =>
    have he : patchedDigestLocal prims salt row.1 row.2 t = localAnswer prims t := by
      rcases t with n | q | x
      · rfl
      · have hq : q ≠ .digest salt row.1 := by intro hq; subst q; simp [digestSaltHit] at ht
        simp [patchedDigestLocal, patchedDigestHash, localAnswer, hq]
      · rfl
    simp only [treeSimHashRowCache, List.foldr_cons]
    simp only [treeSimHashRowCache] at ih
    rw [localAnswer_digest_programmed, he, ih]
    simp only [Functor.map_map, Function.comp_def]

/-- Sample all rows of one hidden salt without referring to the salt itself.
Different holders may use different histories; repeated history hashes reuse a row. -/
def treeSimHashSaltRows (prims : Primitives) : List (List Bit) → HashCache C →
    List (HashOutput × HashOutput) →
    ProbComp (List HashOutput × HashCache C × List (HashOutput × HashOutput))
  | [], cache, rows => pure ([], cache, rows)
  | history :: histories, cache, rows => do
      let r ← (hashAnswer prims (.history history)).run cache
      let d ← match rows.lookup r.1 with
        | some d => pure d
        | none => $ᵗ HashOutput
      let next := if (rows.lookup r.1).isSome then rows else (r.1, d) :: rows
      let out ← treeSimHashSaltRows prims histories r.2 next
      pure (d :: out.1, out.2)

/-- Exact shared-cache normalization for all holders' rows of a fresh salt. -/
theorem treeSimHashSaltRows_run (prims : Primitives) (salt : List Bit)
    (histories : List (List Bit)) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (hs : salt ∉ seen)
    (rows : List (HashOutput × HashOutput)) :
    (histories.mapM (saltedDigestAnswer prims salt)).run (treeSimHashRowCache cache salt rows) =
      (fun r => (r.1, treeSimHashRowCache r.2.1 salt r.2.2)) <$>
        treeSimHashSaltRows prims histories cache rows := by
  induction histories generalizing cache rows with
  | nil => simp [treeSimHashSaltRows]
  | cons history histories ih =>
    simp only [List.mapM_cons, saltedDigestAnswer, StateT.run_bind, StateT.run_pure,
      treeSimHashSaltRows, map_bind, map_pure, bind_assoc]
    rw [treeSimHashRowCache_history, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro r hr
    have hc' := history_preserves_digestSalts prims cache seen hc history r hr
    have hf : r.2 (.digest salt r.1) = none := by
      by_contra hn
      exact hs (hc' salt r.1 hn)
    have hn : ¬ IsFixed (Query.digest (C := C) salt r.1) := by
      rintro ⟨_, he, _⟩; cases he
    cases hd : rows.lookup r.1 with
    | none =>
      have he : treeSimHashRowCache r.2 salt rows (.digest salt r.1) = none := by
        simp [treeSimHashRowCache_digest, hd, hf]
      rw [hashAnswer_of_not_isFixed prims hn, OracleSpec.randomOracle,
        QueryImpl.withCaching_run_none _ he]
      simp only [hd, bind_map_left, map_bind, map_pure, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte]
      apply bind_congr
      intro d
      change ((histories.mapM (saltedDigestAnswer prims salt)).run
        (treeSimHashRowCache r.2 salt ((r.1, d) :: rows)) >>= fun p => pure (d :: p.1, p.2)) = _
      rw [ih r.2 hc']
      simp only [bind_map_left]
    | some d =>
      have he : treeSimHashRowCache r.2 salt rows (.digest salt r.1) = some d := by
        simp [treeSimHashRowCache_digest, hd]
      rw [hashAnswer_run_cached prims hn he]
      simp only [hd, pure_bind, map_bind, map_pure, Option.isSome_some, ↓reduceIte]
      rw [ih r.2 hc']
      simp only [bind_map_left]

/-- A shared hidden salt can hash arbitrarily many different honest histories.
Only the earlier public salt set and later digest queries enter its first-hit bound. -/
theorem treeSimHash_salted_rows_hit_bound (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (histories : List (List Bit)) (k : List HashOutput → OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : ∀ ds, IsQueryBoundP (k ds) DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      let r ← (histories.mapM (saltedDigestAnswer prims (List.ofFn salt))).run cache
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
        (r.2, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let actual := fun salt : Fin 256 → Bit => do
    let r ← (histories.mapM (saltedDigestAnswer prims (List.ofFn salt))).run cache
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
      (r.2, decide (List.ofFn salt ∈ seen))
  let planted := fun salt : Fin 256 → Bit => do
    let r ← treeSimHashSaltRows prims histories cache []
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
      (treeSimHashRowCache r.2.1 (List.ofFn salt) r.2.2, false)
  have heq : ∀ salt, List.ofFn salt ∉ seen → actual salt = planted salt := by
    intro salt hs
    have he := treeSimHashSaltRows_run prims (List.ofFn salt) histories cache seen hc hs []
    simp only [treeSimHashRowCache, List.foldr_nil] at he
    dsimp only [actual, planted]
    rw [he]
    simp only [bind_map_left, hs, decide_false, treeSimHashRowCache]
  have hb := treeSimHash_exception_bound ($ᵗ (Fin 256 → Bit)) actual planted
    (fun salt => List.ofFn salt ∈ seen) (fun r => r.2.2 = true) heq
  have hs := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
    List.ofFn_injective seen
  have hp : Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      ($ᵗ (Fin 256 → Bit)) >>= planted] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
    dsimp only [planted]
    rw [probEvent_bind_bind_swap ($ᵗ (Fin 256 → Bit)) (treeSimHashSaltRows prims histories cache [])]
    apply probEvent_bind_le_of_forall_le
    intro r _
    simp only [treeSimHashRowCache_plant]
    exact treeSimHash_planted_rows_bound prims r.2.1 (fun _ => r.2.2.reverse) (k r.1) q (hq r.1)
  refine hb.trans ((add_le_add hs hp).trans_eq ?_)
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add, ENNReal.add_div]

/-- A private row oracle keeps its row table separate from the unchanged shared hash cache. -/
def treeSimHashSaltAnswer (prims : Primitives) :
    QueryImpl (List Bit →ₒ HashOutput)
      (StateT (HashCache C × List (HashOutput × HashOutput)) ProbComp) := fun history =>
  StateT.mk fun s => (fun r => (r.1.headD 0, r.2)) <$>
    treeSimHashSaltRows prims [history] s.1 s.2

theorem treeSimHashSaltAnswer_run (prims : Primitives) (salt history : List Bit)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (hs : salt ∉ seen) (rows : List (HashOutput × HashOutput)) :
    (saltedDigestAnswer prims salt history).run (treeSimHashRowCache cache salt rows) =
      (fun r => (r.1, treeSimHashRowCache r.2.1 salt r.2.2)) <$>
        (treeSimHashSaltAnswer prims history).run (cache, rows) := by
  have he := treeSimHashSaltRows_run prims salt [history] cache seen hc hs rows
  have hm := congrArg (fun p => (fun r : List HashOutput × HashCache C => (r.1.headD 0, r.2)) <$> p) he
  simpa only [List.mapM_cons, List.mapM_nil, StateT.run_bind, StateT.run_pure, pure_bind,
    map_bind, map_pure, List.headD_cons, treeSimHashSaltAnswer, StateT.run_mk,
    Functor.map_map, Function.comp_def, Prod.eta, bind_pure] using hm

theorem treeSimHashSaltAnswer_covered (prims : Primitives) (history : List Bit)
    (cache : HashCache C) (rows : List (HashOutput × HashOutput)) (seen : Finset (List Bit))
    (hc : DigestSaltsCovered cache seen) (r)
    (hr : r ∈ support ((treeSimHashSaltAnswer prims history).run (cache, rows))) :
    DigestSaltsCovered r.2.1 seen := by
  simp only [treeSimHashSaltAnswer, StateT.run_mk, treeSimHashSaltRows, map_bind,
    map_pure, pure_bind, List.headD_cons, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  have hcov := history_preserves_digestSalts prims cache seen hc history a ha
  cases hd : rows.lookup a.1 with
  | none =>
    simp only [hd, map_bind, map_pure, List.headD_cons, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨d, _, hr⟩ := hr
    subst r
    exact hcov
  | some d =>
    simp only [hd, map_pure, List.headD_cons, Option.isSome_some, ↓reduceIte,
      mem_support_pure_iff] at hr
    subst r
    exact hcov

/-- The private row normalization permits adaptive histories and arbitrary holder order. -/
theorem treeSimHashSaltProgram_run (prims : Primitives) (salt : List Bit)
    (p : OracleComp (List Bit →ₒ HashOutput) α) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (hs : salt ∉ seen)
    (rows : List (HashOutput × HashOutput)) :
    (simulateQ (saltedDigestAnswer prims salt) p).run (treeSimHashRowCache cache salt rows) =
      (fun r => (r.1, treeSimHashRowCache r.2.1 salt r.2.2)) <$>
        (simulateQ (treeSimHashSaltAnswer prims) p).run (cache, rows) := by
  induction p using OracleComp.inductionOn generalizing cache rows with
  | pure a => simp
  | query_bind history k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [treeSimHashSaltAnswer_run prims salt history cache seen hc hs rows, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro r hr
    exact ih r.1 r.2.1 (treeSimHashSaltAnswer_covered prims history cache rows seen hc r hr) r.2.2

theorem treeSimHash_bind_event_eq {β γ δ : Type} (p : ProbComp β)
    (f : β → ProbComp γ) (g : β → ProbComp δ) (P : γ → Prop) (Q : δ → Prop)
    (h : ∀ r ∈ support p, Pr[P | f r] = Pr[Q | g r]) :
    Pr[P | p >>= f] = Pr[Q | p >>= g] := by
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro r
  by_cases hr : r ∈ support p
  · rw [h r hr]
  · simp [probOutput_eq_zero_of_not_mem_support hr]

/-- Private salted digests may be interleaved with arbitrary public local queries. -/
abbrev TreeSimHashSaltSpec (C : Committee) := (List Bit →ₒ HashOutput) + LocalSpec C

def treeSimHashSaltProject : (TreeSimHashSaltSpec C).Domain → Option (List Bit)
  | .inl _ => none
  | .inr t => digestSaltProjection t

def treeSimHashSaltHit (salt : List Bit) : (TreeSimHashSaltSpec C).Domain → Bool
  | .inl _ => false
  | .inr t => digestSaltHit salt t

def treeSimHashSaltMixed (prims : Primitives) : QueryImpl (TreeSimHashSaltSpec C)
    (StateT (HashCache C × List (HashOutput × HashOutput)) ProbComp) :=
  treeSimHashSaltAnswer (C := C) prims +
    (show QueryImpl (LocalSpec C)
      (StateT (HashCache C × List (HashOutput × HashOutput)) ProbComp) from
      fun t => StateT.mk fun s =>
        (fun r => (r.1, r.2, s.2)) <$> (localAnswer prims t).run s.1)

theorem treeSimHash_local_covered_off_hit (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (salt : List Bit)
    (hs : salt ∉ seen) (t : (LocalSpec C).Domain) (ht : digestSaltHit salt t = false)
    (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) :
    ∃ seen', DigestSaltsCovered r.2 seen' ∧ salt ∉ seen' := by
  refine ⟨((digestSaltProjection t).toList ++ seen.toList).toFinset, ?_, ?_⟩
  · intro s h hh
    apply List.mem_toFinset.mpr
    exact localAnswer_digest_covered prims cache seen.toList
      (fun s h hh => Finset.mem_toList.mpr (hc s h hh)) t r hr s h hh
  · simp only [List.mem_toFinset, List.mem_append, Finset.mem_toList, hs, or_false]
    rw [digestSaltHit_projection] at ht
    simpa only [Option.mem_toList, decide_eq_false_iff_not] using ht

theorem treeSimHash_salt_interleaved_hit_eq (prims : Primitives) (salt : List Bit)
    (p : OracleComp (TreeSimHashSaltSpec C) α) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) (hs : salt ∉ seen)
    (rows : List (HashOutput × HashOutput)) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      (simulateQ (flagQueries ((show QueryImpl (List Bit →ₒ HashOutput)
          (StateT (HashCache C) ProbComp) from saltedDigestAnswer prims salt) + localAnswer (C := C) prims)
        (treeSimHashSaltHit salt)) p).run
        (treeSimHashRowCache cache salt rows, false)] =
    Pr[fun r : α × (HashCache C × List (HashOutput × HashOutput)) × Bool => r.2.2 = true |
      (simulateQ (flagQueries (treeSimHashSaltMixed prims)
        (treeSimHashSaltHit salt)) p).run
        ((cache, rows), false)] := by
  induction p using OracleComp.inductionOn generalizing cache seen rows with
  | pure a => simp
  | query_bind t k ih =>
    cases t with
    | inl history =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, flagQueries_run,
        treeSimHashSaltHit, Bool.false_or, bind_map_left]
      change Pr[_ | (saltedDigestAnswer prims salt history).run _ >>= _] =
        Pr[_ | (treeSimHashSaltAnswer prims history).run _ >>= _]
      simp only [OracleSpec.add_apply_inl, OracleSpec.ofFn] at *
      rw [treeSimHashSaltAnswer_run prims salt history cache seen hc hs rows, bind_map_left]
      apply treeSimHash_bind_event_eq
      intro r hr
      exact ih r.1 r.2.1 seen (treeSimHashSaltAnswer_covered prims history cache rows seen hc r hr) hs r.2.2
    | inr t =>
      by_cases ht : digestSaltHit salt t = true
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, flagQueries_run,
          treeSimHashSaltHit, bind_map_left, Bool.false_or]
        simp only [ht, treeSimHash_flag_true, probEvent_bind_eq_tsum, mul_one]
        simp
      · have ht : digestSaltHit salt t = false := Bool.eq_false_iff.mpr ht
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, flagQueries_run,
          treeSimHashSaltHit, bind_map_left, Bool.false_or]
        simp only [ht]
        change Pr[_ | (localAnswer prims t).run _ >>= _] =
          Pr[_ | ((fun r => (r.1, r.2, rows)) <$> (localAnswer prims t).run cache) >>= _]
        simp only [OracleSpec.add_apply_inr] at *
        rw [treeSimHashRowCache_local prims cache salt rows t ht]
        simp only [bind_map_left]
        apply treeSimHash_bind_event_eq
        intro r hr
        obtain ⟨seen', hc', hs'⟩ := treeSimHash_local_covered_off_hit prims cache seen hc salt hs t ht r hr
        exact ih r.1 r.2 seen' hc' hs' rows

theorem treeSimHash_event_exception_bound {β γ δ : Type} (p : ProbComp β)
    (f : β → ProbComp γ) (g : β → ProbComp δ) (bad : β → Prop)
    (P : γ → Prop) (Q : δ → Prop) (heq : ∀ b, ¬ bad b → Pr[P | f b] = Pr[Q | g b]) :
    Pr[P | p >>= f] ≤ Pr[bad | p] + Pr[Q | p >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite,
    ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro b
  by_cases hb : bad b
  · simp only [hb, ite_true]
    exact (mul_le_of_le_one_right zero_le probEvent_le_one).trans le_self_add
  · simp only [hb, ite_false, zero_add, heq b hb]
    exact le_rfl

/-- A single hidden salt stays uniform through adaptive interleaving. Private queries
are unlimited, and public queries share the original cache. -/
theorem treeSimHash_salt_interleaved_bound (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (p : OracleComp (TreeSimHashSaltSpec C) α) (q : ℕ)
    (hq : IsQueryBoundP p (fun t => (treeSimHashSaltProject t).isSome) q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries ((show QueryImpl (List Bit →ₒ HashOutput)
          (StateT (HashCache C) ProbComp) from saltedDigestAnswer prims (List.ofFn salt)) +
          localAnswer (C := C) prims) (treeSimHashSaltHit (List.ofFn salt))) p).run
        (cache, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let actual := fun salt : Fin 256 → Bit =>
    (simulateQ (flagQueries ((show QueryImpl (List Bit →ₒ HashOutput)
        (StateT (HashCache C) ProbComp) from saltedDigestAnswer prims (List.ofFn salt)) +
        localAnswer (C := C) prims) (treeSimHashSaltHit (List.ofFn salt))) p).run
      (cache, decide (List.ofFn salt ∈ seen))
  let abstract := fun salt : Fin 256 → Bit =>
    (simulateQ (flagQueries (treeSimHashSaltMixed prims) (treeSimHashSaltHit (List.ofFn salt))) p).run
      ((cache, []), false)
  have heq : ∀ salt, List.ofFn salt ∉ seen →
      Pr[fun r => r.2.2 = true | actual salt] = Pr[fun r => r.2.2 = true | abstract salt] := by
    intro salt hs
    simpa only [actual, abstract, hs, decide_false, treeSimHashRowCache, List.foldr_nil] using
      treeSimHash_salt_interleaved_hit_eq prims (List.ofFn salt) p cache seen hc hs []
  have hb := treeSimHash_event_exception_bound ($ᵗ (Fin 256 → Bit)) actual abstract
    (fun salt => List.ofFn salt ∈ seen) (fun r => r.2.2 = true) (fun r => r.2.2 = true) heq
  have hs := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
    List.ofFn_injective seen
  have hp : Pr[fun r => r.2.2 = true | ($ᵗ (Fin 256 → Bit)) >>= abstract] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
    have he : ∀ salt : List Bit, treeSimHashSaltHit (C := C) salt =
        fun t => decide (treeSimHashSaltProject t = some salt) := by
      intro salt
      funext t
      cases t with
      | inl history => simp [treeSimHashSaltHit, treeSimHashSaltProject]
      | inr t => exact congrFun (digestSaltHit_projection salt) t
    simp only [abstract, he]
    exact treeSimHash_projected_salt_bound (treeSimHashSaltMixed prims) treeSimHashSaltProject p
      (cache, []) (fun t => (treeSimHashSaltProject t).isSome) (fun _ h => h) q hq
  refine hb.trans ((add_le_add hs hp).trans_eq ?_)
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add, ENNReal.add_div]

abbrev TreeSimHashSaltTableSpec (κ : Type) (C : Committee) :=
  ((κ × List Bit) →ₒ HashOutput) + LocalSpec C

def treeSimHashSaltTableAnswer {κ : Type} (prims : Primitives) (table : κ → List Bit) :
    QueryImpl (TreeSimHashSaltTableSpec κ C) (StateT (HashCache C) ProbComp) :=
  (show QueryImpl ((κ × List Bit) →ₒ HashOutput) (StateT (HashCache C) ProbComp) from
    fun t => saltedDigestAnswer prims (table t.1) t.2) + localAnswer (C := C) prims

def treeSimHashSaltTableCharged {κ : Type} : (TreeSimHashSaltTableSpec κ C).Domain → Prop
  | .inl _ => True
  | .inr t => DigestQuery t

/-- Expose the other salt coordinates while keeping one coordinate opaque. -/
def treeSimHashSaltCoordinate {κ : Type} [DecidableEq κ] (i : κ) (table : κ → List Bit) :
    QueryImpl (TreeSimHashSaltTableSpec κ C) (OracleComp (TreeSimHashSaltSpec C))
  | .inl (j, history) => if j = i then
      OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inl history)
    else do
      let h ← OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inr (.inr (.inl (.history history))))
      OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inr (.inr (.inl (.digest (table j) h))))
  | .inr t => OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inr t)

def treeSimHashSaltCoordinateHit {κ : Type} [DecidableEq κ]
    (i : κ) (table : κ → List Bit) (salt : List Bit) : (TreeSimHashSaltTableSpec κ C).Domain → Bool
  | .inl (j, _) => if j = i then false else decide (table j = salt)
  | .inr t => digestSaltHit salt t

theorem treeSimHash_salt_coordinate_count {κ : Type} [DecidableEq κ]
    (i : κ) (table : κ → List Bit) (p : OracleComp (TreeSimHashSaltTableSpec κ C) α)
    (n : ℕ) (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    IsQueryBoundP (simulateQ (treeSimHashSaltCoordinate i table) p)
      (fun t => (treeSimHashSaltProject t).isSome) n := by
  letI : IsUniformSpec (TreeSimHashSaltSpec C) := IsUniformSpec.ofFintypeInhabited _
  apply hn.simulateQ_of_step
  · intro t ht
    rcases t with ⟨j, history⟩ | t
    · by_cases he : j = i
      · simp only [treeSimHashSaltCoordinate, he, ↓reduceIte]
        change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inl history))) _ 1
        rw [isQueryBoundP_query_iff]
        simp
      · simp only [treeSimHashSaltCoordinate, he, ↓reduceIte]
        rw [isQueryBoundP_query_bind_iff]
        constructor
        · exact Or.inl (by simp [treeSimHashSaltProject, digestSaltProjection])
        · intro h
          change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inr (.inr (.inl (.digest (table j) h)))))) _ 1
          rw [isQueryBoundP_query_iff]
          simp
    · change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inr t))) _ 1
      rw [isQueryBoundP_query_iff]
      simp
  · intro t ht
    cases t with
    | inl t => exact False.elim (ht trivial)
    | inr t =>
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltSpec C) (.inr t))) _ 0
      rw [isQueryBoundP_query_iff]
      simpa [treeSimHashSaltProject, treeSimHashSaltTableCharged, DigestQuery] using ht

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_salt_coordinate_step {κ : Type} [DecidableEq κ]
    (prims : Primitives) (i : κ) (table : κ → List Bit) (salt : List Bit)
    (t : (TreeSimHashSaltTableSpec κ C).Domain) (cache : HashCache C) (b : Bool) :
    (simulateQ (flagQueries ((show QueryImpl (List Bit →ₒ HashOutput)
        (StateT (HashCache C) ProbComp) from saltedDigestAnswer prims salt) + localAnswer (C := C) prims)
        (treeSimHashSaltHit salt)) (treeSimHashSaltCoordinate i table t)).run (cache, b) =
      (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        (treeSimHashSaltCoordinateHit i table salt) t).run (cache, b) := by
  rcases t with ⟨j, history⟩ | t
  · by_cases he : j = i
    · subst j
      simp only [treeSimHashSaltCoordinate, ↓reduceIte, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        flagQueries_run, treeSimHashSaltHit, treeSimHashSaltTableAnswer,
        treeSimHashSaltCoordinateHit, QueryImpl.add_apply_inl, Function.update_self,
        Bool.or_false]
      rfl
    · simp only [treeSimHashSaltCoordinate, he, ↓reduceIte, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind, flagQueries_run, bind_map_left,
        treeSimHashSaltHit, treeSimHashSaltCoordinateHit, treeSimHashSaltTableAnswer,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, Function.update_of_ne he]
      simp only [localAnswer, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        saltedDigestAnswer, digestSaltHit, StateT.run_bind, map_bind, Bool.or_false]
      simp only [OracleSpec.add_apply_inr, OracleSpec.add_apply_inl, OracleSpec.ofFn] at *
      apply bind_congr
      intro r
      rfl
  · simp only [treeSimHashSaltCoordinate, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, flagQueries_run,
      treeSimHashSaltHit, treeSimHashSaltTableAnswer, treeSimHashSaltCoordinateHit,
      QueryImpl.add_apply_inr]
    rfl

theorem treeSimHash_salt_coordinate_run {κ : Type} [DecidableEq κ]
    (prims : Primitives) (i : κ) (table : κ → List Bit) (salt : List Bit)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (cache : HashCache C) (b : Bool) :
    (simulateQ (flagQueries ((show QueryImpl (List Bit →ₒ HashOutput)
        (StateT (HashCache C) ProbComp) from saltedDigestAnswer prims salt) + localAnswer (C := C) prims)
        (treeSimHashSaltHit salt)) (simulateQ (treeSimHashSaltCoordinate i table) p)).run (cache, b) =
      (simulateQ (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        (treeSimHashSaltCoordinateHit i table salt)) p).run (cache, b) := by
  induction p using OracleComp.inductionOn generalizing cache b with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [treeSimHash_salt_coordinate_step]
    apply bind_congr
    intro r
    exact ih r.1 r.2.1 r.2.2

/-- Resampling one hidden coordinate bounds guesses throughout the entire program,
including equality with any other private salt used in that program. -/
theorem treeSimHash_salt_coordinate_bound {κ : Type} [DecidableEq κ]
    (prims : Primitives) (i : κ) (table : κ → List Bit) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      (simulateQ (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i (List.ofFn salt)))
        (treeSimHashSaltCoordinateHit i table (List.ofFn salt))) p).run
          (cache, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hb := treeSimHash_salt_interleaved_bound prims cache seen hc
    (simulateQ (treeSimHashSaltCoordinate i table) p) n
    (treeSimHash_salt_coordinate_count i table p n hn)
  simpa only [treeSimHash_salt_coordinate_run] using hb

def treeSimHashSaltTablePublic {κ : Type} : (TreeSimHashSaltTableSpec κ C).Domain → Option (List Bit)
  | .inl _ => none
  | .inr t => digestSaltProjection t

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_salt_coordinate_public {κ : Type} [DecidableEq κ]
    (prims : Primitives) (i : κ) (table : κ → List Bit) (salt : List Bit)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (cache : HashCache C) :
    Pr[fun r => salt ∈ r.2.2 |
      (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        treeSimHashSaltTablePublic) p).run (cache, [])] ≤
    Pr[fun r => r.2.2 = true |
      (simulateQ (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        (treeSimHashSaltCoordinateHit i table salt)) p).run (cache, false)] := by
  have he := projectQueries_flag (treeSimHashSaltTableAnswer prims (Function.update table i salt))
    treeSimHashSaltTablePublic salt p cache []
  simp only [List.not_mem_nil, decide_false] at he
  have hmono := treeSimHash_flag_mono (treeSimHashSaltTableAnswer prims (Function.update table i salt))
    (fun t => decide (treeSimHashSaltTablePublic t = some salt))
    (treeSimHashSaltCoordinateHit i table salt) (by
      intro t ht
      cases t with
      | inl t => simp [treeSimHashSaltTablePublic] at ht
      | inr t =>
        simp only [decide_eq_true_eq] at ht
        change digestSaltHit salt t = true
        rw [digestSaltHit_projection]
        simpa only [decide_eq_true_eq, treeSimHashSaltTablePublic] using ht) p cache false false (fun h => h)
  have he' : (simulateQ (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
      (fun t => decide (treeSimHashSaltTablePublic t = some salt))) p).run (cache, false) =
      (fun z : α × HashCache C × List (List Bit) => (z.1, z.2.1, decide (salt ∈ z.2.2))) <$>
      (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        treeSimHashSaltTablePublic) p).run (cache, []) := by
    convert he.symm using 1 <;> congr
    · funext t
      by_cases h : treeSimHashSaltTablePublic t = some salt <;> simp only [h, decide_true, decide_false]
    · funext z
      by_cases h : salt ∈ z.2.2 <;> simp only [h, decide_true, decide_false]
  rw [he', probEvent_map] at hmono
  simpa only [Function.comp_def, decide_eq_true_eq] using hmono

theorem treeSimHash_uniform_coordinate_event {κ R β : Type} [Finite κ] [DecidableEq κ]
    [Finite R] [Nonempty R] [SampleableType R] [SampleableType (κ → R)]
    (i : κ) (f : (κ → R) → ProbComp β) (P : β → Prop) :
    Pr[P | (do let table ← $ᵗ (κ → R); let value ← $ᵗ R; f (Function.update table i value))] =
      Pr[P | ($ᵗ (κ → R)) >>= f] := by
  rw [probEvent_bind_bind_swap]
  have he : 𝒟[((do
      let value ← $ᵗ R
      let table ← $ᵗ (κ → R)
      pure (Function.update table i value)) >>= f)] = 𝒟[($ᵗ (κ → R)) >>= f] := by
    rw [evalDist_bind, evalDist_uniformSample_bind_update, ← evalDist_bind]
  simpa only [bind_assoc, pure_bind] using (OracleComp.probEvent_congr' (p := P) (q := P) (fun _ _ => Iff.rfl) he)


theorem treeSimHash_salt_table_one_bound {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)] (prims : Primitives) (i : κ)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    Pr[fun z => List.ofFn (z.1 i) ∈ z.2.2.2 | (do
      let table ← $ᵗ (κ → Fin 256 → Bit)
      let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
        treeSimHashSaltTablePublic) p).run (∅, [])
      pure (table, r))] ≤ (n : ℝ≥0∞) / 2 ^ 256 := by
  let run := fun table : κ → Fin 256 → Bit => do
    let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
      treeSimHashSaltTablePublic) p).run (∅, [])
    pure (table, r)
  change Pr[fun z => List.ofFn (z.1 i) ∈ z.2.2.2 | ($ᵗ (κ → Fin 256 → Bit)) >>= run] ≤ _
  rw [← treeSimHash_uniform_coordinate_event i run]
  apply probEvent_bind_le_of_forall_le
  intro table _
  have he (salt : Fin 256 → Bit) :
      (fun j => List.ofFn (Function.update table i salt j)) =
        Function.update (fun j => List.ofFn (table j)) i (List.ofFn salt) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  have hb := treeSimHash_salt_coordinate_bound prims i (fun j => List.ofFn (table j))
    (∅ : HashCache C) ∅ (by intro salt h hh; simp at hh) p n hn
  simp only [Finset.card_empty, Nat.zero_add] at hb
  refine le_trans ?_ hb
  simp only [run, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Function.update_self, he]
  apply ENNReal.tsum_le_tsum
  intro salt
  apply mul_le_mul_left'
  simpa only [Finset.notMem_empty, decide_false] using
    treeSimHash_salt_coordinate_public prims i (fun j => List.ofFn (table j)) (List.ofFn salt) p ∅

/-- A single union over all opaque salt blocks, with arbitrary adaptive reuse,
interleaved public queries, and one shared hash cache. Salt collisions need no
separate assumption: queries to the other private blocks are charged by `n`. -/
theorem treeSimHash_salt_table_bound {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    Pr[fun z => ∃ i, List.ofFn (z.1 i) ∈ z.2.2.2 | (do
      let table ← $ᵗ (κ → Fin 256 → Bit)
      let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
        treeSimHashSaltTablePublic) p).run (∅, [])
      pure (table, r))] ≤ ((Fintype.card κ * n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let run := do
    let table ← $ᵗ (κ → Fin 256 → Bit)
    let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
      treeSimHashSaltTablePublic) p).run (∅, [])
    pure (table, r)
  have hb := probEvent_exists_finset_le_sum Finset.univ run
    (fun i z => List.ofFn (z.1 i) ∈ z.2.2.2)
  simp only [Finset.mem_univ, true_and] at hb
  refine hb.trans ((Finset.sum_le_sum (fun i _ =>
    treeSimHash_salt_table_one_bound prims i p n hn)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, mul_div_assoc]

/-- Addresses are allocated once, independently of the sampled salt table. -/
def treeSimHashSaltHandle (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (b : TreeSimHashSaltBlock C) : Fin (H + 1) :=
  ⟨min (seen.idxOf b) H, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

def treeSimHashSaltRemember (seen : List (TreeSimHashSaltBlock C))
    (b : TreeSimHashSaltBlock C) : List (TreeSimHashSaltBlock C) :=
  if b ∈ seen then seen else seen ++ [b]

theorem treeSimHash_salt_handle_fresh (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (b : TreeSimHashSaltBlock C) (hb : b ∉ seen) (hs : seen.length ≤ H) :
    (treeSimHashSaltHandle H seen b).val = seen.length := by
  simp only [treeSimHashSaltHandle, List.idxOf_eq_length hb, Nat.min_eq_left hs]

theorem treeSimHash_salt_handle_stable (H : ℕ) (seen more : List (TreeSimHashSaltBlock C))
    (b : TreeSimHashSaltBlock C) (hb : b ∈ seen) :
    treeSimHashSaltHandle H (seen ++ more) b = treeSimHashSaltHandle H seen b := by
  simp only [treeSimHashSaltHandle, List.idxOf_append_of_mem hb]

theorem treeSimHash_salt_handle_injective (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (hs : seen.length ≤ H) (a b : TreeSimHashSaltBlock C) (ha : a ∈ seen)
    (he : treeSimHashSaltHandle H seen a = treeSimHashSaltHandle H seen b) : a = b := by
  have hi := congrArg Fin.val he
  have hia : seen.idxOf a ≤ H := List.idxOf_le_length.trans hs
  have hib : seen.idxOf b ≤ H := List.idxOf_le_length.trans hs
  simp only [treeSimHashSaltHandle, Nat.min_eq_left hia, Nat.min_eq_left hib] at hi
  exact (List.idxOf_inj ha).mp hi

theorem treeSimHash_salt_remember_length (seen : List (TreeSimHashSaltBlock C))
    (b : TreeSimHashSaltBlock C) : (treeSimHashSaltRemember seen b).length ≤ seen.length + 1 := by
  unfold treeSimHashSaltRemember
  split_ifs <;> simp

/-- Compile an address-indexed private digest into the shared finite table.
The extra last coordinate is unreachable when at most `H` new blocks are used. -/
def treeSimHashSaltAllocate (H : ℕ) :
    QueryImpl (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C)
      (StateT (List (TreeSimHashSaltBlock C))
        (OracleComp (TreeSimHashSaltTableSpec (Fin (H + 1)) C)))
  | .inl (b, history) => StateT.mk fun seen =>
      (fun h => (h, treeSimHashSaltRemember seen b)) <$>
        (OracleSpec.query (spec := TreeSimHashSaltTableSpec (Fin (H + 1)) C)
          (.inl (treeSimHashSaltHandle H seen b, history)))
  | .inr t => StateT.lift
      (OracleSpec.query (spec := TreeSimHashSaltTableSpec (Fin (H + 1)) C) (.inr t))

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_salt_allocate_count (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (n : ℕ) (hn : IsQueryBoundP p treeSimHashSaltTableCharged n)
    (seen : List (TreeSimHashSaltBlock C)) :
    IsQueryBoundP ((simulateQ (treeSimHashSaltAllocate H) p).run seen)
      treeSimHashSaltTableCharged n := by
  letI : IsUniformSpec (TreeSimHashSaltTableSpec (Fin (H + 1)) C) :=
    IsUniformSpec.ofFintypeInhabited _
  apply hn.simulateQ_run_of_step
  · intro t ht s
    rcases t with ⟨b, history⟩ | t
    · simp [treeSimHashSaltAllocate, StateT.run_mk, isQueryBoundP_map_iff,
        isQueryBoundP_query_iff]
    · simpa [treeSimHashSaltAllocate, StateT.run_lift, isQueryBoundP_map_iff,
        isQueryBoundP_query_iff] using (Or.inr (by omega) : ¬ treeSimHashSaltTableCharged
          (κ := Fin (H + 1)) (C := C) (.inr t) ∨ 1 ≤ 1)
  · intro t ht s
    rcases t with ⟨b, history⟩ | t
    · exact False.elim (ht trivial)
    · simpa [treeSimHashSaltAllocate, StateT.run_lift, isQueryBoundP_map_iff,
        isQueryBoundP_query_iff, treeSimHashSaltTableCharged] using ht

/-- An adaptive address schedule inherits the table bound; allocation uses no
salt bits, and every repeated address keeps its first handle. -/
theorem treeSimHash_salt_address_bound (prims : Primitives) (H n : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    Pr[fun z => ∃ i, List.ofFn (z.1 i) ∈ z.2.2.2 | (do
      let table ← $ᵗ (Fin (H + 1) → Fin 256 → Bit)
      let r ← (simulateQ (projectQueries
        (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
        treeSimHashSaltTablePublic) ((simulateQ (treeSimHashSaltAllocate H) p).run [])).run (∅, [])
      pure (table, r))] ≤ (((H + 1) * n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  simpa only [Fintype.card_fin] using treeSimHash_salt_table_bound prims
    ((simulateQ (treeSimHashSaltAllocate H) p).run []) n
    (treeSimHash_salt_allocate_count H p n hn [])

def TreeSimHashSaltPrivate {κ : Type} : (TreeSimHashSaltTableSpec κ C).Domain → Prop
  | .inl _ => True
  | .inr _ => False

theorem treeSimHash_salt_remember_prefix (seen : List (TreeSimHashSaltBlock C))
    (b : TreeSimHashSaltBlock C) : seen <+: treeSimHashSaltRemember seen b := by
  unfold treeSimHashSaltRemember
  split_ifs
  · exact ⟨[], by simp⟩
  · exact List.prefix_append _ _

set_option backward.isDefEq.respectTransparency false in
/-- Capacity is charged to private calls alone, independent of the public query count. -/
theorem treeSimHash_salt_allocate_capacity (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (n : ℕ) (hn : IsQueryBoundP p TreeSimHashSaltPrivate n)
    (seen : List (TreeSimHashSaltBlock C)) (r : α × List (TreeSimHashSaltBlock C))
    (hr : r ∈ support ((simulateQ (treeSimHashSaltAllocate H) p).run seen)) :
    r.2.length ≤ seen.length + n ∧ seen <+: r.2 := by
  induction p using OracleComp.inductionOn generalizing n seen r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨Nat.le_add_right _ _, ⟨[], by simp⟩⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    rcases t with ⟨b, history⟩ | t
    · have hs : u.2 = treeSimHashSaltRemember seen b := by
        simp only [treeSimHashSaltAllocate, StateT.run_mk, support_map, Set.mem_image] at hu
        obtain ⟨v, _, rfl⟩ := hu
        rfl
      have hpos : 1 ≤ n := hn.1.resolve_left (fun h => h trivial)
      have hk : IsQueryBoundP (k u.1) TreeSimHashSaltPrivate (n - 1) := by
        simpa only [TreeSimHashSaltPrivate, if_true] using hn.2 u.1
      obtain ⟨hlen, hpref⟩ := ih u.1 (n - 1) hk u.2 r hr
      have hlen' := treeSimHash_salt_remember_length seen b
      refine ⟨by rw [hs] at hlen; omega, ?_⟩
      exact (treeSimHash_salt_remember_prefix seen b).trans (hs ▸ hpref)
    · have hs : u.2 = seen := by
        simp only [treeSimHashSaltAllocate, StateT.run_lift, bind_pure_comp,
          support_map, Set.mem_image] at hu
        obtain ⟨v, _, rfl⟩ := hu
        rfl
      have hk : IsQueryBoundP (k u.1) TreeSimHashSaltPrivate n := by
        simpa only [TreeSimHashSaltPrivate, if_false] using hn.2 u.1
      simpa only [hs] using ih u.1 n hk u.2 r hr

theorem treeSimHash_uniform_update_bind {κ V β : Type} [DecidableEq κ]
    [Finite κ] [Finite V] [Nonempty V] [SampleableType V] [SampleableType (κ → V)]
    (i : κ) (f : (κ → V) → ProbComp β) :
    𝒟[(do let v ← $ᵗ V; let table ← $ᵗ (κ → V); f (Function.update table i v))] =
      𝒟[(do let table ← $ᵗ (κ → V); f table)] := by
  have he := evalDist_uniformSample_bind_update (D := κ) (R := V) i
  have he' := congrArg (fun d => d >>= (fun table => 𝒟[f table])) he
  simpa only [evalDist_bind, bind_assoc, evalDist_pure, pure_bind] using he'

abbrev TreeSimHashBlockTableSpec (κ : Type) (S : OracleSpec ι) :=
  (κ →ₒ (Fin 256 → Bit)) + S

def treeSimHashBlockCacheAnswer {κ : Type} [DecidableEq κ]
    (impl : QueryImpl S (StateT σ ProbComp)) :
    QueryImpl (TreeSimHashBlockTableSpec κ S)
      (StateT (σ × (κ →ₒ (Fin 256 → Bit)).QueryCache) ProbComp)
  | .inl i => StateT.mk fun st =>
      (fun r => (r.1, st.1, r.2)) <$> ((κ →ₒ (Fin 256 → Bit)).randomOracle i).run st.2
  | .inr t => StateT.mk fun st =>
      (fun r => (r.1, r.2, st.2)) <$> (impl t).run st.1

def treeSimHashBlockTableAnswer {κ : Type} (table : κ → Fin 256 → Bit)
    (impl : QueryImpl S (StateT σ ProbComp)) : QueryImpl (TreeSimHashBlockTableSpec κ S)
      (StateT σ ProbComp)
  | .inl i => pure (table i)
  | .inr t => impl t

set_option backward.isDefEq.respectTransparency false in
/-- Deferred block sampling is valid with arbitrary public state and randomness. -/
theorem treeSimHash_block_eager {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)]
    (impl : QueryImpl S (StateT σ ProbComp))
    (p : OracleComp (TreeSimHashBlockTableSpec κ S) α)
    (s : σ) (cache : (κ →ₒ (Fin 256 → Bit)).QueryCache) :
    𝒟[(fun r => (r.1, r.2.1)) <$>
      ((simulateQ (treeSimHashBlockCacheAnswer impl) p).run (s, cache))] =
      𝒟[($ᵗ (κ → Fin 256 → Bit)) >>= fun table =>
        (simulateQ (treeSimHashBlockTableAnswer (tableExtending cache table) impl) p).run s] := by
  induction p using OracleComp.inductionOn generalizing s cache with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    apply evalDist_ext
    intro r
    simp only [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    cases t with
    | inl i =>
      simp only [treeSimHashBlockCacheAnswer, StateT.run_mk, bind_map_left,
        Function.comp_def, treeSimHashBlockTableAnswer, StateT.run_pure, pure_bind]
      cases hc : cache i with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hc]
        simp only [bind_map_left, Function.comp_def]
        let f : (κ → Fin 256 → Bit) → ProbComp (α × σ) := fun table =>
          (simulateQ (treeSimHashBlockTableAnswer (tableExtending cache table) impl)
            (k (tableExtending cache table i))).run s
        trans 𝒟[(do let v ← $ᵗ (Fin 256 → Bit)
                    let table ← $ᵗ (κ → Fin 256 → Bit)
                    f (Function.update table i v))]
        · apply evalDist_bind_congr'
          intro v
          rw [ih]
          apply evalDist_bind_congr'
          intro table
          simp only [f, ← tableExtending_update_of_none cache table hc v,
            ← tableExtending_cacheQuery, Function.update_self]
          simp only [tableExtending, hc, Function.update_self, Option.getD_none]
        · exact treeSimHash_uniform_update_bind i f
      | some v =>
        rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih]
        simp only [tableExtending, hc, Option.getD_some]
    | inr t =>
      simp only [treeSimHashBlockCacheAnswer, StateT.run_mk, bind_map_left,
        Function.comp_def, treeSimHashBlockTableAnswer]
      rw [evalDist_bind_bind_swap]
      apply evalDist_bind_congr'
      intro r
      exact ih r.1 r.2 cache

/-- Expand a private digest into a cached block read and its two real hash calls.
The list records the used salts without returning them to the calling program. -/
def treeSimHashSaltRead {κ : Type} : QueryImpl (TreeSimHashSaltTableSpec κ C)
    (StateT (List (List Bit) × List (List Bit))
      (OracleComp (TreeSimHashBlockTableSpec κ (LocalSpec C))))
  | .inl (i, history) => StateT.mk fun used => do
      let salt ← OracleSpec.query (spec := TreeSimHashBlockTableSpec κ (LocalSpec C)) (.inl i)
      let h ← OracleSpec.query (spec := TreeSimHashBlockTableSpec κ (LocalSpec C))
        (.inr (.inr (.inl (.history history))))
      let d ← OracleSpec.query (spec := TreeSimHashBlockTableSpec κ (LocalSpec C))
        (.inr (.inr (.inl (.digest (List.ofFn salt) h))))
      pure (d, used.1 ++ [List.ofFn salt], used.2)
  | .inr t => StateT.mk fun used =>
      (fun a => (a, used.1, (digestSaltProjection t).toList ++ used.2)) <$>
        (OracleSpec.query (spec := TreeSimHashBlockTableSpec κ (LocalSpec C)) (.inr t))

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_salt_read_step {κ : Type} (prims : Primitives)
    (table : κ → Fin 256 → Bit) (t : (TreeSimHashSaltTableSpec κ C).Domain)
    (used : List (List Bit) × List (List Bit)) (cache : HashCache C) :
    (simulateQ (treeSimHashBlockTableAnswer table (localAnswer prims))
      ((treeSimHashSaltRead t).run used)).run cache =
      (fun r => ((r.1, match t with
        | .inl (i, _) => used.1 ++ [List.ofFn (table i)]
        | .inr _ => used.1, r.2.2), r.2.1)) <$>
        (projectQueries (treeSimHashSaltTableAnswer prims (fun i => List.ofFn (table i)))
          treeSimHashSaltTablePublic t).run (cache, used.2) := by
  rcases t with ⟨i, history⟩ | t
  · simp only [treeSimHashSaltRead, StateT.run_mk, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, treeSimHashBlockTableAnswer, StateT.run_bind, StateT.run_pure, pure_bind,
      projectQueries_run, treeSimHashSaltTablePublic, Option.toList_none, List.nil_append,
      treeSimHashSaltTableAnswer, QueryImpl.add_apply_inl, saltedDigestAnswer, map_bind, map_pure,
      Functor.map_map, Function.comp_def]
    rfl
  · simp only [treeSimHashSaltRead, StateT.run_mk, projectQueries_run, treeSimHashSaltTablePublic,
      simulateQ_map, simulateQ_spec_query, treeSimHashBlockTableAnswer, StateT.run_map,
      treeSimHashSaltTableAnswer, QueryImpl.add_apply_inr, Functor.map_map, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/-- Erasing the salt-use list gives exactly the opaque-table computation. -/
theorem treeSimHash_salt_read_erase {κ : Type} (prims : Primitives)
    (table : κ → Fin 256 → Bit) (p : OracleComp (TreeSimHashSaltTableSpec κ C) α)
    (used : List (List Bit) × List (List Bit)) (cache : HashCache C) :
    (fun r => (r.1.1, r.2, r.1.2.2)) <$>
      (simulateQ (treeSimHashBlockTableAnswer table (localAnswer prims))
        ((simulateQ treeSimHashSaltRead p).run used)).run cache =
      (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun i => List.ofFn (table i)))
        treeSimHashSaltTablePublic) p).run (cache, used.2) := by
  induction p using OracleComp.inductionOn generalizing used cache with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [treeSimHash_salt_read_step]
    simp only [bind_map_left, Function.comp_def]
    apply bind_congr
    intro r
    exact ih r.1 _ r.2.1

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_salt_read_values {κ : Type} (prims : Primitives)
    (table : κ → Fin 256 → Bit) (p : OracleComp (TreeSimHashSaltTableSpec κ C) α)
    (used : List (List Bit) × List (List Bit)) (hu : ∀ salt ∈ used.1, ∃ i, salt = List.ofFn (table i))
    (cache : HashCache C) (r : (α × List (List Bit) × List (List Bit)) × HashCache C)
    (hr : r ∈ support ((simulateQ (treeSimHashBlockTableAnswer table (localAnswer prims))
      ((simulateQ treeSimHashSaltRead p).run used)).run cache)) :
    ∀ salt ∈ r.1.2.1, ∃ i, salt = List.ofFn (table i) := by
  induction p using OracleComp.inductionOn generalizing used cache r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hu
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, hr⟩ := hr
    rw [treeSimHash_salt_read_step, support_map, Set.mem_image] at ha
    obtain ⟨v, hv, rfl⟩ := ha
    apply ih v.1 _ _ v.2.1 r hr
    cases t with
    | inl t =>
      intro salt hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hu salt hs
      · have he : salt = List.ofFn (table t.1) := by simpa only [List.mem_singleton] using hs
        exact ⟨t.1, he⟩
    | inr t => exact hu

/-- The opaque bound applies to lazy cached block sampling, with the public
guess list and all used salts taken from the same execution. -/
theorem treeSimHash_lazy_salt_bound {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    Pr[fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2 |
      (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
        ((simulateQ treeSimHashSaltRead p).run ([], []))).run (∅, ∅)] ≤
      ((Fintype.card κ * n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have he := treeSimHash_block_eager (localAnswer prims)
    ((simulateQ treeSimHashSaltRead p).run ([], [])) (∅ : HashCache C) ∅
  have hp := OracleComp.probEvent_congr'
    (p := fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2)
    (q := fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2)
    (fun _ _ => Iff.rfl) he
  simp only [probEvent_map, Function.comp_def, tableExtending_empty] at hp
  rw [hp]
  apply le_trans _ (treeSimHash_salt_table_bound prims p n hn)
  simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul_left'
  rw [← treeSimHash_salt_read_erase prims table p ([], []) ∅, probEvent_map]
  apply probEvent_mono
  intro r hr hs
  obtain ⟨salt, hu, hg⟩ := hs
  obtain ⟨i, hi⟩ := treeSimHash_salt_read_values prims table p ([], [])
    (by intro salt h; cases h) ∅ r hr salt hu
  exact ⟨i, hi ▸ hg⟩

/-- The lazy address allocator fits the raw salt coefficient used by the
ceremony bound. Its public prefix uses the very same hash cache. -/
theorem treeSimHash_lazy_address_bound (prims : Primitives) (H n : ℕ) (hH : 0 < H)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n) :
    Pr[fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2 |
      (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
        ((simulateQ treeSimHashSaltRead
          ((simulateQ (treeSimHashSaltAllocate H) p).run [])).run ([], []))).run (∅, ∅)] ≤
      ((2 * H * n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hb := treeSimHash_lazy_salt_bound prims
    ((simulateQ (treeSimHashSaltAllocate H) p).run []) n
    (treeSimHash_salt_allocate_count H p n hn [])
  apply hb.trans
  simp only [Fintype.card_fin]
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_right n (show H + 1 ≤ 2 * H by omega)

/-- The handle may depend on the actual term key and label. Holders reading the
same PRSS address use the same handle; histories need not agree. -/
def treeSimHashSaltColumn {κ : Type} (D : C.Coalition) (T : C.Term)
    (handle : C.Party → κ) (histories : C.Party → C.Term → List Bit) :
    OracleComp (TreeSimHashSaltTableSpec κ C) (C.Party → HashOutput) :=
  Concrete.sequenceFin fun i => if i ∉ D.1 ∧ i ∈ C.holders T then
    OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltTableSpec κ C)
      (.inl (handle i, histories i T))) else pure 0

set_option backward.isDefEq.respectTransparency false in
/-- Exact normalization of the actual honest holder column into opaque handles,
retaining every cache update and every holder's returned digest. -/
theorem treeSimHash_salt_column_run {κ : Type} (prims : Primitives) (D : C.Coalition)
    (T : C.Term) (handle : C.Party → κ) (table : κ → List Bit)
    (salts : C.Party → Shares C Bit) (histories : C.Party → C.Term → List Bit)
    (hs : ∀ i, i ∉ D.1 → i ∈ C.holders T → vector 256 (salts i T) = table (handle i)) :
    simulateQ (localAnswer prims) (Concrete.sequenceFin (honestDigestColumn D T salts histories)) =
      simulateQ (treeSimHashSaltTableAnswer prims table) (treeSimHashSaltColumn D T handle histories) := by
  simp only [treeSimHashSaltColumn, simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
  · simp only [honestDigestColumn, if_pos hi, hs i hi.1 hi.2,
      simulate_oneDigestQuery, simulateQ_spec_query]
    rfl
  · simp only [honestDigestColumn, if_neg hi, simulateQ_pure]

/-- First-hit bound for an adaptive private row program, with a shared salt. -/
theorem treeSimHash_salt_program_hit_bound {β : Type} (prims : Primitives) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (p : OracleComp (List Bit →ₒ HashOutput) β) (k : β → OracleComp (LocalSpec C) α)
    (q : ℕ) (hq : ∀ ds, IsQueryBoundP (k ds) DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      let r ← (simulateQ (saltedDigestAnswer prims (List.ofFn salt)) p).run cache
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
        (r.2, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let actual := fun salt : Fin 256 → Bit => do
    let r ← (simulateQ (saltedDigestAnswer prims (List.ofFn salt)) p).run cache
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
      (r.2, decide (List.ofFn salt ∈ seen))
  let planted := fun salt : Fin 256 → Bit => do
    let r ← (simulateQ (treeSimHashSaltAnswer prims) p).run (cache, [])
    (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
      (treeSimHashRowCache r.2.1 (List.ofFn salt) r.2.2, false)
  have heq : ∀ salt, List.ofFn salt ∉ seen → actual salt = planted salt := by
    intro salt hs
    have he := treeSimHashSaltProgram_run prims (List.ofFn salt) p cache seen hc hs []
    simp only [treeSimHashRowCache, List.foldr_nil] at he
    dsimp only [actual, planted]
    rw [he]
    simp only [bind_map_left, hs, decide_false, treeSimHashRowCache]
  have hb := treeSimHash_exception_bound ($ᵗ (Fin 256 → Bit)) actual planted
    (fun salt => List.ofFn salt ∈ seen) (fun r => r.2.2 = true) heq
  have hs := probEvent_uniform_injective_mem (fun salt : Fin 256 → Bit => List.ofFn salt)
    List.ofFn_injective seen
  have hp : Pr[fun r : α × HashCache C × Bool => r.2.2 = true |
      ($ᵗ (Fin 256 → Bit)) >>= planted] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
    dsimp only [planted]
    rw [probEvent_bind_bind_swap ($ᵗ (Fin 256 → Bit)) ((simulateQ (treeSimHashSaltAnswer prims) p).run (cache, []))]
    apply probEvent_bind_le_of_forall_le
    intro r _
    simp only [treeSimHashRowCache_plant]
    exact treeSimHash_planted_rows_bound prims r.2.1 (fun _ => r.2.2.reverse) (k r.1) q (hq r.1)
  refine hb.trans ((add_le_add hs hp).trans_eq ?_)
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add, ENNReal.add_div]

/-- The actual honest column needs no history-agreement hypothesis for salt secrecy. -/
theorem treeSimHash_digest_column_rows_hit_bound (prims : Primitives) (D : C.Coalition)
    (T : C.Term) (cache : HashCache C) (seen : Finset (List Bit))
    (hc : DigestSaltsCovered cache seen)
    (salts : (Fin 256 → Bit) → C.Party → Shares C Bit)
    (histories : C.Party → C.Term → List Bit)
    (hs : ∀ salt i, i ∉ D.1 → i ∈ C.holders T → vector 256 (salts salt i T) = List.ofFn salt)
    (k : (C.Party → HashOutput) → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ ds, IsQueryBoundP (k ds) DigestQuery q) :
    Pr[fun r : α × HashCache C × Bool => r.2.2 = true | (do
      let salt ← $ᵗ (Fin 256 → Bit)
      let r ← (simulateQ (localAnswer prims)
        (Concrete.sequenceFin (honestDigestColumn D T (salts salt) histories))).run cache
      (simulateQ (flagQueries (localAnswer prims) (digestSaltHit (List.ofFn salt))) (k r.1)).run
        (r.2, decide (List.ofFn salt ∈ seen)))] ≤
      ((seen.card + q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let p : OracleComp (List Bit →ₒ HashOutput) (C.Party → HashOutput) :=
    Concrete.sequenceFin fun i => if i ∉ D.1 ∧ i ∈ C.holders T then
      OracleComp.lift (OracleSpec.query (spec := List Bit →ₒ HashOutput) (histories i T)) else pure 0
  have he : ∀ salt, simulateQ (localAnswer prims)
      (Concrete.sequenceFin (honestDigestColumn D T (salts salt) histories)) =
        simulateQ (saltedDigestAnswer prims (List.ofFn salt)) p := by
    intro salt
    simp only [p, simulateQ_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∉ D.1 ∧ i ∈ C.holders T
    · simp only [honestDigestColumn, if_pos hi, hs salt i hi.1 hi.2,
        simulate_oneDigestQuery, simulateQ_spec_query]
    · simp only [honestDigestColumn, if_neg hi, simulateQ_pure]
  simp_rw [he]
  exact treeSimHash_salt_program_hit_bound prims cache seen hc p k q hq

end SaltProbability

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

section DigestCount

variable {ι α β σ : Type} {G : OracleSpec ι}

/-- A list budget retains the individual cost of each entry. -/
theorem treeSimHash_mapM_bound {κ γ δ : Type} {S : OracleSpec κ}
    (P : κ → Prop) [DecidablePred P] (f : γ → OracleComp S δ) (cost : γ → ℕ)
    (xs : List γ) (hf : ∀ x ∈ xs, IsQueryBoundP (f x) P (cost x)) :
    IsQueryBoundP (xs.mapM f) P (xs.map cost).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons]
    have ht := ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))
    simpa using isQueryBoundP_bind (hf x (List.mem_cons_self ..)) (fun y _ =>
      isQueryBoundP_bind ht (fun ys _ => isQueryBoundP_pure P (y :: ys) 0))

def TreeSimHashDigestRunBound (p : StateT σ (PartyM C E G) α) (n : ℕ) : Prop :=
  ∀ s, DigestPartyBound (p.run s) n

theorem TreeSimHashDigestRunBound.pure (a : α) (n : ℕ) :
    TreeSimHashDigestRunBound (pure a : StateT σ (PartyM C E G) α) n :=
  fun _ => isQueryBoundP_pure _ _ _

theorem TreeSimHashDigestRunBound.bind {p : StateT σ (PartyM C E G) α}
    {f : α → StateT σ (PartyM C E G) β}
    {n m : ℕ} (hp : TreeSimHashDigestRunBound p n)
    (hf : ∀ a, TreeSimHashDigestRunBound (f a) m) :
    TreeSimHashDigestRunBound (p >>= f) (n + m) := by
  intro s
  exact DigestPartyBound.bind (hp s) (fun r => hf r.1 r.2)

theorem TreeSimHashDigestRunBound.mono {p : StateT σ (PartyM C E G) α} {n m : ℕ}
    (hp : TreeSimHashDigestRunBound p n) (hnm : n ≤ m) :
    TreeSimHashDigestRunBound p m := fun s => (hp s).mono hnm

theorem TreeSimHashDigestRunBound.bind_zero {p : StateT σ (PartyM C E G) α}
    {f : α → StateT σ (PartyM C E G) β} {m : ℕ}
    (hp : TreeSimHashDigestRunBound p 0)
    (hf : ∀ a, TreeSimHashDigestRunBound (f a) m) :
    TreeSimHashDigestRunBound (p >>= f) m := by
  simpa only [Nat.zero_add] using hp.bind hf

theorem TreeSimHashDigestRunBound.lift {p : PartyM C E G α} {n : ℕ}
    (hp : DigestPartyBound p n) :
    TreeSimHashDigestRunBound (StateT.lift p : StateT σ (PartyM C E G) α) n := by
  intro s
  exact (DigestPartyBound.bind hp (fun a => DigestPartyBound.pure (a, s)))

theorem TreeSimHashDigestRunBound.of_zero {p : RunM C E G α} (hp : RunBound p 0) :
    TreeSimHashDigestRunBound p 0 := fun s => (hp s).to_digest

theorem TreeSimHashDigestRunBound.foldlM {δ : Type} (f : α → δ → StateT σ (PartyM C E G) α)
    (n : ℕ) (hf : ∀ a x, TreeSimHashDigestRunBound (f a x) n)
    (xs : List δ) (a : α) :
    TreeSimHashDigestRunBound (xs.foldlM f a) (xs.length * n) := by
  induction xs generalizing a with
  | nil => exact .pure _ _
  | cons x xs ih =>
    simpa [List.foldlM_cons, Nat.succ_mul, Nat.add_comm] using (hf a x).bind (ih)

theorem treeSimHash_ro_digest {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => DigestQuery (C := C) (.inr t)) n) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) DigestQuery n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftComp_bind]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr t)) >>=
      fun u => liftComp (k u) (LocalSpec C)) DigestQuery n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

theorem treeSimHash_oracle_digest {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => DigestQuery (C := C) (.inr t)) n) :
    DigestPartyBound (oracleStep oa : PartyM C E G α) n :=
  localStep_digestBound (treeSimHash_ro_digest h)

theorem treeSimHash_prg_digest (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    IsQueryBoundP (prgBits name key label idx count)
      (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
    (fun position => (query (spec := RoSpec C) (.inr (name, key, label, idx, position)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun position _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, label, idx, position)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [DigestQuery, digestSaltProjection]

theorem treeSimHash_prss_digest {R : Type} [Zero R] (ctx : Context C)
    (codec : Codec C E R)
    (hd : ∀ name key label idx count, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => DigestQuery (C := C) (.inr t)) 0) (idx count : ℕ) :
    TreeSimHashDigestRunBound (prssRandomness ctx codec idx count : RunM C E G _) 0 := by
  unfold prssRandomness
  refine (TreeSimHashDigestRunBound.of_zero
    (RunBound.freshLabel (C := C) (E := E) (G := G))).bind (m := 0) (fun label => ?_)
  refine (TreeSimHashDigestRunBound.lift (treeSimHash_oracle_digest (n := 0) ?_)).bind
    (m := 0) (fun r => ?_)
  · simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => by
          split_ifs
          · exact hd _ _ _ _ _
          · exact isQueryBoundP_pure _ _ _)
  · refine (TreeSimHashDigestRunBound.lift (treeSimHash_oracle_digest (n := 0) ?_)).bind
      (m := 0) (fun Z => .pure _ 0)
    simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
      (fun j => if h : j = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label idx count)
      0 C.parties (fun j _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact hd _ _ _ _ _)

theorem treeSimHash_reshare_no_digest {R : Type} [Field R] (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    TreeSimHashDigestRunBound (reshare K ctx codec randomness v count : RunM C E G _) 0 := by
  apply TreeSimHashDigestRunBound.of_zero
  unfold reshare
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.record K ctx codec .peer _ count).bind (m := 0) (fun _ => RunBound.pure _))

structure TreeSimHashCheckDigestBounds (gadgets : CheckGadgets C E G) : Prop where
  coin : ∀ count, TreeSimHashDigestRunBound (gadgets.coin count) 0
  mult : ∀ products, TreeSimHashDigestRunBound (gadgets.extendMult products) 0
  elements : ∀ count, TreeSimHashDigestRunBound (gadgets.randElements count) 0
  bits : ∀ count, TreeSimHashDigestRunBound (gadgets.randBits count) 0

theorem treeSimHash_real_gadgets_digest (ctx : Context C) :
    TreeSimHashCheckDigestBounds (realCheckGadgets K ctx : CheckGadgets C E G) := by
  have hd : ∀ name key label idx count, IsQueryBoundP
      ((elementCodec K).draw name key label idx count)
      (fun t => DigestQuery (C := C) (.inr t)) 0 := by
    intro name key label idx count
    unfold elementCodec
    exact isQueryBoundP_bind (treeSimHash_prg_digest name key label idx _)
      (fun _ _ => isQueryBoundP_pure _ _ 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro count
    change TreeSimHashDigestRunBound
      (prssRandomness ctx (elementCodec K) 1 count >>= fun r => coinWith K ctx r count) 0
    refine (treeSimHash_prss_digest ctx (elementCodec K) hd 1 count).bind (m := 0) (fun r => ?_)
    unfold coinWith
    exact (TreeSimHashDigestRunBound.lift (RunBound.openSh K ctx _ count).to_digest).bind
      (m := 0) (fun _ => .pure _ 0)
  · intro products
    change TreeSimHashDigestRunBound
      (prssRandomness ctx (elementCodec K) 0 products.length >>= fun r =>
        reshare K ctx (elementCodec K) r _ products.length) 0
    exact (treeSimHash_prss_digest ctx (elementCodec K) hd 0 products.length).bind
      (m := 0) (fun r => treeSimHash_reshare_no_digest K ctx _ r _ _)
  · intro count
    exact treeSimHash_prss_digest ctx (elementCodec K) hd 1 count
  · intro count
    exact treeSimHash_prss_digest ctx bitCodec treeSimHash_prg_digest 2 count

def treeSimHashHeld (i : C.Party) : ℕ :=
  ∑ T : C.Term, if i ∈ C.holders T then 1 else 0

theorem treeSimHashHeld_total : ∑ i : C.Party, treeSimHashHeld i = C.t * termCount C := by
  unfold treeSimHashHeld
  rw [Finset.sum_comm]
  simp [keygen_card_holders, card_term, termCount, Nat.mul_comm]

theorem treeSimHash_hash_no_digest (q : Query C) (hq : ¬ DigestQuery (.inr (.inl q))) :
    IsQueryBoundP (hashQuery q) (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  exact fun h => (hq h).elim

theorem treeSimHash_digest_count (i : C.Party) (salts : Shares C Bit) (hist : C.Term → List Bit) :
    IsQueryBoundP (digestQuery i salts hist) (fun t => DigestQuery (C := C) (.inr t))
      (treeSimHashHeld i) := by
  unfold digestQuery
  rw [show treeSimHashHeld i =
    (C.terms.map fun T => if i ∈ C.holders T then 1 else 0).sum by
      simp [treeSimHashHeld, Committee.terms, Finset.sum_map_toList]]
  apply treeSimHash_mapM_bound
  intro T hT
  split_ifs with hi
  · refine isQueryBoundP_bind (n := 0) (m := 1)
      (treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])) (fun h _ => ?_)
    exact IsQueryBoundP.of_imp (fun _ _ => trivial) (hashQuery_queryBound _)
  · exact isQueryBoundP_pure _ _ _

theorem treeSimHash_compare_digest (ctx : Context C) (salts : Shares C Bit) :
    TreeSimHashDigestRunBound (compareDigests ctx salts : RunM C E G _) (treeSimHashHeld ctx.self) := by
  unfold compareDigests
  refine ((TreeSimHashDigestRunBound.of_zero
    (RunBound.get (C := C) (E := E) (G := G))).bind (fun s =>
    (TreeSimHashDigestRunBound.lift (treeSimHash_oracle_digest
      (treeSimHash_digest_count ctx.self salts s.history))).bind (fun ds =>
      (TreeSimHashDigestRunBound.lift (PartyBound.exchange _).to_digest).bind (fun inbox =>
        TreeSimHashDigestRunBound.lift (PartyBound.require _).to_digest)))).mono ?_
  omega

theorem treeSimHash_coinKey_digest (gadgets : CheckGadgets C E G)
    (hg : TreeSimHashCheckDigestBounds gadgets) :
    TreeSimHashDigestRunBound (coinKey K gadgets) 0 := by
  unfold coinKey
  refine ((TreeSimHashDigestRunBound.of_zero
    (RunBound.get (C := C) (E := E) (G := G))).bind (fun s =>
      (hg.coin 1).bind (fun values => TreeSimHashDigestRunBound.lift
        (treeSimHash_oracle_digest (treeSimHash_hash_no_digest _ ?_))))).mono (by omega)
  simp [DigestQuery, digestSaltProjection]

theorem treeSimHash_findChallenge_digest (key : HashOutput) (tries index : ℕ) :
    IsQueryBoundP (findChallenge K key tries index)
      (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  induction tries generalizing index with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ tries ih =>
    unfold findChallenge
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])) (fun h _ => ?_)
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

theorem treeSimHash_challenge_digest (gadgets : CheckGadgets C E G)
    (hg : TreeSimHashCheckDigestBounds gadgets) :
    TreeSimHashDigestRunBound (challenge K gadgets) 0 := by
  unfold challenge
  refine (treeSimHash_coinKey_digest K gadgets hg).bind (m := 0) (fun key => ?_)
  refine (TreeSimHashDigestRunBound.lift (treeSimHash_oracle_digest
    (treeSimHash_findChallenge_digest K key _ _))).bind (m := 0) (fun out => ?_)
  cases out with
  | none => exact .lift PartyBound.failure.to_digest
  | some r => exact .pure _ 0

theorem treeSimHash_expand_digest (key : HashOutput) (count : ℕ) :
    TreeSimHashDigestRunBound (expand K key count : RunM C E G _) 0 := by
  unfold expand
  apply TreeSimHashDigestRunBound.lift
  apply treeSimHash_oracle_digest
  simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
    (fun k => elementOfHash K <$> hashQuery (.expand key k)) 0 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr
      (treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])))

theorem treeSimHash_slice_digest (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : TreeSimHashCheckDigestBounds gadgets) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    TreeSimHashDigestRunBound (sliceStep K ctx gadgets τ count v j) 0 := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact (hg.mult _).bind (m := 0) (fun _ =>
    (treeSimHash_challenge_digest K gadgets hg).bind (m := 0) (fun _ => .pure _ 0))

theorem treeSimHash_halving_digest (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : TreeSimHashCheckDigestBounds gadgets) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    TreeSimHashDigestRunBound (halvingStep K ctx gadgets width v j) 0 := by
  rcases v with ⟨a, b, d⟩
  unfold halvingStep
  exact (hg.mult _).bind (m := 0) (fun _ =>
    (treeSimHash_challenge_digest K gadgets hg).bind (m := 0) (fun _ => .pure _ 0))

theorem treeSimHash_final_digest (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : TreeSimHashCheckDigestBounds gadgets) (v : (ℕ → E) × (ℕ → E) × E) :
    TreeSimHashDigestRunBound (finalStep K ctx gadgets v) (treeSimHashHeld ctx.self) := by
  rcases v with ⟨a, b, d⟩
  unfold finalStep
  refine ((hg.elements 2).bind (fun w =>
    (hg.mult _).bind (fun q =>
      (hg.bits 256).bind (fun salts =>
        (treeSimHash_compare_digest ctx salts.1).bind (fun _ =>
          (treeSimHash_challenge_digest K gadgets hg).bind (fun r =>
            (TreeSimHashDigestRunBound.lift (RunBound.openSh K ctx _ 3).to_digest).bind
              (fun opened => TreeSimHashDigestRunBound.lift (PartyBound.require _).to_digest))))))).mono ?_
  omega

/-- A complete real check, including all early-abort branches, asks one digest per held term. -/
theorem treeSimHash_check_digest (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : TreeSimHashCheckDigestBounds gadgets) (tuples : List (Tuple C)) :
    TreeSimHashDigestRunBound (check K ctx gadgets tuples) (treeSimHashHeld ctx.self) := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact .pure _ _
  · rw [check_eq K ctx gadgets tuples hz]
    refine ((treeSimHash_coinKey_digest K gadgets hg).bind (fun key =>
      (treeSimHash_expand_digest K key _).bind (fun τ =>
        (TreeSimHashDigestRunBound.lift (PartyBound.require _).to_digest).bind (fun _ =>
          (TreeSimHashDigestRunBound.foldlM _ 0 (treeSimHash_slice_digest K ctx gadgets hg τ _)
            _ _).bind (fun v =>
            (TreeSimHashDigestRunBound.foldlM _ 0 (treeSimHash_halving_digest K ctx gadgets hg _)
              _ _).bind (fun v' => treeSimHash_final_digest K ctx gadgets hg v')))))).mono ?_
    simp

theorem treeSimHash_collector_digest (ctx : Context C) (r : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    TreeSimHashDigestRunBound (reshareCollector K ctx r v count : RunM C E G _) 0 := by
  apply TreeSimHashDigestRunBound.of_zero
  unfold reshareCollector
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun forward =>
      (RunBound.record K ctx bitCodec .collector _ count).bind (m := 0) (fun _ => RunBound.pure _)))

theorem treeSimHash_reshareWith_digest (ctx : Context C) (mode : ReshareMode)
    (r : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    TreeSimHashDigestRunBound (reshareWith K ctx mode r v count : RunM C E G _) 0 := by
  cases mode with
  | peer => exact treeSimHash_reshare_no_digest K ctx _ r v count
  | collector => exact treeSimHash_collector_digest K ctx r v count

theorem treeSimHash_copy_pass_digest (xs : List C.Term) (f : C.Term → List Bit) :
    IsQueryBoundP (xs.mapM fun T => hashQuery (.copy (f T)))
      (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
    (fun T => hashQuery (.copy (f T))) 0 xs
    (fun _ _ => treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection]))

theorem treeSimHash_openRep_digest (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    DigestPartyBound (openRep K ctx v count : PartyM C E G _) 0 := by
  unfold openRep
  exact (treeSimHash_oracle_digest (treeSimHash_copy_pass_digest _ _)).bind (m := 0) (fun ds =>
    (PartyBound.exchange _).to_digest.bind (m := 0) (fun inbox =>
      (treeSimHash_oracle_digest (treeSimHash_copy_pass_digest _ _)).bind (m := 0) (fun copies =>
        (PartyBound.require _).to_digest.bind (m := 0) (fun _ => DigestPartyBound.pure _))))

/-- The complete real batch has precisely the digest budget of its one check. -/
theorem treeSimHash_runJobs_digest (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    TreeSimHashDigestRunBound
      (runJobs K (realRunGadgets K ctx mode : RunGadgets C E G) jobs inputs)
      (treeSimHashHeld ctx.self) := by
  have hm : ∀ x y count, TreeSimHashDigestRunBound
      ((realRunGadgets K ctx mode : RunGadgets C E G).mult x y count) 0 := by
    intro x y count
    change TreeSimHashDigestRunBound (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (treeSimHash_prss_digest ctx bitCodec treeSimHash_prg_digest 0 count).bind
      (m := 0) (fun r => treeSimHash_reshareWith_digest K ctx mode r _ count)
  have hr : ∀ v count, TreeSimHashDigestRunBound
      ((realRunGadgets K ctx mode : RunGadgets C E G).rerand v count) 0 := by
    intro v count
    change TreeSimHashDigestRunBound (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (treeSimHash_prss_digest ctx bitCodec treeSimHash_prg_digest 0 count).bind
      (m := 0) (fun r => treeSimHash_reshare_no_digest K ctx _ r _ count)
  unfold runJobs
  refine ((TreeSimHashDigestRunBound.foldlM _ 0 (fun v layer => ?_) _ _).bind (fun r =>
    (hr _ _).bind (fun v =>
      (treeSimHash_check_digest K ctx _ (treeSimHash_real_gadgets_digest K ctx) _).bind (fun _ =>
        (TreeSimHashDigestRunBound.lift (treeSimHash_openRep_digest K ctx v _)).bind
          (fun out => TreeSimHashDigestRunBound.pure _ 0))))).mono ?_
  · exact (hm _ _ _).bind (m := 0) (fun z => TreeSimHashDigestRunBound.pure _ 0)
  · simp

theorem TreeSimHashDigestRunBound.get :
    TreeSimHashDigestRunBound (get : StateT σ (PartyM C E G) σ) 0 :=
  fun _ => isQueryBoundP_pure _ _ _

theorem TreeSimHashDigestRunBound.set (s : σ) :
    TreeSimHashDigestRunBound (set s : StateT σ (PartyM C E G) Unit) 0 :=
  fun _ => isQueryBoundP_pure _ _ _

theorem TreeSimHashDigestRunBound.run' {p : StateT σ (PartyM C E G) α} {n : ℕ}
    (h : TreeSimHashDigestRunBound p n) (s : σ) : DigestPartyBound (p.run' s) n :=
  DigestPartyBound.bind (h s) (fun _ => DigestPartyBound.pure _)

theorem treeSimHash_party_mapM_digest {δ : Type} (f : δ → PartyM C E G α) (n : ℕ)
    (hf : ∀ x, DigestPartyBound (f x) n) (xs : List δ) :
    DigestPartyBound (xs.mapM f) (xs.length * n) := by
  induction xs with
  | nil => simpa using (DigestPartyBound.pure (C := C) (E := E) (G := G) ([] : List α))
  | cons x xs ih =>
    simpa [List.mapM_cons, Nat.succ_mul, Nat.add_comm] using
      (hf x).bind (fun y => ih.bind (fun ys => DigestPartyBound.pure (y :: ys)))

theorem TreeSimHashDigestRunBound.mapM {δ : Type} (f : δ → StateT σ (PartyM C E G) α)
    (n : ℕ) (hf : ∀ x, TreeSimHashDigestRunBound (f x) n) (xs : List δ) :
    TreeSimHashDigestRunBound (xs.mapM f) (xs.length * n) := by
  induction xs with
  | nil => exact .pure _ _
  | cons x xs ih =>
    simpa [List.mapM_cons, Nat.succ_mul, Nat.add_comm] using
      (hf x).bind (fun y => ih.bind (fun ys => TreeSimHashDigestRunBound.pure (y :: ys) 0))

theorem treeSimHash_tweakable_digest (oa : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable oa) (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [tweakable]
  | query_bind t k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query]
    exact isQueryBoundP_bind
      (treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])) (fun u _ => ih u)

theorem treeSimHash_inputShares_digest (ctx : Context C) (job : Job) :
    DigestPartyBound (inputShares ctx job : PartyM C E G _) 0 := by
  have hp (seed : HashOutput) (xs : List Point) :
      IsQueryBoundP (xs.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x)
        (fun t => DigestQuery (C := C) (.inr t)) 0 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMapM_cons]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_
        (fun ys _ => isQueryBoundP_bind ih (fun zs _ => isQueryBoundP_pure _ _ 0))
      simp only [prf, Functor.map_map, isQueryBoundP_map_iff]
      exact treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])
  unfold inputShares
  refine (treeSimHash_oracle_digest (n := 0) ?_).bind (m := 0) (fun terms => DigestPartyBound.pure _)
  simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
    (fun T => if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
      else pure []) 0 C.terms (fun T _ => by
        split_ifs
        · exact hp _ _
        · exact isQueryBoundP_pure _ _ _)

theorem treeSimHash_map_hash_digest {δ : Type} (xs : List δ) (f : δ → Query C)
    (hf : ∀ x, ¬ DigestQuery (.inr (.inl (f x)))) :
    IsQueryBoundP (xs.mapM fun x => hashQuery (f x))
      (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t))
    (fun x => hashQuery (f x)) 0 xs (fun x _ => treeSimHash_hash_no_digest _ (hf x))

theorem treeSimHash_derive_digest (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (fun t => DigestQuery (C := C) (.inr t)) 0 := by
  unfold deriveKeys
  dsimp only
  rw [← ite_bind]
  refine isQueryBoundP_bind (p := fun t => DigestQuery (C := C) (.inr t))
    (n := 0) (m := 0) ?_ (fun parameter _ => ?_)
  · split_ifs
    · exact treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])
    · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun terms _ => ?_)
    · simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t)) _ 0 C.terms
        (fun T _ => by
          split_ifs
          · exact treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])
          · exact isQueryBoundP_pure _ _ _)
    · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun pairs _ => isQueryBoundP_pure _ _ _)
      simpa using queryBound_mapM (fun t => DigestQuery (C := C) (.inr t)) _ 0 C.parties
        (fun j _ => by
          split_ifs
          · exact isQueryBoundP_pure _ _ _
          · exact treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection]))

theorem treeSimHash_setup_digest (i : C.Party) :
    DigestPartyBound (prssSetup i : PartyM C E G _) 0 := by
  have hm (f : C.Party → Query C) (hf : ∀ j, ¬ DigestQuery (.inr (.inl (f j)))) :
      DigestPartyBound (oracleStep (C.parties.mapM fun j => hashQuery (f j)) : PartyM C E G _) 0 :=
    treeSimHash_oracle_digest (treeSimHash_map_hash_digest _ f hf)
  unfold prssSetup
  refine (localStep_digestBound (IsQueryBoundP.of_imp split_digestQuery_region
    (split_prob_lift_no_digest (sampleParts (C := C))))).bind (m := 0) (fun own => ?_)
  unfold commitRevealEcho
  simp only [bind_assoc]
  refine (hm _ (by intro j; simp [DigestQuery, digestSaltProjection])).bind (m := 0) (fun commits => ?_)
  refine (PartyBound.exchange _).to_digest.bind (m := 0) (fun committed => ?_)
  refine (PartyBound.exchange _).to_digest.bind (m := 0) (fun revealed => ?_)
  refine (hm _ (by intro j; simp [DigestQuery, digestSaltProjection])).bind (m := 0) (fun opens => ?_)
  refine (PartyBound.require _).to_digest.bind (m := 0) (fun _ => ?_)
  refine (treeSimHash_oracle_digest (treeSimHash_derive_digest _ _ _)).bind (m := 0) (fun keys => ?_)
  refine (hm _ (by intro j; simp [DigestQuery, digestSaltProjection])).bind (m := 0) (fun shared => ?_)
  refine (PartyBound.exchange _).to_digest.bind (m := 0) (fun received => ?_)
  refine (PartyBound.require _).to_digest.bind (m := 0) (fun _ => ?_)
  exact (DigestPartyBound.pure _).bind (m := 0) (fun result => DigestPartyBound.pure _)

def treeSimHashBatch (ctx : Context C) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E G) (Option (List (List Bit))) := do
  let (label, k) ← get
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let (outputs, state) ← StateT.lift ((runJobs K (realRunGadgets K ctx settings.mode)
    (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩)
  set (state.label, k + 1)
  pure (some outputs)

theorem treeSimHash_batch_digest (ctx : Context C) (jobs : List Job) :
    TreeSimHashDigestRunBound (treeSimHashBatch (G := G) K circuits settings ctx jobs)
      (treeSimHashHeld ctx.self) := by
  have hi : DigestPartyBound (jobs.mapM (inputShares ctx) : PartyM C E G _) 0 := by
    simpa using treeSimHash_party_mapM_digest (inputShares ctx) 0
      (treeSimHash_inputShares_digest ctx) jobs
  unfold treeSimHashBatch
  refine ((TreeSimHashDigestRunBound.get (C := C) (E := E) (G := G) (σ := ℕ × ℕ)).bind
    (fun s => (TreeSimHashDigestRunBound.lift hi).bind (fun inputs =>
      (TreeSimHashDigestRunBound.lift
        (treeSimHash_runJobs_digest K ctx settings.mode _ inputs ⟨fun _ => [], s.1, s.2⟩)).bind
        (fun result => (TreeSimHashDigestRunBound.set _).bind
          (fun _ => TreeSimHashDigestRunBound.pure _ 0))))).mono ?_
  omega

theorem treeSimHash_batched_digest (ctx : Context C) (jobs : List Job) :
    TreeSimHashDigestRunBound
      (batched settings.batchSize (treeSimHashBatch (G := G) K circuits settings ctx) jobs)
      ((chunks settings.batchSize jobs).length * treeSimHashHeld ctx.self) := by
  unfold batched
  exact (TreeSimHashDigestRunBound.mapM _ _
    (treeSimHash_batch_digest K circuits settings ctx) _).bind
    (fun outputs => TreeSimHashDigestRunBound.pure _ 0)

theorem treeSimHash_ceremonyOutput_digest (i : C.Party)
    (lift : ∀ {δ : Type}, OracleComp HashSpec δ → StateT σ (PartyM C E G) δ)
    (hl : ∀ {δ : Type} (oa : OracleComp HashSpec δ), TreeSimHashDigestRunBound (lift oa) 0)
    (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hr : ∀ jobs, TreeSimHashDigestRunBound (run jobs)
      ((chunks settings.batchSize jobs).length * treeSimHashHeld i))
    (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    TreeSimHashDigestRunBound (ceremonyOutput lift parameter run top tree)
      (treeBatches settings tree * treeSimHashHeld i) := by
  cases tree with
  | top =>
    unfold ceremonyOutput treeBatches
    refine (hr topJobs).bind (m := 0) (fun outputs => ?_)
    cases outputs with
    | none => exact .pure _ 0
    | some outputs => exact (hl _).bind (m := 0) (fun root => .pure _ 0)
  | bottom b =>
    unfold ceremonyOutput treeBatches
    rw [Nat.add_mul]
    refine (hr (bottomJobs b)).bind (fun outputs => ?_)
    cases outputs with
    | none => exact .pure _ _
    | some outputs =>
      refine (hl _).bind_zero (fun root => (hl _).bind_zero (fun base => (hl _).bind_zero
        (fun found => ?_)))
      cases found with
      | none => exact .pure _ _
      | some result =>
        have h := hr (signJobs b result.2)
        rw [length_chunks_signJobs settings b b result.2 (fun _ => digit 0)] at h
        refine h.bind (m := 0) (fun values => ?_)
        cases values with
        | none => exact .pure _ 0
        | some values =>
          refine (hl _).bind (m := 0) (fun path => (hl _).bind (m := 0) (fun root => ?_))
          split_ifs <;> exact .pure _ 0

/-- A complete honest ceremony spends at most one held-term digest per batch. -/
theorem treeSimHash_ceremony_digest (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    DigestPartyBound (ceremony K circuits settings i keys top tree : PartyM C E G _)
      (treeBatches settings tree * treeSimHashHeld i) := by
  unfold ceremony ceremonyWith
  refine ((treeSimHash_setup_digest (E := E) (G := G) i).bind
    (m := treeBatches settings tree * treeSimHashHeld i) (fun prss => ?_)).mono ?_
  · let ctx : Context C := ⟨i, keys, prss⟩
    have hb := treeSimHash_ceremonyOutput_digest (G := G) (σ := ℕ × ℕ) settings i
      (fun {δ} (oa : OracleComp HashSpec δ) => StateT.lift (oracleStep (tweakable oa)))
      (fun oa => TreeSimHashDigestRunBound.lift
        (treeSimHash_oracle_digest (treeSimHash_tweakable_digest oa)))
      (batched settings.batchSize (treeSimHashBatch K circuits settings ctx))
      (treeSimHash_batched_digest K circuits settings ctx) keys.parameter top tree
    refine (hb.run' (0, 0)).bind (m := 0) (fun out => ?_)
    cases out with
    | none => exact PartyBound.failure.to_digest
    | some out => exact DigestPartyBound.pure _
  · omega

end DigestCount

namespace TreeSimHashCount

variable {ι α β σ : Type} {G : OracleSpec ι}
variable {P : (LocalSpec C).Domain → Prop}

def PartyQuery (P : (LocalSpec C).Domain → Prop) : (PartySpec C E G).Domain → Prop
  | .inl (.inl q) => P q
  | _ => False

def PartyBudget (P : (LocalSpec C).Domain → Prop) (p : PartyM C E G α) (n : ℕ) : Prop :=
  IsQueryBoundP p.run (PartyQuery P (E := E) (G := G)) n


theorem PartyBudget.of_counted {p : PartyM C E G α} {n : ℕ}
    (imp : ∀ t, P t → Counted t) (h : PartyBound p n) : PartyBudget P p n := by
  apply IsQueryBoundP.of_imp _ h
  rintro ((q | out) | input) ht
  · have hq := imp q ht
    rcases q with n | q
    · exact False.elim hq
    · trivial
  · exact False.elim ht
  · exact False.elim ht

theorem PartyBudget.mono {p : PartyM C E G α} {n m : ℕ}
    (h : PartyBudget P p n) (hn : n ≤ m) : PartyBudget P p m := IsQueryBoundP.mono h hn

lemma PartyBudget.pure (a : α) : PartyBudget P (pure a : PartyM C E G α) 0 :=
  isQueryBoundP_pure _ _ _

lemma PartyBudget.bind {p : PartyM C E G α} {f : α → PartyM C E G β} {n m : ℕ}
    (h : PartyBudget P p n) (hf : ∀ a,PartyBudget P (f a) m) : PartyBudget P (p >>= f) (n+m) := by
  unfold PartyBudget
  simp only [OptionT.run_bind]
  apply isQueryBoundP_bind h
  intro a _
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact hf a
lemma localStep_bound {oa : OracleComp (LocalSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa P n) : PartyBudget P (localStep oa : PartyM C E G α) n := by
  unfold PartyBudget localStep
  change IsQueryBoundP (some <$> liftComp oa (PartySpec C E G)) _ n
  rw [isQueryBoundP_map_iff]
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftComp_bind]
    have he : liftComp (OracleComp.lift (OracleSpec.query t)) (PartySpec C E G)=
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inl (.inl t))) := by
      rcases t with n | q | x <;> rfl
    rw [he]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1,fun u => ih u (h.2 u)⟩

def RunBudget (P : (LocalSpec C).Domain → Prop) (p : StateT σ (PartyM C E G) α) (n : ℕ) : Prop :=
  ∀ s, PartyBudget P (p.run s) n

theorem RunBudget.pure (a : α) (n : ℕ) :
    RunBudget P (pure a : StateT σ (PartyM C E G) α) n :=
  fun _ => isQueryBoundP_pure _ _ _

theorem RunBudget.bind {p : StateT σ (PartyM C E G) α}
    {f : α → StateT σ (PartyM C E G) β}
    {n m : ℕ} (hp : RunBudget P p n)
    (hf : ∀ a, RunBudget P (f a) m) :
    RunBudget P (p >>= f) (n + m) := by
  intro s
  exact PartyBudget.bind (hp s) (fun r => hf r.1 r.2)

theorem RunBudget.mono {p : StateT σ (PartyM C E G) α} {n m : ℕ}
    (hp : RunBudget P p n) (hnm : n ≤ m) :
    RunBudget P p m := fun s => (hp s).mono hnm

theorem RunBudget.bind_zero {p : StateT σ (PartyM C E G) α}
    {f : α → StateT σ (PartyM C E G) β} {m : ℕ}
    (hp : RunBudget P p 0)
    (hf : ∀ a, RunBudget P (f a) m) :
    RunBudget P (p >>= f) m := by
  simpa only [Nat.zero_add] using hp.bind hf

theorem RunBudget.lift {p : PartyM C E G α} {n : ℕ}
    (hp : PartyBudget P p n) :
    RunBudget P (StateT.lift p : StateT σ (PartyM C E G) α) n := by
  intro s
  exact (PartyBudget.bind hp (fun a => PartyBudget.pure (a, s)))

theorem RunBudget.foldlM {δ : Type} (f : α → δ → StateT σ (PartyM C E G) α)
    (n : ℕ) (hf : ∀ a x, RunBudget P (f a x) n)
    (xs : List δ) (a : α) :
    RunBudget P (xs.foldlM f a) (xs.length * n) := by
  induction xs generalizing a with
  | nil => exact .pure _ _
  | cons x xs ih =>
    simpa [List.foldlM_cons, Nat.succ_mul, Nat.add_comm] using (hf a x).bind (ih)

theorem RunBudget.bind_right_zero {p : StateT σ (PartyM C E G) α}
    {f : α → StateT σ (PartyM C E G) β} {n : ℕ}
    (hp : RunBudget P p n) (hf : ∀ a, RunBudget P (f a) 0) :
    RunBudget P (p >>= f) n := by
  simpa only [Nat.add_zero] using hp.bind hf

theorem RunBudget.of_counted {p : RunM C E G α} {n : ℕ}
    (imp : ∀ t, P t → Counted t) (h : RunBound p n) : RunBudget P p n :=
  fun s => PartyBudget.of_counted imp (h s)

theorem ro_bound {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => P (.inr t)) n) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) P n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [liftComp_bind]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr t)) >>=
      fun u => liftComp (k u) (LocalSpec C)) P n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

theorem oracle_bound {oa : OracleComp (RoSpec C) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t => P (.inr t)) n) :
    PartyBudget P (oracleStep oa : PartyM C E G α) n :=
  localStep_bound (ro_bound h)
theorem RunBudget.get :
    RunBudget P (get : StateT σ (PartyM C E G) σ) 0 :=
  fun _ => isQueryBoundP_pure _ _ _

theorem RunBudget.set (s : σ) :
    RunBudget P (set s : StateT σ (PartyM C E G) Unit) 0 :=
  fun _ => isQueryBoundP_pure _ _ _

theorem RunBudget.run' {p : StateT σ (PartyM C E G) α} {n : ℕ}
    (h : RunBudget P p n) (s : σ) : PartyBudget P (p.run' s) n :=
  PartyBudget.bind (h s) (fun _ => PartyBudget.pure _)

theorem party_mapM {δ : Type} (f : δ → PartyM C E G α) (n : ℕ)
    (hf : ∀ x, PartyBudget P (f x) n) (xs : List δ) :
    PartyBudget P (xs.mapM f) (xs.length * n) := by
  induction xs with
  | nil => simpa using (PartyBudget.pure (C := C) (E := E) (G := G) ([] : List α))
  | cons x xs ih =>
    simpa [List.mapM_cons, Nat.succ_mul, Nat.add_comm] using
      (hf x).bind (fun y => ih.bind (fun ys => PartyBudget.pure (y :: ys)))

theorem RunBudget.mapM {δ : Type} (f : δ → StateT σ (PartyM C E G) α)
    (n : ℕ) (hf : ∀ x, RunBudget P (f x) n) (xs : List δ) :
    RunBudget P (xs.mapM f) (xs.length * n) := by
  induction xs with
  | nil => exact .pure _ _
  | cons x xs ih =>
    simpa [List.mapM_cons, Nat.succ_mul, Nat.add_comm] using
      (hf x).bind (fun y => ih.bind (fun ys => RunBudget.pure (y :: ys) 0))

/-- The local budget remaining after the next round or hybrid call. -/
def StepBudget (P : (LocalSpec C).Domain → Prop) (st : Step C E G α) (n : ℕ) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyQuery P (E := E) (G := G)) n
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyQuery P (E := E) (G := G)) n

/-- Advancing a party spends only its local budget, leaving the residual budget for its continuation. -/
theorem advance_bind_regionBound (oa : OracleComp (PartySpec C E G) (Option α))
    (k : Step C E G α → OracleComp (LocalSpec C) β) (extra : ℕ) :
    ∀ n, IsQueryBoundP oa (PartyQuery P (E := E) (G := G)) n →
      (∀ st b, b ≤ n → StepBudget P st b → IsQueryBoundP (k st) P (extra + b)) →
      IsQueryBoundP (advance oa >>= k) P (extra + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ hk
    rw [advance_pure, pure_bind]
    exact hk (.done a) n le_rfl trivial
  | query_bind t f ih =>
    intro n h hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · rw [advance_query_bind, bind_assoc, isQueryBoundP_query_bind_iff]
      have hcp : P q → PartyQuery P (E := E) (G := G) (.inl (.inl q)) := by
        exact id
      constructor
      · by_cases hc : P q
        · right
          have hn := h.1.resolve_left (not_not.mpr (hcp hc))
          omega
        · exact Or.inl hc
      · intro u
        have hb : (if PartyQuery P (E := E) (G := G) (.inl (.inl q)) then n - 1 else n) ≤ n := by
          split_ifs <;> omega
        have hi := ih u _ (h.2 u) (fun st b hb' hs => hk st b (hb'.trans hb) hs)
        apply hi.mono
        by_cases hp : PartyQuery P (E := E) (G := G) (.inl (.inl q))
        · by_cases hc : P q
          · simp only [if_pos hp, if_pos hc]
            have hn := h.1.resolve_left (not_not.mpr hp)
            omega
          · simp only [if_pos hp, if_neg hc]
            omega
        · have hc : ¬ P q := fun hc => hp (hcp hc)
          simp only [if_neg hp, if_neg hc]
          exact le_rfl
    · change IsQueryBoundP (k (.wait outbox f)) P (extra + n)
      apply hk _ n le_rfl
      simpa [StepBudget, PartyQuery] using h.2
    · change IsQueryBoundP (k (.call input f)) P (extra + n)
      apply hk _ n le_rfl
      simpa [StepBudget, PartyQuery] using h.2

/-- Advance the parties sequentially while accounting for each residual budget. -/
theorem sequenceFin_advance_bind_regionBound : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E G) (Option α)) (budget : Fin N → ℕ)
    (h : ∀ i, IsQueryBoundP (oa i) (PartyQuery P (E := E) (G := G)) (budget i))
    (k : (Fin N → Step C E G α) → OracleComp (LocalSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) → (∀ i, StepBudget P (st i) (b i)) →
      IsQueryBoundP (k st) P (extra + ∑ i, b i)) →
    IsQueryBoundP ((Concrete.sequenceFin fun i => advance (oa i)) >>= k) P
      (extra + ∑ i, budget i)
  | 0, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    refine advance_bind_regionBound (oa 0) _ _ (budget 0) (h 0) (fun st0 b0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 =
        (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine sequenceFin_advance_bind_regionBound (fun i : Fin N => oa i.succ) (fun i => budget i.succ)
      (fun i => h i.succ) (fun st => k (Fin.cases st0 st)) (extra + b0) (fun st b hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases hs0 hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

section NetworkBound
variable {I O Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R)

lemma roundResume_regionBound (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBudget P (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (roundResume D sent steps j) (PartyQuery P (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k => exact isQueryBoundP_pure _ _ _
  | wait out k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [StepBudget, hs] at hj
      exact hj _

lemma callResume_regionBound (out : C.Party → Option O)
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBudget P (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (callResume D out steps j) (PartyQuery P (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold callResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [StepBudget, hs] at hj
      exact hj _
  | wait out k =>
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · exact Or.inl (by simp [PartyQuery])
    · simpa [StepBudget, hs, PartyQuery] using hj

lemma stepRound_bind_regionBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) P step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) P step)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBudget P (steps j) (budget j))
    (k : (A.State × (C.Party → Step C E (CallSpec I O) α) × (C.Party → C.Party → Option (Msg E))) →
      OracleComp (LocalSpec C) β) (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ), (∀ j, b j ≤ budget j) → (∀ j, StepBudget P (st.2.1 j) (b j)) →
      IsQueryBoundP (k st) P (extra + ∑ j, b j)) :
    IsQueryBoundP (stepRound localRoles D A F state steps >>= k) P (step + extra + ∑ j, budget j) := by
  unfold stepRound
  split_ifs
  · simp only [bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j) (hF _ _) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .call _ resume => if j ∈ D.1 then pure (Step.done none) else advance (resume (result.2 j))
        | st => pure st) = fun j => advance (callResume D result.2 steps j) := by
      funext j
      cases hs : steps j with
      | done out => simp only [callResume, hs]; rfl
      | wait out k => simp only [callResume, hs]; rfl
      | call input k => simp only [callResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_regionBound
      (fun j => callResume D result.2 steps j) budget (callResume_regionBound D result.2 steps budget h)
      (fun st => k (result.1, st, fun _ _ => none)) extra
      (fun st b hb hs => hk (result.1, st, fun _ _ => none) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, fun _ _ => none))
        P (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl
  · simp only [localRoles, bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j) (hr _ _) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .done out => pure (Step.done out)
        | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
            advance (resume fun k => if k ∈ D.1 then result.2 k j else (steps k).delivered j)
        | .call _ _ => pure (Step.done none)) = fun j => advance (roundResume D result.2 steps j) := by
      funext j
      cases hs : steps j with
      | done out => simp only [roundResume, hs]; rfl
      | call input k => simp only [roundResume, hs]; rfl
      | wait out k => simp only [roundResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_regionBound
      (fun j => roundResume D result.2 steps j) budget (roundResume_regionBound D result.2 steps budget h)
      (fun st => k (result.1, st, result.2)) extra
      (fun st b hb hs => hk (result.1, st, result.2) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (LocalSpec C) (Step C E (CallSpec I O) α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, result.2))
        P (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl

lemma executeRounds_regionBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) P step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) P step) :
    ∀ fuel state (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ),
      (∀ j, StepBudget P (steps j) (budget j)) →
      IsQueryBoundP (executeRounds localRoles D A F fuel state steps) P (fuel * step + ∑ j, budget j)
  | 0, state, steps, budget, h => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, budget, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine (stepRound_bind_regionBound D A F step hr hF state steps budget h _ (fuel * step) ?_).mono ?_
      · intro st b hb hs
        exact executeRounds_regionBound step hr hF fuel st.1 st.2.1 b hs
      · simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma executePhase_regionBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) P step)
    (hF : ∀ state inputs, IsQueryBoundP (runFunctionality localRoles D A F state inputs) P step)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α)
    (budget : C.Party → ℕ) (hp : ∀ j, j ∉ D.1 → PartyBudget P (program j) (budget j)) :
    IsQueryBoundP (executePhase localRoles D A F fuel state program) P (fuel * step + ∑ j, budget j) := by
  unfold executePhase startSteps
  simp only [localRoles]
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else advance (program i).run) =
      fun i => advance (if i ∈ D.1 then pure none else (program i).run) := by
    funext i
    split_ifs <;> rfl
  change IsQueryBoundP ((Concrete.sequenceFin _) >>= _) _ _
  rw [he]
  apply sequenceFin_advance_bind_regionBound _ budget
  · intro j
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
  · intro st b hb hs
    exact executeRounds_regionBound D A F step hr hF fuel state st b hs

end NetworkBound

abbrev Region : (LocalSpec C).Domain → Prop := SplitRegionCounted TreeSimHashBudgetDomain

theorem region_counted (t : (LocalSpec C).Domain) (h : Region t) : Counted t :=
  splitRegionCounted_counted _ t h

theorem PartyBudget.of_all {p : PartyM C E G α} {n : ℕ} (h : PartyBound p n) :
    PartyBudget Region p n := PartyBudget.of_counted region_counted h

theorem RunBudget.of_zero {p : RunM C E G α} (h : RunBound p 0) : RunBudget Region p 0 :=
  RunBudget.of_counted region_counted h

theorem prg_zero (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    IsQueryBoundP (prgBits name key label idx count)
      (fun t => Region (C := C) (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => Region (C := C) (.inr t))
    (fun position => (query (spec := RoSpec C) (.inr (name, key, label, idx, position)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun position _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, label, idx, position)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed]

theorem prss_zero {R : Type} [Zero R] (ctx : Context C)
    (codec : Codec C E R)
    (hd : ∀ name key label idx count, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => Region (C := C) (.inr t)) 0) (idx count : ℕ) :
    RunBudget Region (prssRandomness ctx codec idx count : RunM C E G _) 0 := by
  unfold prssRandomness
  refine (RunBudget.of_zero
    (RunBound.freshLabel (C := C) (E := E) (G := G))).bind (m := 0) (fun label => ?_)
  refine (RunBudget.lift (oracle_bound (n := 0) ?_)).bind
    (m := 0) (fun r => ?_)
  · simpa using queryBound_mapM (fun t => Region (C := C) (.inr t))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => by
          split_ifs
          · exact hd _ _ _ _ _
          · exact isQueryBoundP_pure _ _ _)
  · refine (RunBudget.lift (oracle_bound (n := 0) ?_)).bind
      (m := 0) (fun Z => .pure _ 0)
    simpa using queryBound_mapM (fun t => Region (C := C) (.inr t))
      (fun j => if h : j = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label idx count)
      0 C.parties (fun j _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact hd _ _ _ _ _)

theorem reshare_zero {R : Type} [Field R] (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    RunBudget Region (reshare K ctx codec randomness v count : RunM C E G _) 0 := by
  apply RunBudget.of_zero
  unfold reshare
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.record K ctx codec .peer _ count).bind (m := 0) (fun _ => RunBound.pure _))

structure GadgetBounds (gadgets : CheckGadgets C E G) : Prop where
  coin : ∀ count, RunBudget Region (gadgets.coin count) 0
  mult : ∀ products, RunBudget Region (gadgets.extendMult products) 0
  elements : ∀ count, RunBudget Region (gadgets.randElements count) 0
  bits : ∀ count, RunBudget Region (gadgets.randBits count) 0

theorem gadgets_zero (ctx : Context C) :
    GadgetBounds (realCheckGadgets K ctx : CheckGadgets C E G) := by
  have hd : ∀ name key label idx count, IsQueryBoundP
      ((elementCodec K).draw name key label idx count)
      (fun t => Region (C := C) (.inr t)) 0 := by
    intro name key label idx count
    unfold elementCodec
    exact isQueryBoundP_bind (prg_zero name key label idx _)
      (fun _ _ => isQueryBoundP_pure _ _ 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro count
    change RunBudget Region
      (prssRandomness ctx (elementCodec K) 1 count >>= fun r => coinWith K ctx r count) 0
    refine (prss_zero ctx (elementCodec K) hd 1 count).bind (m := 0) (fun r => ?_)
    unfold coinWith
    exact (RunBudget.lift (PartyBudget.of_all (RunBound.openSh K ctx _ count))).bind
      (m := 0) (fun _ => .pure _ 0)
  · intro products
    change RunBudget Region
      (prssRandomness ctx (elementCodec K) 0 products.length >>= fun r =>
        reshare K ctx (elementCodec K) r _ products.length) 0
    exact (prss_zero ctx (elementCodec K) hd 0 products.length).bind
      (m := 0) (fun r => reshare_zero K ctx _ r _ _)
  · intro count
    exact prss_zero ctx (elementCodec K) hd 1 count
  · intro count
    exact prss_zero ctx bitCodec prg_zero 2 count

theorem hash_zero (q : Query C) (hq : ¬ Region (.inr (.inl q))) :
    IsQueryBoundP (hashQuery q) (fun t => Region (C := C) (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  exact fun h => (hq h).elim

theorem findChallenge_zero (key : HashOutput) (tries index : ℕ) :
    IsQueryBoundP (findChallenge K key tries index)
      (fun t => Region (C := C) (.inr t)) 0 := by
  induction tries generalizing index with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ tries ih =>
    unfold findChallenge
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed])) (fun h _ => ?_)
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

theorem expand_zero (key : HashOutput) (count : ℕ) :
    RunBudget Region (expand K key count : RunM C E G _) 0 := by
  unfold expand
  apply RunBudget.lift
  apply oracle_bound
  simpa using queryBound_mapM (fun t => Region (C := C) (.inr t))
    (fun k => elementOfHash K <$> hashQuery (.expand key k)) 0 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr
      (hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed])))

theorem collector_zero (ctx : Context C) (r : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    RunBudget Region (reshareCollector K ctx r v count : RunM C E G _) 0 := by
  apply RunBudget.of_zero
  unfold reshareCollector
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun forward =>
      (RunBound.record K ctx bitCodec .collector _ count).bind (m := 0) (fun _ => RunBound.pure _)))

theorem reshareWith_zero (ctx : Context C) (mode : ReshareMode)
    (r : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunBudget Region (reshareWith K ctx mode r v count : RunM C E G _) 0 := by
  cases mode with
  | peer => exact reshare_zero K ctx _ r v count
  | collector => exact collector_zero K ctx r v count

theorem tweakable_zero (oa : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable oa) (fun t => Region (C := C) (.inr t)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [tweakable]
  | query_bind t k ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query]
    exact isQueryBoundP_bind
      (hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed])) (fun u _ => ih u)

theorem inputShares_zero (ctx : Context C) (job : Job) :
    PartyBudget Region (inputShares ctx job : PartyM C E G _) 0 := by
  have hp (seed : HashOutput) (xs : List Point) :
      IsQueryBoundP (xs.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x)
        (fun t => Region (C := C) (.inr t)) 0 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMapM_cons]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_
        (fun ys _ => isQueryBoundP_bind ih (fun zs _ => isQueryBoundP_pure _ _ 0))
      simp only [prf, Functor.map_map, isQueryBoundP_map_iff]
      exact hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed])
  unfold inputShares
  refine (oracle_bound (n := 0) ?_).bind (m := 0) (fun terms => PartyBudget.pure _)
  simpa using queryBound_mapM (fun t => Region (C := C) (.inr t))
    (fun T => if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
      else pure []) 0 C.terms (fun T _ => by
        split_ifs
        · exact hp _ _
        · exact isQueryBoundP_pure _ _ _)

theorem map_hash_zero {δ : Type} (xs : List δ) (f : δ → Query C)
    (hf : ∀ x, ¬ Region (.inr (.inl (f x)))) :
    IsQueryBoundP (xs.mapM fun x => hashQuery (f x))
      (fun t => Region (C := C) (.inr t)) 0 := by
  simpa using queryBound_mapM (fun t => Region (C := C) (.inr t))
    (fun x => hashQuery (f x)) 0 xs (fun x _ => hash_zero _ (hf x))

theorem derive_zero (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (fun t => Region (C := C) (.inr t)) 0 := by
  unfold deriveKeys
  dsimp only
  rw [← ite_bind]
  refine isQueryBoundP_bind (p := fun t => Region (.inr t))
    (n := 0) (m := 0) ?_ (fun parameter _ => ?_)
  · split_ifs
    · exact hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed])
    · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun terms _ => ?_)
    · simpa using queryBound_mapM (fun t => Region (C := C) (.inr t)) _ 0 C.terms
        (fun T _ => by
          split_ifs
          · exact hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed])
          · exact isQueryBoundP_pure _ _ _)
    · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun pairs _ => isQueryBoundP_pure _ _ _)
      simpa using queryBound_mapM (fun t => Region (C := C) (.inr t)) _ 0 C.parties
        (fun j _ => by
          split_ifs
          · exact isQueryBoundP_pure _ _ _
          · exact hash_zero _ (by simp [Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain, IsFixed]))



theorem hash_one (q : Query C) :
    IsQueryBoundP (hashQuery q) (fun t => Region (C := C) (.inr t)) 1 :=
  IsQueryBoundP.of_imp (fun _ _ => trivial) (hashQuery_queryBound q)

theorem compare_bound (ctx : Context C) (salts : Shares C Bit) :
    RunBudget Region (compareDigests ctx salts : RunM C E G _) (2 * termCount C) := by
  unfold compareDigests
  refine ((RunBudget.of_zero
    (RunBound.get (C := C) (E := E) (G := G))).bind (fun s =>
    (RunBudget.lift (PartyBudget.of_all (oracleStep_queryBound
      (digestQuery_queryBound ctx.self salts s.history)))).bind (fun ds =>
      (RunBudget.lift (PartyBudget.of_all (PartyBound.exchange _))).bind (fun inbox =>
        RunBudget.lift (PartyBudget.of_all (PartyBound.require _)))))).mono ?_
  simp [Committee.terms, card_term, termCount]

theorem coinKey_bound (gadgets : CheckGadgets C E G) (hg : GadgetBounds gadgets) :
    RunBudget Region (coinKey K gadgets) 1 := by
  unfold coinKey
  exact (RunBudget.of_zero (RunBound.get (C := C) (E := E) (G := G))).bind_zero
    (fun s => (hg.coin 1).bind_zero (fun values => RunBudget.lift (oracle_bound (hash_one _))))

theorem challenge_bound (gadgets : CheckGadgets C E G) (hg : GadgetBounds gadgets) :
    RunBudget Region (challenge K gadgets) 1 := by
  unfold challenge
  refine (coinKey_bound K gadgets hg).bind (m := 0) (fun key => ?_)
  refine (RunBudget.lift (oracle_bound (findChallenge_zero K key _ _))).bind (m := 0) (fun out => ?_)
  cases out with
  | none => exact .lift (PartyBudget.of_all PartyBound.failure)
  | some r => exact .pure _ 0

theorem slice_bound (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    RunBudget Region (sliceStep K ctx gadgets τ count v j) 1 := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact (hg.mult _).bind_zero (fun _ =>
    (challenge_bound K gadgets hg).bind (m := 0) (fun _ => .pure _ 0))

theorem halving_bound (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunBudget Region (halvingStep K ctx gadgets width v j) 1 := by
  rcases v with ⟨a, b, d⟩
  unfold halvingStep
  exact (hg.mult _).bind_zero (fun _ =>
    (challenge_bound K gadgets hg).bind (m := 0) (fun _ => .pure _ 0))

theorem final_bound (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (v : (ℕ → E) × (ℕ → E) × E) :
    RunBudget Region (finalStep K ctx gadgets v) (2 * termCount C + 1) := by
  rcases v with ⟨a, b, d⟩
  unfold finalStep
  refine ((hg.elements 2).bind (fun w =>
    (hg.mult _).bind (fun q =>
      (hg.bits 256).bind (fun salts =>
        (compare_bound ctx salts.1).bind (fun _ =>
          (challenge_bound K gadgets hg).bind (fun r =>
            (RunBudget.lift (PartyBudget.of_all (RunBound.openSh K ctx _ 3))).bind
              (fun opened => RunBudget.lift (PartyBudget.of_all (PartyBound.require _))))))))).mono ?_
  omega

theorem check_bound (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (tuples : List (Tuple C)) :
    RunBudget Region (check K ctx gadgets tuples)
      (2 * termCount C + halvings (tuples.map (·.count)).sum + 2) := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact .pure _ _
  · rw [check_eq K ctx gadgets tuples hz]
    refine ((coinKey_bound K gadgets hg).bind (fun key =>
      (expand_zero K key _).bind (fun τ =>
        (RunBudget.lift (PartyBudget.of_all (PartyBound.require _))).bind (fun _ =>
          (RunBudget.foldlM _ 1 (slice_bound K ctx gadgets hg τ _) _ _).bind (fun v =>
            (RunBudget.foldlM _ 1 (halving_bound K ctx gadgets hg _) _ _).bind
              (fun v' => final_bound K ctx gadgets hg v')))))).mono ?_
    simp only [List.length_range, Nat.mul_one]
    have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by unfold halvings; omega
    omega

theorem copy_pass (xs : List C.Term) (f : C.Term → List Bit) :
    IsQueryBoundP (xs.mapM fun T => hashQuery (.copy (f T)))
      (fun t => Region (C := C) (.inr t)) xs.length := by
  simpa using queryBound_mapM (fun t => Region (C := C) (.inr t))
    (fun T => hashQuery (.copy (f T))) 1 xs (fun _ _ => hash_one _)

theorem openRep_bound (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    PartyBudget Region (openRep K ctx v count : PartyM C E G _) (2 * termCount C) := by
  unfold openRep
  refine ((oracle_bound (copy_pass _ _)).bind (fun ds =>
    (PartyBudget.of_all (PartyBound.exchange _)).bind (fun inbox =>
      (oracle_bound (copy_pass _ _)).bind (fun copies =>
        (PartyBudget.of_all (PartyBound.require _)).bind (fun _ => PartyBudget.pure _))))).mono ?_
  simp [Committee.terms, card_term, termCount, two_mul]

lemma prob_zero (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) (SplitRegionCounted TreeSimHashBudgetDomain) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind,liftComp_query]
    simp only [OracleQuery.input_query,OracleQuery.cont_query,id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) (SplitRegionCounted TreeSimHashBudgetDomain) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [SplitRegionCounted,splitLocalHashInput, SplitRegionCounted, TreeSimHashBudgetDomain, IsFixed]),fun u => by
      simpa [SplitRegionCounted,splitLocalHashInput, SplitRegionCounted, TreeSimHashBudgetDomain, IsFixed] using ih u⟩



theorem setup_bound (i : C.Party) :
    PartyBudget Region (prssSetup i : PartyM C E G _) (3 * C.n) := by
  have hm (f : C.Party → Query C) :
      PartyBudget Region (oracleStep (C.parties.mapM fun j => hashQuery (f j)) : PartyM C E G _) C.n := by
    apply oracle_bound
    simpa [Committee.parties] using queryBound_mapM (fun t => Region (C := C) (.inr t))
      (fun j => hashQuery (f j)) 1 C.parties (fun _ _ => hash_one _)
  have sample : IsQueryBoundP (liftComp (sampleParts (C := C)) (LocalSpec C)) Region 0 :=
    prob_zero _
  unfold prssSetup
  refine ((localStep_bound sample).bind (m := 3 * C.n) (fun own => ?_)).mono (by omega)
  unfold commitRevealEcho
  simp only [bind_assoc]
  refine ((hm _).bind (fun commits =>
    (PartyBudget.of_all (PartyBound.exchange _)).bind (fun committed =>
      (PartyBudget.of_all (PartyBound.exchange _)).bind (fun revealed =>
        (hm _).bind (fun opens =>
          (PartyBudget.of_all (PartyBound.require _)).bind (fun _ =>
            (oracle_bound (derive_zero _ _ _)).bind (fun keys =>
              (hm _).bind (fun shared =>
                (PartyBudget.of_all (PartyBound.exchange _)).bind (fun received =>
                  (PartyBudget.of_all (PartyBound.require _)).bind (fun _ =>
                    (PartyBudget.pure _).bind (fun result => PartyBudget.pure _))))))))))).mono ?_
  omega


/-- The circuit layer loop preserves its deterministic total tuple count. -/
theorem layers_cont_bound (gadgets : RunGadgets C E G)
    (hm : ∀ x y count, RunBudget Region (gadgets.mult x y count) 0) (jobs : List Circuit)
    (layers : List ℕ) (count n : ℕ)
    (k : List (C.Term → List Bit) × List (Tuple C) → RunM C E G α)
    (hk : ∀ p, (p.2.map (·.count)).sum = count → RunBudget Region (k p) n)
    (p : List (C.Term → List Bit) × List (Tuple C))
    (hc : (p.2.map (·.count)).sum + (layers.map fun l => (gatesAt jobs l).length).sum = count) :
    RunBudget Region (layers.foldlM (layerBody K gadgets jobs) p >>= k) n := by
  induction layers generalizing p with
  | nil =>
    simp only [List.foldlM_nil, pure_bind]
    exact hk p (by simpa using hc)
  | cons l layers ih =>
    simp only [List.foldlM_cons, layerBody, bind_assoc, pure_bind]
    refine (hm _ _ _).bind_zero (fun z => ih _ ?_)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil] at hc ⊢
    omega

theorem runJobs_bound (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunBudget Region (runJobs K (realRunGadgets K ctx mode : RunGadgets C E G) jobs inputs)
      (4 * termCount C + halvings (tupleCount jobs) + 2) := by
  have hm : ∀ x y count, RunBudget Region
      ((realRunGadgets K ctx mode : RunGadgets C E G).mult x y count) 0 := by
    intro x y count
    change RunBudget Region (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshareWith_zero K ctx mode r _ count)
  have hr : ∀ v count, RunBudget Region
      ((realRunGadgets K ctx mode : RunGadgets C E G).rerand v count) 0 := by
    intro v count
    change RunBudget Region (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshare_zero K ctx _ r _ count)
  rw [runJobs_eq]
  refine layers_cont_bound K _ hm jobs _
    ((List.range (depth jobs)).map fun l => (gatesAt jobs l).length).sum _ _
    (fun p hc => ?_) (inputs, []) (by simp)
  unfold tailBody
  refine (hr _ _).bind_zero (fun v => ?_)
  have hc' : ((p.2 ++ [(⟨outputShares K jobs p.1, one K, v, (outputsOf jobs).length, .peer⟩ : Tuple C)]).map
      (·.count)).sum = tupleCount jobs := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero, hc, tupleCount_eq]
  have hv := check_bound (G := G) K ctx _ (gadgets_zero K ctx)
    (p.2 ++ [⟨outputShares K jobs p.1, one K, v, (outputsOf jobs).length, .peer⟩])
  rw [hc'] at hv
  exact (hv.bind (fun _ => (RunBudget.lift (openRep_bound K ctx v _)).bind
    (fun out => RunBudget.pure _ 0))).mono (by omega)


theorem RunBudget.mapM_mem {δ : Type} (f : δ → StateT σ (PartyM C E G) α)
    (n : ℕ) (xs : List δ) (hf : ∀ x ∈ xs, RunBudget P (f x) n) :
    RunBudget P (xs.mapM f) (xs.length * n) := by
  induction xs with
  | nil => exact .pure _ _
  | cons x xs ih =>
    simpa [List.mapM_cons, Nat.succ_mul, Nat.add_comm] using
      (hf x (List.mem_cons_self ..)).bind (fun y =>
        (ih (fun z hz => hf z (List.mem_cons_of_mem _ hz))).bind
          (fun ys => RunBudget.pure (y :: ys) 0))

attribute [local irreducible] maxBatch

def batchCost : ℕ := 4 * termCount C +
  maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2

theorem batch_bound (ctx : Context C) (jobs : List Job)
    (hj : halvings (tupleCount (runCircuits circuits ctx.keys.parameter jobs)) ≤
      maxBatch circuits settings (fun js => halvings (tupleCount js))) :
    RunBudget Region (treeSimHashBatch (G := G) K circuits settings ctx jobs)
      (batchCost (C := C) circuits settings) := by
  have hi : PartyBudget Region (jobs.mapM (inputShares ctx) : PartyM C E G _) 0 := by
    simpa using party_mapM (inputShares ctx) 0 (inputShares_zero ctx) jobs
  unfold treeSimHashBatch
  refine ((RunBudget.get (C := C) (E := E) (G := G) (σ := ℕ × ℕ)).bind
    (fun s => (RunBudget.lift hi).bind (fun inputs =>
      (RunBudget.lift
        (runJobs_bound K ctx settings.mode _ inputs ⟨fun _ => [], s.1, s.2⟩)).bind
        (fun result => (RunBudget.set _).bind (fun _ => RunBudget.pure _ 0))))).mono ?_
  unfold batchCost
  change halvings (tupleCount (jobs.map (circuits ctx.keys.parameter ·.kind))) ≤ _ at hj
  omega

attribute [local irreducible] topJobs bottomJobs signJobs

theorem batched_bound (ctx : Context C) (b : Fin (2 ^ layerHeight)) (enc : Encoding) (jobs : List Job)
    (hj : jobs = topJobs ∨ jobs = bottomJobs b ∨ jobs = signJobs b enc) :
    RunBudget Region (batched settings.batchSize (treeSimHashBatch (G := G) K circuits settings ctx) jobs)
      ((chunks settings.batchSize jobs).length * batchCost (C := C) circuits settings) := by
  have hmeasure (js : List Job) (hjs : js ∈ chunks settings.batchSize jobs) :
      halvings (tupleCount (runCircuits circuits ctx.keys.parameter js)) ≤
        maxBatch circuits settings (fun js => halvings (tupleCount js)) := by
    apply measure_le_maxBatch circuits settings (fun js => halvings (tupleCount js)) ctx.keys.parameter b enc js
    exact hj.elim
      (fun ht => Or.inl ((congrArg (fun xs => js ∈ chunks settings.batchSize xs) ht).mp hjs))
      (fun ht => ht.elim
        (fun ht => Or.inr (Or.inl ((congrArg (fun xs => js ∈ chunks settings.batchSize xs) ht).mp hjs)))
        (fun ht => Or.inr (Or.inr ((congrArg (fun xs => js ∈ chunks settings.batchSize xs) ht).mp hjs))))
  unfold batched
  have hb := RunBudget.mapM_mem (treeSimHashBatch (G := G) K circuits settings ctx)
    (batchCost (C := C) circuits settings) (chunks settings.batchSize jobs)
    (fun js hjs => batch_bound K circuits settings ctx js (hmeasure js hjs))
  have hend (outputs : List (Option (List (List Bit)))) :
      RunBudget Region (pure (outputs.foldlM (fun acc batch => batch.map (fun x => acc ++ x)) []) :
        StateT (ℕ × ℕ) (PartyM C E G) (Option (List (List Bit)))) 0 := .pure _ 0
  exact hb.bind_right_zero hend

theorem ceremonyOutput_bound (N : ℕ)
    (lift : ∀ {δ : Type}, OracleComp HashSpec δ → StateT σ (PartyM C E G) δ)
    (hl : ∀ {δ : Type} (oa : OracleComp HashSpec δ), RunBudget Region (lift oa) 0)
    (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hr : ∀ (b : Fin (2 ^ layerHeight)) (enc : Encoding) (jobs : List Job),
      (jobs = topJobs ∨ jobs = bottomJobs b ∨ jobs = signJobs b enc) → RunBudget Region (run jobs)
      ((chunks settings.batchSize jobs).length * N))
    (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    RunBudget Region (ceremonyOutput lift parameter run top tree)
      (treeBatches settings tree * N) := by
  cases tree with
  | top =>
    unfold ceremonyOutput treeBatches
    refine (hr 0 (fun _ => digit 0) topJobs (Or.inl rfl)).bind (m := 0) (fun outputs => ?_)
    cases outputs with
    | none => exact .pure _ 0
    | some outputs => exact (hl _).bind (m := 0) (fun root => .pure _ 0)
  | bottom b =>
    unfold ceremonyOutput treeBatches
    rw [Nat.add_mul]
    refine (hr b (fun _ => digit 0) (bottomJobs b) (Or.inr (Or.inl rfl))).bind (fun outputs => ?_)
    cases outputs with
    | none => exact .pure _ _
    | some outputs =>
      refine (hl _).bind_zero (fun root => (hl _).bind_zero (fun base => (hl _).bind_zero
        (fun found => ?_)))
      cases found with
      | none => exact .pure _ _
      | some result =>
        have h := hr b result.2 (signJobs b result.2) (Or.inr (Or.inr rfl))
        rw [length_chunks_signJobs settings b b result.2 (fun _ => digit 0)] at h
        refine h.bind (m := 0) (fun values => ?_)
        cases values with
        | none => exact .pure _ 0
        | some values =>
          refine (hl _).bind (m := 0) (fun path => (hl _).bind (m := 0) (fun root => ?_))
          split_ifs <;> exact .pure _ 0


/-- Raw region calls in one complete party program, including setup and all batches. -/
theorem ceremony_bound (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PartyBudget Region (ceremony K circuits settings i keys top tree : PartyM C E G _)
      (3 * C.n + treeBatches settings tree * batchCost (C := C) circuits settings) := by
  unfold ceremony ceremonyWith
  refine (setup_bound (E := E) (G := G) i).bind (fun prss => ?_)
  let ctx : Context C := ⟨i, keys, prss⟩
  have hb := ceremonyOutput_bound (G := G) (σ := ℕ × ℕ) settings
    (batchCost (C := C) circuits settings)
    (fun {δ} (oa : OracleComp HashSpec δ) => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => RunBudget.lift (oracle_bound (tweakable_zero oa)))
    (batched settings.batchSize (treeSimHashBatch K circuits settings ctx))
    (batched_bound K circuits settings ctx) keys.parameter top tree
  apply (hb.run' (0, 0)).bind (m := 0) (fun out => ?_) |>.mono (by omega)
  cases out with
  | none => exact PartyBudget.of_all PartyBound.failure
  | some out => exact PartyBudget.pure _

end TreeSimHashCount

/-- Forget the distinction between the two local interfaces, without answering queries. -/
def treeSimHashMerge : QueryImpl (LocalSpec C + LocalSpec C) (OracleComp (LocalSpec C))
  | .inl t => OracleComp.lift (OracleSpec.query t)
  | .inr t => OracleComp.lift (OracleSpec.query t)

theorem treeSimHash_merge_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimHashMerge (treeSimLocalRoles.adversary p) = p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query, treeSimHashMerge]
    exact congrArg (OracleComp.lift (OracleSpec.query t) >>= ·) (funext ih)

theorem treeSimHash_merge_honest {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimHashMerge (treeSimLocalRoles.honest p) = p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query, treeSimHashMerge]
    exact congrArg (OracleComp.lift (OracleSpec.query t) >>= ·) (funext ih)

/-- The merged syntax retains the actual adversary, scheduling, and stopping decisions. -/
theorem treeSimHash_merge_game (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    simulateQ treeSimHashMerge (treeSimLocalRealGame K circuits settings top tree D A x z Z) =
      (do
        let state ← A.start (corruptInputs D x) z
        let out ← executePhase localRoles D A noFunctionality (ceremonyFuel circuits settings)
          state (fun i => ceremony K circuits settings i (x i) top tree)
        Z out) := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  unfold treeSimLocalRealGame
  simp only [simulateQ_bind, treeSimHash_merge_adversary]
  congr 1
  funext state
  rw [treeSim_hom_phase (fun p => simulateQ treeSimHashMerge p)
    (fun a => by simp) (fun p f => by simp [simulateQ_bind])
    treeSimLocalRoles localRoles (fun p => treeSimHash_merge_adversary p)
    (fun p => treeSimHash_merge_honest p)]


namespace TreeSimHashCount

/-- Coarse whole-ceremony region count. It is used only to find a good completion. -/
theorem game_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    IsQueryBoundP
      (simulateQ treeSimHashMerge (treeSimLocalRealGame K circuits settings top tree D A x z Z))
      Region (q + C.n * (3 * C.n + treeBatches settings tree * batchCost (C := C) circuits settings)) := by
  rw [treeSimHash_merge_game]
  rcases hq with ⟨start, step, final, htotal, hs, hr, ha, hz⟩
  have hf : ∀ state inputs, IsQueryBoundP
      (runFunctionality localRoles D A noFunctionality state inputs) Region step := by
    intro state inputs
    unfold runFunctionality
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp
  have hp := fun state => executePhase_regionBound D A noFunctionality step
    (fun state sent => counted_splitRegionBound _ (hr state sent)) hf
    (ceremonyFuel circuits settings) state
    (fun i => ceremony K circuits settings i (x i) top tree)
    (fun _ => 3 * C.n + treeBatches settings tree * batchCost (C := C) circuits settings)
    (fun i _ => ceremony_bound K circuits settings i (x i) top tree)
  refine (isQueryBoundP_bind (counted_splitRegionBound _ (hs _ _)) (fun state _ =>
    isQueryBoundP_bind (hp state) (fun out _ => counted_splitRegionBound _ (hz out)))).mono ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

def BothRegion : (LocalSpec C + LocalSpec C).Domain → Prop
  | .inl t | .inr t => Region t

set_option backward.isDefEq.respectTransparency false in
theorem merge_bound {α : Type}
    (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ) :
    IsQueryBoundP (simulateQ treeSimHashMerge p) Region n ↔ IsQueryBoundP p BothRegion n := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    cases t <;> simp only [simulateQ_bind, simulateQ_spec_query, treeSimHashMerge,
      isQueryBoundP_query_bind_iff, BothRegion, ih] <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem local_bound (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) (cache : HiddenCache C) :
    IsQueryBoundP ((treeSimHashLocal D t).run cache) Region
      (if BothRegion t then 1 else 0) := by
  rcases t with t | (t | (t | t))
  · simp [treeSimHashLocal, BothRegion, StateT.run_lift, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff]; split_ifs <;> simp_all
  · simp [treeSimHashLocal, BothRegion, StateT.run_lift, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff]; split_ifs <;> simp_all
  · simp [treeSimHashLocal, BothRegion, StateT.run_lift, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff]; split_ifs <;> simp_all
  · have hnot : ¬ BothRegion (.inr (.inr (.inr t))) := by
      simp [BothRegion, Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain,
        TreeSimHashDomain]
    rw [if_neg hnot]
    simp only [treeSimHashLocal]
    split_ifs
    · exact prob_zero _
    · simp [StateT.run_lift, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        Region, SplitRegionCounted, splitLocalHashInput, TreeSimHashBudgetDomain, TreeSimHashDomain]

set_option backward.isDefEq.respectTransparency false in
/-- This bound retains the shared hash cache and the shared hidden PRG cache. -/
theorem normalized_bound (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (cache : HiddenCache C) :
    IsQueryBoundP
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged
        (treeSimLocalRealGame K circuits settings top tree D A x z Z))).run cache)
      Region (q + C.n * (3 * C.n + treeBatches settings tree * batchCost (C := C) circuits settings)) := by
  letI : (LocalSpec C).IsUniformSpec := OracleSpec.IsUniformSpec.ofFintypeInhabited _
  letI : (LocalSpec C + LocalSpec C).IsUniformSpec := OracleSpec.IsUniformSpec.ofFintypeInhabited _
  have h := (merge_bound _ _).mp (game_bound K circuits settings top tree D A x z Z q hq)
  have hl : IsQueryBoundP (treeSimLocalLogged
      (treeSimLocalRealGame K circuits settings top tree D A x z Z))
      BothRegion (q + C.n * (3 * C.n + treeBatches settings tree * batchCost (C := C) circuits settings)) := by
    unfold treeSimLocalLogged
    rw [isQueryBoundP_run_simulateQ_withTraceAppend_iff]
    change IsQueryBoundP (simulateQ (QueryImpl.id' _) _) _ _
    rwa [simulateQ_id']
  apply hl.simulateQ_run_of_step
  · intro t ht s
    simpa only [if_pos ht] using local_bound D t s
  · intro t ht s
    simpa only [if_neg ht] using local_bound D t s

end TreeSimHashCount

/-- Total digest queries of the complete ceremony, including the distinguisher. -/
theorem treeSimHash_game_digest (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    IsQueryBoundP
      (simulateQ treeSimHashMerge (treeSimLocalRealGame K circuits settings top tree D A x z Z))
      DigestQuery (q + treeBatches settings tree * (C.t * termCount C)) := by
  rw [treeSimHash_merge_game]
  rcases hq with ⟨start, step, final, htotal, hs, hr, ha, hz⟩
  have hf : ∀ state inputs, IsQueryBoundP
      (runFunctionality localRoles D A noFunctionality state inputs) DigestQuery step := by
    intro state inputs
    unfold runFunctionality
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp
  have hp := fun state => executePhase_digestBound D A noFunctionality step
    (fun state sent => counted_digestBound (hr state sent)) hf
    (ceremonyFuel circuits settings) state
    (fun i => ceremony K circuits settings i (x i) top tree)
    (fun i => treeBatches settings tree * treeSimHashHeld i)
    (fun i _ => treeSimHash_ceremony_digest K circuits settings i (x i) top tree)
  refine (isQueryBoundP_bind (counted_digestBound (hs _ _)) (fun state _ =>
    isQueryBoundP_bind (hp state) (fun out _ => counted_digestBound (hz out)))).mono ?_
  rw [← Finset.mul_sum, treeSimHashHeld_total]
  omega

/-- Digest queries in either side of the local representation. -/
def TreeSimHashDigest : (LocalSpec C + LocalSpec C).Domain → Prop
  | .inl t | .inr t => DigestQuery t

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_merge_bound {α : Type}
    (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ) :
    IsQueryBoundP (simulateQ treeSimHashMerge p) DigestQuery n ↔
      IsQueryBoundP p TreeSimHashDigest n := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    cases t <;> simp only [simulateQ_bind, simulateQ_spec_query, treeSimHashMerge,
      isQueryBoundP_query_bind_iff, TreeSimHashDigest, ih] <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem treeSimHash_local_digest (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) (cache : HiddenCache C) :
    IsQueryBoundP ((treeSimHashLocal D t).run cache) DigestQuery
      (if TreeSimHashDigest t then 1 else 0) := by
  rcases t with t | (t | (t | t))
  · simp [treeSimHashLocal, TreeSimHashDigest, StateT.run_lift, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff]; split_ifs <;> simp_all
  · simp [treeSimHashLocal, TreeSimHashDigest, StateT.run_lift, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff]; split_ifs <;> simp_all
  · simp [treeSimHashLocal, TreeSimHashDigest, StateT.run_lift, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff]; split_ifs <;> simp_all
  · simp only [TreeSimHashDigest, DigestQuery, digestSaltProjection, Option.isSome_none,
      Bool.false_eq_true, if_false]
    simp only [treeSimHashLocal]
    split_ifs
    · exact IsQueryBoundP.of_imp split_digestQuery_region
        (split_prob_lift_no_digest _)
    · simp [StateT.run_lift, isQueryBoundP_map_iff,
        isQueryBoundP_query_iff, DigestQuery, digestSaltProjection]

set_option backward.isDefEq.respectTransparency false in
/-- Logging and the private hidden cache preserve the whole-game digest bound. -/
theorem treeSimHash_normalized_digest (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (cache : HiddenCache C) :
    IsQueryBoundP
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged
        (treeSimLocalRealGame K circuits settings top tree D A x z Z))).run cache)
      DigestQuery (q + treeBatches settings tree * (C.t * termCount C)) := by
  letI : (LocalSpec C).IsUniformSpec := OracleSpec.IsUniformSpec.ofFintypeInhabited _
  letI : (LocalSpec C + LocalSpec C).IsUniformSpec :=
    OracleSpec.IsUniformSpec.ofFintypeInhabited _
  have h := (treeSimHash_merge_bound _ _).mp
    (treeSimHash_game_digest K circuits settings top tree D A x z Z q hq)
  have hl : IsQueryBoundP (treeSimLocalLogged
      (treeSimLocalRealGame K circuits settings top tree D A x z Z))
      TreeSimHashDigest (q + treeBatches settings tree * (C.t * termCount C)) := by
    unfold treeSimLocalLogged
    rw [isQueryBoundP_run_simulateQ_withTraceAppend_iff]
    change IsQueryBoundP (simulateQ (QueryImpl.id' _) _ ) _ _
    rwa [simulateQ_id']
  apply hl.simulateQ_run_of_step
  · intro t ht s
    simpa only [if_pos ht] using treeSimHash_local_digest D t s
  · intro t ht s
    simpa only [if_neg ht] using treeSimHash_local_digest D t s

def treeSimHashDigestSalts (log : TreeSimLog C) : List (List Bit) :=
  log.filterMap fun r => match r.1 with
    | .inl (.inl t) | .inr t => digestSaltProjection t
    | _ => none

theorem treeSimHash_digestSalts_append (a b : TreeSimLog C) :
    treeSimHashDigestSalts (a ++ b) = treeSimHashDigestSalts a ++ treeSimHashDigestSalts b := by
  exact List.filterMap_append

theorem treeSimHash_digestSalts_step (t : (LocalSpec C + LocalSpec C).Domain)
    (u : (LocalSpec C + LocalSpec C).Range t) :
    (treeSimHashDigestSalts (treeSimLocalLog t u)).length =
      if TreeSimHashDigest t then 1 else 0 := by
  rcases t with t | t
  all_goals
    cases ht : digestSaltProjection t <;>
      simp [treeSimHashDigestSalts, treeSimLocalLog, TreeSimHashDigest, DigestQuery, ht]

/-- The digest count bounds the concrete logged salt tests, including tests after an abort. -/
theorem treeSimHash_logged_digest_length (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ)
    (h : IsQueryBoundP p TreeSimHashDigest n) (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld p)).run s)) :
    (treeSimHashDigestSalts r.2.2).length ≤ (treeSimHashDigestSalts s.2).length + n := by
  induction p using OracleComp.inductionOn generalizing n s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact Nat.le_add_right _ n
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    have hb := ih mid.1 _ (h.2 mid.1) mid.2 r hr
    rw [treeSimHash_logged_step, support_map] at hmid
    obtain ⟨u, hu, rfl⟩ := hmid
    simp only [treeSimHash_digestSalts_append, List.length_append,
      treeSimHash_digestSalts_step] at hb
    by_cases ht : TreeSimHashDigest t
    · have hp := h.1.resolve_left (not_not.mpr ht)
      simp only [if_pos ht] at hb
      omega
    · simpa only [if_neg ht, Nat.add_zero] using hb

/-- The original experiment has at most the proved whole-game number of salt tests. -/
theorem treeSimHash_actual_digest_length (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (r : Bool × TreeSimLog C)
    (hr : r ∈ support (treeSimLoggedRun prims D
      (treeRealGame K circuits settings top tree D A x z Z))) :
    (treeSimHashDigestSalts r.2).length ≤ q + treeBatches settings tree * (C.t * termCount C) := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  rw [← treeSim_localReal_eq K circuits settings top tree D A x z Z] at hr
  simp only [treeSimLoggedRun, StateT.run'_eq, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  have hs : (u.1.1, u.2, u.1.2) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (simulateQ treeSimLocalWorld (treeSimLocalRealGame K circuits settings top tree D A x z Z))).run
          ((∅, ∅), [])) := by
    rw [treeSimLoggedWorld_run, support_map]
    exact ⟨u, hu, by simp⟩
  have h := treeSimHash_logged_digest_length prims D _ _
    ((treeSimHash_merge_bound _ _).mp
      (treeSimHash_game_digest K circuits settings top tree D A x z Z q hq)) _ _ hs
  simpa [treeSimHashDigestSalts] using h

def treeSimHashCountedSalt : (WorldSpec C).Domain → Option (List Bit)
  | .inl (.inl t) => digestSaltProjection t
  | _ => none

def treeSimHashCountedSalts (log : TreeSimLog C) : List (List Bit) :=
  log.filterMap fun r => treeSimHashCountedSalt r.1

theorem treeSimHash_counted_salt_charged (t : (WorldSpec C).Domain)
    (h : (treeSimHashCountedSalt t).isSome) : WorldCounted t := by
  rcases t with (t | t) | t
  · exact digestSaltProjection_counted t h
  · simp [treeSimHashCountedSalt] at h
  · simp [treeSimHashCountedSalt] at h

theorem treeSimHash_saltGuess_mem (D : C.Coalition) (log : TreeSimLog C)
    (h : TreeSimSaltGuess D log) : ∃ salt, salt ∈ treeSimHashCountedSalts log := by
  obtain ⟨salt, hist, out, _, h⟩ := h
  refine ⟨salt, List.mem_filterMap.mpr ⟨_, h, ?_⟩⟩
  rfl

theorem treeSimHash_counted_log_length (D : C.Coalition) {α : Type}
    (p : OracleComp (WorldSpec C) α) (n : ℕ) (h : IsQueryBoundP p WorldCounted n)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    (treeSimHashCountedSalts r.2.2).length ≤ (treeSimHashCountedSalts s.2).length + n := by
  induction p using OracleComp.inductionOn generalizing n s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact Nat.le_add_right _ n
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    have hb := ih mid.1 _ (h.2 mid.1) mid.2 r hr
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hmid
    obtain ⟨u, hu, rfl⟩ := hmid
    simp only [treeSimHashCountedSalts, List.filterMap_append, List.length_append,
      List.filterMap_cons, List.filterMap_nil] at hb
    dsimp only [treeSimHashCountedSalts]
    cases hp : treeSimHashCountedSalt t with
    | none =>
      simp only [hp] at hb
      by_cases ht : WorldCounted t <;>
        simp only [ht, if_true, if_false, List.length_nil] at hb <;> omega
    | some salt =>
      have ht := treeSimHash_counted_salt_charged t (by simp [hp])
      have hn := h.1.resolve_left (not_not.mpr ht)
      simp only [hp, if_pos ht, List.length_cons, List.length_nil] at hb
      omega

theorem treeSimHash_actual_counted_length (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (r : Bool × TreeSimLog C)
    (hr : r ∈ support (treeSimLoggedRun prims D
      (treeRealGame K circuits settings top tree D A x z Z))) :
    (treeSimHashCountedSalts r.2).length ≤ q := by
  have hgame : IsQueryBoundP (treeRealGame K circuits settings top tree D A x z Z) WorldCounted q :=
    isQueryBoundP_distinguish_realExecution D A noFunctionality _ _ x z Z q hq
      (fun step _ state inputs => isQueryBoundP_runFunctionality_noFunctionality D A state inputs step)
  simp only [treeSimLoggedRun, StateT.run'_eq, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  have hs : (u.1.1, u.2, u.1.2) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run ((∅, ∅), [])) := by
    rw [treeSimLoggedWorld_run, support_map]
    exact ⟨u, hu, by simp⟩
  have h := treeSimHash_counted_log_length prims D _ q hgame _ _ hs
  simpa [treeSimHashCountedSalts] using h

theorem treeSimHash_no_queries_no_saltGuess (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) 0) :
    Pr[fun r => TreeSimSaltGuess D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro r hr hguess
  have hn := treeSimHash_actual_counted_length prims K circuits settings top tree D A x z Z 0 hq r hr
  obtain ⟨salt, hs⟩ := treeSimHash_saltGuess_mem D r.2 hguess
  have he : treeSimHashCountedSalts r.2 = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [he, List.not_mem_nil] using hs

/-- Two accepted Shamir openings agree even when the honest input shares were not
known in advance to lie on a polynomial. This is enough to share one coin-key point. -/
theorem treeSimHash_openSh_agreement (D : C.Coalition) (a b : C.Party → E)
    (honest : ∀ j, j ∉ D.1 → a j = b j)
    (ha : ∀ j, a j = ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t),
      lagrangeFirst K (K.point j) l * a l)
    (hb : ∀ j, b j = ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t),
      lagrangeFirst K (K.point j) l * b l) :
    (∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * a l) =
      ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * b l := by
  classical
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  let S := Finset.univ.filter (fun l : C.Party => l.val < C.t)
  let V := Lagrange.interpolate S K.point b
  have eval (x : E) : V.eval x = ∑ l ∈ S, lagrangeFirst K x l * b l := by
    simp only [V, Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Lagrange.eval_basis_eq_prod, lagrangeFirst]
    apply Finset.sum_congr rfl
    intro l _
    rw [mul_comm]
  have deg : V.natDegree ≤ C.t - 1 := by
    apply Polynomial.natDegree_le_of_degree_le
    simpa only [V, S, card_first] using
      Lagrange.degree_interpolate_le (s := S) b K.point.injective.injOn
  have out := gs20_openSh_robust K D V deg a
    (fun j hj => (honest j hj).trans ((hb j).trans (eval (K.point j)).symm)) ha
  exact out.trans (eval 0)

/-- Every pair of surviving receivers in the actual coin round has the same value. -/
theorem treeSimHash_coin_outputs_agree (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E)
    (i j : C.Party) (a b : List E)
    (ha : treeSimCoinOutput K D count rnd sent i = some a)
    (hb : treeSimCoinOutput K D count rnd sent j = some b) : a = b := by
  classical
  have hi : i ∉ D.1 := by intro hi; simp [treeSimCoinOutput, hi] at ha
  have hj : j ∉ D.1 := by intro hj; simp [treeSimCoinOutput, hj] at hb
  let inbox := fun i k => if k ∈ D.1 then sent k i else coinOut K k count (rnd k) i
  let shares := fun i => openShare i (conv K (localContext i) (rnd i).1) (inbox i)
  have honest (i l : C.Party) (hl : l ∉ D.1) (g : ℕ) (hg : g < count) :
      shares i l g = conv K (localContext l) (rnd l).1 g := by
    simp only [shares, openShare, inbox, hl, if_false, coinOut, openOut, localContext]
    split_ifs with hli hil
    · subst l; rfl
    · exact (hli hil.symm).elim
    · change (vector count _).getD g 0 = _
      exact vector_getD _ _ g hg
  simp only [treeSimCoinOutput, if_neg hi, if_neg hj, coinRes] at ha hb
  split_ifs at ha with hai
  split_ifs at hb with hbj
  simp only [openRes] at ha hb
  letI (receiver : C.Party) : Decidable (∀ l : C.Party, ∀ g < count,
      openShare (localContext receiver).self (conv K (localContext receiver) (rnd receiver).1)
        (fun j => if j ∈ D.1 then sent j receiver else coinOut K j count (rnd j) receiver) l g =
      ∑ u ∈ Finset.univ.filter (fun u : C.Party => u.val < C.t),
        lagrangeFirst K (K.point l) u *
          openShare (localContext receiver).self (conv K (localContext receiver) (rnd receiver).1)
            (fun j => if j ∈ D.1 then sent j receiver else coinOut K j count (rnd j) receiver) u g) :=
    Classical.propDecidable _
  split_ifs at ha with hac <;> try simp only [Option.map_none, reduceCtorEq] at ha
  split_ifs at hb with hbc <;> try simp only [Option.map_none, reduceCtorEq] at hb
  simp only [Option.map_some, Option.some.injEq] at ha hb
  rw [← ha, ← hb]
  apply List.map_congr_left
  intro g hg
  have hg' : g < count := List.mem_range.mp hg
  have eq := treeSimHash_openSh_agreement K D (fun l => shares i l g) (fun l => shares j l g)
    (fun l hl => (honest i l hl g hg').trans (honest j l hl g hg').symm)
    (fun l => by simpa only [shares, inbox, localContext] using hac l g hg')
    (fun l => by simpa only [shares, inbox, localContext] using hbc l g hg')
  simpa only [shares, inbox, localContext] using eq

/-- A completed coin round contributes at most one region point, across all survivors. -/
theorem treeSimHash_coin_points (D : C.Coalition) (count tag label : ℕ)
    (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ ∀ i values,
      treeSimCoinOutput K D count rnd sent i = some values →
        Query.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v)) ∈ S := by
  classical
  by_cases live : ∃ i values, treeSimCoinOutput K D count rnd sent i = some values
  · obtain ⟨i, values, hi⟩ := live
    refine ⟨{.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))}, by simp, ?_⟩
    intro j values' hj
    rw [← treeSimHash_coin_outputs_agree K D count rnd sent i j values values' hi hj]
    exact Finset.mem_singleton_self _
  · refine ⟨∅, by simp, ?_⟩
    intro i values hi
    exact (live ⟨i, values, hi⟩).elim

/-- All actual copy inputs of one opening fit in `n * terms + 1` points.
The second pass repeats the first pass for held terms; unheld first-pass
vectors are all the same zero vector. No equality between holders is assumed. -/
theorem treeSimHash_open_points (count : ℕ) (v : C.Party → Shares C Bit)
    (inbox : C.Party → Mail C E)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0) :
    ∃ S : Finset (Query C), S.card ≤ C.n * termCount C + 1 ∧
      ∀ i T, Query.copy (vector count (v i T)) ∈ S ∧
        Query.copy (vector count (treeSimOpenCopy K i count (v i) (inbox i) T)) ∈ S := by
  let points : Finset (Query C) := Finset.univ.image fun p : C.Party × C.Term =>
    Query.copy (vector count (treeSimOpenCopy K p.1 count (v p.1) (inbox p.1) p.2))
  refine ⟨insert (.copy (vector count fun _ => (0 : Bit))) points, ?_, ?_⟩
  · have hp : points.card ≤ C.n * termCount C := by
      simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_term, termCount] using
        (Finset.card_image_le (s := (Finset.univ : Finset (C.Party × C.Term)))
          (f := fun p => Query.copy (vector count
            (treeSimOpenCopy K p.1 count (v p.1) (inbox p.1) p.2))))
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hp 1)
  · intro i T
    have hcopy : Query.copy (vector count (treeSimOpenCopy K i count (v i) (inbox i) T)) ∈
        insert (.copy (vector count fun _ => (0 : Bit))) points :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i, T), Finset.mem_univ _, rfl⟩)
    refine ⟨?_, hcopy⟩
    by_cases hi : i ∈ C.holders T
    · have he : treeSimOpenCopy K i count (v i) (inbox i) T = v i T := by
        funext g
        simp only [treeSimOpenCopy, if_pos hi]
      simpa only [he] using hcopy
    · have he : v i T = fun _ => (0 : Bit) := funext (zero i T hi)
      rw [he]
      exact Finset.mem_insert_self _ _

/-- An unknown peer term has no corrupt filler. Its copies agree whenever its
unfilled PRSS masks agree, even if all known masks and additive inputs differ. -/
theorem treeSimHash_peer_hidden (D : C.Coalition) (ctx : C.Party → Context C)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent : C.Party → Mail C E) (T : C.Term) (hidden : ¬ KnownTo D.1 T)
    (i j : C.Party) (g : ℕ) (masks : (rnd i).1 T g = (rnd j).1 T g) :
    treeSimPeerValue K D ctx rnd v sent i T g = treeSimPeerValue K D ctx rnd v sent j T g := by
  unfold treeSimPeerValue
  by_cases filled : T ∈ filledTerms K
  · rw [if_pos filled, if_pos filled]
    apply Finset.sum_congr rfl
    intro a ha
    have haT : a ∈ C.holders T := by
      rw [← (Finset.mem_filter.mp ha).2]
      exact K.filled_held a
    have honest : a ∉ D.1 := fun haD => hidden ⟨a, haD, haT⟩
    simp only [if_neg honest]
  · simpa only [if_neg filled] using masks

/-- Shared hidden keys and a single populated cache give identical finite PRSS masks.
This is independent of every known term and of all earlier circuit values. -/
theorem treeSimHash_prss_hidden (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (label idx count : ℕ) (r : C.Party → Shares C Bit) (Z : C.Party → C.Party → ℕ → Bit)
    (hash : HashCache C) (cache : HiddenCache C) (T : C.Term) (hidden : ¬ KnownTo D.1 T)
    (keys : ConsistentAt D (fun i T => (ctx i).prss.term T) T)
    (ready : ∀ i, i ∉ D.1 → i ∈ C.holders T →
      TreeSimStreamReady prims D (.term T) ((ctx i).prss.term T) label idx count (r i T) hash cache) :
    ConsistentAt D (fun i T => (treeSimPrssBits (ctx i) count (r i) (Z i)).1 T) T := by
  intro i hiT j hjT hiD hjD
  funext g
  simp only [treeSimPrssBits, self i hiD, self j hjD, if_pos hiT, if_pos hjT]
  by_cases hg : g < count
  · have hi := ready i hiD hiT
    have hj := ready j hjD hjT
    simp only [TreeSimStreamReady, Hidden, if_pos hidden] at hi hj
    have eqkeys := keys i hiT j hjT hiD hjD
    dsimp only at eqkeys
    have eq := hi g hg
    rw [eqkeys] at eq
    have values := Option.some.inj (eq.symm.trans (hj g hg))
    change (vector count (r i T)).getD g 0 = (vector count (r j T)).getD g 0
    simpa only [vector_getD _ _ g hg] using values
  · simp [List.getD, List.getElem?_eq_none
      (show (List.range count).length ≤ g by simpa using Nat.le_of_not_gt hg)]

/-- The actual peer exchange preserves hidden-term consistency. -/
theorem treeSimHash_reshare_hidden (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (count : ℕ)
    (sent : C.Party → Mail C E) (T : C.Term) (hidden : ¬ KnownTo D.1 T)
    (masks : ConsistentAt D (fun i T => (rnd i).1 T) T) :
    ConsistentAt D (fun i T => reshareZ K (ctx i) (bitCodec (E := E))
      (rnd i).1 (rnd i).2 (v i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) bitCodec (rnd j).1 (rnd j).2 (v j) count i) T) T := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  intro i hiT j hjT hiD hjD
  funext g
  simp only [treeSim_reshareZ_value K D ctx self rnd v count sent i hiD T g,
    treeSim_reshareZ_value K D ctx self rnd v count sent j hjD T g]
  simp only [hiT, hjT, not_true_eq_false, false_or]
  by_cases hg : count ≤ g
  · simp only [if_pos hg]
  · simp only [if_neg hg]
    exact treeSimHash_peer_hidden K D ctx rnd v sent T hidden i j g
      (congrFun (masks i hiT j hjT hiD hjD) g)

/-- The final rerandomization restores hidden-term agreement from its own PRSS
draw. Its additive inputs can be arbitrary, so no circuit or collector invariant
is required for this part of the batch-to-batch argument. -/
theorem treeSimHash_rerand_hidden (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (label count : ℕ) (r : C.Party → Shares C Bit) (Z : C.Party → C.Party → ℕ → Bit)
    (hash : HashCache C) (cache : HiddenCache C) (T : C.Term) (hidden : ¬ KnownTo D.1 T)
    (keys : ConsistentAt D (fun i T => (ctx i).prss.term T) T)
    (ready : ∀ i, i ∉ D.1 → i ∈ C.holders T →
      TreeSimStreamReady prims D (.term T) ((ctx i).prss.term T) label 0 count (r i T) hash cache)
    (v : C.Party → ℕ → Bit) (sent : C.Party → Mail C E) :
    let rnd := fun i => treeSimPrssBits (ctx i) count (r i) (Z i)
    ConsistentAt D (fun i T => reshareZ K (ctx i) (bitCodec (E := E))
      (rnd i).1 (rnd i).2 (v i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) bitCodec (rnd j).1 (rnd j).2 (v j) count i) T) T := by
  exact treeSimHash_reshare_hidden K D ctx self _ v count sent T hidden
    (treeSimHash_prss_hidden prims D ctx self label 0 count r Z hash cache T hidden keys ready)

/-- Every known term has an honest nonholder who checks its copies. -/
theorem treeSimHash_known_nonholder (D : C.Coalition) (T : C.Term)
    (known : KnownTo D.1 T) : ∃ i, i ∉ D.1 ∧ i ∉ C.holders T := by
  classical
  obtain ⟨h, hhD, hhT⟩ := known
  by_contra hn
  have sub : T.1 ⊆ D.1 := by
    intro i hi
    by_contra hiD
    exact hn ⟨i, hiD, by simpa [Committee.holders] using hi⟩
  have hh : h ∉ T.1 := by simpa [Committee.holders] using hhT
  have card := Finset.card_le_card (Finset.insert_subset hhD sub)
  rw [Finset.card_insert_of_notMem hh, T.2] at card
  have ht := C.one_le_t
  have hd := D.2
  omega

/-- An accepting nonholder agrees with each honest holder separately. No
agreement of the holder inputs or of known PRSS keys is assumed. -/
theorem treeSimHash_open_holder_eq (D : C.Coalition) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (hlen : ∀ h, (ds h).length = C.terms.length)
    (i h : C.Party) (T : C.Term) (hiT : i ∉ C.holders T)
    (hhD : h ∉ D.1) (hhT : h ∈ C.holders T)
    (inbox : Mail C E) (hinbox : ∀ h, h ∉ D.1 →
      inbox h = repOutbox K h (v h) count (ds h) i)
    (cds : List HashOutput) (hcdlen : cds.length = C.terms.length)
    (cache : HashCache C) (good : ¬ MainCopyCollision cache)
    (hds : ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      cache (.copy (vector count (v h T))) = some u)
    (hcds : ∃ u, cds[C.terms.idxOf T]? = some u ∧
      cache (.copy (vector count (repCopy K i (v i) count inbox T))) = some u)
    (valid : repCheck K i inbox cds) (g : ℕ) (hg : g < count) :
    repCopy K i (v i) count inbox T g = v h T g := by
  by_cases owner : h = K.owner T
  · subst h
    have hne : i ≠ K.owner T := fun he => hiT (he ▸ K.owner_held T)
    simp only [repCopy, if_neg hiT, hinbox _ hhD, repOutbox, if_neg hne,
      Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    exact getD_flatMap_vector _ _ _ T
      (List.mem_filter.mpr ⟨mem_terms T, by simp [hiT]⟩) (terms_nodup.filter _) g hg
  · have check := valid T hiT h hhT owner
    dsimp only at check
    rw [hinbox h hhD, main_open_hash_sent K i h (v h) count (ds h) (hlen h) T hiT hhT owner,
      lookup_zip_idxOf C.terms cds hcdlen T (mem_terms T)] at check
    obtain ⟨a, ha, hca⟩ := hds
    obtain ⟨b, hb, hcb⟩ := hcds
    rw [ha, hb] at check
    have hab := Option.some.inj check
    subst b
    have eq := main_copy_eq_of_not_collision cache good
      (vector count (repCopy K i (v i) count inbox T)) (vector count (v h T)) a hcb hca
    have point := congrArg (fun xs : List Bit => xs.getD g 0) eq
    simpa only [vector_getD _ _ g hg] using point

/-- If every honest receiver accepts, the copy checks establish consistency of
known terms. Only consistency of hidden terms is needed as an input invariant. -/
theorem treeSimHash_open_all_consistent (D : C.Coalition) (count : ℕ)
    (v : C.Party → Shares C Bit)
    (hidden : ∀ T, ¬ KnownTo D.1 T → ConsistentAt D (fun i T => vector count (v i T)) T)
    (ds : C.Party → List HashOutput) (hlen : ∀ h, (ds h).length = C.terms.length)
    (inbox : C.Party → Mail C E) (hinbox : ∀ i h, h ∉ D.1 →
      inbox i h = repOutbox K h (v h) count (ds h) i)
    (cds : C.Party → List HashOutput) (hcdlen : ∀ i, (cds i).length = C.terms.length)
    (cache : HashCache C) (good : ¬ MainCopyCollision cache)
    (hds : ∀ h, h ∉ D.1 → ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      cache (.copy (vector count (v h T))) = some u)
    (hcds : ∀ i, i ∉ D.1 → ∀ T, ∃ u, (cds i)[C.terms.idxOf T]? = some u ∧
      cache (.copy (vector count (repCopy K i (v i) count (inbox i) T))) = some u)
    (valid : ∀ i, i ∉ D.1 → repCheck K i (inbox i) (cds i)) :
    Consistent D (fun i T => vector count (v i T)) := by
  intro T
  by_cases known : KnownTo D.1 T
  · obtain ⟨i, hiD, hiT⟩ := treeSimHash_known_nonholder D T known
    intro a haT b hbT haD hbD
    apply List.map_congr_left
    intro g hg
    have hg' := List.mem_range.mp hg
    have first := treeSimHash_open_holder_eq K D count v ds hlen i a T hiT haD haT
      (inbox i) (hinbox i) (cds i) (hcdlen i) cache good (hds a haD T)
      (hcds i hiD T) (valid i hiD) g hg'
    have second := treeSimHash_open_holder_eq K D count v ds hlen i b T hiT hbD hbT
      (inbox i) (hinbox i) (cds i) (hcdlen i) cache good (hds b hbD T)
      (hcds i hiD T) (valid i hiD) g hg'
    exact first.symm.trans second
  · exact hidden T known

/-- All successful opening outputs agree, without assuming agreement of known PRSS keys. -/
theorem treeSimHash_open_all_outputs (D : C.Coalition) (count : ℕ)
    (v : C.Party → Shares C Bit)
    (hidden : ∀ T, ¬ KnownTo D.1 T → ConsistentAt D (fun i T => vector count (v i T)) T)
    (ds : C.Party → List HashOutput) (hlen : ∀ h, (ds h).length = C.terms.length)
    (inbox : C.Party → Mail C E) (hinbox : ∀ i h, h ∉ D.1 →
      inbox i h = repOutbox K h (v h) count (ds h) i)
    (cds : C.Party → List HashOutput) (hcdlen : ∀ i, (cds i).length = C.terms.length)
    (cache : HashCache C) (good : ¬ MainCopyCollision cache)
    (hds : ∀ h, h ∉ D.1 → ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      cache (.copy (vector count (v h T))) = some u)
    (hcds : ∀ i, i ∉ D.1 → ∀ T, ∃ u, (cds i)[C.terms.idxOf T]? = some u ∧
      cache (.copy (vector count (repCopy K i (v i) count (inbox i) T))) = some u)
    (valid : ∀ i, i ∉ D.1 → repCheck K i (inbox i) (cds i))
    (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) :
    vector count (fun g => ∑ T, repCopy K i (v i) count (inbox i) T g) =
      vector count (fun g => ∑ T, repCopy K j (v j) count (inbox j) T g) := by
  have agree := treeSimHash_open_all_consistent K D count v hidden ds hlen inbox hinbox cds hcdlen
    cache good hds hcds valid
  let w : Shares C Bit := fun T => v (mainRefHolder D T) T
  have held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < count → v i T g = w T g := by
    intro i T g hi hiT hg
    have eq := agree T i hiT (mainRefHolder D T) (mainRefHolder_spec D T).1 hi
      (mainRefHolder_spec D T).2
    have point := congrArg (fun xs : List Bit => xs.getD g 0) eq
    simpa only [vector_getD _ _ g hg] using point
  have output (a : C.Party) (ha : a ∉ D.1) (T : C.Term) (g : ℕ) (hg : g < count) :=
    main_openCopy_sound K D w v count held ds hlen a ha (inbox a) (hinbox a)
      (cds a) (hcdlen a) cache good (fun h T hh => hds h hh T) (hcds a ha) (valid a ha) T g hg
  apply List.map_congr_left
  intro g hg
  apply Finset.sum_congr rfl
  intro T _
  exact (output i hi T g (List.mem_range.mp hg)).trans
    (output j hj T g (List.mem_range.mp hg)).symm

/-- The selected hash region is injective on a log without a collision. -/
theorem treeSimHash_log_injective (log : TreeSimLog C) (good : ¬ TreeSimHashCollision log)
    (q r : Query C) (h : HashOutput) (hq : TreeSimHashDomain q) (hr : TreeSimHashDomain r)
    (aq : TreeSimHashAnswer log q h) (ar : TreeSimHashAnswer log r h) : q = r := by
  by_contra hne
  exact good ⟨q, r, h, hq, hr, hne, aq, ar⟩

omit [Field E] [Algebra Bit E] in
/-- Any surviving digest receiver forces identical honest digest inputs.
This applies to all terms, including distinct salts and distinct PRSS keys. -/
theorem treeSimHash_digest_inputs_equal (D : C.Coalition) (log : TreeSimLog C)
    (good : ¬ TreeSimHashCollision log)
    (salts histories : C.Party → C.Term → List Bit)
    (inner outer : C.Party → C.Term → HashOutput) (ds : C.Party → List HashOutput)
    (answers : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
      TreeSimHashAnswer log (.history (histories i T)) (inner i T) ∧
      TreeSimHashAnswer log (.digest (salts i T) (inner i T)) (outer i T) ∧
      (ds i)[C.terms.idxOf T]? = some (outer i T))
    (sent : C.Party → Mail C E) (receiver : C.Party)
    (live : digestLive D ds sent receiver)
    (T : C.Term) (a b : C.Party) (ha : a ∉ D.1) (hb : b ∉ D.1)
    (haT : a ∈ C.holders T) (hbT : b ∈ C.holders T) :
    histories a T = histories b T ∧
      Query.digest (C := C) (salts a T) (inner a T) = Query.digest (salts b T) (inner b T) := by
  have rows : (ds a)[C.terms.idxOf T]? = (ds b)[C.terms.idxOf T]? := by
    have read : ∀ j, j ∉ D.1 →
        (if j = receiver then ds receiver else Msg.hashesOf (digestInbox D ds sent receiver j)) = ds j := by
      intro j hj
      by_cases hji : j = receiver
      · subst j
        simp
      · simp [digestInbox, digestOutbox, hj, hji, Ne.symm hji, Msg.hashesOf]
    simpa only [read a ha, read b hb] using (live.2 T a haT b hbT).1
  have same : outer a T = outer b T :=
    Option.some.inj ((answers a ha T haT).2.2.symm.trans (rows.trans (answers b hb T hbT).2.2))
  have hd : Query.digest (C := C) (salts a T) (inner a T) =
      Query.digest (salts b T) (inner b T) :=
    treeSimHash_log_injective log good _ _ (outer a T) trivial trivial
      (answers a ha T haT).2.1 (same.symm ▸ (answers b hb T hbT).2.1)
  have hh : Query.history (C := C) (histories a T) = Query.history (histories b T) :=
    treeSimHash_log_injective log good _ _ (inner a T) trivial trivial
      (answers a ha T haT).1 ((Query.digest.inj hd).2.symm ▸ (answers b hb T hbT).1)
  exact ⟨Query.history.inj hh, hd⟩

omit [Field E] [Algebra Bit E] in
/-- A digest phase with a surviving receiver uses only two points per term,
unless the fixed collision event has already occurred. -/
theorem treeSimHash_digest_points (D : C.Coalition) (log : TreeSimLog C)
    (good : ¬ TreeSimHashCollision log)
    (salts histories : C.Party → C.Term → List Bit)
    (inner outer : C.Party → C.Term → HashOutput) (ds : C.Party → List HashOutput)
    (answers : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
      TreeSimHashAnswer log (.history (histories i T)) (inner i T) ∧
      TreeSimHashAnswer log (.digest (salts i T) (inner i T)) (outer i T) ∧
      (ds i)[C.terms.idxOf T]? = some (outer i T))
    (sent : C.Party → Mail C E) (receiver : C.Party)
    (live : digestLive D ds sent receiver) :
    ∃ S : Finset (Query C), S.card ≤ 2 * termCount C ∧
      ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
        Query.history (histories i T) ∈ S ∧ Query.digest (salts i T) (inner i T) ∈ S := by
  let representative : C.Term → C.Party := fun T => (exists_honest_holder D T).choose
  let point : C.Term × Bool → Query C := fun p =>
    if p.2 then .history (histories (representative p.1) p.1)
    else .digest (salts (representative p.1) p.1) (inner (representative p.1) p.1)
  refine ⟨Finset.univ.image point, ?_, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      card_term, termCount, Nat.mul_comm] using
      Finset.card_image_le (s := (Finset.univ : Finset (C.Term × Bool))) (f := point)
  · intro i hi T hiT
    have hr := (exists_honest_holder D T).choose_spec
    have he := treeSimHash_digest_inputs_equal D log good salts histories inner outer ds
      answers sent receiver live T i (representative T) hi hr.2 hiT hr.1
    refine ⟨Finset.mem_image.mpr ⟨(T, true), Finset.mem_univ _, ?_⟩,
      Finset.mem_image.mpr ⟨(T, false), Finset.mem_univ _, ?_⟩⟩
    · simpa only [point, Bool.true_eq, ↓reduceIte] using
        congrArg (Query.history (C := C)) he.1.symm
    · simpa only [point, Bool.false_eq_true, ↓reduceIte] using he.2.symm

/-- Even a terminal, inconsistent digest phase uses two points per holder. -/
theorem treeSimHash_digest_terminal_points
    (salts histories : C.Party → C.Term → List Bit)
    (inner : C.Party → C.Term → HashOutput) :
    ∃ S : Finset (Query C), S.card ≤ (C.n + 1) * termCount C ∧
      ∀ i T, i ∈ C.holders T → Query.history (histories i T) ∈ S ∧
        Query.digest (salts i T) (inner i T) ∈ S := by
  let points : C.Term → C.Party → Finset (Query C) := fun T i =>
    {Query.history (histories i T), Query.digest (salts i T) (inner i T)}
  refine ⟨Finset.univ.biUnion (fun T => (C.holders T).biUnion (points T)), ?_, ?_⟩
  · calc
      _ ≤ ∑ T : C.Term, ((C.holders T).biUnion (points T)).card := Finset.card_biUnion_le
      _ ≤ ∑ T : C.Term, ∑ i ∈ C.holders T, (points T i).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ T : C.Term, ∑ _i ∈ C.holders T, 2 := by
        gcongr with T hT i hi
        simp [points]
      _ = _ := by
        have hn : C.t * 2 = C.n + 1 := by
          have := C.one_le_t
          unfold Committee.n
          omega
        simp only [Finset.sum_const, smul_eq_mul, keygen_card_holders, Finset.card_univ,
          card_term, termCount, hn]
        exact Nat.mul_comm _ _
  · intro i T hi
    constructor <;> apply Finset.mem_biUnion.mpr
    · exact ⟨T, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨i, hi, by simp [points]⟩⟩
    · exact ⟨T, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨i, hi, by simp [points]⟩⟩

/-- Remove exactly the PRSS points already charged by the key hop. -/
theorem treeSimHash_rest (tree : Tree) :
    treeSecrets circuits settings C tree - 2 * prssKeyCount C =
      C.n * (termCount C + C.n) + C.n ^ 2 +
        treeBatches settings tree * (3 * termCount C + C.n * termCount C +
          maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2) := by
  unfold treeSecrets prssKeyCount
  simp only
  omega


/-- The raw selected-call count is small enough to extend every good prefix. -/
theorem treeSimHash_coarse_square (tree : Tree) (q : ℕ) :
    q + C.n * (3 * C.n + treeBatches settings tree * TreeSimHashCount.batchCost (C := C) circuits settings) ≤
      (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 := by
  rw [treeSimHash_rest]
  have hn : 1 ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have ht := treeSimHash_parties_le_terms (C := C)
  have hs : 3 * C.n ≤ C.n * (termCount C + C.n) + C.n ^ 2 := by nlinarith
  have hb : TreeSimHashCount.batchCost (C := C) circuits settings ≤
      3 * termCount C + C.n * termCount C +
        maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2 := by
    unfold TreeSimHashCount.batchCost
    nlinarith [Nat.mul_le_mul_right (termCount C) hn]
  have hb' := Nat.mul_le_mul_left (treeBatches settings tree) hb
  have hp := Nat.mul_le_mul_left C.n (Nat.add_le_add hs hb')
  have hq := Nat.mul_le_mul_right q hn
  have hN : C.n ≤ q + (C.n * (termCount C + C.n) + C.n ^ 2 +
      treeBatches settings tree * (3 * termCount C + C.n * termCount C +
        maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)) := by omega
  have hf := Nat.mul_le_mul_right
    (q + (C.n * (termCount C + C.n) + C.n ^ 2 +
      treeBatches settings tree * (3 * termCount C + C.n * termCount C +
        maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2))) hN
  nlinarith only [hp, hq, hf]

/-- The normalized actual ceremony, with its log and the one shared hidden cache. -/
def treeSimHashProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (LocalSpec C) ((Bool × TreeSimLog C) × HiddenCache C) :=
  (simulateQ (treeSimHashLocal D) (treeSimLocalLogged
    (treeSimLocalRealGame K circuits settings top tree D A x z Z))).run ∅

/-- A final-cache count now suffices for the actual shared-cache birthday bound. -/
theorem treeSimHash_terminal_fresh (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (hsmall : q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) < 2 ^ 128)
    (terminal : ∀ r ∈ support ((simulateQ (localAnswer prims)
        (treeSimHashProgram K circuits settings top tree D A x z Z)).run ∅),
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2) →
      SplitCacheBound (splitRegionCache TreeSimHashBudgetDomain r.2)
        (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C))) :
    TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      (treeSimHashProgram K circuits settings top tree D A x z Z) ∅
      (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) := by
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  have coarse := (TreeSimHashCount.normalized_bound K circuits settings top tree D A x z Z q hq ∅).mono
    (treeSimHash_coarse_square circuits settings tree q)
  have small : (∅ : Finset (Query C)).card + N ^ 2 < 2 ^ 256 := by
    simp only [Finset.card_empty, Nat.zero_add]
    calc N ^ 2 < (2 ^ 128) ^ 2 := Nat.pow_lt_pow_left hsmall (by decide)
         _ = 2 ^ 256 := by rw [← pow_mul]
  have keys : TreeSimHashRegionKeys TreeSimHashBudgetDomain (∅ : HashCache C) ∅ := by
    intro t
    simp
  have good : ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain (∅ : HashCache C)) := by
    rintro ⟨a, b, u, v, hab, ha, hb, huv⟩
    simp [splitRegionCache] at ha
  simpa only [Finset.card_empty, Nat.sub_zero] using
    treeSimHash_fresh_of_terminal_bound prims TreeSimHashBudgetDomain
      (treeSimHashProgram K circuits settings top tree D A x z Z) ∅ ∅ N (N ^ 2)
      keys good coarse small terminal

/-- The remaining budget pays four points per distinct hidden term salt. -/
theorem treeSimHash_salt_capacity (tree : Tree) :
    4 * (treeBatches settings tree * termCount C) ≤
      treeSecrets circuits settings C tree - 2 * prssKeyCount C := by
  rw [treeSimHash_rest]
  have hn : 1 ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have ht := Nat.mul_le_mul_right (termCount C) hn
  have h : 4 * termCount C ≤ 3 * termCount C + C.n * termCount C +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2 := by omega
  have h' := Nat.mul_le_mul_left (treeBatches settings tree) h
  nlinarith

/-- The remaining hash budget also pays twice the number of honest salt uses,
including repeated holders. -/
theorem treeSimHash_raw_salt_capacity (tree : Tree) :
    2 * (treeBatches settings tree * (C.t * termCount C)) ≤
      treeSecrets circuits settings C tree - 2 * prssKeyCount C := by
  rw [treeSimHash_rest]
  have ht : 2 * C.t = C.n + 1 := by
    have := C.one_le_t
    unfold Committee.n
    omega
  have he : 2 * (C.t * termCount C) = (C.n + 1) * termCount C := by
    nlinarith
  have hb := Nat.mul_le_mul_left (treeBatches settings tree)
    (show 2 * (C.t * termCount C) ≤ 3 * termCount C + C.n * termCount C +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2 by
        rw [he]; nlinarith)
  nlinarith

/-- The recorded hash flag is exactly the fixed union on the actual log. -/
theorem treeSimHash_flag (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents prims K circuits settings)
        top tree D A x z Z] =
    Pr[fun r => TreeSimHashBad D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] := by
  simp only [treeSimTrace, treeSimEvents, probEvent_map, Function.comp_def, decide_eq_true_eq]

/-- A total of at least `2^128` makes the requested square budget at least one. -/
theorem treeSimHash_unit_budget (n : ℕ) (hn : 2 ^ 128 ≤ n) :
    1 ≤ ((n ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  have hcast : (2 : ℝ) ^ 128 ≤ (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256), one_mul, Nat.cast_pow,
    show (2 : ℝ) ^ 256 = ((2 : ℝ) ^ 128) ^ 2 by ring]
  gcongr

/-- The fixed hash bound is unconditional when its total budget is large. -/
theorem treeSimHash_bound_of_large_total (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hlarge : 2 ^ 128 ≤ q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) :
    (Pr[fun r => r.2.1 = true |
      treeSimTrace prims K circuits settings (treeSimEvents prims K circuits settings)
        top tree D A x z Z]).toReal ≤
      (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) /
        2 ^ 256 := by
  apply le_trans _ (treeSimHash_unit_budget _ hlarge)
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
    (probEvent_le_one (mx := treeSimTrace prims K circuits settings
      (treeSimEvents prims K circuits settings) top tree D A x z Z) (p := fun r => r.2.1 = true))

/-- Remaining collision estimate for the actual shared-cache ceremony. -/
def TreeSimHashCollisionEstimate : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    (Pr[fun r => TreeSimHashCollision r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
      (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) /
        (2 * 2 ^ 256)

/-- The concrete combinatorial obligation: fresh inputs in the auxiliary region
before its first collision. Setup echoes are included so that this invariant can
use PRSS key agreement. All shared caches remain in scope. -/
def TreeSimHashCeremonyBudget : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged
        (treeSimLocalRealGame K circuits settings top tree D A x z Z))).run ∅) ∅
      (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C))

/-- The concrete fresh-point certificate suffices for the actual collision estimate. -/
theorem treeSimHash_collision_of_budget
    (budget : TreeSimHashCeremonyBudget prims K circuits settings) :
    TreeSimHashCollisionEstimate prims K circuits settings := by
  classical
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  intro hb top tree D A x z Z q hx hq hsmall
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  have h := treeSimHash_logged_birthday_region prims D TreeSimHashBudgetDomain treeSimHash_domain_budget
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) N
    (budget hb top tree D A x z Z q hx hq hsmall)
  rw [treeSim_localReal_eq K circuits settings top tree D A x z Z] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] at hreal
  refine hreal.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have hn : N * (N - 1) ≤ N ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left N (Nat.sub_le N 1)
  exact_mod_cast hn

/-- Remaining adaptive salt estimate outside collisions. It includes the honest
digest tests as well as the counted queries; repeated holders do not create new salts. -/
def TreeSimHashSaltEstimate : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
      2 * ((treeBatches settings tree * termCount C : ℕ) : ℝ) *
        ((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) : ℕ) : ℝ) / 2 ^ 256

/-- An alternative salt estimate using all holder occurrences rather than distinct salts. -/
def TreeSimHashRawSaltEstimate : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
      2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) *
        ((q + treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) / 2 ^ 256

/-- Assembly with the whole-game holder-occurrence budget. -/
theorem treeSimHashBound_of_raw_estimates
    (collision : TreeSimHashCollisionEstimate prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings) :
    TreeSimHashBoundGoal prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  rw [treeSimHash_flag]
  refine (treeSimHash_union_clean D _).trans ((add_le_add
    (collision hb top tree D A x z Z q hx hq hsmall)
    (salt hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [Nat.cast_pow, Nat.cast_add]
  apply treeSimHash_union_raw_arith _ _ _ (by positivity) (by positivity)
  have hs : 2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_raw_salt_capacity (C := C) circuits settings tree
  linarith

/-- Assembly only: the two named probability estimates remain unproved. -/
theorem treeSimHashBound_of_estimates
    (collision : TreeSimHashCollisionEstimate prims K circuits settings)
    (salt : TreeSimHashSaltEstimate prims K circuits settings) :
    TreeSimHashBoundGoal prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  rw [treeSimHash_flag]
  refine (treeSimHash_union_clean D _).trans ((add_le_add
    (collision hb top tree D A x z Z q hx hq hsmall)
    (salt hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [Nat.cast_pow]
  apply treeSimHash_union_clean_arith _ _ (by positivity)
  have hs : 4 * ((treeBatches settings tree * termCount C : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_salt_capacity (C := C) circuits settings tree
  simp only [Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) q]

/-- Assembly from the concrete ceremony count and the adaptive salt estimate. -/
theorem treeSimHashBound_of_budget
    (budget : TreeSimHashCeremonyBudget prims K circuits settings)
    (salt : TreeSimHashSaltEstimate prims K circuits settings) :
    TreeSimHashBoundGoal prims K circuits settings :=
  treeSimHashBound_of_estimates prims K circuits settings
    (treeSimHash_collision_of_budget prims K circuits settings budget) salt


/-- Remaining deterministic obligation, only in the nontrivial budget range. -/
def TreeSimHashTerminalBudget : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) < 2 ^ 128 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (treeSimHashProgram K circuits settings top tree D A x z Z)).run ∅),
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2) →
      SplitCacheBound (splitRegionCache TreeSimHashBudgetDomain r.2)
        (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C))

/-- This route needs a final-cache count, rather than an inductive fresh-query certificate. -/
theorem treeSimHashBound_of_terminal
    (terminal : TreeSimHashTerminalBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings) :
    TreeSimHashBoundGoal prims K circuits settings := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  intro hb top tree D A x z Z q hx hq hsmall
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  by_cases hlarge : 2 ^ 128 ≤ N
  · exact treeSimHash_bound_of_large_total prims K circuits settings top tree D A x z Z q hlarge
  have hn : N < 2 ^ 128 := Nat.lt_of_not_ge hlarge
  have cert := treeSimHash_terminal_fresh prims K circuits settings top tree D A x z Z q hq hn
    (terminal hb top tree D A x z Z q hx hq hn)
  have h := treeSimHash_logged_birthday_region prims D TreeSimHashBudgetDomain treeSimHash_domain_budget
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) N cert
  rw [treeSim_localReal_eq K circuits settings top tree D A x z Z] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] at hreal
  have hc : (Pr[fun r => TreeSimHashCollision r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
        ((N ^ 2 : ℕ) : ℝ) / (2 * 2 ^ 256) := by
    refine hreal.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hN : N * (N - 1) ≤ N ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_left N (Nat.sub_le N 1)
    exact_mod_cast hN
  rw [treeSimHash_flag]
  refine (treeSimHash_union_clean D _).trans ((add_le_add hc
    (salt hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [N, Nat.cast_pow, Nat.cast_add]
  apply treeSimHash_union_raw_arith _ _ _ (by positivity) (by positivity)
  have hs : 2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_raw_salt_capacity (C := C) circuits settings tree
  linarith

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashCollision_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHashCollision_cache
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_cached_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_cached_step
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_fresh_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_fresh_step
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_union
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_union_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_union_arith
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_rest
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_flag
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_unit_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_unit_budget
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_bound_of_large_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_bound_of_large_total
/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBound_of_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHashBound_of_estimates

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_logged
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_normalized_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_normalized_coherent
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_logged_birthday' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_logged_birthday
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_open_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_open_points
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_digest_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_digest_points
/--
info: 'ThresholdLeanXmssSecurity.treeSimHash_digest_terminal_points' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeSimHash_digest_terminal_points
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_capacity
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_collision_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_collision_of_budget
/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBound_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHashBound_of_budget

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_ceremony_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_ceremony_digest
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_game_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_game_digest
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_normalized_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_normalized_digest
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_fresh_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_fresh_of_cover
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_hashes_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_hashes_fresh
/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBound_of_raw_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHashBound_of_raw_estimates

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_actual_digest_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_actual_digest_length
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_actual_counted_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_actual_counted_length
/--
info: 'ThresholdLeanXmssSecurity.treeSimHash_no_queries_no_saltGuess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeSimHash_no_queries_no_saltGuess
/--
info: 'ThresholdLeanXmssSecurity.treeSimHash_logged_birthday_region' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeSimHash_logged_birthday_region
/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_setup_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_setup_capacity

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_first_hit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_first_hit_eq

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_planted_rows_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_planted_rows_bound

/--
info: 'ThresholdLeanXmssSecurity.treeSimHash_digest_column_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeSimHash_digest_column_hit_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_coin_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_coin_points

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_open_all_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_open_all_outputs

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_reshare_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_reshare_hidden

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_copy_region_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_copy_region_good

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashSaltProgram_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHashSaltProgram_run

/--
info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_program_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeSimHash_salt_program_hit_bound

/--
info: 'ThresholdLeanXmssSecurity.treeSimHash_digest_column_rows_hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeSimHash_digest_column_rows_hit_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_rerand_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_rerand_hidden

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_good_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_good_completion

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_fresh_of_terminal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_fresh_of_terminal_bound

/-- info: 'ThresholdLeanXmssSecurity.TreeSimHashCount.ceremony_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimHashCount.ceremony_bound

/-- info: 'ThresholdLeanXmssSecurity.TreeSimHashCount.normalized_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimHashCount.normalized_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_coarse_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_coarse_square

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_terminal_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_terminal_fresh

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBound_of_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHashBound_of_terminal

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_projected_salt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_projected_salt_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_interleaved_hit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_interleaved_hit_eq

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_interleaved_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_interleaved_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_coordinate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_coordinate_count

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_coordinate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_coordinate_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_table_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_table_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_column_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimHash_salt_column_run

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_block_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_salt_block_support

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_block_randomOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_salt_block_randomOracle

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_prssBits_logged_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_prssBits_logged_complete

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_prssElements_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_prssElements_complete

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_digest_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_salt_digest_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_address_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_salt_address_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_salt_allocate_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_salt_allocate_capacity

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_block_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_block_eager

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_lazy_salt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_lazy_salt_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_lazy_address_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_lazy_address_bound

end ThresholdLeanXmssSecurity
