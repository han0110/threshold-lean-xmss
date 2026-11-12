import ThresholdLeanXmssSecurity.Proof.TreeRawSalt
import XmssSecurity.Proof.Deterministic.Replay

/-!
Local execution laws for the whole-ceremony raw salt normalization.

The real hidden PRSS block and its two-level digest can be implemented by an
opaque digest call, retaining the full original log through a decoder of the
final caches. The calling program receives only the digest. Repeated PRSS
addresses keep their original block; none of these laws assumes independence
between stages or between known and hidden salts. The row laws also normalize
the actual order of all hidden term draws followed by all digest queries;
`realRows_read_fullLog` retains that original transcript order. The rows can be
chosen from the state at entry to the local pass, and addresses can repeat.

The whole-run interface is the existing named Prop
`TreeRawSaltCeremonyRepresentation`.
It requires the mixed known/hidden term pass and unused pair draws,
the actual check/ceremony coroutine transformation including aborted logs,
the lazy address allocator, the global private/charged budgets, and the
salt-guess event transport under the original collision guard. The local
row bounds do not give those global budgets. A setup-fixed address cover is
not available for adaptive bottom-tree jobs. The whole-ceremony fact that
salts reach only digest queries is a global constraint; these laws do not supply
the cross-stage independence obligation of `TreeSaltStagesPairsGuarded`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeRawSaltCeremonyProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The two entries of a real honest digest, with the intermediate answer read
from the final hash cache. Later cache extension preserves this decoding. -/
def digestEntries (salt history : List Bit) (h digest : HashOutput) : TreeSimLog C :=
  [⟨.inr (.inr (.inl (.history history))), h⟩,
    ⟨.inr (.inr (.inl (.digest salt h))), digest⟩]

def digestLog (salt history : List Bit) (digest : HashOutput) (cache : HashCache C) : TreeSimLog C :=
  digestEntries salt history ((cache (.history history)).getD 0) digest

theorem digestLog_mono (salt history : List Bit) (digest : HashOutput)
    {a b : HashCache C} (hle : a ≤ b) (h : HashOutput)
    (hc : a (.history history) = some h) :
    digestLog salt history digest a = digestLog salt history digest b := by
  simp only [digestLog, hc, hle hc, Option.getD_some]

/-- The logged honest hash handler retains the same hash-cache update and
does not touch the private stream cache. -/
theorem hash_logged (prims : Primitives) (D : C.Coalition) (q : Query C)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C) :
    ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C)))).run ((cache, streams), log)) =
      (fun r => (r.1, (r.2, streams), log ++ [⟨.inr (.inr (.inl q)), r.1⟩])) <$>
        (hashAnswer prims q).run cache := by
  change ((simulateQ (treeSimLoggedWorld prims D)
    (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q)))))).run
      ((cache, streams), log)) = _
  rw [simulateQ_spec_query]
  simp only [treeSimLoggedWorld, StateT.run_mk]
  change (fun r => (r.1, r.2, log ++ [⟨.inr (.inr (.inl q)), r.1⟩])) <$>
      ((fun r => (r.1, r.2, streams)) <$> (hashAnswer prims q).run cache) = _
  simp only [Functor.map_map]

/-- Both real digest queries, including cache hits, are recovered from the
final cache and the returned digest. -/
theorem oneDigest_logged (prims : Primitives) (D : C.Coalition)
    (salt history : List Bit) (cache : HashCache C) (streams : HiddenCache C)
    (log : TreeSimLog C) :
    ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)))).run
        ((cache, streams), log)) =
      (fun r => (r.1, (r.2, streams), log ++ digestLog salt history r.1 r.2)) <$>
        (saltedDigestAnswer prims salt history).run cache := by
  simp only [oneDigestQuery, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind,
    hash_logged, saltedDigestAnswer, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro r hr
  simp only [map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro u hu
  rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hr
  have hfirst : r.2 (.history history) = some r.1 := by
    exact (randomOracle_support (.history history) cache r hr).2.1
  have hlast := (hashAnswer_support (prims := prims) (.digest salt r.1) r.2 u hu).1 hfirst
  have hd : digestLog salt history u.1 u.2 = digestEntries salt history r.1 u.1 := by
    unfold digestLog
    rw [hlast]
    rfl
  dsimp only [Function.comp_def]
  rw [hd]
  simp only [digestEntries, List.append_assoc, List.singleton_append]

theorem vector_getD_ofFn {n : ℕ} (values : Fin n → Bit) :
    vector n (fun g => (List.ofFn values).getD g 0) = List.ofFn values := by
  apply List.ext_getElem
  · simp [vector]
  · intro k hk _
    have hkn : k < n := by simpa [vector] using hk
    simp [vector, hkn]

/-- The actual hidden term block followed by the digest that consumes it. -/
def saltDigest (b : TreeSimHashSaltBlock C) (history : List Bit) :
    OracleComp (WorldSpec C) HashOutput := do
  let salt ← free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C))
  free (liftComp (oneDigestQuery (C := C) (vector 256 salt) history) (LocalSpec C))

abbrev BlockCache (C : Committee) := (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).QueryCache

/-- Only the digest leaves this handler; the sampled block stays in its
private cache. This is the private branch of `treeSimHashSaltRead`. -/
def opaqueDigest (prims : Primitives) (b : TreeSimHashSaltBlock C) (history : List Bit) :
    StateT (HashCache C × BlockCache C) ProbComp HashOutput := do
  let salt ← treeSimHashBlockCacheAnswer (localAnswer prims) (.inl b)
  let h ← treeSimHashBlockCacheAnswer (localAnswer prims) (.inr (.inr (.inl (.history history))))
  treeSimHashBlockCacheAnswer (localAnswer prims) (.inr (.inr (.inl (.digest (List.ofFn salt) h))))

theorem opaqueDigest_run (prims : Primitives) (b : TreeSimHashSaltBlock C)
    (history : List Bit) (cache : HashCache C) (blocks : BlockCache C) :
    (opaqueDigest prims b history).run (cache, blocks) = (do
      let salt ← ((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run blocks
      (fun r => (r.1, r.2, salt.2)) <$> (saltedDigestAnswer prims (List.ofFn salt.1) history).run cache) := by
  simp only [opaqueDigest, treeSimHashBlockCacheAnswer, StateT.run_bind, StateT.run_mk,
    bind_map_left, saltedDigestAnswer, map_bind]
  rfl

/-- Decode private PRG calls and both honest hash calls from final caches.
The decoder is proof instrumentation and is not exposed to the program. -/
def saltDigestDecode (b : TreeSimHashSaltBlock C) (history : List Bit)
    (streams : HiddenCache C) (log : TreeSimLog C)
    (r : HashOutput × HashCache C × BlockCache C) : HashOutput × TreeSimState C :=
  let values := (r.2.2 b).getD (fun _ => 0)
  (r.1, (r.2.1, cacheFin (treeSimHashSaltAddress b) values streams),
    (log ++ treeSimHiddenLog (treeSimHashSaltAddress b) values) ++
      digestLog (List.ofFn values) history r.1 r.2.1)

/-- Exact full-state, full-log law for a real hidden block consumed by an
opaque digest call. The initial hash cache is arbitrary and shared. -/
theorem saltDigest_joint (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬KnownTo D.1 b.1) (history : List Bit)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) :
    𝒟[((simulateQ (treeSimLoggedWorld prims D) (saltDigest b history)).run ((cache, streams), log))] =
      𝒟[saltDigestDecode b history streams log <$>
        (opaqueDigest prims b history).run (cache, treeSimHashSaltLookup streams)] := by
  simp only [saltDigest, simulateQ_bind, StateT.run_bind]
  rw [treeRawSalt_block_bind prims D b hidden cache streams log complete]
  simp only [opaqueDigest_run, map_bind]
  congr 1
  apply bind_congr_of_forall_mem_support
  intro salt hsalt
  have hc := DeterministicSigning.query_caches b (treeSimHashSaltLookup streams) salt hsalt
  rw [vector_getD_ofFn, oneDigest_logged]
  simp only [Functor.map_map]
  apply map_congr
  intro r
  dsimp only [Function.comp_def, saltDigestDecode]
  rw [hc]
  rfl

/-- Erasing the existing opaque salt interpreter's ghost lists gives
exactly this fused handler. -/
theorem opaqueDigest_read (prims : Primitives) (b : TreeSimHashSaltBlock C)
    (history : List Bit) (cache : HashCache C) (blocks : BlockCache C)
    (used : List (List Bit) × List (List Bit)) :
    (fun r => (r.1.1, r.2)) <$>
      (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
        ((treeSimHashSaltRead (C := C) (.inl (b, history))).run used)).run (cache, blocks) =
      (opaqueDigest prims b history).run (cache, blocks) := by
  simp only [treeSimHashSaltRead, StateT.run_mk, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    Prod.mk.eta, bind_pure, opaqueDigest]

/-- The one-step law uses the exact interpreter of `treeRawSaltRun`; no
replacement probability model is introduced. -/
theorem saltDigest_read_joint (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬KnownTo D.1 b.1) (history : List Bit)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams)
    (used : List (List Bit) × List (List Bit)) :
    𝒟[((simulateQ (treeSimLoggedWorld prims D) (saltDigest b history)).run ((cache, streams), log))] =
      𝒟[(fun r => saltDigestDecode b history streams log (r.1.1, r.2)) <$>
        (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
          ((treeSimHashSaltRead (C := C) (.inl (b, history))).run used)).run
            (cache, treeSimHashSaltLookup streams)] := by
  rw [saltDigest_joint prims D b hidden history cache streams log complete,
    ← opaqueDigest_read prims b history cache (treeSimHashSaltLookup streams) used]
  simp only [Functor.map_map]

/-- The normalized call leaves its block and its intermediate history answer
cached. This is the evidence needed to decode earlier entries after more calls. -/
theorem opaqueDigest_cached (prims : Primitives) (b : TreeSimHashSaltBlock C)
    (history : List Bit) (cache : HashCache C) (blocks : BlockCache C)
    (r : HashOutput × HashCache C × BlockCache C)
    (hr : r ∈ support ((opaqueDigest prims b history).run (cache, blocks))) :
    cache ≤ r.2.1 ∧ blocks ≤ r.2.2 ∧
      ∃ values h, r.2.2 b = some values ∧ r.2.1 (.history history) = some h ∧
        r.2.1 (.digest (List.ofFn values) h) = some r.1 := by
  rw [opaqueDigest_run, mem_support_bind_iff] at hr
  obtain ⟨salt, hsalt, hr⟩ := hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨output, hout, rfl⟩ := hr
  have hblocks := QueryImpl.withCaching_cache_le _ b blocks salt hsalt
  have hb := DeterministicSigning.query_caches b blocks salt hsalt
  simp only [saltedDigestAnswer, StateT.run_bind, mem_support_bind_iff] at hout
  obtain ⟨inner, hinner, hout⟩ := hout
  have hi := (hashAnswer_support (prims := prims) (.history history) cache inner hinner).1
  have ho := (hashAnswer_support (prims := prims) (.digest (List.ofFn salt.1) inner.1) inner.2 output hout).1
  rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hinner hout
  have hhistory := (randomOracle_support _ cache inner hinner).2.1
  have hdigest := (randomOracle_support _ inner.2 output hout).2.1
  exact ⟨hi.trans ho, hblocks, salt.1, inner.1, hb, ho hhistory, hdigest⟩

/-- The real fused operation keeps the complete-block invariant, so its law
can be applied repeatedly even when holders reuse a PRSS address. -/
theorem saltDigest_complete (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬KnownTo D.1 b.1) (history : List Bit)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) r
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (saltDigest b history)).run ((cache, streams), log))) :
    TreeSimHashSaltBlocksComplete r.2.1.2 := by
  rw [mem_support_iff_of_evalDist_eq (saltDigest_joint prims D b hidden history cache streams log complete),
    support_map] at hr
  obtain ⟨v, _, rfl⟩ := hr
  exact treeSimHash_salt_blocks_install streams complete b _

/-- A continuation receives exactly the real digest and reconstructed state.
Opacity of a public continuation still requires that it branch only on the
digest, not on the private state supplied to proof instrumentation. -/
theorem saltDigest_bind {α : Type} (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬KnownTo D.1 b.1) (history : List Bit)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams)
    (k : HashOutput × TreeSimState C → ProbComp α) :
    𝒟[(((simulateQ (treeSimLoggedWorld prims D) (saltDigest b history)).run
      ((cache, streams), log)) >>= k)] =
      𝒟[(opaqueDigest prims b history).run (cache, treeSimHashSaltLookup streams) >>=
        fun r => k (saltDigestDecode b history streams log r)] := by
  rw [evalDist_bind, saltDigest_joint prims D b hidden history cache streams log complete]
  simp only [← evalDist_bind, bind_map_left]

/-- Draw a fixed local pass of PRSS blocks before hashing any of its rows.
The block cache still identifies every repeated address. -/
def sampleRows (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    StateT (BlockCache C) ProbComp (List (List Bit × List Bit)) :=
  rows.mapM fun row => do
    let values ← (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle row.1
    pure (List.ofFn values, row.2)

def hashRows (prims : Primitives) (rows : List (List Bit × List Bit)) :
    StateT (HashCache C) ProbComp (List HashOutput) :=
  rows.mapM fun row => saltedDigestAnswer prims row.1 row.2

def opaqueRows (prims : Primitives) (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    StateT (HashCache C × BlockCache C) ProbComp (List HashOutput) :=
  rows.mapM fun row => opaqueDigest prims row.1 row.2

/-- Delaying each hidden block until its digest call preserves the complete
joint cache law. This is local reordering of independent state components,
not a premise asserting independence of adaptively chosen stages. -/
theorem opaqueRows_eager (prims : Primitives)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (cache : HashCache C) (blocks : BlockCache C) :
    𝒟[(opaqueRows prims rows).run (cache, blocks)] =
      𝒟[(do
        let salts ← (sampleRows rows).run blocks
        let result ← (hashRows prims salts.1).run cache
        pure (result.1, result.2, salts.2))] := by
  induction rows generalizing cache blocks with
  | nil => simp [opaqueRows, sampleRows, hashRows]
  | cons row rows ih =>
    simp only [opaqueRows, sampleRows, List.mapM_cons, StateT.run_bind,
      StateT.run_pure, opaqueDigest_run, bind_assoc, bind_map_left,
      pure_bind]
    apply evalDist_bind_congr'
    intro salt
    simp only [evalDist_bind]
    have htail : ∀ r : HashOutput × HashCache C,
        𝒟[(do
          let rest ← (opaqueRows prims rows).run (r.2, salt.2)
          pure (r.1 :: rest.1, rest.2))] =
        𝒟[(do
          let salts ← (sampleRows rows).run salt.2
          let rest ← (hashRows prims salts.1).run r.2
          pure (r.1 :: rest.1, rest.2, salts.2))] := by
      intro r
      rw [evalDist_bind, ih]
      simp only [← evalDist_bind, bind_assoc, pure_bind]
    simp only [← evalDist_bind]
    calc
      _ = 𝒟[(do
        let r ← (saltedDigestAnswer prims (List.ofFn salt.1) row.2).run cache
        let salts ← (sampleRows rows).run salt.2
        let rest ← (hashRows prims salts.1).run r.2
        pure (r.1 :: rest.1, rest.2, salts.2))] := by
          apply evalDist_bind_congr'
          intro r
          exact htail r
      _ = _ := by
        rw [evalDist_bind_bind_swap]
        simp only [hashRows, List.mapM_cons, StateT.run_bind, StateT.run_pure,
          bind_assoc, pure_bind]
        rfl

/-- The generic form of the cache-update proof in leanVM
`XmssSecurity/Proof/Bridge/Basic.lean`, `randomOracle_run_cache_eq`,
specialized here to the block oracle. -/
theorem block_result (b : TreeSimHashSaltBlock C) (blocks : BlockCache C)
    (r : (Fin 256 → Bit) × BlockCache C)
    (hr : r ∈ support (((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run blocks)) :
    r.2 = blocks.cacheQuery b r.1 := by
  cases hc : blocks b with
  | none =>
    rw [QueryImpl.withCaching_run_none _ hc, support_map, Set.mem_image] at hr
    obtain ⟨sampled, _, heq⟩ := hr
    cases heq
    rfl
  | some cached =>
    rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
    cases hr
    dsimp only
    funext candidate
    by_cases heq : candidate = b
    · subst candidate
      rw [QueryCache.cacheQuery_self, hc]
    · rw [QueryCache.cacheQuery_of_ne _ _ heq]

/-- The actual hidden term draws in their original order, without yet
evaluating the digest queries. -/
def realSampleRows (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    OracleComp (WorldSpec C) (List (List Bit × List Bit)) :=
  rows.mapM fun row => do
    let salt ← free (liftComp (prgBits (.term row.1.1) row.1.2.1 row.1.2.2 2 256) (LocalSpec C))
    pure (vector 256 salt, row.2)

/-- The actual hidden draw pass gives the same salts and final block cache
as `sampleRows`. Only this projection drops the original per-bit log; the
one-call theorem `saltDigest_read_joint` retains it exactly. -/
theorem realSampleRows_joint (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) :
    𝒟[(fun r => (r.1, treeSimHashSaltLookup r.2.1.2)) <$>
      (simulateQ (treeSimLoggedWorld prims D) (realSampleRows rows)).run ((cache, streams), log)] =
      𝒟[(sampleRows rows).run (treeSimHashSaltLookup streams)] := by
  induction rows generalizing cache streams log with
  | nil => simp [realSampleRows, sampleRows]
  | cons row rows ih =>
    simp only [realSampleRows, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure]
    rw [treeRawSalt_block_bind prims D row.1 (hidden row (by simp)) cache streams log complete]
    simp only [sampleRows, List.mapM_cons, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind]
    apply evalDist_bind_congr
    intro salt hsalt
    have hlookup : treeSimHashSaltLookup
        (cacheFin (treeSimHashSaltAddress row.1) salt.1 streams) = salt.2 := by
      rw [treeSimHash_salt_lookup_install, block_result row.1 _ salt hsalt]
    have htail := ih (fun r hr => hidden r (by simp [hr])) cache
      (cacheFin (treeSimHashSaltAddress row.1) salt.1 streams)
      (log ++ treeSimHiddenLog (treeSimHashSaltAddress row.1) salt.1)
      (treeSimHash_salt_blocks_install streams complete row.1 salt.1)
    rw [hlookup] at htail
    rw [vector_getD_ofFn]
    have hm := evalDist_map_eq_of_evalDist_eq htail
      (fun r => ((List.ofFn salt.1, row.2) :: r.1, r.2))
    unfold realSampleRows sampleRows at hm
    simpa only [← evalDist_map, Functor.map_map, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind] using hm

theorem realSampleRows_state (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) r
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (realSampleRows rows)).run ((cache, streams), log))) :
    r.2.1.1 = cache ∧ TreeSimHashSaltBlocksComplete r.2.1.2 := by
  induction rows generalizing cache streams log r with
  | nil =>
    simpa only [realSampleRows, List.mapM_nil, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] using hr ▸ (show cache = cache ∧ TreeSimHashSaltBlocksComplete streams from
        ⟨rfl, complete⟩)
  | cons row rows ih =>
    simp only [realSampleRows, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    obtain ⟨values, _, hcache, _, hcomplete, _, _⟩ := treeSimHash_salt_block_support
      prims D row.1 (hidden row (by simp)) cache streams log complete head hhead
    have hi := ih (fun r hr => hidden r (by simp [hr])) head.2.1.1 head.2.1.2 head.2.2 hcomplete tail htail
    exact ⟨hi.1.trans hcache, hi.2⟩

def realHashRows (rows : List (List Bit × List Bit)) : OracleComp (WorldSpec C) (List HashOutput) :=
  rows.mapM fun row => free (liftComp (oneDigestQuery (C := C) row.1 row.2) (LocalSpec C))

/-- A digest pass has the ordinary shared-hash execution and leaves the
private stream cache unchanged. This equality explicitly projects away logs. -/
theorem realHashRows_project (prims : Primitives) (D : C.Coalition)
    (rows : List (List Bit × List Bit)) (cache : HashCache C)
    (streams : HiddenCache C) (log : TreeSimLog C) :
    (fun r => (r.1, r.2.1.1, r.2.1.2)) <$>
      (simulateQ (treeSimLoggedWorld prims D) (realHashRows rows)).run ((cache, streams), log) =
      (fun r => (r.1, r.2, streams)) <$> (hashRows prims rows).run cache := by
  induction rows generalizing cache log with
  | nil => simp [realHashRows, hashRows]
  | cons row rows ih =>
    simp only [realHashRows, hashRows, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, map_bind, map_pure, oneDigest_logged, bind_map_left]
    apply bind_congr
    intro head
    have ht := congrArg (fun p => (fun r => (head.1 :: r.1, r.2)) <$> p)
      (ih head.2 (log ++ digestLog row.1 row.2 head.1 head.2))
    unfold realHashRows hashRows at ht
    simpa only [Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind] using ht

/-- The real order, all hidden draws followed by all digests, has the same
output and both final caches as opaque per-row calls. Every address can be
chosen at the start of this local pass from the preceding execution state. -/
theorem realRows_opaque (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) :
    𝒟[(fun r => (r.1, r.2.1.1, treeSimHashSaltLookup r.2.1.2)) <$>
      (simulateQ (treeSimLoggedWorld prims D)
        (realSampleRows rows >>= realHashRows)).run ((cache, streams), log)] =
      𝒟[(opaqueRows prims rows).run (cache, treeSimHashSaltLookup streams)] := by
  let k := fun r : List (List Bit × List Bit) × BlockCache C =>
    (fun out => (out.1, out.2, r.2)) <$> (hashRows prims r.1).run cache
  rw [opaqueRows_eager]
  change _ = 𝒟[(sampleRows rows).run (treeSimHashSaltLookup streams) >>= k]
  rw [evalDist_bind, ← realSampleRows_joint prims D rows hidden cache streams log complete,
    ← evalDist_bind, bind_map_left]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  apply evalDist_bind_congr
  intro r hr
  have hcache := (realSampleRows_state prims D rows hidden cache streams log complete r hr).1
  have hp := congrArg (fun p => (fun out => (out.1, out.2.1, treeSimHashSaltLookup out.2.2)) <$> p)
    (realHashRows_project prims D r.1 r.2.1.1 r.2.1.2 r.2.2)
  simp only [Functor.map_map, hcache] at hp
  have hstate : ((cache, r.2.1.2), r.2.2) = r.2 := by rw [← hcache]
  rw [hstate] at hp
  exact congrArg evalDist hp

/-- The ordinary interpreter of an opaque program, without its ghost lists. -/
def opaqueAnswer (prims : Primitives) :
    QueryImpl (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C)
      (StateT (HashCache C × BlockCache C) ProbComp)
  | .inl row => opaqueDigest prims row.1 row.2
  | .inr t => treeSimHashBlockCacheAnswer (localAnswer prims) (.inr t)

theorem read_step_erase (prims : Primitives)
    (t : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain)
    (used : List (List Bit) × List (List Bit)) (cache : HashCache C) (blocks : BlockCache C) :
    (fun r => (r.1.1, r.2)) <$>
      (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
        ((treeSimHashSaltRead t).run used)).run (cache, blocks) =
      (opaqueAnswer prims t).run (cache, blocks) := by
  cases t with
  | inl row => exact opaqueDigest_read prims row.1 row.2 cache blocks used
  | inr t =>
    simp only [treeSimHashSaltRead, opaqueAnswer, StateT.run_mk, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, Functor.map_map, Prod.mk.eta, id_map']

/-- The used-salt and public-guess lists never influence the caller, even for
an adaptive opaque program with arbitrary interleaved public queries. -/
theorem read_program_erase {α : Type} (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (used : List (List Bit) × List (List Bit)) (cache : HashCache C) (blocks : BlockCache C) :
    (fun r => (r.1.1, r.2)) <$>
      (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
        ((simulateQ treeSimHashSaltRead p).run used)).run (cache, blocks) =
      (simulateQ (opaqueAnswer prims) p).run (cache, blocks) := by
  induction p using OracleComp.inductionOn generalizing used cache blocks with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← read_step_erase prims t used cache blocks, bind_map_left]
    apply bind_congr
    intro r
    exact ih r.1.1 r.1.2 r.2.1 r.2.2

def rowProgram (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (List HashOutput) :=
  rows.mapM fun row => OracleComp.lift
    (OracleSpec.query (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inl row))

theorem rowProgram_run (prims : Primitives) (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    simulateQ (opaqueAnswer prims) (rowProgram rows) = opaqueRows prims rows := by
  simp only [rowProgram, simulateQ_list_mapM, simulateQ_spec_query, opaqueAnswer, opaqueRows]

theorem rowProgram_bound (rows : List (TreeSimHashSaltBlock C × List Bit))
    (charged : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    [DecidablePred charged] : IsQueryBoundP (rowProgram rows) charged rows.length := by
  induction rows with
  | nil => simp [rowProgram]
  | cons row rows ih =>
    simp only [rowProgram, List.mapM_cons, List.length_cons]
    rw [show rows.length + 1 = 1 + rows.length by omega]
    apply isQueryBoundP_bind (n := 1) (m := rows.length)
      (by simp [isQueryBoundP_query_iff])
    intro digest _
    change IsQueryBoundP (List.cons digest <$> rowProgram rows) charged rows.length
    simpa only [isQueryBoundP_map_iff] using ih

theorem rowProgram_private (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    IsQueryBoundP (rowProgram rows) TreeSimHashSaltPrivate rows.length :=
  rowProgram_bound rows TreeSimHashSaltPrivate

theorem rowProgram_charged (rows : List (TreeSimHashSaltBlock C × List Bit)) :
    IsQueryBoundP (rowProgram rows) treeSimHashSaltTableCharged rows.length :=
  rowProgram_bound rows treeSimHashSaltTableCharged

def blockValues (blocks : BlockCache C) (b : TreeSimHashSaltBlock C) : Fin 256 → Bit :=
  (blocks b).getD (fun _ => 0)

def blockRows (rows : List (TreeSimHashSaltBlock C × List Bit)) (blocks : BlockCache C) :
    List (List Bit × List Bit) :=
  rows.map fun row => (List.ofFn (blockValues blocks row.1), row.2)

theorem sampleRows_values (rows : List (TreeSimHashSaltBlock C × List Bit))
    (blocks : BlockCache C) r (hr : r ∈ support ((sampleRows rows).run blocks)) :
    blocks ≤ r.2 ∧ r.1 = blockRows rows r.2 := by
  induction rows generalizing blocks r with
  | nil =>
    simp only [sampleRows, List.mapM_nil, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨le_rfl, rfl⟩
  | cons row rows ih =>
    simp only [sampleRows, List.mapM_cons, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    have hheadLe := QueryImpl.withCaching_cache_le _ row.1 blocks head hhead
    have hheadAt := DeterministicSigning.query_caches row.1 blocks head hhead
    have hi := ih head.2 tail htail
    refine ⟨hheadLe.trans hi.1, ?_⟩
    have hvalues : blockValues tail.2 row.1 = head.1 := by
      unfold blockValues
      rw [hi.1 hheadAt]
      rfl
    change (List.ofFn head.1, row.2) :: tail.1 = _
    simp only [blockRows, List.map_cons, hvalues]
    exact congrArg (List.cons (List.ofFn head.1, row.2)) hi.2

theorem realSampleRows_values (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) r
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (realSampleRows rows)).run ((cache, streams), log))) :
    treeSimHashSaltLookup streams ≤ treeSimHashSaltLookup r.2.1.2 ∧
      r.1 = blockRows rows (treeSimHashSaltLookup r.2.1.2) := by
  apply sampleRows_values rows (treeSimHashSaltLookup streams) (r.1, treeSimHashSaltLookup r.2.1.2)
  rw [← mem_support_iff_of_evalDist_eq (realSampleRows_joint prims D rows hidden cache streams log complete),
    support_map]
  exact ⟨r, hr, rfl⟩

def sampleLog (rows : List (TreeSimHashSaltBlock C × List Bit)) (blocks : BlockCache C) : TreeSimLog C :=
  rows.flatMap fun row => treeSimHiddenLog (treeSimHashSaltAddress row.1) (blockValues blocks row.1)

/-- The complete per-bit log of the ordered draw pass is decoded from the
final block cache, with repeated addresses retaining the same values. -/
theorem realSampleRows_log (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) r
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (realSampleRows rows)).run ((cache, streams), log))) :
    r.2.2 = log ++ sampleLog rows (treeSimHashSaltLookup r.2.1.2) := by
  induction rows generalizing cache streams log r with
  | nil =>
    simp only [realSampleRows, List.mapM_nil, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hr
    subst r
    simp [sampleLog]
  | cons row rows ih =>
    simp only [realSampleRows, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    obtain ⟨values, _, _, hcached, hcomplete, hlog, _⟩ := treeSimHash_salt_block_support
      prims D row.1 (hidden row (by simp)) cache streams log complete head hhead
    have ht := ih (fun r hr => hidden r (by simp [hr])) head.2.1.1 head.2.1.2 head.2.2 hcomplete tail htail
    have hle := (realSampleRows_values prims D rows (fun r hr => hidden r (by simp [hr]))
      head.2.1.1 head.2.1.2 head.2.2 hcomplete tail htail).1
    have hvalues : blockValues (treeSimHashSaltLookup tail.2.1.2) row.1 = values := by
      unfold blockValues
      rw [hle (treeSimHash_salt_lookup_some _ row.1 values hcached)]
      rfl
    dsimp only
    rw [ht, hlog]
    simp only [sampleLog, List.flatMap_cons, hvalues, List.append_assoc]

theorem saltedDigest_cached (prims : Primitives) (salt history : List Bit)
    (cache : HashCache C) r
    (hr : r ∈ support ((saltedDigestAnswer prims salt history).run cache)) :
    cache ≤ r.2 ∧ ∃ h, r.2 (.history history) = some h := by
  simp only [saltedDigestAnswer, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨head, hhead, hr⟩ := hr
  have hfirst := (hashAnswer_support (prims := prims) (.history history) cache head hhead).1
  have hlast := (hashAnswer_support (prims := prims) (.digest salt head.1) head.2 r hr).1
  rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hhead
  exact ⟨hfirst.trans hlast, head.1, hlast (randomOracle_support _ cache head hhead).2.1⟩

def hashRowsLog (rows : List (List Bit × List Bit)) (digests : List HashOutput)
    (cache : HashCache C) : TreeSimLog C :=
  (rows.zip digests).flatMap fun row => digestLog row.1.1 row.1.2 row.2 cache

/-- Every history answer needed to decode the real digest pass survives in
the final cache, including when a later row reuses the history. -/
theorem realHashRows_log (prims : Primitives) (D : C.Coalition)
    (rows : List (List Bit × List Bit)) (cache : HashCache C)
    (streams : HiddenCache C) (log : TreeSimLog C) r
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (realHashRows rows)).run ((cache, streams), log))) :
    cache ≤ r.2.1.1 ∧ r.2.1.2 = streams ∧
      r.2.2 = log ++ hashRowsLog rows r.1 r.2.1.1 := by
  induction rows generalizing cache log r with
  | nil =>
    simp only [realHashRows, List.mapM_nil, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hr
    subst r
    exact ⟨le_rfl, rfl, by simp [hashRowsLog]⟩
  | cons row rows ih =>
    simp only [realHashRows, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, oneDigest_logged, bind_map_left,
      mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    obtain ⟨hle, h, hcached⟩ := saltedDigest_cached prims row.1 row.2 cache head hhead
    have hi := ih head.2 (log ++ digestLog row.1 row.2 head.1 head.2) tail htail
    refine ⟨hle.trans hi.1, hi.2.1, ?_⟩
    have hlog := digestLog_mono row.1 row.2 head.1 hi.1 h hcached
    dsimp only
    rw [hi.2.2, hlog]
    simp only [hashRowsLog, List.zip_cons_cons, List.flatMap_cons, List.append_assoc]

/-- The local pass decoder reads salts only after execution has finished. -/
def rowsDecode (rows : List (TreeSimHashSaltBlock C × List Bit)) (log : TreeSimLog C)
    (r : List HashOutput × HashCache C × BlockCache C) : List HashOutput × TreeSimLog C :=
  (r.1, (log ++ sampleLog rows r.2.2) ++ hashRowsLog (blockRows rows r.2.2) r.1 r.2.1)

/-- Complete real log normalization for a local hidden-term pass. This keeps
the original order of all draws before all hashes in the decoded transcript. -/
theorem realRows_fullLog (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) :
    𝒟[(fun r => (r.1, r.2.2)) <$>
      (simulateQ (treeSimLoggedWorld prims D)
        (realSampleRows rows >>= realHashRows)).run ((cache, streams), log)] =
      𝒟[rowsDecode rows log <$>
        (opaqueRows prims rows).run (cache, treeSimHashSaltLookup streams)] := by
  have hlaw := evalDist_map_eq_of_evalDist_eq
    (realRows_opaque prims D rows hidden cache streams log complete) (rowsDecode rows log)
  rw [Functor.map_map] at hlaw
  rw [← hlaw]
  apply congrArg evalDist
  simp only [map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro r hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨sampled, hsampled, hr⟩ := hr
  have hslog := realSampleRows_log prims D rows hidden cache streams log complete sampled hsampled
  have hsvalues := (realSampleRows_values prims D rows hidden cache streams log complete sampled hsampled).2
  have hhlog := realHashRows_log prims D sampled.1 sampled.2.1.1 sampled.2.1.2 sampled.2.2 r hr
  apply congrArg pure
  dsimp only [Function.comp_def, rowsDecode]
  congr 1
  rw [hhlog.2.1, hhlog.2.2, hslog, hsvalues]

/-- The retained-log row law uses the same opaque reader as the exact
ceremony target. The caller receives only digests; the decoder sees the final
private block cache. This is a local pass law, not a whole-ceremony compiler. -/
theorem realRows_read_fullLog (prims : Primitives) (D : C.Coalition)
    (rows : List (TreeSimHashSaltBlock C × List Bit))
    (hidden : ∀ row ∈ rows, ¬KnownTo D.1 row.1.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams)
    (used : List (List Bit) × List (List Bit)) :
    𝒟[(fun r => (r.1, r.2.2)) <$>
      (simulateQ (treeSimLoggedWorld prims D)
        (realSampleRows rows >>= realHashRows)).run ((cache, streams), log)] =
      𝒟[(fun r => rowsDecode rows log (r.1.1, r.2)) <$>
        (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
          ((simulateQ treeSimHashSaltRead (rowProgram rows)).run used)).run
            (cache, treeSimHashSaltLookup streams)] := by
  rw [realRows_fullLog prims D rows hidden cache streams log complete,
    ← rowProgram_run prims rows,
    ← read_program_erase prims (rowProgram rows) used cache (treeSimHashSaltLookup streams),
    Functor.map_map]

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCeremonyProof.saltDigest_read_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saltDigest_read_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCeremonyProof.realRows_opaque' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRows_opaque

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCeremonyProof.read_program_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms read_program_erase

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCeremonyProof.realRows_read_fullLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRows_read_fullLog

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCeremonyProof.rowProgram_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowProgram_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCeremonyProof.rowProgram_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowProgram_charged

end TreeRawSaltCeremonyProof
end ThresholdLeanXmssSecurity
