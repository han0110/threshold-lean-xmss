import ThresholdLeanXmssSecurity.Proof.TreeRawSaltCompile
import ThresholdLeanXmssSecurity.Proof.TreeKeyAimed

/-!
Address reconstruction for the opaque salt table.

Finite handles are assigned in order of first use. Decoding retains exactly the
allocated addresses; unused finite coordinates stay empty. The private-call
budget ensures that a new address never aliases an earlier handle. Repeated
addresses reuse the same block, without a salt-consistency assumption.

`allocate_program_joint` preserves the complete opaque experiment, including
its output, hash cache, block cache and both salt event lists. It applies to
adaptive addresses and continuations. `ceremonyBoundary` fixes the exact
whole-ceremony compiler, with the original order and abort behavior. Its
source makes no programming call; erasing only unreachable programming
requests also certifies the boundary syntax on every continuation.

`CeremonyOpaqueNormalization` asks for the mixed term/pair interpreter and its
full-state decoder at that fixed boundary program. It retains both original
budgets, H and q+H, and the original collision-guarded salt event. The theorem
`ceremonyRepresentation_of_opaque` composes this normalization with finite
allocation to give `TreeRawSaltCeremonyRepresentation` itself.

The pinned and current leanVM cache and simulation lemmas were searched. The
address allocator is specific to the threshold salt layout.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeRawSaltRepresentationProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

abbrev FiniteCache (H : ℕ) := (Fin (H + 1) →ₒ (Fin 256 → Bit)).QueryCache

/-- Unallocated coordinates have not been sampled. -/
def FreshTail (seen : List (TreeSimHashSaltBlock C)) {H : ℕ}
    (table : FiniteCache H) : Prop :=
  ∀ i, seen.length ≤ i.val → table i = none

/-- The decoder does not give unallocated addresses the next free coordinate. -/
def addressCache (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (table : FiniteCache H) : TreeRawSaltFlowProof.BlockCache C := fun b =>
  if b ∈ seen then table (treeSimHashSaltHandle H seen b) else none

theorem addressCache_at (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (table : FiniteCache H) (fresh : FreshTail seen table)
    (capacity : seen.length ≤ H) (b : TreeSimHashSaltBlock C) :
    addressCache H seen table b = table (treeSimHashSaltHandle H seen b) := by
  by_cases hb : b ∈ seen
  · simp [addressCache, hb]
  · rw [addressCache, if_neg hb]
    exact (fresh _ (by rw [treeSimHash_salt_handle_fresh H seen b hb capacity])).symm

theorem remember_mem (seen : List (TreeSimHashSaltBlock C))
    (b a : TreeSimHashSaltBlock C) :
    a ∈ treeSimHashSaltRemember seen b ↔ a ∈ seen ∨ a = b := by
  unfold treeSimHashSaltRemember
  split_ifs with hb <;> simp_all

theorem remember_handle (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (b a : TreeSimHashSaltBlock C) (ha : a ∈ seen ∨ a = b) :
    treeSimHashSaltHandle H (treeSimHashSaltRemember seen b) a =
      treeSimHashSaltHandle H seen a := by
  unfold treeSimHashSaltRemember
  split_ifs with hb
  · rfl
  · rcases ha with ha | rfl
    · exact treeSimHash_salt_handle_stable H seen [b] a ha
    · simp [treeSimHashSaltHandle, List.idxOf_append, hb]

theorem addressCache_update (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (table : FiniteCache H) (capacity : seen.length ≤ H)
    (b : TreeSimHashSaltBlock C) (values : Fin 256 → Bit) :
    addressCache H (treeSimHashSaltRemember seen b)
      (table.cacheQuery (treeSimHashSaltHandle H seen b) values) =
      (addressCache H seen table).cacheQuery b values := by
  funext a
  by_cases hab : a = b
  · subst a
    rw [QueryCache.cacheQuery_self]
    simp only [addressCache, remember_mem, or_true, if_true]
    rw [remember_handle H seen b b (Or.inr rfl), QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hab]
    by_cases ha : a ∈ seen
    · have hm : a ∈ treeSimHashSaltRemember seen b := (remember_mem seen b a).2 (Or.inl ha)
      simp only [addressCache, if_pos ha, if_pos hm]
      rw [remember_handle H seen b a (Or.inl ha)]
      exact QueryCache.cacheQuery_of_ne _ _ (fun he => hab
        (treeSimHash_salt_handle_injective H seen capacity a b ha he))
    · simp [addressCache, remember_mem, ha, hab]

theorem freshTail_update (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (table : FiniteCache H) (fresh : FreshTail seen table)
    (capacity : seen.length ≤ H) (b : TreeSimHashSaltBlock C)
    (values : Fin 256 → Bit) :
    FreshTail (treeSimHashSaltRemember seen b)
      (table.cacheQuery (treeSimHashSaltHandle H seen b) values) := by
  intro i hi
  have hlen : seen.length ≤ (treeSimHashSaltRemember seen b).length :=
    (treeSimHash_salt_remember_prefix seen b).length_le
  rw [QueryCache.cacheQuery_of_ne]
  · exact fresh i (hlen.trans hi)
  · intro he
    have hv := congrArg Fin.val he
    by_cases hb : b ∈ seen
    · have hlt : (treeSimHashSaltHandle H seen b).val < seen.length :=
        (Nat.min_le_left _ _).trans_lt (List.idxOf_lt_length_iff.mpr hb)
      omega
    · rw [treeSimHash_salt_handle_fresh H seen b hb capacity] at hv
      have hl : (treeSimHashSaltRemember seen b).length = seen.length + 1 := by
        simp [treeSimHashSaltRemember, hb]
      omega

/-- One actual lazy block read, including its whole cache, is reconstructed
from its finite handle. -/
theorem allocate_block_joint (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (table : FiniteCache H) (fresh : FreshTail seen table)
    (capacity : seen.length ≤ H) (b : TreeSimHashSaltBlock C) :
    ((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run
        (addressCache H seen table) =
      (fun r => (r.1, addressCache H (treeSimHashSaltRemember seen b) r.2)) <$>
        ((Fin (H + 1) →ₒ (Fin 256 → Bit)).randomOracle
          (treeSimHashSaltHandle H seen b)).run table := by
  have he := addressCache_at H seen table fresh capacity b
  cases hc : table (treeSimHashSaltHandle H seen b) with
  | none =>
    rw [QueryImpl.withCaching_run_none _ (he.trans hc),
      QueryImpl.withCaching_run_none _ hc, Functor.map_map]
    apply map_congr
    intro values
    rw [addressCache_update H seen table capacity]
  | some values =>
    have hb : b ∈ seen := by
      by_contra hn
      have ha : addressCache H seen table b = none := by simp [addressCache, hn]
      rw [ha, hc] at he
      cases he
    rw [QueryImpl.withCaching_run_some _ (he.trans hc),
      QueryImpl.withCaching_run_some _ hc, map_pure]
    simp only [treeSimHashSaltRemember, if_pos hb]

theorem allocate_block_freshTail (H : ℕ) (seen : List (TreeSimHashSaltBlock C))
    (table : FiniteCache H) (fresh : FreshTail seen table)
    (capacity : seen.length ≤ H) (b : TreeSimHashSaltBlock C)
    (r : (Fin 256 → Bit) × FiniteCache H)
    (hr : r ∈ support (((Fin (H + 1) →ₒ (Fin 256 → Bit)).randomOracle
      (treeSimHashSaltHandle H seen b)).run table)) :
    FreshTail (treeSimHashSaltRemember seen b) r.2 := by
  have he : r.2 = table.cacheQuery (treeSimHashSaltHandle H seen b) r.1 := by
    cases hc : table (treeSimHashSaltHandle H seen b) with
    | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map, Set.mem_image] at hr
      obtain ⟨sampled, _, heq⟩ := hr
      cases heq
      rfl
    | some cached =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
      cases hr
      dsimp only
      funext i
      by_cases hi : i = treeSimHashSaltHandle H seen b
      · subst i
        rw [QueryCache.cacheQuery_self, hc]
      · rw [QueryCache.cacheQuery_of_ne _ _ hi]
  rw [he]
  exact freshTail_update H seen table fresh capacity b r.1

abbrev SaltLists := List (List Bit) × List (List Bit)

abbrev TableOutcome (κ α : Type) :=
  (α × SaltLists) × HashCache C × (κ →ₒ (Fin 256 → Bit)).QueryCache

/-- The opaque reader before finite address allocation, retaining its two
event lists and both caches. -/
def tableRun {κ α : Type} [DecidableEq κ] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (used : SaltLists)
    (cache : HashCache C) (blocks : (κ →ₒ (Fin 256 → Bit)).QueryCache) :
    ProbComp (TableOutcome (C := C) κ α) :=
  (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
    ((simulateQ treeSimHashSaltRead p).run used)).run (cache, blocks)

theorem tableRun_bind {κ α β : Type} [DecidableEq κ] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α)
    (k : α → OracleComp (TreeSimHashSaltTableSpec κ C) β)
    (used : SaltLists) (cache : HashCache C)
    (blocks : (κ →ₒ (Fin 256 → Bit)).QueryCache) :
    tableRun prims (p >>= k) used cache blocks =
      (tableRun prims p used cache blocks >>= fun r =>
        tableRun prims (k r.1.1) r.1.2 r.2.1 r.2.2) := by
  simp only [tableRun, simulateQ_bind, StateT.run_bind]

theorem tableRun_private {κ : Type} [DecidableEq κ] (prims : Primitives)
    (b : κ) (history : List Bit) (used : SaltLists) (cache : HashCache C)
    (blocks : (κ →ₒ (Fin 256 → Bit)).QueryCache) :
    tableRun prims (OracleComp.lift (OracleSpec.query
      (spec := TreeSimHashSaltTableSpec κ C) (.inl (b, history)))) used cache blocks = (do
      let salt ← ((κ →ₒ (Fin 256 → Bit)).randomOracle b).run blocks
      (fun r => ((r.1, used.1 ++ [List.ofFn salt.1], used.2), r.2, salt.2)) <$>
        (saltedDigestAnswer prims (List.ofFn salt.1) history).run cache) := by
  simp only [tableRun, simulateQ_spec_query, treeSimHashSaltRead, StateT.run_mk,
    simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
    treeSimHashBlockCacheAnswer, bind_map_left, bind_pure_comp,
    saltedDigestAnswer, map_bind, Functor.map_map]
  rfl

theorem tableRun_public {κ : Type} [DecidableEq κ] (prims : Primitives)
    (t : (LocalSpec C).Domain) (used : SaltLists) (cache : HashCache C)
    (blocks : (κ →ₒ (Fin 256 → Bit)).QueryCache) :
    tableRun prims (OracleComp.lift (OracleSpec.query
      (spec := TreeSimHashSaltTableSpec κ C) (.inr t))) used cache blocks =
      (fun r => ((r.1, used.1, (digestSaltProjection t).toList ++ used.2), r.2, blocks)) <$>
        (localAnswer prims t).run cache := by
  simp only [tableRun, simulateQ_spec_query, treeSimHashSaltRead, StateT.run_mk,
    simulateQ_map, StateT.run_map, treeSimHashBlockCacheAnswer, Functor.map_map]

def allocatedRun {α : Type} (prims : Primitives) (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (seen : List (TreeSimHashSaltBlock C)) (used : SaltLists)
    (cache : HashCache C) (table : FiniteCache H) : ProbComp (TreeRawSaltOutcome C H α) :=
  tableRun prims ((simulateQ (treeSimHashSaltAllocate H) p).run seen) used cache table

theorem allocatedRun_bind {α β : Type} (prims : Primitives) (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (k : α → OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) β)
    (seen : List (TreeSimHashSaltBlock C)) (used : SaltLists)
    (cache : HashCache C) (table : FiniteCache H) :
    allocatedRun prims H (p >>= k) seen used cache table =
      (allocatedRun prims H p seen used cache table >>= fun r =>
        allocatedRun prims H (k r.1.1.1) r.1.1.2 r.1.2 r.2.1 r.2.2) := by
  simp only [allocatedRun, simulateQ_bind, StateT.run_bind, tableRun_bind]

theorem tableRun_map {κ α β : Type} [DecidableEq κ] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (f : α → β)
    (used : SaltLists) (cache : HashCache C)
    (blocks : (κ →ₒ (Fin 256 → Bit)).QueryCache) :
    tableRun prims (f <$> p) used cache blocks =
      (fun r => ((f r.1.1, r.1.2), r.2)) <$> tableRun prims p used cache blocks := by
  simp only [tableRun, simulateQ_map, StateT.run_map]

theorem allocatedRun_private (prims : Primitives) (H : ℕ)
    (b : TreeSimHashSaltBlock C) (history : List Bit)
    (seen : List (TreeSimHashSaltBlock C)) (used : SaltLists)
    (cache : HashCache C) (table : FiniteCache H) :
    allocatedRun prims H (OracleComp.lift (OracleSpec.query
      (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inl (b, history))))
      seen used cache table = (do
      let salt ← ((Fin (H + 1) →ₒ (Fin 256 → Bit)).randomOracle
        (treeSimHashSaltHandle H seen b)).run table
      (fun r => (((r.1, treeSimHashSaltRemember seen b),
        used.1 ++ [List.ofFn salt.1], used.2), r.2, salt.2)) <$>
        (saltedDigestAnswer prims (List.ofFn salt.1) history).run cache) := by
  simp only [allocatedRun, simulateQ_spec_query, treeSimHashSaltAllocate,
    StateT.run_mk, tableRun_map, tableRun_private, map_bind, Functor.map_map]

theorem allocatedRun_public (prims : Primitives) (H : ℕ)
    (t : (LocalSpec C).Domain) (seen : List (TreeSimHashSaltBlock C))
    (used : SaltLists) (cache : HashCache C) (table : FiniteCache H) :
    allocatedRun prims H (OracleComp.lift (OracleSpec.query
      (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inr t)))
      seen used cache table =
      (fun r => (((r.1, seen), used.1, (digestSaltProjection t).toList ++ used.2),
        r.2, table)) <$> (localAnswer prims t).run cache := by
  simp only [allocatedRun, simulateQ_spec_query, treeSimHashSaltAllocate,
    StateT.run_lift, bind_pure_comp, tableRun_map, tableRun_public, Functor.map_map]

def allocationDecode {α : Type} (H : ℕ) (r : TreeRawSaltOutcome C H α) :
    TableOutcome (C := C) (TreeSimHashSaltBlock C) α :=
  ((r.1.1.1, r.1.2), r.2.1, addressCache H r.1.1.2 r.2.2)

/-- Adaptive allocation preserves the complete opaque experiment. The same
decoder retains both ghost lists, the public cache and every allocated block. -/
theorem allocate_program_joint {α : Type} (prims : Primitives) (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (n : ℕ) (bound : IsQueryBoundP p TreeSimHashSaltPrivate n)
    (seen : List (TreeSimHashSaltBlock C)) (used : SaltLists)
    (cache : HashCache C) (table : FiniteCache H)
    (fresh : FreshTail seen table) (capacity : seen.length + n ≤ H) :
    tableRun prims p used cache (addressCache H seen table) =
      allocationDecode H <$> allocatedRun prims H p seen used cache table := by
  induction p using OracleComp.inductionOn generalizing n seen used cache table with
  | pure a =>
    simp only [tableRun, allocatedRun, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    rw [tableRun_bind, allocatedRun_bind, map_bind]
    rcases t with ⟨b, history⟩ | t
    · have positive : 1 ≤ n := bound.1.resolve_left (fun h => h trivial)
      have next : ∀ a, IsQueryBoundP (k a) TreeSimHashSaltPrivate (n - 1) := by
        simpa only [TreeSimHashSaltPrivate, if_true] using bound.2
      have cap : seen.length ≤ H := by omega
      have cap' : (treeSimHashSaltRemember seen b).length + (n - 1) ≤ H := by
        have := treeSimHash_salt_remember_length seen b
        omega
      rw [tableRun_private, allocatedRun_private,
        allocate_block_joint H seen table fresh cap b]
      simp only [bind_map_left, bind_assoc]
      apply bind_congr_of_forall_mem_support
      intro salt hsalt
      apply bind_congr_of_forall_mem_support
      intro hashed _
      exact ih hashed.1 (n - 1) (next hashed.1) (treeSimHashSaltRemember seen b)
        (used.1 ++ [List.ofFn salt.1], used.2) hashed.2 salt.2
        (allocate_block_freshTail H seen table fresh cap b salt hsalt) cap'
    · have next : ∀ a, IsQueryBoundP (k a) TreeSimHashSaltPrivate n := by
        simpa only [TreeSimHashSaltPrivate, if_false, Nat.sub_zero] using bound.2
      rw [tableRun_public, allocatedRun_public]
      simp only [bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro r _
      exact ih r.1 n (next r.1) seen
        (used.1, (digestSaltProjection t).toList ++ used.2) r.2 table fresh capacity

/-- Finite allocation of a bounded opaque program starts from the exact empty
state of `treeRawSaltRun`; there is no unused initial block or cache premise. -/
theorem allocate_program_empty {α : Type} (prims : Primitives) (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (bound : IsQueryBoundP p TreeSimHashSaltPrivate H) :
    tableRun prims p ([], []) ∅ ∅ = allocationDecode H <$> treeRawSaltRun prims H p := by
  have h := allocate_program_joint prims H p H bound [] ([], []) ∅ ∅
    (fun _ _ => rfl) (by simp)
  have he : addressCache H ([] : List (TreeSimHashSaltBlock C)) ∅ = ∅ := by
    funext b
    simp [addressCache]
  rw [he] at h
  exact h

variable {E : Type} [Field E] [Algebra Bit E]

set_option backward.isDefEq.respectTransparency true in
/-- Programming is absent from the original whole ceremony, including aborts
and its final adversary continuation. -/
theorem ceremony_noProgram (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (treeRealGame K circuits settings top tree D A x z Z) AimedProgramCall 0 := by
  letI : DecidableEq E := Classical.decEq E
  unfold treeRealGame distinguish realExecution executePhase startSteps
  apply qb0_bind
  · apply qb0_bind (aimed_noProgram_adversary _)
    intro state
    apply qb0_bind
    · apply isQueryBoundP_sequenceFin
      intro i
      split_ifs
      · simp
      · exact aimed_noProgram_free _
    · intro steps
      generalize ceremonyFuel circuits settings = fuel
      exact aimed_noProgram_rounds D A fuel state steps
  · intro r
    exact aimed_noProgram_adversary _

/-- Erase simulator programming at the source interface. -/
def dropPrograms : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C))
  | .inl (.inr _) => pure false
  | .inl (.inl t) => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t)))
  | .inr t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t))

theorem dropPrograms_eq {α : Type} (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p AimedProgramCall 0) : simulateQ dropPrograms p = p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have next : ∀ a, simulateQ dropPrograms (k a) = k a := fun a =>
      ih a (by simpa only [Nat.zero_sub, ite_self] using safe.2 a)
    simp only [simulateQ_bind, simulateQ_spec_query, next]
    rcases t with (t | t) | t
    · rfl
    · exact (safe.1.resolve_right (Nat.lt_irrefl 0) trivial).elim
    · rfl

def BoundaryProgramCall (D : C.Coalition) : (TreeRawSaltFlowProof.BoundarySpec D).Domain → Prop
  | .inl _ => False
  | .inr t => AimedProgramCall t.1

/-- Remove only simulator programming requests. Actual source runs have none,
but this also removes them from unreachable boundary continuations. -/
def boundaryDropPrograms (D : C.Coalition) :
    QueryImpl (TreeRawSaltFlowProof.BoundarySpec D)
      (OracleComp (TreeRawSaltFlowProof.BoundarySpec D))
  | .inl row => OracleComp.lift (OracleSpec.query (spec := TreeRawSaltFlowProof.BoundarySpec D) (.inl row))
  | .inr ⟨.inl (.inr _), _⟩ => pure false
  | .inr ⟨.inl (.inl t), safe⟩ => OracleComp.lift (OracleSpec.query (spec := TreeRawSaltFlowProof.BoundarySpec D) (.inr ⟨.inl (.inl t), safe⟩))
  | .inr ⟨.inr t, safe⟩ => OracleComp.lift (OracleSpec.query (spec := TreeRawSaltFlowProof.BoundarySpec D) (.inr ⟨.inr t, safe⟩))

omit [Field E] [Algebra Bit E] in
theorem boundaryDropPrograms_source (D : C.Coalition)
    (t : (TreeRawSaltFlowProof.BoundarySpec D).Domain) :
    simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D) (boundaryDropPrograms D t) =
      simulateQ dropPrograms (TreeRawSaltFlowProof.boundarySource (E := E) D t) := by
  rcases t with ⟨ctx, st⟩ | ⟨t, safe⟩
  · simp only [boundaryDropPrograms, simulateQ_spec_query, TreeRawSaltFlowProof.boundarySource]
    exact (dropPrograms_eq _ (aimed_noProgram_free _)).symm
  · rcases t with (t | t) | t <;>
      simp only [boundaryDropPrograms, TreeRawSaltFlowProof.boundarySource,
        simulateQ_spec_query, simulateQ_pure, dropPrograms]

omit [Field E] [Algebra Bit E] in
theorem boundaryDropPrograms_program {α : Type} (D : C.Coalition)
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α) :
    simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D)
      (simulateQ (boundaryDropPrograms D) p) =
      simulateQ dropPrograms (simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, boundaryDropPrograms_source, ih]

theorem boundaryDropPrograms_safe {α : Type} (D : C.Coalition)
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α) :
    IsQueryBoundP (simulateQ (boundaryDropPrograms D) p) (BoundaryProgramCall D) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    apply qb0_bind _ ih
    rcases t with row | ⟨t, safe⟩
    · simp [boundaryDropPrograms, isQueryBoundP_query_iff, BoundaryProgramCall]
    · rcases t with (t | t) | t <;>
        simp [boundaryDropPrograms, isQueryBoundP_query_iff, BoundaryProgramCall, AimedProgramCall]

/-- Fix the actual compiler witness once, so semantic and budget obligations
refer to the same ceremony program. -/
def ceremonyBoundary (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (TreeRawSaltFlowProof.BoundarySpec D) Bool := by
  classical
  letI : DecidableEq E := Classical.decEq E
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  exact simulateQ (boundaryDropPrograms D) (Subtype.val <$> Classical.choose
    (TreeRawSaltCompileProof.compiled_treeRealGame D K circuits settings top tree A x z Z))

theorem ceremonyBoundary_source (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D)
      (ceremonyBoundary K circuits settings top tree D A x z Z) =
      treeRealGame K circuits settings top tree D A x z Z := by
  classical
  letI : DecidableEq E := Classical.decEq E
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  unfold ceremonyBoundary
  rw [boundaryDropPrograms_program, simulateQ_map, Classical.choose_spec
    (TreeRawSaltCompileProof.compiled_treeRealGame D K circuits settings top tree A x z Z)]
  exact dropPrograms_eq _ (ceremony_noProgram K circuits settings top tree D A x z Z)

/-- The chosen boundary program has no programming request on any branch,
including responses that the real digest handler cannot produce. -/
theorem ceremonyBoundary_safe (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (ceremonyBoundary K circuits settings top tree D A x z Z)
      (BoundaryProgramCall D) 0 := boundaryDropPrograms_safe D _

theorem ceremonyBoundary_noProgram (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D)
      (ceremonyBoundary K circuits settings top tree D A x z Z)) AimedProgramCall 0 := by
  rw [ceremonyBoundary_source]
  exact ceremony_noProgram K circuits settings top tree D A x z Z

def boundaryRun (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) Bool) :
    ProbComp (Bool × TreeSimState C) :=
  (fun r => (r.1, TreeRawSaltFlowProof.decodeState r.2)) <$>
    (simulateQ (TreeRawSaltFlowProof.boundarySplit prims D) p).run (((∅, ∅), []), ∅)

theorem ceremonyBoundary_run (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (treeRealGame K circuits settings top tree D A x z Z)).run ((∅, ∅), [])] =
      𝒟[boundaryRun prims D (ceremonyBoundary K circuits settings top tree D A x z Z)] := by
  rw [← ceremonyBoundary_source K circuits settings top tree D A x z Z]
  exact TreeRawSaltFlowProof.decodeState_empty ▸
    TreeRawSaltFlowProof.boundary_program_joint (E := E) prims D _ (((∅, ∅), []), ∅)

def AddressHit {α : Type} (r : TableOutcome (C := C) (TreeSimHashSaltBlock C) α) : Prop :=
  ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2

/-- Mixed known/hidden/pair normalization at the fixed actual boundary
program. The decoder retains the entire state and original writer order.
The two bounds are the original fixed H and q+H; the guarded event is
tested on this same decoded execution. -/
def CeremonyOpaqueNormalization (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    let H := treeBatches settings tree * (C.t * termCount C)
    ∃ (α : Type) (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
      (decode : TableOutcome (C := C) (TreeSimHashSaltBlock C) α → Bool × TreeSimState C),
      IsQueryBoundP p TreeSimHashSaltPrivate H ∧
      IsQueryBoundP p treeSimHashSaltTableCharged (q + H) ∧
      𝒟[boundaryRun prims D (ceremonyBoundary K circuits settings top tree D A x z Z)] =
        𝒟[decode <$> tableRun prims p ([], []) ∅ ∅] ∧
      ∀ r ∈ support (tableRun prims p ([], []) ∅ ∅),
        ¬ TreeSimHashCollision (decode r).2.2 → TreeSimSaltGuess D (decode r).2.2 →
          AddressHit r

/-- Full-state opaque normalization, followed by the exact finite allocator,
gives the original quantitative ceremony representation. -/
theorem ceremonyRepresentation_of_opaque (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (normalization : CeremonyOpaqueNormalization prims K circuits settings) :
    TreeRawSaltCeremonyRepresentation prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  obtain ⟨α, p, decode, hprivate, charged, law, event⟩ :=
    normalization hb top tree D A x z Z q hx hq hsmall
  let H := treeBatches settings tree * (C.t * termCount C)
  let finalDecode : TreeRawSaltOutcome C H α → Bool × TreeSimLog C := fun r =>
    let d := decode (allocationDecode H r)
    (d.1, d.2.2)
  refine ⟨α, p, finalDecode, hprivate, charged, ?_, ?_⟩
  · rw [treeSimLoggedRun_eq_run]
    have full := (ceremonyBoundary_run prims K circuits settings top tree D A x z Z).trans law
    have logged := evalDist_map_eq_of_evalDist_eq full (fun r => (r.1, r.2.2))
    rw [allocate_program_empty prims H p hprivate] at logged
    simpa only [Functor.map_map, Function.comp_def, finalDecode] using logged
  · intro r hr collision guess
    have member : allocationDecode H r ∈ support (tableRun prims p ([], []) ∅ ∅) := by
      rw [allocate_program_empty prims H p hprivate, support_map]
      exact ⟨r, hr, rfl⟩
    exact event _ member collision guess

/-- The original salt estimate uses the same fixed budgets and guard after
the full-state mixed-boundary normalization. -/
theorem rawSaltEstimate_of_opaque (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (normalization : CeremonyOpaqueNormalization prims K circuits settings) :
    TreeSimHashRawSaltEstimate prims K circuits settings :=
  treeSimHashRawSaltEstimate_of_representation prims K circuits settings
    (ceremonyRepresentation_of_opaque prims K circuits settings normalization)

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.allocate_block_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allocate_block_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.allocate_program_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allocate_program_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.allocate_program_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allocate_program_empty

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.ceremony_noProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_noProgram

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.ceremonyBoundary_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyBoundary_source

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.ceremonyBoundary_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyBoundary_safe

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.ceremonyBoundary_noProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyBoundary_noProgram

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.ceremonyBoundary_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyBoundary_run

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.ceremonyRepresentation_of_opaque' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyRepresentation_of_opaque

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltRepresentationProof.rawSaltEstimate_of_opaque' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rawSaltEstimate_of_opaque

end TreeRawSaltRepresentationProof
end ThresholdLeanXmssSecurity
