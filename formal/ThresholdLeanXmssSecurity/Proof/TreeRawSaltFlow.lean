import ThresholdLeanXmssSecurity.Proof.TreeRawSaltCeremony
import ThresholdLeanXmssSecurity.Proof.TreeSaltGuard

/-!
Salt blocks and the other stream reads in the actual ceremony.

The local laws cover the exact cache split and noninterference of other queries; absence
of salt reads in the actual index-zero/one PRSS traversals; the full joint
law of mixed known/hidden term and pair draws; the actual digest boundary
and its coroutine continuation; and adaptive boundary programs, with full
logs even on abort and arbitrary complete starting caches. Known streams
retain actual AES answers. Repeated addresses retain their cached block.

`TreeRawSaltCeremonyRepresentation` is a whole-program interface.
`CeremonyBoundaryProgram` names the syntactic salt-flow compiler:
the real ceremony must expand from complete digest boundaries and public
requests that cannot read hidden salt bits. The checked local boundary
and generic execution laws do not establish that whole-program premise.
The mixed boundary handler must then be compiled to the existing opaque
salt-table oracle, followed by its lazy address allocator, the fixed global
private/charged budgets, and event transport under `¬TreeSimHashCollision`.
The cache split is not an
independence assumption between ceremony stages, and these laws do not
prove `TreeSaltStagesPairsGuarded`.

The pinned and current leanVM proofs were searched. The address split is
specific to the threshold PRSS layout. The hidden-block law is reused from
`TreeRawSalt`, and no setup-fixed address cover is assumed.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeRawSaltFlowProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

abbrev BlockCache (C : Committee) := TreeRawSaltCeremonyProof.BlockCache C

/-- Only the 256 positions of a term at index two belong to a salt block. -/
def saltAt (x : HiddenAddress C) : Option (TreeSimHashSaltBlock C × Fin 256) :=
  match x with
  | ((.term T, key), label, idx, g) =>
      if h : idx = 2 ∧ g < 256 then some ((T, key, label), ⟨g, h.2⟩) else none
  | _ => none

theorem saltAt_address (b : TreeSimHashSaltBlock C) (g : Fin 256) :
    saltAt (treeSimHashSaltAddress b g) = some (b, g) := by
  rcases b with ⟨T, key, label⟩
  simp [saltAt, treeSimHashSaltAddress, g.isLt]

theorem saltAt_sound {x : HiddenAddress C} {b : TreeSimHashSaltBlock C} {g : Fin 256}
    (h : saltAt x = some (b, g)) : x = treeSimHashSaltAddress b g := by
  rcases x with ⟨⟨name, key⟩, label, idx, pos⟩
  cases name with
  | parameter => simp [saltAt] at h
  | pair p => simp [saltAt] at h
  | term T =>
    dsimp only [saltAt] at h
    split_ifs at h with hp
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp [treeSimHashSaltAddress, hp.1]

theorem saltAt_pair (p : C.Pair) (key : HashOutput) (label idx g : ℕ) :
    saltAt (((.pair p, key), label, idx, g) : HiddenAddress C) = none := rfl

theorem saltAt_other_index (name : KeyName C) (key : HashOutput) (label idx g : ℕ)
    (hne : idx ≠ 2) : saltAt (((name, key), label, idx, g) : HiddenAddress C) = none := by
  cases name <;> simp [saltAt, hne]

def restore (blocks : BlockCache C) (other : HiddenCache C) : HiddenCache C := fun x =>
  match saltAt x with
  | none => other x
  | some (b, g) => (blocks b).map fun values => values g

def erase (streams : HiddenCache C) : HiddenCache C := fun x =>
  if (saltAt x).isSome then none else streams x

theorem restore_address (blocks : BlockCache C) (other : HiddenCache C)
    (b : TreeSimHashSaltBlock C) (g : Fin 256) :
    restore blocks other (treeSimHashSaltAddress b g) = (blocks b).map (fun values => values g) := by
  simp [restore, saltAt_address]

theorem restore_lookup (blocks : BlockCache C) (other : HiddenCache C) :
    treeSimHashSaltLookup (restore blocks other) = blocks := by
  funext b
  simp only [treeSimHashSaltLookup, restore_address]
  cases blocks b <;> rfl

theorem restore_complete (blocks : BlockCache C) (other : HiddenCache C) :
    TreeSimHashSaltBlocksComplete (restore blocks other) := by
  intro b
  cases h : blocks b with
  | none => exact Or.inl (fun g => by simp [restore_address, h])
  | some values => exact Or.inr ⟨values, fun g => by simp [restore_address, h]⟩

/-- Splitting a complete real cache loses no entry, including unrelated
streams and blocks already read under another operator's shared key. -/
theorem restore_erase (streams : HiddenCache C) (complete : TreeSimHashSaltBlocksComplete streams) :
    restore (treeSimHashSaltLookup streams) (erase streams) = streams := by
  funext x
  cases h : saltAt x with
  | none => simp [restore, erase, h]
  | some bg =>
    rcases bg with ⟨b, g⟩
    have hx := saltAt_sound h
    subst x
    rw [restore_address]
    rcases complete b with fresh | ⟨values, cached⟩
    · rw [treeSimHash_salt_lookup_none streams b fresh, Option.map_none, fresh]
    · rw [treeSimHash_salt_lookup_some streams b values cached, Option.map_some, cached]

/-- A non-salt lazy read updates only the other part of the cache. -/
theorem restore_cache_other (blocks : BlockCache C) (other : HiddenCache C)
    (x : HiddenAddress C) (outside : saltAt x = none) (value : Bit) :
    restore blocks (other.cacheQuery x value) = (restore blocks other).cacheQuery x value := by
  funext y
  by_cases hy : y = x
  · subst y
    simp [restore, outside]
  · rw [QueryCache.cacheQuery_of_ne _ _ hy]
    cases h : saltAt y with
    | none => simp [restore, h, QueryCache.cacheQuery_of_ne _ _ hy]
    | some bg => simp [restore, h]

/-- Installing one opaque block changes exactly its 256 term positions. -/
theorem restore_cache_block (blocks : BlockCache C) (other : HiddenCache C)
    (b : TreeSimHashSaltBlock C) (values : Fin 256 → Bit) :
    restore (blocks.cacheQuery b values) other =
      cacheFin (treeSimHashSaltAddress b) values (restore blocks other) := by
  funext x
  cases h : saltAt x with
  | none =>
    rw [cacheFin_of_not_mem _ _ _ x (by
      intro g hg
      have := saltAt_address b g
      rw [← hg, h] at this
      cases this)]
    simp [restore, h]
  | some ag =>
    rcases ag with ⟨a, g⟩
    have hx := saltAt_sound h
    subst x
    by_cases hab : a = b
    · subst a
      rw [restore_address, QueryCache.cacheQuery_self,
        cacheFin_at _ (treeSimHash_salt_address_injective b)]
      rfl
    · rw [cacheFin_of_not_mem _ _ _ _ (by
        intro j hj
        exact hab (treeSimHash_salt_address_block hj))]
      rw [restore_address, restore_address, QueryCache.cacheQuery_of_ne _ _ hab]

/-- A public step may use a known salt stream: it reads AES, not the hidden
block cache. Only a hidden salt-bit read is excluded here. -/
def NoSaltRead (D : C.Coalition) (t : (WorldSpec C).Domain) : Prop :=
  match t with
  | .inr (.inr (.inr x)) => Hidden D x.1 → saltAt ((x.1, x.2.1), x.2.2) = none
  | _ => True

def restoreState (blocks : BlockCache C) (s : TreeSimState C) : TreeSimState C :=
  ((s.1.1, restore blocks s.1.2), s.2)

theorem randomOracle_restore (blocks : BlockCache C) (other : HiddenCache C)
    (x : HiddenAddress C) (outside : saltAt x = none) :
    (((HiddenAddress C →ₒ Bit).randomOracle x).run (restore blocks other)) =
      (fun r => (r.1, restore blocks r.2)) <$>
        (((HiddenAddress C →ₒ Bit).randomOracle x).run other) := by
  cases h : other x with
  | none =>
    rw [QueryImpl.withCaching_run_none _ h,
      QueryImpl.withCaching_run_none _ (by simpa only [restore, outside] using h)]
    simp only [Functor.map_map]
    apply map_congr
    intro v
    exact congrArg (Prod.mk v) (restore_cache_other blocks other x outside v).symm
  | some v =>
    rw [QueryImpl.withCaching_run_some _ h,
      QueryImpl.withCaching_run_some _ (by simpa only [restore, outside] using h), map_pure]

/-- Every other real query acts on the other cache component, with the
same answer and the same hash-cache update. This also covers programming. -/
theorem stream_query_restore (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : NoSaltRead D t)
    (hash : HashCache C) (other : HiddenCache C) (blocks : BlockCache C) :
    (streamWorld prims D t).run (hash, restore blocks other) =
      (fun r => (r.1, r.2.1, restore blocks r.2.2)) <$>
        (streamWorld prims D t).run (hash, other) := by
  rcases t with t | t
  · simp only [streamWorld, onHash, StateT.run_mk, Functor.map_map]
  rcases t with u | q | x
  · simp only [streamWorld, onHash, StateT.run_mk, Functor.map_map]
  · simp only [streamWorld, onHash, StateT.run_mk, Functor.map_map]
  · by_cases hidden : Hidden D x.1
    · simp only [streamWorld, if_pos hidden, StateT.run_mk]
      rw [randomOracle_restore blocks other _ (safe hidden)]
      simp only [Functor.map_map]
    · simp only [streamWorld, if_neg hidden, onHash, StateT.run_mk, Functor.map_map]

theorem logged_query_restore (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : NoSaltRead D t)
    (s : TreeSimState C) (blocks : BlockCache C) :
    (treeSimLoggedWorld prims D t).run (restoreState blocks s) =
      (fun r => (r.1, restoreState blocks r.2)) <$>
        (treeSimLoggedWorld prims D t).run s := by
  simp only [treeSimLoggedWorld, StateT.run_mk, restoreState,
    stream_query_restore prims D t safe s.1.1 s.1.2 blocks, Functor.map_map]

/-- Exact execution noninterference for a public segment, including its
full log and final caches. The source program is identical on both sides. -/
theorem program_restore {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p (fun t => ¬NoSaltRead D t) 0)
    (s : TreeSimState C) (blocks : BlockCache C) :
    (simulateQ (treeSimLoggedWorld prims D) p).run (restoreState blocks s) =
      (fun r => (r.1, restoreState blocks r.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D) p).run s := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : NoSaltRead D t := by simpa using safe.1
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      logged_query_restore prims D t ht s blocks, bind_map_left, map_bind]
    apply bind_congr
    intro r
    exact ih r.1 (by simpa using safe.2 r.1) r.2

/-- Lifting an ordinary oracle program preserves its forbidden-query bound. -/
theorem ro_noSalt {α : Type} (D : C.Coalition) (p : OracleComp (RoSpec C) α)
    (safe : IsQueryBoundP p (fun t => ¬NoSaltRead D (.inr (.inr t))) 0) :
    IsQueryBoundP (free (liftComp p (LocalSpec C))) (fun t => ¬NoSaltRead D t) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    rw [liftComp_bind, free_bind]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := WorldSpec C) (.inr (.inr t))) >>= _) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨safe.1, fun u => by simpa using ih u (by simpa using safe.2 u)⟩

/-- Known streams, pair streams, and term indices other than two do not read
the private salt table. No assumption about the AES primitive is used. -/
theorem prg_noSalt_ro (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (label idx count : ℕ)
    (safe : Hidden D name → ∀ g, saltAt ((name, key), label, idx, g) = none) :
    IsQueryBoundP (prgBits name key label idx count)
      (fun t => ¬NoSaltRead D (.inr (.inr t))) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => ¬NoSaltRead D (.inr (.inr t)))
    (fun g => (query (spec := RoSpec C) (.inr (name, key, label, idx, g)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun g _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, label, idx, g)))) _ 0
    rw [isQueryBoundP_query_iff]
    have hs : NoSaltRead D (.inr (.inr (.inr (name, key, label, idx, g)))) :=
      fun hidden => safe hidden g
    simp [hs]

theorem prg_noSalt (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (label idx count : ℕ)
    (safe : Hidden D name → ∀ g, saltAt ((name, key), label, idx, g) = none) :
    IsQueryBoundP (free (liftComp (prgBits name key label idx count) (LocalSpec C)))
      (fun t => ¬NoSaltRead D t) 0 :=
  ro_noSalt D _ (prg_noSalt_ro D name key label idx count safe)

/-- The intermediate machine separates complete salt blocks from the rest
of the real cache. It still returns raw bits; it is not an opaque caller. -/
abbrev SplitState (C : Committee) := TreeSimState C × BlockCache C

def decodeState (s : SplitState C) : TreeSimState C := restoreState s.2 s.1

def publicRun {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) : StateT (SplitState C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1, r.2, s.2)) <$>
    (simulateQ (treeSimLoggedWorld prims D) p).run s.1

def blockRun (b : TreeSimHashSaltBlock C) : StateT (SplitState C) ProbComp (ℕ → Bit) :=
  StateT.mk fun s => (fun r => ((fun g => (List.ofFn r.1).getD g 0),
    ((s.1.1, s.1.2 ++ treeSimHiddenLog (treeSimHashSaltAddress b) r.1), r.2))) <$>
      (((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run s.2)

theorem publicRun_joint {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p (fun t => ¬NoSaltRead D t) 0) (s : SplitState C) :
    (simulateQ (treeSimLoggedWorld prims D) p).run (decodeState s) =
      (fun r => (r.1, decodeState r.2)) <$> (publicRun prims D p).run s := by
  simpa only [decodeState, publicRun, StateT.run_mk, Functor.map_map] using
    program_restore prims D p safe s.1 s.2

theorem blockRun_joint (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬KnownTo D.1 b.1) (s : SplitState C) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C)))).run
        (decodeState s)] =
      𝒟[(fun r => (r.1, decodeState r.2)) <$> (blockRun b).run s] := by
  rw [decodeState, restoreState,
    treeRawSalt_block_joint prims D b hidden _ _ _ (restore_complete _ _), restore_lookup]
  simp only [blockRun, StateT.run_mk, Functor.map_map]
  apply congrArg evalDist
  simp only [map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro r hr
  apply congrArg pure
  change (_, (_, cacheFin _ _ (restore _ _)), _) = (_, (_, restore r.2 _), _)
  have cache := TreeRawSaltCeremonyProof.block_result b s.2 r hr
  -- The block handler retains exactly its lazy cache update.
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · rw [cache, restore_cache_block]
    · rfl

/-- Exact decoding relation, including all answers, all caches, and the log. -/
def RunLaw {α : Type} (real : StateT (TreeSimState C) ProbComp α)
    (split : StateT (SplitState C) ProbComp α) : Prop :=
  ∀ s, 𝒟[real.run (decodeState s)] =
    𝒟[(fun r => (r.1, decodeState r.2)) <$> split.run s]

theorem RunLaw.pure {α : Type} (a : α) :
    RunLaw (C := C) (pure a) (pure a) := by
  intro s
  simp

theorem RunLaw.bind {α β : Type} {p : StateT (TreeSimState C) ProbComp α}
    {q : StateT (SplitState C) ProbComp α}
    {f : α → StateT (TreeSimState C) ProbComp β}
    {g : α → StateT (SplitState C) ProbComp β}
    (first : RunLaw p q) (next : ∀ a, RunLaw (f a) (g a)) :
    RunLaw (p >>= f) (q >>= g) := by
  intro s
  simp only [StateT.run_bind]
  rw [evalDist_bind, first s, ← evalDist_bind, bind_map_left, map_bind]
  apply evalDist_bind_congr
  intro r _
  exact next r.1 r.2

theorem RunLaw.mapM {α β : Type} (xs : List α)
    (f : α → StateT (TreeSimState C) ProbComp β)
    (g : α → StateT (SplitState C) ProbComp β)
    (law : ∀ x ∈ xs, RunLaw (f x) (g x)) :
    RunLaw (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => simpa using RunLaw.pure (C := C) ([] : List β)
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact (law x (by simp)).bind fun y =>
      (ih (fun a ha => law a (by simp [ha]))).bind fun ys => RunLaw.pure (y :: ys)

/-- A real bit draw with term index two moved to its own lazy table when
hidden; known terms and every pair draw still use the actual handler. -/
def splitDraw (prims : Primitives) (D : C.Coalition) (name : KeyName C)
    (key : HashOutput) (label : ℕ) : StateT (SplitState C) ProbComp (ℕ → Bit) :=
  match name with
  | .term T => if KnownTo D.1 T then
      publicRun prims D (free (liftComp (prgBits name key label 2 256) (LocalSpec C)))
    else blockRun (T, key, label)
  | _ => publicRun prims D
      (free (liftComp (prgBits name key label 2 256) (LocalSpec C)))

theorem splitDraw_joint (prims : Primitives) (D : C.Coalition) (name : KeyName C)
    (key : HashOutput) (label : ℕ) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits name key label 2 256) (LocalSpec C))))
      (splitDraw prims D name key label) := by
  cases name with
  | term T =>
    by_cases known : KnownTo D.1 T
    · simp only [splitDraw, if_pos known]
      intro s
      rw [publicRun_joint prims D _ (prg_noSalt D (.term T) key label 2 256 (by
        intro hidden
        exact False.elim (hidden known)))]
    · simp only [splitDraw, if_neg known]
      exact blockRun_joint prims D (T, key, label) known
  | pair p =>
    intro s
    exact congrArg evalDist (publicRun_joint prims D _
      (prg_noSalt D (.pair p) key label 2 256 (fun _ g => saltAt_pair p key label 2 g)) s)
  | parameter =>
    intro s
    exact congrArg evalDist (publicRun_joint prims D _
      (prg_noSalt D .parameter key label 2 256 (fun _ _ => rfl)) s)

variable {E : Type} [Field E] [Algebra Bit E]

/-- The actual term and pair loops preserve the absence of forbidden reads. -/
theorem prss_noSalt {R : Type} [Zero R] (D : C.Coalition) (ctx : Context C)
    (codec : Codec C E R) (label idx count : ℕ)
    (safe : ∀ name key, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => ¬NoSaltRead D (.inr (.inr t))) 0) :
    IsQueryBoundP (free (liftComp (prssDraw ctx codec label idx count) (LocalSpec C)))
      (fun t => ¬NoSaltRead D t) 0 := by
  apply ro_noSalt
  unfold prssDraw
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => ?_)
  · unfold termDraws
    have h := queryBound_mapM (fun t => ¬NoSaltRead D (.inr (.inr t)))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => ?_)
    · simpa using h
    · split_ifs
      · exact safe _ _
      · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
    unfold pairDraws
    have h := queryBound_mapM (fun t => ¬NoSaltRead D (.inr (.inr t)))
      (fun j => if hj : j = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm hj))) (ctx.prss.pair j) label idx count)
      0 C.parties (fun j _ => ?_)
    · simpa using h
    · split_ifs
      · exact isQueryBoundP_pure _ _ _
      · exact safe _ _

theorem prssBits_noSalt (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (other : idx ≠ 2) :
    IsQueryBoundP (free (liftComp (prssDraw ctx (bitCodec (E := E)) label idx count) (LocalSpec C)))
      (fun t => ¬NoSaltRead D t) 0 :=
  prss_noSalt D ctx _ label idx count (fun name key =>
    prg_noSalt_ro D name key label idx count (fun _ g => saltAt_other_index name key label idx g other))

/-- The index-zero masking/rerandomization draws and index-one field draws
of the real gadgets never address a private salt position. -/
theorem prssElements_noSalt (K : Constants C E) (D : C.Coalition)
    (ctx : Context C) (label idx count : ℕ) (other : idx ≠ 2) :
    IsQueryBoundP (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))
      (fun t => ¬NoSaltRead D t) 0 := by
  apply prss_noSalt
  intro name key
  dsimp only [elementCodec]
  exact isQueryBoundP_bind (m := 0)
    (prg_noSalt_ro D name key label idx (elementBits * count)
      (fun _ g => saltAt_other_index name key label idx g other))
    (fun _ _ => isQueryBoundP_pure _ _ _)

def splitTerms (prims : Primitives) (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    StateT (SplitState C) ProbComp (List (ℕ → Bit)) :=
  C.terms.mapM fun T => if ctx.self ∈ C.holders T then
    splitDraw prims D (.term T) (ctx.prss.term T) label else pure fun _ => 0

def splitPairs (prims : Primitives) (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    StateT (SplitState C) ProbComp (List (ℕ → Bit)) :=
  C.parties.mapM fun j => if h : j = ctx.self then pure fun _ => 0
    else splitDraw prims D (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label

def splitPrss (prims : Primitives) (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    StateT (SplitState C) ProbComp (PrssOutput C Bit) := do
  let terms ← splitTerms prims D ctx label
  let pairs ← splitPairs prims D ctx label
  pure (fun T => terms.getD (C.terms.idxOf T) fun _ => 0,
    fun j => pairs.getD j.val fun _ => 0)

theorem splitTerms_joint (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (termDraws ctx (bitCodec (E := E)) label 2 256) (LocalSpec C))))
      (splitTerms prims D ctx label) := by
  unfold termDraws splitTerms
  rw [treeSimHash_mapM_ro]
  apply RunLaw.mapM
  intro T _
  by_cases held : ctx.self ∈ C.holders T
  · simpa only [if_pos held, bitCodec] using splitDraw_joint prims D (.term T) (ctx.prss.term T) label
  · simpa only [if_neg held, liftComp_pure, free_pure, simulateQ_pure] using
      RunLaw.pure (C := C) (fun _ : ℕ => (0 : Bit))

theorem splitPairs_joint (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (pairDraws ctx (bitCodec (E := E)) label 2 256) (LocalSpec C))))
      (splitPairs prims D ctx label) := by
  unfold pairDraws splitPairs
  rw [treeSimHash_mapM_ro]
  apply RunLaw.mapM
  intro j _
  by_cases hj : j = ctx.self
  · simpa only [dif_pos hj, liftComp_pure, free_pure, simulateQ_pure] using
      RunLaw.pure (C := C) (fun _ : ℕ => (0 : Bit))
  · simpa only [dif_neg hj, bitCodec] using
      splitDraw_joint prims D (.pair (C.pairOf ctx.self j (Ne.symm hj))) (ctx.prss.pair j) label

/-- The actual mixed term/pair sampling traversal, retaining its original
per-bit log and both caches. Known terms are evaluated by real AES. -/
theorem splitPrss_joint (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) label 2 256) (LocalSpec C))))
      (splitPrss prims D ctx label) := by
  simp only [prssDraw, splitPrss, liftComp_bind, liftComp_pure, free_bind, free_pure,
    simulateQ_bind, simulateQ_pure]
  exact (splitTerms_joint (E := E) prims D ctx label).bind fun terms =>
    (splitPairs_joint (E := E) prims D ctx label).bind fun pairs => RunLaw.pure _

theorem hash_noSalt_ro (D : C.Coalition) (q : Query C) :
    IsQueryBoundP (hashQuery q) (fun t => ¬NoSaltRead D (.inr (.inr t))) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [NoSaltRead]

theorem digest_noSalt (D : C.Coalition) (i : C.Party)
    (salts : Shares C Bit) (history : C.Term → List Bit) :
    IsQueryBoundP (free (liftComp (digestQuery i salts history) (LocalSpec C)))
      (fun t => ¬NoSaltRead D t) 0 := by
  apply ro_noSalt
  unfold digestQuery
  have h := queryBound_mapM (fun t => ¬NoSaltRead D (.inr (.inr t)))
    (fun T => if i ∈ C.holders T then do
      hashQuery (.digest (vector 256 (salts T)) (← hashQuery (.history (history T))))
      else pure 0) 0 C.terms (fun T _ => ?_)
  · simpa using h
  · split_ifs
    · exact isQueryBoundP_bind (hash_noSalt_ro D _) (fun _ _ => hash_noSalt_ro D _)
    · exact isQueryBoundP_pure _ _ _

/-- This private handler consumes the intermediate raw bits inside the
actual digest pass. Its only response to the caller is the digest list. -/
def splitDigest (prims : Primitives) (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    StateT (SplitState C) ProbComp (List HashOutput) := do
  let rnd ← splitPrss prims D ctx st.label
  publicRun prims D (free (liftComp (digestQuery ctx.self rnd.1 st.history) (LocalSpec C)))

/-- Full execution law for the actual mixed draw/digest pass. -/
theorem splitDigest_joint (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st) (LocalSpec C))))
      (splitDigest prims D ctx st) := by
  simp only [treeSimHashSaltDigestDraw, splitDigest, liftComp_bind, free_bind, simulateQ_bind]
  apply (splitPrss_joint (E := E) prims D ctx st.label).bind
  intro rnd s
  exact congrArg evalDist (publicRun_joint prims D _
    (digest_noSalt D ctx.self rnd.1 st.history) s)

/-- The actual coroutine boundary captures only the digest response. It
does not retain the raw PRSS term or pair outputs in its continuation. -/
theorem salt_digest_entry_joint (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) {α : Type} (ctx : Context C) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α) (s : SplitState C) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.honest (advance ((((prssRandomness ctx bitCodec 2 256 >>= fun rnd =>
        compareDigests ctx rnd.1).run st >>= k).run))))).run (decodeState s)] =
      𝒟[(fun r => (treeSimCheckStep K (.digests (fun _ => r.1)) ctx.self
        (k ((), nextLabel st)), decodeState r.2)) <$> (splitDigest prims D ctx st).run s] := by
  rw [treeSimHash_salt_digest_entry K ctx st k, simulateQ_map, StateT.run_map]
  have law := evalDist_map_eq_of_evalDist_eq (splitDigest_joint (E := E) prims D ctx st s)
    (fun r => (treeSimCheckStep K (.digests (fun _ => r.1)) ctx.self (k ((), nextLabel st)), r.2))
  simpa only [Functor.map_map] using law

/-- Public requests cannot access hidden salt bits. A private request is a
whole real digest boundary, with a digest list as its response type. -/
abbrev BoundarySpec (D : C.Coalition) :=
  ((Context C × RunState C) →ₒ List HashOutput) +
    OracleSpec.ofFn (fun t : {t : (WorldSpec C).Domain // NoSaltRead D t} => (WorldSpec C).Range t.1)

def boundarySource (D : C.Coalition) :
    QueryImpl (BoundarySpec D) (OracleComp (WorldSpec C))
  | .inl (ctx, st) => free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st) (LocalSpec C))
  | .inr t => OracleComp.lift (OracleSpec.query t.1)

def boundarySplit (prims : Primitives) (D : C.Coalition) :
    QueryImpl (BoundarySpec D) (StateT (SplitState C) ProbComp)
  | .inl (ctx, st) => splitDigest prims D ctx st
  | .inr t => StateT.mk fun s => (fun r => (r.1, r.2, s.2)) <$>
      (treeSimLoggedWorld prims D t.1).run s.1

theorem boundary_query_joint (prims : Primitives) (D : C.Coalition)
    (t : (BoundarySpec D).Domain) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D) (boundarySource (E := E) D t))
      (boundarySplit prims D t) := by
  rcases t with ⟨ctx, st⟩ | ⟨t, ht⟩
  · exact splitDigest_joint (E := E) prims D ctx st
  · intro s
    simp only [boundarySource, simulateQ_spec_query]
    change 𝒟[(treeSimLoggedWorld prims D t).run (restoreState s.2 s.1)] = _
    rw [logged_query_restore prims D t ht s.1 s.2]
    simp only [boundarySplit, StateT.run_mk, Functor.map_map, decodeState]

/-- Arbitrarily adaptive digest-boundary programs, including programs that
return an abort, preserve the full real transcript and caches. This is an
execution theorem for the displayed syntax, not an assertion that the
whole ceremony has already been compiled to that syntax. -/
theorem boundary_program_joint {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (BoundarySpec D) α) :
    RunLaw (simulateQ (treeSimLoggedWorld prims D) (simulateQ (boundarySource (E := E) D) p))
      (simulateQ (boundarySplit prims D) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using RunLaw.pure (C := C) a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (boundary_query_joint (E := E) prims D t).bind ih

/-- Split an existing complete state, without discarding any cached value
or imposing a probabilistic independence condition on its contents. -/
def encodeState (s : TreeSimState C) : SplitState C :=
  (((s.1.1, erase s.1.2), s.2), treeSimHashSaltLookup s.1.2)

theorem decode_encode (s : TreeSimState C) (complete : TreeSimHashSaltBlocksComplete s.1.2) :
    decodeState (encodeState s) = s := by
  simp only [decodeState, encodeState, restoreState, restore_erase s.1.2 complete]

theorem boundary_program_from {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (BoundarySpec D) α) (s : TreeSimState C)
    (complete : TreeSimHashSaltBlocksComplete s.1.2) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D) (simulateQ (boundarySource (E := E) D) p)).run s] =
      𝒟[(fun r => (r.1, decodeState r.2)) <$>
        (simulateQ (boundarySplit prims D) p).run (encodeState s)] := by
  simpa only [decode_encode s complete] using
    boundary_program_joint (E := E) prims D p (encodeState s)

theorem decodeState_empty :
    decodeState (((∅, ∅), []), (∅ : BlockCache C)) = ((∅, ∅), []) := by
  change ((∅, restore ∅ ∅), []) = ((∅, ∅), [])
  congr 2
  funext x
  cases h : saltAt x <;> simp [restore, h]

/-- The exact original writer-log output, also for a run that returns an
abort. No successful-run restriction or transcript projection is added. -/
theorem boundary_program_logged {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (BoundarySpec D) α) :
    𝒟[treeSimLoggedRun prims D (simulateQ (boundarySource (E := E) D) p)] =
      𝒟[(fun r => (r.1, r.2.1.2)) <$>
        (simulateQ (boundarySplit prims D) p).run (((∅, ∅), []), ∅)] := by
  rw [treeSimLoggedRun_eq_run]
  have law := boundary_program_joint (E := E) prims D p (((∅, ∅), []), ∅)
  rw [decodeState_empty] at law
  have mapped := evalDist_map_eq_of_evalDist_eq law (fun r => (r.1, r.2.2))
  simpa only [Functor.map_map, Function.comp_def, decodeState, restoreState] using mapped

/-- The unproved syntactic salt-flow step: factor every actual ceremony
read through the displayed digest boundaries and the safe public syntax.
This is a sufficient compiler target, not the quantitative representation.
The latter remains exactly `TreeRawSaltCeremonyRepresentation`. -/
def CeremonyBoundaryProgram (K : Constants C E) (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∃ p : OracleComp (BoundarySpec D) Bool,
      simulateQ (boundarySource (E := E) D) p = treeRealGame K circuits settings top tree D A x z Z

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFlowProof.program_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program_restore

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFlowProof.prssElements_noSalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prssElements_noSalt

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFlowProof.splitPrss_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitPrss_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFlowProof.salt_digest_entry_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms salt_digest_entry_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFlowProof.boundary_program_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_program_from

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltFlowProof.boundary_program_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_program_logged

end TreeRawSaltFlowProof
end ThresholdLeanXmssSecurity
