import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Parts

/-!
# The digest table merged over the hash cache

`SaltTable` is a table of digests on pairs of a salt and a history hash. `mergeCache cache table`
takes a digest cell from `table` when the table has it, and each other cell from `cache`.
`fullHiddenSalts` is the set of the salts of the hidden places with all 256 cells.

`loggedWorld_merge` is the frame lemma of `loggedWorld` on the merged cache. `loggedWorld_grows` states
that the caches of `loggedWorld` only grow (`Grows`), and `fullHiddenSalts_mono` that the full hidden
salts only grow with them.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The salts of the places -/

/-- The 256 bits of the stream at the index 2 of the place `(name, key, ρ)` in a table of streams. -/
def placeSalt (cells : HiddenCache C) (name : KeyName C) (key : HashOutput) (ρ : ℕ) : List Bit :=
  (List.range 256).map fun position => (cells ((name, key), ρ, 2, position)).getD 0

/-- The salts of the hidden places with all 256 cells. -/
def fullHiddenSalts (D : C.Coalition) (hidden : HiddenCache C) : Set (List Bit) :=
  {salt | ∃ (T : C.Term) (key : HashOutput) (ρ : ℕ), ¬ KnownTo D.1 T ∧
    (∀ position < 256, hidden ((.term T, key), ρ, 2, position) ≠ none) ∧ salt = placeSalt hidden (.term T) key ρ}

/-! ## The merged cache -/

/-- The separate table of the digests, on pairs of a salt and a history hash. -/
abbrev SaltTable := ((List Bit × HashOutput) →ₒ HashOutput).QueryCache

variable (prims : Primitives)

/-- The hash cache with the separate table merged over its digest cells. -/
def mergeCache (cache : HashCache C) (table : SaltTable) : HashCache C :=
  QueryCache.ofFn fun q => match q with
    | .digest salt history => match table (salt, history) with
      | some v => some v
      | none => cache (.digest salt history)
    | q => cache q

/-- The separate table has no value at the cell `q`. -/
def CellFree (table : SaltTable) (q : Query C) : Prop :=
  ∀ salt history, q = .digest salt history → table (salt, history) = none

theorem mergeCache_of_free {table : SaltTable} {q : Query C} (h : CellFree table q) (cache : HashCache C) :
    mergeCache cache table q = cache q := by
  cases q with
  | digest salt history =>
    have ht := h salt history rfl
    simp [mergeCache, QueryCache.ofFn, ht]
  | _ => rfl

theorem mergeCache_digest (cache : HashCache C) (table : SaltTable) (salt : List Bit) (history : HashOutput)
    (v : HashOutput) (ht : table (salt, history) = some v) : mergeCache cache table (.digest salt history) = some v := by
  simp [mergeCache, QueryCache.ofFn, ht]

theorem mergeCache_cacheQuery_of_free {table : SaltTable} {q : Query C} (h : CellFree table q) (cache : HashCache C)
    (u : HashOutput) : mergeCache (cache.cacheQuery q u) table = (mergeCache cache table).cacheQuery q u := by
  refine QueryCache.ext fun q' => ?_
  by_cases hq : q' = q
  · subst hq
    rw [mergeCache_of_free h, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hq]
    cases q' with
    | digest salt history =>
      simp only [mergeCache, QueryCache.ofFn]
      cases table (salt, history) with
      | some v => rfl
      | none => exact QueryCache.cacheQuery_of_ne _ _ hq
    | _ => exact QueryCache.cacheQuery_of_ne _ _ hq

theorem mergeCache_cacheTable (cache : HashCache C) (table : SaltTable) (salt : List Bit) (history : HashOutput)
    (u : HashOutput) :
    mergeCache cache (table.cacheQuery (salt, history) u) = (mergeCache cache table).cacheQuery (.digest salt history) u := by
  refine QueryCache.ext fun q' => ?_
  by_cases hq : q' = .digest salt history
  · subst hq
    simp [mergeCache, QueryCache.ofFn]
  · rw [QueryCache.cacheQuery_of_ne _ _ hq]
    cases q' with
    | digest salt' history' =>
      have hne : (salt', history') ≠ (salt, history) := fun e => hq (by cases e; rfl)
      simp only [mergeCache, QueryCache.ofFn, QueryCache.cacheQuery_of_ne _ _ hne]
    | _ => rfl


theorem mergeCache_empty : mergeCache (∅ : HashCache C) (∅ : SaltTable) = ∅ := by
  refine QueryCache.ext fun q => ?_
  cases q <;> rfl

/-! ## The frame of `loggedWorld` on the merged cache -/

/-- The state of `loggedWorld` with the separate table merged over the hash cache. -/
def mergeLog (table : SaltTable) (st : LogState C) : LogState C := ((mergeCache st.1.1 table, st.1.2), st.2)

/-- The cell of the hash cache that a call of `H` or a programming call reads or writes. -/
def mainCell : (WorldSpec C).Domain → Option (Query C)
  | .inl (.inl (.inr (.inl q))) => some q
  | .inl (.inr p) => some p.1
  | .inr (.inr (.inl q)) => some q
  | _ => none

theorem randomOracle_merge {table : SaltTable} {q : Query C} (h : CellFree table q) (cache : HashCache C) :
    ((Query C →ₒ HashOutput).randomOracle q).run (mergeCache cache table) =
      (fun z => (z.1, mergeCache z.2 table)) <$> ((Query C →ₒ HashOutput).randomOracle q).run cache := by
  rw [randomOracle.run_eq, randomOracle.run_eq, mergeCache_of_free h]
  cases cache q with
  | some v => simp
  | none => simp [mergeCache_cacheQuery_of_free h]

theorem hashAnswer_merge {table : SaltTable} {q : Query C} (h : CellFree table q) (cache : HashCache C) :
    (hashAnswer prims q).run (mergeCache cache table) =
      (fun z => (z.1, mergeCache z.2 table)) <$> (hashAnswer prims q).run cache := by
  cases q with
  | hash input =>
    simp only [hashAnswer]
    split_ifs
    · simp
    · exact randomOracle_merge h cache
  | _ => exact randomOracle_merge h cache

theorem prgAnswer_merge (table : SaltTable) (x : PrgInput C) (cache : HashCache C) :
    (prgAnswer prims x).run (mergeCache cache table) =
      (fun z => (z.1, mergeCache z.2 table)) <$> (prgAnswer prims x).run cache := by
  have h : CellFree table (.streamKey x.2.1 : Query C) := fun _ _ e => by cases e
  simp only [prgAnswer, StateT.run_bind, hashAnswer_merge prims h, bind_map_left, map_bind]
  rfl

theorem programAnswer_merge {table : SaltTable} (x : Query C × HashOutput) (h : CellFree table x.1)
    (cache : HashCache C) :
    (programAnswer x).run (mergeCache cache table) =
      (fun z => (z.1, mergeCache z.2 table)) <$> (programAnswer x).run cache := by
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind, mergeCache_of_free h]
  split_ifs
  · simp
  · simp [mergeCache_cacheQuery_of_free h]


theorem localAnswer_merge (table : SaltTable) (t : (LocalSpec C).Domain)
    (h : ∀ q, t = .inr (.inl q) → CellFree table q) (cache : HashCache C) :
    (localAnswer prims t).run (mergeCache cache table) =
      (fun z => (z.1, mergeCache z.2 table)) <$> (localAnswer prims t).run cache := by
  rcases t with u | q | x
  · simp [localAnswer, unifFwdImpl]
  · exact hashAnswer_merge prims (h q rfl) cache
  · exact prgAnswer_merge prims table x cache

theorem localProgram_inl (t : (LocalSpec C).Domain) :
    (localAnswer (C := C) prims + programAnswer (C := C) : QueryImpl (SimulatorSpec C) (StateT (HashCache C) ProbComp))
      (Sum.inl t) = localAnswer prims t := rfl

theorem localProgram_inr (x : Query C × HashOutput) :
    (localAnswer (C := C) prims + programAnswer (C := C) : QueryImpl (SimulatorSpec C) (StateT (HashCache C) ProbComp))
      (Sum.inr x) = programAnswer x := rfl

/-- A call of the world whose cell of the hash cache has no value in the separate table runs on the
merged state as on the state, with the table merged over the end. -/
theorem loggedWorld_merge (D : C.Coalition) (table : SaltTable) (t : (WorldSpec C).Domain)
    (h : ∀ q, mainCell t = some q → CellFree table q) (st : LogState C) :
    (loggedWorld prims D t).run (mergeLog table st) =
      (fun z => (z.1, mergeLog table z.2)) <$> (loggedWorld prims D t).run st := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [loggedWorld, streamWorld, onHash, mergeLog, StateT.run_mk, Functor.map_map]
  · rw [localProgram_inl, localAnswer_merge prims table (Sum.inl u) (fun _ e => nomatch e), Functor.map_map]
    rfl
  · rw [localProgram_inl, localAnswer_merge prims table (Sum.inr (Sum.inl q)) (fun q' e => by
      cases e; exact h _ rfl), Functor.map_map]
    rfl
  · rw [localProgram_inl, localAnswer_merge prims table (Sum.inr (Sum.inr x)) (fun _ e => nomatch e),
      Functor.map_map]
    rfl
  · rw [localProgram_inr, programAnswer_merge p (h p.1 rfl), Functor.map_map]
    rfl
  · rw [localAnswer_merge prims table (Sum.inl u) (fun _ e => nomatch e), Functor.map_map]
    rfl
  · rw [localAnswer_merge prims table (Sum.inr (Sum.inl q)) (fun q' e => by cases e; exact h _ rfl),
      Functor.map_map]
    rfl
  · split_ifs
    · simp only [StateT.run_mk, Functor.map_map]
    · simp only [StateT.run_mk, Functor.map_map]
      rw [localAnswer_merge prims table (Sum.inr (Sum.inr x)) (fun _ e => nomatch e), Functor.map_map]
      rfl


/-! ## The caches only grow -/

/-- Each cell with a value in `c` has the same value in `c'`. -/
def Grows {ι : Type} {spec : OracleSpec ι} (c c' : spec.QueryCache) : Prop := ∀ t v, c t = some v → c' t = some v

theorem Grows.refl {ι : Type} {spec : OracleSpec ι} (c : spec.QueryCache) : Grows c c := fun _ _ h => h

theorem Grows.trans {ι : Type} {spec : OracleSpec ι} {c c' c'' : spec.QueryCache} (h : Grows c c')
    (h' : Grows c' c'') : Grows c c'' := fun t v hv => h' t v (h t v hv)

theorem grows_cacheQuery {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} (c : spec.QueryCache) (t : ι)
    (u : spec.Range t) (ht : c t = none) : Grows c (c.cacheQuery t u) := by
  intro t' v hv
  by_cases e : t' = t
  · subst e
    rw [ht] at hv
    cases hv
  · rw [QueryCache.cacheQuery_of_ne _ _ e]
    exact hv

/-- A call of a lazy random function grows its cache and sets the asked cell. -/
theorem randomOracle_grows {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] (t : ι) (c : spec.QueryCache) :
    ∀ z ∈ support ((spec.randomOracle t).run c), Grows c z.2 ∧ z.2 t ≠ none := by
  intro z hz
  rw [randomOracle.run_eq] at hz
  cases hc : c t with
  | some v =>
    rw [hc] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨Grows.refl c, by simp [hc]⟩
  | none =>
    rw [hc] at hz
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨u, _, rfl⟩ := hz
    exact ⟨grows_cacheQuery c t u hc, by simp⟩

theorem hashAnswer_grows (q : Query C) (c : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run c), Grows c z.2 := by
  intro z hz
  cases q with
  | hash input =>
    simp only [hashAnswer] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Grows.refl c
    · exact (randomOracle_grows _ c z hz).1
  | _ => exact (randomOracle_grows _ c z hz).1

theorem localAnswer_grows (t : (LocalSpec C).Domain) (c : HashCache C) :
    ∀ z ∈ support ((localAnswer prims t).run c), Grows c z.2 := by
  intro z hz
  rcases t with u | q | x
  · simp [localAnswer, unifFwdImpl] at hz
    obtain ⟨_, rfl⟩ := hz
    exact Grows.refl c
  · exact hashAnswer_grows prims q c z hz
  · simp only [localAnswer, QueryImpl.add_apply_inr, prgAnswer, StateT.run_bind, support_bind,
      Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hashAnswer_grows prims _ c w hw

theorem programAnswer_grows (x : Query C × HashOutput) (c : HashCache C) :
    ∀ z ∈ support ((programAnswer x).run c), Grows c z.2 ∧
      (c x.1 = none → (¬ ∃ input, x.1 = .hash input ∧ MpcInput input) → z.2 x.1 ≠ none) := by
  intro z hz
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hif
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨Grows.refl c, fun hn hm => ?_⟩
    rcases hif with hif | hif
    · exact absurd hif hm
    · rw [hn] at hif
      simp at hif
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    push Not at hif
    have hn : c x.1 = none := Option.not_isSome_iff_eq_none.mp (by simpa using hif.2)
    exact ⟨grows_cacheQuery c x.1 x.2 hn, fun _ _ => by simp⟩


theorem loggedWorld_grows (D : C.Coalition) (t : (WorldSpec C).Domain) (st : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run st), Grows st.1.1 z.2.1.1 ∧ Grows st.1.2 z.2.1.2 := by
  intro z hz
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hz
  all_goals try rw [localProgram_inl] at hz
  all_goals try rw [localProgram_inr] at hz
  · obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
    exact ⟨localAnswer_grows prims (Sum.inl u) _ w' hw', Grows.refl _⟩
  · obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
    exact ⟨localAnswer_grows prims (Sum.inr (Sum.inl q)) _ w' hw', Grows.refl _⟩
  · obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
    exact ⟨localAnswer_grows prims (Sum.inr (Sum.inr x)) _ w' hw', Grows.refl _⟩
  · obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
    exact ⟨(programAnswer_grows p _ w' hw').1, Grows.refl _⟩
  · obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
    exact ⟨localAnswer_grows prims (Sum.inl u) _ w' hw', Grows.refl _⟩
  · obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
    exact ⟨localAnswer_grows prims (Sum.inr (Sum.inl q)) _ w' hw', Grows.refl _⟩
  · split_ifs at hz
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
      exact ⟨Grows.refl _, (randomOracle_grows _ _ w' hw').1⟩
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hz
      exact ⟨localAnswer_grows prims (Sum.inr (Sum.inr x)) _ w' hw', Grows.refl _⟩

theorem placeSalt_of_grows {h h' : HiddenCache C} (hg : Grows h h') (name : KeyName C) (key : HashOutput) (ρ : ℕ)
    (hfull : ∀ position < 256, h ((name, key), ρ, 2, position) ≠ none) :
    placeSalt h' name key ρ = placeSalt h name key ρ := by
  unfold placeSalt
  refine List.map_congr_left fun position hp => ?_
  have hlt : position < 256 := List.mem_range.mp hp
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hfull position hlt)
  rw [hv, hg _ v hv]

theorem fullHiddenSalts_mono (D : C.Coalition) {h h' : HiddenCache C} (hg : Grows h h') :
    fullHiddenSalts D h ⊆ fullHiddenSalts D h' := by
  rintro salt ⟨T, key, ρ, hT, hfull, rfl⟩
  refine ⟨T, key, ρ, hT, fun position hp => ?_, (placeSalt_of_grows hg _ key ρ hfull).symm⟩
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hfull position hp)
  rw [hg _ v hv]
  simp

/-! ## The calls of `H` in `loggedWorld` -/

theorem loggedWorld_freeHash (D : C.Coalition) (q : Query C) (st : LogState C) :
    (loggedWorld prims D (.inr (.inr (.inl q)))).run st =
      (fun r => (r.1, ((r.2, st.1.2), st.2))) <$> (hashAnswer prims q).run st.1.1 := by
  simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, Functor.map_map]
  have hc : countedCells (C := C) (.inr (.inr (.inl q))) = [] := rfl
  rw [hc, List.append_nil]
  rfl

theorem loggedWorld_countedHash (D : C.Coalition) (q : Query C) (st : LogState C) :
    (loggedWorld prims D (.inl (.inl (.inr (.inl q))))).run st =
      (fun r => (r.1, ((r.2, st.1.2), st.2 ++ [q]))) <$> (hashAnswer prims q).run st.1.1 := by
  simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, Functor.map_map]
  rfl

theorem hashAnswer_digest (salt : List Bit) (history : HashOutput) :
    hashAnswer (C := C) prims (.digest salt history) = (Query C →ₒ HashOutput).randomOracle (.digest salt history) :=
  rfl

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.loggedWorld_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.loggedWorld_merge
