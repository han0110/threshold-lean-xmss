import ThresholdLeanXmssSecurity.Proof.TreeSimHash

/-!
# The hash bound of the tree simulation hop

`treeSimHashBoundFinal` gives `TreeSimHashBoundGoal` from two hypotheses, the honest count
`TreeSimHashHonestBudget` and the salt estimate `TreeSimHashRawSaltEstimate`.
`treeSimHash_terminal_of_honest` reduces the final-cache count to the honest count. Each
budget-region key of the final cache has an answer in the log, and at most `q` counted calls
are in the log.

A paper argument supports the honest count, per batch. Write `T` for `termCount C` and `m` for
the halvings. It uses two facts of the scheme. `reshare` gives zero shares outside the held
terms, and the honest operators agree on the tag and the label of each coin key.

* A batch with a surviving digest receiver uses `2 T` digest points, `n T + 1` copy points and
  `m + 2` coin keys. The allowance is `(n + 3) T + m + 2`.
* A batch where every honest receiver aborts at the digests uses `(n + 1) T` digest points and
  `m + 1` coin keys, and opens nothing.
* If one honest receiver survives the digests, all honest holder digests agree, so the batch
  pays as the first case.
* The setup uses at most `3 n ^ 2` commit and echo points (`treeSimHash_setup_capacity`).

A paper argument supports the salt estimate. Only `randBits` reads index `2` of a stream, and
its bits go only into `digest` queries.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The final-cache count splits into the counted points and the honest points. -/
theorem treeSimHash_cache_bound_of_cover (cache : HashCache C) (counted honest : Finset (Query C))
    (q R : ℕ) (hcounted : counted.card ≤ q) (hhonest : honest.card ≤ R)
    (cover : ∀ t, TreeSimHashBudgetDomain t → cache t ≠ none → t ∈ counted ∨ t ∈ honest) :
    SplitCacheBound (splitRegionCache TreeSimHashBudgetDomain cache) (q + R) := by
  refine ⟨counted ∪ honest, (Finset.card_union_le _ _).trans (Nat.add_le_add hcounted hhonest), ?_⟩
  intro t ht
  simp only [splitRegionCache] at ht
  split_ifs at ht with hd
  · exact Finset.mem_union.mpr (cover t hd ht)
  · exact absurd rfl ht

/-- A local call adds at most its own random-oracle input to the hash cache. -/
theorem treeSimHash_local_new_key (t : (LocalSpec C).Domain) (cache : HashCache C)
    (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) (q : Query C) (hq : r.2 q ≠ none) :
    cache q ≠ none ∨ splitLocalHashInput t = some q := by
  rcases hs : splitLocalHashInput t with _ | q'
  · obtain ⟨p, hp⟩ := splitLocalHashInput_none prims t hs
    rw [hp] at hr
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    exact Or.inl hq
  · obtain ⟨f, hf⟩ := splitLocalHashInput_some prims t q' hs
    rw [hf, StateT.run_map, support_map] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    have h := randomOracle_support q' cache u hu
    by_cases he : q = q'
    · exact Or.inr (congrArg some he.symm)
    · exact Or.inl (by simpa only [h.2.2 q he] using hq)

/-- Every budget-region key of the hash cache has an answer in the log. -/
def TreeSimHashFootprint (cache : HashCache C) (log : TreeSimLog C) : Prop :=
  ∀ q, TreeSimHashBudgetDomain q → cache q ≠ none → ∃ h, TreeSimHashAnswer log q h

theorem TreeSimHashFootprint.append {cache : HashCache C} {a : TreeSimLog C}
    (h : TreeSimHashFootprint cache a) (b : TreeSimLog C) :
    TreeSimHashFootprint cache (a ++ b) := by
  intro q hq hc
  obtain ⟨u, hu⟩ := h q hq hc
  exact ⟨u, hu.imp (fun hm => List.mem_append_left b hm) (fun hm => List.mem_append_left b hm)⟩

/-- One actual call keeps the footprint, with the call appended to the log. -/
theorem treeSimHash_footprint_step (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) (cache : HashCache C × HiddenCache C)
    (log : TreeSimLog C) (hc : TreeSimHashFootprint cache.1 log)
    (r : (LocalSpec C + LocalSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimLocalWorld t)).run cache)) :
    TreeSimHashFootprint r.2.1 (log ++ treeSimLocalLog t r.1) := by
  rcases t with (t | t | t) | (t | t | t)
  case inr.inr.inr =>
    by_cases hx : Hidden D t.1
    · simp [treeSimLocalWorld, streamWorld, hx] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      exact hc.append _
    · simp [treeSimLocalWorld, streamWorld, onHash, hx] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      intro q' hq' hc'
      rcases treeSimHash_local_new_key prims (.inr (.inr t)) cache.1 _ hu q' hc' with h | h
      · exact (hc.append _) q' hq' h
      · simp only [splitLocalHashInput, Option.some.injEq] at h
        subst h
        exact absurd hq' (treeSimHash_budget_excludes_paid .keygen .term [] t.2.1).2
  all_goals
    simp [treeSimLocalWorld, streamWorld, onHash] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    intro q' hq' hc'
  case inl.inl | inr.inl =>
    rcases treeSimHash_local_new_key prims (.inl t) cache.1 u hu q' hc' with h | h
    · exact (hc.append _) q' hq' h
    · simp only [splitLocalHashInput, reduceCtorEq] at h
  case inl.inr.inl | inr.inr.inl =>
    rcases treeSimHash_local_new_key prims (.inr (.inl t)) cache.1 u hu q' hc' with h | h
    · exact (hc.append _) q' hq' h
    · simp only [splitLocalHashInput] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨u.1, by simp [TreeSimHashAnswer, treeSimLocalLog]⟩
  case inl.inr.inr =>
    rcases treeSimHash_local_new_key prims (.inr (.inr t)) cache.1 u hu q' hc' with h | h
    · exact (hc.append _) q' hq' h
    · simp only [splitLocalHashInput, Option.some.injEq] at h
      subst h
      exact absurd hq' (treeSimHash_budget_excludes_paid .keygen .term [] t.2.1).2

/-- The footprint holds along a whole actual run. -/
theorem treeSimHash_local_footprint (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hc : TreeSimHashFootprint s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld p)).run s)) :
    TreeSimHashFootprint r.2.1.1 r.2.2 := by
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
    exact treeSimHash_footprint_step prims D t s.1 s.2 hc u hu

/-- The footprint of the normalized program from empty caches. -/
theorem treeSimHash_normalized_footprint (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (r : ((α × TreeSimLog C) × HiddenCache C) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run ∅)).run ∅)) :
    TreeSimHashFootprint r.2 r.1.1.2 := by
  apply treeSimHash_local_footprint prims D p ((∅, ∅), [])
    (r.1.1.1, (r.2, r.1.2), r.1.1.2)
  · intro q _ hq
    exact absurd rfl hq
  · rw [treeSimHash_state_normalize, support_map]
    exact ⟨r, hr, rfl⟩

/-- The budget-region input of a counted hash call. -/
def treeSimHashCountedQuery : (WorldSpec C).Domain → Option (Query C)
  | .inl (.inl (.inr (.inl q))) => if TreeSimHashBudgetDomain q then some q else none
  | _ => none

def treeSimHashCountedQueries (log : TreeSimLog C) : List (Query C) :=
  log.filterMap fun r => treeSimHashCountedQuery r.1

theorem treeSimHash_counted_query_charged (t : (WorldSpec C).Domain)
    (h : (treeSimHashCountedQuery t).isSome) : WorldCounted t := by
  rcases t with ((n | q | x) | t) | t
  all_goals simp only [treeSimHashCountedQuery, Option.isSome_none, Bool.false_eq_true] at h
  split_ifs at h with hq
  · cases q <;> simp_all [WorldCounted, Counted, TreeSimHashBudgetDomain, TreeSimHashDomain]
  · simp at h

theorem treeSimHash_counted_queries_length (D : C.Coalition) {α : Type}
    (p : OracleComp (WorldSpec C) α) (n : ℕ) (h : IsQueryBoundP p WorldCounted n)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    (treeSimHashCountedQueries r.2.2).length ≤ (treeSimHashCountedQueries s.2).length + n := by
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
    simp only [treeSimHashCountedQueries, List.filterMap_append, List.length_append,
      List.filterMap_cons, List.filterMap_nil] at hb
    dsimp only [treeSimHashCountedQueries]
    cases hp : treeSimHashCountedQuery t with
    | none =>
      simp only [hp] at hb
      by_cases ht : WorldCounted t <;>
        simp only [ht, if_true, if_false, List.length_nil] at hb <;> omega
    | some q =>
      have ht := treeSimHash_counted_query_charged t (by simp [hp])
      have hn := h.1.resolve_left (not_not.mpr ht)
      simp only [hp, if_pos ht, List.length_cons, List.length_nil] at hb
      omega

/-- The counted budget-region inputs of the normalized program number at most `q`. -/
theorem treeSimHash_program_counted (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (r : ((Bool × TreeSimLog C) × HiddenCache C) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (treeSimHashProgram K circuits settings top tree D A x z Z)).run ∅)) :
    (treeSimHashCountedQueries r.1.1.2).length ≤ q := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  have hgame : IsQueryBoundP (treeRealGame K circuits settings top tree D A x z Z) WorldCounted q :=
    isQueryBoundP_distinguish_realExecution D A noFunctionality _ _ x z Z q hq
      (fun step _ state inputs => isQueryBoundP_runFunctionality_noFunctionality D A state inputs step)
  have hs : (r.1.1.1, (r.2, r.1.2), r.1.1.2) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run ((∅, ∅), [])) := by
    rw [← treeSim_localReal_eq K circuits settings top tree D A x z Z,
      treeSimHash_state_normalize, support_map]
    exact ⟨r, hr, rfl⟩
  simpa [treeSimHashCountedQueries] using
    treeSimHash_counted_queries_length prims D _ q hgame _ _ hs

/-- The remaining honest count. Without a region collision, the honest budget-region inputs of
the normalized program lie in at most `treeSecrets - 2 m` points. -/
def TreeSimHashHonestBudget : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) < 2 ^ 128 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (treeSimHashProgram K circuits settings top tree D A x z Z)).run ∅),
      ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2) →
      ∃ S : Finset (Query C), S.card ≤ treeSecrets circuits settings C tree - 2 * prssKeyCount C ∧
        ∀ t h, TreeSimHashBudgetDomain t →
          (⟨.inr (.inr (.inl t)), h⟩ : (u : (WorldSpec C).Domain) × (WorldSpec C).Range u) ∈
            r.1.1.2 → t ∈ S

/-- The final-cache count follows from the honest count. -/
theorem treeSimHash_terminal_of_honest
    (honest : TreeSimHashHonestBudget prims K circuits settings) :
    TreeSimHashTerminalBudget prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall r hr good
  obtain ⟨S, hS, hcover⟩ := honest hb top tree D A x z Z q hx hq hsmall r hr good
  have foot := treeSimHash_normalized_footprint prims D
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) r hr
  refine treeSimHash_cache_bound_of_cover r.2 (treeSimHashCountedQueries r.1.1.2).toFinset S q _
    ((List.toFinset_card_le _).trans
      (treeSimHash_program_counted prims K circuits settings top tree D A x z Z q hq r hr))
    hS ?_
  intro t ht hc
  obtain ⟨h, hh | hh⟩ := foot t ht hc
  · exact Or.inr (hcover t h ht hh)
  · refine Or.inl (List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, hh, ?_⟩))
    simp only [treeSimHashCountedQuery, if_pos ht]

/-- The hash bound follows from the honest count and the salt estimate. -/
theorem treeSimHashBoundFinal
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings) :
    TreeSimHashBoundGoal prims K circuits settings :=
  treeSimHashBound_of_terminal prims K circuits settings
    (treeSimHash_terminal_of_honest prims K circuits settings honest) salt

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBoundFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundFinal

end ThresholdLeanXmssSecurity
