import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Games
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition
import ThresholdLeanXmssSecurity.Proof.SeedGenSecurity

/-!
# A private table for a set of cells

A cell predicate `Q` on the inputs of `H` splits the cache of the world. `isPrivate Q` marks the local
calls that touch a cell with `Q`. `tableLocal Q prims` answers each private call from its own lazy
table with the step of the world and forwards each other call. Both come from
`DkgCorrectnessProof.Partitioned`.

The side with the merged cache runs in `streamWorld` with a fixed cache of the hidden streams. A
query of `WorldSafe Q` is no private call, no programming query and no free call of `PRG`.

* `streamWorld_frame` and `simulate_frame` show that a world computation with only `WorldSafe Q`
  queries reads and writes only the cells of the outer cache.
* `adversary_coupling` shows that a computation on the counted copy equals its run with the private
  table, with the table merged into the cache.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedPartition

open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Partitioned (isPrivate)

variable {C : Committee} (Q : Query C → Bool)

/-- A query of the world that is no private call, no programming query of a cell with `Q` and no
free call of `PRG`. -/
def WorldSafe : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => isPrivate Q t = false
  | .inl (.inr x) => Q x.1 = false
  | .inr (.inr (.inr _)) => False
  | .inr t => isPrivate Q t = false

/-- The cache with the cells with `Q` from `p` and the other cells from `s`. -/
def merge (s p : HashCache C) : HashCache C := QueryCache.ofFn fun q => if Q q then p q else s q

/-! ## The frame -/

theorem merge_read_left {q : Query C} (hq : Q q = false) (s p : HashCache C) : merge Q s p q = s q := by
  simp [merge, hq]

theorem merge_read_right {q : Query C} (hq : Q q = true) (s p : HashCache C) : merge Q s p q = p q := by
  simp [merge, hq]

theorem merge_write_left {q : Query C} (hq : Q q = false) (s p : HashCache C) (v : HashOutput) :
    merge Q (s.cacheQuery q v) p = (merge Q s p).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases h : q' = q
  · subst h; simp [merge, hq]
  · by_cases h' : Q q' <;> simp [merge, h', QueryCache.cacheQuery_of_ne, h]

theorem merge_write_right {q : Query C} (hq : Q q = true) (s p : HashCache C) (v : HashOutput) :
    merge Q s (p.cacheQuery q v) = (merge Q s p).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases h : q' = q
  · subst h; simp [merge, hq]
  · by_cases h' : Q q' <;> simp [merge, h', QueryCache.cacheQuery_of_ne, h]

theorem merge_empty : merge Q (∅ : HashCache C) ∅ = ∅ := by
  refine QueryCache.ext fun q => ?_
  simp [merge]

/-- A local call that is not private reads and writes only the cells of `s`. -/
theorem localAnswer_left (prims : Primitives) (t : (LocalSpec C).Domain) (ht : isPrivate Q t = false)
    (s p : HashCache C) :
    (localAnswer prims t).run (merge Q s p) =
      (fun z => (z.1, merge Q z.2 p)) <$> (localAnswer prims t).run s := by
  rcases t with n | q | x
  · change (unifFwdImpl (Query C →ₒ HashOutput) n).run (merge Q s p) =
      (fun z => (z.1, merge Q z.2 p)) <$> (unifFwdImpl (Query C →ₒ HashOutput) n).run s
    simp [unifFwdImpl]
  · exact DkgCorrectnessProof.UsedHit.hashAnswer_map prims q (merge Q · p) s (merge_read_left Q ht s p)
      (merge_write_left Q ht s p)
  · change (prgAnswer prims x).run (merge Q s p) = (fun z => (z.1, merge Q z.2 p)) <$> (prgAnswer prims x).run s
    simp only [prgAnswer, StateT.run_bind,
      DkgCorrectnessProof.UsedHit.hashAnswer_map prims _ (merge Q · p) s (merge_read_left Q ht s p)
        (merge_write_left Q ht s p),
      bind_map_left, map_bind, StateT.run_pure, map_pure]

/-- A private call reads and writes only the cells of `p`. -/
theorem localAnswer_right (prims : Primitives) (t : (LocalSpec C).Domain) (ht : isPrivate Q t = true)
    (s p : HashCache C) :
    (localAnswer prims t).run (merge Q s p) =
      (fun z => (z.1, merge Q s z.2)) <$> (localAnswer prims t).run p := by
  rcases t with n | q | x
  · exact absurd ht (by simp [isPrivate])
  · exact DkgCorrectnessProof.UsedHit.hashAnswer_map prims q (merge Q s ·) p (merge_read_right Q ht s p)
      (merge_write_right Q ht s p)
  · change (prgAnswer prims x).run (merge Q s p) = (fun z => (z.1, merge Q s z.2)) <$> (prgAnswer prims x).run p
    simp only [prgAnswer, StateT.run_bind,
      DkgCorrectnessProof.UsedHit.hashAnswer_map prims _ (merge Q s ·) p (merge_read_right Q ht s p)
        (merge_write_right Q ht s p),
      bind_map_left, map_bind, StateT.run_pure, map_pure]

/-- A programming query of a cell outside `Q` reads and writes only the cells of `s`. -/
theorem programAnswer_left (x : Query C × HashOutput) (hx : Q x.1 = false) (s p : HashCache C) :
    (programAnswer x).run (merge Q s p) = (fun z => (z.1, merge Q z.2 p)) <$> (programAnswer x).run s := by
  have hr : (merge Q s p).toFn x.1 = s.toFn x.1 := merge_read_left Q hx s p
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with h1 h2 h2
  · simp
  · rw [hr] at h1
    exact absurd h1 h2
  · rw [hr] at h1
    exact absurd h2 h1
  · simp [merge_write_left Q hx]

/-- A step of `streamWorld` on a safe query from the merged cache is the step of the world on `s`,
and it keeps the cache of the hidden streams. -/
theorem streamWorld_frame (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain) (ht : WorldSafe Q t)
    (s p : HashCache C) (H : HiddenCache C) :
    (streamWorld prims D t).run (merge Q s p, H) =
      (fun z => (z.1, (merge Q z.2 p, H))) <$> (worldAnswer prims t).run s := by
  rcases t with (t | x) | (n | q | x)
  · change (fun r => (r.1, (r.2, H))) <$> (localAnswer prims t).run (merge Q s p) = _
    rw [localAnswer_left Q prims t ht s p, Functor.map_map]
    rfl
  · change (fun r => (r.1, (r.2, H))) <$> (programAnswer x).run (merge Q s p) = _
    rw [programAnswer_left Q x ht s p, Functor.map_map]
    rfl
  · change (fun r => (r.1, (r.2, H))) <$> (localAnswer prims (.inl n)).run (merge Q s p) = _
    rw [localAnswer_left Q prims (.inl n) ht s p, Functor.map_map]
    rfl
  · change (fun r => (r.1, (r.2, H))) <$> (localAnswer prims (.inr (.inl q))).run (merge Q s p) = _
    rw [localAnswer_left Q prims (.inr (.inl q)) ht s p, Functor.map_map]
    rfl
  · exact ht.elim

/-- A world computation with only `WorldSafe Q` queries reads and writes only the cells of `s`. -/
theorem simulate_frame (prims : Primitives) (D : C.Coalition) {α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy oa (WorldSafe Q)) (s p : HashCache C) (H : HiddenCache C) :
    (simulateQ (streamWorld prims D) oa).run (merge Q s p, H) =
      (fun z => (z.1, (merge Q z.2 p, H))) <$> (simulateQ (worldAnswer prims) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self]
    rw [streamWorld_frame Q prims D t h.1 s p H, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ (h.2 _) z.2

/-! ## One computation on the counted copy -/

/-- The run of one computation on the counted copy equals its run with the private table, with the
table merged into the cache. -/
theorem adversary_coupling (prims : Primitives) (D : C.Coalition) {α : Type} (b : OracleComp (LocalSpec C) α)
    (s p : HashCache C) (H : HiddenCache C) :
    (simulateQ (streamWorld prims D) (worldRoles.adversary b)).run (merge Q s p, H) =
      (fun z => (z.1.1, (merge Q z.2 z.1.2, H))) <$>
        (simulateQ (worldAnswer prims) (worldRoles.adversary ((simulateQ (DkgCorrectnessProof.Partitioned.tableLocal Q prims) b).run p))).run s := by
  rw [SeedHitProof.simulateQ_adversary_split, SeedHitProof.simulateQ_adversary_split]
  induction b using OracleComp.inductionOn generalizing s p with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases ht : isPrivate Q t = true
    · have e : (DkgCorrectnessProof.Partitioned.tableLocal Q prims t).run p = liftComp ((localAnswer prims t).run p) (LocalSpec C) := by
        simp [DkgCorrectnessProof.Partitioned.tableLocal, ht]
      rw [e]
      change (fun r => (r.1, (r.2, H))) <$> (localAnswer prims t).run (merge Q s p) >>= _ = _
      rw [localAnswer_right Q prims t ht s p, Functor.map_map, bind_map_left]
      change _ = _ <$> ((simulateQ (localAnswer prims) (liftComp ((localAnswer prims t).run p) (LocalSpec C))).run s
        >>= _)
      rw [simulateQ_local_sample_seedGensecurity, StateT.run_lift, bind_assoc, map_bind]
      simp only [pure_bind]
      exact bind_congr fun z => ih z.1 s z.2
    · have hf : isPrivate Q t = false := by simpa using ht
      have e : (DkgCorrectnessProof.Partitioned.tableLocal Q prims t).run p =
          OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun a => pure (a, p) := by
        simp only [DkgCorrectnessProof.Partitioned.tableLocal, hf, Bool.false_eq_true, ite_false]
        rw [StateT.run_monadLift, monadLift_self]
      rw [e, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc, map_bind]
      rw [streamWorld_frame Q prims D (.inl (.inl t)) hf s p H, bind_map_left]
      exact bind_congr fun z => ih z.1 z.2 p

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedPartition

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedPartition.adversary_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedPartition.adversary_coupling
