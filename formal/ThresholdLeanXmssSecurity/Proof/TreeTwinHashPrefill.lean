import ThresholdLeanXmssSecurity.Proof.TreeTwinPrefill

/-! # Prefilling public hash cells read by free programs
The equality retains the returned value, both caches, and the complete query log.
Visible PRG reads count as reads of their public stream key.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinHashPrefill
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} (prims : Primitives)

private theorem hash_update (q t : Query C) (hne : t ≠ q)
    (h : HashCache C) (v : HashOutput) :
    (hashAnswer prims t).run (h.cacheQuery q v) =
      (fun r => (r.1, r.2.cacheQuery q v)) <$> (hashAnswer prims t).run h := by
  by_cases fixed : IsFixed t
  · obtain ⟨input, rfl, hm⟩ := fixed
    simp [hashAnswer_of_isFixed prims hm]
  · rw [hashAnswer_of_not_isFixed prims fixed]
    exact treeSimCheck_randomOracle_update h t q hne v

private theorem hash_other (q t : Query C) (hne : t ≠ q)
    (h : HashCache C) (r : HashOutput × HashCache C)
    (hr : r ∈ support ((hashAnswer prims t).run h)) : r.2 q = h q := by
  by_cases fixed : IsFixed t
  · obtain ⟨input, rfl, hm⟩ := fixed
    simp only [hashAnswer_of_isFixed prims hm, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst r
    rfl
  · rw [hashAnswer_of_not_isFixed prims fixed] at hr
    exact (randomOracle_support t h r hr).2.2 q (Ne.symm hne)

/-- The public cell read by a free hash or visible PRG query. -/
def Reads (D : C.Coalition) (q : Query C) : (LocalSpec C).Domain → Prop
  | .inl _ => False
  | .inr (.inl t) => t = q
  | .inr (.inr x) => ¬ Hidden D x.1 ∧ .streamKey x.2.1 = q

private theorem logged_update (D : C.Coalition) (q : Query C)
    (t : (LocalSpec C).Domain) (hne : ¬ Reads D q t) (s : TreeSimState C) (v : HashOutput) :
    (treeSimLoggedWorld prims D (.inr t)).run ((s.1.1.cacheQuery q v, s.1.2), s.2) =
      (fun r => (r.1, (r.2.1.1.cacheQuery q v, r.2.1.2), r.2.2)) <$>
        (treeSimLoggedWorld prims D (.inr t)).run s := by
  rcases t with n | t | x
  · simp [treeSimLoggedWorld, streamWorld, onHash, localAnswer, unifFwdImpl, StateT.run_monadLift, Functor.map_map]
  · simp only [Reads] at hne
    simp only [treeSimLoggedWorld, streamWorld, onHash, localAnswer,
      QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_mk,
      Functor.map_map]
    erw [hash_update prims q t hne]
    simp only [Functor.map_map]
    rfl
  · by_cases hidden : Hidden D x.1
    · simp [treeSimLoggedWorld, streamWorld, hidden, Functor.map_map]
    · have ne : Query.streamKey x.2.1 ≠ q := fun he => hne ⟨hidden, he⟩
      simp [treeSimLoggedWorld, streamWorld, hidden, onHash, localAnswer, prgAnswer,
        hash_update prims q (.streamKey x.2.1) ne, Functor.map_map]

private theorem logged_other (D : C.Coalition) (q : Query C)
    (t : (LocalSpec C).Domain) (hne : ¬ Reads D q t) (s : TreeSimState C)
    (r : (LocalSpec C).Range t × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
    r.2.1.1 q = s.1.1 q := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  rcases t with n | t | x
  · simp only [streamWorld, onHash, localAnswer, QueryImpl.add_apply_inl,
      unifFwdImpl, QueryImpl.liftTarget, StateT.run_monadLift, StateT.run_mk,
      support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    change v ∈ support ((fun a => (a, s.1.1)) <$> (liftM (unifSpec.query n) : ProbComp _)) at hv
    rw [support_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rfl
  · simp only [streamWorld, onHash, localAnswer, QueryImpl.add_apply_inr,
      QueryImpl.add_apply_inl, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact hash_other prims q t hne s.1.1 v hv
  · by_cases hidden : Hidden D x.1
    · simp only [streamWorld, hidden, if_true, StateT.run_mk, support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rfl
    · have ne : Query.streamKey x.2.1 ≠ q := fun he => hne ⟨hidden, he⟩
      simp only [streamWorld, hidden, if_false, onHash, localAnswer, QueryImpl.add_apply_inr,
        StateT.run_mk, support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      simp [prgAnswer, support_map, Set.mem_image] at hv
      obtain ⟨w, c, hw, rfl⟩ := hv
      exact hash_other prims q (.streamKey x.2.1) ne s.1.1 (w, c) hw

private theorem free_query (t : (LocalSpec C).Domain) :
    free (liftM ((LocalSpec C).query t)) =
      (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) := rfl

/-- Full-state deferred sampling, by the A180 first-read induction. -/
theorem treeSim_prefillHash_logged {α : Type} (D : C.Coalition) (q : Query C)
    (random : ¬ IsFixed q) (p : OracleComp (LocalSpec C) α) :
    ∀ s : TreeSimState C, s.1.1 q = none →
      (∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s),
        u.2.1.1 q ≠ none) →
      evalDist ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s) =
        evalDist (do
          let v ← ($ᵗ HashOutput : ProbComp HashOutput)
          (simulateQ (treeSimLoggedWorld prims D) (free p)).run
            ((s.1.1.cacheQuery q v, s.1.2), s.2)) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    intro s fresh read
    exact False.elim (read (a, s) (by simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff]) fresh)
  | query_bind t k ih =>
    intro s fresh read
    simp only [free_bind, free_query, simulateQ_bind] at read ⊢
    simp only [simulateQ_spec_query, StateT.run_bind] at read ⊢
    by_cases hit : Reads D q t
    · rcases t with n | t | x
      · exact False.elim hit
      · change t = q at hit
        subst t
        simp only [treeSimLoggedWorld, streamWorld, onHash, localAnswer,
          QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_mk,
          hashAnswer_of_not_isFixed prims random]
        rw [QueryImpl.withCaching_run_none _ fresh]
        simp only [Functor.map_map, bind_map_left]
        apply evalDist_bind_congr_all
        intro v
        rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self s.1.1 q v)]
        simp only [pure_bind]
      · obtain ⟨hidden, he⟩ := hit
        subst q
        simp only [treeSimLoggedWorld, streamWorld, hidden, if_false, onHash, localAnswer,
          QueryImpl.add_apply_inr, StateT.run_mk, prgAnswer, StateT.run_bind, StateT.run_pure,
          hashAnswer_of_not_isFixed prims random]
        rw [QueryImpl.withCaching_run_none _ fresh]
        simp only [bind_map_left, pure_bind, map_bind, map_pure, bind_assoc]
        apply evalDist_bind_congr_all
        intro v
        rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self s.1.1 (.streamKey x.2.1) v)]
        simp only [pure_bind]
    · simp_rw [logged_update prims D q t hit, bind_map_left]
      rw [← OracleComp.DeferredSampling.evalDist_bind_comm]
      apply evalDist_bind_congr
      intro r hr
      apply ih r.1 r.2 ((logged_other prims D q t hit s r hr).trans fresh)
      intro u hu
      exact read u ((mem_support_bind_iff _ _ _).2 ⟨r, hr, hu⟩)


/-- Every fixed prefill outcome is supported by the original computation. -/
theorem prefillHash_supported {α : Type} (D : C.Coalition) (q : Query C)
    (random : ¬ IsFixed q) (p : OracleComp (LocalSpec C) α) (s : TreeSimState C)
    (fresh : s.1.1 q = none)
    (read : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s),
      u.2.1.1 q ≠ none) (v : HashOutput) (u : α × TreeSimState C)
    (hu : u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run
      ((s.1.1.cacheQuery q v, s.1.2), s.2))) :
    u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s) := by
  have he := treeSim_prefillHash_logged prims D q random p s fresh read
  rw [mem_support_iff, probOutput_def, he, ← probOutput_def, ← mem_support_iff]
  exact (mem_support_bind_iff _ _ _).2 ⟨v, by simp, hu⟩

/-- Erasing only the log gives the full two-cache stream law. -/
theorem treeSim_prefillHash_stream {α : Type} (D : C.Coalition) (q : Query C)
    (random : ¬ IsFixed q) (p : OracleComp (LocalSpec C) α)
    (s : HashCache C × HiddenCache C) (fresh : s.1 q = none)
    (read : ∀ u ∈ support ((simulateQ (streamWorld prims D) (free p)).run s),
      u.2.1 q ≠ none) :
    evalDist ((simulateQ (streamWorld prims D) (free p)).run s) =
      evalDist (do
        let v ← ($ᵗ HashOutput : ProbComp HashOutput)
        (simulateQ (streamWorld prims D) (free p)).run (s.1.cacheQuery q v, s.2)) := by
  have hr : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run (s, [])),
      u.2.1.1 q ≠ none := by
    intro u hu
    apply read (u.1, u.2.1)
    rw [← treeSimLoggedWorld_erase prims D (free p) s [], support_map]
    exact ⟨u, hu, rfl⟩
  have he := treeSim_prefillHash_logged prims D q random p (s, []) fresh hr
  have hm := evalDist_map_eq_of_evalDist_eq he (fun r : α × TreeSimState C => (r.1, r.2.1))
  simpa only [map_bind, treeSimLoggedWorld_erase] using hm

/-- Sequential finite prefilling, retaining both caches and the complete log.
This is A180's finite induction with public hash cells and HashOutput samples. -/
theorem prefillHash_sequence_fin {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α) :
    ∀ {n : ℕ} (addr : Fin n → Query C) (_inj : Function.Injective addr)
      (_random : ∀ i, ¬ IsFixed (addr i)) (h : HashCache C) (c : HiddenCache C) (log : TreeSimLog C),
      (∀ i, h (addr i) = none) →
      (∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run ((h, c), log)),
        ∀ i, u.2.1.1 (addr i) ≠ none) →
      evalDist ((simulateQ (treeSimLoggedWorld prims D) (free p)).run ((h, c), log)) =
        evalDist (do
          let vals ← Concrete.sequenceFin (fun _ : Fin n => ($ᵗ HashOutput))
          (simulateQ (treeSimLoggedWorld prims D) (free p)).run ((cacheFin addr vals h, c), log))
  | 0, addr, _, _, h, c, log, fresh, read => by simp [Concrete.sequenceFin, cacheFin]
  | n + 1, addr, inj, random, h, c, log, fresh, read => by
    rw [treeSim_prefillHash_logged prims D (addr 0) (random 0) p ((h, c), log) (fresh 0)
      (fun u hu => read u hu 0)]
    simp only [Concrete.sequenceFin, bind_assoc]
    apply evalDist_bind_congr_all
    intro v
    have hf : ∀ i : Fin n, (h.cacheQuery (addr 0) v) (addr i.succ) = none := fun i =>
      (QueryCache.cacheQuery_of_ne h v (fun he => Fin.succ_ne_zero i (inj he))).trans (fresh i.succ)
    have hr : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run
        ((h.cacheQuery (addr 0) v, c), log)), ∀ i : Fin n, u.2.1.1 (addr i.succ) ≠ none := by
      intro u hu i
      exact read u (prefillHash_supported prims D (addr 0) (random 0) p ((h, c), log) (fresh 0)
        (fun u hu => read u hu 0) v u hu) i.succ
    simpa only [pure_bind, cacheFin, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ] using
      prefillHash_sequence_fin D p (fun i : Fin n => addr i.succ)
        (inj.comp (Fin.succ_injective n)) (fun i => random i.succ) (h.cacheQuery (addr 0) v) c log hf hr

/-- A jointly uniform public hash table for a family read on every run. -/
theorem treeSim_prefillHash_logged_table {α : Type} (D : C.Coalition) {n : ℕ}
    (addr : Fin n → Query C) (inj : Function.Injective addr)
    (random : ∀ i, ¬ IsFixed (addr i)) (p : OracleComp (LocalSpec C) α)
    (h : HashCache C) (c : HiddenCache C) (log : TreeSimLog C)
    (fresh : ∀ i, h (addr i) = none)
    (read : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run ((h, c), log)),
      ∀ i, u.2.1.1 (addr i) ≠ none) :
    evalDist ((simulateQ (treeSimLoggedWorld prims D) (free p)).run ((h, c), log)) =
      evalDist (do
        let table ← ($ᵗ (Fin n → HashOutput) : ProbComp (Fin n → HashOutput))
        (simulateQ (treeSimLoggedWorld prims D) (free p)).run ((cacheFin addr table h, c), log)) := by
  rw [prefillHash_sequence_fin prims D p addr inj random h c log fresh read,
    evalDist_bind, evalDist_sequenceFin_uniform, ← evalDist_bind]



/-- Uniform table prefilling for a duplicate-free list of public hash cells. -/
theorem prefillHash_sequence {α : Type} (D : C.Coalition) (qs : List (Query C))
    (nodup : qs.Nodup) (random : ∀ q ∈ qs, ¬ IsFixed q)
    (p : OracleComp (LocalSpec C) α) (s : TreeSimState C)
    (fresh : ∀ q ∈ qs, s.1.1 q = none)
    (read : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s),
      ∀ q ∈ qs, u.2.1.1 q ≠ none) :
    evalDist ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s) =
      evalDist (do
        let table ← ($ᵗ (Fin qs.length → HashOutput) : ProbComp (Fin qs.length → HashOutput))
        (simulateQ (treeSimLoggedWorld prims D) (free p)).run
          ((cacheFin qs.get table s.1.1, s.1.2), s.2)) := by
  exact treeSim_prefillHash_logged_table prims D qs.get nodup.injective_get
    (fun i => random _ (List.get_mem _ i)) p s.1.1 s.1.2 s.2
    (fun i => fresh _ (List.get_mem _ i)) (fun u hu i => read u hu _ (List.get_mem _ i))

/-- The list-table law with only the log erased. -/
theorem prefillHash_sequence_stream {α : Type} (D : C.Coalition) (qs : List (Query C))
    (nodup : qs.Nodup) (random : ∀ q ∈ qs, ¬ IsFixed q)
    (p : OracleComp (LocalSpec C) α) (s : HashCache C × HiddenCache C)
    (fresh : ∀ q ∈ qs, s.1 q = none)
    (read : ∀ u ∈ support ((simulateQ (streamWorld prims D) (free p)).run s),
      ∀ q ∈ qs, u.2.1 q ≠ none) :
    evalDist ((simulateQ (streamWorld prims D) (free p)).run s) =
      evalDist (do
        let table ← ($ᵗ (Fin qs.length → HashOutput) : ProbComp (Fin qs.length → HashOutput))
        (simulateQ (streamWorld prims D) (free p)).run (cacheFin qs.get table s.1, s.2)) := by
  have hr : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run (s, [])),
      ∀ q ∈ qs, u.2.1.1 q ≠ none := by
    intro u hu
    apply read (u.1, u.2.1)
    rw [← treeSimLoggedWorld_erase prims D (free p) s [], support_map]
    exact ⟨u, hu, rfl⟩
  have he := prefillHash_sequence prims D qs nodup random p (s, []) fresh hr
  have hm := evalDist_map_eq_of_evalDist_eq he (fun r : α × TreeSimState C => (r.1, r.2.1))
  simpa only [map_bind, treeSimLoggedWorld_erase] using hm

/-- Fixed prefill support inclusion after erasing the log. -/
theorem prefillHash_supported_stream {α : Type} (D : C.Coalition) (q : Query C)
    (random : ¬ IsFixed q) (p : OracleComp (LocalSpec C) α) (s : HashCache C × HiddenCache C)
    (fresh : s.1 q = none)
    (read : ∀ u ∈ support ((simulateQ (streamWorld prims D) (free p)).run s),
      u.2.1 q ≠ none) (v : HashOutput) (u : α × (HashCache C × HiddenCache C))
    (hu : u ∈ support ((simulateQ (streamWorld prims D) (free p)).run
      (s.1.cacheQuery q v, s.2))) :
    u ∈ support ((simulateQ (streamWorld prims D) (free p)).run s) := by
  have he := treeSim_prefillHash_stream prims D q random p s fresh read
  rw [mem_support_iff, probOutput_def, he, ← probOutput_def, ← mem_support_iff]
  exact (mem_support_bind_iff _ _ _).2 ⟨v, by simp, hu⟩

end ThresholdLeanXmssSecurity.TreeTwinHashPrefill

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.treeSim_prefillHash_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.treeSim_prefillHash_logged

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.treeSim_prefillHash_stream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.treeSim_prefillHash_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_supported

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_supported_stream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_supported_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_sequence_fin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_sequence_fin

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.treeSim_prefillHash_logged_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.treeSim_prefillHash_logged_table

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_sequence

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_sequence_stream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeTwinHashPrefill.prefillHash_sequence_stream
