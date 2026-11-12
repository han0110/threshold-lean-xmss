import ThresholdLeanXmssSecurity.Proof.TreeCheckBranches

/-!
# The uncounted branch of the guarded check route

This module works on `TreeCheckUncountedGuess` (`TreeCheckBranches`). The bound is one guess,
`2^-256`, so the factor `2` of the target is slack.

* `guessWeight` is a potential for one point of `H` and one target value. It is `1` when the
  cache holds the target at the point, `0` when it holds another value, and `2^-256` while the
  point is open. One lazy random-oracle query keeps its expected value. So
  `guess_free_probEvent_le` bounds the probability that a free computation ends with the target
  in the cache by the weight at the start. The proof uses `XmssSecurity.expectedFinal_le` of
  leanVM, as `saltPair_probEvent_le` does.
* `SetupFresh` holds before the honest openings of the reveal round. A corrupt commitment point
  with no counted query is open in the cache, and no free query hit such a point. The adversary
  steps and `prssInitialData` keep it.
* `rows_finish_guess` is the reveal and echo rounds. If some opening point of an honest receiver
  and a corrupt sender has no counted query, one such pair is fixed by the state before the
  openings. An honest output needs a row of each honest operator, because an
  operator with no row sends an abort frame in the echo round (`setupFinishResult_rows`). That row
  caches the opening at the committed value, which is one guess. If each opening point has a
  counted query, no opening is uncounted.
* `treeSaltSetup_guess` gives the bound on the whole PRSS setup.
* `treeCheckAudited_split` splits the audited run at the end of the setup. With no honest keys, no
  honest operator gives an output (`auditAfter_none`).
* `treeCheckUncountedGuess_of_noCommit` proves `TreeCheckUncountedGuess` from
  `TreeCheckAfterSetupNoCommit`, which says that the run after the setup adds no free entry of `H`
  at a corrupt commitment point.
* `treeCheckAfterSetupNoCommit_of_audit` lifts a zero query budget of the honest program through
  `continueStep`, `executeRounds` and the distinguisher on the logged world (`advance_stepBudget`,
  `round_noNewFree`, `executeRounds_noNewFree`). `treeCheckUncountedGuess_of_audit` combines the
  two steps.

`TreeCheckAfterSetupAuditNoCommit` says that `treeSimCheckAfterSetupAudit` makes no
`.commit` query. It is true, because only `commitRevealEcho` queries `.commit`. Its proof is a walk
of the audited program with this predicate, as `TreeSimHashCount.ceremony_bound` does for `Region`.
Each `Region` lemma with a zero bound transfers by `IsQueryBoundP.of_imp`, as in
`derive_freeHashIn_zero`. Each lemma with a nonzero bound needs a new proof with zero bound.

The abort propagation uses the echo round of the setup (`setupFinishResult_rows`). The private
`setupFinishResult`, `setupFinish_local` and `setupFinish_round` of `TreeSetupKeys.lean` are copied
here verbatim.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Weight

variable {C : Committee} (prims : Primitives)

/-- The potential of one point `point` of `H` and one target value `target`. -/
def guessWeight (point : Query C) (target : HashOutput) (cache : HashCache C) : ℝ≥0∞ :=
  match cache point with
  | none => (2 ^ 256 : ℝ≥0∞)⁻¹
  | some v => if v = target then 1 else 0

theorem guessWeight_of_target {point : Query C} {target : HashOutput} {cache : HashCache C}
    (h : cache point = some target) : 1 ≤ guessWeight point target cache := by
  simp [guessWeight, h]

theorem guessWeight_of_open {point : Query C} {target : HashOutput} {cache : HashCache C}
    (h : cache point = none) : guessWeight point target cache = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simp [guessWeight, h]

/-- A step that keeps the cache at the point keeps the expected weight. -/
theorem guessWeight_keep {σ β : Type} (step : ProbComp (β × σ)) (cache : σ → HashCache C)
    (point : Query C) (target : HashOutput) (s : σ)
    (hkeep : ∀ r ∈ support step, cache r.2 point = cache s point) :
    ∑' r, Pr[= r | step] * guessWeight point target (cache r.2) ≤
      guessWeight point target (cache s) := by
  calc ∑' r, Pr[= r | step] * guessWeight point target (cache r.2)
      = ∑' r, Pr[= r | step] * guessWeight point target (cache s) := by
        refine tsum_congr fun r => ?_
        by_cases hr : r ∈ support step
        · simp only [guessWeight, hkeep r hr]
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ = (∑' r, Pr[= r | step]) * guessWeight point target (cache s) := ENNReal.tsum_mul_right
    _ ≤ guessWeight point target (cache s) := mul_le_of_le_one_left (zero_le) tsum_probOutput_le_one

/-- One lazy random-oracle query keeps the expected weight. -/
theorem guessWeight_randomOracle (point x : Query C) (target : HashOutput) (cache : HashCache C) :
    ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle x).run cache] *
      guessWeight point target r.2 ≤ guessWeight point target cache := by
  by_cases hx : x = point
  · subst hx
    cases hc : cache x with
    | some u =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, tsum_probOutput_pure_mul]
    | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, tsum_probOutput_map_mul]
      have hp : ∀ u : HashOutput, Pr[= u | uniformSampleImpl (spec := (Query C →ₒ HashOutput)) x] =
          (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        intro u
        simp [uniformSampleImpl, probOutput_uniformSample, hashOutputBits]
        norm_num
      have hw : ∀ u : HashOutput, guessWeight x target (cache.cacheQuery x u) =
          if u = target then 1 else 0 := by
        intro u
        simp [guessWeight]
      simp only [hw, hp, guessWeight_of_open hc]
      rw [tsum_fintype]
      simp
  · exact guessWeight_keep _ id point target cache
      (fun r hr => (randomOracle_support x cache r hr).2.2 point (Ne.symm hx))

/-- Each local query keeps the expected weight. -/
theorem guessWeight_localStep (point : Query C) (target : HashOutput) (t : (LocalSpec C).Domain)
    (cache : HashCache C) :
    ∑' r, Pr[= r | (localAnswer prims t).run cache] * guessWeight point target r.2 ≤
      guessWeight point target cache := by
  rcases isAtom_localAnswer prims t with ⟨p, hp⟩ | ⟨q, g, hq⟩
  · refine guessWeight_keep _ id point target cache fun r hr => ?_
    rw [hp] at hr
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    rfl
  · rw [hq, StateT.run_map, tsum_probOutput_map_mul]
    exact guessWeight_randomOracle point q target cache

/-- Each query of the free copy keeps the expected weight of the hash cache. -/
theorem guessWeight_freeStep (D : C.Coalition) (point : Query C) (target : HashOutput)
    (t : (LocalSpec C).Domain) (s : TreeSimState C) :
    ∑' r, Pr[= r | (treeSimLoggedWorld prims D (.inr t)).run s] *
      guessWeight point target r.2.1.1 ≤ guessWeight point target s.1.1 := by
  simp only [treeSimLoggedWorld, StateT.run_mk]
  rw [tsum_probOutput_map_mul]
  rcases t with u | q | x
  · simp only [streamWorld, onHash, StateT.run_mk]
    rw [tsum_probOutput_map_mul]
    simpa using guessWeight_localStep prims point target (.inl u) s.1.1
  · simp only [streamWorld, onHash, StateT.run_mk]
    rw [tsum_probOutput_map_mul]
    simpa using guessWeight_localStep prims point target (.inr (.inl q)) s.1.1
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk]
      rw [tsum_probOutput_map_mul]
      simpa using guessWeight_keep _ (fun _ => s.1.1) point target s.1.2 fun _ _ => rfl
    · simp only [streamWorld, if_neg hx, onHash, StateT.run_mk]
      rw [tsum_probOutput_map_mul]
      simpa using guessWeight_localStep prims point target (.inr (.inr x)) s.1.1

/-- The guess bound on the free copy from any state. -/
theorem guess_free_probEvent_le (D : C.Coalition) (point : Query C) (target : HashOutput)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (s : TreeSimState C) :
    Pr[fun r => r.2.1.1 point = some target |
      (simulateQ (treeSimLoggedWorld prims D) (free oa)).run s] ≤
      guessWeight point target s.1.1 := by
  let I : QueryImpl (SimulatorSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inl t)
  let impl : QueryImpl (LocalSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inr t)
  have hsplit : treeSimLoggedWorld prims D = I + impl := by
    funext t
    rcases t with t | t <;> rfl
  rw [hsplit, simulateQ_free]
  refine (XmssSecurity.probEvent_le_expectedFinal impl (fun s => guessWeight point target s.1.1)
    (fun s => s.1.1 point = some target) (fun _ h => guessWeight_of_target h) oa s).trans ?_
  have h := XmssSecurity.expectedFinal_le impl (Inv := fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun s => guessWeight point target s.1.1) (fun _ _ => 0)
    (fun t s _ => by rw [add_zero]; exact guessWeight_freeStep prims D point target t s) oa s trivial
  have hz : XmssSecurity.expectedSimulatedCost impl (fun _ _ => 0) oa s = 0 := by
    simpa using XmssSecurity.expectedSimulatedCost_const_mul impl 0 (fun _ _ => 0) oa s
  rwa [hz, add_zero] at h

end Weight

section Invariants

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- A state invariant that each free query outside `Q` keeps holds after a free computation with
no query in `Q`. -/
theorem logged_free_inv (Q : (LocalSpec C).Domain → Prop) (Inv : TreeSimState C → Prop)
    (hstep : ∀ t, ¬ Q t → ∀ s, Inv s →
      ∀ r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s), Inv r.2)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (hQ : IsQueryBoundP oa Q 0)
    (s : TreeSimState C) (hs : Inv s) (x : α × TreeSimState C)
    (hx : x ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free oa)).run s)) : Inv x.2 := by
  let I : QueryImpl (SimulatorSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inl t)
  let impl : QueryImpl (LocalSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inr t)
  have hsplit : treeSimLoggedWorld prims D = I + impl := by
    funext t
    rcases t with t | t <;> rfl
  rw [hsplit, simulateQ_free] at hx
  induction oa using OracleComp.inductionOn generalizing s x with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst x
    exact hs
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hx
    obtain ⟨mid, hmid, hx⟩ := hx
    have ht : ¬ Q t := by simpa using hQ.1
    exact ih mid.1 (by simpa [ht] using hQ.2 mid.1) mid.2 (hstep t ht s hs mid hmid) x hx

/-- A state invariant that each counted local query keeps holds after a step of the adversary. -/
theorem logged_adversary_inv (Inv : TreeSimState C → Prop)
    (hstep : ∀ t s, Inv s →
      ∀ r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl t))).run s), Inv r.2)
    {α : Type} (oa : OracleComp (LocalSpec C) α)
    (s : TreeSimState C) (hs : Inv s) (x : α × TreeSimState C)
    (hx : x ∈ support ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary oa)).run s)) :
    Inv x.2 := by
  induction oa using OracleComp.inductionOn generalizing s x with
  | pure a =>
    change x ∈ support ((simulateQ (treeSimLoggedWorld prims D) (pure a)).run s) at hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst x
    exact hs
  | query_bind t k ih =>
    rw [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a)
      from rfl, adversary_query] at hx
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
    obtain ⟨mid, hmid, hx⟩ := hx
    have he := simulateQ_spec_query (treeSimLoggedWorld prims D) (.inl (.inl t))
    erw [he] at hmid
    exact ih mid.1 mid.2 (hstep t s hs mid hmid) x hx

end Invariants

section Frame

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- A hash query at another point keeps the cache at a point. -/
theorem hashAnswer_frame (x q : Query C) (hx : x ≠ q) (cache : HashCache C)
    (z : HashOutput × HashCache C) (hz : z ∈ support ((hashAnswer prims x).run cache)) :
    z.2 q = cache q := by
  by_cases hf : IsFixed x
  · obtain ⟨input, rfl, hm⟩ := hf
    rw [hashAnswer_of_isFixed prims hm] at hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    rfl
  · rw [hashAnswer_of_not_isFixed prims hf] at hz
    exact (randomOracle_support x cache z hz).2.2 q (Ne.symm hx)

/-- A local query other than `H` at a point keeps the cache at the point, unless the point keys a
stream. -/
theorem localAnswer_frame (t : (LocalSpec C).Domain) (q : Query C) (hq : ∀ k, q ≠ .streamKey k)
    (ht : t ≠ .inr (.inl q)) (cache : HashCache C) (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) : r.2 q = cache q := by
  rcases t with n | x | x
  · change r ∈ support ((StateT.lift _ : StateT (HashCache C) ProbComp _).run cache) at hr
    simp only [StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    rfl
  · exact hashAnswer_frame prims x q (fun h => ht (by rw [h])) cache r hr
  · change r ∈ support ((prgAnswer prims x).run cache) at hr
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure] at hr
    erw [mem_support_bind_iff] at hr
    obtain ⟨z, hz, hr⟩ := hr
    erw [mem_support_pure_iff] at hr
    subst hr
    exact hashAnswer_frame prims _ q (fun h => hq x.2.1 h.symm) cache z hz

/-- A free query other than `H` at a point keeps the cache at the point. -/
theorem free_cache_frame (t : (LocalSpec C).Domain) (q : Query C) (hq : ∀ k, q ≠ .streamKey k)
    (ht : t ≠ .inr (.inl q)) (s : TreeSimState C)
    (r : (WorldSpec C).Range (.inr t) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
    r.2.1.1 q = s.1.1 q ∧ r.2.2 = s.2 ++ [⟨.inr t, r.1⟩] := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  refine ⟨?_, rfl⟩
  rcases t with n | x | x
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact localAnswer_frame prims (.inl n) q hq ht s.1.1 v hv
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact localAnswer_frame prims (.inr (.inl x)) q hq ht s.1.1 v hv
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rfl
    · simp only [streamWorld, if_neg hx, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact localAnswer_frame prims (.inr (.inr x)) q hq ht s.1.1 v hv

/-- A counted query other than `H` at a point keeps the cache at the point. -/
theorem counted_cache_frame (t : (LocalSpec C).Domain) (q : Query C) (hq : ∀ k, q ≠ .streamKey k)
    (ht : t ≠ .inr (.inl q)) (s : TreeSimState C)
    (r : (WorldSpec C).Range (.inl (.inl t)) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl t))).run s)) :
    r.2.1.1 q = s.1.1 q ∧ r.2.2 = s.2 ++ [⟨.inl (.inl t), r.1⟩] := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  refine ⟨?_, rfl⟩
  simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact localAnswer_frame prims t q hq ht s.1.1 v hv

/-- Each logged query appends one entry. -/
theorem logged_step_log (t : (WorldSpec C).Domain) (s : TreeSimState C)
    (r : (WorldSpec C).Range t × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D t).run s)) :
    r.2.2 = s.2 ++ [⟨t, r.1⟩] := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  rfl

end Frame

section Fresh

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- A PRSS commitment point from a corrupt sender to an honest receiver. -/
def CorruptCommit (D : C.Coalition) (q : Query C) : Prop :=
  ∃ j i reveal, q = .commit .prss j i reveal ∧ j ∈ D.1 ∧ i ∉ D.1

/-- The counted log entry of `H` at `q` with answer `h`. -/
abbrev countedEntry (q : Query C) (h : HashOutput) : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t :=
  ⟨.inl (.inl (.inr (.inl q))), h⟩

/-- The free log entry of `H` at `q` with answer `h`. -/
abbrev freeEntry (q : Query C) (h : HashOutput) : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t :=
  ⟨.inr (.inr (.inl q)), h⟩

/-- A free query of `H` at a point in `P`. -/
def FreeHashIn (P : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q, P q ∧ t = .inr (.inl q)

/-- A free query of `H` at a corrupt commitment point. -/
abbrev FreeCorruptQuery (D : C.Coalition) : (LocalSpec C).Domain → Prop :=
  FreeHashIn (CorruptCommit D)

/-- The state before the honest openings. A corrupt commitment point with no counted query is open
in the cache, and no free query hit a corrupt commitment point. -/
def SetupFresh (D : C.Coalition) (s : TreeSimState C) : Prop :=
  (∀ q, CorruptCommit D q → (∀ h, countedEntry q h ∉ s.2) → s.1.1 q = none) ∧
    ∀ q h, CorruptCommit D q → freeEntry q h ∉ s.2

theorem CorruptCommit.not_streamKey {q : Query C} (hq : CorruptCommit D q) :
    ∀ k, q ≠ .streamKey k := by
  obtain ⟨j, i, reveal, rfl, -⟩ := hq
  intro k h
  cases h

theorem setupFresh_empty : SetupFresh D (((∅, ∅), []) : TreeSimState C) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ h => by simp at h⟩

theorem setupFresh_counted (t : (LocalSpec C).Domain) (s : TreeSimState C) (hs : SetupFresh D s)
    (r : (WorldSpec C).Range (.inl (.inl t)) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl t))).run s)) : SetupFresh D r.2 := by
  have hlog := logged_step_log prims D _ s r hr
  refine ⟨fun q hq hnone => ?_, fun q h hq hmem => ?_⟩
  · have ht : t ≠ .inr (.inl q) := by
      rintro rfl
      exact hnone r.1 (by rw [hlog]; simp)
    rw [(counted_cache_frame prims D t q (hq.not_streamKey D) ht s r hr).1]
    exact hs.1 q hq fun h hh => hnone h (by rw [hlog]; exact List.mem_append_left _ hh)
  · rw [hlog, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · exact hs.2 q h hq hmem
    · cases hmem

theorem setupFresh_free (t : (LocalSpec C).Domain) (ht : ¬ FreeCorruptQuery D t)
    (s : TreeSimState C) (hs : SetupFresh D s)
    (r : (WorldSpec C).Range (.inr t) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) : SetupFresh D r.2 := by
  have hlog := logged_step_log prims D _ s r hr
  refine ⟨fun q hq hnone => ?_, fun q h hq hmem => ?_⟩
  · have htq : t ≠ .inr (.inl q) := fun he => ht ⟨q, hq, he⟩
    rw [(free_cache_frame prims D t q (hq.not_streamKey D) htq s r hr).1]
    exact hs.1 q hq fun h hh => hnone h (by rw [hlog]; exact List.mem_append_left _ hh)
  · rw [hlog, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · exact hs.2 q h hq hmem
    · have he : t = .inr (.inl q) := by
        have := congrArg Sigma.fst hmem
        simp only [Sum.inr.injEq] at this
        exact this.symm
      exact ht ⟨q, hq, he⟩

theorem prob_freeHashIn_zero (P : Query C → Prop) {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) (FreeHashIn P) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) (FreeHashIn P) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [FreeHashIn]), fun u => by simpa [FreeHashIn] using ih u⟩

theorem hashes_freeHashIn_zero (P : Query C → Prop) {ι : Type} (qs : ι → Query C) (xs : List ι)
    (h : ∀ x ∈ xs, ¬ P (qs x)) :
    IsQueryBoundP (liftComp (xs.mapM fun x => hashQuery (qs x)) (LocalSpec C))
      (FreeHashIn P) 0 := by
  apply TreeSimHashCount.ro_bound
  have hb := queryBound_mapM (fun t => FreeHashIn P (.inr t))
    (fun x => hashQuery (qs x)) 0 xs fun x hx => by
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl (qs x)))) _ 0
      rw [isQueryBoundP_query_iff]
      rintro ⟨q, hq, he⟩
      simp only [Sum.inr.injEq, Sum.inl.injEq] at he
      exact (h x hx (he ▸ hq)).elim
  simpa using hb

/-- `deriveKeys` makes no query of the budget domain, so no commitment query. -/
theorem derive_freeHashIn_zero (P : Query C → Prop) (hP : ∀ q, P q → TreeSimHashBudgetDomain q ∧ ¬ IsFixed q)
    (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (liftComp (deriveKeys phase i view) (LocalSpec C)) (FreeHashIn P) 0 := by
  apply TreeSimHashCount.ro_bound
  refine IsQueryBoundP.of_imp (fun t ht => ?_) (TreeSimHashCount.derive_zero phase i view)
  obtain ⟨q, hq, he⟩ := ht
  simp only [Sum.inr.injEq] at he
  subst he
  exact ⟨q, by simp [splitLocalHashInput, (hP q hq).2], (hP q hq).1⟩

theorem prssInitialData_freeCorrupt_zero :
    IsQueryBoundP (prssInitialData D) (FreeCorruptQuery D) 0 := by
  unfold prssInitialData
  refine isQueryBoundP_sequenceFin (p := FreeCorruptQuery D) _ fun i => ?_
  split_ifs with hi
  · trivial
  · refine isQueryBoundP_bind (n := 0) (m := 0) (prob_freeHashIn_zero _ _) fun own _ => ?_
    refine isQueryBoundP_bind (n := 0) (m := 0) (hashes_freeHashIn_zero _ _ _ ?_)
      fun _ _ => isQueryBoundP_pure _ _ _
    rintro j - ⟨j', i', reveal, he, hj', -⟩
    cases he
    exact hi hj'

end Fresh

section Cache

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

theorem isQueryBoundP_false {ι α : Type} {spec : OracleSpec ι} (oa : OracleComp spec α) :
    IsQueryBoundP oa (fun _ => False) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simp only [if_false]; exact ih u⟩

/-- A free query grows the hash cache. -/
theorem free_step_mono (t : (LocalSpec C).Domain) (s : TreeSimState C)
    (r : (WorldSpec C).Range (.inr t) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) : s.1.1 ≤ r.2.1.1 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  rcases t with n | x | x
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact treeSimHash_local_mono prims (.inl n) s.1.1 v hv
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact treeSimHash_local_mono prims (.inr (.inl x)) s.1.1 v hv
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact le_rfl
    · simp only [streamWorld, if_neg hx, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact treeSimHash_local_mono prims (.inr (.inr x)) s.1.1 v hv

/-- A free computation grows the hash cache. -/
theorem free_mono {α : Type} (oa : OracleComp (LocalSpec C) α) (s : TreeSimState C)
    (x : α × TreeSimState C)
    (hx : x ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free oa)).run s)) :
    s.1.1 ≤ x.2.1.1 :=
  logged_free_inv prims D (fun _ => False) (fun s' => s.1.1 ≤ s'.1.1)
    (fun t _ s' hs' r hr => hs'.trans (free_step_mono prims D t s' r hr))
    oa (by convert isQueryBoundP_false oa) s le_rfl x hx

/-- A free query of `H` at a point with a random answer caches its answer. -/
theorem free_hash_cached (q : Query C) (hq : ¬ IsFixed q) (s : TreeSimState C)
    (r : HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C)))).run s)) :
    r.2.1.1 q = some r.1 := by
  have he := simulateQ_spec_query (treeSimLoggedWorld prims D) (.inr (.inr (.inl q)))
  change simulateQ (treeSimLoggedWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C))) =
    treeSimLoggedWorld prims D (.inr (.inr (.inl q))) at he
  rw [he] at hr
  change r ∈ support ((fun a : HashOutput × (HashCache C × HiddenCache C) =>
    (a.1, a.2, s.2 ++ [⟨.inr (.inr (.inl q)), a.1⟩])) <$>
      (streamWorld prims D (.inr (.inr (.inl q)))).run s.1) at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  change u ∈ support ((fun r : HashOutput × HashCache C => (r.1, (r.2, s.1.2))) <$>
    (hashAnswer prims q).run s.1.1) at hu
  simp only [support_map, Set.mem_image] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact hashAnswer_cached prims hq s.1.1 v hv

/-- All answers of a free hash traversal stay in the final cache. -/
theorem free_hashes_cached {ι : Type} (qs : ι → Query C) (hq : ∀ i, ¬ IsFixed (qs i)) (xs : List ι)
    (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (xs.mapM fun i => hashQuery (qs i)) (LocalSpec C)))).run s)) :
    List.Forall₂ (fun i h => r.2.1.1 (qs i) = some h) xs r.1 := by
  induction xs generalizing s r with
  | nil =>
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact .nil
  | cons i xs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hr
    have hmono : a.2.1.1 ≤ b.2.1.1 := free_mono prims D _ a.2 b hb
    exact .cons (hmono (free_hash_cached prims D (qs i) (hq i) s a ha)) (ih a.2 b hb)

theorem commit_not_fixed (phase : Phase) (j i : C.Party) (reveal : List HashOutput) :
    ¬ IsFixed (Query.commit phase j i reveal) := by
  rintro ⟨input, h, -⟩
  cases h

/-- A successful reveal row caches the opening of each commitment at the committed value. -/
theorem revealData_cached (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (s : TreeSimState C) (r : Option (PrssKeys C × List HashOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealData i own committed revealed))).run s)) :
    ∀ row, r.1 = some row → ∀ j, j ≠ i →
      r.2.1.1 (.commit .prss j i (Msg.hashesOf (revealed j))) =
        some ((Msg.hashesOf (committed j)).getD 0 0) := by
  unfold prssRevealData at hr
  split_ifs at hr with ha
  · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    intro row he
    cases he
  · unfold prssPostRevealData at hr
    simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨opens, hopens, hr⟩ := hr
    split_ifs at hr with hc
    · simp only [free_bind, free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨keys, hkeys, shared, hshared, rfl⟩ := hr
      intro row _ j hji
      have hall := free_hashes_cached prims D
        (fun j => Query.commit .prss j i (Msg.hashesOf (revealed j)))
        (fun j => commit_not_fixed _ _ _ _) C.parties s opens hopens
      have hj := forall₂_getD_idxOf _ _ _ hall j (by simp [Committee.parties]) 0
      have hle := (free_mono prims D _ opens.2 keys hkeys).trans
        (free_mono prims D _ keys.2 shared hshared)
      have hv : opens.1.getD j.val 0 = (Msg.hashesOf (committed j)).getD 0 0 := by
        rw [← (hc j hji).2]
        rfl
      rw [← hv]
      exact hle (by simpa [Committee.parties] using hj)
    · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      intro row he
      cases he

/-- The opening point of the commitment from `j` that `i` checks in the reveal round. -/
abbrev revealPoint (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent : C.Party → Mail C E) (i j : C.Party) : Query C :=
  .commit .prss j i (Msg.hashesOf (prssRevealInbox D active parts sent i j))

/-- Each successful reveal row caches each opening at its committed value. -/
theorem revealRows_cached (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : TreeSimState C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent))).run s)) :
    ∀ i row, r.1 i = some row → ∀ j, j ≠ i →
      r.2.1.1 (revealPoint D active parts sent i j) =
        some ((Msg.hashesOf (committed i j)).getD 0 0) := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.1.1 ≤ t.1.1
    le_refl := fun _ => le_rfl
    le_trans := fun _ _ _ => le_trans }
  rw [prssRevealRows, free_sequenceFin, simulateQ_sequenceFin] at hr
  apply (sequenceFin_state_post _
    (fun i out st => ∀ row, out = some row → ∀ j, j ≠ i →
      st.1.1 (revealPoint D active parts sent i j) =
        some ((Msg.hashesOf (committed i j)).getD 0 0)) ?_ ?_ s r hr).2
  · intro i st result hresult
    refine ⟨free_mono prims D _ st result hresult, ?_⟩
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hresult
      subst result
      intro row he
      cases he
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        exact revealData_cached prims D i (parts i) (committed i) _ st result hresult
      · simp only [if_neg hi, if_neg ha, free_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hresult
        subst result
        intro row he
        cases he
  · intro i out st next hle h row he j hji
    exact hle (h row he j hji)

/-- A corrupt commitment point that no honest operator opens in the reveal round. -/
def StrayCommit (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent : C.Party → Mail C E) (q : Query C) : Prop :=
  CorruptCommit D q ∧ ∀ i j, q ≠ revealPoint D active parts sent i j

/-- The reveal round makes no free query at a stray commitment point. -/
theorem revealRows_stray_zero (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    IsQueryBoundP (prssRevealRows D active parts committed sent)
      (FreeHashIn (StrayCommit D active parts sent)) 0 := by
  have hP : ∀ q, StrayCommit D active parts sent q → TreeSimHashBudgetDomain q ∧ ¬ IsFixed q := by
    rintro q ⟨⟨j, i, reveal, rfl, -⟩, -⟩
    exact ⟨by simp [TreeSimHashBudgetDomain], commit_not_fixed _ _ _ _⟩
  unfold prssRevealRows
  refine isQueryBoundP_sequenceFin (p := FreeHashIn (StrayCommit D active parts sent)) _
    fun i => ?_
  split_ifs with hi ha
  · trivial
  · unfold prssRevealData
    split_ifs with hab
    · trivial
    · unfold prssPostRevealData
      refine isQueryBoundP_bind (n := 0) (m := 0) (hashes_freeHashIn_zero _ _ _ ?_) fun opens _ => ?_
      · intro j _ hj
        exact hj.2 i j rfl
      · split_ifs
        · refine isQueryBoundP_bind (n := 0) (m := 0) (derive_freeHashIn_zero _ hP _ _ _)
            fun keys _ => ?_
          refine isQueryBoundP_bind (n := 0) (m := 0) (hashes_freeHashIn_zero _ _ _ ?_)
            fun _ _ => isQueryBoundP_pure _ _ _
          rintro j - ⟨⟨j', i', reveal, he, -⟩, -⟩
          cases he
        · trivial
  · trivial

end Cache

section Finish

variable {C : Committee} {E : Type} (D : C.Coalition)

/-! `setupFinishResult`, `setupFinish_local` and `setupFinish_round` are private in
`TreeSetupKeys.lean`. They are copied here verbatim. -/

private def setupFinishResult
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) : Option (PrssKeys C) :=
  if i ∈ D.1 then none else
    match rows i with
    | none => none
    | some row =>
      let inbox := fun j => if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [row.2.getD j.val 0]
        then some row.1 else none

private theorem setupFinish_local
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (fun j => prssFinishStep j (rows j)) sent i =
      pure (.done (setupFinishResult D rows sent i)) := by
  by_cases hi : i ∈ D.1
  · cases hrow : rows i <;> simp [roundLocal, prssFinishStep, hrow, hi, setupFinishResult]
  · cases hrow : rows i with
    | none => simp [roundLocal, prssFinishStep, hrow, hi, setupFinishResult]
    | some row =>
      simp only [roundLocal, hrow, prssFinishStep, if_neg hi]
      let inbox : Mail C E := fun j => if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i
      change advance (exchangeResume (fun received => do
        require (∀ j, j ≠ i → Msg.hashesOf (received j) = [row.2.getD j.val 0])
        pure row.1) inbox) = pure (.done (setupFinishResult D rows sent i))
      simp only [setupFinishResult, if_neg hi, hrow]
      change _ = (pure (Step.done (C := C) (E := E) (G := RealSpec)
        (if C.parties.any (fun j => Msg.isAbort (inbox j)) then none
        else if ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [row.2.getD j.val 0]
          then some row.1 else none)) : OracleComp (LocalSpec C) _)
      rw [exchangeResume]
      by_cases ha : C.parties.any (fun j => Msg.isAbort (inbox j)) = true
      · simp only [if_pos ha]
        rfl
      · simp only [if_neg ha]
        rw [advance_require_bind]
        split_ifs <;> rfl

/-- The final setup round only exchanges and checks the recorded echo hashes. -/
private theorem setupFinish_round (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (rows : C.Party → Option (PrssKeys C × List HashOutput)) :
    stepRound worldRoles D A noFunctionality state (fun i => prssFinishStep i (rows i)) = (do
      let adv ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (prssFinishStep i (rows i)).outbox c else none)
      pure (adv.1, fun i => Step.done (C := C) (E := E) (G := RealSpec)
        (setupFinishResult D rows adv.2 i), adv.2)) := by
  rw [stepRound_real]
  apply bind_congr
  rintro ⟨state', sent⟩
  dsimp only
  rw [show roundLocal D (fun i => prssFinishStep i (rows i)) sent =
    (fun i => pure (.done (setupFinishResult D rows sent i))) from
      funext (setupFinish_local D rows sent)]
  simp only [sequenceFin_pure, free_pure, pure_bind]

/-- A successful echo round needs a reveal row of each honest operator, because an honest operator
with no row sends an abort frame. -/
theorem setupFinishResult_rows (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) (ki : PrssKeys C)
    (hi : setupFinishResult D rows sent i = some ki) (j : C.Party) (hj : j ∉ D.1) :
    rows j ≠ none := by
  intro hrow
  unfold setupFinishResult at hi
  split_ifs at hi with hcorrupt
  cases hrowi : rows i with
  | none => simp [hrowi] at hi
  | some row =>
    simp only [hrowi] at hi
    split_ifs at hi with ha
    apply ha
    refine List.any_eq_true.mpr ⟨j, List.mem_finRange j, ?_⟩
    simp [hj, hrow, prssFinishStep, Step.delivered, Msg.isAbort]

/-- The echo round of the setup. An honest output needs a reveal row of each honest operator, and
the round adds no free log entry of `H`. -/
theorem finish_facts (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (s : TreeSimState C)
    (y : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hy : y ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality 1 state
        (fun i => prssFinishStep i (rows i)))).run s)) :
    (∀ i, y.1.2 i ≠ none → ∀ j, j ∉ D.1 → rows j ≠ none) ∧
      ∀ q h, freeEntry q h ∈ y.2.2 → freeEntry q h ∈ s.2 := by
  rw [executeRounds] at hy
  split_ifs at hy with hd
  · simp only [prssFinishStep_output, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hy
    subst y
    exact ⟨fun i hi => (hi rfl).elim, fun _ _ h => h⟩
  · rw [setupFinish_round] at hy
    simp only [bind_assoc, pure_bind, executeRounds, Step.output, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hy
    obtain ⟨adv, hadv, rfl⟩ := hy
    refine ⟨fun i hi j hj => ?_, fun q h hq => ?_⟩
    · obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp hi
      exact setupFinishResult_rows D rows adv.1.2 i ki hki j hj
    · refine logged_adversary_inv prims D (fun s' => ∀ q h, freeEntry q h ∈ s'.2 → freeEntry q h ∈ s.2)
        (fun t s' hs' r hr q h hq => ?_) _ s (fun _ _ h => h) adv hadv q h hq
      rw [logged_step_log prims D _ s' r hr, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | hq
      · exact hs' q h hq
      · cases hq

end Finish

section Core

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

theorem prefix_before_of_not_mem {α : Type} {pre before after : List α} {e : α}
    (h : pre <+: before ++ e :: after) (he : e ∉ pre) : pre <+: before := by
  have hb : before ++ [e] <+: before ++ e :: after := ⟨after, by simp⟩
  rcases List.prefix_or_prefix_of_prefix h hb with h1 | h1
  · rcases List.prefix_concat_iff.mp h1 with h2 | h2
    · exact (he (by simp [h2])).elim
    · exact h2
  · exact (he (h1.subset (by simp))).elim

/-- Each free entry of `H` at a corrupt commitment point after the reveal round is an opening. -/
theorem revealRows_entries (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : TreeSimState C) (hs : SetupFresh D s)
    (x : (C.Party → Option (PrssKeys C × List HashOutput)) × TreeSimState C)
    (hx : x ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent))).run s)) :
    ∀ q h, CorruptCommit D q → freeEntry q h ∈ x.2.2 →
      ∃ i j, q = revealPoint D active parts sent i j := by
  refine logged_free_inv prims D (FreeHashIn (StrayCommit D active parts sent))
    (fun s' => ∀ q h, CorruptCommit D q → freeEntry q h ∈ s'.2 →
      ∃ i j, q = revealPoint D active parts sent i j)
    (fun t ht s' hs' r hr q h hq hmem => ?_) _ (revealRows_stray_zero D active parts committed sent)
    s (fun q h hq hmem => (hs.2 q h hq hmem).elim) x hx
  rw [logged_step_log prims D _ s' r hr, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact hs' q h hq hmem
  · have he : t = .inr (.inl q) := by
      have := congrArg Sigma.fst hmem
      simp only [Sum.inr.injEq] at this
      exact this.symm
    by_contra hn
    push Not at hn
    exact ht ⟨q, ⟨hq, hn⟩, he⟩

/-- The setup event of the uncounted branch. An honest operator ends the setup with keys, and an
honest operator opened a corrupt commitment with no counted query of its point before. -/
def SetupGuessEvent {σ : Type} (D : C.Coalition)
    (p : (σ × (C.Party → Option (PrssKeys C))) × TreeSimState C) : Prop :=
  (∃ i, i ∉ D.1 ∧ p.1.2 i ≠ none) ∧ TreeCheckUncounted D p.2.2

/-- The reveal and echo rounds from a fresh state. If some opening point has no counted query,
then one such pair, fixed by the state before the openings, pays one guess of a fresh answer of
`H`. Otherwise no opening is uncounted. -/
theorem rows_finish_guess (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (state : A.State)
    (s : TreeSimState C) (hs : SetupFresh D s) :
    Pr[SetupGuessEvent D | (simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent) >>= fun rows =>
        executeRounds worldRoles D A noFunctionality 1 state
          (fun i => prssFinishStep i (rows i)))).run s] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [simulateQ_bind, StateT.run_bind]
  rcases Classical.em (∃ i j, i ∉ D.1 ∧ j ∈ D.1 ∧
      ∀ h, countedEntry (revealPoint D active parts sent i j) h ∉ s.2) with hU | hU
  · obtain ⟨i, j, hi, hj, hfresh⟩ := hU
    have hP : CorruptCommit D (revealPoint D active parts sent i j) := ⟨j, i, _, rfl, hj, hi⟩
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    calc _ ≤ Pr[fun x => x.1 i ≠ none | (simulateQ (treeSimLoggedWorld prims D)
          (free (prssRevealRows D active parts committed sent))).run s] := by
          refine probEvent_bind_le_probEvent fun x _ hn => probEvent_eq_zero fun y hy hev => ?_
          obtain ⟨⟨k, hk, hkey⟩, -⟩ := hev
          exact (finish_facts D prims A state x.1 x.2 y hy).1 k hkey i hi (not_not.mp hn)
      _ ≤ Pr[fun x => x.2.1.1 (revealPoint D active parts sent i j) =
            some ((Msg.hashesOf (committed i j)).getD 0 0) | (simulateQ (treeSimLoggedWorld prims D)
          (free (prssRevealRows D active parts committed sent))).run s] := by
          refine probEvent_mono fun x hx hne => ?_
          obtain ⟨row, hrow⟩ := Option.ne_none_iff_exists'.mp hne
          exact revealRows_cached prims D active parts committed sent s x hx i row hrow j hji
      _ ≤ guessWeight (revealPoint D active parts sent i j)
            ((Msg.hashesOf (committed i j)).getD 0 0) s.1.1 := guess_free_probEvent_le prims D _ _ _ s
      _ = _ := guessWeight_of_open (hs.1 _ hP hfresh)
  · push Not at hU
    refine le_of_eq_of_le (probEvent_eq_zero fun y hy hev => ?_) zero_le
    rw [mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨-, before, after, j, i, reveal, h, hlog, hj, hi, hnone⟩ := hev
    have hmem : freeEntry (.commit .prss j i reveal) h ∈ y.2.2 := by
      rw [hlog]
      simp
    have hcc : CorruptCommit D (Query.commit .prss j i reveal) := ⟨j, i, reveal, rfl, hj, hi⟩
    obtain ⟨i', j', hq⟩ := revealRows_entries prims D active parts committed sent s hs x hx _ h hcc
      ((finish_facts D prims A state x.1 x.2 y hy).2 _ h hmem)
    simp only [revealPoint, Query.commit.injEq, true_and] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    obtain ⟨h0, h0mem⟩ := hU i j hi hj
    have hpre : s.2 <+: y.2.2 := (treeSimLoggedWorld_prefix prims D _ s x hx).trans
      (treeSimLoggedWorld_prefix prims D _ x.2 y hy)
    rw [hlog] at hpre
    have hbefore := prefix_before_of_not_mem hpre (hs.2 _ h hcc)
    exact hnone h0 (hbefore.subset h0mem)

/-- The whole PRSS setup pays at most one guess for the uncounted branch. -/
theorem treeSaltSetup_guess (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) :
    Pr[SetupGuessEvent D | treeSaltSetup prims D A x z] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  unfold treeSaltSetup
  refine probEvent_bind_le_of_forall_le fun start hstart => ?_
  have hs0 : SetupFresh D start.2 :=
    logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D) _ _
      (setupFresh_empty D) start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase]
  change Pr[SetupGuessEvent D | (simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) start.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run start.2] ≤ _
  rw [executePhase_prssSetup_prefix]
  simp only [simulateQ_bind, StateT.run_bind]
  refine probEvent_bind_le_of_forall_le fun data hdata => ?_
  have hs1 : SetupFresh D data.2 :=
    logged_free_inv prims D (FreeCorruptQuery D) (SetupFresh D) (setupFresh_free prims D) _
      (prssInitialData_freeCorrupt_zero D) _ hs0 data hdata
  refine probEvent_bind_le_of_forall_le fun adv hadv => ?_
  have hs2 : SetupFresh D adv.2 :=
    logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D) _ _ hs1 adv hadv
  split_ifs with habort
  · refine le_of_eq_of_le (probEvent_eq_zero fun y hy hev => ?_) zero_le
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hy
    subst y
    obtain ⟨⟨k, -, hk⟩, -⟩ := hev
    exact hk rfl
  · simp only [simulateQ_bind, StateT.run_bind]
    refine probEvent_bind_le_of_forall_le fun adv' hadv' => ?_
    have hs3 : SetupFresh D adv'.2 :=
      logged_adversary_inv prims D (SetupFresh D) (setupFresh_counted prims D) _ _ hs2 adv' hadv'
    have h := rows_finish_guess prims D A
      (fun i => (C.parties.any fun j => Msg.isAbort (prssCommitInbox D data.1 adv.1.2 i j)) = false)
      (fun i => (data.1 i).1) (prssCommitInbox D data.1 adv.1.2) adv'.1.2 adv'.1.1 adv'.2 hs3
    simpa only [simulateQ_bind, StateT.run_bind] using h

end Core

section Split

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The program of the audited run after the PRSS setup, with the batches and the
distinguisher. -/
def auditAfterProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State)
    (keys : C.Party → Option (PrssKeys C)) :
    OracleComp (WorldSpec C) (Bool × (A.State ×
      (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) := do
  let next ← free (Concrete.sequenceFin fun i => continueStep
    (fun prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
    (.done (keys i)))
  let out ← executeRounds worldRoles D A noFunctionality (ceremonyFuel circuits settings - 3)
    state next
  let b ← worldRoles.adversary (Z (out.1, fun i => (out.2 i).map Prod.fst))
  pure (b, out)

/-- The logged audited run is the PRSS setup followed by the rest of the run. -/
theorem treeCheckAudited_split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z) =
      (fun r => (r.1, r.2.2)) <$> (treeSaltSetup prims D A x z >>= fun p =>
        (simulateQ (treeSimLoggedWorld prims D)
          (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2) := by
  obtain ⟨fuel, hf⟩ : ∃ fuel, ceremonyFuel circuits settings = fuel + 3 :=
    ⟨ceremonyFuel circuits settings - 3, by simp only [ceremonyFuel, setupRounds]; omega⟩
  have hc : (fun i => treeSimCheckCeremonyAudit K circuits settings i (x i) top tree) =
      fun i => prssSetup i >>= fun prss =>
        treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree := rfl
  rw [treeSimLoggedRun_eq_run]
  unfold treeSimCheckAuditedGame realExecution treeSaltSetup auditAfterProgram
  simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_assoc]
  apply bind_congr
  intro start
  rw [hf, hc, executePhase_prssSetup_bind]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_executePhase, treeSimRealRoles,
    Nat.add_sub_cancel]
  rfl

theorem executeRounds_all_done {m : Type → Type} [Monad m] {I O Ia L R α : Type}
    (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (h : ∀ i, i ∉ D.1 → (steps i).isDone) :
    executeRounds Ro D A F fuel state steps = pure (state, fun i => (steps i).output) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [executeRounds, if_pos h]

set_option linter.constructorNameAsVariable false in
/-- With no honest PRSS keys, no honest operator gives an output after the setup. -/
theorem auditAfter_none (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State)
    (keys : C.Party → Option (PrssKeys C)) (hkeys : ∀ i, i ∉ D.1 → keys i = none)
    (s : TreeSimState C) (y : _ × TreeSimState C)
    (hy : y ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (auditAfterProgram K circuits settings top tree D A x Z state keys)).run s)) :
    ∀ i, i ∉ D.1 → y.1.2.2 i = none := by
  unfold auditAfterProgram at hy
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨next, hnext, out, hout, b, hb, hy⟩ := hy
  letI : Preorder (TreeSimState C) := {
    le := fun _ _ => True
    le_refl := fun _ => trivial
    le_trans := fun _ _ _ _ _ => trivial }
  rw [free_sequenceFin, simulateQ_sequenceFin] at hnext
  have hdone := (sequenceFin_state_post _ (fun i out _ => i ∉ D.1 → out = Step.done none)
    (fun i st r hr => ⟨trivial, fun hi => by
      rw [hkeys i hi] at hr
      simp only [continueStep, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hr
      rw [hr]⟩) (fun _ _ _ _ _ h => h) s next hnext).2
  rw [executeRounds_all_done _ D A _ _ _ _ (fun i hi => by rw [hdone i hi]; trivial)] at hout
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hout hy
  subst hout
  subst hy
  intro i hi
  change (next.1 i).output = none
  rw [hdone i hi]
  rfl

/-- The honest programs after the PRSS setup make no free query at a corrupt commitment point.
Only `commitRevealEcho` queries `.commit`, and the audited continuation runs no setup. -/
def TreeCheckAfterSetupNoCommit : Prop :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State)
    (keys : C.Party → Option (PrssKeys C)) (s : TreeSimState C),
    ∀ y ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (auditAfterProgram K circuits settings top tree D A x Z state keys)).run s),
      ∀ q h, CorruptCommit D q → freeEntry q h ∈ y.2.2 → freeEntry q h ∈ s.2

theorem list_first_mem {α : Type} {l : List α} {e : α} (h : e ∈ l) :
    ∃ b a, l = b ++ e :: a ∧ e ∉ b := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases Classical.em (x = e) with hx | hx
    · exact ⟨[], l, by rw [hx]; rfl, by simp⟩
    · obtain ⟨b, a, rfl, hb⟩ := ih (by simpa [Ne.symm hx] using h)
      exact ⟨x :: b, a, rfl, by simp [Ne.symm hx, hb]⟩

/-- An uncounted opening in a log extends to an uncounted opening in its prefix, when the prefix
holds the opening entry. -/
theorem treeCheckUncounted_prefix (D : C.Coalition) {pre log : TreeSimLog C} (hpre : pre <+: log)
    (h : TreeCheckUncounted D log)
    (hin : ∀ q h, CorruptCommit D q → freeEntry q h ∈ log → freeEntry q h ∈ pre) :
    TreeCheckUncounted D pre := by
  obtain ⟨before, after, j, i, reveal, u, hlog, hj, hi, hnone⟩ := h
  have hmem := hin _ u ⟨j, i, reveal, rfl, hj, hi⟩ (by rw [hlog]; simp)
  obtain ⟨b, a, hb, hnb⟩ := list_first_mem hmem
  have hbpre : b <+: log := (List.prefix_append b _).trans (hb ▸ hpre)
  rw [hlog] at hbpre
  have hbb := prefix_before_of_not_mem hbpre hnb
  exact ⟨b, a, j, i, reveal, u, hb, hj, hi, fun h' hh => hnone h' (hbb.subset hh)⟩

theorem guess_le_bound :
    (2 ^ 256 : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ 256) := by
  have he : (2 ^ 256 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 256) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.inv_pow]
    simp
  rw [he]
  exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (by positivity) (by norm_num))

/-- `TreeCheckUncountedGuess` from the absence of commitment queries after the setup. -/
theorem treeCheckUncountedGuess_of_noCommit
    (noCommit : TreeCheckAfterSetupNoCommit prims K circuits settings) :
    TreeCheckUncountedGuess prims K circuits settings := by
  intro _ top tree D A x z Z q _ _ _ j
  rw [treeCheckAudited_split, probEvent_map]
  refine le_trans ?_ ((treeSaltSetup_guess prims D A x z).trans guess_le_bound)
  refine probEvent_bind_le_probEvent fun p hp hng => probEvent_eq_zero fun y hy hev => hng ?_
  obtain ⟨⟨-, ⟨-, _, _, _, i, value, records, -, -, -, -, -, hi, hout, -⟩⟩, hunc⟩ := hev
  refine ⟨?_, treeCheckUncounted_prefix D (treeSimLoggedWorld_prefix prims D _ p.2 y hy) hunc
    (noCommit top tree D A x Z p.1.1 p.1.2 p.2 y hy)⟩
  by_contra hn
  push Not at hn
  have := auditAfter_none prims K circuits settings top tree D A x Z p.1.1 p.1.2 hn p.2 y hy i hi
  rw [this] at hout
  cases hout

end Split

section Lift

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)

open TreeSimHashCount in
/-- Each step in the support of `advance` keeps a zero budget. -/
theorem advance_stepBudget {α : Type} (Q : (LocalSpec C).Domain → Prop)
    (oa : OracleComp (PartySpec C E RealSpec) (Option α))
    (h : IsQueryBoundP oa (PartyQuery Q (E := E) (G := RealSpec)) 0) :
    ∀ st ∈ support (advance oa), StepBudget Q st 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st hst
    rw [advance_pure, mem_support_pure_iff] at hst
    subst st
    trivial
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · intro st hst
      rw [advance_query_bind, mem_support_bind_iff] at hst
      obtain ⟨u, -, hst⟩ := hst
      exact ih u (by simpa using h.2 u) st hst
    · intro st hst
      change st ∈ support (pure (Step.wait outbox f) : OracleComp (LocalSpec C) _) at hst
      rw [mem_support_pure_iff] at hst
      subst st
      simpa [StepBudget, PartyQuery] using h.2
    · exact input.elim

open TreeSimHashCount in
/-- `advance` keeps a zero budget of local queries. -/
theorem advance_zero {α : Type} (Q : (LocalSpec C).Domain → Prop)
    (oa : OracleComp (PartySpec C E RealSpec) (Option α))
    (h : IsQueryBoundP oa (PartyQuery Q (E := E) (G := RealSpec)) 0) :
    IsQueryBoundP (advance oa) Q 0 := by
  have hb := advance_bind_regionBound (P := Q) oa pure 0 0 h
    (fun _ _ _ _ => isQueryBoundP_pure _ _ _)
  simpa using hb

/-- The result of a free computation on the logged world is in the support of the computation. -/
theorem free_support {α : Type} (oa : OracleComp (LocalSpec C) α) (s : TreeSimState C)
    (x : α × TreeSimState C)
    (hx : x ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free oa)).run s)) :
    x.1 ∈ support oa := by
  let I : QueryImpl (SimulatorSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inl t)
  let impl : QueryImpl (LocalSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inr t)
  have hsplit : treeSimLoggedWorld prims D = I + impl := by
    funext t
    rcases t with t | t <;> rfl
  rw [hsplit, simulateQ_free] at hx
  apply support_simulateQ_run'_subset impl oa s
  rw [StateT.run'_eq, support_map]
  exact ⟨x, hx, rfl⟩

/-- No free entry of `H` at a corrupt commitment point is new since `s0`. -/
def NoNewFree (D : C.Coalition) (s0 s : TreeSimState C) : Prop :=
  ∀ q h, CorruptCommit D q → freeEntry q h ∈ s.2 → freeEntry q h ∈ s0.2

theorem noNewFree_counted (s0 : TreeSimState C) (t : (LocalSpec C).Domain) (s : TreeSimState C)
    (hs : NoNewFree D s0 s) (r : (WorldSpec C).Range (.inl (.inl t)) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl t))).run s)) :
    NoNewFree D s0 r.2 := by
  intro q h hq hmem
  rw [logged_step_log prims D _ s r hr, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact hs q h hq hmem
  · cases hmem

theorem noNewFree_free (s0 : TreeSimState C) (t : (LocalSpec C).Domain)
    (ht : ¬ FreeCorruptQuery D t) (s : TreeSimState C)
    (hs : NoNewFree D s0 s) (r : (WorldSpec C).Range (.inr t) × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s)) :
    NoNewFree D s0 r.2 := by
  intro q h hq hmem
  rw [logged_step_log prims D _ s r hr, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact hs q h hq hmem
  · have he : t = .inr (.inl q) := by
      have := congrArg Sigma.fst hmem
      simp only [Sum.inr.injEq] at this
      exact this.symm
    exact (ht ⟨q, hq, he⟩).elim

open TreeSimHashCount in
/-- One round of the real network adds no free entry at a corrupt commitment point and keeps a
zero budget of each step. -/
theorem round_noNewFree {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget (FreeCorruptQuery D) (steps i) 0)
    (s0 s : TreeSimState C) (hs : NoNewFree D s0 s)
    (y : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (hy : y ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state steps)).run s)) :
    NoNewFree D s0 y.2 ∧ ∀ i, StepBudget (FreeCorruptQuery D) (y.1.2.1 i) 0 := by
  rw [stepRound_real] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hy
  obtain ⟨adv, hadv, nxt, hnxt, rfl⟩ := hy
  have hs1 := logged_adversary_inv prims D (NoNewFree D s0) (noNewFree_counted prims D s0) _ s hs
    adv hadv
  have hlocal : ∀ i, IsQueryBoundP (roundLocal D steps adv.1.2 i) (FreeCorruptQuery D) 0 := by
    intro i
    unfold roundLocal
    cases h : steps i with
    | done out => trivial
    | wait outbox resume =>
      have hb := hsteps i
      rw [h] at hb
      dsimp only
      split_ifs
      · trivial
      · exact advance_zero _ _ (hb _)
    | call input _ => exact input.elim
  refine ⟨logged_free_inv prims D (FreeCorruptQuery D) (NoNewFree D s0)
    (noNewFree_free prims D s0) _ (isQueryBoundP_sequenceFin _ hlocal) adv.2 hs1 nxt hnxt, ?_⟩
  letI : Preorder (TreeSimState C) := {
    le := fun _ _ => True
    le_refl := fun _ => trivial
    le_trans := fun _ _ _ _ _ => trivial }
  rw [free_sequenceFin, simulateQ_sequenceFin] at hnxt
  refine (sequenceFin_state_post _ (fun _ out _ => StepBudget (FreeCorruptQuery D) out 0)
    (fun i st r hr => ⟨trivial, ?_⟩) (fun _ _ _ _ _ h => h) adv.2 nxt hnxt).2
  have hsup := free_support prims D _ st r hr
  revert hsup
  unfold roundLocal
  cases h : steps i with
  | done out =>
    intro hsup
    rw [mem_support_pure_iff] at hsup
    rw [hsup]
    trivial
  | wait outbox resume =>
    have hb := hsteps i
    rw [h] at hb
    dsimp only
    split_ifs
    · intro hsup
      rw [mem_support_pure_iff] at hsup
      rw [hsup]
      trivial
    · exact advance_stepBudget _ _ (hb _) r.1
  | call input _ => exact input.elim

open TreeSimHashCount in
/-- The real network adds no free entry at a corrupt commitment point when each honest step
keeps a zero budget. -/
theorem executeRounds_noNewFree {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (s0 : TreeSimState C) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α) (s : TreeSimState C),
      (∀ i, StepBudget (FreeCorruptQuery D) (steps i) 0) → NoNewFree D s0 s →
      ∀ y ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality fuel state steps)).run s),
        NoNewFree D s0 y.2
  | 0, state, steps, s, _, hs, y, hy => by
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hy
    subst y
    exact hs
  | fuel + 1, state, steps, s, hsteps, hs, y, hy => by
    rw [executeRounds] at hy
    split_ifs at hy
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hy
      subst y
      exact hs
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
      obtain ⟨r, hr, hy⟩ := hy
      obtain ⟨hs', hsteps'⟩ := round_noNewFree prims D A state steps hsteps s0 s hs r hr
      exact executeRounds_noNewFree A s0 fuel r.1.1 r.1.2.1 r.2 hsteps' hs' y hy

end Lift


section AfterLift

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A commitment query of `H`. -/
def IsCommit (q : Query C) : Prop := ∃ phase j i reveal, q = .commit phase j i reveal

/-- The audited honest program after the PRSS setup makes no commitment query. Only
`commitRevealEcho` queries `.commit`. -/
def TreeCheckAfterSetupAuditNoCommit : Prop :=
  ∀ (ctx : Context C) (top : TopTree) (tree : Tree),
    TreeSimHashCount.PartyBudget (E := E) (FreeHashIn IsCommit)
      (treeSimCheckAfterSetupAudit K circuits settings ctx top tree) 0

open TreeSimHashCount in
theorem continueStep_noNewFree {α β : Type} (D : C.Coalition)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hk : ∀ i a, PartyBudget (FreeCorruptQuery D) (k i a) 0) (keys : C.Party → Option α)
    (s0 : TreeSimState C) (hs : NoNewFree D s0 s0) (y : (C.Party → Step C E RealSpec β) × TreeSimState C)
    (hy : y ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (Concrete.sequenceFin fun i => continueStep (k i) (.done (keys i))))).run s0)) :
    NoNewFree D s0 y.2 ∧ ∀ i, StepBudget (FreeCorruptQuery D) (y.1 i) 0 := by
  have hlocal : ∀ i, IsQueryBoundP (continueStep (k i) (.done (keys i))) (FreeCorruptQuery D) 0 := by
    intro i
    cases keys i with
    | none => trivial
    | some a => exact advance_zero _ _ (hk i a)
  refine ⟨logged_free_inv prims D (FreeCorruptQuery D) (NoNewFree D s0)
    (noNewFree_free prims D s0) _ (isQueryBoundP_sequenceFin _ hlocal) s0 hs y hy, ?_⟩
  letI : Preorder (TreeSimState C) := {
    le := fun _ _ => True
    le_refl := fun _ => trivial
    le_trans := fun _ _ _ _ _ => trivial }
  rw [free_sequenceFin, simulateQ_sequenceFin] at hy
  refine (sequenceFin_state_post _ (fun _ out _ => StepBudget (FreeCorruptQuery D) out 0)
    (fun i st r hr => ⟨trivial, ?_⟩) (fun _ _ _ _ _ h => h) s0 y hy).2
  have hsup := free_support prims D _ st r hr
  revert hsup
  cases keys i with
  | none =>
    intro hsup
    simp only [continueStep, mem_support_pure_iff] at hsup
    rw [hsup]
    trivial
  | some a => exact advance_stepBudget _ _ (hk i a) r.1

set_option linter.constructorNameAsVariable false in
theorem treeCheckAfterSetupNoCommit_of_audit
    (audit : TreeCheckAfterSetupAuditNoCommit (E := E) K circuits settings) :
    TreeCheckAfterSetupNoCommit prims K circuits settings := by
  intro top tree D A x Z state keys s y hy
  have hk : ∀ i prss, TreeSimHashCount.PartyBudget (E := E) (FreeCorruptQuery D)
      (treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree) 0 := by
    intro i prss
    refine IsQueryBoundP.of_imp (fun t ht => ?_) (audit ⟨i, x i, prss⟩ top tree)
    rcases t with (t | _) | _
    · obtain ⟨q, ⟨j, i', reveal, rfl, -⟩, he⟩ := ht
      exact ⟨_, ⟨.prss, j, i', reveal, rfl⟩, he⟩
    · exact ht.elim
    · exact ht.elim
  unfold auditAfterProgram at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hy
  obtain ⟨next, hnext, out, hout, b, hb, hy⟩ := hy
  obtain ⟨hs1, hsteps⟩ := continueStep_noNewFree prims D _ hk keys s (fun _ _ _ h => h) next hnext
  generalize ceremonyFuel circuits settings - 3 = fuel at hout
  have hs2 := executeRounds_noNewFree prims D A s fuel state next.1 next.2 hsteps hs1 out hout
  have hs3 := logged_adversary_inv prims D (NoNewFree D s) (noNewFree_counted prims D s) _ _ hs2 b hb
  rw [hy]
  exact hs3

/-- `TreeCheckUncountedGuess` from the absence of commitment queries in the audited honest
program after the setup. -/
theorem treeCheckUncountedGuess_of_audit
    (audit : TreeCheckAfterSetupAuditNoCommit (E := E) K circuits settings) :
    TreeCheckUncountedGuess prims K circuits settings :=
  treeCheckUncountedGuess_of_noCommit prims K circuits settings
    (treeCheckAfterSetupNoCommit_of_audit prims K circuits settings audit)

end AfterLift

/-- info: 'ThresholdLeanXmssSecurity.treeSaltSetup_guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltSetup_guess

/-- info: 'ThresholdLeanXmssSecurity.treeCheckUncountedGuess_of_noCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckUncountedGuess_of_noCommit

/-- info: 'ThresholdLeanXmssSecurity.treeCheckUncountedGuess_of_audit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckUncountedGuess_of_audit

end ThresholdLeanXmssSecurity
