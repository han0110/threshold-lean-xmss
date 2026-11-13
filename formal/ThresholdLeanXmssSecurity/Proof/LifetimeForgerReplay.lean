import ThresholdLeanXmssSecurity.Proof.LifetimeO3Bridge

/-!
# The final slot world against the lifetime forger

`LifetimeForgerExplicit` states that the final slot world `S_N` wins with probability at most
`2^layerHeight * searchFailure + lifetimeForgerAdvantage`. In `S_N` every slot is ideal. The
comparison is one-sided.

The proof goes through one fixed world, `precomputeGame`. It is `S_N` with one change. Before the
keygen, it samples the dealing of `F_keygen` and runs `F_tree` for the top tree and for every bottom
tree from the empty cache. Each ideal start reads the output from this table. So the table is built
in the same order as in `tsigGame`. The game returns two bits. The first bit is the bad event, namely
that the search of a bottom tree fails. The second bit is the win of `S_N`.

Each hop Prop takes the premises `CircuitsCompute circuits prims.Th` and `0 < settings.batchSize`.

* `FinalPrecompute` states that `S_N` and `precomputeGame` win with the same probability. It holds
  the lazy-oracle reorder (E1) and the common top tree (E3).
* `PrecomputeSearch` states that the bad event has probability at most
  `2^layerHeight * searchFailure` (E5).
* `PrecomputeReplay` states that a win without the bad event has probability at most
  `lifetimeForgerAdvantage` (E2, E4 and E6). In E4 the private keygen table of `forgerWorld` holds
  only the inputs `.derive .keygen`. The dealer, the signing and the verification never read them, so
  the table agrees with `H` on every point that both runs read.
* `lifetimeForgerExplicit_of_hops` gives `LifetimeForgerExplicit` from the three Props.
* `ForgerQueryBound` (E7) states that `lifetimeForger` makes at most
  `q₀ = Q + lifetimeOverhead C attempts Q` calls of `H` and `PRG` on each path when the lifetime game
  makes at most `Q`.

`SwapPort` holds the commutation of lazy random-oracle queries, ported from VCVio. The pinned
`evalDist` is a sub-probability mass function, so the ported statements have no measurable space.
`evalDist_simulateQ_run_swap` extends the port from one query to a whole computation, and
`evalDist_simulateQ_run_ghost` drops a computation whose output and cache no later step reads.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Commuting queries to the lazy random oracle

The lemmas of this section come from VCVio (Apache 2.0), namely
`VCVio/OracleComp/QueryTracking/RandomOracle/Commute.lean` (Alexander Hicks, lines 1 to 116),
`CachingOracle.lean` (`withCaching_run_caches`) and `Structures.lean` (`cacheQuery_comm`), at the
checkout `/home/han/playground/arg/VCVio`. The pinned VCVio does not have them. The pinned
`evalDist_bind_congr` replaces `evalDist_bind_congr_of_support`. -/

namespace ThresholdLeanXmssSecurity.SwapPort

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- Let `t` be a query, and consider any possible outcome of a `withCaching` step
on `t`. Then the final cache maps `t` to the returned answer. -/
theorem withCaching_run_caches (so : QueryImpl spec₀ ProbComp) (t : spec₀.Domain)
    (cache₀ : QueryCache spec₀) (z) (hz : z ∈ support ((so.withCaching t).run cache₀)) :
    z.2 t = some z.1 := by
  cases ht : cache₀ t with
  | some u =>
    rw [QueryImpl.withCaching_run_some so ht, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ht
  | none =>
    rw [QueryImpl.withCaching_run_none so ht, support_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact QueryCache.cacheQuery_self cache₀ t v

/-- Caching answers at two distinct inputs commutes. -/
theorem cacheQuery_comm (cache : QueryCache spec₀) {t t' : spec₀.Domain} (h : t ≠ t')
    (u : spec₀.Range t) (u' : spec₀.Range t') :
    (cache.cacheQuery t u).cacheQuery t' u' = (cache.cacheQuery t' u').cacheQuery t u := by
  funext s
  by_cases hs : s = t
  · subst hs
    rw [QueryCache.cacheQuery_of_ne _ _ h, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · by_cases hs' : s = t'
    · subst hs'
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne _ _ hs, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hs', QueryCache.cacheQuery_of_ne _ _ hs,
        QueryCache.cacheQuery_of_ne _ _ hs, QueryCache.cacheQuery_of_ne _ _ hs']

/-- Two queries to the lazy random oracle commute: their answers and the final cache have the
same joint distribution in either order. -/
theorem evalDist_run_bind_run_swap {γ : Type} (t t' : ι₀)
    (cache : spec₀.QueryCache)
    (f : spec₀.Range t → spec₀.Range t' → spec₀.QueryCache → ProbComp γ) :
    𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦
        (spec₀.randomOracle t').run z.2 >>= fun y ↦ f z.1 y.1 y.2] =
      𝒟[(spec₀.randomOracle t').run cache >>= fun y ↦
        (spec₀.randomOracle t).run y.2 >>= fun z ↦ f z.1 y.1 z.2] := by
  -- After a query at `t`, a query at `t` is answered from the cache.
  have hit : ∀ {t : ι₀} {c : spec₀.QueryCache} {z}, z ∈ support ((spec₀.randomOracle t).run c) →
      (spec₀.randomOracle t).run z.2 = pure z := fun {t c z} hz ↦ by
    rw [QueryImpl.withCaching_run_some _ (withCaching_run_caches _ _ _ _ hz)]
  have keep : ∀ {t t' : ι₀} {c : spec₀.QueryCache} {v : spec₀.Range t'} {z},
      z ∈ support ((spec₀.randomOracle t).run c) → c t' = some v →
      (spec₀.randomOracle t').run z.2 = pure (v, z.2) := fun {t t' c v z} hz hv ↦
    QueryImpl.withCaching_run_some _ (QueryImpl.withCaching_cache_le _ _ _ _ hz hv)
  by_cases htt : t = t'
  · subst htt
    calc _ = 𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦ f z.1 z.1 z.2] :=
          evalDist_bind_congr fun z hz ↦ by rw [hit hz, pure_bind]
      _ = _ := evalDist_bind_congr fun z hz ↦ by rw [hit hz, pure_bind]
  cases ht : cache t with
  | some v =>
    calc _ = 𝒟[(spec₀.randomOracle t').run cache >>= fun y ↦ f v y.1 y.2] := by
          rw [QueryImpl.withCaching_run_some _ ht, pure_bind]
      _ = _ := evalDist_bind_congr fun z hz ↦ by rw [keep hz ht, pure_bind]
  | none =>
    cases ht' : cache t' with
    | some v' =>
      calc _ = 𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦ f z.1 v' z.2] :=
            evalDist_bind_congr fun z hz ↦ by rw [keep hz ht', pure_bind]
        _ = _ := by rw [QueryImpl.withCaching_run_some _ ht', pure_bind]
    | none =>
      have h₁ : ∀ u, (cache.cacheQuery t u) t' = none := fun u ↦
        (QueryCache.cacheQuery_of_ne _ _ (Ne.symm htt)).trans ht'
      have h₂ : ∀ u', (cache.cacheQuery t' u') t = none := fun u' ↦
        (QueryCache.cacheQuery_of_ne _ _ htt).trans ht
      simp only [QueryImpl.withCaching_run_none _ ht, QueryImpl.withCaching_run_none _ ht',
        QueryImpl.withCaching_run_none _ (h₁ _), QueryImpl.withCaching_run_none _ (h₂ _),
        bind_map_left]
      rw [evalDist_bind_bind_swap]
      simp only [cacheQuery_comm _ htt]

/-- A query to the lazy random oracle commutes with any computation run against the same
oracle: the answer, the computation's output and the final cache have the same joint
distribution in either order. -/
theorem evalDist_run_bind_simulateQ_run_swap {α γ : Type} (t : ι₀)
    (oa : OracleComp spec₀ α) (cache : spec₀.QueryCache)
    (f : spec₀.Range t → α → spec₀.QueryCache → ProbComp γ) :
    𝒟[(spec₀.randomOracle t).run cache >>= fun z ↦
        (simulateQ spec₀.randomOracle oa).run z.2 >>= fun w ↦ f z.1 w.1 w.2] =
      𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (spec₀.randomOracle t).run w.2 >>= fun z ↦ f z.1 w.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t' k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [evalDist_run_bind_run_swap t t' cache fun u u' c ↦
      (simulateQ spec₀.randomOracle (k u')).run c >>= fun w ↦ f u w.1 w.2]
    exact evalDist_bind_congr fun y _ ↦ ih y.1 y.2

/-- Two computations run against the same lazy random oracle commute: their outputs and the final
cache have the same joint distribution in either order. -/
theorem evalDist_simulateQ_run_swap {α β γ : Type} (oa : OracleComp spec₀ α)
    (ob : OracleComp spec₀ β) (cache : spec₀.QueryCache)
    (f : α → β → spec₀.QueryCache → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ spec₀.randomOracle ob).run w.2 >>= fun v ↦ f w.1 v.1 v.2] =
      𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun v ↦
        (simulateQ spec₀.randomOracle oa).run v.2 >>= fun w ↦ f w.1 v.1 w.2] := by
  induction ob using OracleComp.inductionOn generalizing cache with
  | pure b => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [← evalDist_run_bind_simulateQ_run_swap t oa cache fun u a c ↦
      (simulateQ spec₀.randomOracle (k u)).run c >>= fun v ↦ f a v.1 v.2]
    exact evalDist_bind_congr fun y _ ↦ ih y.1 y.2

/-- A computation whose output is dropped does not change the output of the next computation. -/
theorem evalDist_bind_ignore {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] :=
  evalDist_ext fun y => by simp [probOutput_bind_const]

/-- A computation run before `ob` on the same lazy random oracle, whose output and final cache are
dropped, does not change the output of `ob`. -/
theorem evalDist_simulateQ_run_ghost {α β γ : Type} (oa : OracleComp spec₀ α)
    (ob : OracleComp spec₀ β) (cache : spec₀.QueryCache) (g : β → ProbComp γ) :
    𝒟[(simulateQ spec₀.randomOracle oa).run cache >>= fun w ↦
        (simulateQ spec₀.randomOracle ob).run w.2 >>= fun v ↦ g v.1] =
      𝒟[(simulateQ spec₀.randomOracle ob).run cache >>= fun v ↦ g v.1] := by
  rw [evalDist_simulateQ_run_swap oa ob cache fun _ b _ ↦ g b]
  exact evalDist_bind_congr fun v _ ↦ evalDist_bind_ignore _ _

end ThresholdLeanXmssSecurity.SwapPort

namespace ThresholdLeanXmssSecurity.LifetimeForgerReplay

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- In `S_N` every slot is ideal. -/
theorem worldMode_final (attempts : ℕ) (σ : LifetimeJointLink.Slot attempts) :
    LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false σ = .ideal := by
  simp only [LifetimeSlots.worldMode, if_pos ((LifetimeSlots.slotOrder attempts) σ).isLt]

section Worlds

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The target. The final slot world `S_N` wins at most the failed searches and the advantage of
`lifetimeForger`. -/
def LifetimeForgerExplicit : Prop :=
  LifetimeO3Bridge.slotProbability prims K circuits settings attempts D A (lifetimeRuns attempts) false ≤
    2 ^ layerHeight * searchFailure + lifetimeForgerAdvantage prims K circuits settings attempts D A

/-- `F_tree` for the top tree and then for every bottom tree, on the seeds of the honest
operators. The bottom trees use the top tree of the first output. -/
def dealerTables (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    OracleComp (RoSpec C) (Tree → Option TreeOutput × List (List (List Bit))) := do
  let top ← dealerCeremony circuits settings parameter seeds emptyTop .top
  let topTree := (TreeOutput.topTree top.1).getD emptyTop
  let bottoms ← (List.finRange (2 ^ layerHeight)).mapM fun b =>
    dealerCeremony circuits settings parameter seeds topTree (.bottom b)
  pure fun
    | .top => top
    | .bottom b => bottoms.getD b.val default

/-- The parts of `S_N`, with `F_tree` read from `tables`. -/
def tableEnv (tables : Tree → Option TreeOutput × List (List (List Bit))) :
    LifetimeSlots.SlotEnv C E (EmulationM C) :=
  { LifetimeSlots.worldEnv D circuits settings with dealer := fun _ _ _ tree => pure (tables tree) }

/-- The search of a bottom tree fails in the table. -/
def searchFails (tables : Tree → Option TreeOutput × List (List (List Bit))) : Bool :=
  (List.finRange (2 ^ layerHeight)).any fun b => (tables (.bottom b)).1.isNone

/-- `S_N` with `F_tree` of every tree computed once, before the keygen. The game samples the dealing
of `F_keygen`, computes the table of `F_tree` on the free copy, and then runs the keygen on this
dealing and the lifetime of `S_N` with this table. It returns the bad event `searchFails` and the
win. -/
def precomputeGame : OracleComp (WorldSpec C) (Bool × Bool) :=
  (fun r => r.1.1) <$> ((do
    let dealing ← StateT.lift (liftM (free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))))
    let tables ← (lifetimeHybridRoles D 0 0).honest
      (liftComp (dealerTables circuits settings dealing.1 (honestSeeds D dealing.2.2)) _)
    let (state, outputs) ← StateT.lift (liftM (idealExecution (fun p => p) D
      (LifetimeSlots.dealtKeygen dealing) (keygenSimulator D A.keygen) (fun _ => ()) []))
    let win ← LifetimeSlots.slotRun K circuits settings attempts (tableEnv circuits settings D tables)
      (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D A state outputs
    pure (searchFails tables, win) : EmulationM C (Bool × Bool)).run ∅).run

/-- `precomputeGame` in the lifetime world, from an empty cache. -/
def precomputeRun : ProbComp (Bool × Bool) :=
  (simulateQ (lifetimeWorld prims) (precomputeGame K circuits settings attempts D A)).run.run' ∅ >>=
    fun r => pure r.1

/-- E1 and E3. When the circuits compute `Th` and the batch size is positive, `S_N` and
`precomputeGame` win with the same probability. -/
def FinalPrecompute : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    LifetimeO3Bridge.slotProbability prims K circuits settings attempts D A (lifetimeRuns attempts) false =
      (Pr[fun r => r.2 = true | precomputeRun prims K circuits settings attempts D A]).toReal

/-- E5. When the circuits compute `Th` and the batch size is positive, the search of some bottom
tree fails in `precomputeGame` with probability at most `2^layerHeight * searchFailure`. -/
def PrecomputeSearch : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    (Pr[fun r => r.1 = true | precomputeRun prims K circuits settings attempts D A]).toReal ≤
      2 ^ layerHeight * searchFailure

/-- E2, E4 and E6. When the circuits compute `Th` and the batch size is positive, `precomputeGame`
wins with no failed search with probability at most `lifetimeForgerAdvantage`. In E4 the private
keygen table of `forgerWorld` holds only the inputs `.derive .keygen`. The dealer, the signing and
the verification never read them, so the table agrees with `H` on every point that both runs
read. -/
def PrecomputeReplay : Prop :=
  CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
    (Pr[fun r => r.1 = false ∧ r.2 = true | precomputeRun prims K circuits settings attempts D A]).toReal ≤
      lifetimeForgerAdvantage prims K circuits settings attempts D A

/-- The calls of `H` and `PRG` of a forger. -/
def ForgerCounted : (ForgerSpec C).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- E7. When the lifetime game makes at most `Q` calls, `lifetimeForger` makes at most
`Q + lifetimeOverhead C attempts Q` calls of `H` and `PRG` on each path. -/
def ForgerQueryBound (Q : ℕ) : Prop :=
  HasLifetimeQueryBound K circuits settings attempts D A Q →
    ∀ (publicKey : PublicKey) (top : TopTree),
      IsQueryBoundP (lifetimeForger K circuits settings attempts D A publicKey top) ForgerCounted
        (Q + lifetimeOverhead C attempts Q)

/-- `LifetimeForgerExplicit` follows from the three hops under the premises of the target. -/
theorem lifetimeForgerExplicit_of_hops (hc : CircuitsCompute circuits prims.Th)
    (hsize : 0 < settings.batchSize)
    (h1 : FinalPrecompute prims K circuits settings attempts D A)
    (h2 : PrecomputeSearch prims K circuits settings attempts D A)
    (h3 : PrecomputeReplay prims K circuits settings attempts D A) :
    LifetimeForgerExplicit prims K circuits settings attempts D A := by
  unfold LifetimeForgerExplicit
  rw [h1 hc hsize]
  replace h2 := h2 hc hsize
  replace h3 := h3 hc hsize
  set p := precomputeRun prims K circuits settings attempts D A
  have hsplit : Pr[fun r => r.2 = true | p] ≤
      Pr[fun r => r.1 = true | p] + Pr[fun r => r.1 = false ∧ r.2 = true | p] := by
    calc Pr[fun r => r.2 = true | p]
        ≤ Pr[fun r => r.1 = true ∨ (r.1 = false ∧ r.2 = true) | p] :=
          probEvent_mono fun r _ hr => by cases h : r.1 <;> simp_all
      _ ≤ _ := probEvent_or_le p _ _
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hsplit
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at hreal
  linarith

end Worlds

end ThresholdLeanXmssSecurity.LifetimeForgerReplay

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.withCaching_run_caches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.withCaching_run_caches

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.cacheQuery_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.cacheQuery_comm

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.evalDist_run_bind_run_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.evalDist_run_bind_run_swap

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.evalDist_run_bind_simulateQ_run_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.evalDist_run_bind_simulateQ_run_swap

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.evalDist_simulateQ_run_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.evalDist_simulateQ_run_swap

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.evalDist_bind_ignore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.evalDist_bind_ignore

/-- info: 'ThresholdLeanXmssSecurity.SwapPort.evalDist_simulateQ_run_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SwapPort.evalDist_simulateQ_run_ghost

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerReplay.worldMode_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerReplay.worldMode_final

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerReplay.lifetimeForgerExplicit_of_hops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerReplay.lifetimeForgerExplicit_of_hops
