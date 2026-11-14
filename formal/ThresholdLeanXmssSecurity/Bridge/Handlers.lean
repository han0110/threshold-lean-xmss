import ThresholdLeanXmss.Statement

/-!
# The handlers, the transformers and the budgets of the statement layer in elementary terms

`ThresholdLeanXmssSecurity/Bridge/Characterization.lean` fixes the probability of each output of a
computation. This file fixes how the statement layer makes that computation. It states how
`simulateQ` gives each query to a handler, how `liftComp` moves a query into a larger oracle spec,
how a program in `StateT`, in `WriterT` or in `OptionT` becomes a computation, how a cache answers,
what the structural budget `IsQueryBoundP` permits, and what the two experiments of the PRF game
are. The last part unfolds the runs and the claims of `ThresholdLeanXmss/Statement.lean` that read
these terms.

The import lines and the part `Dictionary` are the only text that names a definition of one VCVio
revision. Each theorem after the dictionary uses the names of the dictionary, or a name that the
two revisions share. The same theorem text, with the dictionary of the other revision, states the
same fact about that revision.

The three equations `simulateQ_pure`, `simulateQ_query` and `simulateQ_bind` fix the simulation of
each computation. `simulateQ_unique` proves this. The two equations `isQueryBoundP_pure` and
`isQueryBoundP_query_bind` fix the structural budget. `isQueryBoundP_unique` proves this.
-/

set_option autoImplicit false

namespace ThresholdLeanXmss.Handlers

noncomputable section

/-! ## Dictionary -/

open OracleComp OracleSpec HashSig LeanXmss ENNReal

/-- The probability that `mx` returns `a`. -/
abbrev outputProbability {α : Type} (mx : ProbComp α) (a : α) : ℝ≥0∞ := Pr{let x ← mx}[x = a]

/-- The probability that the output of `mx` satisfies `p`. -/
abbrev eventProbability {α : Type} (mx : ProbComp α) (p : α → Prop) : ℝ≥0∞ := Pr{let x ← mx}[p x]

/-- The real experiment of the PRF game. -/
abbrev prfRealRun {K D R : Type} (prf : PRFScheme K D R) (adversary : PRFScheme.PRFAdversary D R) :
    ProbComp Bool :=
  prf.prfRealExperiment adversary

/-- The ideal experiment of the PRF game. -/
abbrev prfIdealRun {D R : Type} [DecidableEq D] [SampleableType R]
    (adversary : PRFScheme.PRFAdversary D R) : ProbComp Bool :=
  PRFScheme.prfIdealExperiment adversary

/-- The computation that starts with the query `t` and continues with `k`, as `advance` reads it. -/
abbrev queryBind {ι : Type} {spec : OracleSpec ι} {α : Type} (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) : OracleComp spec α :=
  .liftBind t k

/-! ## The simulation of a computation -/

section Simulation

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} {α β : Type}

/-- The simulation of `pure a` returns `a`. -/
theorem simulateQ_pure [Monad m] (impl : QueryImpl spec m) (a : α) :
    simulateQ impl (pure a : OracleComp spec α) = pure a :=
  _root_.simulateQ_pure impl a

/-- The simulation of one query is the answer of the handler to this query. -/
theorem simulateQ_query [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (t : spec.Domain) :
    simulateQ impl (query t : OracleComp spec (spec.Range t)) = impl t := by
  rw [HasQuery.instOfMonadLift_query]
  exact simulateQ_spec_query impl t

/-- The simulation of `mx >>= f` is the simulation of `mx`, and then the simulation of `f a` for
the output `a`. -/
theorem simulateQ_bind [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (mx : OracleComp spec α) (f : α → OracleComp spec β) :
    simulateQ impl (mx >>= f) = simulateQ impl mx >>= fun a => simulateQ impl (f a) :=
  _root_.simulateQ_bind impl mx f

/-- A function that satisfies the three equations is the simulation with `impl`. -/
theorem simulateQ_unique [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (S : {α : Type} → OracleComp spec α → m α)
    (pure_eq : ∀ {α : Type} (a : α), S (pure a : OracleComp spec α) = pure a)
    (query_eq : ∀ t : spec.Domain, S (query t : OracleComp spec (spec.Range t)) = impl t)
    (bind_eq : ∀ {α β : Type} (mx : OracleComp spec α) (f : α → OracleComp spec β),
      S (mx >>= f) = S mx >>= fun a => S (f a))
    (mx : OracleComp spec α) : S mx = simulateQ impl mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => rw [pure_eq, simulateQ_pure]
  | query_bind t oa ih =>
    have hS := query_eq t
    have hquery := simulateQ_query impl t
    rw [HasQuery.instOfMonadLift_query] at hS hquery
    rw [bind_eq, simulateQ_bind, hS, hquery]
    exact bind_congr ih

/-- The statement layer also writes one query as `OracleComp.lift (OracleSpec.query t)`. -/
theorem lift_query (t : spec.Domain) :
    (OracleComp.lift (OracleSpec.query t) : OracleComp spec (spec.Range t)) = query t :=
  rfl

/-- The constructor `.pure` of a computation, as `advance` reads it, is `pure`. -/
theorem constructor_pure (a : α) : (.pure a : OracleComp spec α) = pure a :=
  rfl

/-- The constructor of a computation that starts with a query, as `advance` reads it, is the query
and then the continuation. -/
theorem queryBind_eq (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    queryBind t k = (query t : OracleComp spec (spec.Range t)) >>= k :=
  rfl

end Simulation

/-! ## The sum of two oracle specs -/

section Sum

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m : Type → Type}
  {α β : Type}

/-- The sum of two handlers gives a query of the left spec to the left handler. -/
theorem add_inl (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) (t : spec₁.Domain) :
    (impl₁ + impl₂ : QueryImpl (spec₁ + spec₂) m) (.inl t) = impl₁ t :=
  rfl

/-- The sum of two handlers gives a query of the right spec to the right handler. -/
theorem add_inr (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) (t : spec₂.Domain) :
    (impl₁ + impl₂ : QueryImpl (spec₁ + spec₂) m) (.inr t) = impl₂ t :=
  rfl

/-- `QueryImpl.add` is the sum of two handlers. -/
theorem add_eq (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) :
    QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ :=
  rfl

/-- A lifted `pure a` is `pure a`. -/
theorem liftComp_pure {ι τ : Type} {spec : OracleSpec ι} (superSpec : OracleSpec τ)
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] (a : α) :
    liftComp (pure a : OracleComp spec α) superSpec = pure a :=
  rfl

/-- The lift of `mx >>= f` is the lift of `mx`, and then the lift of `f a` for the output `a`. -/
theorem liftComp_bind {ι τ : Type} {spec : OracleSpec ι} (superSpec : OracleSpec τ)
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] (mx : OracleComp spec α)
    (f : α → OracleComp spec β) :
    liftComp (mx >>= f) superSpec = liftComp mx superSpec >>= fun a => liftComp (f a) superSpec :=
  OracleComp.liftComp_bind superSpec mx f

/-- A lifted query of the left spec is the same query on the left side of the sum. -/
theorem liftComp_query_left (t : spec₁.Domain) :
    liftComp (query t : OracleComp spec₁ (spec₁.Range t)) (spec₁ + spec₂) =
      query (spec := spec₁ + spec₂) (Sum.inl t) := by
  simp only [HasQuery.instOfMonadLift_query, OracleComp.liftComp_liftM_query]
  rfl

/-- A lifted query of the right spec is the same query on the right side of the sum. -/
theorem liftComp_query_right (t : spec₂.Domain) :
    liftComp (query t : OracleComp spec₂ (spec₂.Range t)) (spec₁ + spec₂) =
      query (spec := spec₁ + spec₂) (Sum.inr t) := by
  simp only [HasQuery.instOfMonadLift_query, OracleComp.liftComp_liftM_query]
  rfl

end Sum

/-! ## The run of a program in `StateT` -/

section State

variable {σ : Type} {m : Type → Type} {α β : Type}

/-- `pure a` returns `a` and keeps the state. -/
theorem stateT_run_pure [Monad m] (a : α) (s : σ) : (pure a : StateT σ m α).run s = pure (a, s) :=
  rfl

/-- `mx >>= f` runs `mx`, and then runs `f` on its output from its next state. -/
theorem stateT_run_bind [Monad m] (mx : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (mx >>= f).run s = mx.run s >>= fun r => (f r.1).run r.2 :=
  rfl

/-- A lifted computation keeps the state. -/
theorem stateT_run_lift [Monad m] (mx : m α) (s : σ) :
    (StateT.lift mx : StateT σ m α).run s = mx >>= fun a => pure (a, s) :=
  rfl

/-- `StateT.mk f` runs `f` on the state. -/
theorem stateT_run_mk (f : σ → m (α × σ)) (s : σ) : (StateT.mk f).run s = f s :=
  rfl

/-- `get` returns the state and keeps it. -/
theorem stateT_run_get [Monad m] (s : σ) : (get : StateT σ m σ).run s = pure (s, s) :=
  rfl

/-- `set s'` replaces the state with `s'`. -/
theorem stateT_run_set [Monad m] (s' s : σ) :
    (set s' : StateT σ m PUnit).run s = pure (PUnit.unit, s') :=
  rfl

/-- `run'` gives the output of `run` without the last state. -/
theorem stateT_run' [Monad m] (mx : StateT σ m α) (s : σ) :
    mx.run' s = (fun r => r.1) <$> mx.run s :=
  rfl

end State

/-! ## The run of a program in `WriterT` -/

section MonoidWriter

variable {ω : Type} {m : Type → Type} {α β : Type}

/-- `pure a` returns `a` with the log `1`. -/
theorem writerT_run_pure [Monoid ω] [Monad m] (a : α) :
    (pure a : WriterT ω m α).run = pure (a, 1) :=
  rfl

/-- `mx >>= f` runs `mx`, and then runs `f` on its output. Its log is the product of the two logs,
in this order. -/
theorem writerT_run_bind [Monoid ω] [Monad m] (mx : WriterT ω m α) (f : α → WriterT ω m β) :
    (mx >>= f).run = mx.run >>= fun r => (fun r' => (r'.1, r.2 * r'.2)) <$> (f r.1).run :=
  rfl

/-- A lifted computation has the log `1`. -/
theorem writerT_run_lift [Monoid ω] [Monad m] (mx : m α) :
    (liftM mx : WriterT ω m α).run = (fun a => (a, 1)) <$> mx :=
  rfl

/-- `tell w` has the log `w`. -/
theorem writerT_run_tell [Monad m] (w : ω) :
    (tell w : WriterT ω m PUnit).run = pure (PUnit.unit, w) :=
  rfl

/-- The log `1` of the counting handler is the count 0. -/
theorem toAdd_one : Multiplicative.toAdd (1 : Multiplicative ℕ) = 0 :=
  rfl

/-- The product of two logs of the counting handler is the sum of the two counts. -/
theorem toAdd_mul (a b : Multiplicative ℕ) :
    Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b :=
  rfl

/-- The log `Multiplicative.ofAdd n` of the counting handler is the count `n`. -/
theorem toAdd_ofAdd (n : ℕ) : Multiplicative.toAdd (Multiplicative.ofAdd n) = n :=
  rfl

end MonoidWriter

section AppendWriter

variable {ω : Type} {m : Type → Type} {α β : Type}

/-- `pure a` returns `a` with the empty log. -/
theorem appendWriterT_run_pure [EmptyCollection ω] [Append ω] [Monad m] (a : α) :
    (pure a : WriterT ω m α).run = pure (a, ∅) :=
  rfl

/-- `mx >>= f` runs `mx`, and then runs `f` on its output. Its log is the log of `mx` and then the
log of `f`. -/
theorem appendWriterT_run_bind [EmptyCollection ω] [Append ω] [Monad m] (mx : WriterT ω m α)
    (f : α → WriterT ω m β) :
    (mx >>= f).run = mx.run >>= fun r => (fun r' => (r'.1, r.2 ++ r'.2)) <$> (f r.1).run :=
  rfl

/-- A lifted computation has the empty log. -/
theorem appendWriterT_run_lift [EmptyCollection ω] [Monad m] (mx : m α) :
    (liftM mx : WriterT ω m α).run = (fun a => (a, ∅)) <$> mx :=
  rfl

/-- `WriterT.mk x` runs `x`. -/
theorem writerT_run_mk (x : m (α × ω)) : (WriterT.mk x).run = x :=
  rfl

end AppendWriter

/-! ## The run of a program in `OptionT` -/

section Option

variable {m : Type → Type} {α β : Type}

/-- `pure a` returns `some a`. -/
theorem optionT_run_pure [Monad m] (a : α) : (pure a : OptionT m α).run = pure (some a) :=
  rfl

/-- `mx >>= f` runs `mx`. If the output is `some a`, it runs `f a`. If the output is `none`, it
returns `none`. -/
theorem optionT_run_bind [Monad m] (mx : OptionT m α) (f : α → OptionT m β) :
    (mx >>= f).run = mx.run >>= fun r =>
      match r with
      | some a => (f a).run
      | none => pure none :=
  rfl

/-- A lifted computation returns `some` of its output. -/
theorem optionT_run_lift [Monad m] (mx : m α) :
    (OptionT.lift mx : OptionT m α).run = mx >>= fun a => pure (some a) :=
  rfl

/-- `failure` returns `none`. -/
theorem optionT_run_failure [Monad m] : (failure : OptionT m α).run = pure none :=
  rfl

end Option

/-! ## The cache -/

section Cache

variable {ι : Type} {spec : OracleSpec ι}

/-- The empty cache has no answer. -/
theorem cache_empty (t : spec.Domain) : (∅ : spec.QueryCache) t = none :=
  rfl

/-- After `cacheQuery t u`, the cache has the answer `u` at `t`. -/
theorem cache_cacheQuery_self [DecidableEq ι] (cache : spec.QueryCache) (t : spec.Domain)
    (u : spec.Range t) :
    (cache.cacheQuery t u) t = some u :=
  QueryCache.cacheQuery_self cache t u

/-- `cacheQuery t u` keeps the answer at each other input. -/
theorem cache_cacheQuery_of_ne [DecidableEq ι] (cache : spec.QueryCache) (t t' : spec.Domain)
    (u : spec.Range t) (h : t' ≠ t) : (cache.cacheQuery t u) t' = cache t' :=
  QueryCache.cacheQuery_of_ne cache u h

/-- Two caches with the same answer at each input are equal. -/
theorem cache_ext (cache₁ cache₂ : spec.QueryCache) (h : ∀ t, cache₁ t = cache₂ t) :
    cache₁ = cache₂ :=
  QueryCache.ext h

/-- Each function from the inputs to the optional answers is the lookup of a cache. -/
theorem cache_exists (f : (t : spec.Domain) → Option (spec.Range t)) :
    ∃ cache : spec.QueryCache, ∀ t, cache t = f t :=
  ⟨QueryCache.ofFn f, fun _ => rfl⟩

end Cache

/-! ## The handlers of the world -/

section WorldHandlers

variable {ι : Type} {spec : OracleSpec ι}

/-- The lazy random oracle returns the answer of the cache if the cache has one. If not, it samples
a uniform answer, puts it into the cache and returns it. -/
theorem randomOracle_run [DecidableEq ι] [∀ t : spec.Domain, SampleableType (spec.Range t)]
    (t : spec.Domain) (cache : spec.QueryCache) :
    (spec.randomOracle t).run cache =
      match cache t with
      | some u => pure (u, cache)
      | none => ($ᵗ spec.Range t) >>= fun u => pure (u, cache.cacheQuery t u) :=
  randomOracle.run_eq t cache

/-- The handler of the private sampling makes the same sampling query and keeps the cache. -/
theorem unifFwdImpl_run (n : ℕ) (cache : spec.QueryCache) :
    (unifFwdImpl spec n).run cache = (fun u => (u, cache)) <$> ($[0..n]) := by
  simp [unifFwdImpl]
  rfl

/-- The counting handler gives the query to `impl` and writes the cost of the query. -/
theorem withAddCost_run {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (costFn : spec.Domain → ℕ) (t : spec.Domain) :
    (impl.withAddCost costFn t).run =
      (fun u => (u, Multiplicative.ofAdd (costFn t))) <$> impl t := by
  simp [QueryImpl.withAddCost_apply, AddWriterT.addTell]

end WorldHandlers

/-! ## The structural budget -/

section Budget

variable {ι : Type} {spec : OracleSpec ι} {α : Type} (p : ι → Prop) [DecidablePred p]

/-- `pure a` is in each budget. -/
theorem isQueryBoundP_pure (a : α) (n : ℕ) : IsQueryBoundP (pure a : OracleComp spec α) p n :=
  OracleComp.isQueryBoundP_pure p a n

/-- A query and then `f` is in the budget `n` if and only if the query is not counted or `n` is
not 0, and for each answer `u` the computation `f u` is in the budget that remains. A counted
query takes 1 from the budget. -/
theorem isQueryBoundP_query_bind (t : spec.Domain) (f : spec.Range t → OracleComp spec α) (n : ℕ) :
    IsQueryBoundP ((query t : OracleComp spec (spec.Range t)) >>= f) p n ↔
      (p t → 0 < n) ∧ ∀ u, IsQueryBoundP (f u) p (if p t then n - 1 else n) := by
  rw [HasQuery.instOfMonadLift_query, isQueryBoundP_query_bind_iff, imp_iff_not_or]

/-- A computation that starts with a counted query is not in the budget 0. -/
theorem not_isQueryBoundP_zero (t : spec.Domain) (f : spec.Range t → OracleComp spec α)
    (h : p t) : ¬ IsQueryBoundP ((query t : OracleComp spec (spec.Range t)) >>= f) p 0 :=
  fun hbound => Nat.lt_irrefl 0 (((isQueryBoundP_query_bind p t f 0).mp hbound).1 h)

/-- A predicate that satisfies the two equations is the structural budget. -/
theorem isQueryBoundP_unique (B : {α : Type} → OracleComp spec α → ℕ → Prop)
    (pure_eq : ∀ {α : Type} (a : α) (n : ℕ), B (pure a : OracleComp spec α) n)
    (query_bind_eq : ∀ {α : Type} (t : spec.Domain) (f : spec.Range t → OracleComp spec α) (n : ℕ),
      B ((query t : OracleComp spec (spec.Range t)) >>= f) n ↔
        (p t → 0 < n) ∧ ∀ u, B (f u) (if p t then n - 1 else n))
    (mx : OracleComp spec α) (n : ℕ) : B mx n ↔ IsQueryBoundP mx p n := by
  induction mx using OracleComp.inductionOn generalizing n with
  | pure x => exact iff_of_true (pure_eq x n) (isQueryBoundP_pure p x n)
  | query_bind t oa ih =>
    have hB := query_bind_eq t oa n
    have hbound := isQueryBoundP_query_bind p t oa n
    rw [HasQuery.instOfMonadLift_query] at hB hbound
    rw [hB, hbound]
    exact and_congr_right fun _ => forall_congr' fun u => ih u _

end Budget

/-! ## The experiments of the PRF game -/

section Prf

variable {K D R : Type} {α : Type}

/-- The handler of the real experiment under the key `k`. A sampling query makes the same sampling
query. A function query at `d` has the answer `prf.eval k d`. -/
abbrev prfRealAnswer (prf : PRFScheme K D R) (k : K) :
    QueryImpl (PRFScheme.PRFOracleSpec D R) ProbComp
  | .inl n => $[0..n]
  | .inr d => pure (prf.eval k d)

/-- The handler of the ideal experiment. A sampling query makes the same sampling query and keeps
the cache. A function query at `d` has the answer of the cache if the cache has one. If not, the
handler samples a uniform answer, puts it into the cache and returns it. -/
abbrev prfIdealAnswer [DecidableEq D] [SampleableType R] :
    QueryImpl (PRFScheme.PRFOracleSpec D R) (StateT (D →ₒ R).QueryCache ProbComp)
  | .inl n => StateT.mk fun cache => (fun u => (u, cache)) <$> ($[0..n])
  | .inr d => StateT.mk fun cache =>
      match cache d with
      | some u => pure (u, cache)
      | none => ($ᵗ R) >>= fun u => pure (u, cache.cacheQuery d u)

/-- The real experiment samples one key. Then it answers each query of the adversary with the
handler under this key. -/
theorem prfRealRun_eq (prf : PRFScheme K D R) (adversary : PRFScheme.PRFAdversary D R) :
    prfRealRun prf adversary =
      prf.keygen >>= fun k => simulateQ (prfRealAnswer prf k) adversary := by
  have h : ∀ k, prf.prfRealQueryImpl k = prfRealAnswer prf k := by
    intro k
    funext t
    cases t with
    | inl n =>
      rw [PRFScheme.prfRealQueryImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
      rfl
    | inr d => exact PRFScheme.prfRealQueryImpl_apply_inr prf k d
  simp only [prfRealRun, PRFScheme.prfRealExperiment, h]

/-- The ideal experiment answers each query of the adversary with the lazy random function, from
the empty cache. -/
theorem prfIdealRun_eq [DecidableEq D] [SampleableType R]
    (adversary : PRFScheme.PRFAdversary D R) :
    prfIdealRun adversary = (simulateQ prfIdealAnswer adversary).run' ∅ := by
  have h : PRFScheme.prfIdealQueryImpl (D := D) (R := R) = prfIdealAnswer := by
    funext t
    cases t with
    | inl n => exact StateT.ext fun cache => unifFwdImpl_run n cache
    | inr d =>
      refine StateT.ext fun cache => ?_
      rw [PRFScheme.prfIdealQueryImpl_apply_inr, randomOracle_run]
      change _ = match cache d with
        | some u => pure (u, cache)
        | none => ($ᵗ R) >>= fun u => pure (u, cache.cacheQuery d u)
      cases cache d <;> rfl
  simp only [prfIdealRun, PRFScheme.prfIdealExperiment, h]

/-- The private sampling of the adversary is the same sampling in the real experiment. -/
theorem simulateQ_prfRealAnswer_liftComp (prf : PRFScheme K D R) (k : K) (oa : ProbComp α) :
    simulateQ (prfRealAnswer prf k) (liftComp oa (PRFScheme.PRFOracleSpec D R)) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind n oa ih =>
    rw [liftComp_bind, simulateQ_bind]
    have hquery := liftComp_query_left (spec₂ := D →ₒ R) (spec₁ := unifSpec) n
    rw [HasQuery.instOfMonadLift_query] at hquery
    rw [hquery, simulateQ_query]
    exact bind_congr ih

/-- The private sampling of the adversary is the same sampling in the ideal experiment, and it
keeps the cache. -/
theorem simulateQ_prfIdealAnswer_liftComp [DecidableEq D] [SampleableType R] (oa : ProbComp α)
    (cache : (D →ₒ R).QueryCache) :
    (simulateQ (prfIdealAnswer (D := D) (R := R))
      (liftComp oa (PRFScheme.PRFOracleSpec D R))).run cache = (fun a => (a, cache)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp
  | query_bind n oa ih =>
    rw [liftComp_bind, simulateQ_bind]
    have hquery := liftComp_query_left (spec₂ := D →ₒ R) (spec₁ := unifSpec) n
    rw [HasQuery.instOfMonadLift_query] at hquery
    rw [hquery, simulateQ_query, stateT_run_bind]
    change ((fun u => (u, cache)) <$> ($[0..n])) >>= _ = _
    rw [bind_map_left, map_bind]
    exact bind_congr fun u => ih u cache

end Prf

/-! ## The runs of the statement layer -/

section Statements

variable {C : Committee} (prims : Primitives) {α : Type}

/-- A sampling query that is lifted to the local oracles is the sampling query of the local
oracles. -/
theorem liftComp_sample_local (n : ℕ) :
    liftComp ($[0..n]) (LocalSpec C) = query (spec := LocalSpec C) (Sum.inl n) :=
  rfl

/-- A query of `H` or of `PRG` that is lifted to the local oracles is the same query of the local
oracles. -/
theorem liftComp_ro_local (t : (RoSpec C).Domain) :
    liftComp (query t : OracleComp (RoSpec C) ((RoSpec C).Range t)) (LocalSpec C) =
      query (spec := LocalSpec C) (Sum.inr t) :=
  rfl

/-- A query of the local oracles that is lifted to the oracles of the simulator is the same query
on the left side. `worldRoles` lifts each step of the adversary in this way. -/
theorem liftComp_local_simulator (t : (LocalSpec C).Domain) :
    liftComp (query t : OracleComp (LocalSpec C) ((LocalSpec C).Range t)) (SimulatorSpec C) =
      query (spec := SimulatorSpec C) (Sum.inl t) := by
  rcases t with _ | _ | _ <;> rfl

/-- A query of the local oracles that is lifted to the oracles of an operator is the same query on
the left side of the left side. `localStep` lifts each local step of an operator in this way. -/
theorem liftComp_local_party {E κ : Type} {G : OracleSpec κ} (t : (LocalSpec C).Domain) :
    liftComp (query t : OracleComp (LocalSpec C) ((LocalSpec C).Range t)) (PartySpec C E G) =
      query (spec := PartySpec C E G) (Sum.inl (Sum.inl t)) := by
  rcases t with _ | _ | _ <;> rfl

/-- A sampling query that is lifted to the oracles of a functionality is the sampling query of the
local oracles, on the left side. -/
theorem liftComp_sample_functionality {L R : Type} (n : ℕ) :
    liftComp ($[0..n]) (LocalSpec C + (L →ₒ R)) =
      query (spec := LocalSpec C + (L →ₒ R)) (Sum.inl (Sum.inl n)) :=
  rfl

/-- A query of `H` or of `PRG` that is lifted to the oracles of a functionality is the same query
of the local oracles, on the left side. -/
theorem liftComp_ro_functionality {L R : Type} (t : (RoSpec C).Domain) :
    liftComp (query t : OracleComp (RoSpec C) ((RoSpec C).Range t)) (LocalSpec C + (L →ₒ R)) =
      query (spec := LocalSpec C + (L →ₒ R)) (Sum.inl (Sum.inr t)) := by
  rcases t with _ | _ <;> rfl

/-- A sampling query that is lifted to the PRF oracles of `prgReduction` is the sampling query of
these oracles. -/
theorem liftComp_sample_stream (n : ℕ) :
    liftComp ($[0..n]) (StreamSpec C) = query (spec := StreamSpec C) (Sum.inl n) :=
  rfl

/-! The writer of `observe` has a list of calls as its log, and the writer of `world` has a count
as its log. The four examples apply the equations of `WriterT` to these two writers. -/

example (mx : OracleComp (WorldSpec C) α) :
    (liftM mx : WriterT (CallLog C) (OracleComp (WorldSpec C)) α).run = (fun a => (a, ∅)) <$> mx :=
  appendWriterT_run_lift mx

example {β : Type} (mx : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (f : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β) :
    (mx >>= f).run = mx.run >>= fun r => (fun r' => (r'.1, r.2 ++ r'.2)) <$> (f r.1).run :=
  appendWriterT_run_bind mx f

example (mx : StateT (HashCache C) ProbComp α) :
    (liftM mx : AddWriterT ℕ (StateT (HashCache C) ProbComp) α).run = (fun a => (a, 1)) <$> mx :=
  writerT_run_lift mx

example {β : Type} (mx : AddWriterT ℕ (StateT (HashCache C) ProbComp) α)
    (f : α → AddWriterT ℕ (StateT (HashCache C) ProbComp) β) :
    (mx >>= f).run = mx.run >>= fun r => (fun r' => (r'.1, r.2 * r'.2)) <$> (f r.1).run :=
  writerT_run_bind mx f

/-- `runWorld` simulates the computation with the handler `world` from the empty cache. It returns
the output and the number that the counting handler wrote, without the last cache. -/
theorem runWorld_eq (oa : OracleComp (WorldSpec C) α) :
    runWorld prims oa =
      (fun r => (r.1.1, Multiplicative.toAdd r.1.2)) <$>
        (simulateQ (world prims) oa).run.run ∅ := by
  simp [runWorld, StateT.run']
  rfl

/-- `runSigningWorld` simulates the computation with the handler `signingWorld` from the empty
cache. It returns the output and the number that the counting handler wrote, without the last
cache. -/
theorem runSigningWorld_eq (oa : OracleComp (WorldSpec C) α) :
    runSigningWorld prims oa =
      (fun r => (r.1.1, Multiplicative.toAdd r.1.2)) <$>
        (simulateQ (signingWorld prims) oa).run.run ∅ := by
  simp [runSigningWorld, StateT.run']
  rfl

/-- `accepts` is the probability that the run returns `true`. -/
theorem accepts_eq (oa : OracleComp (WorldSpec C) Bool) :
    accepts prims oa = (eventProbability (runWorld prims oa) fun r => r.1 = true).toReal :=
  rfl

/-- `signingAccepts` is the probability that the run in the signing world returns `true`. -/
theorem signingAccepts_eq (oa : OracleComp (WorldSpec C) Bool) :
    signingAccepts prims oa =
      (eventProbability (runSigningWorld prims oa) fun r => r.1 = true).toReal :=
  rfl

/-- `HasHashQueryBound` bounds the count of each output that has a probability that is not 0. -/
theorem hasHashQueryBound_iff (run : ProbComp (α × ℕ)) (q : ℕ) :
    HasHashQueryBound run q ↔ ∀ r, outputProbability run r ≠ 0 → r.2 ≤ q :=
  forall_congr' fun r => imp_congr_left (OracleComp.mem_support_iff_prEvent_ne_zero run r)

/-- `HasSigningQueryBound` bounds the count of each output of the run in the signing world that has
a probability that is not 0. -/
theorem hasSigningQueryBound_iff (oa : OracleComp (WorldSpec C) α) (q : ℕ) :
    HasSigningQueryBound prims oa q ↔
      ∀ r, outputProbability (runSigningWorld prims oa) r ≠ 0 → r.2 ≤ q :=
  forall_congr' fun r =>
    imp_congr_left (OracleComp.mem_support_iff_prEvent_ne_zero (runSigningWorld prims oa) r)

/-- The real experiment that `TreeSecurityStatement` reads samples one key of `hiddenStreams`. Then
it answers each query of `prgReduction` with the handler under this key. -/
theorem prfRealRun_prgReduction (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    prfRealRun (hiddenStreams prims.aes) (prgReduction prims D game) =
      (hiddenStreams (C := C) prims.aes).keygen >>= fun k =>
        simulateQ (prfRealAnswer (hiddenStreams prims.aes) k) (prgReduction prims D game) :=
  prfRealRun_eq _ _

/-- The ideal experiment that `TreeSecurityStatement` reads answers each query of `prgReduction`
with the lazy random function, from the empty cache. -/
theorem prfIdealRun_prgReduction (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    prfIdealRun (prgReduction prims D game) =
      (simulateQ prfIdealAnswer (prgReduction prims D game)).run' ∅ :=
  prfIdealRun_eq _

/-- The run that `TreeSuccessStatement` reads. -/
abbrev treeSuccessRun (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) : ProbComp (Option TreeOutput × ℕ) :=
  runWorld prims (free (C := C) (liftComp (do
    let (output, _) ← dealerCeremony circuits settings parameter seeds emptyTop .top
    let some top := TreeOutput.topTree output | pure none
    Prod.fst <$> dealerCeremony circuits settings parameter seeds top (.bottom b)) _))

/-- `TreeSuccessStatement` bounds the probability that the run of the dealer returns no tree. -/
theorem treeSuccessStatement_iff (circuits : Circuits) (settings : Settings) :
    TreeSuccessStatement prims circuits settings C ↔
      (CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
        ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)),
          (eventProbability (treeSuccessRun prims circuits settings parameter seeds b)
            fun r => r.1 = none).toReal ≤ searchFailure) :=
  Iff.rfl

/-- `SigningCorrectnessStatement` says that no output of the honest signing run with a probability
that is not 0 is `some false`, and it bounds the probability that the run returns no result. -/
theorem signingCorrectnessStatement_iff :
    SigningCorrectnessStatement prims C ↔
      ∀ (J : C.Quorum) (e : KeyIndex) (m : Message),
        (∀ r, outputProbability (runWorld prims (honestSigning J e m)) r ≠ 0 → r.1 ≠ some false) ∧
          (eventProbability (runWorld prims (honestSigning J e m)) fun r => r.1 = none).toReal ≤
            2 * searchFailure :=
  forall₃_congr fun J e m => and_congr_left' (forall_congr' fun r => imp_congr_left
    (OracleComp.mem_support_iff_prEvent_ne_zero (runWorld prims (honestSigning J e m)) r))

end Statements

end

/-! The build fails if the axioms of a theorem of this file change. -/

/-- info: 'ThresholdLeanXmss.Handlers.simulateQ_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_pure

/-- info: 'ThresholdLeanXmss.Handlers.simulateQ_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_query

/-- info: 'ThresholdLeanXmss.Handlers.simulateQ_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_bind

/-- info: 'ThresholdLeanXmss.Handlers.simulateQ_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_unique

/-- info: 'ThresholdLeanXmss.Handlers.lift_query' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms lift_query

/-- info: 'ThresholdLeanXmss.Handlers.constructor_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms constructor_pure

/-- info: 'ThresholdLeanXmss.Handlers.queryBind_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms queryBind_eq

/-- info: 'ThresholdLeanXmss.Handlers.add_inl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms add_inl

/-- info: 'ThresholdLeanXmss.Handlers.add_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms add_inr

/-- info: 'ThresholdLeanXmss.Handlers.add_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms add_eq

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_pure

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_bind

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_query_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_query_left

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_query_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_query_right

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run_pure

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run_bind

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run_lift' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run_lift

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run_mk' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run_mk

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run_get' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run_get

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run_set' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run_set

/-- info: 'ThresholdLeanXmss.Handlers.stateT_run'' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms stateT_run'

/-- info: 'ThresholdLeanXmss.Handlers.writerT_run_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms writerT_run_pure

/-- info: 'ThresholdLeanXmss.Handlers.writerT_run_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms writerT_run_bind

/-- info: 'ThresholdLeanXmss.Handlers.writerT_run_lift' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms writerT_run_lift

/-- info: 'ThresholdLeanXmss.Handlers.writerT_run_tell' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms writerT_run_tell

/-- info: 'ThresholdLeanXmss.Handlers.toAdd_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toAdd_one

/-- info: 'ThresholdLeanXmss.Handlers.toAdd_mul' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toAdd_mul

/-- info: 'ThresholdLeanXmss.Handlers.toAdd_ofAdd' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toAdd_ofAdd

/-- info: 'ThresholdLeanXmss.Handlers.appendWriterT_run_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms appendWriterT_run_pure

/-- info: 'ThresholdLeanXmss.Handlers.appendWriterT_run_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms appendWriterT_run_bind

/-- info: 'ThresholdLeanXmss.Handlers.appendWriterT_run_lift' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms appendWriterT_run_lift

/-- info: 'ThresholdLeanXmss.Handlers.writerT_run_mk' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms writerT_run_mk

/-- info: 'ThresholdLeanXmss.Handlers.optionT_run_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms optionT_run_pure

/-- info: 'ThresholdLeanXmss.Handlers.optionT_run_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms optionT_run_bind

/-- info: 'ThresholdLeanXmss.Handlers.optionT_run_lift' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms optionT_run_lift

/-- info: 'ThresholdLeanXmss.Handlers.optionT_run_failure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms optionT_run_failure

/-- info: 'ThresholdLeanXmss.Handlers.cache_empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms cache_empty

/-- info: 'ThresholdLeanXmss.Handlers.cache_cacheQuery_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms cache_cacheQuery_self

/-- info: 'ThresholdLeanXmss.Handlers.cache_cacheQuery_of_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms cache_cacheQuery_of_ne

/-- info: 'ThresholdLeanXmss.Handlers.cache_ext' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cache_ext

/-- info: 'ThresholdLeanXmss.Handlers.cache_exists' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms cache_exists

/-- info: 'ThresholdLeanXmss.Handlers.randomOracle_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomOracle_run

/-- info: 'ThresholdLeanXmss.Handlers.unifFwdImpl_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unifFwdImpl_run

/-- info: 'ThresholdLeanXmss.Handlers.withAddCost_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withAddCost_run

/-- info: 'ThresholdLeanXmss.Handlers.isQueryBoundP_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms isQueryBoundP_pure

/-- info: 'ThresholdLeanXmss.Handlers.isQueryBoundP_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isQueryBoundP_query_bind

/-- info: 'ThresholdLeanXmss.Handlers.not_isQueryBoundP_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_isQueryBoundP_zero

/-- info: 'ThresholdLeanXmss.Handlers.isQueryBoundP_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isQueryBoundP_unique

/-- info: 'ThresholdLeanXmss.Handlers.prfRealRun_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfRealRun_eq

/-- info: 'ThresholdLeanXmss.Handlers.prfIdealRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfIdealRun_eq

/-- info: 'ThresholdLeanXmss.Handlers.simulateQ_prfRealAnswer_liftComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_prfRealAnswer_liftComp

/-- info: 'ThresholdLeanXmss.Handlers.simulateQ_prfIdealAnswer_liftComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulateQ_prfIdealAnswer_liftComp

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_sample_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_sample_local

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_ro_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_ro_local

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_local_simulator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_local_simulator

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_local_party' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_local_party

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_sample_functionality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_sample_functionality

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_ro_functionality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_ro_functionality

/-- info: 'ThresholdLeanXmss.Handlers.liftComp_sample_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_sample_stream

/-- info: 'ThresholdLeanXmss.Handlers.runWorld_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runWorld_eq

/-- info: 'ThresholdLeanXmss.Handlers.runSigningWorld_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runSigningWorld_eq

/-- info: 'ThresholdLeanXmss.Handlers.accepts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepts_eq

/-- info: 'ThresholdLeanXmss.Handlers.signingAccepts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingAccepts_eq

/-- info: 'ThresholdLeanXmss.Handlers.hasHashQueryBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasHashQueryBound_iff

/-- info: 'ThresholdLeanXmss.Handlers.hasSigningQueryBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasSigningQueryBound_iff

/-- info: 'ThresholdLeanXmss.Handlers.prfRealRun_prgReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfRealRun_prgReduction

/-- info: 'ThresholdLeanXmss.Handlers.prfIdealRun_prgReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfIdealRun_prgReduction

/-- info: 'ThresholdLeanXmss.Handlers.treeSuccessStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSuccessStatement_iff

/-- info: 'ThresholdLeanXmss.Handlers.signingCorrectnessStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCorrectnessStatement_iff

end ThresholdLeanXmss.Handlers
