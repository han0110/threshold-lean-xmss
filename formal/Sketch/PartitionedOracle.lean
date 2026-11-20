import Sketch.PrivateTable

/-!
# An emulator that answers a set of domains from its own table

A cell predicate `Q` on the inputs of `H` splits the cache of the world. `isPrivate Q` marks the local
calls that touch a cell with `Q`, namely `H` at such a cell and `PRG` whose cell `.streamKey key` has `Q`.

* `tableImpl Q prims` answers each private call of an emulator from its own lazy table with the step of
  the world, and forwards each other call.
* `simulate_frame` shows that a world computation with only `WorldSafe Q` queries reads and writes only
  the public cells.
* `adversary_coupling` and `coupling` show that the run of an emulator on the world equals its run with
  the private table, with the table merged into the cache. The first one is for one computation on the
  counted copy, and the second one for an emulator under an environment whose steps are safe.
* `emulate_run'` gives the law of the result from a cache with empty private cells.
* `accepts_privateTable'` gives `accepts_privateTable` again as the instance `Q = isSetupQuery`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmss.Sketch.Partitioned

variable {C : Committee} (Q : Query C → Bool)

/-! ## The private domains -/

/-- A local call that touches a cell with `Q`. -/
def isPrivate : (LocalSpec C).Domain → Bool
  | .inl _ => false
  | .inr (.inl q) => Q q
  | .inr (.inr x) => Q (.streamKey x.2.1)

/-- A query of the world that is no private call on either copy and no programming query. -/
def WorldSafe : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => isPrivate Q t = false
  | .inl (.inr _) => False
  | .inr t => isPrivate Q t = false

/-- The cache with the cells with `Q` from `p` and the other cells from `s`. -/
def merge (s p : HashCache C) : HashCache C := QueryCache.ofFn fun q => if Q q then p q else s q

/-- The handler of an emulator on `LocalSpec C + E`. A private call runs the step of the world on the
table with private coins, and each other call goes on. -/
def tableImpl (prims : Primitives) {κ : Type} (E : OracleSpec κ) :
    QueryImpl (LocalSpec C + E) (StateT (HashCache C) (OracleComp (LocalSpec C + E))) := fun t =>
  match t with
  | .inl t =>
      if isPrivate Q t then StateT.mk fun table => liftComp ((localAnswer prims t).run table) _
      else liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C + E) (.inl t)))
  | .inr e => liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C + E) (.inr e)))

/-- The handler of an emulator on `LocalSpec C` alone. -/
def tableLocal (prims : Primitives) :
    QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (LocalSpec C))) := fun t =>
  if isPrivate Q t then StateT.mk fun table => liftComp ((localAnswer prims t).run table) _
  else liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))

/-- An environment for an emulator. A local call goes to the counted copy, and a call in `E` runs `env`. -/
def withEnv {κ : Type} {E : OracleSpec κ} {σ : Type} (env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))) :
    QueryImpl (LocalSpec C + E) (StateT σ (OracleComp (WorldSpec C))) :=
  (((fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) :
      QueryImpl (LocalSpec C) (StateT σ (OracleComp (WorldSpec C)))) + env : QueryImpl _ _)

/-- Each step of `env` makes only `WorldSafe Q` queries. -/
def EnvSafe {κ : Type} {E : OracleSpec κ} {σ : Type} (env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))) :
    Prop :=
  ∀ e st, AllQueriesSatisfy ((env e).run st) (WorldSafe Q)

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
  · exact hashAnswer_frame prims q (merge Q · p) s (merge_read_left Q ht s p) (merge_write_left Q ht s p)
  · change (prgAnswer prims x).run (merge Q s p) = (fun z => (z.1, merge Q z.2 p)) <$> (prgAnswer prims x).run s
    simp only [prgAnswer, StateT.run_bind,
      hashAnswer_frame prims _ (merge Q · p) s (merge_read_left Q ht s p) (merge_write_left Q ht s p),
      bind_map_left, map_bind, StateT.run_pure, map_pure]

/-- A private call reads and writes only the cells of `p`. -/
theorem localAnswer_right (prims : Primitives) (t : (LocalSpec C).Domain) (ht : isPrivate Q t = true)
    (s p : HashCache C) :
    (localAnswer prims t).run (merge Q s p) =
      (fun z => (z.1, merge Q s z.2)) <$> (localAnswer prims t).run p := by
  rcases t with n | q | x
  · exact absurd ht (by simp [isPrivate])
  · exact hashAnswer_frame prims q (merge Q s ·) p (merge_read_right Q ht s p) (merge_write_right Q ht s p)
  · change (prgAnswer prims x).run (merge Q s p) = (fun z => (z.1, merge Q s z.2)) <$> (prgAnswer prims x).run p
    simp only [prgAnswer, StateT.run_bind,
      hashAnswer_frame prims _ (merge Q s ·) p (merge_read_right Q ht s p) (merge_write_right Q ht s p),
      bind_map_left, map_bind, StateT.run_pure, map_pure]

theorem baseAnswer_frame (prims : Primitives) (t : (WorldSpec C).Domain) (ht : WorldSafe Q t)
    (s p : HashCache C) :
    (baseAnswer prims t).run (merge Q s p) = (fun z => (z.1, merge Q z.2 p)) <$> (baseAnswer prims t).run s := by
  rcases t with (t | x) | t
  · exact localAnswer_left Q prims t ht s p
  · exact ht.elim
  · exact localAnswer_left Q prims t ht s p

/-- A world computation with only `WorldSafe Q` queries reads and writes only the cells of `s`. -/
theorem simulate_frame (prims : Primitives) {α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy oa (WorldSafe Q)) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) oa).run (merge Q s p) =
      (fun z => (z.1, merge Q z.2 p)) <$> (simulateQ (baseAnswer prims) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self]
    rw [baseAnswer_frame Q prims t h.1 s p, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ (h.2 _) z.2

theorem simulate_frame_run' (prims : Primitives) {α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : AllQueriesSatisfy oa (WorldSafe Q)) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) oa).run' (merge Q s p) = (simulateQ (baseAnswer prims) oa).run' s := by
  rw [StateT.run'_eq, StateT.run'_eq, simulate_frame Q prims h s p, Functor.map_map]

/-! ## One computation on the counted copy -/

-- Ported from `formal/ThresholdLeanXmssSecurity/Proof/Check.lean` (`adversary_bind`).
theorem adversary_bind {α β : Type} (oa : OracleComp (LocalSpec C) α) (k : α → OracleComp (LocalSpec C) β) :
    worldRoles.adversary (oa >>= k) = worldRoles.adversary oa >>= fun a => worldRoles.adversary (k a) := by
  change counted (liftComp (oa >>= k) (SimulatorSpec C)) = _
  rw [liftComp_bind, ThresholdLeanXmssSecurity.counted_bind]
  rfl

/-- A private sample on the counted copy keeps the cache. -/
theorem adversary_liftComp (prims : Primitives) {α : Type} (pc : ProbComp α) (c : HashCache C) :
    (simulateQ (baseAnswer prims) (worldRoles.adversary (liftComp pc (LocalSpec C)))).run c =
      (fun a => (a, c)) <$> pc := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    have e : liftComp (liftM (unifSpec.query n) : ProbComp _) (LocalSpec C) =
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl n)) : OracleComp _ _) := rfl
    rw [liftComp_bind, e, adversary_bind, simulateQ_bind,
      ThresholdLeanXmssSecurity.SeedHitProof.simulateQ_adversary_query, StateT.run_bind]
    change ((unifFwdImpl (Query C →ₒ HashOutput) n).run c >>= _) = _
    simp [unifFwdImpl]
    exact bind_congr fun a => ih a

/-- The run of one computation on the counted copy equals its run with the private table, with the table
merged into the cache. -/
theorem adversary_coupling (prims : Primitives) {α : Type} (b : OracleComp (LocalSpec C) α) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) (worldRoles.adversary b)).run (merge Q s p) =
      (fun z => (z.1.1, merge Q z.2 z.1.2)) <$>
        (simulateQ (baseAnswer prims) (worldRoles.adversary ((simulateQ (tableLocal Q prims) b).run p))).run s := by
  induction b using OracleComp.inductionOn generalizing s p with
  | pure x => simp
  | query_bind t k ih =>
    rw [adversary_bind, simulateQ_bind, StateT.run_bind,
      ThresholdLeanXmssSecurity.SeedHitProof.simulateQ_adversary_query, simulateQ_bind, StateT.run_bind,
      adversary_bind, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    by_cases ht : isPrivate Q t = true
    · have e : (tableLocal Q prims t).run p = liftComp ((localAnswer prims t).run p) (LocalSpec C) := by
        simp [tableLocal, ht]
      change (localAnswer prims t).run (merge Q s p) >>= _ = _
      rw [e, adversary_liftComp, localAnswer_right Q prims t ht s p, bind_map_left, bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 s z.2
    · have hf : isPrivate Q t = false := by simpa using ht
      have e : worldRoles.adversary ((tableLocal Q prims t).run p) =
          worldRoles.adversary (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)) >>=
            fun a => pure (a, p) := by
        simp only [tableLocal, hf, Bool.false_eq_true, ite_false]
        rw [StateT.run_monadLift, monadLift_self]
        exact adversary_bind _ _
      rw [e, simulateQ_bind, StateT.run_bind, ThresholdLeanXmssSecurity.SeedHitProof.simulateQ_adversary_query,
        bind_assoc]
      change (localAnswer prims t).run (merge Q s p) >>= _ = _ <$> ((localAnswer prims t).run s >>= _)
      rw [localAnswer_left Q prims t hf s p, bind_map_left]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_bind]
      exact bind_congr fun z => ih z.1 z.2 p

/-! ## An emulator under an environment -/

theorem withEnv_local (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    (env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))) (t : (LocalSpec C).Domain) (st : σ) (c : HashCache C) :
    (simulateQ (baseAnswer prims) ((withEnv env (.inl t)).run st)).run c =
      (fun z => ((z.1, st), z.2)) <$> (localAnswer prims t).run c := by
  have e : (withEnv env (.inl t)).run st =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, st) := rfl
  rw [e, simulateQ_bind, ThresholdLeanXmssSecurity.SeedHitProof.simulateQ_adversary_query]
  simp only [simulateQ_pure, bind_pure_comp, StateT.run_map]
  rfl

theorem withEnv_liftComp (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    (env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))) {α : Type} (pc : ProbComp α) (st : σ)
    (c : HashCache C) :
    (simulateQ (baseAnswer prims) ((simulateQ (withEnv env) (liftComp pc (LocalSpec C + E))).run st)).run c =
      (fun a => ((a, st), c)) <$> pc := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    have e : liftComp (liftM (unifSpec.query n) : ProbComp _) (LocalSpec C + E) =
        (liftM ((LocalSpec C + E).query (.inl (.inl n))) : OracleComp _ _) := rfl
    rw [liftComp_bind, e, simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map, StateT.run_bind, simulateQ_bind]
    rw [withEnv_local, bind_map_left]
    change ((unifFwdImpl (Query C →ₒ HashOutput) n).run c >>= _) = _
    simp [unifFwdImpl, ih]

theorem withEnv_local_safe {κ : Type} {E : OracleSpec κ} {σ : Type}
    (env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))) (t : (LocalSpec C).Domain)
    (ht : isPrivate Q t = false) (st : σ) :
    AllQueriesSatisfy ((withEnv env (.inl t)).run st) (WorldSafe Q) := by
  have e : (withEnv env (.inl t)).run st =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, st) := rfl
  rw [e, ThresholdLeanXmssSecurity.adversary_query]
  exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inl t)) _).2 ht)
    fun _ => allQueriesSatisfy_pure _ _

/-- A call that the emulator forwards to its environment. -/
theorem step_forward (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    (env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))) (t : (LocalSpec C + E).Domain)
    (hT : tableImpl Q prims E t = StateT.lift (OracleComp.lift (OracleSpec.query t)))
    (hsafe : ∀ st, AllQueriesSatisfy ((withEnv env t).run st) (WorldSafe Q)) (st : σ) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) ((withEnv env t).run st)).run (merge Q s p) =
      (fun z => ((z.1.1.1, z.1.2), merge Q z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          ((simulateQ (withEnv env) ((tableImpl Q prims E t).run p)).run st)).run s := by
  rw [hT, simulate_frame Q prims (hsafe st) s p]
  simp only [StateT.run_lift, simulateQ_spec_query, bind_pure_comp, simulateQ_map, StateT.run_map,
    Functor.map_map]

/-- One call of the emulator in the two runs. -/
theorem step_coupling (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    {env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))} (henv : EnvSafe Q env)
    (t : (LocalSpec C + E).Domain) (st : σ) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) ((withEnv env t).run st)).run (merge Q s p) =
      (fun z => ((z.1.1.1, z.1.2), merge Q z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          ((simulateQ (withEnv env) ((tableImpl Q prims E t).run p)).run st)).run s := by
  rcases t with t | e
  · by_cases ht : isPrivate Q t = true
    · have e : (tableImpl Q prims E (.inl t)).run p = liftComp ((localAnswer prims t).run p) (LocalSpec C + E) := by
        simp [tableImpl, ht]
      rw [e, withEnv_liftComp, withEnv_local, localAnswer_right Q prims t ht s p]
      simp [Functor.map_map]
    · have hf : isPrivate Q t = false := by simpa using ht
      exact step_forward Q prims env _ (by simp [tableImpl, hf]; rfl)
        (fun st => withEnv_local_safe Q env t hf st) st s p
  · exact step_forward Q prims env (.inr e) rfl (fun st => henv e st) st s p

/-- The run of an emulator on the world equals its run with the private table, with the table merged into
the cache. -/
theorem coupling (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    {env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))} (henv : EnvSafe Q env)
    {α : Type} (b : OracleComp (LocalSpec C + E) α) (st : σ) (s p : HashCache C) :
    (simulateQ (baseAnswer prims) ((simulateQ (withEnv env) b).run st)).run (merge Q s p) =
      (fun z => ((z.1.1.1, z.1.2), merge Q z.2 z.1.1.2)) <$>
        (simulateQ (baseAnswer prims)
          ((simulateQ (withEnv env) ((simulateQ (tableImpl Q prims E) b).run p)).run st)).run s := by
  induction b using OracleComp.inductionOn generalizing st s p with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rw [step_coupling Q prims henv t st s p, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ _ _ _

/-- From a cache with empty private cells, the emulator with the private table and a safe rest `post` give
the same law of the result as the emulator on the world. -/
theorem emulate_run' (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    {env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))} (henv : EnvSafe Q env)
    {α γ : Type} (b : OracleComp (LocalSpec C + E) α) (st : σ) (post : α × σ → OracleComp (WorldSpec C) γ)
    (hpost : ∀ z, AllQueriesSatisfy (post z) (WorldSafe Q)) (s : HashCache C) :
    (simulateQ (baseAnswer prims) ((simulateQ (withEnv env) b).run st >>= post)).run' (merge Q s ∅) =
      (simulateQ (baseAnswer prims)
        ((simulateQ (withEnv env) ((simulateQ (tableImpl Q prims E) b).run' ∅)).run st >>= post)).run' s := by
  rw [run'_bind, run'_bind, coupling Q prims henv, bind_map_left]
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, bind_map_left]
  exact bind_congr fun z => simulate_frame_run' Q prims (hpost _) _ _

/-- From the empty cache, the emulator with the private table and a safe rest `post` give the same law of
the result as the emulator on the world. -/
theorem emulate_run'_empty (prims : Primitives) {κ : Type} {E : OracleSpec κ} {σ : Type}
    {env : QueryImpl E (StateT σ (OracleComp (WorldSpec C)))} (henv : EnvSafe Q env)
    {α γ : Type} (b : OracleComp (LocalSpec C + E) α) (st : σ) (post : α × σ → OracleComp (WorldSpec C) γ)
    (hpost : ∀ z, AllQueriesSatisfy (post z) (WorldSafe Q)) :
    (simulateQ (baseAnswer prims) ((simulateQ (withEnv env) b).run st >>= post)).run' ∅ =
      (simulateQ (baseAnswer prims)
        ((simulateQ (withEnv env) ((simulateQ (tableImpl Q prims E) b).run' ∅)).run st >>= post)).run' ∅ := by
  rw [← emulate_run' Q prims henv b st post hpost ∅, merge_empty]

/-! ## The instance of the setup domains -/

theorem isPrivate_setup (x : (RoSpec C).Domain) : isPrivate isSetupQuery (.inr x) = isSetupRo x := by
  rcases x with q | y <;> rfl

theorem worldSafe_setup (t : (WorldSpec C).Domain) (h : ThresholdLeanXmss.Sketch.WorldSafe t) :
    WorldSafe isSetupQuery t := by
  rcases t with ((n | x) | y) | (n | x)
  · rfl
  · simpa [ThresholdLeanXmss.Sketch.WorldSafe, SetupOnly, WorldSafe, isPrivate_setup] using h
  · exact h.elim
  · rfl
  · simpa [ThresholdLeanXmss.Sketch.WorldSafe, SetupOnly, WorldSafe, isPrivate_setup] using h

/-- On a setup domain, one step of the private table of `PrivateTable.lean` is the step of the world. -/
theorem privateStep_eq (prims : Primitives) (x : (RoSpec C).Domain) (hx : isSetupRo x = true) :
    privateStep prims.aes x = localAnswer prims (.inr x) := by
  rcases x with q | y
  · have hq : isSetupQuery q = true := hx
    cases q <;> first | rfl | exact absurd hq (by simp [isSetupQuery])
  · rfl

/-- The wrapper of `PrivateTable.lean` is the emulator of the setup domains. -/
theorem privateImpl_eq (prims : Primitives) :
    privateImpl (C := C) prims.aes = tableImpl isSetupQuery prims (TsigSpec C) := by
  funext t
  rcases t with (n | x) | q
  · rfl
  · by_cases hx : isSetupRo x = true
    · simp only [privateImpl, tableImpl, hx, isPrivate_setup, ite_true, privateStep_eq prims x hx]
    · simp [privateImpl, tableImpl, hx, isPrivate_setup]
  · rfl

open ThresholdLeanXmssSecurity.SigningCoreProof in
/-- `accepts_privateTable` of `PrivateTable.lean` as the instance `Q = isSetupQuery`. -/
theorem accepts_privateTable' (prims : Primitives) (B : TsigAdversary C) :
    accepts prims (tsigGame (privateTable prims.aes B)) = accepts prims (tsigGame B) := by
  rw [accepts_eq, accepts_eq]
  refine congrArg ENNReal.toReal (EvalDistEq.prEvent_eq ?_ _)
  unfold tsigGame
  rw [run'_bind, run'_bind]
  conv_rhs => rw [← merge_empty isSetupQuery,
    simulate_frame isSetupQuery prims (dealerKeyGen_safe.mono worldSafe_setup) ∅ ∅, bind_map_left]
  refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  obtain ⟨output, c⟩ := z
  have hmem : output ∈ support (dealerKeyGen (C := C)) := by
    refine support_simulateQ_run'_subset (baseAnswer prims) _ ∅ ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨_, hz, rfl⟩
  cases output with
  | none => exact EvalDistEq.rfl
  | some dealt =>
    have hdealt := dealerKeyGen_support _ hmem dealt rfl
    have henv : EnvSafe isSetupQuery (tsigOracles (fun oa => honestLift oa) dealt) :=
      fun q st => (tsigOracles_safe freeLift_safe hdealt q st).mono worldSafe_setup
    dsimp only
    rw [game_eq, game_eq]
    have h := emulate_run' isSetupQuery prims henv (B ⟨dealt.top.root, dealt.parameter⟩ dealt.top) tsigInit
      (fun z => forgeryWins (fun oa => worldRoles.honest (liftComp oa _)) dealt z.2 z.1)
      (fun z => (forgeryWins_safe freeLift_safe hdealt _ _).mono worldSafe_setup) c
    rw [← privateImpl_eq] at h
    have e : gameOracles dealt = withEnv (tsigOracles (fun oa => honestLift oa) dealt) := rfl
    unfold privateTable
    rw [e, h]

/-- info: 'ThresholdLeanXmss.Sketch.Partitioned.accepts_privateTable'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepts_privateTable'

/-- info: 'ThresholdLeanXmss.Sketch.Partitioned.emulate_run'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emulate_run'

/-- info: 'ThresholdLeanXmss.Sketch.Partitioned.adversary_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms adversary_coupling

end ThresholdLeanXmss.Sketch.Partitioned
