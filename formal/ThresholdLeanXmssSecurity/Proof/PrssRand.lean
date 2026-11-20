import ThresholdLeanXmssSecurity.Proof.StreamWorld
import ThresholdLeanXmssSecurity.Base.SetupSimulators

/-!
# The PRSS streams from dealt keys

`prssStreams` and `callStreams` give the PRSS outputs of one operator from the stream of each key,
and `dealtKey` gives the dealt key of a name. `hashAnswer_streamKey_cached` and
`programAnswer_streamKey_cached` keep a stream key in the cache, and `isQueryBoundP_prgBits_zero`
bounds the calls of the bits of a PRG. `streamWorld_presample` samples empty cells of the hidden
cache first as a uniform table. `frandShare_eq_clipOutput` reads the PRSS output of an honest
receiver from the cached streams, and `elementSplit` cuts a table of bits into field elements.
-/

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The real run -/

/-- The PRSS outputs of operator `i` in one round, as `prssRandomness` computes them. `stream` gives
the stream of a key. -/
def prssStreams {R : Type} [Zero R] (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R))
    (prss : PrssKeys C) (i : C.Party) : OracleComp (RoSpec C) (PrssOutput C R) := do
  let r ← C.terms.mapM fun T => if i ∈ C.holders T then stream (.term T) (prss.term T) else pure fun _ => 0
  let Z ← C.parties.mapM fun j =>
    if h : j = i then pure fun _ => 0 else stream (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)
  pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)

/-- The output of one call of operator `i` at round label `ρ`, as `randCall` computes it. `bits`
gives the stream bits of a key. -/
def callStreams (K : Constants C E) (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit))
    (prss : PrssKeys C) (i : C.Party) (ρ : ℕ) : RandCall → OracleComp (RoSpec C) (RandOutput C E)
  | .elements idx count => (fun o => .inl (clipOutput count o)) <$> prssStreams (fun name key =>
      (fun b g => K.encode.symm fun e => b (elementBits * g + e)) <$> bits name key ρ idx (elementBits * count))
      prss i
  | .bits idx count => (fun o => .inr (clipOutput count o)) <$> prssStreams (fun name key =>
      bits name key ρ idx count) prss i

/-- The dealt key of a name. -/
def dealtKey (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) : KeyName C → Option HashOutput
  | .parameter => none
  | .term T => some (term T)
  | .pair p => some (pair p)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem oracleStep_map {ι : Type} {G : OracleSpec ι} {α β : Type} (f : α → β)
    (oa : OracleComp (RoSpec C) α) :
    oracleStep (C := C) (E := E) (G := G) (f <$> oa) = f <$> oracleStep oa := by
  simp only [oracleStep, localStep, liftComp_map]
  apply OptionT.ext
  simp [OptionT.run_map, OptionT.run_lift]

omit [Fintype E] [DecidableEq E] in
/-- One call is one oracle step of `callStreams` at the label of the state, and it moves the label. -/
private theorem randCall_run {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C)
    (call : RandCall) (st : RunState C) :
    (randCall (G := G) K ctx call).run st = (fun o => (o, { st with label := st.label + 1 })) <$>
      oracleStep (callStreams K prgBits ctx.prss ctx.self st.label call) := by
  cases call <;> simp [randCall, prssRandomness, freshLabel, callStreams, prssStreams, elementCodec,
    bitCodec, oracleStep_bind, oracleStep_map, StateT.run_bind, map_bind, Functor.map_map]

end ThresholdLeanXmssSecurity

end

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- A hash query of a stream key caches it. -/
theorem hashAnswer_streamKey_cached (prims : Primitives) (k : HashOutput) (s : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims (.streamKey k)).run s), z.2 (.streamKey k) ≠ none := by
  intro z hz
  rw [hashAnswer_cached prims (by rintro ⟨_, h, _⟩; cases h) s z hz]
  simp

theorem onJointHash_support {α : Type} (m : StateT (HashCache C) ProbComp α) (s : KeyJointState C) :
    ∀ r ∈ support ((onJointHash m).run s), ∃ z ∈ support (m.run s.hash), r = (z.1, { s with hash := z.2 }) := by
  intro r hr
  simp only [onJointHash, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  exact ⟨z, hz, rfl⟩

theorem prgAnswer_support (prims : Primitives) (x : PrgInput C) (h : HashCache C) :
    ∀ z ∈ support ((prgAnswer prims x).run h),
      ∃ w ∈ support ((hashAnswer prims (.streamKey x.2.1)).run h), z.2 = w.2 := by
  intro z hz
  simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- A programming of a stream key leaves it cached. -/
theorem programAnswer_streamKey_cached (k v : HashOutput) (h : HashCache C) :
    ∀ z ∈ support ((programAnswer (.streamKey k, v)).run h), z.2 (.streamKey k) ≠ none := by
  intro z hz
  by_cases hc : (h (.streamKey k)).isSome
  · have he : (programAnswer (C := C) (.streamKey k, v)).run h = pure (false, h) := by
      simp [programAnswer, hc]
    rw [he, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simpa [Option.isSome_iff_ne_none] using hc
  · have he : (programAnswer (C := C) (.streamKey k, v)).run h =
        pure (true, h.cacheQuery (.streamKey k) v) := by
      simp [programAnswer, hc]
    rw [he, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp

end ThresholdLeanXmssSecurity

end

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## Uniform tables -/

/-- A computation of `H` and `PRG` with no call of `P` keeps this bound in the local oracles. -/
theorem isQueryBoundP_liftComp_ro (P : (LocalSpec C).Domain → Prop) [DecidablePred P] {α : Type}
    (oa : OracleComp (RoSpec C) α) (h : IsQueryBoundP oa (fun t => P (.inr t)) 0) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) P 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ?_⟩
    simpa using ih u (by simpa using h.2 u)

/-- The bits of a PRG make no call of `P` when `P` holds at no position of its name and key. -/
theorem isQueryBoundP_prgBits_zero (P : (RoSpec C).Domain → Prop) [DecidablePred P] (name : KeyName C)
    (k : HashOutput) (ρ idx count : ℕ) (hP : ∀ position, ¬ P (.inr (name, k, ρ, idx, position))) :
    IsQueryBoundP (prgBits name k ρ idx count) P 0 := by
  unfold prgBits
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure _ _ 0
  simpa using queryBound_mapM P (fun position =>
    (query (spec := RoSpec C) (.inr (name, k, ρ, idx, position)) : OracleComp (RoSpec C) Bit)) 0
    (List.range count) fun position _ => (isQueryBoundP_query_iff P _ _).2 fun h => absurd h (hP position)

/-! ## A private sample -/

section Bound

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)
  (Z : Distinguisher C A.State (List (RandOutput C E))) (prims : Primitives)

/-- A private sample makes no call of `P` when `P` holds at no sample. -/
theorem isQueryBoundP_liftComp_prob_of_sample (P : (LocalSpec C).Domain → Prop) [DecidablePred P]
    (hP : ∀ u, ¬ P (.inl u)) {α : Type} (p : ProbComp α) : IsQueryBoundP (liftComp p (LocalSpec C)) P 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inl t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (hP t), fun u => ?_⟩
    simpa only [hP t, ite_false] using ih u

end Bound

end ThresholdLeanXmssSecurity

end

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

section Draws

set_option backward.isDefEq.respectTransparency false

/-! ## One stream -/

/-- Writing two different cells of the hidden cache commutes. -/
private theorem hiddenCache_cacheQuery_comm (c : HiddenCache C) {x y : (KeyName C × HashOutput) × ℕ × ℕ × ℕ}
    (hne : x ≠ y) (u v : Bit) : (c.cacheQuery x u).cacheQuery y v = (c.cacheQuery y v).cacheQuery x u := by
  simp only [QueryCache.cacheQuery, QueryCache.toFn_ofFn]
  exact congrArg QueryCache.ofFn (Function.update_comm hne _ _ _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The presampling step of `streamWorld_presample_cell` at a query that only uses the hash cache. -/
private theorem presample_cell_onHash (prims : Primitives) (D : C.Coalition) {α : Type}
    (x : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) (t : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α)
    (m : StateT (HashCache C) ProbComp ((WorldSpec C).Range t)) (hm : streamWorld prims D t = onHash m)
    (ih : ∀ u (s : HashCache C) (c : HiddenCache C), c x = none →
      (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) (k u)).run (s, c) =ᵈ
        (($ᵗ Bit) >>= fun b => (fun r => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) (k u)).run (s, c.cacheQuery x b)))
    (s : HashCache C) (c : HiddenCache C) (hx : c x = none) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
        ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= k)).run (s, c) =ᵈ
      (($ᵗ Bit) >>= fun b => (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
        ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= k)).run (s, c.cacheQuery x b)) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
    StateT.run_bind, hm, onHash, StateT.run_mk, bind_map_left, map_bind]
  exact (EvalDistEq.bind_right _ fun r : (WorldSpec C).Range t × HashCache C => ih r.1 r.2 c hx).trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One empty cell of the hidden cache can be sampled first. The result and the hash cache keep
their law. -/
theorem streamWorld_presample_cell (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (x : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) :
    ∀ (s : HashCache C) (c : HiddenCache C), c x = none →
      (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) oa).run (s, c) =ᵈ
        (($ᵗ Bit) >>= fun b => (fun r => (r.1, r.2.1)) <$>
          (simulateQ (streamWorld prims D) oa).run (s, c.cacheQuery x b)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s c _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    intro s c hx
    rcases t with ((u | q | y) | p) | (u | q | y)
    · exact presample_cell_onHash prims D x _ k _ rfl ih s c hx
    · exact presample_cell_onHash prims D x _ k _ rfl ih s c hx
    · exact presample_cell_onHash prims D x _ k _ rfl ih s c hx
    · exact presample_cell_onHash prims D x _ k _ rfl ih s c hx
    · exact presample_cell_onHash prims D x _ k _ rfl ih s c hx
    · exact presample_cell_onHash prims D x _ k _ rfl ih s c hx
    · by_cases h : Hidden D y.1
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
          StateT.run_bind, streamWorld, h, ↓reduceIte, StateT.run_mk, bind_map_left, map_bind]
        set z : (KeyName C × HashOutput) × ℕ × ℕ × ℕ := ((y.1, y.2.1), y.2.2)
        by_cases hz : z = x
        · rw [hz, QueryImpl.withCaching_run_none _ hx]
          simp only [bind_map_left]
          refine EvalDistEq.bind_right _ fun b => ?_
          rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self c x b), pure_bind]
        · rcases hc : c z with _ | v
          · have hr : ∀ b : Bit, ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle z).run
                (c.cacheQuery x b) = (fun u => (u, (c.cacheQuery x b).cacheQuery z u)) <$> uniformSampleImpl z :=
              fun b => QueryImpl.withCaching_run_none _ ((QueryCache.cacheQuery_of_ne c _ hz).trans hc)
            rw [QueryImpl.withCaching_run_none _ hc]
            simp only [hr, bind_map_left]
            refine (EvalDistEq.bind_right _ fun v => ih v s _
              ((QueryCache.cacheQuery_of_ne c _ (Ne.symm hz)).trans hx)).trans ?_
            refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
            simp only [hiddenCache_cacheQuery_comm c hz]
            exact .rfl
          · have hr : ∀ b : Bit, ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle z).run
                (c.cacheQuery x b) = pure (v, c.cacheQuery x b) :=
              fun b => QueryImpl.withCaching_run_some _ ((QueryCache.cacheQuery_of_ne c _ hz).trans hc)
            rw [QueryImpl.withCaching_run_some _ hc]
            simp only [hr, pure_bind]
            exact ih v s c hx
      · exact presample_cell_onHash prims D x _ k (localAnswer prims (.inr (.inr y)))
          (by simp only [streamWorld, h, ↓reduceIte]) ih s c hx

/-- A uniform table of `n + 1` bits is a uniform bit and a uniform table of `n` bits. -/
private theorem uniformFin_succ_bind {β : Type} (n : ℕ) (F : (Fin (n + 1) → Bit) → ProbComp β) :
    (($ᵗ (Fin (n + 1) → Bit)) >>= F) =ᵈ
      (($ᵗ Bit) >>= fun b => ($ᵗ (Fin n → Bit)) >>= fun v => F (Fin.cons b v)) := by
  refine (EvalDistEq.bind_left (evalDist_sequenceFin_uniform (n + 1)).symm F).trans ?_
  simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
  exact EvalDistEq.bind_right _ fun b => EvalDistEq.bind_left (evalDist_sequenceFin_uniform n) _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Distinct empty cells of the hidden cache can be sampled first as a uniform table. The result and
the hash cache keep their law. -/
theorem streamWorld_presample (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) {n : ℕ} (addr : Fin n → (KeyName C × HashOutput) × ℕ × ℕ × ℕ)
    (ha : Function.Injective addr) (s : HashCache C) (c : HiddenCache C) (hc : ∀ i, c (addr i) = none) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) oa).run (s, c) =ᵈ
      (($ᵗ (Fin n → Bit)) >>= fun vals => (fun r => (r.1, r.2.1)) <$>
        (simulateQ (streamWorld prims D) oa).run (s, cacheFin addr vals c)) := by
  induction n generalizing c with
  | zero =>
    simp only [cacheFin]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | succ n ih =>
    refine (streamWorld_presample_cell prims D oa (addr 0) s c (hc 0)).trans ?_
    refine (EvalDistEq.bind_right _ fun b => ih (fun i => addr i.succ) (ha.comp (Fin.succ_injective n)) _
      fun i => (QueryCache.cacheQuery_of_ne c _ fun h => Fin.succ_ne_zero i (ha h)).trans (hc i.succ)).trans ?_
    refine EvalDistEq.trans ?_ (uniformFin_succ_bind n fun vals => (fun r => (r.1, r.2.1)) <$>
      (simulateQ (streamWorld prims D) oa).run (s, cacheFin addr vals c)).symm
    simp only [cacheFin, Fin.cons_zero, Fin.cons_succ]
    exact .rfl

/-! ## The streams of the calls -/

/-- The stream bits of a key. A hidden key reads its bits from the cache `c`, and another key
queries `PRG`. -/
def cachedBits (D : C.Coalition) (c : HiddenCache C) (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) :
    OracleComp (RoSpec C) (ℕ → Bit) :=
  if Hidden D name then pure fun g => if g < m then (c ((name, key), ρ, idx, g)).getD 0 else 0
  else prgBits name key ρ idx m

/-- The bit at position `g` of the stream of `name` at round `ρ` and index `idx`, read from the hidden
cache `c` under the dealt key. -/
def tableBit (c : HiddenCache C) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (name : KeyName C)
    (ρ idx g : ℕ) : Bit :=
  (c ((name, (dealtKey term pair name).getD 0), ρ, idx, g)).getD 0

/-- The keys of the known streams that an honest receiver computes. They are hashed only when a call
reads at least one position. -/
def knownKeys (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (calls : List RandCall) : List HashOutput :=
  if calls.any (fun call => decide (0 < call.streamBits)) then
    (C.terms.filter fun T => decide (KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T)).map term ++
      C.parties.flatMap fun j => C.parties.filterMap fun i =>
        if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then some (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
        else none
  else []

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hidden_pairOf (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    Hidden D (.pair (C.pairOf i j h)) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  simp only [Hidden, Committee.pairOf]
  split_ifs <;> simp [and_comm]

/-- From the hash cache `s`, the run of `oa` returns `v` and keeps the cache. -/
private def RunsPure (prims : Primitives) (s : HashCache C) {β : Type} (oa : OracleComp (LocalSpec C) β) (v : β) :
    Prop :=
  (simulateQ (localAnswer prims) oa).run s = pure (v, s)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem RunsPure.pure (prims : Primitives) (s : HashCache C) {β : Type} (v : β) :
    RunsPure prims s (pure v) v := by
  simp [RunsPure]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem RunsPure.bind {prims : Primitives} {s : HashCache C} {β γ : Type} {oa : OracleComp (LocalSpec C) β}
    {f : β → OracleComp (LocalSpec C) γ} {v : β} {w : γ} (h : RunsPure prims s oa v) (hf : RunsPure prims s (f v) w) :
    RunsPure prims s (oa >>= f) w := by
  simp only [RunsPure, simulateQ_bind, StateT.run_bind] at h hf ⊢
  rw [h, pure_bind]
  exact hf

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem RunsPure.map {prims : Primitives} {s : HashCache C} {β γ : Type} {oa : OracleComp (LocalSpec C) β}
    {v : β} (h : RunsPure prims s oa v) (f : β → γ) : RunsPure prims s (f <$> oa) (f v) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind (RunsPure.pure prims s _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem RunsPure.mapM {prims : Primitives} {s : HashCache C} {γ β : Type} {f : γ → OracleComp (RoSpec C) β}
    {g : γ → β} : ∀ l : List γ, (∀ x ∈ l, RunsPure prims s (liftComp (f x) (LocalSpec C)) (g x)) →
      RunsPure prims s (liftComp (l.mapM f) (LocalSpec C)) (l.map g)
  | [], _ => by simpa using RunsPure.pure prims s ([] : List β)
  | a :: l, h => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, List.map_cons]
    exact (h a List.mem_cons_self).bind ((RunsPure.mapM l fun x hx => h x (List.mem_cons_of_mem a hx)).bind
      (RunsPure.pure prims s _))

/-- The bits of `PRG(key, ρ, idx)` at the first `m` positions, from the cached answer of `H` at the key. -/
private def prgValue (prims : Primitives) (s : HashCache C) (key : HashOutput) (ρ idx m : ℕ) : ℕ → Bit :=
  fun g => ((List.range m).map fun p => prims.aes.eval (truncateHash ((s (.streamKey key)).getD 0)) (ρ, idx, p)).getD g 0

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem runsPure_prgBits (prims : Primitives) (s : HashCache C) (name : KeyName C) (key : HashOutput)
    (ρ idx m : ℕ) (hs : 0 < m → (s (.streamKey key)).isSome) :
    RunsPure prims s (liftComp (prgBits name key ρ idx m) (LocalSpec C)) (prgValue prims s key ρ idx m) := by
  unfold prgBits prgValue
  simp only [liftComp_bind, liftComp_pure]
  refine (RunsPure.mapM _ fun p hp => ?_).bind (RunsPure.pure prims s _)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hs (by have := List.mem_range.mp hp; omega))
  unfold RunsPure
  rw [simulateQ_localAnswer_liftComp]
  erw [simulateQ_query]
  change (prgAnswer prims (name, key, ρ, idx, p) >>= pure).run s = _
  simp only [prgAnswer, bind_pure, StateT.run_bind]
  rw [hashAnswer_run_cached prims (by rintro ⟨_, h, _⟩; cases h) hu]
  simp [hu]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem runsPure_knownStreams {prims : Primitives} {s : HashCache C} {R : Type} [Zero R] (D : C.Coalition)
    (receivers : Finset C.Party) (codec : Codec C E R) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (ρ idx count : ℕ) (val : KeyName C → HashOutput → ℕ → R)
    (hterm : ∀ T, KnownTo D.1 T ∧ (∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T) →
      RunsPure prims s (liftComp (codec.draw (.term T) (term T) ρ idx count) (LocalSpec C)) (val (.term T) (term T)))
    (hpair : ∀ j i (h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers),
      RunsPure prims s (liftComp (codec.draw (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
        (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) ρ idx count) (LocalSpec C))
        (val (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))))) :
    RunsPure prims s (liftComp (knownStreams D receivers codec term pair ρ idx count) (LocalSpec C))
      (fun T g => if g < count then (if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
          val (.term T) (term T) else fun _ => 0) g else 0,
        fun j i g => if g < count then (if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
          val (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
          else fun _ => 0) g else 0) := by
  unfold knownStreams
  simp only [liftComp_bind, liftComp_pure]
  refine (RunsPure.mapM (g := fun T => if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
    val (.term T) (term T) else fun _ => 0) _ fun T _ => ?_).bind ((RunsPure.mapM (g := fun j => C.parties.map fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
        val (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
      else fun _ => 0) _ fun j _ => RunsPure.mapM _ fun i _ => ?_).bind ?_)
  · split_ifs with h
    · exact hterm T h
    · exact RunsPure.pure prims s _
  · split_ifs with h
    · exact hpair j i h
    · exact RunsPure.pure prims s _
  · simp only [getD_terms_idxOf, getD_parties]
    exact RunsPure.pure prims s _

/-- The stream bits of `cachedBits` from the hash cache `s`. -/
private def cachedValue (prims : Primitives) (D : C.Coalition) (c : HiddenCache C) (s : HashCache C) (name : KeyName C)
    (key : HashOutput) (ρ idx m : ℕ) : ℕ → Bit :=
  if Hidden D name then fun g => if g < m then (c ((name, key), ρ, idx, g)).getD 0 else 0
  else prgValue prims s key ρ idx m

/-- The hash cache `s` holds every key of a known stream that an honest receiver computes. -/
private def KeysCached (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (s : HashCache C) : Prop :=
  (∀ T, KnownTo D.1 T ∧ (∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T) → (s (.streamKey (term T))).isSome) ∧
    ∀ j i (h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers),
      (s (.streamKey (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))))).isSome

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The share of `F_rand` at an honest receiver is the clipped output of its streams. `dec` reads one
value from the stream bits, and it reads only the first `m` bits for each of the `count` values. -/
private theorem frandShare_eq_clipOutput {R : Type} [Zero R] (prims : Primitives) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (c : HiddenCache C)
    (s : HashCache C) (ρ idx count m : ℕ) (dec : (ℕ → Bit) → ℕ → R)
    (hdec : ∀ F g, g < count → dec (fun g' => if g' < m then F g' else 0) g = dec F g) (i : C.Party)
    (hiD : i ∉ D.1) (hi : i ∈ receivers) :
    frandShare D count
      (fun T g => if g < count then (if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
        dec (prgValue prims s (term T) ρ idx m) else fun _ => 0) g else 0)
      (fun j i g => if g < count then (if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
        dec (prgValue prims s (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) ρ idx m) else fun _ => 0) g else 0)
      (fun T g => dec (fun g' => tableBit c term pair (.term T) ρ idx g') g)
      (fun p g => dec (fun g' => tableBit c term pair (.pair p) ρ idx g') g) i =
    clipOutput count
      (fun T => if i ∈ C.holders T then dec (cachedValue prims D c s (.term T) ((dealtPrssKeys term pair i).term T) ρ idx m)
        else fun _ => 0,
       fun j => if h : j = i then fun _ => 0 else
        dec (cachedValue prims D c s (.pair (C.pairOf i j (Ne.symm h))) ((dealtPrssKeys term pair i).pair j) ρ idx m)) := by
  refine Prod.ext (funext fun T => funext fun g => ?_) (funext fun j => funext fun g => ?_)
  · by_cases hT : i ∈ C.holders T
    · dsimp only [frandShare, clipOutput]
      rw [show (dealtPrssKeys term pair i).term T = term T by simp [dealtPrssKeys, hT]]
      have hex : ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T := ⟨i, hi, hiD, hT⟩
      by_cases hK : KnownTo D.1 T <;> by_cases hg : g < count <;>
        simp [cachedValue, tableBit, dealtKey, Hidden, hT, hK, hg, hex, hdec]
    · simp [frandShare, clipOutput, hT]
  · by_cases hji : i = j
    · subst hji
      simp [frandShare, clipOutput]
    · dsimp only [frandShare, clipOutput]
      rw [show (dealtPrssKeys term pair i).pair j = pair (C.pairOf i j hji) by simp [dealtPrssKeys, Ne.symm hji]]
      by_cases hj : j ∈ D.1 <;> by_cases hg : g < count <;>
        simp [cachedValue, tableBit, dealtKey, hidden_pairOf, hji, Ne.symm hji, hj, hg, hiD,
          hi, hdec]

/-- A hidden key name is the name of a hidden term or of a hidden pair. -/
private def hiddenNameSum (D : C.Coalition) :
    {name : KeyName C // Hidden D name} ≃ {T : C.Term // Hidden D (.term T)} ⊕ {p : C.Pair // Hidden D (.pair p)} where
  toFun n := match n with
    | ⟨.parameter, h⟩ => h.elim
    | ⟨.term T, h⟩ => .inl ⟨T, h⟩
    | ⟨.pair p, h⟩ => .inr ⟨p, h⟩
  invFun q := match q with
    | .inl T => ⟨.term T.1, T.2⟩
    | .inr p => ⟨.pair p.1, p.2⟩
  left_inv n := by rcases n with ⟨_ | T | p, h⟩ <;> first | exact h.elim | rfl
  right_inv q := by rcases q with T | p <;> rfl

private theorem elementPos_lt {count : ℕ} (g : Fin count) (e : Fin elementBits) :
    elementBits * g.val + e.val < elementBits * count := by
  have := Nat.mul_le_mul_left elementBits (Nat.succ_le_of_lt g.isLt)
  rw [Nat.mul_succ] at this
  omega

/-- The bits of `count` elements of the check field, `elementBits` bits for each element. -/
private def elementSplit (K : Constants C E) (count : ℕ) : (Fin (elementBits * count) → Bit) ≃ (Fin count → E) :=
  (Equiv.arrowCongr ((finProdFinEquiv (m := count) (n := elementBits)).trans
    (finCongr (Nat.mul_comm count elementBits))).symm (Equiv.refl Bit)).trans
    ((Equiv.curry (Fin count) (Fin elementBits) Bit).trans (Equiv.arrowCongr (Equiv.refl _) K.encode.symm))

omit [Fintype E] [DecidableEq E] in
private theorem elementSplit_apply (K : Constants C E) (count : ℕ) (b : Fin (elementBits * count) → Bit)
    (g : Fin count) : elementSplit K count b g = K.encode.symm fun e => b ⟨elementBits * g.val + e.val, elementPos_lt g e⟩ := by
  simp only [elementSplit, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, id_eq, Equiv.curry_apply]
  congr 1
  funext e
  exact congrArg b (Fin.ext (by simp [finProdFinEquiv]; ring))

end Draws

end ThresholdLeanXmssSecurity

end
