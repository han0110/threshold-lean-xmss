import ThresholdLeanXmssSecurity.Proof.PrssRand.Runs

/-!
# The PRSS streams from dealt keys, the random hidden streams

`prssRand_streamHop` states that the real run with random hidden streams is the ideal run. The
streams under hidden keys at the positions of the calls are the fresh values of `F_rand`, and the
simulator computes the other streams. The step follows the PRSS of CDI05, Section 4.
`streamWorld_randStreams` takes the operators that draw, which are the honest receivers in the real run.
A hidden key reads its address in the hidden cache from `dealtKey` with the value 0 for no key.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation on the hash cache commutes with a computation on the cache of the hidden streams. -/
theorem commutes_onHash_onHidden {α β : Type} (m : StateT (HashCache C) ProbComp α)
    (p : StateT (HiddenCache C) ProbComp β) : Commutes (onHash m) (onHidden p) := by
  intro s
  simp only [onHash, onHidden, StateT.run_bind, StateT.run_mk, StateT.run_pure, bind_map_left]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

section Draws

set_option backward.isDefEq.respectTransparency false

/-! ## One stream -/

/-- `sequenceFin` and `List.mapM` draw in the same order. -/
private theorem ofFn_sequenceFin {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : ℕ} (f : Fin n → m α) :
    List.ofFn <$> OverPermutation.sequenceFin f = (List.finRange n).mapM f := by
  induction n with
  | zero => simp [OverPermutation.sequenceFin, List.finRange]
  | succ n ih =>
    simp only [OverPermutation.sequenceFin, List.finRange_succ, List.mapM_cons, List.mapM_map,
      map_bind, map_pure, List.ofFn_succ]
    rw [← ih]
    simp only [bind_map_left]
    rfl

/-- The stream bits of a key on the free copy are the hidden draws at its positions. -/
private theorem free_prgBits (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) :
    free (liftComp (prgBits name key ρ idx m) (LocalSpec C)) =
      (fun v : Fin m → Bit => fun g => if h : g < m then v ⟨g, h⟩ else 0) <$>
        hiddenDraws (fun g : Fin m => ((name, key), ρ, idx, g.val)) := by
  unfold prgBits hiddenDraws free
  have e : (fun (v : Fin m → Bit) g => if h : g < m then v ⟨g, h⟩ else 0) =
      (fun l g => List.getD l g 0) ∘ List.ofFn := by
    funext v g
    simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split_ifs <;> rfl
  have hl : ∀ l : List ℕ, free (liftComp (l.mapM fun g =>
      (query (spec := RoSpec C) (.inr (name, key, ρ, idx, g)) : OracleComp (RoSpec C) Bit)) (LocalSpec C)) =
      l.mapM fun g => hiddenQuery ((name, key), ρ, idx, g) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free, simulateQ_bind, simulateQ_pure] at ih ⊢
      rw [ih]
      rfl
  rw [e, comp_map, ofFn_sequenceFin, ← List.map_coe_finRange_eq_range]
  simp only [free, liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure] at hl ⊢
  rw [hl, List.mapM_map, map_eq_bind_pure_comp]
  rfl

/-- A sequence of steps that each return a fixed value and keep the state returns the table and keeps
the state. -/
private theorem sequenceFin_run_pure {σ α : Type} : ∀ {n : ℕ} (f : Fin n → StateT σ ProbComp α)
    (vals : Fin n → α) (st : σ), (∀ i, (f i).run st = pure (vals i, st)) →
      (OverPermutation.sequenceFin f).run st = pure (vals, st)
  | 0, f, vals, st, _ => by
    simp only [OverPermutation.sequenceFin, StateT.run_pure]
    congr 2
    funext i
    exact i.elim0
  | n + 1, f, vals, st, h => by
    simp only [OverPermutation.sequenceFin, StateT.run_bind, h 0, pure_bind]
    rw [sequenceFin_run_pure (fun i => f i.succ) (fun i => vals i.succ) st (fun i => h i.succ)]
    simp only [pure_bind, StateT.run_pure]
    congr 2
    exact Fin.cons_self_tail vals

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The positions of one stream that the operators read are fresh. Then the stream is a uniform table,
and the hidden cache keeps it. -/
theorem streamWorld_draw_fresh (prims : Primitives) (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx m : ℕ) (hn : Hidden D name) (s : HashCache C) (c : HiddenCache C)
    (hc : ∀ g : Fin m, c ((name, key), ρ, idx, g.val) = none) :
    (simulateQ (streamWorld prims D) (free (liftComp (prgBits name key ρ idx m) (LocalSpec C)))).run (s, c) =ᵈ
      (fun v : Fin m → Bit => ((fun g => if h : g < m then v ⟨g, h⟩ else 0 : ℕ → Bit),
        (s, cacheFin (fun g : Fin m => ((name, key), ρ, idx, g.val)) v c))) <$> ($ᵗ (Fin m → Bit)) := by
  rw [free_prgBits, simulateQ_map, StateT.run_map]
  refine ((streamWorld_sequenceFin_fresh prims D _ (fun a b h => Fin.ext (congrArg (fun x => x.2.2.2) h))
    (fun _ => hn) s c hc).map _).trans ?_
  simp only [Functor.map_map, EvalDistEq.refl]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The positions of one stream are in the hidden cache. Then a later operator reads them and no
cache changes. -/
theorem streamWorld_draw_replay (prims : Primitives) (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx m : ℕ) (hn : Hidden D name) (s : HashCache C) (c : HiddenCache C) (vals : Fin m → Bit)
    (hc : ∀ g : Fin m, c ((name, key), ρ, idx, g.val) = some (vals g)) :
    (simulateQ (streamWorld prims D) (free (liftComp (prgBits name key ρ idx m) (LocalSpec C)))).run (s, c) =
      pure ((fun g => if h : g < m then vals ⟨g, h⟩ else 0 : ℕ → Bit), (s, c)) := by
  rw [free_prgBits, simulateQ_map, StateT.run_map]
  unfold hiddenDraws
  rw [simulateQ_sequenceFin, sequenceFin_run_pure _ vals _
    (fun g => streamWorld_hidden_cached prims D _ hn s c _ (hc g))]
  simp only [map_pure]

/-! ## Presampling -/

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

/-- The stream index of a call. -/
def _root_.ThresholdLeanXmss.RandCall.idx : RandCall → ℕ
  | .elements idx _ => idx
  | .bits idx _ => idx

/-- The positions of the streams under the hidden keys that the calls read. -/
abbrev HiddenPos (D : C.Coalition) (calls : List RandCall) :=
  Σ k : Fin calls.length, {name : KeyName C // Hidden D name} × Fin (calls.get k).streamBits

/-- The address in the hidden cache of a position of `HiddenPos`, with the round label `label + k`
of call `k`. -/
def hiddenAddr (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (p : HiddenPos D calls) : (KeyName C × HashOutput) × ℕ × ℕ × ℕ :=
  ((p.2.1.1, (dealtKey term pair p.2.1.1).getD 0), label + p.1.val, (calls.get p.1).idx, p.2.2.val)

/-- The stream bits of a key. A hidden key reads its bits from the cache `c`, and another key
queries `PRG`. -/
def cachedBits (D : C.Coalition) (c : HiddenCache C) (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) :
    OracleComp (RoSpec C) (ℕ → Bit) :=
  if Hidden D name then pure fun g => if g < m then (c ((name, key), ρ, idx, g)).getD 0 else 0
  else prgBits name key ρ idx m

/-- From the hidden cache `c`, the run of `oa` in `streamWorld` is the run of `ob` on the hash cache,
and the hidden cache does not change. -/
private def Replays (prims : Primitives) (D : C.Coalition) (c : HiddenCache C) {β : Type}
    (oa ob : OracleComp (LocalSpec C) β) : Prop :=
  ∀ s, (simulateQ (streamWorld prims D) (free oa)).run (s, c) =
    (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) ob).run s

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Replays.pure (prims : Primitives) (D : C.Coalition) (c : HiddenCache C) {β : Type} (b : β) :
    Replays prims D c (pure b) (pure b) := by
  intro s
  simp [free]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Replays.bind {prims : Primitives} {D : C.Coalition} {c : HiddenCache C} {β γ : Type}
    {oa ob : OracleComp (LocalSpec C) β} {f g : β → OracleComp (LocalSpec C) γ}
    (h : Replays prims D c oa ob) (hf : ∀ b, Replays prims D c (f b) (g b)) :
    Replays prims D c (oa >>= f) (ob >>= g) := by
  intro s
  simp only [Replays, free] at h hf ⊢
  simp only [simulateQ_bind, StateT.run_bind]
  rw [h s, bind_map_left, map_bind]
  exact bind_congr fun r => hf r.1 r.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Replays.map {prims : Primitives} {D : C.Coalition} {c : HiddenCache C} {β γ : Type}
    {oa ob : OracleComp (LocalSpec C) β} (h : Replays prims D c oa ob) (f : β → γ) :
    Replays prims D c (f <$> oa) (f <$> ob) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind fun b => Replays.pure prims D c (f b)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Replays.mapM {prims : Primitives} {D : C.Coalition} {c : HiddenCache C} {γ β : Type}
    (l : List γ) {f g : γ → OracleComp (RoSpec C) β}
    (h : ∀ x ∈ l, Replays prims D c (liftComp (f x) (LocalSpec C)) (liftComp (g x) (LocalSpec C))) :
    Replays prims D c (liftComp (l.mapM f) (LocalSpec C)) (liftComp (l.mapM g) (LocalSpec C)) := by
  induction l with
  | nil => simpa using Replays.pure prims D c ([] : List β)
  | cons a l ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure]
    exact (h a List.mem_cons_self).bind fun b =>
      (ih fun x hx => h x (List.mem_cons_of_mem a hx)).bind fun bs => Replays.pure prims D c _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Replays.sequenceFin {prims : Primitives} {D : C.Coalition} {c : HiddenCache C} {β : Type} :
    ∀ {n : ℕ} {f g : Fin n → OracleComp (LocalSpec C) β}, (∀ i, Replays prims D c (f i) (g i)) →
      Replays prims D c (OverPermutation.sequenceFin f) (OverPermutation.sequenceFin g)
  | 0, _, _, _ => Replays.pure prims D c _
  | n + 1, f, g, h => by
    simp only [OverPermutation.sequenceFin]
    exact (h 0).bind fun b => (Replays.sequenceFin (fun i => h i.succ)).bind fun bs => Replays.pure prims D c _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A stream under a key that the coalition knows runs on the hash cache. -/
private theorem replays_prgBits_known (prims : Primitives) (D : C.Coalition) (c : HiddenCache C)
    (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) (hn : ¬ Hidden D name) :
    Replays prims D c (liftComp (prgBits name key ρ idx m) (LocalSpec C))
      (liftComp (prgBits name key ρ idx m) (LocalSpec C)) := by
  unfold prgBits
  simp only [liftComp_bind, liftComp_pure]
  refine (Replays.mapM _ fun g _ => ?_).bind fun bits => Replays.pure prims D c _
  intro s
  simp only [free, liftComp]
  erw [simulateQ_spec_query, simulateQ_spec_query]
  change (streamWorld prims D (.inr (.inr (.inr (name, key, ρ, idx, g))))).run (s, c) =
    (fun r => (r.1, (r.2, c))) <$> (localAnswer prims (.inr (.inr (name, key, ρ, idx, g)))).run s
  simp only [streamWorld, hn, ↓reduceIte, onHash, StateT.run_mk]
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The stream bits of a key with every hidden position in the cache are the cached bits. -/
private theorem replays_cachedBits (prims : Primitives) (D : C.Coalition) (c : HiddenCache C)
    (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ)
    (hc : Hidden D name → ∀ g < m, ∃ b, c ((name, key), ρ, idx, g) = some b) :
    Replays prims D c (liftComp (prgBits name key ρ idx m) (LocalSpec C))
      (liftComp (cachedBits D c name key ρ idx m) (LocalSpec C)) := by
  by_cases hn : Hidden D name
  · intro s
    rw [streamWorld_draw_replay prims D name key ρ idx m hn s c (fun g => (c ((name, key), ρ, idx, g.val)).getD 0)
      (fun g => by obtain ⟨b, hb⟩ := hc hn g.val g.isLt; simp [hb])]
    simp only [cachedBits, hn, ↓reduceIte, liftComp_pure, simulateQ_pure, StateT.run_pure, map_pure]
    congr 2
  · simp only [cachedBits, hn, ↓reduceIte]
    exact replays_prgBits_known prims D c name key ρ idx m hn

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem replays_prssStreams {prims : Primitives} {D : C.Coalition} {c : HiddenCache C} {R : Type} [Zero R]
    {stream stream' : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R)} (prss : PrssKeys C) (i : C.Party)
    (hterm : ∀ T, i ∈ C.holders T → Replays prims D c (liftComp (stream (.term T) (prss.term T)) (LocalSpec C))
      (liftComp (stream' (.term T) (prss.term T)) (LocalSpec C)))
    (hpair : ∀ j (h : j ≠ i), Replays prims D c
      (liftComp (stream (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)) (LocalSpec C))
      (liftComp (stream' (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)) (LocalSpec C))) :
    Replays prims D c (liftComp (prssStreams stream prss i) (LocalSpec C))
      (liftComp (prssStreams stream' prss i) (LocalSpec C)) := by
  unfold prssStreams
  simp only [liftComp_bind, liftComp_pure]
  refine (Replays.mapM _ fun T _ => ?_).bind fun r => (Replays.mapM _ fun j _ => ?_).bind fun Z =>
    Replays.pure prims D c _
  · split_ifs with h
    · exact hterm T h
    · simpa using Replays.pure prims D c (fun _ => 0 : ℕ → R)
  · split_ifs with h
    · simpa using Replays.pure prims D c (fun _ => 0 : ℕ → R)
    · exact hpair j h

/-- Every hidden position that the calls `cs` read from round label `ρ` is in the cache `c`. -/
private def CachedCalls (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (c : HiddenCache C) (ρ : ℕ) (cs : List RandCall) : Prop :=
  ∀ (k : Fin cs.length) (name : KeyName C), Hidden D name → ∀ g < (cs.get k).streamBits,
    ∃ b, c ((name, (dealtKey term pair name).getD 0), ρ + k.val, (cs.get k).idx, g) = some b

omit [Fintype E] [DecidableEq E] in
private theorem replays_randStreams (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (c : HiddenCache C) (i : C.Party) :
    ∀ (ρ : ℕ) (cs : List RandCall), CachedCalls D term pair c ρ cs →
      Replays prims D c (liftComp (randStreams K prgBits (dealtPrssKeys term pair i) i ρ cs) (LocalSpec C))
        (liftComp (randStreams K (cachedBits D c) (dealtPrssKeys term pair i) i ρ cs) (LocalSpec C))
  | ρ, [], _ => by simpa [randStreams] using Replays.pure prims D c ([] : List (RandOutput C E))
  | ρ, call :: rest, hc => by
    have hbits : ∀ name, Replays prims D c
        (liftComp (prgBits name ((dealtKey term pair name).getD 0) ρ call.idx call.streamBits) (LocalSpec C))
        (liftComp (cachedBits D c name ((dealtKey term pair name).getD 0) ρ call.idx call.streamBits) (LocalSpec C)) :=
      fun name => replays_cachedBits prims D c name _ ρ _ _ fun hn g hg => by
        simpa using hc ⟨0, by simp⟩ name hn g hg
    have hcall : Replays prims D c (liftComp (callStreams K prgBits (dealtPrssKeys term pair i) i ρ call) (LocalSpec C))
        (liftComp (callStreams K (cachedBits D c) (dealtPrssKeys term pair i) i ρ call) (LocalSpec C)) := by
      cases call with
      | elements idx count =>
        simp only [callStreams, liftComp_map]
        refine (replays_prssStreams _ i (fun T hT => ?_) (fun j h => ?_)).map _
        · simp only [dealtPrssKeys, hT, ↓reduceIte, liftComp_map]
          exact (hbits (.term T)).map _
        · simp only [dealtPrssKeys, h, ↓reduceDIte, liftComp_map]
          exact (hbits (.pair (C.pairOf i j (Ne.symm h)))).map _
      | bits idx count =>
        simp only [callStreams, liftComp_map]
        refine (replays_prssStreams _ i (fun T hT => ?_) (fun j h => ?_)).map _
        · simp only [dealtPrssKeys, hT, ↓reduceIte]
          exact hbits (.term T)
        · simp only [dealtPrssKeys, h, ↓reduceDIte]
          exact hbits (.pair (C.pairOf i j (Ne.symm h)))
    simp only [randStreams, liftComp_bind, liftComp_pure]
    refine hcall.bind fun o => (replays_randStreams prims K D term pair c i (ρ + 1) rest fun k name hn g hg => ?_).bind
      fun os => Replays.pure prims D c _
    have e : ρ + 1 + k.val = ρ + (k.val + 1) := by omega
    rw [e]
    simpa using hc k.succ name hn g hg

omit [Fintype E] [DecidableEq E] in
/-- The streams of the calls under the hidden keys are fresh uniform bits. The operators of `drawers`
read them from a presampled table, and the other streams stay on the hash cache. The run of all
honest operators is the case `drawers = Finset.univ.filter (· ∉ D.1)`. -/
theorem streamWorld_randStreams (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (drawers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (s : HashCache C) (c : HiddenCache C) (hc : ∀ x, label ≤ x.2.1 → c x = none) :
    (fun r => (r.1, r.2.1)) <$>
        (simulateQ (streamWorld prims D) (free (honestStreams K prgBits drawers term pair label calls))).run (s, c) =ᵈ
      (($ᵗ (Fin (Fintype.card (HiddenPos D calls)) → Bit)) >>= fun vals =>
        (simulateQ (localAnswer prims) (honestStreams K (cachedBits D (cacheFin
          (hiddenAddr D term pair label calls ∘ (Fintype.equivFin (HiddenPos D calls)).symm) vals c))
          drawers term pair label calls)).run s) := by
  set e := Fintype.equivFin (HiddenPos D calls)
  set addr := hiddenAddr D term pair label calls ∘ e.symm
  have hinj : Function.Injective (hiddenAddr D term pair label calls) := by
    rintro ⟨k, ⟨n, hn⟩, g⟩ ⟨k', ⟨n', hn'⟩, g'⟩ h
    simp only [hiddenAddr, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, hk, -, hg⟩ := h
    obtain rfl : k = k' := Fin.ext (by omega)
    obtain rfl : g = g' := Fin.ext hg
    rfl
  have ha : Function.Injective addr := hinj.comp e.symm.injective
  refine (streamWorld_presample prims D _ addr ha s c fun i => hc _ (by simp [addr, hiddenAddr])).trans
    (EvalDistEq.bind_right _ fun vals => ?_)
  have hcached : CachedCalls D term pair (cacheFin addr vals c) label calls := by
    intro k name hn g hg
    refine ⟨vals (e ⟨k, ⟨name, hn⟩, ⟨g, hg⟩⟩), ?_⟩
    have h := cacheFin_at addr ha vals c (e ⟨k, ⟨name, hn⟩, ⟨g, hg⟩⟩)
    have e2 : addr (e ⟨k, ⟨name, hn⟩, ⟨g, hg⟩⟩) = hiddenAddr D term pair label calls ⟨k, ⟨name, hn⟩, ⟨g, hg⟩⟩ := by
      simp only [addr, Function.comp_apply, Equiv.symm_apply_apply]
    rw [e2] at h
    exact h
  have hr : Replays prims D (cacheFin addr vals c) (honestStreams K prgBits drawers term pair label calls)
      (honestStreams K (cachedBits D (cacheFin addr vals c)) drawers term pair label calls) := by
    refine Replays.sequenceFin fun j => ?_
    split_ifs
    · exact (replays_randStreams prims K D term pair _ j label calls hcached).map some
    · exact Replays.pure prims D _ none
  rw [hr s, Functor.map_map]
  simp only [Prod.mk.eta, id_map']
  exact .rfl

/-! ## The world of the streams on the hash cache -/

/-- A run with a count is the run without the count. -/
private theorem run_withAddCost {κ : Type} {spec : OracleSpec κ} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (costFn : spec.Domain → ℕ) (oa : OracleComp spec α) (s : σ) :
    (fun r => (r.1.1, r.2)) <$> (simulateQ (impl.withAddCost costFn) oa).run.run s = (simulateQ impl oa).run s := by
  rw [QueryImpl.withAddCost, ← QueryImpl.fst_map_run_withCost impl (fun t => Multiplicative.ofAdd (costFn t)) oa]
  simp only [StateT.run_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `worldAnswer` is `world` without the query count. -/
private theorem worldAnswer_run (prims : Primitives) {α : Type} (oa : OracleComp (WorldSpec C) α) (s : HashCache C) :
    (simulateQ (worldAnswer prims) oa).run s = (fun r => (r.1.1, r.2)) <$> (simulateQ (world prims) oa).run.run s :=
  (run_withAddCost (worldAnswer prims) _ oa s).symm

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A sample on the free copy keeps the hash cache. -/
private theorem worldAnswer_free_liftComp (prims : Primitives) {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (free (liftComp p (LocalSpec C)))).run s = (fun a => (a, s)) <$> p := by
  rw [worldAnswer_run, world_free_liftComp, Functor.map_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A sample on the counted copy keeps the hash cache. -/
private theorem worldAnswer_counted_liftComp (prims : Primitives) {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (counted (liftComp (liftComp p (LocalSpec C)) (SimulatorSpec C)))).run s =
      (fun a => (a, s)) <$> p := by
  rw [worldAnswer_run, world_counted_liftComp, Functor.map_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation on the hash cache keeps the hidden cache. -/
private theorem simulateQ_onHash {κ : Type} {spec : OracleSpec κ} (I : QueryImpl spec (StateT (HashCache C) ProbComp))
    {α : Type} (oa : OracleComp spec α) (s : HashCache C) (c : HiddenCache C) :
    (simulateQ (fun t => onHash (I t)) oa).run (s, c) = (fun r => (r.1, (r.2, c))) <$> (simulateQ I oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    rw [show (onHash (I t)).run (s, c) = (fun r => (r.1, (r.2, c))) <$> (I t).run s from rfl, bind_map_left,
      map_bind]
    exact bind_congr fun r => ih r.1 r.2

/-- The counted copy of `streamWorld`. -/
private def streamCounted (prims : Primitives) :
    QueryImpl (SimulatorSpec C) (StateT (HashCache C × HiddenCache C) ProbComp) :=
  fun t => onHash ((localAnswer (C := C) prims + programAnswer (C := C) : QueryImpl (SimulatorSpec C) (StateT (HashCache C) ProbComp)) t)

/-- The free copy of `streamWorld`. -/
private def streamFree (prims : Primitives) (D : C.Coalition) :
    QueryImpl (LocalSpec C) (StateT (HashCache C × HiddenCache C) ProbComp) :=
  fun t => streamWorld prims D (.inr t)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem streamWorld_eq_add (prims : Primitives) (D : C.Coalition) :
    streamWorld prims D = streamCounted (C := C) prims + streamFree prims D := by
  funext t
  rcases t with t | t <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The counted copy runs on the hash cache and keeps the hidden cache. -/
private theorem streamWorld_counted (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (SimulatorSpec C) α) (sc : HashCache C × HiddenCache C) :
    (simulateQ (streamWorld prims D) (counted oa)).run sc =
      (fun r => (r.1, (r.2, sc.2))) <$> (simulateQ (worldAnswer prims) (counted oa)).run sc.1 := by
  obtain ⟨s, c⟩ := sc
  rw [streamWorld_eq_add, simulateQ_counted]
  refine (simulateQ_onHash (localAnswer (C := C) prims + programAnswer (C := C)) oa s c).trans ?_
  rw [worldAnswer, simulateQ_counted]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A sample on the free copy keeps both caches. -/
private theorem streamWorld_free_liftComp (prims : Primitives) (D : C.Coalition) {α : Type} (p : ProbComp α)
    (sc : HashCache C × HiddenCache C) :
    (simulateQ (streamWorld prims D) (free (liftComp p (LocalSpec C)))).run sc = (fun a => (a, sc)) <$> p := by
  obtain ⟨s, c⟩ := sc
  have hq : ∀ t : unifSpec.Domain, (simulateQ (streamWorld prims D)
      (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _)).run (s, c) =
      (fun a => (a, (s, c))) <$> (liftM (unifSpec.query t) : ProbComp _) := fun t => by
    rw [simulateQ_query]
    simp [streamWorld, onHash, localAnswer, unifFwdImpl]
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [liftComp_bind, free_bind, simulateQ_bind, free_liftComp_query, StateT.run_bind]
    erw [hq]
    simp only [bind_map_left]
    rw [map_bind]
    exact bind_congr fun a => ih a

/-! ## The calls with tables from the hidden cache -/

/-- The bit at position `g` of the stream of `name` at round `ρ` and index `idx`, read from the hidden
cache `c` under the dealt key. -/
def tableBit (c : HiddenCache C) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (name : KeyName C)
    (ρ idx g : ℕ) : Bit :=
  (c ((name, (dealtKey term pair name).getD 0), ρ, idx, g)).getD 0

/-- One call of `F_rand` with the known streams on the hash cache and the fresh values read from the
hidden cache `c`. -/
def tableCall (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (c : HiddenCache C) (ρ : ℕ) :
    RandCall → OracleComp (LocalSpec C) (C.Party → Option (RandOutput C E))
  | .elements idx count => do
      let known ← liftComp (knownStreams D receivers (elementCodec K) term pair ρ idx count) (LocalSpec C)
      let decode := fun (name : KeyName C) (g : Fin count) =>
        K.encode.symm fun e => tableBit c term pair name ρ idx (elementBits * g.val + e.val)
      pure fun i => (frandOut D count known.1 known.2 (fun T => decode (.term T)) (fun p => decode (.pair p)) i).map
        Sum.inl
  | .bits idx count => do
      let known ← liftComp (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C)
      let read := fun (name : KeyName C) (g : Fin count) => tableBit c term pair name ρ idx g.val
      pure fun i => (frandOut D count known.1 known.2 (fun T => read (.term T)) (fun p => read (.pair p)) i).map
        Sum.inr

/-- The calls of `F_rand` from round label `ρ`, as `tableCall`. -/
def tableCalls (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (c : HiddenCache C) :
    ℕ → List RandCall → OracleComp (LocalSpec C) (List (C.Party → Option (RandOutput C E)))
  | _, [] => pure []
  | ρ, call :: calls => do
      let output ← tableCall K D receivers term pair c ρ call
      let outputs ← tableCalls K D receivers term pair c (ρ + 1) calls
      pure (output :: outputs)

/-! ## The hash half -/

/-- The query of `H` at the input that derives the PRG key of a stream key. -/
def streamKeyQuery (key : HashOutput) : OracleComp (LocalSpec C) HashOutput :=
  liftM ((LocalSpec C).query (.inr (.inl (.streamKey key))))

/-- The computation `oa` queries `H` at the stream key `key` in every run. Then the query can be made
first. -/
def Touches (prims : Primitives) (key : HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) : Prop :=
  SameRun prims oa (streamKeyQuery key >>= fun _ => oa)

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
private theorem Touches.map {prims : Primitives} {key : HashOutput} {α β : Type} {oa : OracleComp (LocalSpec C) α}
    (h : Touches prims key oa) (f : α → β) : Touches prims key (f <$> oa) := by
  unfold Touches at h ⊢
  exact (h.map f).trans (by rw [map_bind]; exact SameRun.refl prims _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The queries of `H` at keys that `oa` queries in every run can be made first. -/
private theorem sameRun_prepend (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ keys : List HashOutput, (∀ key ∈ keys, Touches prims key oa) →
      SameRun prims oa (keys.mapM streamKeyQuery >>= fun _ => oa)
  | [], _ => by simpa using SameRun.refl prims oa
  | key :: keys, h => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    exact (h key List.mem_cons_self).trans (SameRun.bind_right _ fun _ =>
      sameRun_prepend prims oa keys fun k hk => h k (List.mem_cons_of_mem key hk))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem simulateQ_streamKeyQuery (prims : Primitives) (key : HashOutput) :
    simulateQ (localAnswer prims) (streamKeyQuery (C := C) key) = hashAnswer prims (.streamKey key) := by
  simp [streamKeyQuery, localAnswer]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Touches.bind_left {prims : Primitives} {key : HashOutput} {α β : Type}
    {oa : OracleComp (LocalSpec C) α} (h : Touches prims key oa) (f : α → OracleComp (LocalSpec C) β) :
    Touches prims key (oa >>= f) :=
  (h.bind fun a => SameRun.refl prims (f a)).trans (SameRun.of_eq (bind_assoc _ _ _))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Touches.bind_right {prims : Primitives} {key : HashOutput} {α β : Type}
    (oa : OracleComp (LocalSpec C) α) {f : α → OracleComp (LocalSpec C) β} (h : ∀ a, Touches prims key (f a)) :
    Touches prims key (oa >>= f) :=
  (SameRun.bind_right oa h).trans (sameRun_swap prims oa (streamKeyQuery key) fun a _ => f a)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Touches.mapM {prims : Primitives} {key : HashOutput} {γ β : Type} {f : γ → OracleComp (RoSpec C) β} :
    ∀ l : List γ, (∃ x ∈ l, Touches prims key (liftComp (f x) (LocalSpec C))) →
      Touches prims key (liftComp (l.mapM f) (LocalSpec C))
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, ⟨x, hx, h⟩ => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.bind_left _
    · exact Touches.bind_right _ fun _ => (Touches.mapM l ⟨x, hx, h⟩).bind_left _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem Touches.sequenceFin {prims : Primitives} {key : HashOutput} {β : Type} :
    ∀ {n : ℕ} {f : Fin n → OracleComp (LocalSpec C) β} (i : Fin n), Touches prims key (f i) →
      Touches prims key (OverPermutation.sequenceFin f)
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    simp only [OverPermutation.sequenceFin]
    cases i using Fin.cases with
    | zero => exact h.bind_left _
    | succ i => exact Touches.bind_right _ fun _ => (Touches.sequenceFin (f := fun i => f i.succ) i h).bind_left _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A stream with at least one position queries `H` at its key. -/
private theorem touches_prgBits (prims : Primitives) (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ)
    (hm : 0 < m) : Touches prims key (liftComp (prgBits name key ρ idx m) (LocalSpec C)) := by
  unfold prgBits
  simp only [liftComp_bind]
  refine (Touches.mapM _ ⟨0, List.mem_range.mpr hm, ?_⟩).bind_left _
  intro s
  have hp : simulateQ (localAnswer prims) (liftComp (query (spec := RoSpec C) (.inr (name, key, ρ, idx, 0)) :
      OracleComp (RoSpec C) Bit) (LocalSpec C)) = prgAnswer prims (name, key, ρ, idx, 0) := by
    rw [simulateQ_localAnswer_liftComp]
    exact (simulateQ_query _ _).trans (id_map _)
  simp only [simulateQ_bind, hp, simulateQ_streamKeyQuery, prgAnswer]
  rw [hashAnswer_dup prims _ fun _ b => pure (prims.aes.eval (truncateHash b) (ρ, idx, 0))]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem hidden_pairOf (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    Hidden D (.pair (C.pairOf i j h)) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  simp only [Hidden, Committee.pairOf]
  split_ifs <;> simp [and_comm]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem touches_cachedBits (prims : Primitives) (D : C.Coalition) (c : HiddenCache C) (name : KeyName C)
    (key : HashOutput) (ρ idx m : ℕ) (hn : ¬ Hidden D name) (hm : 0 < m) :
    Touches prims key (liftComp (cachedBits D c name key ρ idx m) (LocalSpec C)) := by
  simp only [cachedBits, hn, ↓reduceIte]
  exact touches_prgBits prims name key ρ idx m hm

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem touches_prssStreams_term {prims : Primitives} {key : HashOutput} {R : Type} [Zero R]
    (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R)) (prss : PrssKeys C) (i : C.Party)
    (T : C.Term) (hT : i ∈ C.holders T) (h : Touches prims key (liftComp (stream (.term T) (prss.term T)) (LocalSpec C))) :
    Touches prims key (liftComp (prssStreams stream prss i) (LocalSpec C)) := by
  unfold prssStreams
  simp only [liftComp_bind]
  exact (Touches.mapM _ ⟨T, by simp [Committee.terms], by simp only [hT, ↓reduceIte]; exact h⟩).bind_left _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem touches_prssStreams_pair {prims : Primitives} {key : HashOutput} {R : Type} [Zero R]
    (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R)) (prss : PrssKeys C) (i j : C.Party)
    (hj : j ≠ i) (h : Touches prims key (liftComp (stream (.pair (C.pairOf i j hj.symm)) (prss.pair j)) (LocalSpec C))) :
    Touches prims key (liftComp (prssStreams stream prss i) (LocalSpec C)) := by
  unfold prssStreams
  simp only [liftComp_bind]
  exact Touches.bind_right _ fun _ =>
    (Touches.mapM _ ⟨j, by simp [Committee.parties], by simp only [hj, ↓reduceDIte]; exact h⟩).bind_left _

omit [Fintype E] [DecidableEq E] in
private theorem touches_callStreams {prims : Primitives} {key : HashOutput} (K : Constants C E)
    (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit)) (prss : PrssKeys C)
    (i : C.Party) (ρ : ℕ) (call : RandCall) (hpos : 0 < call.streamBits) (name : KeyName C) (k : HashOutput)
    (hb : ∀ ρ idx m, 0 < m → Touches prims key (liftComp (bits name k ρ idx m) (LocalSpec C)))
    (hp : ∀ {R : Type} [Zero R] (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R)),
      Touches prims key (liftComp (stream name k) (LocalSpec C)) →
        Touches prims key (liftComp (prssStreams stream prss i) (LocalSpec C))) :
    Touches prims key (liftComp (callStreams K bits prss i ρ call) (LocalSpec C)) := by
  cases call with
  | elements idx count =>
    simp only [callStreams, liftComp_map]
    exact (hp _ (by simp only [liftComp_map]; exact (hb ρ idx _ hpos).map _)).map _
  | bits idx count =>
    simp only [callStreams, liftComp_map]
    exact (hp _ (hb ρ idx _ hpos)).map _

omit [Fintype E] [DecidableEq E] in
private theorem touches_randStreams {prims : Primitives} {key : HashOutput} (K : Constants C E)
    (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit)) (prss : PrssKeys C) (i : C.Party)
    (h : ∀ ρ call, 0 < call.streamBits → Touches prims key (liftComp (callStreams K bits prss i ρ call) (LocalSpec C))) :
    ∀ ρ cs, (∃ call ∈ cs, 0 < call.streamBits) →
      Touches prims key (liftComp (randStreams K bits prss i ρ cs) (LocalSpec C))
  | _, [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | ρ, call :: rest, ⟨x, hx, hpos⟩ => by
    simp only [randStreams, liftComp_bind, liftComp_pure]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (h ρ x hpos).bind_left _
    · exact Touches.bind_right _ fun _ => (touches_randStreams K bits prss i h (ρ + 1) rest ⟨x, hx, hpos⟩).bind_left _

omit [Fintype E] [DecidableEq E] in
/-- The honest receivers query `H` at each known key. -/
private theorem touches_honestStreams (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (c : HiddenCache C) :
    ∀ key ∈ knownKeys D receivers term pair calls,
      Touches prims key (honestStreams K (cachedBits D c) (honestReceivers D receivers) term pair label calls) := by
  intro key hk
  unfold knownKeys at hk
  split_ifs at hk with hany
  · obtain ⟨call, hcall, hpos⟩ : ∃ call ∈ calls, 0 < call.streamBits := by simpa using hany
    have main : ∃ i, i ∉ D.1 ∧ i ∈ receivers ∧ Touches prims key
        (liftComp (randStreams K (cachedBits D c) (dealtPrssKeys term pair i) i label calls) (LocalSpec C)) := by
      rcases List.mem_append.mp hk with hk | hk
      · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hk
        obtain ⟨T, ⟨-, hT, i, hi, hiD, hiT⟩, rfl⟩ := hk
        refine ⟨i, hiD, hi, touches_randStreams K _ _ i (fun ρ call hpos => touches_callStreams K _ _ i ρ call hpos
          (.term T) (term T) (fun ρ idx m hm => touches_cachedBits prims D c _ _ ρ idx m (by simpa [Hidden] using hT) hm)
          fun stream h => touches_prssStreams_term stream _ i T hiT (by simpa [dealtPrssKeys, hiT] using h))
          label calls ⟨call, hcall, hpos⟩⟩
      · simp only [List.mem_flatMap, List.mem_filterMap, Option.dite_none_right_eq_some, Option.some.injEq] at hk
        obtain ⟨j, -, i, -, ⟨hj, hiD, hi⟩, rfl⟩ := hk
        have hji : j ≠ i := fun e => hiD (e ▸ hj)
        refine ⟨i, hiD, hi, touches_randStreams K _ _ i (fun ρ call hpos => touches_callStreams K _ _ i ρ call hpos
          (.pair (C.pairOf i j hji.symm)) _ (fun ρ idx m hm => touches_cachedBits prims D c _ _ ρ idx m
            ((hidden_pairOf D i j _).not.mpr fun h => h.2 hj) hm)
          fun stream h => touches_prssStreams_pair stream _ i j hji (by simpa [dealtPrssKeys, hji] using h))
          label calls ⟨call, hcall, hpos⟩⟩
    obtain ⟨i, hiD, hi, ht⟩ := main
    unfold honestStreams
    refine Touches.sequenceFin i ?_
    simp only [honestReceivers, Finset.mem_filter, hi, hiD, not_false_eq_true, and_self, ↓reduceIte]
    exact ht.map some
  · simp at hk

omit [Fintype E] [DecidableEq E] in
/-- The simulator queries `H` at each known key. -/
private theorem touches_tableCalls (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (c : HiddenCache C) :
    ∀ key ∈ knownKeys D receivers term pair calls,
      Touches prims key (tableCalls K D receivers term pair c label calls) := by
  intro key hk
  unfold knownKeys at hk
  split_ifs at hk with hany
  · obtain ⟨call, hmem, hpos⟩ : ∃ call ∈ calls, 0 < call.streamBits := by simpa using hany
    have hknown : ∀ {R : Type} [Zero R] (codec : Codec C E R) (ρ idx count : ℕ),
        (∀ name k, Touches prims k (liftComp (codec.draw name k ρ idx count) (LocalSpec C))) →
        Touches prims key (liftComp (knownStreams D receivers codec term pair ρ idx count) (LocalSpec C)) := by
      intro R _ codec ρ idx count hdraw
      unfold knownStreams
      simp only [liftComp_bind]
      rcases List.mem_append.mp hk with hk | hk
      · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hk
        obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hk
        exact (Touches.mapM _ ⟨T, by simp [Committee.terms], by simp only [hT]; exact hdraw _ _⟩).bind_left _
      · simp only [List.mem_flatMap, List.mem_filterMap, Option.dite_none_right_eq_some, Option.some.injEq] at hk
        obtain ⟨j, -, i, -, h, rfl⟩ := hk
        exact Touches.bind_right _ fun _ => (Touches.mapM _ ⟨j, by simp [Committee.parties], Touches.mapM _
          ⟨i, by simp [Committee.parties], by simp only [h]; exact hdraw _ _⟩⟩).bind_left _
    have hstep : ∀ ρ call, 0 < call.streamBits → Touches prims key (tableCall K D receivers term pair c ρ call) := by
      intro ρ call hpos
      cases call with
      | elements idx count =>
        simp only [tableCall]
        refine (hknown _ ρ idx count fun name k => ?_).bind_left _
        simp only [elementCodec, liftComp_bind]
        exact (touches_prgBits prims name k ρ idx _ hpos).bind_left _
      | bits idx count =>
        simp only [tableCall]
        exact (hknown _ ρ idx count fun name k => touches_prgBits prims name k ρ idx _ hpos).bind_left _
    clear hknown hk hany
    induction calls generalizing label with
    | nil => simp at hmem
    | cons x rest ih =>
      simp only [tableCalls]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact (hstep label call hpos).bind_left _
      · exact Touches.bind_right _ fun _ => (ih label.succ hmem).bind_left _
  · simp at hk

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- After the queries of `H` at the keys, each key is in the hash cache. -/
private theorem streamKeys_cached (prims : Primitives) (keys : List HashOutput) (s : HashCache C) :
    ∀ r ∈ support ((simulateQ (localAnswer prims) (keys.mapM streamKeyQuery)).run s),
      ∀ key ∈ keys, (r.2 (.streamKey key)).isSome := by
  induction keys generalizing s with
  | nil => simp
  | cons k ks ih =>
    intro r hr key hk
    have hq : simulateQ (localAnswer prims) (streamKeyQuery (C := C) k) = hashAnswer prims (.streamKey k) := by
      simp [streamKeyQuery, localAnswer]
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, hq, StateT.run_bind, support_bind,
      Set.mem_iUnion] at hr
    obtain ⟨p, hp, q, hq', hr⟩ := hr
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rcases List.mem_cons.mp hk with rfl | hk
    · have h1 := hashAnswer_cached prims (q := .streamKey key) (by rintro ⟨_, h, _⟩; cases h) s p hp
      have h2 := Grows.simulateQ (grows_localAnswer prims) _ p.2 q hq' h1
      simp [h2]
    · exact ih p.2 q hq' key hk

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem RunsPure.sequenceFin {prims : Primitives} {s : HashCache C} {β : Type} :
    ∀ {n : ℕ} {f : Fin n → OracleComp (LocalSpec C) β} {g : Fin n → β}, (∀ i, RunsPure prims s (f i) (g i)) →
      RunsPure prims s (OverPermutation.sequenceFin f) g
  | 0, _, g, _ => by
    simp only [OverPermutation.sequenceFin]
    rw [show g = Fin.elim0 from funext fun i => i.elim0]
    exact RunsPure.pure prims s _
  | n + 1, f, g, h => by
    simp only [OverPermutation.sequenceFin]
    refine (h 0).bind ((RunsPure.sequenceFin (g := fun i => g i.succ) fun i => h i.succ).bind ?_)
    rw [show (Fin.cases (g 0) fun i => g i.succ : Fin (n + 1) → β) = g from
      funext fun i => by cases i using Fin.cases <;> rfl]
    exact RunsPure.pure prims s _

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
private theorem runsPure_prssStreams {prims : Primitives} {s : HashCache C} {R : Type} [Zero R]
    (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R)) (val : KeyName C → HashOutput → ℕ → R)
    (prss : PrssKeys C) (i : C.Party)
    (hterm : ∀ T, i ∈ C.holders T →
      RunsPure prims s (liftComp (stream (.term T) (prss.term T)) (LocalSpec C)) (val (.term T) (prss.term T)))
    (hpair : ∀ j (h : j ≠ i), RunsPure prims s (liftComp (stream (.pair (C.pairOf i j h.symm)) (prss.pair j)) (LocalSpec C))
      (val (.pair (C.pairOf i j h.symm)) (prss.pair j))) :
    RunsPure prims s (liftComp (prssStreams stream prss i) (LocalSpec C))
      (fun T => if i ∈ C.holders T then val (.term T) (prss.term T) else fun _ => 0,
        fun j => if h : j = i then fun _ => 0 else val (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)) := by
  unfold prssStreams
  simp only [liftComp_bind, liftComp_pure]
  refine (RunsPure.mapM (g := fun T => if i ∈ C.holders T then val (.term T) (prss.term T) else fun _ => 0) _
    fun T _ => ?_).bind ((RunsPure.mapM (g := fun j => if h : j = i then fun _ => 0 else
      val (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)) _ fun j _ => ?_).bind ?_)
  · split_ifs with h
    · exact hterm T h
    · exact RunsPure.pure prims s _
  · split_ifs with h
    · exact RunsPure.pure prims s _
    · exact hpair j h
  · simp only [getD_terms_idxOf, getD_parties]
    exact RunsPure.pure prims s _

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem runsPure_cachedBits (prims : Primitives) (D : C.Coalition) (c : HiddenCache C) (s : HashCache C)
    (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) (hs : ¬ Hidden D name → 0 < m → (s (.streamKey key)).isSome) :
    RunsPure prims s (liftComp (cachedBits D c name key ρ idx m) (LocalSpec C)) (cachedValue prims D c s name key ρ idx m) := by
  by_cases hn : Hidden D name
  · simp only [cachedBits, cachedValue, hn, ↓reduceIte, liftComp_pure]
    exact RunsPure.pure prims s _
  · simp only [cachedBits, cachedValue, hn, ↓reduceIte]
    exact runsPure_prgBits prims s name key ρ idx m (hs hn)

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

omit [Fintype E] [DecidableEq E] in
private theorem runsPure_tableCall (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (c : HiddenCache C)
    (s : HashCache C) (ρ : ℕ) (call : RandCall) (hs : 0 < call.streamBits → KeysCached D receivers term pair s) :
    ∃ f, RunsPure prims s (tableCall K D receivers term pair c ρ call) f ∧ ∀ i, i ∉ D.1 → i ∈ receivers →
      ∃ o, f i = some o ∧
        RunsPure prims s (liftComp (callStreams K (cachedBits D c) (dealtPrssKeys term pair i) i ρ call) (LocalSpec C)) o := by
  cases call with
  | elements idx count =>
    have hk := runsPure_knownStreams (prims := prims) (s := s) D receivers (elementCodec K) term pair ρ idx count
      (fun _ key g => K.encode.symm fun b => prgValue prims s key ρ idx (elementBits * count) (elementBits * g + b))
      (fun T hT => by
        simp only [elementCodec, liftComp_bind, liftComp_pure]
        exact (runsPure_prgBits prims s _ _ ρ idx _ fun hm => (hs hm).1 T hT).bind (RunsPure.pure prims s _))
      (fun j i h => by
        simp only [elementCodec, liftComp_bind, liftComp_pure]
        exact (runsPure_prgBits prims s _ _ ρ idx _ fun hm => (hs hm).2 j i h).bind (RunsPure.pure prims s _))
    simp only [tableCall]
    refine ⟨_, hk.bind (RunsPure.pure prims s _), fun i hiD hi => ?_⟩
    simp only [frandOut_eq, hiD, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    have hc := (runsPure_prssStreams (prims := prims) (s := s) (fun name key =>
        (fun b g => K.encode.symm fun e => b (elementBits * g + e)) <$> cachedBits D c name key ρ idx (elementBits * count))
      (fun name key g => K.encode.symm fun e => cachedValue prims D c s name key ρ idx (elementBits * count)
        (elementBits * g + e)) (dealtPrssKeys term pair i) i
      (fun T hT => by
        simp only [liftComp_map]
        refine (runsPure_cachedBits prims D c s _ _ ρ idx _ fun hn hm => ?_).map _
        rw [show (dealtPrssKeys term pair i).term T = term T by simp [dealtPrssKeys, hT]]
        exact (hs hm).1 T ⟨by simpa [Hidden] using hn, i, hi, hiD, hT⟩)
      (fun j h => by
        simp only [liftComp_map]
        refine (runsPure_cachedBits prims D c s _ _ ρ idx _ fun hn hm => ?_).map _
        have hj : j ∈ D.1 := by_contra fun hj => hn ((hidden_pairOf D i j _).mpr ⟨hiD, hj⟩)
        rw [show (dealtPrssKeys term pair i).pair j = pair (C.pairOf i j h.symm) by simp [dealtPrssKeys, h]]
        exact (hs hm).2 j i ⟨hj, hiD, hi⟩)).map
      (fun o => (Sum.inl (clipOutput count o) : RandOutput C E))
    simp only [callStreams, liftComp_map]
    convert hc using 2
    refine frandShare_eq_clipOutput prims D receivers term pair c s ρ idx count (elementBits * count)
      (fun b g => K.encode.symm fun e => b (elementBits * g + e)) (fun F g hg => ?_) i hiD hi
    congr 1
    funext e
    have hpos : elementBits * g + e.val < elementBits * count := by
      have := Nat.mul_le_mul_left elementBits (Nat.succ_le_of_lt hg)
      rw [Nat.mul_succ] at this
      omega
    simp only [hpos, ↓reduceIte]
  | bits idx count =>
    have hk := runsPure_knownStreams (prims := prims) (s := s) D receivers (bitCodec (E := E)) term pair ρ idx count
      (fun _ key => prgValue prims s key ρ idx count)
      (fun T hT => runsPure_prgBits prims s _ _ ρ idx _ fun hm => (hs hm).1 T hT)
      (fun j i h => runsPure_prgBits prims s _ _ ρ idx _ fun hm => (hs hm).2 j i h)
    simp only [tableCall]
    refine ⟨_, hk.bind (RunsPure.pure prims s _), fun i hiD hi => ?_⟩
    simp only [frandOut_eq, hiD, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    have hc := (runsPure_prssStreams (prims := prims) (s := s) (fun name key => cachedBits D c name key ρ idx count)
      (fun name key => cachedValue prims D c s name key ρ idx count) (dealtPrssKeys term pair i) i
      (fun T hT => by
        refine runsPure_cachedBits prims D c s _ _ ρ idx _ fun hn hm => ?_
        rw [show (dealtPrssKeys term pair i).term T = term T by simp [dealtPrssKeys, hT]]
        exact (hs hm).1 T ⟨by simpa [Hidden] using hn, i, hi, hiD, hT⟩)
      (fun j h => by
        refine runsPure_cachedBits prims D c s _ _ ρ idx _ fun hn hm => ?_
        have hj : j ∈ D.1 := by_contra fun hj => hn ((hidden_pairOf D i j _).mpr ⟨hiD, hj⟩)
        rw [show (dealtPrssKeys term pair i).pair j = pair (C.pairOf i j h.symm) by simp [dealtPrssKeys, h]]
        exact (hs hm).2 j i ⟨hj, hiD, hi⟩)).map
      (fun o => (Sum.inr (clipOutput count o) : RandOutput C E))
    simp only [callStreams, liftComp_map]
    convert hc using 2
    exact frandShare_eq_clipOutput prims D receivers term pair c s ρ idx count count (fun b g => b g)
      (fun F g hg => by simp only [hg, ↓reduceIte]) i hiD hi

omit [Fintype E] [DecidableEq E] in
private theorem runsPure_tableCalls (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (c : HiddenCache C)
    (s : HashCache C) : ∀ (ρ : ℕ) (cs : List RandCall),
      (∀ call ∈ cs, 0 < call.streamBits → KeysCached D receivers term pair s) →
      ∃ outs, RunsPure prims s (tableCalls K D receivers term pair c ρ cs) outs ∧ ∀ i, i ∉ D.1 → i ∈ receivers →
        ∃ os, outs.mapM (· i) = some os ∧
          RunsPure prims s (liftComp (randStreams K (cachedBits D c) (dealtPrssKeys term pair i) i ρ cs) (LocalSpec C)) os
  | ρ, [], _ => ⟨[], RunsPure.pure prims s _, fun i _ _ => ⟨[], rfl, by
      simpa [randStreams] using RunsPure.pure prims s ([] : List (RandOutput C E))⟩⟩
  | ρ, call :: rest, hs => by
    obtain ⟨f, hf, hfi⟩ := runsPure_tableCall prims K D receivers term pair c s ρ call (hs call List.mem_cons_self)
    obtain ⟨outs, ho, hoi⟩ := runsPure_tableCalls prims K D receivers term pair c s (ρ + 1) rest
      fun x hx => hs x (List.mem_cons_of_mem call hx)
    refine ⟨f :: outs, ?_, fun i hiD hi => ?_⟩
    · simp only [tableCalls]
      exact hf.bind (ho.bind (RunsPure.pure prims s _))
    · obtain ⟨o, hfo, hro⟩ := hfi i hiD hi
      obtain ⟨os, hos, hros⟩ := hoi i hiD hi
      refine ⟨o :: os, by simp [List.mapM_cons, hfo, hos], ?_⟩
      simp only [randStreams, liftComp_bind, liftComp_pure]
      exact hro.bind (hros.bind (RunsPure.pure prims s _))

omit [Fintype E] [DecidableEq E] in
/-- From a hash cache with every known key, the draws of the honest receivers and the calls with
tables are fixed and keep the cache, and they give the same outputs. -/
private theorem honestStreams_eq_tableCalls (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (c : HiddenCache C) (s : HashCache C)
    (hs : ∀ key ∈ knownKeys D receivers term pair calls, (s (.streamKey key)).isSome) :
    (simulateQ (localAnswer prims) (honestStreams K (cachedBits D c) (honestReceivers D receivers) term pair label
      calls)).run s =
      (simulateQ (localAnswer prims) ((fun outs i => if i ∉ D.1 ∧ i ∈ receivers then outs.mapM (· i) else none) <$>
        tableCalls K D receivers term pair c label calls)).run s := by
  have hcached : ∀ call ∈ calls, 0 < call.streamBits → KeysCached D receivers term pair s := by
    intro call hcall hpos
    have hany : calls.any (fun call => decide (0 < call.streamBits)) = true :=
      List.any_eq_true.mpr ⟨call, hcall, by simpa using hpos⟩
    refine ⟨fun T hT => hs _ ?_, fun j i h => hs _ ?_⟩
    · simp only [knownKeys, hany, ↓reduceIte]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨T, List.mem_filter.mpr ⟨by simp [Committee.terms],
        by simpa using hT⟩, rfl⟩)
    · simp only [knownKeys, hany, ↓reduceIte]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, by simp [Committee.parties],
        List.mem_filterMap.mpr ⟨i, by simp [Committee.parties], by simp [h]⟩⟩)
  obtain ⟨outs, ho, hoi⟩ := runsPure_tableCalls prims K D receivers term pair c s label calls hcached
  have hl : RunsPure prims s (honestStreams K (cachedBits D c) (honestReceivers D receivers) term pair label calls)
      (fun i => if i ∉ D.1 ∧ i ∈ receivers then outs.mapM (· i) else none) := by
    unfold honestStreams
    refine RunsPure.sequenceFin fun j => ?_
    by_cases hj : j ∉ D.1 ∧ j ∈ receivers
    · obtain ⟨os, hos, hr⟩ := hoi j hj.1 hj.2
      simp only [honestReceivers, Finset.mem_filter, hj, hos]
      exact hr.map some
    · have hj' : j ∉ honestReceivers D receivers := by
        simp only [honestReceivers, Finset.mem_filter]
        tauto
      simp only [hj', hj, ↓reduceIte]
      exact RunsPure.pure prims s _
  exact hl.trans (ho.map fun outs i => if i ∉ D.1 ∧ i ∈ receivers then outs.mapM (· i) else none).symm

omit [Fintype E] [DecidableEq E] in
/-- The hash half. The honest receivers compute the known streams one operator after the other, and
the simulator computes each known stream one time, one call after the other. -/
private theorem streamHop_hash (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (c : HiddenCache C) :
    SameRun prims (honestStreams K (cachedBits D c) (honestReceivers D receivers) term pair label calls)
      ((fun outs i => if i ∉ D.1 ∧ i ∈ receivers then outs.mapM (· i) else none) <$>
        tableCalls K D receivers term pair c label calls) := by
  intro s
  set keys := knownKeys D receivers term pair calls
  have hreal := sameRun_prepend prims _ keys
    (touches_honestStreams prims K D receivers term pair label calls c)
  have hideal := sameRun_prepend prims ((fun outs i => if i ∉ D.1 ∧ i ∈ receivers then outs.mapM (· i) else none) <$>
    tableCalls K D receivers term pair c label calls) keys fun key hk =>
    (touches_tableCalls prims K D receivers term pair label calls c key hk).map _
  refine (hreal s).trans (EvalDistEq.trans ?_ (hideal s).symm)
  simp only [simulateQ_bind, StateT.run_bind]
  refine EvalDistEq.bind_congr_of_support _ fun r hr => ?_
  rw [honestStreams_eq_tableCalls prims K D receivers term pair label calls c r.2
    (streamKeys_cached prims keys s r hr)]

/-! ## The random half -/

/-- The hidden cache that holds the table `g` at the hidden positions of the calls `cs` from round
label `ρ`. -/
def tableCache (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ : ℕ)
    (cs : List RandCall) (g : HiddenPos D cs → Bit) : HiddenCache C :=
  cacheFin (hiddenAddr D term pair ρ cs ∘ (Fintype.equivFin (HiddenPos D cs)).symm)
    (g ∘ (Fintype.equivFin (HiddenPos D cs)).symm) ∅

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `frandOut` reads the fresh values only at the hidden names. -/
private theorem frandOut_congr {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh fresh' : C.Term → Fin count → R)
    (freshPair freshPair' : C.Pair → Fin count → R) (hterm : ∀ T, Hidden D (.term T) → fresh T = fresh' T)
    (hpair : ∀ p, Hidden D (.pair p) → freshPair p = freshPair' p) :
    frandOut D count known knownPairs fresh freshPair = frandOut D count known knownPairs fresh' freshPair' := by
  funext i
  unfold frandOut
  split_ifs with hi
  · rfl
  · refine congrArg some (Prod.ext (funext fun T => ?_) (funext fun j => ?_))
    · dsimp only
      split_ifs with h1 h2
      · rfl
      · rw [hterm T h2]
      · rfl
    · dsimp only
      split_ifs with h1 h2
      · rfl
      · rfl
      · have hp : Hidden D (.pair (C.pairOf i j h1)) := by
          simp only [Hidden, Committee.pairOf]
          split_ifs <;> exact ⟨by assumption, by assumption⟩
        rw [hpair _ hp]

omit [Fintype E] [DecidableEq E] in
/-- One call reads the hidden cache only at its hidden positions. -/
private theorem tableCall_congr (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (c c' : HiddenCache C) (ρ : ℕ) (call : RandCall)
    (h : ∀ name, Hidden D name → ∀ pos < call.streamBits,
      c ((name, (dealtKey term pair name).getD 0), ρ, call.idx, pos) =
        c' ((name, (dealtKey term pair name).getD 0), ρ, call.idx, pos)) :
    tableCall K D receivers term pair c ρ call = tableCall K D receivers term pair c' ρ call := by
  cases call with
  | elements idx count =>
    simp only [RandCall.streamBits, RandCall.idx] at h
    simp only [tableCall]
    refine bind_congr fun known => congrArg pure (funext fun i => congrArg _ (congrFun (frandOut_congr _ _ _ _ _ _ _ _
      (fun T hT => ?_) (fun q hq => ?_)) i))
    all_goals
      funext g
      congr 1
      funext e
      have hpos : elementBits * g.val + e.val < elementBits * count := by
        have := Nat.mul_le_mul_left elementBits (Nat.succ_le_of_lt g.isLt)
        rw [Nat.mul_succ] at this
        omega
      simp only [tableBit]
      rw [h _ (by assumption) _ hpos]
  | bits idx count =>
    simp only [RandCall.streamBits, RandCall.idx] at h
    simp only [tableCall]
    refine bind_congr fun known => congrArg pure (funext fun i => congrArg _ (congrFun (frandOut_congr _ _ _ _ _ _ _ _
      (fun T hT => ?_) (fun q hq => ?_)) i))
    all_goals
      funext g
      simp only [tableBit]
      rw [h _ (by assumption) _ g.isLt]

omit [Fintype E] [DecidableEq E] in
/-- The calls read the hidden cache only at their hidden positions. -/
private theorem tableCalls_congr (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (c c' : HiddenCache C) :
    ∀ (ρ : ℕ) (cs : List RandCall), (∀ (k : Fin cs.length) name, Hidden D name → ∀ pos < (cs.get k).streamBits,
      c ((name, (dealtKey term pair name).getD 0), ρ + k.val, (cs.get k).idx, pos) =
        c' ((name, (dealtKey term pair name).getD 0), ρ + k.val, (cs.get k).idx, pos)) →
      tableCalls K D receivers term pair c ρ cs = tableCalls K D receivers term pair c' ρ cs
  | _, [], _ => rfl
  | ρ, call :: rest, h => by
    simp only [tableCalls]
    rw [tableCall_congr K D receivers term pair c c' ρ call fun name hn pos hpos => by
        simpa using h ⟨0, by simp⟩ name hn pos hpos,
      tableCalls_congr K D receivers term pair c c' (ρ + 1) rest fun k name hn pos hpos => by
        have e : ρ + 1 + k.val = ρ + (k.val + 1) := by omega
        rw [e]
        simpa using h k.succ name hn pos hpos]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation on the counted copy is the same computation on the free copy, without the count. -/
private theorem worldAnswer_counted_local (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α)
    (s : HashCache C) :
    (simulateQ (worldAnswer prims) (counted (liftComp oa (SimulatorSpec C)))).run s =
      (simulateQ (localAnswer prims) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    have e : counted (liftComp (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _) (SimulatorSpec C)) =
        (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
      rcases t with t | (q | x) <;> rfl
    rw [liftComp_bind, counted_bind, simulateQ_bind, StateT.run_bind, e, simulateQ_bind, StateT.run_bind]
    simp only [ih]
    rcases t with t | (q | x) <;> rfl

/-- A uniform sample is a uniform sample of a type in bijection with it. -/
private theorem uniform_bij_bind {P Q β : Type} [SampleableType P] [SampleableType Q] (f : Q → P)
    (hf : Function.Bijective f) (F : P → ProbComp β) :
    (($ᵗ P) >>= F) =ᵈ (($ᵗ Q) >>= fun q => F (f q)) := by
  refine (EvalDistEq.bind_left (SampleableType.map_uniformSample_evalDistEq_of_bijective hf).symm F).trans ?_
  rw [bind_map_left]

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

/-- The table of a uniform function at the points of a subtype is uniform. -/
private theorem uniform_restrict {α X : Type} [Fintype α] [DecidableEq α] (P : α → Prop) [SampleableType (α → X)]
    [SampleableType ({x // P x} → X)] [SampleableType ({x // ¬ P x} → X)] :
    (fun (t : α → X) (a : {x // P x}) => t a.1) <$> ($ᵗ (α → X)) =ᵈ ($ᵗ ({x // P x} → X)) := by
  have hb := (Equiv.piEquivPiSubtypeProd P fun _ => X).bijective
  have h1 : (fun (t : α → X) (a : {x // P x}) => t a.1) <$> ($ᵗ (α → X)) =
      Prod.fst <$> ((Equiv.piEquivPiSubtypeProd P fun _ => X) <$> ($ᵗ (α → X))) := by
    rw [Functor.map_map]
    rfl
  rw [h1]
  refine ((SampleableType.map_uniformSample_evalDistEq_of_bijective hb).map Prod.fst).trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [map_bind, map_pure]
  refine (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans ?_
  rw [bind_pure]

private theorem uniform_restrict_bind {α X γ : Type} [Fintype α] [DecidableEq α] (P : α → Prop)
    [SampleableType (α → X)] [SampleableType ({x // P x} → X)] [SampleableType ({x // ¬ P x} → X)]
    (G : ({x // P x} → X) → ProbComp γ) :
    (($ᵗ (α → X)) >>= fun t => G fun a => t a.1) =ᵈ (($ᵗ ({x // P x} → X)) >>= G) := by
  refine EvalDistEq.trans ?_ (EvalDistEq.bind_left (uniform_restrict P) G)
  rw [bind_map_left]

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The fresh values that a call reads at the hidden names are uniform. A uniform table of the hidden
stream bits, decoded by `split`, has the law of the uniform tables of `F_rand` on each statistic that
reads only the hidden names. -/
private theorem uniform_hiddenTables {R β : Type} [SampleableType R] (D : C.Coalition) (m count : ℕ)
    (split : (Fin m → Bit) ≃ (Fin count → R))
    (F : (C.Term → Fin count → R) → (C.Pair → Fin count → R) → β)
    (hF : ∀ t t' u u', (∀ T, Hidden D (.term T) → t T = t' T) → (∀ p, Hidden D (.pair p) → u p = u' p) →
      F t u = F t' u')
    (dt : ({name : KeyName C // Hidden D name} × Fin m → Bit) → C.Term → Fin count → R)
    (dp : ({name : KeyName C // Hidden D name} × Fin m → Bit) → C.Pair → Fin count → R)
    (hdt : ∀ g T (h : Hidden D (.term T)), dt g T = split fun pos => g (⟨.term T, h⟩, pos))
    (hdp : ∀ g p (h : Hidden D (.pair p)), dp g p = split fun pos => g (⟨.pair p, h⟩, pos)) :
    (($ᵗ ({name : KeyName C // Hidden D name} × Fin m → Bit)) >>= fun g => pure (F (dt g) (dp g))) =ᵈ
      (($ᵗ (C.Term → Fin count → R)) >>= fun t => ($ᵗ (C.Pair → Fin count → R)) >>= fun u => pure (F t u)) := by
  let HT := ({T : C.Term // Hidden D (.term T)} → Fin count → R) × ({q : C.Pair // Hidden D (.pair q)} → Fin count → R)
  let d0 : {name : KeyName C // Hidden D name} × Fin m → Bit := fun _ => 0
  let ext1 : ({T : C.Term // Hidden D (.term T)} → Fin count → R) → C.Term → Fin count → R := fun a T =>
    if h : Hidden D (.term T) then a ⟨T, h⟩ else dt d0 T
  let ext2 : ({q : C.Pair // Hidden D (.pair q)} → Fin count → R) → C.Pair → Fin count → R := fun b q =>
    if h : Hidden D (.pair q) then b ⟨q, h⟩ else dp d0 q
  let G : HT → ProbComp β := fun ab => pure (F (ext1 ab.1) (ext2 ab.2))
  let Φ : ({name : KeyName C // Hidden D name} × Fin m → Bit) → HT := fun g =>
    (fun T => split fun pos => g (⟨.term T.1, T.2⟩, pos), fun q => split fun pos => g (⟨.pair q.1, q.2⟩, pos))
  have hΦ : Function.Bijective Φ := by
    let e := (Equiv.curry {name : KeyName C // Hidden D name} (Fin m) Bit).trans
      ((Equiv.arrowCongr (Equiv.refl _) split).trans
        ((Equiv.arrowCongr (hiddenNameSum D) (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)))
    exact (show ⇑e = Φ from rfl) ▸ e.bijective
  have hL : ∀ g, F (dt g) (dp g) = F (ext1 (Φ g).1) (ext2 (Φ g).2) := fun g =>
    hF _ _ _ _ (fun T h => by simp only [ext1, Φ, h, ↓reduceDIte, hdt g T h])
      (fun q h => by simp only [ext2, Φ, h, ↓reduceDIte, hdp g q h])
  have hR : ∀ t u, F t u = F (ext1 fun T => t T.1) (ext2 fun q => u q.1) := fun t u =>
    hF _ _ _ _ (fun T h => by simp only [ext1, h, ↓reduceDIte]) (fun q h => by simp only [ext2, h, ↓reduceDIte])
  have lhs : (($ᵗ ({name : KeyName C // Hidden D name} × Fin m → Bit)) >>= fun g => pure (F (dt g) (dp g))) =ᵈ
      (($ᵗ HT) >>= G) := by
    conv_lhs => enter [2, g]; rw [hL g]
    exact (uniform_bij_bind Φ hΦ G).symm
  have rhs : (($ᵗ (C.Term → Fin count → R)) >>= fun t => ($ᵗ (C.Pair → Fin count → R)) >>= fun u =>
      pure (F t u)) =ᵈ (($ᵗ HT) >>= G) := by
    conv_lhs => enter [2, t, 2, u]; rw [hR t u]
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind]
    refine (EvalDistEq.bind_right (g := fun t => ($ᵗ ({q : C.Pair // Hidden D (.pair q)} → Fin count → R)) >>=
      fun b => G ((fun T => t T.1), b)) _ fun t => ?_).trans ?_
    · exact uniform_restrict_bind (fun q : C.Pair => Hidden D (.pair q)) fun b => G ((fun T => t T.1), b)
    · exact uniform_restrict_bind (fun T : C.Term => Hidden D (.term T)) fun a =>
        ($ᵗ ({q : C.Pair // Hidden D (.pair q)} → Fin count → R)) >>= fun b => G (a, b)
  exact lhs.trans rhs.symm

omit [Fintype E] [DecidableEq E] in
/-- One call. The table of its hidden stream bits decodes to the fresh values of `F_rand`. -/
private theorem random_call [SampleableType E] (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ : ℕ)
    (call : RandCall) (mk : ({name : KeyName C // Hidden D name} × Fin call.streamBits → Bit) → HiddenCache C)
    (hmk : ∀ g name (hn : Hidden D name) pos (hpos : pos < call.streamBits),
      mk g ((name, (dealtKey term pair name).getD 0), ρ, call.idx, pos) = some (g (⟨name, hn⟩, ⟨pos, hpos⟩)))
    (s : HashCache C) :
    (($ᵗ ({name : KeyName C // Hidden D name} × Fin call.streamBits → Bit)) >>= fun g =>
      (simulateQ (localAnswer prims) (tableCall K D receivers term pair (mk g) ρ call)).run s) =ᵈ
      (simulateQ (worldAnswer prims) (idealCall K D receivers term pair ρ call)).run s := by
  cases call with
  | elements idx count =>
    simp only [RandCall.idx, RandCall.streamBits] at hmk
    simp only [tableCall, idealCall, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      worldAnswer_counted_local, worldAnswer_free_liftComp, bind_map_left]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
    refine uniform_hiddenTables D (elementBits * count) count (elementSplit K count)
      (fun t u => ((fun i => (frandOut D count r.1.1 r.1.2 t u i).map Sum.inl), r.2))
      (fun t t' u u' ht hu => by rw [frandOut_congr D count r.1.1 r.1.2 t t' u u' ht hu]) _ _ ?_ ?_
    · intro g T h
      funext g'
      rw [elementSplit_apply]
      congr 1
      funext e
      simp only [tableBit]
      rw [hmk g _ h _ (elementPos_lt g' e)]
      rfl
    · intro g q h
      funext g'
      rw [elementSplit_apply]
      congr 1
      funext e
      simp only [tableBit]
      rw [hmk g _ h _ (elementPos_lt g' e)]
      rfl
  | bits idx count =>
    simp only [RandCall.idx, RandCall.streamBits] at hmk
    simp only [tableCall, idealCall, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      worldAnswer_counted_local, worldAnswer_free_liftComp, bind_map_left]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
    refine uniform_hiddenTables D count count (Equiv.refl _)
      (fun t u => ((fun i => (frandOut D count r.1.1 r.1.2 t u i).map Sum.inr), r.2))
      (fun t t' u u' ht hu => by rw [frandOut_congr D count r.1.1 r.1.2 t t' u u' ht hu]) _ _ ?_ ?_
    · intro g T h
      funext g'
      simp only [tableBit]
      rw [hmk g _ h _ g'.isLt]
      rfl
    · intro g q h
      funext g'
      simp only [tableBit]
      rw [hmk g _ h _ g'.isLt]
      rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem hiddenAddr_injective (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (ρ : ℕ) (cs : List RandCall) : Function.Injective (hiddenAddr D term pair ρ cs) := by
  rintro ⟨k, ⟨n, hn⟩, g⟩ ⟨k', ⟨n', hn'⟩, g'⟩ h
  simp only [hiddenAddr, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, -⟩, hk, -, hg⟩ := h
  obtain rfl : k = k' := Fin.ext (by omega)
  obtain rfl : g = g' := Fin.ext hg
  rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem tableCache_at (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (ρ : ℕ) (cs : List RandCall) (g : HiddenPos D cs → Bit) (p : HiddenPos D cs) :
    tableCache D term pair ρ cs g (hiddenAddr D term pair ρ cs p) = some (g p) := by
  have h := cacheFin_at _ ((hiddenAddr_injective D term pair ρ cs).comp
    (Fintype.equivFin (HiddenPos D cs)).symm.injective) (g ∘ (Fintype.equivFin (HiddenPos D cs)).symm) ∅
    (Fintype.equivFin (HiddenPos D cs) p)
  simp only [Function.comp_apply] at h
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- The hidden positions of the calls `call :: rest` are those of `call` and those of `rest`. -/
private def hiddenPosCons (D : C.Coalition) (call : RandCall) (rest : List RandCall) :
    HiddenPos D (call :: rest) ≃ ({name : KeyName C // Hidden D name} × Fin call.streamBits) ⊕ HiddenPos D rest where
  toFun p := match p with
    | ⟨⟨0, _⟩, n, pos⟩ => .inl (n, pos)
    | ⟨⟨k + 1, hk⟩, n, pos⟩ => .inr ⟨⟨k, by simpa using hk⟩, n, pos⟩
  invFun q := match q with
    | .inl (n, pos) => ⟨⟨0, by simp⟩, n, pos⟩
    | .inr ⟨k, n, pos⟩ => ⟨k.succ, n, pos⟩
  left_inv p := by rcases p with ⟨⟨_ | k, hk⟩, n, pos⟩ <;> rfl
  right_inv q := by rcases q with ⟨n, pos⟩ | ⟨k, n, pos⟩ <;> rfl

/-- A uniform table on `P` is two independent uniform tables on the two parts of `P`. -/
private theorem uniform_split_bind {P A B β : Type} [Fintype P] [DecidableEq P] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (σ : P ≃ A ⊕ B) (F : (P → Bit) → ProbComp β) :
    (($ᵗ (P → Bit)) >>= F) =ᵈ
      (($ᵗ (A → Bit)) >>= fun a => ($ᵗ (B → Bit)) >>= fun b => F fun p => Sum.elim a b (σ p)) := by
  refine (uniform_bij_bind (fun ab : (A → Bit) × (B → Bit) => fun p => Sum.elim ab.1 ab.2 (σ p))
    ((Equiv.sumArrowEquivProdArrow A B Bit).symm.trans (Equiv.arrowCongr σ.symm (Equiv.refl Bit))).bijective F).trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  exact .rfl

omit [Fintype E] [DecidableEq E] in
/-- The calls. Induction on the calls with the split of the hidden positions into the first call and
the other calls. -/
private theorem random_calls [SampleableType E] (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) :
    ∀ (ρ : ℕ) (cs : List RandCall) (s : HashCache C),
      (($ᵗ (HiddenPos D cs → Bit)) >>= fun g =>
        (simulateQ (localAnswer prims) (tableCalls K D receivers term pair (tableCache D term pair ρ cs g) ρ cs)).run s) =ᵈ
        (simulateQ (worldAnswer prims) (idealCalls K D receivers term pair ρ cs)).run s := by
  intro ρ cs
  induction cs generalizing ρ with
  | nil =>
    intro s
    simp only [tableCalls, idealCalls, simulateQ_pure, StateT.run_pure]
    exact OracleComp.EvalDistEq.bind_const _ _
  | cons call rest ih =>
    intro s
    set σ := hiddenPosCons D call rest
    let mk : ({name : KeyName C // Hidden D name} × Fin call.streamBits → Bit) → HiddenCache C := fun a =>
      tableCache D term pair ρ (call :: rest) fun p => Sum.elim a (fun _ => 0) (σ p)
    have hhead : ∀ a b, tableCall K D receivers term pair
        (tableCache D term pair ρ (call :: rest) fun p => Sum.elim a b (σ p)) ρ call =
        tableCall K D receivers term pair (mk a) ρ call := fun a b =>
      tableCall_congr K D receivers term pair _ _ ρ call fun name hn pos hpos =>
        (tableCache_at D term pair ρ (call :: rest) _ ⟨⟨0, by simp⟩, ⟨name, hn⟩, ⟨pos, hpos⟩⟩).trans
          (tableCache_at D term pair ρ (call :: rest) (fun p => Sum.elim a (fun _ => 0) (σ p))
            ⟨⟨0, by simp⟩, ⟨name, hn⟩, ⟨pos, hpos⟩⟩).symm
    have htail : ∀ a b, tableCalls K D receivers term pair
        (tableCache D term pair ρ (call :: rest) fun p => Sum.elim a b (σ p)) (ρ + 1) rest =
        tableCalls K D receivers term pair (tableCache D term pair (ρ + 1) rest b) (ρ + 1) rest := fun a b =>
      tableCalls_congr K D receivers term pair _ _ (ρ + 1) rest fun k name hn pos hpos => by
        have e : ((name, (dealtKey term pair name).getD 0), ρ + 1 + k.val, (rest.get k).idx, pos) =
            hiddenAddr D term pair ρ (call :: rest) ⟨k.succ, ⟨name, hn⟩, ⟨pos, hpos⟩⟩ := by
          simp only [hiddenAddr, Fin.val_succ, Prod.mk.injEq, and_true, true_and]
          refine ⟨by omega, rfl⟩
        exact (congrArg _ e).trans ((tableCache_at D term pair ρ (call :: rest) _ _).trans
          (tableCache_at D term pair (ρ + 1) rest b ⟨k, ⟨name, hn⟩, ⟨pos, hpos⟩⟩).symm)
    refine (uniform_split_bind σ _).trans ?_
    simp only [tableCalls, hhead, htail, idealCalls, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure]
    refine (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    rw [← bind_assoc]
    refine (EvalDistEq.bind_right _ fun r => ?_).trans
      (EvalDistEq.bind_left (random_call prims K D receivers term pair ρ call mk (fun g name hn pos hpos =>
        tableCache_at D term pair ρ (call :: rest) _ ⟨⟨0, by simp⟩, ⟨name, hn⟩, ⟨pos, hpos⟩⟩) s) _)
    rw [← bind_assoc]
    exact EvalDistEq.bind_left (ih (ρ + 1) r.2) _

omit [Fintype E] [DecidableEq E] in
/-- The random half. The presampled hidden streams decode to the fresh values of `F_rand`. -/
private theorem streamHop_random [SampleableType E] (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (s : HashCache C) :
    (($ᵗ (Fin (Fintype.card (HiddenPos D calls)) → Bit)) >>= fun vals =>
      (simulateQ (localAnswer prims) (tableCalls K D receivers term pair (cacheFin
        (hiddenAddr D term pair label calls ∘ (Fintype.equivFin (HiddenPos D calls)).symm) vals ∅)
        label calls)).run s) =ᵈ
      (simulateQ (worldAnswer prims) (idealCalls K D receivers term pair label calls)).run s := by
  set e := Fintype.equivFin (HiddenPos D calls)
  have hb : Function.Bijective fun vals : Fin (Fintype.card (HiddenPos D calls)) → Bit => vals ∘ e :=
    (Equiv.arrowCongr e.symm (Equiv.refl Bit)).bijective
  have hc : ∀ vals : Fin (Fintype.card (HiddenPos D calls)) → Bit,
      cacheFin (hiddenAddr D term pair label calls ∘ e.symm) vals ∅ = tableCache D term pair label calls (vals ∘ e) := by
    intro vals
    simp only [tableCache, e, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  simp only [hc]
  refine EvalDistEq.trans ?_ ((EvalDistEq.bind_left (SampleableType.map_uniformSample_evalDistEq_of_bijective hb) fun g =>
    (simulateQ (localAnswer prims) (tableCalls K D receivers term pair (tableCache D term pair label calls g)
      label calls)).run s).trans (random_calls prims K D receivers term pair label calls s))
  rw [bind_map_left]

omit [Fintype E] [DecidableEq E] in
/-- The hash half and the random half of the hop. The honest receivers read the presampled hidden
streams and compute the known streams. This has the law of the calls of `F_rand` with the known
streams of the simulator. -/
private theorem streamHop_core [SampleableType E] (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) (s : HashCache C) :
    (($ᵗ (Fin (Fintype.card (HiddenPos D calls)) → Bit)) >>= fun vals =>
      (simulateQ (localAnswer prims) (honestStreams K (cachedBits D (cacheFin
        (hiddenAddr D term pair label calls ∘ (Fintype.equivFin (HiddenPos D calls)).symm) vals ∅))
        (honestReceivers D receivers) term pair label calls)).run s) =ᵈ
      (fun r => (fun i => if i ∉ D.1 ∧ i ∈ receivers then r.1.mapM (· i) else none, r.2)) <$>
        (simulateQ (worldAnswer prims) (idealCalls K D receivers term pair label calls)).run s := by
  refine (EvalDistEq.bind_right _ fun vals => streamHop_hash prims K D receivers term pair label calls _ s).trans ?_
  simp only [simulateQ_map, StateT.run_map]
  rw [← map_bind]
  exact (streamHop_random prims K D receivers term pair label calls s).map _

omit [Fintype E] [DecidableEq E] in
/-- The draws of the honest receivers and the distinguisher in `streamWorld` are the calls of
`F_rand` and the distinguisher on the hash cache. -/
private theorem streamHop_tail [SampleableType E] (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) {σ : Type} (Z : σ × (C.Party → Option (List (RandOutput C E))) → OracleComp (LocalSpec C) Bool)
    (st : σ) (s : HashCache C) :
    Prod.fst <$> (simulateQ (streamWorld prims D)
        (free (honestStreams K prgBits (honestReceivers D receivers) term pair label calls) >>= fun outputs =>
          counted (liftComp (Z (st, outputs)) (SimulatorSpec C)))).run (s, ∅) =ᵈ
      Prod.fst <$> (simulateQ (worldAnswer prims) (idealCalls K D receivers term pair label calls >>= fun outputs =>
          counted (liftComp (Z (st, fun i => if i ∉ D.1 ∧ i ∈ receivers then outputs.mapM (· i) else none))
            (SimulatorSpec C)))).run s := by
  simp only [simulateQ_bind, StateT.run_bind, map_bind, streamWorld_counted, Functor.map_map]
  rw [show ((simulateQ (streamWorld prims D) (free (honestStreams K prgBits (honestReceivers D receivers)
      term pair label calls))).run (s, ∅) >>= fun r => (fun q => q.1) <$>
        (simulateQ (worldAnswer prims) (counted (liftComp (Z (st, r.1)) (SimulatorSpec C)))).run r.2.1) =
      ((fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) (free (honestStreams K prgBits
        (honestReceivers D receivers) term pair label calls))).run (s, ∅)) >>= fun r => (fun q => q.1) <$>
        (simulateQ (worldAnswer prims) (counted (liftComp (Z (st, r.1)) (SimulatorSpec C)))).run r.2 by
      rw [bind_map_left]]
  refine (EvalDistEq.bind_left (streamWorld_randStreams prims K D _ term pair label calls s ∅
    fun _ _ => rfl) _).trans ?_
  refine (EvalDistEq.bind_left (streamHop_core prims K D receivers term pair label calls s) _).trans ?_
  rw [bind_map_left]

end Draws

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)
  (Z : Distinguisher C A.State (List (RandOutput C E))) (prims : Primitives)

/-- The real run with random hidden streams is the ideal run. -/
theorem prssRand_streamHop :
    (Pr{let y ← (simulateQ (streamWorld prims D) (prssRandReal K label calls D A x z Z)).run' (∅, ∅)}[y = true]).toReal =
      accepts prims (prssRandIdeal K label calls D A x z Z) := by
  have hR : Pr{let r ← runWorld prims (prssRandIdeal K label calls D A x z Z)}[r.1 = true] =
      Pr{let y ← (simulateQ (worldAnswer prims) (prssRandIdeal K label calls D A x z Z)).run' ∅}[y = true] := by
    rw [← fst_map_runWorld, prEvent_map]
  rw [accepts, hR]
  congr 1
  refine EvalDistEq.prEvent_eq ?_ _
  unfold prssRandReal prssRandIdeal distinguish
  rw [realExecution_prssRand, idealExecution_FrandCalls]
  simp only [bind_assoc, pure_bind, StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
    streamWorld_counted, streamWorld_free_liftComp, worldAnswer_counted_liftComp, bind_map_left]
  refine EvalDistEq.bind_right _ fun r0 => EvalDistEq.bind_right _ fun term => EvalDistEq.bind_right _
    fun pair => EvalDistEq.bind_right _ fun r1 => ?_
  have h := streamHop_tail prims K D r1.1.2 term pair label calls Z r1.1.1 r1.2
  simp only [simulateQ_bind, StateT.run_bind, map_bind] at h
  exact h

end ThresholdLeanXmssSecurity
