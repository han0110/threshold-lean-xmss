import ThresholdLeanXmssSecurity.Proof.Pilot.StreamTables

/-!
# The rows of the join of the pilot

At the values of the prefetch at a cache, the frozen real building blocks of an honest operator agree
with the blocks on drawn values. `mapRun` runs the programs with a map on their local queries, and the
structure rows of the join give the join in its output form.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Map

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}
  (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)))

/-- The table form of a program is its map form with `tableLocal`. -/
private theorem tableProgram_eq_mapProgram (D : C.Coalition) (c : HiddenCache C) {α : Type} (p : PartyM C E G α) :
    RealNetworkN3.tableProgram D c p = mapProgram (RealNetworkN3.tableLocal D c) p := rfl

private theorem mapProgram_pure {α : Type} (a : α) : mapProgram m (pure a : PartyM C E G α) = pure a := by
  unfold mapProgram
  apply OptionT.ext
  simp

private theorem mapProgram_failure {α : Type} : mapProgram m (failure : PartyM C E G α) = failure := by
  unfold mapProgram
  apply OptionT.ext
  simp

private theorem mapProgram_exchange (out : Mail C E) : mapProgram m (exchange out : PartyM C E G (Mail C E)) = exchange out := by
  unfold mapProgram exchange
  apply OptionT.ext
  simp [OptionT.run_bind, OptionT.lift, partyMap, Option.elimM]
  congr 1
  funext x
  split_ifs <;> simp

private theorem mapProgram_require (p : Prop) : mapProgram m (require p : PartyM C E G Unit) = require p := by
  unfold require
  split_ifs
  · exact mapProgram_pure m ()
  · exact mapProgram_failure m

/-- The map on the local queries of a program lifted from the local oracles. It is
`partyTable_liftComp` for each map. -/
private theorem partyMap_liftComp {β : Type} (oa : OracleComp (LocalSpec C) β) :
    simulateQ (partyMap (E := E) (G := G) m) (liftComp oa (PartySpec C E G)) =
      liftComp (simulateQ m oa) (PartySpec C E G) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure]
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k : OracleComp (LocalSpec C) _) (PartySpec C E G) =
        (liftM ((PartySpec C E G).query (.inl (.inl t))) : OracleComp (PartySpec C E G) _) >>=
          fun u => liftComp (k u) _ := by
      rw [liftComp_bind]
      rcases t with n | x | x <;> rfl
    rw [e, simulateQ_bind, simulateQ_bind, liftComp_bind]
    simp only [ih, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rfl

/-- A local step whose local queries the map answers with `v` is `pure v`. -/
private theorem mapProgram_localStep_of_eq {β : Type} (oa : OracleComp (LocalSpec C) β) (v : β)
    (h : simulateQ m oa = pure v) : mapProgram m (localStep oa : PartyM C E G β) = pure v := by
  unfold mapProgram localStep
  apply OptionT.ext
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure, partyMap_liftComp, h,
    liftComp_pure, pure_bind, OptionT.run_pure]

end Map

section Frozen

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (s : HashCache C)

attribute [local instance] inhabitedField

/-- `freezeLocal` answers the computation `oa` of `H` and `PRG` with no query, and it returns `v`. -/
def FrozenPure {β : Type} (oa : OracleComp (RoSpec C) β) (v : β) : Prop :=
  simulateQ (freezeLocal prims s) (liftComp oa (LocalSpec C)) = pure v

omit [Field E] [Algebra Bit E] in
theorem FrozenPure.pure' {β : Type} (v : β) : FrozenPure prims s (pure v) v := by
  simp [FrozenPure]

omit [Field E] [Algebra Bit E] in
theorem FrozenPure.bind {β γ : Type} {oa : OracleComp (RoSpec C) β} {f : β → OracleComp (RoSpec C) γ} {v : β}
    {w : γ} (h : FrozenPure prims s oa v) (hf : FrozenPure prims s (f v) w) : FrozenPure prims s (oa >>= f) w := by
  unfold FrozenPure at h hf ⊢
  rw [liftComp_bind, simulateQ_bind, h, pure_bind]
  exact hf

omit [Field E] [Algebra Bit E] in
theorem FrozenPure.map {β γ : Type} {oa : OracleComp (RoSpec C) β} {v : β} (h : FrozenPure prims s oa v)
    (f : β → γ) : FrozenPure prims s (f <$> oa) (f v) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind prims s (FrozenPure.pure' prims s _)

omit [Field E] [Algebra Bit E] in
theorem FrozenPure.mapM {γ β : Type} {f : γ → OracleComp (RoSpec C) β} {g : γ → β} :
    ∀ l : List γ, (∀ x ∈ l, FrozenPure prims s (f x) (g x)) → FrozenPure prims s (l.mapM f) (l.map g)
  | [], _ => by simpa using FrozenPure.pure' prims s ([] : List β)
  | a :: l, h => by
    simp only [List.mapM_cons, List.map_cons]
    exact (h a List.mem_cons_self).bind prims s ((FrozenPure.mapM l fun x hx => h x (List.mem_cons_of_mem a hx)).bind
      prims s (FrozenPure.pure' prims s _))

omit [Field E] [Algebra Bit E] in
/-- A stream read under a key with a cell in `s` is frozen to the stream value of the cell. -/
theorem frozenPure_prgBits (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ)
    (hs : 0 < m → (s (.streamKey key)).isSome) :
    FrozenPure prims s (prgBits name key ρ idx m) (prgValue prims s key ρ idx m) := by
  unfold prgBits prgValue
  refine (FrozenPure.mapM prims s _ fun p hp => ?_).bind prims s (FrozenPure.pure' prims s _)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hs (by have := List.mem_range.mp hp; omega))
  unfold FrozenPure
  change simulateQ (freezeLocal prims s) (liftM ((LocalSpec C).query (.inr (.inr (name, key, ρ, idx, p))))) = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  simp [freezeLocal, hu]
  rfl

omit [Field E] [Algebra Bit E] in
/-- `cachedBits` is frozen to `cachedValue` when each key that it reads with `PRG` has a cell. -/
theorem frozenPure_cachedBits (D : C.Coalition) (c : HiddenCache C) (name : KeyName C) (key : HashOutput)
    (ρ idx m : ℕ) (hs : ¬ Hidden D name → 0 < m → (s (.streamKey key)).isSome) :
    FrozenPure prims s (cachedBits D c name key ρ idx m) (cachedValue prims D c s name key ρ idx m) := by
  by_cases hn : Hidden D name
  · simp only [cachedBits, cachedValue, hn, ↓reduceIte]
    exact FrozenPure.pure' prims s _
  · simp only [cachedBits, cachedValue, hn, ↓reduceIte]
    exact frozenPure_prgBits prims s name key ρ idx m (hs hn)

/-- The PRSS output of operator `i` with the value `val` of each key that it holds. -/
def keysValue {R : Type} [Zero R] (val : KeyName C → HashOutput → ℕ → R) (prss : PrssKeys C) (i : C.Party) :
    PrssOutput C R :=
  (fun T => if i ∈ C.holders T then val (.term T) (prss.term T) else fun _ => 0,
    fun j => if h : j = i then fun _ => 0 else val (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j))

omit [Field E] [Algebra Bit E] in
/-- The PRSS outputs of operator `i` are `FrozenPure` with the values `keysValue val prss i` when the
stream of each key that `i` holds is `FrozenPure`. -/
theorem frozenPure_prssStreams {R : Type} [Zero R] (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R))
    (val : KeyName C → HashOutput → ℕ → R) (prss : PrssKeys C) (i : C.Party)
    (hterm : ∀ T, i ∈ C.holders T → FrozenPure prims s (stream (.term T) (prss.term T)) (val (.term T) (prss.term T)))
    (hpair : ∀ j (h : j ≠ i), FrozenPure prims s (stream (.pair (C.pairOf i j h.symm)) (prss.pair j))
      (val (.pair (C.pairOf i j h.symm)) (prss.pair j))) :
    FrozenPure prims s (prssStreams stream prss i) (keysValue val prss i) := by
  unfold prssStreams
  refine (FrozenPure.mapM prims s (g := fun T => if i ∈ C.holders T then val (.term T) (prss.term T) else fun _ => 0)
    _ fun T _ => ?_).bind prims s ((FrozenPure.mapM prims s (g := fun j => if h : j = i then fun _ => 0 else
      val (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)) _ fun j _ => ?_).bind prims s ?_)
  · split_ifs with h
    · exact hterm T h
    · exact FrozenPure.pure' prims s _
  · split_ifs with h
    · exact FrozenPure.pure' prims s _
    · exact hpair j h
  · simp only [getD_terms_idxOf, getD_parties]
    exact FrozenPure.pure' prims s _

/-- Each key of operator `i` under a name that the coalition knows has a cell in `s`. -/
def KeysCellsAt (D : C.Coalition) (prss : PrssKeys C) (i : C.Party) : Prop :=
  (∀ T, i ∈ C.holders T → ¬ Hidden D (.term T) → (s (.streamKey (prss.term T))).isSome) ∧
    ∀ j (h : j ≠ i), ¬ Hidden D (.pair (C.pairOf i j h.symm)) → (s (.streamKey (prss.pair j))).isSome

variable (K : Constants C E)

/-- The output of a call of operator `i` at the label `ρ`, with the hidden streams from the table `c`
and the other streams from the cells of `s`. -/
def frozenCall (D : C.Coalition) (c : HiddenCache C) (prss : PrssKeys C) (i : C.Party) (ρ : ℕ) :
    RandCall → RandOutput C E
  | .elements idx count => .inl (clipOutput count (keysValue (fun name key g => K.encode.symm fun e =>
      cachedValue prims D c s name key ρ idx (elementBits * count) (elementBits * g + e)) prss i))
  | .bits idx count => .inr (clipOutput count (keysValue (fun name key =>
      cachedValue prims D c s name key ρ idx count) prss i))

theorem frozenPure_callStreams (D : C.Coalition) (c : HiddenCache C) (prss : PrssKeys C) (i : C.Party) (ρ : ℕ)
    (call : RandCall) (hcells : KeysCellsAt s D prss i) :
    FrozenPure prims s (callStreams K (cachedBits D c) prss i ρ call) (frozenCall prims s K D c prss i ρ call) := by
  cases call with
  | elements idx count =>
    refine (frozenPure_prssStreams prims s _ _ prss i (fun T hT => ?_) (fun j h => ?_)).map prims s _
    · exact (frozenPure_cachedBits prims s D c _ _ ρ idx _ fun hn _ => hcells.1 T hT hn).map prims s _
    · exact (frozenPure_cachedBits prims s D c _ _ ρ idx _ fun hn _ => hcells.2 j h hn).map prims s _
  | bits idx count =>
    refine (frozenPure_prssStreams prims s _ _ prss i (fun T hT => ?_) (fun j h => ?_)).map prims s _
    · exact frozenPure_cachedBits prims s D c _ _ ρ idx _ fun hn _ => hcells.1 T hT hn
    · exact frozenPure_cachedBits prims s D c _ _ ρ idx _ fun hn _ => hcells.2 j h hn

/-- A call of `Rand` and its rest, with `freezeProgram`, is the rest at the frozen output of the call. -/
theorem freezeProgram_randCall_bind (D : C.Coalition) (table : HiddenCache C) (ctx : Context C)
    (hcells : KeysCellsAt s D ctx.prss ctx.self) (call : RandCall) {β : Type}
    (body : RandOutput C E → RunM C E RealSpec β) (st : RunState C) :
    freezeProgram prims D s table ((randCall K ctx call >>= body).run st) =
      freezeProgram prims D s table ((body (frozenCall prims s K D table ctx.prss ctx.self st.label call)).run
        ⟨st.history, st.label + 1, st.tag⟩) := by
  unfold freezeProgram
  rw [RealNetworkN3.tableProgram_randCall_bind, mapProgram_bind, oracleStep,
    mapProgram_localStep_of_eq _ _ _ (frozenPure_callStreams prims s K D table ctx.prss ctx.self st.label call hcells),
    pure_bind]

end Frozen

section Bodies

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C))) (K : Constants C E)

attribute [local instance] inhabitedField

/-- `Coin` makes no local query. -/
private theorem mapProgram_coinWith (ctx : Context C) (randomness : PrssOutput C E) (count : ℕ) (st : RunState C) :
    mapProgram m ((coinWith (G := G) K ctx randomness count).run st) = (coinWith K ctx randomness count).run st := by
  simp only [coinWith, openSh, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
    mapProgram_bind, mapProgram_exchange, mapProgram_require, mapProgram_pure]

/-- `Reshare` makes no local query. -/
private theorem mapProgram_reshare {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R) (randomness : PrssOutput C R)
    (v : ℕ → R) (count : ℕ) (st : RunState C) :
    mapProgram m ((reshare (G := G) K ctx codec randomness v count).run st) =
      (reshare K ctx codec randomness v count).run st := by
  simp only [reshare, record, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_assoc,
    pure_bind, mapProgram_bind, mapProgram_exchange, mapProgram_pure]

end Bodies

section Prefetch

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives)

attribute [local instance] inhabitedField

/-- Each run of `oa` ends with a cell at `streamKey key`. -/
def Caches (key : HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) : Prop :=
  ∀ s₀, ∀ z ∈ support ((simulateQ (localAnswer prims) oa).run s₀), (z.2 (.streamKey key)).isSome

omit [Field E] [Algebra Bit E] in
theorem Caches.bind_left {key : HashOutput} {α β : Type} {oa : OracleComp (LocalSpec C) α}
    (h : Caches prims key oa) (f : α → OracleComp (LocalSpec C) β) : Caches prims key (oa >>= f) := by
  intro s₀ z hz
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨p, hp, hz⟩ := hz
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (h s₀ p hp)
  have h2 := Grows.simulateQ (grows_localAnswer prims) _ p.2 z hz hu
  simp [h2]

omit [Field E] [Algebra Bit E] in
theorem Caches.bind_right {key : HashOutput} {α β : Type} (oa : OracleComp (LocalSpec C) α)
    {f : α → OracleComp (LocalSpec C) β} (h : ∀ a, Caches prims key (f a)) : Caches prims key (oa >>= f) := by
  intro s₀ z hz
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨p, -, hz⟩ := hz
  exact h p.1 p.2 z hz

omit [Field E] [Algebra Bit E] in
theorem Caches.mapM {key : HashOutput} {γ β : Type} {f : γ → OracleComp (LocalSpec C) β} {x : γ}
    (hx : Caches prims key (f x)) : ∀ l : List γ, x ∈ l → Caches prims key (l.mapM f)
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    simp only [List.mapM_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Caches.bind_left prims hx _
    · exact Caches.bind_right prims _ fun _ => Caches.bind_left prims (Caches.mapM hx l h) _

omit [Field E] [Algebra Bit E] in
/-- A stream read of at least one position ends with the cell of its key. -/
theorem caches_prgBits (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) (hm : 0 < m) :
    Caches prims key (liftComp (prgBits name key ρ idx m) (LocalSpec C)) := by
  have hp : prgBits name key ρ idx m = (List.range m).mapM (fun position =>
      (liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, position))) : OracleComp (RoSpec C) Bit)) >>=
        fun bits => pure fun g => bits.getD g 0 := rfl
  rw [hp, liftComp_bind, liftComp_mapM_local]
  refine Caches.bind_left prims (Caches.mapM prims ?_ _ (List.mem_range.mpr hm)) _
  intro s₀ z hz
  rw [simulateQ_localAnswer_liftComp] at hz
  erw [simulateQ_query] at hz
  change z ∈ support ((prgAnswer prims (name, key, ρ, idx, 0) >>= pure).run s₀) at hz
  rw [bind_pure, RealNetworkE1o.prgAnswer_run] at hz
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  simp [hashAnswer_cached prims (q := .streamKey key) (by rintro ⟨_, h, _⟩; cases h) s₀ p hp]

omit [Field E] [Algebra Bit E] in
/-- The known streams of the bits end with the cell of each key that they read. -/
theorem keysCached_of_support (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (ρ idx count : ℕ) (hcount : 0 < count) (s₀ : HashCache C) :
    ∀ z ∈ support ((simulateQ (localAnswer prims)
      (liftComp (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C))).run s₀),
      KeysCached D receivers term pair z.2 := by
  intro z hz
  unfold knownStreams at hz
  rw [liftComp_bind] at hz
  refine ⟨fun T hT => ?_, fun j i h => ?_⟩
  · refine Caches.bind_left prims ?_ _ s₀ z hz
    rw [liftComp_mapM_local]
    refine Caches.mapM prims ?_ _ (x := T) (Finset.mem_toList.mpr (Finset.mem_univ T))
    simp only [hT, and_self, ↓reduceIte]
    exact caches_prgBits prims _ _ ρ idx count hcount
  · refine Caches.bind_right prims _ (fun _ => ?_) s₀ z hz
    rw [liftComp_bind]
    refine Caches.bind_left prims ?_ _
    rw [liftComp_mapM_local]
    refine Caches.mapM prims ?_ _ (x := j) (by simp [Committee.parties])
    rw [liftComp_mapM_local]
    refine Caches.mapM prims ?_ _ (x := i) (by simp [Committee.parties])
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact caches_prgBits prims _ _ ρ idx count hcount

variable (K : Constants C E)

/-- At the values of the prefetch at `s`, the cache `s` holds each key that the prefetch reads. -/
theorem keysCached_of_prefetchAt (D : C.Coalition) (prss : C.Party → PrssKeys C) (L count : ℕ) (s : HashCache C)
    (known : (ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) × (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (h : PrefetchAt prims K D prss L count s known) :
    KeysCached D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss) (pilotPairKey D prss) s := by
  have hmem : (known, s) ∈ support ((simulateQ (localAnswer prims) (pilotPrefetch K D prss L count)).run s) := by
    unfold PrefetchAt at h
    rw [h]
    simp
  unfold pilotPrefetch at hmem
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨p, -, q, hq, hz⟩ := hmem
  rw [show s = q.2 from congrArg Prod.snd hz]
  exact keysCached_of_support prims D _ _ _ _ 2 256 (by norm_num) p.2 q hq

/-- The known streams of one call from the cells of `s`, in the form of `runsPure_knownStreams` of
`ThresholdLeanXmssSecurity/Proof/PrssRand.lean`. `dec` reads the values from the stream bits. -/
def knownValue {R : Type} [Zero R] (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (s : HashCache C) (ρ idx count m : ℕ) (dec : (ℕ → Bit) → ℕ → R) :
    Shares C R × (C.Party → C.Party → ℕ → R) :=
  (fun T g => if g < count then (if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
      dec (prgValue prims s (term T) ρ idx m) else fun _ => 0) g else 0,
    fun j i g => if g < count then (if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
      dec (prgValue prims s (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) ρ idx m) else fun _ => 0) g else 0)

/-- The value of `elementCodec` from the stream bits. -/
def elementDec (K : Constants C E) : (ℕ → Bit) → ℕ → E := fun b g => K.encode.symm fun e => b (elementBits * g + e)

/-- The known streams of `elementCodec` from the cells of `s`. -/
theorem runsPure_knownStreams_elements (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (s : HashCache C) (hs : KeysCached D receivers term pair s) (ρ idx count : ℕ) :
    RunsPure prims s (liftComp (knownStreams D receivers (elementCodec K) term pair ρ idx count) (LocalSpec C))
      (knownValue prims D receivers term pair s ρ idx count (elementBits * count) (elementDec K)) :=
  runsPure_knownStreams (prims := prims) (s := s) D receivers (elementCodec K) term pair ρ idx count
    (fun _ key g => K.encode.symm fun b => prgValue prims s key ρ idx (elementBits * count) (elementBits * g + b))
    (fun T hT => by
      simp only [elementCodec, liftComp_bind, liftComp_pure]
      exact RunsPure.bind (runsPure_prgBits prims s _ _ ρ idx _ fun _ => hs.1 T hT) (RunsPure.pure prims s _))
    (fun j i h => by
      simp only [elementCodec, liftComp_bind, liftComp_pure]
      exact RunsPure.bind (runsPure_prgBits prims s _ _ ρ idx _ fun _ => hs.2 j i h) (RunsPure.pure prims s _))

omit [Field E] [Algebra Bit E] in
/-- The known streams of `bitCodec` from the cells of `s`. -/
theorem runsPure_knownStreams_bits (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (s : HashCache C) (hs : KeysCached D receivers term pair s) (ρ idx count : ℕ) :
    RunsPure prims s (liftComp (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C))
      (knownValue prims D receivers term pair s ρ idx count count fun b g => b g) :=
  runsPure_knownStreams (prims := prims) (s := s) D receivers (bitCodec (E := E)) term pair ρ idx count
    (fun _ key => prgValue prims s key ρ idx count)
    (fun T hT => runsPure_prgBits prims s _ _ ρ idx _ fun _ => hs.1 T hT)
    (fun j i h => runsPure_prgBits prims s _ _ ρ idx _ fun _ => hs.2 j i h)

/-- From a cache with each key that it reads, the prefetch returns the known rows of the cells. -/
theorem runsPure_pilotPrefetch (D : C.Coalition) (prss : C.Party → PrssKeys C) (L count : ℕ) (s : HashCache C)
    (hs : KeysCached D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss) (pilotPairKey D prss) s) :
    RunsPure prims s (pilotPrefetch K D prss L count)
      ((fun n => ((List.range (RealNetworkV3.checkLabels count)).map fun n =>
          knownValue prims D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss)
            (pilotPairKey D prss) s (L + n) (RealNetworkE1g.checkStream (halvings count) n) 2 (elementBits * 2)
            (elementDec K)).getD n (fun _ _ => 0, fun _ _ _ => 0)),
        knownValue prims D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss)
          (pilotPairKey D prss) s (L + (2 * halvings count + 3)) 2 256 256 fun b g => b g) := by
  unfold pilotPrefetch RealNetworkE1o.knownRowsE RealNetworkE1o.knownRowsB
  refine RunsPure.bind (RunsPure.map ?_ _) (RunsPure.bind (runsPure_knownStreams_bits prims D _ _ _ s hs _ 2 256)
    (RunsPure.pure prims s _))
  rw [← liftComp_mapM_local]
  exact RunsPure.mapM _ fun n _ => runsPure_knownStreams_elements prims K D _ _ _ s hs _ _ 2

/-- At the values of the prefetch at `s`, the known rows are the rows of the cells of `s`. -/
theorem known_of_prefetchAt (D : C.Coalition) (prss : C.Party → PrssKeys C) (L count : ℕ) (s : HashCache C)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (h : PrefetchAt prims K D prss L count s (knownE, knownB)) :
    (∀ k < RealNetworkV3.checkLabels count, knownE k =
      knownValue prims D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss)
        (pilotPairKey D prss) s (L + k) (RealNetworkE1g.checkStream (halvings count) k) 2 (elementBits * 2)
        (elementDec K)) ∧
    knownB = knownValue prims D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss)
      (pilotPairKey D prss) s (L + (2 * halvings count + 3)) 2 256 256 fun b g => b g := by
  have hr := runsPure_pilotPrefetch prims K D prss L count s (keysCached_of_prefetchAt prims K D prss L count s _ h)
  unfold PrefetchAt at h
  unfold RunsPure at hr
  rw [h] at hr
  injection hr with e
  simp only [Prod.mk.injEq] at e
  refine ⟨fun k hk => ?_, e.1.2⟩
  rw [e.1.1]
  simp [List.getD_eq_getElem?_getD, hk]

omit [Field E] [Algebra Bit E] in
/-- The output of operator `i` reads only the keys that it holds. -/
theorem keysValue_holdsDealt {R : Type} [Zero R] (val : KeyName C → HashOutput → ℕ → R) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (i : C.Party) (prss : PrssKeys C) (h : RealNetworkE1s.HoldsDealt term pair i prss) :
    keysValue val prss i = keysValue val (dealtPrssKeys term pair i) i := by
  refine Prod.ext (funext fun T => ?_) (funext fun j => ?_)
  · by_cases hT : i ∈ C.holders T
    · simp only [keysValue, hT, ↓reduceIte, h.1 T hT]
    · simp only [keysValue, hT, ↓reduceIte]
  · by_cases hj : j = i
    · simp only [keysValue, hj, ↓reduceDIte]
    · simp only [keysValue, hj, ↓reduceDIte, h.2 j hj]

omit [Field E] [Algebra Bit E] in
private theorem mem_liveSet (D : C.Coalition) (i : C.Party) (hi : i ∉ D.1) :
    i ∈ RealNetworkGP.liveSet D fun i : C.Party => some i := by
  simp [RealNetworkGP.liveSet, hi]

/-- At the values of the prefetch at `s`, each key of an honest operator under a name that the
coalition knows has a cell in `s`. -/
theorem keysCellsAt_of_prefetchAt (D : C.Coalition) (prss : C.Party → PrssKeys C) (L count : ℕ) (s : HashCache C)
    (known : (ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) × (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (h : PrefetchAt prims K D prss L count s known) (hagree : PrssKeysAgree D prss) (i : C.Party) (hi : i ∉ D.1) :
    KeysCellsAt s D (prss i) i := by
  have hc := keysCached_of_prefetchAt prims K D prss L count s _ h
  have hd := holdsDealt_pilot hagree i hi
  refine ⟨fun T hT hn => ?_, fun j hj hn => ?_⟩
  · rw [hd.1 T hT, show (dealtPrssKeys (pilotTermKey D prss) (pilotPairKey D prss) i).term T = pilotTermKey D prss T by
      simp [dealtPrssKeys, hT]]
    exact hc.1 T ⟨by simpa [Hidden] using hn, i, mem_liveSet D i hi, hi, hT⟩
  · rw [hd.2 j hj, show (dealtPrssKeys (pilotTermKey D prss) (pilotPairKey D prss) i).pair j =
      pilotPairKey D prss (C.pairOf i j (Ne.symm hj)) by simp [dealtPrssKeys, hj]]
    have hjD : j ∈ D.1 := by_contra fun hjD => hn ((hidden_pairOf D i j _).mpr ⟨hi, hjD⟩)
    exact hc.2 j i ⟨hjD, hi, mem_liveSet D i hi⟩

/-- At the values of the prefetch at `s`, a drawn output over `E` is the frozen output of operator `i`. -/
theorem drawnE_eq_frozen (D : C.Coalition) (prss : C.Party → PrssKeys C) (table : HiddenCache C) (L count : ℕ)
    (s : HashCache C) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (h : PrefetchAt prims K D prss L count s (knownE, knownB))
    (hagree : PrssKeysAgree D prss) (i : C.Party) (hi : i ∉ D.1) (k : ℕ) (hk : k < RealNetworkV3.checkLabels count) :
    RealNetworkV3.drawnE D knownE
        (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L count) k i =
      clipOutput 2 (keysValue (fun name key g => K.encode.symm fun e => cachedValue prims D table s name key (L + k)
        (RealNetworkE1g.checkStream (halvings count) k) (elementBits * 2) (elementBits * g + e)) (prss i) i) := by
  unfold RealNetworkV3.drawnE
  rw [dite_eq_left_of_eq_true (eq_true hk), (known_of_prefetchAt prims K D prss L count s knownE knownB h).1 k hk,
    keysValue_holdsDealt _ _ _ i (prss i) (holdsDealt_pilot hagree i hi)]
  refine frandShare_eq_clipOutput prims D _ (pilotTermKey D prss) (pilotPairKey D prss) table s (L + k)
    (RealNetworkE1g.checkStream (halvings count) k) 2 (elementBits * 2) (elementDec K) (fun F g hg => ?_) i hi
    (mem_liveSet D i hi)
  unfold elementDec
  congr 1
  funext e
  have hpos : elementBits * g + e.val < elementBits * 2 := by
    have := Nat.mul_le_mul_left elementBits (Nat.succ_le_of_lt hg)
    rw [Nat.mul_succ] at this
    omega
  simp only [hpos, ↓reduceIte]

/-- At the values of the prefetch at `s`, the drawn salts are the frozen output of operator `i`. -/
theorem drawnB_eq_frozen (D : C.Coalition) (prss : C.Party → PrssKeys C) (table : HiddenCache C) (L count : ℕ)
    (s : HashCache C) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (h : PrefetchAt prims K D prss L count s (knownE, knownB))
    (hagree : PrssKeysAgree D prss) (i : C.Party) (hi : i ∉ D.1) :
    frandShare D 256 knownB.1 knownB.2
        (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L count).freshB
        (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L count).freshPairB i =
      clipOutput 256 (keysValue (fun name key => cachedValue prims D table s name key
        (L + (2 * halvings count + 3)) 2 256) (prss i) i) := by
  rw [(known_of_prefetchAt prims K D prss L count s knownE knownB h).2,
    keysValue_holdsDealt _ _ _ i (prss i) (holdsDealt_pilot hagree i hi)]
  exact frandShare_eq_clipOutput prims D _ (pilotTermKey D prss) (pilotPairKey D prss) table s
    (L + (2 * halvings count + 3)) 2 256 256 (fun b g => b g) (fun F g hg => by simp only [hg, ↓reduceIte]) i hi
    (mem_liveSet D i hi)

end Prefetch

section Row

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

omit [Field E] [Algebra Bit E] in
/-- A PRSS output at its first `count` positions keeps them. -/
private theorem clipOutput_clipOutput {R : Type} [Zero R] (count : ℕ) (o : PrssOutput C R) :
    clipOutput count (clipOutput count o) = clipOutput count o := by
  refine Prod.ext (funext fun T => funext fun g => ?_) (funext fun j => funext fun g => ?_) <;>
    by_cases hg : g < count <;> simp [clipOutput, hg]

/-- The coin of the real check is the `Rand` call `.elements 1 count` and then `Coin`. -/
theorem coin_randCall {ι : Type} {G : OracleSpec ι} (ctx : Context C) (count : ℕ) :
    (realCheckBuildingBlocks (G := G) K ctx).coin count =
      randCall K ctx (.elements 1 count) >>= fun o => match o with
        | .inl randomness => coinWith K ctx randomness count
        | .inr _ => StateT.lift failure := by
  simp only [realCheckBuildingBlocks, randCall, bind_assoc, pure_bind, RealNetworkN3.coinWith_clipOutput]

/-- The draw over `E` of the real check, at its first `count` positions, is the `Rand` call
`.elements 1 count`. -/
theorem clipRun_randElements {ι : Type} {G : OracleSpec ι} (ctx : Context C) (count : ℕ) (st : RunState C) :
    clipRun count <$> ((realCheckBuildingBlocks (G := G) K ctx).randElements count).run st =
      (randCall K ctx (.elements 1 count) >>= fun o => match o with
        | .inl randomness => pure randomness
        | .inr _ => StateT.lift failure).run st := by
  simp [realCheckBuildingBlocks, randCall, StateT.run_bind, map_eq_bind_pure_comp]
  rfl

/-- The draw of bits of the real check, at its first `count` positions, is the `Rand` call
`.bits 2 count`. -/
theorem clipRun_randBits {ι : Type} {G : OracleSpec ι} (ctx : Context C) (count : ℕ) (st : RunState C) :
    clipRun count <$> ((realCheckBuildingBlocks (G := G) K ctx).randBits count).run st =
      (randCall K ctx (.bits 2 count) >>= fun o => match o with
        | .inr randomness => pure randomness
        | .inl _ => StateT.lift failure).run st := by
  simp [realCheckBuildingBlocks, randCall, StateT.run_bind, map_eq_bind_pure_comp]
  rfl

/-- `Coin` reads only the operator of its context. -/
theorem coinWith_context {ι : Type} {G : OracleSpec ι} (ctx : Context C) (randomness : PrssOutput C E) (count : ℕ) :
    coinWith (G := G) K ctx randomness count = coinWith K (localContext ctx.self) randomness count := by
  obtain ⟨self, keys, prss⟩ := ctx
  rfl

omit [Field E] [Algebra Bit E] in
private theorem freezeProgram_pure (D : C.Coalition) (s : HashCache C) (table : HiddenCache C) {α : Type} (a : α) :
    freezeProgram prims D s table (pure a : PartyM C E RealSpec α) = pure a := by
  unfold freezeProgram
  rw [tableProgram_eq_mapProgram, mapProgram_pure, mapProgram_pure]

theorem freezeProgram_coinWith (D : C.Coalition) (s : HashCache C) (table : HiddenCache C) (ctx : Context C)
    (randomness : PrssOutput C E) (count : ℕ) (st : RunState C) :
    freezeProgram prims D s table ((coinWith K ctx randomness count).run st) = (coinWith K ctx randomness count).run st := by
  unfold freezeProgram
  rw [tableProgram_eq_mapProgram, mapProgram_coinWith, mapProgram_coinWith]

theorem freezeProgram_reshare {R : Type} [Field R] (D : C.Coalition) (s : HashCache C) (table : HiddenCache C)
    (ctx : Context C) (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) (st : RunState C) :
    freezeProgram prims D s table ((reshare K ctx codec randomness v count).run st) =
      (reshare K ctx codec randomness v count).run st := by
  unfold freezeProgram
  rw [tableProgram_eq_mapProgram, mapProgram_reshare, mapProgram_reshare]

/-- `RowJ8` holds. -/
theorem rowJ8 (D : C.Coalition) : RowJ8 prims K D := by
  intro keys prss table L count s knownE knownB i hcount hi hagree h
  have hcells := keysCellsAt_of_prefetchAt prims K D prss L count s _ h hagree i hi
  refine ⟨fun st hL hlt hstream => ?_, fun st products hlen hL hlt hstream => ?_,
    fun st hL hlt hstream => ?_, fun st hst => ?_⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL
    change freezeProgram prims D s table (((realCheckBuildingBlocks K (pilotContext keys prss i)).coin 2).run st) = _
    rw [coin_randCall, freezeProgram_randCall_bind prims s K D table _ hcells]
    simp only [frozenCall]
    rw [freezeProgram_coinWith, coinWith_context]
    have hk' : st.label - L = k := by omega
    rw [hk'] at hstream hlt
    have e := drawnE_eq_frozen prims K D prss table L count s knownE knownB h hagree i hi k hlt
    rw [hstream] at e
    simp only [RealNetworkV3.drawnCheckBuildingBlocks, freshLabel, StateT.run_bind, StateT.run_modifyGet,
      pure_bind, hk, Nat.add_sub_cancel_left, e]
    rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL
    change freezeProgram prims D s table
      (((realCheckBuildingBlocks K (pilotContext keys prss i)).extendMult products).run st) = _
    rw [RealNetworkN3.extendMult_randCall, freezeProgram_randCall_bind prims s K D table _ hcells]
    simp only [frozenCall]
    rw [freezeProgram_reshare]
    have hk' : st.label - L = k := by omega
    rw [hk'] at hstream hlt
    have e := drawnE_eq_frozen prims K D prss table L count s knownE knownB h hagree i hi k hlt
    rw [hstream] at e
    simp only [RealNetworkV3.drawnCheckBuildingBlocks, freshLabel, StateT.run_bind, StateT.run_modifyGet,
      pure_bind, hk, Nat.add_sub_cancel_left, e, hlen]
    rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL
    change clipRun 2 <$> freezeProgram prims D s table
      (((realCheckBuildingBlocks K (pilotContext keys prss i)).randElements 2).run st) = _
    rw [← freezeProgram_map, clipRun_randElements, freezeProgram_randCall_bind prims s K D table _ hcells]
    simp only [frozenCall, StateT.run_pure]
    rw [freezeProgram_pure]
    have hk' : st.label - L = k := by omega
    rw [hk'] at hstream hlt
    have e := drawnE_eq_frozen prims K D prss table L count s knownE knownB h hagree i hi k hlt
    rw [hstream] at e
    simp only [RealNetworkV3.drawnCheckBuildingBlocks, freshLabel, StateT.run_bind, StateT.run_modifyGet,
      pure_bind, StateT.run_pure, map_pure, clipRun, hk, Nat.add_sub_cancel_left, e, clipOutput_clipOutput]
    rfl
  · change clipRun 256 <$> freezeProgram prims D s table
      (((realCheckBuildingBlocks K (pilotContext keys prss i)).randBits 256).run st) = _
    rw [← freezeProgram_map, clipRun_randBits, freezeProgram_randCall_bind prims s K D table _ hcells]
    simp only [frozenCall, StateT.run_pure]
    rw [freezeProgram_pure]
    have e := drawnB_eq_frozen prims K D prss table L count s knownE knownB h hagree i hi
    simp only [RealNetworkV3.drawnCheckBuildingBlocks, freshLabel, StateT.run_bind, StateT.run_modifyGet,
      pure_bind, StateT.run_pure, map_pure, clipRun, hst, e, clipOutput_clipOutput]
    rfl

end Row

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## A map of the local queries in a run -/

section Map

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}
  (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)))

/-- The map `m` answers each query of `H` with the same query. -/
def FixesHash : Prop :=
  ∀ q : Query C, m (.inr (.inl q)) = (query (spec := LocalSpec C) (.inr (.inl q)) : OracleComp (LocalSpec C) _)

/-- The map `m` does not change the computation `oa` of `H` and `PRG`. -/
def FixesComp {α : Type} (oa : OracleComp (RoSpec C) α) : Prop :=
  simulateQ m (liftComp oa (LocalSpec C)) = liftComp oa (LocalSpec C)

theorem fixesComp_pure {α : Type} (a : α) : FixesComp m (pure a : OracleComp (RoSpec C) α) := by
  simp [FixesComp]

theorem fixesComp_bind {α β : Type} {oa : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    (h : FixesComp m oa) (hf : ∀ a, FixesComp m (f a)) : FixesComp m (oa >>= f) := by
  unfold FixesComp at *
  rw [liftComp_bind, simulateQ_bind, h]
  simp only [hf]

theorem fixesComp_map {α β : Type} {oa : OracleComp (RoSpec C) α} (f : α → β) (h : FixesComp m oa) :
    FixesComp m (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact fixesComp_bind m h fun a => fixesComp_pure m _

theorem fixesComp_hashQuery (hm : FixesHash m) (q : Query C) : FixesComp m (hashQuery q) := by
  unfold FixesComp
  have e : liftComp (hashQuery q) (LocalSpec C) =
      (liftM ((LocalSpec C).query (.inr (.inl q))) : OracleComp (LocalSpec C) _) := rfl
  rw [e, simulateQ_query]
  simpa using hm q

theorem fixesComp_mapM {γ β : Type} {f : γ → OracleComp (RoSpec C) β} (hf : ∀ c, FixesComp m (f c)) :
    ∀ l : List γ, FixesComp m (l.mapM f)
  | [] => fixesComp_pure m _
  | c :: l => by
    rw [List.mapM_cons]
    exact fixesComp_bind m (hf c) fun b => fixesComp_bind m (fixesComp_mapM hf l) fun _ => fixesComp_pure m _

/-- The map on the local queries of a program lifted from the local oracles. It is
`partyTable_liftComp` for each map. -/
theorem partyMap_liftComp_local {β : Type} (oa : OracleComp (LocalSpec C) β) :
    simulateQ (partyMap (E := E) (G := G) m) (liftComp oa (PartySpec C E G)) =
      liftComp (simulateQ m oa) (PartySpec C E G) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure]
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k : OracleComp (LocalSpec C) _) (PartySpec C E G) =
        (liftM ((PartySpec C E G).query (.inl (.inl t))) : OracleComp (PartySpec C E G) _) >>=
          fun u => liftComp (k u) _ := by
      rw [liftComp_bind]
      rcases t with n | x | x <;> rfl
    rw [e, simulateQ_bind, simulateQ_bind, liftComp_bind]
    simp only [ih, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rfl

theorem mapProgram_eq_pure {α : Type} (a : α) : mapProgram m (pure a : PartyM C E G α) = pure a := by
  unfold mapProgram
  apply OptionT.ext
  simp

theorem mapProgram_eq_failure {α : Type} : mapProgram m (failure : PartyM C E G α) = failure := by
  unfold mapProgram
  apply OptionT.ext
  simp

theorem mapProgram_eq_exchange (out : Mail C E) :
    mapProgram m (exchange out : PartyM C E G (Mail C E)) = exchange out := by
  unfold mapProgram exchange
  apply OptionT.ext
  simp [OptionT.run_bind, OptionT.lift, partyMap, Option.elimM]
  congr 1
  funext x
  split_ifs <;> simp

theorem mapProgram_eq_require (p : Prop) : mapProgram m (require p : PartyM C E G Unit) = require p := by
  unfold require
  split_ifs
  · exact mapProgram_eq_pure m ()
  · exact mapProgram_eq_failure m

theorem mapProgram_oracleStep {α : Type} {oa : OracleComp (RoSpec C) α} (h : FixesComp m oa) :
    mapProgram m (oracleStep oa : PartyM C E G α) = oracleStep oa := by
  unfold mapProgram oracleStep localStep
  apply OptionT.ext
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure, partyMap_liftComp_local]
  erw [h]

/-- The run `p` with the map `m` on the local queries of each of its programs. -/
def mapRun {α : Type} (p : RunM C E G α) : RunM C E G α :=
  StateT.mk fun st => mapProgram m (p.run st)

theorem mapRun_bind {α β : Type} (p : RunM C E G α) (f : α → RunM C E G β) :
    mapRun m (p >>= f) = mapRun m p >>= fun a => mapRun m (f a) := by
  apply StateT.ext
  intro st
  simp only [mapRun, StateT.run_bind]
  exact mapProgram_bind m _ _

theorem mapRun_pure {α : Type} (a : α) : mapRun m (pure a : RunM C E G α) = pure a := by
  apply StateT.ext
  intro st
  exact mapProgram_eq_pure m _

theorem mapRun_lift {α : Type} (x : PartyM C E G α) :
    mapRun m (StateT.lift x : RunM C E G α) = StateT.lift (mapProgram m x) := by
  apply StateT.ext
  intro st
  show mapProgram m (x >>= fun a => pure (a, st)) = _
  rw [mapProgram_bind]
  simp only [mapProgram_eq_pure]
  rfl

theorem mapRun_get : mapRun m (get : RunM C E G (RunState C)) = get := by
  apply StateT.ext
  intro st
  exact mapProgram_eq_pure m _

theorem mapRun_foldlM {β γ : Type} (f f' : β → γ → RunM C E G β) (hf : ∀ b c, mapRun m (f b c) = f' b c) :
    ∀ (l : List γ) (init : β), mapRun m (l.foldlM f init) = l.foldlM f' init
  | [], init => mapRun_pure m init
  | c :: l, init => by
    rw [List.foldlM_cons, List.foldlM_cons, mapRun_bind, hf]
    exact bind_congr fun b => mapRun_foldlM f f' hf l b

end Map

/-! ## The check with a map of its local queries -/

section MapCheck

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C))) (K : Constants C E) (ctx : Context C)

attribute [local instance] inhabitedField

/-- The building blocks `B` with `mapRun m` on each call. -/
def mapBlocks (B : CheckBuildingBlocks C E G) : CheckBuildingBlocks C E G where
  coin n := mapRun m (B.coin n)
  extendMult products := mapRun m (B.extendMult products)
  randElements n := mapRun m (B.randElements n)
  randBits n := mapRun m (B.randBits n)

theorem fixesComp_findChallenge (hm : FixesHash m) (key : HashOutput) :
    ∀ (tries index : ℕ), FixesComp m (findChallenge K key tries index)
  | 0, index => fixesComp_pure m _
  | tries + 1, index => by
    rw [findChallenge]
    refine fixesComp_bind m (fixesComp_hashQuery m hm _) fun h => ?_
    dsimp only
    generalize Classical.propDecidable _ = d
    rcases d with ⟨_ | _, _⟩
    · exact fixesComp_findChallenge hm key tries (index + 1)
    · exact fixesComp_pure m _

theorem mapProgram_openSh (v : ℕ → E) (count : ℕ) :
    mapProgram m (openSh (G := G) K ctx v count) = openSh K ctx v count := by
  unfold openSh
  simp only [mapProgram_bind, mapProgram_eq_exchange, mapProgram_eq_require, mapProgram_eq_pure]

theorem mapRun_coinKey (hm : FixesHash m) (B : CheckBuildingBlocks C E G) :
    mapRun m (coinKey K B) = coinKey K (mapBlocks m B) := by
  unfold coinKey
  simp only [mapRun_bind, mapRun_get, mapRun_lift, mapProgram_oracleStep m (fixesComp_hashQuery m hm _)]
  rfl

theorem mapRun_expand (hm : FixesHash m) (key : HashOutput) (count : ℕ) :
    mapRun m (expand (G := G) K key count) = expand K key count := by
  unfold expand
  rw [mapRun_lift, mapProgram_oracleStep m
    (fixesComp_mapM m (fun k => fixesComp_map m _ (fixesComp_hashQuery m hm _)) _)]

theorem mapRun_challenge (hm : FixesHash m) (B : CheckBuildingBlocks C E G) :
    mapRun m (challenge K B) = challenge K (mapBlocks m B) := by
  unfold challenge
  rw [mapRun_bind, mapRun_coinKey m K hm]
  refine bind_congr fun key => ?_
  rw [mapRun_bind, mapRun_lift, mapProgram_oracleStep m (fixesComp_findChallenge m K hm key _ _)]
  refine bind_congr fun o => ?_
  cases o
  · simp only [mapRun_lift, mapProgram_eq_failure]
  · simp only [mapRun_pure]

omit [Field E] [Algebra Bit E] in
theorem mapRun_compareDigests (hm : FixesHash m) (salts : Shares C Bit) :
    mapRun m (compareDigests (E := E) (G := G) ctx salts) = compareDigests ctx salts := by
  unfold compareDigests
  simp only [mapRun_bind, mapRun_get, mapRun_lift, mapProgram_eq_exchange, mapProgram_eq_require]
  refine bind_congr fun st => ?_
  rw [mapProgram_oracleStep m (fixesComp_mapM m (fun T => ?_) _)]
  split_ifs
  · exact fixesComp_bind m (fixesComp_hashQuery m hm _) fun _ => fixesComp_hashQuery m hm _
  · exact fixesComp_pure m _

theorem mapRun_sliceStep (hm : FixesHash m) (B : CheckBuildingBlocks C E G) (τ : List E) (count : ℕ)
    (x : Shares C E × Shares C E × E) (j : ℕ) :
    mapRun m (sliceStep K ctx B τ count x j) = sliceStep K ctx (mapBlocks m B) τ count x j := by
  obtain ⟨xs, ys, D⟩ := x
  simp only [sliceStep, mapRun_bind, mapRun_challenge m K hm, mapRun_pure]
  rfl

theorem mapRun_halvingStep (hm : FixesHash m) (B : CheckBuildingBlocks C E G) (width : ℕ)
    (x : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    mapRun m (halvingStep K ctx B width x j) = halvingStep K ctx (mapBlocks m B) width x j := by
  obtain ⟨A, B', D⟩ := x
  simp only [halvingStep, mapRun_bind, mapRun_challenge m K hm, mapRun_pure]
  rfl

theorem mapRun_finalStep (hm : FixesHash m) (B : CheckBuildingBlocks C E G) (x : (ℕ → E) × (ℕ → E) × E) :
    mapRun m (finalStep K ctx B x) = finalStep K ctx (mapBlocks m B) x := by
  obtain ⟨A, B', D⟩ := x
  simp only [finalStep, mapRun_bind, mapRun_challenge m K hm, mapRun_compareDigests m ctx hm, mapRun_lift,
    mapProgram_openSh, mapProgram_eq_require]
  rfl

/-- The check with `mapRun m` is the check on the building blocks with `mapRun m`. -/
theorem mapRun_check (hm : FixesHash m) (B : CheckBuildingBlocks C E G) (tuples : List (Tuple C)) :
    mapRun m (check K ctx B tuples) = check K ctx (mapBlocks m B) tuples := by
  by_cases h : (tuples.map (·.count)).sum = 0
  · simp only [check, h, ↓reduceIte]
    exact mapRun_pure m ()
  rw [check_eq K ctx B tuples h, check_eq K ctx _ tuples h]
  simp only [mapRun_bind, mapRun_coinKey m K hm, mapRun_expand m K hm, mapRun_lift, mapProgram_eq_require,
    mapRun_foldlM m _ _ (mapRun_sliceStep m K ctx hm B _ _), mapRun_foldlM m _ _ (mapRun_halvingStep m K ctx hm B _),
    mapRun_finalStep m K ctx hm]

end MapCheck

/-! ## The moves of the state in a run -/

section Moves

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- Each continuation of a run of `p` from the state `st` sees a state `s` with `R st s`. Two
continuations that agree on these states give the same run. -/
def Moves (R : RunState C → RunState C → Prop) {α : Type} (p : RunM C E G α) : Prop :=
  ∀ (st : RunState C) {β : Type} (f g : α × RunState C → PartyM C E G β),
    (∀ a s, R st s → f (a, s) = g (a, s)) → p.run st >>= f = p.run st >>= g

/-- The label of the state `s'` is the label of `s` plus `n`. -/
def LabelAdds (n : ℕ) (s s' : RunState C) : Prop := s'.label = s.label + n

theorem moves_pure {R : RunState C → RunState C → Prop} (hR : ∀ s, R s s) {α : Type} (a : α) :
    Moves R (pure a : RunM C E G α) := by
  intro st β f g h
  simp only [StateT.run_pure, pure_bind]
  exact h a st (hR st)

theorem moves_lift {R : RunState C → RunState C → Prop} (hR : ∀ s, R s s) {α : Type} (x : PartyM C E G α) :
    Moves R (StateT.lift x : RunM C E G α) := by
  intro st β f g h
  simp only [StateT.run_lift, bind_assoc, pure_bind]
  exact bind_congr fun a => h a st (hR st)

theorem moves_get {R : RunState C → RunState C → Prop} (hR : ∀ s, R s s) :
    Moves R (get : RunM C E G (RunState C)) := by
  intro st β f g h
  simp only [StateT.run_get, pure_bind]
  exact h st st (hR st)

theorem moves_modifyGet {R : RunState C → RunState C → Prop} {α : Type} (u : RunState C → α × RunState C)
    (hR : ∀ s, R s (u s).2) : Moves R (modifyGet u : RunM C E G α) := by
  intro st β f g h
  simp only [StateT.run_modifyGet, pure_bind]
  exact h _ _ (hR st)

theorem moves_modify {R : RunState C → RunState C → Prop} (u : RunState C → RunState C) (hR : ∀ s, R s (u s)) :
    Moves R (modify u : RunM C E G PUnit) := by
  intro st β f g h
  simp only [StateT.run_modify, pure_bind]
  exact h _ _ (hR st)

theorem moves_bind {R₁ R₂ R₃ : RunState C → RunState C → Prop} {α β : Type} {p : RunM C E G α}
    {q : α → RunM C E G β} (hp : Moves R₁ p) (hq : ∀ a, Moves R₂ (q a))
    (hR : ∀ s₁ s₂ s₃, R₁ s₁ s₂ → R₂ s₂ s₃ → R₃ s₁ s₃) : Moves R₃ (p >>= q) := by
  intro st γ f g h
  simp only [StateT.run_bind, bind_assoc]
  exact hp st _ _ fun a s hs => hq a s f g fun b s' hs' => h b s' (hR _ _ _ hs hs')

theorem moves_label_bind {a b c : ℕ} {α β : Type} {p : RunM C E G α} {q : α → RunM C E G β}
    (hp : Moves (LabelAdds a) p) (hq : ∀ x, Moves (LabelAdds b) (q x)) (h : a + b = c) :
    Moves (LabelAdds c) (p >>= q) :=
  moves_bind hp hq fun s₁ s₂ s₃ h₁ h₂ => by unfold LabelAdds at *; omega

theorem labelAdds_zero (s : RunState C) : LabelAdds 0 s s := rfl

end Moves

/-! ## The frozen programs of a check -/

section RowJ7

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

omit [Field E] [Algebra Bit E] in
theorem fixesHash_freezeLocal (s : HashCache C) : FixesHash (freezeLocal prims s) := fun _ => rfl

theorem fixesHash_tableLocal (D : C.Coalition) (table : HiddenCache C) :
    FixesHash (RealNetworkN3.tableLocal D table) := fun _ => rfl

/-- `RowJ7` holds. `freezeProgram` is the map `freezeLocal` after the map `tableLocal`, and both maps
answer each query of `H` with the same query. -/
theorem rowJ7 (D : C.Coalition) : RowJ7 prims K D := by
  intro s table ctx B tuples rs
  have h := congrArg (fun p => StateT.run p rs)
    ((congrArg (mapRun (freezeLocal prims s)) (mapRun_check _ K ctx (fixesHash_tableLocal D table) B tuples)).trans
      (mapRun_check _ K ctx (fixesHash_freezeLocal prims s) _ tuples))
  exact h

end RowJ7

/-! ## The label range of the check -/

section Range

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι} (K : Constants C E)
  (ctx : Context C) (L : ℕ) (B B' : CheckBuildingBlocks C E G)

attribute [local instance] inhabitedField

/-- Each call of a building block of `B'` adds one to the label on each path. -/
structure OneLabelBlocks (B' : CheckBuildingBlocks C E G) : Prop where
  coin : ∀ n, Moves (LabelAdds 1) (B'.coin n)
  extendMult : ∀ products, Moves (LabelAdds 1) (B'.extendMult products)
  randElements : ∀ n, Moves (LabelAdds 1) (B'.randElements n)
  randBits : ∀ n, Moves (LabelAdds 1) (B'.randBits n)

/-- The part `P` of a check runs the same on `B` and on `B'` from each state with the label `L + k`,
and on `B'` it adds `n` to the label. -/
def AgreeFrom (k n : ℕ) {α : Type} (P : CheckBuildingBlocks C E G → RunM C E G α) : Prop :=
  (∀ st : RunState C, st.label = L + k → (P B).run st = (P B').run st) ∧ Moves (LabelAdds n) (P B')

variable {L B B'}

omit [Field E] [Algebra Bit E] in
theorem agree_bind {k n k' n' n'' : ℕ} {α β : Type} {P : CheckBuildingBlocks C E G → RunM C E G α}
    {Q : α → CheckBuildingBlocks C E G → RunM C E G β} (hP : AgreeFrom L B B' k n P)
    (hQ : ∀ a, AgreeFrom L B B' k' n' (Q a)) (hk : k + n = k') (hn : n + n' = n'') :
    AgreeFrom L B B' k n'' (fun bb => P bb >>= fun a => Q a bb) := by
  refine ⟨fun st hst => ?_, moves_label_bind hP.2 (fun a => (hQ a).2) hn⟩
  simp only [StateT.run_bind]
  rw [hP.1 st hst]
  exact hP.2 st _ _ fun a s hs => (hQ a).1 s (by unfold LabelAdds at hs; omega)

omit [Field E] [Algebra Bit E] in
theorem agree_const {k n : ℕ} {α : Type} (p : RunM C E G α) (hp : Moves (LabelAdds n) p) :
    AgreeFrom L B B' k n (fun _ => p) :=
  ⟨fun _ _ => rfl, hp⟩

omit [Field E] [Algebra Bit E] in
theorem agree_clip_bind {R : Type} [Zero R] {k n c : ℕ} {β : Type}
    (P : CheckBuildingBlocks C E G → RunM C E G (PrssOutput C R))
    {Q : PrssOutput C R → CheckBuildingBlocks C E G → RunM C E G β}
    (hP : ∀ st : RunState C, st.label = L + k → clipRun c <$> (P B).run st = clipRun c <$> (P B').run st)
    (hP' : Moves (LabelAdds 1) (P B')) (hQ : ∀ o, AgreeFrom L B B' (k + 1) n (Q o))
    (hclip : ∀ o bb, Q (clipOutput c o) bb = Q o bb) :
    AgreeFrom L B B' k (1 + n) (fun bb => P bb >>= fun o => Q o bb) := by
  refine ⟨fun st hst => ?_, moves_label_bind hP' (fun a => (hQ a).2) rfl⟩
  have e : ∀ bb, (P bb).run st >>= (fun x => (Q x.1 B).run x.2) =
      (clipRun c <$> (P bb).run st) >>= fun x => (Q x.1 B).run x.2 := by
    intro bb
    rw [bind_map_left]
    exact bind_congr fun x => by simp only [clipRun, hclip]
  simp only [StateT.run_bind]
  rw [e B, hP st hst, ← e B']
  exact hP' st _ _ fun a s hs => (hQ a).1 s (by unfold LabelAdds at hs; omega)

end Range

section Pieces

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι} (K : Constants C E)
  (ctx : Context C) {L count : ℕ} {B B' : CheckBuildingBlocks C E G}

attribute [local instance] inhabitedField

omit [Algebra Bit E] in
theorem agree_coin (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') {k : ℕ}
    (hk : k < RealNetworkV3.checkLabels count) (hs : RealNetworkE1g.checkStream (halvings count) k = 1) :
    AgreeFrom L B B' k 1 (fun bb => bb.coin 2) :=
  ⟨fun st hst => hB.coin st (by omega) (by omega) (by rw [hst, Nat.add_sub_cancel_left]; exact hs), h1.coin 2⟩

omit [Algebra Bit E] in
theorem agree_extendMult (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') {k : ℕ}
    (products : List (Product C E)) (hlen : products.length = 2)
    (hk : k < RealNetworkV3.checkLabels count) (hs : RealNetworkE1g.checkStream (halvings count) k = 0) :
    AgreeFrom L B B' k 1 (fun bb => bb.extendMult products) :=
  ⟨fun st hst => hB.extendMult st products hlen (by omega) (by omega)
    (by rw [hst, Nat.add_sub_cancel_left]; exact hs), h1.extendMult products⟩

theorem agree_coinKey (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') {k : ℕ}
    (hk : k < RealNetworkV3.checkLabels count) (hs : RealNetworkE1g.checkStream (halvings count) k = 1) :
    AgreeFrom L B B' k 1 (fun bb => coinKey K bb) := by
  unfold coinKey
  refine agree_bind (k' := k) (n' := 1) (agree_const _ (moves_get labelAdds_zero)) (fun state => ?_) (by omega) (by omega)
  exact agree_bind (k' := k + 1) (n' := 0) (agree_coin hB h1 hk hs) (fun _ => agree_const _ (moves_lift labelAdds_zero _)) (by omega) (by omega)

theorem agree_challenge (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') {k : ℕ}
    (hk : k < RealNetworkV3.checkLabels count) (hs : RealNetworkE1g.checkStream (halvings count) k = 1) :
    AgreeFrom L B B' k 1 (fun bb => challenge K bb) := by
  unfold challenge
  refine agree_bind (k' := k + 1) (n' := 0) (agree_coinKey K hB h1 hk hs) (fun key => ?_) (by omega) (by omega)
  refine agree_bind (k' := k + 1) (n' := 0) (agree_const _ (moves_lift labelAdds_zero _)) (fun o => agree_const _ ?_) (by omega) (by omega)
  cases o
  · exact moves_lift labelAdds_zero _
  · exact moves_pure labelAdds_zero _

theorem checkLabels_eq (n : ℕ) : RealNetworkV3.checkLabels n = 2 * halvings n + 5 := rfl

theorem checkStream_odd {R j : ℕ} (hj : j < R) : RealNetworkE1g.checkStream R (1 + 2 * j) = 0 := by
  unfold RealNetworkE1g.checkStream
  split_ifs <;> omega

theorem checkStream_even {R j : ℕ} (hj : j < R) : RealNetworkE1g.checkStream R (2 + 2 * j) = 1 := by
  unfold RealNetworkE1g.checkStream
  split_ifs <;> omega

theorem agree_sliceStep (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') (τ : List E) (c : ℕ)
    (x : Shares C E × Shares C E × E) {j : ℕ} (hj : j < halvings count) :
    AgreeFrom L B B' (1 + 2 * j) 2 (fun bb => sliceStep K ctx bb τ c x j) := by
  obtain ⟨xs, ys, D⟩ := x
  unfold sliceStep
  refine agree_bind (k' := 2 + 2 * j) (n' := 1) (agree_extendMult hB h1 _ rfl
    (by rw [checkLabels_eq]; omega) (checkStream_odd hj)) (fun t => ?_) (by omega) (by omega)
  exact agree_bind (k' := 2 + 2 * j + 1) (n' := 0) (agree_challenge K hB h1
    (by rw [checkLabels_eq]; omega) (checkStream_even hj)) (fun r => agree_const _ (moves_pure labelAdds_zero _))
    (by omega) (by omega)

theorem agree_halvingStep (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') (width : ℕ)
    (x : (ℕ → E) × (ℕ → E) × E) (j : ℕ) {i : ℕ} (hi : i < halvings count) :
    AgreeFrom L B B' (1 + 2 * i) 2 (fun bb => halvingStep K ctx bb width x j) := by
  obtain ⟨A, B0, D⟩ := x
  unfold halvingStep
  refine agree_bind (k' := 2 + 2 * i) (n' := 1) (agree_extendMult hB h1 _ rfl
    (by rw [checkLabels_eq]; omega) (checkStream_odd hi)) (fun t => ?_) (by omega) (by omega)
  exact agree_bind (k' := 2 + 2 * i + 1) (n' := 0) (agree_challenge K hB h1
    (by rw [checkLabels_eq]; omega) (checkStream_even hi)) (fun r => agree_const _ (moves_pure labelAdds_zero _))
    (by omega) (by omega)

omit [Field E] [Algebra Bit E] in
/-- A loop over `List.range` whose step `j` takes two labels from the offset `start + 2 * j`. -/
theorem agree_foldlM_range {β : Type} (f : CheckBuildingBlocks C E G → β → ℕ → RunM C E G β) (start N : ℕ)
    (hf : ∀ j < N, ∀ b, AgreeFrom L B B' (start + 2 * j) 2 (fun bb => f bb b j)) :
    ∀ n ≤ N, ∀ init, AgreeFrom L B B' start (2 * n) (fun bb => (List.range n).foldlM (f bb) init)
  | 0, _, init => by
    simp only [List.range_zero, List.foldlM_nil]
    exact agree_const _ (moves_pure labelAdds_zero _)
  | n + 1, hn, init => by
    simp only [List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_pure]
    exact agree_bind (k' := start + 2 * n) (n' := 2) (agree_foldlM_range f start N hf n (by omega) init)
      (fun b => hf n (by omega) b) (by omega) (by omega)

omit [Field E] [Algebra Bit E] in
theorem moves_compareDigests (salts : Shares C Bit) :
    Moves (LabelAdds 0) (compareDigests (E := E) (G := G) ctx salts) := by
  unfold compareDigests
  exact moves_label_bind (moves_get labelAdds_zero) (fun _ => moves_label_bind (moves_lift labelAdds_zero _)
    (fun _ => moves_label_bind (moves_lift labelAdds_zero _) (fun _ => moves_lift labelAdds_zero _) rfl) rfl) rfl

theorem conv_clipOutput (o : PrssOutput C E) {n g : ℕ} (hg : g < n) :
    conv K ctx (clipOutput n o).1 g = conv K ctx o.1 g := by
  simp only [conv, clipOutput, hg, ↓reduceIte]

omit [Field E] [Algebra Bit E] in
theorem compareDigests_clipOutput (o : PrssOutput C Bit) :
    compareDigests (E := E) (G := G) ctx (clipOutput 256 o).1 = compareDigests ctx o.1 := by
  have h : ∀ T, vector 256 ((clipOutput 256 o).1 T) = vector 256 (o.1 T) := fun T =>
    List.map_congr_left fun g hg => by simp [clipOutput, List.mem_range.1 hg]
  simp only [compareDigests, h]

theorem agree_finalStep (hB : BlocksAgree L count B B') (h1 : OneLabelBlocks B') (x : (ℕ → E) × (ℕ → E) × E) :
    AgreeFrom L B B' (1 + 2 * halvings count) 4 (fun bb => finalStep K ctx bb x) := by
  obtain ⟨A, B0, D⟩ := x
  unfold finalStep
  refine agree_clip_bind (c := 2) (n := 3) (fun bb => bb.randElements 2)
    (fun st hst => hB.randElements st (by omega) (by rw [checkLabels_eq]; omega)
      (by rw [hst, Nat.add_sub_cancel_left]; unfold RealNetworkE1g.checkStream; split_ifs <;> omega))
    (h1.randElements 2) (fun w => ?_) (fun w bb => ?_)
  · refine agree_bind (k' := 1 + 2 * halvings count + 1 + 1) (n' := 2) (agree_extendMult hB h1 _ rfl
      (by rw [checkLabels_eq]; omega) (by unfold RealNetworkE1g.checkStream; split_ifs <;> omega))
      (fun q => ?_) (by omega) (by omega)
    refine agree_clip_bind (c := 256) (n := 1) (fun bb => bb.randBits 256)
      (fun st hst => hB.randBits st (by omega)) (h1.randBits 256) (fun salts => ?_) (fun salts bb => ?_)
    · refine agree_bind (k' := 1 + 2 * halvings count + 1 + 1 + 1) (n' := 1)
        (agree_const _ (moves_compareDigests ctx _)) (fun _ => ?_) (by omega) (by omega)
      exact agree_bind (k' := 1 + 2 * halvings count + 1 + 1 + 1 + 1) (n' := 0) (agree_challenge K hB h1
        (by rw [checkLabels_eq]; omega) (by unfold RealNetworkE1g.checkStream; split_ifs <;> omega))
        (fun r => agree_const _ (moves_label_bind (moves_lift labelAdds_zero _)
          (fun _ => moves_lift labelAdds_zero _) rfl)) (by omega) (by omega)
    · simp only [compareDigests_clipOutput]
  · simp only [conv_clipOutput K ctx w (show 0 < 2 by norm_num), conv_clipOutput K ctx w (show 1 < 2 by norm_num)]

/-- A check of a nonzero count from the label `L` runs the same on `B` and on `B'`, when the blocks
agree at the calls of the check and each block of `B'` takes one label. -/
theorem agree_check (tuples : List (Tuple C)) (hB : BlocksAgree L (tuples.map (·.count)).sum B B')
    (h1 : OneLabelBlocks B') (h : (tuples.map (·.count)).sum ≠ 0) :
    AgreeFrom L B B' 0 (2 * halvings (tuples.map (·.count)).sum + 5) (fun bb => check K ctx bb tuples) := by
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := Nat.le_add_right _ _
  simp only [check_eq K ctx _ tuples h]
  refine agree_bind (k' := 1) (n' := 2 * halvings (tuples.map (·.count)).sum + 4)
    (agree_coinKey K hB h1 (by rw [checkLabels_eq]; omega)
      (by unfold RealNetworkE1g.checkStream; split_ifs <;> omega)) (fun key => ?_) (by omega) (by omega)
  refine agree_bind (k' := 1) (n' := 2 * halvings (tuples.map (·.count)).sum + 4)
    (agree_const _ (moves_lift labelAdds_zero _)) (fun τ => ?_) (by omega) (by omega)
  refine agree_bind (k' := 1) (n' := 2 * halvings (tuples.map (·.count)).sum + 4)
    (agree_const _ (moves_lift labelAdds_zero _)) (fun _ => ?_) (by omega) (by omega)
  have hslice := agree_foldlM_range (L := L) (B := B) (B' := B')
    (fun bb => sliceStep K ctx bb τ (tuples.map (·.count)).sum) 1 sliceBits
    (fun j hj b => by exact agree_sliceStep K ctx hB h1 τ _ b (j := j) (lt_of_lt_of_le hj hs)) sliceBits le_rfl
    ((fun T k => wordWeightOf K τ (tuples.map (·.count)).sum k * liftedPart tuples (·.x) T k : Shares C E),
      liftedPart tuples (·.y), conv K ctx (claimOf K τ (tuples.map (·.count)).sum (liftedPart tuples (·.z))) 0)
  refine agree_bind (k' := 1 + 2 * sliceBits) (n' := 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 4)
    hslice (fun p => ?_) (by omega) (by omega)
  have hhalf := agree_foldlM_range (L := L) (B := B) (B' := B')
    (fun bb => halvingStep K ctx bb (sliceWidth (tuples.map (·.count)).sum)) (1 + 2 * sliceBits)
    (halvings (tuples.map (·.count)).sum - sliceBits) (fun j hj b => by
      have e : 1 + 2 * sliceBits + 2 * j = 1 + 2 * (sliceBits + j) := by ring
      rw [e]
      exact agree_halvingStep K ctx hB h1 _ b j (i := sliceBits + j) (by omega))
    _ le_rfl (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
  exact agree_bind (k' := 1 + 2 * halvings (tuples.map (·.count)).sum) (n' := 4) hhalf
    (fun p' => agree_finalStep K ctx hB h1 p') (by omega) (by omega)

end Pieces

/-! ## The label range of the check -/

section RowJ6

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

attribute [local instance] inhabitedField

omit [Field E] [Algebra Bit E] in
theorem moves_freshLabel {ι : Type} {G : OracleSpec ι} : Moves (LabelAdds 1) (freshLabel : RunM C E G ℕ) :=
  moves_modifyGet _ fun _ => rfl

theorem moves_coinWith {ι : Type} {G : OracleSpec ι} (ctx : Context C) (randomness : PrssOutput C E) (count : ℕ) :
    Moves (LabelAdds 0) (coinWith (G := G) K ctx randomness count) := by
  unfold coinWith
  exact moves_label_bind (moves_lift labelAdds_zero _) (fun _ => moves_pure labelAdds_zero _) rfl

theorem moves_reshare {ι : Type} {G : OracleSpec ι} {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    Moves (LabelAdds 0) (reshare (G := G) K ctx codec randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshare record
  exact moves_label_bind (moves_lift labelAdds_zero _) (fun _ => moves_label_bind (a := 0) (b := 0)
    (moves_modify _ fun _ => rfl) (fun _ => moves_pure labelAdds_zero _) rfl) rfl

/-- Each block on drawn values takes one label. -/
theorem oneLabelBlocks_drawn (D : C.Coalition) (L : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) {m : ℕ} (tables : RealNetworkV3.DrawTables C E m)
    (i : C.Party) : OneLabelBlocks (RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB tables i) where
  coin n := moves_label_bind moves_freshLabel (fun _ => moves_coinWith K _ _ n) rfl
  extendMult _ := moves_label_bind moves_freshLabel (fun _ => moves_reshare K _ _ _ _ _) rfl
  randElements _ := moves_label_bind moves_freshLabel (fun _ => moves_pure labelAdds_zero _) rfl
  randBits _ := moves_label_bind moves_freshLabel (fun _ => moves_pure labelAdds_zero _) rfl

/-- `RowJ6` holds. The check calls each block at one label of its range, and at that label the blocks
agree. -/
theorem rowJ6 (D : C.Coalition) : RowJ6 K D := by
  intro ctx L knownE knownB m tables i B tuples rs hcount hL hB
  exact (agree_check K ctx tuples hB (oneLabelBlocks_drawn K D L knownE knownB tables i) hcount).1 rs
    (by rw [hL, Nat.add_zero])

end RowJ6

/-! ## The join in its output form -/

section Join

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)

attribute [local instance] inhabitedField

/-- The join of the pilot in its output form holds for each coalition. -/
theorem pilotJoinOut : ∀ D : C.Coalition, PilotJoinOut prims K D := fun D =>
  pilotJoinOut_of_rows prims K D (rowJ2 prims K D) (rowJ4 D) (rowJ5 prims D) (rowJ6 K D) (rowJ7 prims K D)
    (rowJ8 prims K D)

end Join

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ8

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ6

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ7

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotJoinOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotJoinOut
