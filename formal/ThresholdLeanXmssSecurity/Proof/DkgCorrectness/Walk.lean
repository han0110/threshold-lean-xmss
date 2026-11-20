import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Game
import ThresholdLeanXmssSecurity.Proof.Pilot.Outputs

/-!
# The stream world only grows

A run in `streamWorld` only adds cells to its two caches (`streamWorld_le`, `simulateQ_le`), and
`Keeps` is the form of a step that keeps a property of the world. Two reads of one stream cell agree
in `streamWorld`. `headCounts` gives the counts of the head of a check.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

/-! ## The hash cache of `streamWorld` -/

section World

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

theorem mem_support_onHash {α : Type} (m : StateT (HashCache C) ProbComp α) (s : HashCache C × HiddenCache C)
    (y : α × (HashCache C × HiddenCache C)) (hy : y ∈ support ((onHash m).run s)) :
    ∃ r ∈ support (m.run s.1), y = (r.1, (r.2, s.2)) := by
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact ⟨r, hr, rfl⟩

theorem programAnswer_mono (x : Query C × HashOutput) (c : HashCache C) (y : Bool × HashCache C)
    (hy : y ∈ support ((programAnswer x).run c)) : c ≤ y.2 := by
  unfold programAnswer at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  split_ifs at hy with hc
  · simp at hy
    rw [hy]
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    rw [hy]
    exact QueryCache.le_cacheQuery _ (Option.not_isSome_iff_eq_none.1 fun h => hc (Or.inr h))

end World

section WorldQuery

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- A local query of an honest operator in `streamWorld` grows the hash cache. Its answer is an
answer with `H` fixed to each good `h` that agrees with the new cache. -/
theorem streamWorld_local {E ι : Type} {G : OracleSpec ι} (q : (LocalSpec C).Domain)
    (s : HashCache C × HiddenCache C) (y : (LocalSpec C).Range q × (HashCache C × HiddenCache C))
    (hy : y ∈ support ((streamWorld prims D (.inr q)).run s)) :
    s.1 ≤ y.2.1 ∧ ∀ h, Good prims h → Agrees h y.2.1 →
      y.1 ∈ support (fixHash (E := E) (G := G) h (Sum.inl (Sum.inl q))) := by
  rcases q with n | q | x
  · obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s y hy
    exact ⟨(localAnswer_support (fun _ => 0) _ s.1 r hr).1, fun _ _ _ => by simp [fixHash]⟩
  · obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s y hy
    obtain ⟨hle, -, hd⟩ := hashAnswer_support q s.1 r hr
    exact ⟨hle, fun h hg ha => by simp [fixHash, hd h hg ha]⟩
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, hx, ↓reduceIte, StateT.run_mk, support_map, Set.mem_image] at hy
      obtain ⟨r, -, rfl⟩ := hy
      exact ⟨le_rfl, fun _ _ _ => by simp [fixHash]⟩
    · simp only [streamWorld, hx, ↓reduceIte] at hy
      obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s y hy
      exact ⟨(localAnswer_support (fun _ => 0) _ s.1 r hr).1, fun _ _ _ => by simp [fixHash]⟩

/-- Each query in `streamWorld` grows the hash cache. -/
theorem streamWorld_mono (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (y : (WorldSpec C).Range t × (HashCache C × HiddenCache C)) (hy : y ∈ support ((streamWorld prims D t).run s)) :
    s.1 ≤ y.2.1 := by
  rcases t with (q | x) | q
  · obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s y hy
    exact (localAnswer_support (fun _ => 0) _ s.1 r hr).1
  · obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s y hy
    exact programAnswer_mono x s.1 r hr
  · exact (streamWorld_local (E := Unit) (G := []ₒ) prims D q s y hy).1

/-- Each run in `streamWorld` grows the hash cache. -/
theorem streamWorld_run_mono {β : Type} (oa : OracleComp (WorldSpec C) β) :
    ∀ s z, z ∈ support ((simulateQ (streamWorld prims D) oa).run s) → s.1 ≤ z.2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact (streamWorld_mono prims D t s y hy).trans (ih y.1 y.2 z hz)

end WorldQuery

section Walk

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

/-- Each computation of a sequence in `streamWorld` gives a value with a property that a larger
cache keeps. Then the sequence gives each value with the property at the end cache. -/
theorem sequenceFin_streamWorld {β : Type} :
    ∀ {n : ℕ} (Q : Fin n → β → HashCache C → Prop) (f : Fin n → OracleComp (WorldSpec C) β),
      (∀ i b c c', Q i b c → c ≤ c' → Q i b c') →
      (∀ i s y, y ∈ support ((simulateQ (streamWorld prims D) (f i)).run s) → Q i y.1 y.2.1) →
      ∀ s z, z ∈ support ((simulateQ (streamWorld prims D) (OverPermutation.sequenceFin f)).run s) →
        ∀ i, Q i (z.1 i) z.2.1
  | 0, _, _, _, _, _, _, _, i => i.elim0
  | n + 1, Q, f, hmono, hf, s, z, hz, i => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    cases i using Fin.cases with
    | zero => exact hmono 0 _ _ _ (hf 0 s y hy) (streamWorld_run_mono prims D _ y.2 w hw)
    | succ i =>
      exact sequenceFin_streamWorld (fun i => Q i.succ) (fun i => f i.succ) (fun i => hmono i.succ)
        (fun i => hf i.succ) y.2 w hw i

end Walk

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

namespace Ready

/-! ## The world grows -/

section Grow

variable {C : Committee} (prims : Primitives)

/-- A call of a lazy random oracle grows its cache and caches its answer. It is
`randomOracle_support` for each domain. -/
theorem randomOracle_support' {α β : Type} [DecidableEq α] [SampleableType β] (q : α)
    (s : (α →ₒ β).QueryCache) (p : β × (α →ₒ β).QueryCache)
    (hp : p ∈ support (((α →ₒ β).randomOracle q).run s)) : s ≤ p.2 ∧ p.2 q = some p.1 := by
  rcases hs : s q with _ | u
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs] at hp
    erw [support_map, Set.mem_image] at hp
    obtain ⟨u, _, rfl⟩ := hp
    exact ⟨QueryCache.le_cacheQuery _ hs, by simp⟩
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs] at hp
    simp at hp
    subst hp
    exact ⟨le_rfl, hs⟩

theorem onHash_le {α : Type} {m : StateT (HashCache C) ProbComp α}
    (hm : ∀ s, ∀ r ∈ support (m.run s), s ≤ r.2) : ∀ st, ∀ z ∈ support ((onHash m).run st), st ≤ z.2 := by
  intro st z hz
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact ⟨hm st.1 r hr, le_rfl⟩

theorem programAnswer_le (x : Query C × HashOutput) :
    ∀ s, ∀ r ∈ support ((programAnswer x).run s), s ≤ r.2 := by
  intro s z hz
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hg
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    have hnone : s x.1 = none := by
      push Not at hg
      exact Option.not_isSome_iff_eq_none.mp (by simpa using hg.2)
    exact QueryCache.le_cacheQuery _ hnone

/-- Each call of `streamWorld` grows the world. -/
theorem streamWorld_le (D : C.Coalition) (t : (WorldSpec C).Domain) :
    ∀ w, ∀ z ∈ support ((streamWorld prims D t).run w), w ≤ z.2 := by
  rcases t with ((t | p) | (u | q | x))
  · exact onHash_le fun s r hr => (localAnswer_support (fun _ => 0) t s r hr).1
  · exact onHash_le (programAnswer_le p)
  · exact onHash_le fun s r hr => (localAnswer_support (fun _ => 0) (.inl u) s r hr).1
  · exact onHash_le fun s r hr => (localAnswer_support (fun _ => 0) (.inr (.inl q)) s r hr).1
  · show ∀ w, ∀ z ∈ support ((if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w), w ≤ z.2
    split_ifs
    · intro w z hz
      simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      exact ⟨le_rfl, (randomOracle_support' _ _ r hr).1⟩
    · exact onHash_le fun s r hr => (localAnswer_support (fun _ => 0) (.inr (.inr x)) s r hr).1

/-- Each computation in `streamWorld` grows the world. -/
theorem simulateQ_le (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) (w : StreamState C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run w), w ≤ z.2 :=
  OracleComp.simulateQ_run_preservesInv _ (fun st => w ≤ st)
    (fun t s hs z hz => le_trans hs (streamWorld_le prims D t s z hz)) oa w le_rfl

end Grow

/-! ## A generic invariant of the game after the PRF hop -/

section Keep

variable {C : Committee} {σ : Type} (I : FirstState C σ → StreamState C → Prop)

/-- A computation of the game that keeps the invariant `I`. -/
def Keeps {α : Type} (m : FirstM C σ α) : Prop :=
  ∀ s world, I s world → ∀ z ∈ support ((m.run s).run world), I z.1.2 z.2

/-- A computation of the signing phase that keeps `I` from each state of the signing game. -/
def KeepsT {α : Type} (m : StateT (TsigState C) (FirstM C σ) α) : Prop := ∀ t, Keeps I (m.run t)

variable {I}

theorem keeps_pure {α : Type} (a : α) : Keeps I (pure a : FirstM C σ α) := by
  intro s world hs z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hs

theorem keeps_bind {α β : Type} {m : FirstM C σ α} {f : α → FirstM C σ β} (hm : Keeps I m)
    (hf : ∀ a, Keeps I (f a)) : Keeps I (m >>= f) := by
  intro s world hs z hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  exact hf y.1.1 y.1.2 y.2 (hm s world hs y hy) z hz

theorem keeps_get_bind {β : Type} {f : FirstState C σ → FirstM C σ β} (hf : ∀ s, Keeps I (f s)) :
    Keeps I (get >>= f) := by
  intro s world hs z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf s s world hs z hz

theorem keeps_get : Keeps I (get : FirstM C σ _) := by
  intro s world hs z hz
  simp only [StateT.run_get] at hz
  subst hz
  exact hs

theorem keeps_modify (f : FirstState C σ → FirstState C σ) (h : ∀ s world, I s world → I (f s) world) :
    Keeps I (modify f : FirstM C σ Unit) := by
  intro s world hs z hz
  simp only [StateT.run_modify] at hz
  subst hz
  exact h s world hs

/-- A computation of the world keeps an invariant that holds in each larger world. -/
theorem keeps_lift (grow : ∀ s w w', I s w → w ≤ w' → I s w') {α : Type} {x : StateT (StreamState C) ProbComp α}
    (hx : ∀ w, ∀ z ∈ support (x.run w), w ≤ z.2) : Keeps I (StateT.lift x : FirstM C σ α) := by
  intro s world hs z hz
  simp only [StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact grow s world y.2 hs (hx world y hy)

theorem keepsT_lift {α : Type} {m : FirstM C σ α} (hm : Keeps I m) :
    KeepsT I (StateT.lift m : StateT (TsigState C) (FirstM C σ) α) := fun t => by
  rw [StateT.run_lift]
  exact keeps_bind hm fun _ => keeps_pure _

theorem keepsT_bind {α β : Type} {m : StateT (TsigState C) (FirstM C σ) α}
    {f : α → StateT (TsigState C) (FirstM C σ) β} (hm : KeepsT I m) (hf : ∀ a, KeepsT I (f a)) :
    KeepsT I (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact keeps_bind (hm t) fun y => hf y.1 y.2

theorem keepsT_simulateQ {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT (TsigState C) (FirstM C σ)))
    (h : ∀ q, KeepsT I (impl q)) {α : Type} (oa : OracleComp spec α) : KeepsT I (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun t => by rw [simulateQ_pure, StateT.run_pure]; exact keeps_pure _
  | query_bind q k ih =>
    intro t
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    exact keeps_bind (h q t) fun y => ih y.1 y.2

end Keep

/-! ## The invariant of readiness -/

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

attribute [local irreducible] streamTreeRun wrongOutput

theorem streamTreeRun_le (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (world : StreamState C) :
    ∀ x ∈ support ((streamTreeRun prims K circuits settings D net tree s).run world), world ≤ x.2 := by
  unfold streamTreeRun
  exact simulateQ_le prims D _ world

theorem none_orElse {α : Type} (b : Option α) : (none <|> b) = b := rfl

theorem some_orElse {α : Type} (a : α) (b : Option α) : (some a <|> b) = some a := rfl

end Game

end Ready

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

section Cells

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The free query of `PRG` at `x`. -/
abbrev freeRead (x : PrgInput C) : (WorldSpec C).Domain := .inr (.inr (.inr x))

/-- The state holds bit `b` at the stream cell `x`. Under a hidden key the table holds `b`. Under a
known key the hash cache holds the stream key, and `b` is AES under its first 128 bits. -/
def StreamCell (x : PrgInput C) (s : HashCache C × HiddenCache C) (b : Bit) : Prop :=
  if Hidden D x.1 then s.2 ((x.1, x.2.1), x.2.2) = some b
  else ∃ h, s.1 (.streamKey x.2.1) = some h ∧ b = prims.aes.eval (truncateHash h) x.2.2

theorem StreamCell.unique {x : PrgInput C} {s : HashCache C × HiddenCache C} {b b' : Bit}
    (h : StreamCell prims D x s b) (h' : StreamCell prims D x s b') : b = b' := by
  unfold StreamCell at h h'
  split_ifs at h h'
  · exact Option.some_injective _ (h.symm.trans h')
  · obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨k', hk', rfl⟩ := h'
    rw [Option.some_injective _ (hk.symm.trans hk')]

theorem StreamCell.mono {x : PrgInput C} {s s' : HashCache C × HiddenCache C} {b : Bit}
    (h : StreamCell prims D x s b) (h₁ : s.1 ≤ s'.1) (h₂ : s.2 ≤ s'.2) : StreamCell prims D x s' b := by
  unfold StreamCell at h ⊢
  split_ifs at h ⊢
  · exact h₂ h
  · obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, h₁ hk, rfl⟩

/-- A query of the table of the hidden streams grows the table and writes its cell. -/
theorem hiddenOracle_cached (q : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) (c : HiddenCache C)
    (r : Bit × HiddenCache C)
    (hr : r ∈ support (((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle q).run c)) :
    c ≤ r.2 ∧ r.2 q = some r.1 := by
  rw [OracleSpec.randomOracle] at hr
  rcases hc : c q with _ | u
  · rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
    obtain ⟨v, -, rfl⟩ := hr
    exact ⟨QueryCache.le_cacheQuery _ hc, QueryCache.cacheQuery_self _ _ _⟩
  · rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨le_rfl, hc⟩

/-- Each query in `streamWorld` grows the table of the hidden streams. -/
theorem streamWorld_hidden_mono (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (y : (WorldSpec C).Range t × (HashCache C × HiddenCache C)) (hy : y ∈ support ((streamWorld prims D t).run s)) :
    s.2 ≤ y.2.2 := by
  rcases t with (q | x) | (n | q | x)
  · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ s y hy
    exact le_rfl
  · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ s y hy
    exact le_rfl
  · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ s y hy
    exact le_rfl
  · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ s y hy
    exact le_rfl
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, hx, ↓reduceIte, StateT.run_mk, support_map, Set.mem_image] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      exact (hiddenOracle_cached _ _ r hr).1
    · simp only [streamWorld, hx, ↓reduceIte] at hy
      obtain ⟨r, -, rfl⟩ := mem_support_onHash _ s y hy
      exact le_rfl

/-- Each run in `streamWorld` grows the table of the hidden streams. -/
theorem streamWorld_run_hidden_mono {β : Type} (oa : OracleComp (WorldSpec C) β) :
    ∀ s z, z ∈ support ((simulateQ (streamWorld prims D) oa).run s) → s.2 ≤ z.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact (streamWorld_hidden_mono prims D t s y hy).trans (ih y.1 y.2 z hz)

/-- Each run in `streamWorld` keeps each stream cell. -/
theorem StreamCell.run {x : PrgInput C} {s : HashCache C × HiddenCache C} {b : Bit}
    (h : StreamCell prims D x s b) {β : Type} (oa : OracleComp (WorldSpec C) β) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run s), StreamCell prims D x z.2 b := fun z hz =>
  h.mono prims D (streamWorld_run_mono prims D oa s z hz) (streamWorld_run_hidden_mono prims D oa s z hz)

/-- A free read of `PRG` writes its stream cell with its answer. -/
theorem freeRead_cell (x : PrgInput C) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((streamWorld prims D (freeRead x)).run s), StreamCell prims D x z.2 z.1 := by
  intro z hz
  by_cases hx : Hidden D x.1
  · simp only [streamWorld, hx, ↓reduceIte, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simp only [StreamCell, hx, ↓reduceIte]
    exact (hiddenOracle_cached _ _ r hr).2
  · simp only [streamWorld, hx, ↓reduceIte] at hz
    obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s z hz
    change r ∈ support ((prgAnswer prims x).run s.1) at hr
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    simp only [StreamCell, hx, ↓reduceIte]
    exact ⟨p.1, hashAnswer_cached prims (by rintro ⟨_, h, _⟩; cases h) s.1 p hp, rfl⟩

/-- The free reads of `PRG` at the inputs of a list. -/
def readAll (xs : List (PrgInput C)) : OracleComp (WorldSpec C) (List Bit) :=
  xs.mapM fun x => query (spec := WorldSpec C) (freeRead x)

/-- `count` bits of `PRG(key, ρ, idx)` on the free copy. -/
def freeBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) : OracleComp (WorldSpec C) (ℕ → Bit) :=
  free (liftComp (prgBits name key ρ idx count) (LocalSpec C))

theorem free_mapM {α β : Type} (f : α → OracleComp (LocalSpec C) β) :
    ∀ l : List α, free (l.mapM f) = l.mapM fun a => free (f a)
  | [] => by simp
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, free_bind]
    refine bind_congr fun b => ?_
    rw [free_bind, free_mapM f l]
    simp

theorem free_liftComp_reads (name : KeyName C) (key : HashOutput) (ρ idx : ℕ) (l : List ℕ) :
    free (liftComp (l.mapM fun position =>
      (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) : OracleComp (RoSpec C) Bit)) (LocalSpec C)) =
      readAll (l.map fun position => (name, key, ρ, idx, position)) := by
  have e := liftComp_mapM_local (C := C) (β := Bit)
    (fun position => (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) : OracleComp (RoSpec C) Bit)) l
  refine (congrArg free e).trans ?_
  rw [free_mapM, readAll, List.mapM_map]
  rfl

theorem freeBits_eq (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    freeBits name key ρ idx count = (fun bits g => bits.getD g 0) <$>
      readAll ((List.range count).map fun position => (name, key, ρ, idx, position)) := by
  unfold freeBits prgBits
  rw [liftComp_bind, free_bind, free_liftComp_reads, map_eq_bind_pure_comp]
  rfl

/-- The free reads of a list write the stream cell of each input with its answer. -/
theorem readAll_cells (xs : List (PrgInput C)) :
    ∀ s, ∀ z ∈ support ((simulateQ (streamWorld prims D) (readAll xs)).run s),
      List.Forall₂ (fun x b => StreamCell prims D x z.2 b) xs z.1 := by
  have e : ∀ x : PrgInput C, simulateQ (streamWorld prims D) (query (spec := WorldSpec C) (freeRead x)) =
      streamWorld prims D (freeRead x) := fun x => (simulateQ_query _ _).trans (id_map _)
  induction xs with
  | nil =>
    intro s z hz
    simp only [readAll, List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact List.Forall₂.nil
  | cons x xs ih =>
    intro s z hz
    simp only [readAll, List.mapM_cons, simulateQ_bind, e, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    exact List.Forall₂.cons ((freeRead_cell prims D x s y hy).run prims D (readAll xs) w hw) (ih y.2 w hw)

end Cells

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

attribute [local instance] inhabitedField

/-! ## The head of a batch -/

section Head

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The counts of the tuples of the head of a batch of the circuits `jobs`. There is one tuple for each
AND layer and one for `Rerand`. -/
def headCounts (jobs : List Circuit) : List ℕ :=
  (List.range (depth jobs)).map (fun l => (gatesAt jobs l).length) ++ [(outputsOf jobs).length]

end Head

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.streamWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.streamWorld_le

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.simulateQ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.simulateQ_le
