import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Compare
import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# The step to the comparison game up to a touch of a hidden cell

A hidden cell is the derive input `hiddenInput parts T` of a hidden term `T`. A touch is a counted
call of `H` or a programming call at a hidden cell. `flagWorld` is `loggedWorld` with a flag that
records each touch.

* A call that asks no hidden cell commutes with the erasure of the hidden cells (`loggedWorld_erase`)
  and keeps the value of each hidden cell (`loggedWorld_keep`).
* `interWorld seed` is `flagWorld` where a free call of `H` at an empty hidden cell writes the seed of
  its hidden term. Each seed is read at most once, so `flagWorld` is `interWorld` on uniform seeds
  (`wp_flagWorld_eq`).
* With no touch, each hidden cell of `interWorld` is empty or holds the seed of its term (`SeedInv`),
  and the state of `compWorld` is the state of `interWorld` with no hidden cell. So `interWorld` is
  dominated by `compWorld` until a touch (`interWorld_dominated`).
* `SeedTouch` bounds the probability of a touch in `touchRun` by `compCloseError C q`. It gives
  `SeedClose` (`seedClose_of_touch`), and with `CompHit` it gives `HitSeed` (`hitSeed_of_touch`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## Hidden cells -/

section Cells

variable (D : C.Coalition) (parts : C.Party → Parts C)

/-- The derive input of a hidden term. -/
def HiddenCell (q : Query C) : Prop := ∃ T, ¬ KnownTo D.1 T ∧ q = hiddenInput parts T

theorem hiddenTermOf_some {q : Query C} {T : C.Term} (h : hiddenTermOf D parts q = some T) :
    ¬ KnownTo D.1 T ∧ q = hiddenInput parts T := by
  unfold hiddenTermOf at h
  split_ifs at h with hq
  cases h
  exact Classical.choose_spec hq

theorem hiddenTermOf_none {q : Query C} (h : hiddenTermOf D parts q = none) : ¬ HiddenCell D parts q := by
  unfold hiddenTermOf at h
  split_ifs at h with hq
  exact hq

theorem hiddenCell_of_some {q : Query C} {T : C.Term} (h : hiddenTermOf D parts q = some T) :
    HiddenCell D parts q :=
  ⟨T, hiddenTermOf_some D parts h⟩

theorem not_hiddenCell_streamKey (k : HashOutput) : ¬ HiddenCell D parts (.streamKey k) :=
  fun ⟨_, _, h⟩ => by cases h

/-- The cache with no hidden cell. -/
def eraseHidden (c : HashCache C) : HashCache C :=
  QueryCache.ofFn fun q => if HiddenCell D parts q then none else c q

/-- The world state with no hidden cell. -/
def eraseLog (w : LogState C) : LogState C := ((eraseHidden D parts w.1.1, w.1.2), w.2)

theorem eraseHidden_apply {c : HashCache C} {q : Query C} (hq : ¬ HiddenCell D parts q) :
    eraseHidden D parts c q = c q := by
  simp [eraseHidden, hq]

theorem eraseHidden_cacheQuery {c : HashCache C} {q : Query C} (hq : ¬ HiddenCell D parts q) (v : HashOutput) :
    eraseHidden D parts (c.cacheQuery q v) = (eraseHidden D parts c).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases h : q' = q
  · subst h
    simp [eraseHidden, hq]
  · by_cases h' : HiddenCell D parts q'
    · simp [eraseHidden, h', h]
    · simp [eraseHidden, h', h]

theorem eraseHidden_cacheQuery_hidden {c : HashCache C} {q : Query C} (hq : HiddenCell D parts q) (v : HashOutput) :
    eraseHidden D parts (c.cacheQuery q v) = eraseHidden D parts c := by
  refine QueryCache.ext fun q' => ?_
  by_cases h' : HiddenCell D parts q'
  · simp [eraseHidden, h']
  · have h : q' ≠ q := fun e => h' (e ▸ hq)
    simp [eraseHidden, h', h]

/-- A counted call of `H` or a programming call at a hidden cell. -/
def Touch : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inr (.inl q))) => HiddenCell D parts q
  | .inl (.inr x) => HiddenCell D parts x.1
  | _ => False

/-- A free call of `H` at a hidden cell. -/
def FreeHidden : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inl q)) => HiddenCell D parts q
  | _ => False

end Cells

/-! ## The calls that ask no hidden cell -/

section Commute

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C)

theorem randomOracle_erase {q : Query C} (hq : ¬ HiddenCell D parts q) (c : HashCache C) :
    ((Query C →ₒ HashOutput).randomOracle q).run (eraseHidden D parts c) =
      (fun z => (z.1, eraseHidden D parts z.2)) <$> ((Query C →ₒ HashOutput).randomOracle q).run c := by
  rw [randomOracle.run_eq, randomOracle.run_eq, eraseHidden_apply D parts hq]
  rcases c q with _ | u
  · simp only [map_bind, map_pure, eraseHidden_cacheQuery D parts hq]
  · simp

theorem randomOracle_keep {q : Query C} (hq : ¬ HiddenCell D parts q) (c : HashCache C) :
    ∀ z ∈ support (((Query C →ₒ HashOutput).randomOracle q).run c), ∀ q', HiddenCell D parts q' → z.2 q' = c q' := by
  intro z hz q' hq'
  rw [randomOracle.run_eq] at hz
  have hne : q' ≠ q := fun e => hq (e ▸ hq')
  rcases hc : c q with _ | u <;> rw [hc] at hz
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_of_ne _ _ hne
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl

theorem hashAnswer_erase {q : Query C} (hq : ¬ HiddenCell D parts q) (c : HashCache C) :
    (hashAnswer prims q).run (eraseHidden D parts c) =
      (fun z => (z.1, eraseHidden D parts z.2)) <$> (hashAnswer prims q).run c := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hf
    rw [hashAnswer_of_isFixed prims hm]
    simp
  · rw [hashAnswer_of_not_isFixed prims hf]
    exact randomOracle_erase D parts hq c

theorem hashAnswer_keep {q : Query C} (hq : ¬ HiddenCell D parts q) (c : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run c), ∀ q', HiddenCell D parts q' → z.2 q' = c q' := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hf
    rw [hashAnswer_of_isFixed prims hm]
    intro z hz q' _
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · rw [hashAnswer_of_not_isFixed prims hf]
    exact randomOracle_keep D parts hq c

/-- A local call that asks no hidden cell. -/
def LocalOff : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => ¬ HiddenCell D parts q
  | _ => True

theorem localAnswer_erase (t : (LocalSpec C).Domain) (ht : LocalOff D parts t) (c : HashCache C) :
    (localAnswer prims t).run (eraseHidden D parts c) =
      (fun z => (z.1, eraseHidden D parts z.2)) <$> (localAnswer prims t).run c := by
  rcases t with n | q | x
  · change (unifFwdImpl (Query C →ₒ HashOutput) n).run _ = _ <$> (unifFwdImpl (Query C →ₒ HashOutput) n).run _
    simp [unifFwdImpl]
  · exact hashAnswer_erase prims D parts ht c
  · change (prgAnswer prims x).run _ = _ <$> (prgAnswer prims x).run _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure]
    rw [hashAnswer_erase prims D parts (not_hiddenCell_streamKey D parts x.2.1)]
    simp only [bind_map_left, map_bind, map_pure]

theorem localAnswer_keep (t : (LocalSpec C).Domain) (ht : LocalOff D parts t) (c : HashCache C) :
    ∀ z ∈ support ((localAnswer prims t).run c), ∀ q', HiddenCell D parts q' → z.2 q' = c q' := by
  rcases t with n | q | x
  · change ∀ z ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run c), _
    intro z hz q' _
    simp only [unifFwdImpl, QueryImpl.liftTarget_apply, StateT.run_monadLift, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨_, -, rfl⟩ := hz
    rfl
  · exact hashAnswer_keep prims D parts ht c
  · change ∀ z ∈ support ((prgAnswer prims x).run c), _
    intro z hz q' hq'
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hashAnswer_keep prims D parts (not_hiddenCell_streamKey D parts x.2.1) c y hy q' hq'

/-- A call of the world that asks no hidden cell. -/
def WorldOff (t : (WorldSpec C).Domain) : Prop := ¬ Touch D parts t ∧ ¬ FreeHidden D parts t

theorem loggedWorld_erase (t : (WorldSpec C).Domain) (ht : WorldOff D parts t) (w : LogState C) :
    (loggedWorld prims D t).run (eraseLog D parts w) =
      (fun z => (z.1, eraseLog D parts z.2)) <$> (loggedWorld prims D t).run w := by
  obtain ⟨⟨c, h⟩, log⟩ := w
  obtain ⟨ht₁, ht₂⟩ := ht
  have hloc : ∀ u : (LocalSpec C).Domain, LocalOff D parts u →
      (onHash (localAnswer prims u)).run (eraseHidden D parts c, h) =
        (fun z => (z.1, (eraseHidden D parts z.2.1, z.2.2))) <$> (onHash (localAnswer prims u)).run (c, h) :=
    fun u hu => by
      simp only [onHash, StateT.run_mk, localAnswer_erase prims D parts u hu c, Functor.map_map]
  simp only [loggedWorld, eraseLog, StateT.run_mk, Functor.map_map]
  rcases t with ((n | q | x) | p) | (n | q | x)
  · simp only [streamWorld]; erw [hloc (.inl n) trivial]; simp only [Functor.map_map]; rfl
  · simp only [streamWorld]; erw [hloc (.inr (.inl q)) ht₁]; simp only [Functor.map_map]; rfl
  · simp only [streamWorld]; erw [hloc (.inr (.inr x)) trivial]; simp only [Functor.map_map]; rfl
  · simp only [streamWorld, onHash, StateT.run_mk, Functor.map_map]
    change (fun r => _) <$> (programAnswer p).run (eraseHidden D parts c) = _ <$> (programAnswer p).run c
    have hp : ¬ HiddenCell D parts p.1 := ht₁
    unfold programAnswer
    simp only [StateT.run_bind, StateT.run_get, pure_bind, eraseHidden_apply D parts hp]
    split_ifs
    · simp
    · simp [eraseHidden_cacheQuery D parts hp]
  · simp only [streamWorld]; rw [hloc (.inl n) trivial]; simp [Functor.map_map]
  · simp only [streamWorld]; rw [hloc (.inr (.inl q)) ht₂]; simp [Functor.map_map]
  · simp only [streamWorld]
    split_ifs
    · simp [Functor.map_map]
    · rw [hloc (.inr (.inr x)) trivial]; simp [Functor.map_map]

theorem loggedWorld_keep (t : (WorldSpec C).Domain) (ht : WorldOff D parts t) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w), ∀ q, HiddenCell D parts q → z.2.1.1 q = w.1.1 q := by
  obtain ⟨⟨c, h⟩, log⟩ := w
  obtain ⟨ht₁, ht₂⟩ := ht
  have hloc : ∀ u : (LocalSpec C).Domain, LocalOff D parts u →
      ∀ z ∈ support ((onHash (localAnswer prims u)).run (c, h)), ∀ q, HiddenCell D parts q → z.2.1 q = c q :=
    fun u hu z hz q hq => by
      simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact localAnswer_keep prims D parts u hu c y hy q hq
  intro z hz q hq
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rcases t with ((n | q' | x) | p) | (n | q' | x)
  · exact hloc (.inl n) trivial y hy q hq
  · exact hloc (.inr (.inl q')) ht₁ y hy q hq
  · exact hloc (.inr (.inr x)) trivial y hy q hq
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    change y' ∈ support ((programAnswer p).run c) at hy'
    have hp : ¬ HiddenCell D parts p.1 := ht₁
    have hne : q ≠ p.1 := fun e => hp (e ▸ hq)
    unfold programAnswer at hy'
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy'
    split_ifs at hy'
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy'
      subst hy'
      rfl
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hy'
      subst hy'
      exact QueryCache.cacheQuery_of_ne _ _ hne
  · exact hloc (.inl n) trivial y hy q hq
  · exact hloc (.inr (.inl q')) ht₂ y hy q hq
  · simp only [streamWorld] at hy
    split_ifs at hy
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hy
      obtain ⟨y', -, rfl⟩ := hy
      rfl
    · exact hloc (.inr (.inr x)) trivial y hy q hq

end Commute

/-! ## The flagged world and the world with the seeds -/

section Worlds

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C)

/-- `loggedWorld` with a flag that records each touch of a hidden cell. -/
def flagWorld : QueryImpl (WorldSpec C) (StateT (LogState C × Bool) ProbComp) := fun t =>
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2 || decide (Touch D parts t)))) <$> (loggedWorld prims D t).run s.1

/-- `flagWorld` where a free call of `H` at an empty hidden cell writes the seed `seed T` of the
hidden term `T` of the cell. -/
def interWorld (seed : C.Term → HashOutput) : QueryImpl (WorldSpec C) (StateT (LogState C × Bool) ProbComp) :=
  fun t => match t with
  | .inr (.inr (.inl q)) =>
      match hiddenTermOf D parts q with
      | some T => StateT.mk fun s => match s.1.1.1 q with
          | some v => pure (v, s)
          | none => pure (seed T, (((s.1.1.1.cacheQuery q (seed T), s.1.1.2), s.1.2), s.2))
      | none => flagWorld prims D parts (.inr (.inr (.inl q)))
  | t => flagWorld prims D parts t

theorem flagWorld_run (t : (WorldSpec C).Domain) (s : LogState C × Bool) :
    (flagWorld prims D parts t).run s =
      (fun r => (r.1, (r.2, s.2 || decide (Touch D parts t)))) <$> (loggedWorld prims D t).run s.1 := rfl

/-- The flag changes no law of the result and of the world state. -/
theorem flagWorld_proj {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LogState C × Bool) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (flagWorld prims D parts) oa).run s =
      (simulateQ (loggedWorld prims D) oa).run s.1 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, map_bind, OracleQuery.input_query, OracleQuery.cont_query,
      liftM, monadLift_self, flagWorld_run, bind_map_left]
    exact bind_congr fun r => ih _ (r.2, _)

/-- The free call of `H` at a hidden cell in `flagWorld`. -/
theorem flagWorld_freeHidden {q : Query C} (hq : HiddenCell D parts q) (s : LogState C × Bool) :
    (flagWorld prims D parts (.inr (.inr (.inl q)))).run s =
      match s.1.1.1 q with
      | some v => pure (v, s)
      | none => ($ᵗ HashOutput) >>= fun u => pure (u, (((s.1.1.1.cacheQuery q u, s.1.1.2), s.1.2), s.2)) := by
  obtain ⟨⟨⟨c, h⟩, log⟩, b⟩ := s
  obtain ⟨T, -, rfl⟩ := hq
  have hf : ¬ IsFixed (hiddenInput parts T) := fun ⟨_, h, _⟩ => by cases h
  have hd : decide (Touch D parts (.inr (.inr (.inl (hiddenInput parts T))))) = false := decide_eq_false id
  simp only [flagWorld_run, hd, Bool.or_false, loggedWorld, streamWorld, onHash, StateT.run_mk, Functor.map_map]
  change (fun r => _) <$> (hashAnswer prims (hiddenInput parts T)).run c = _
  rw [hashAnswer_of_not_isFixed prims hf, randomOracle.run_eq]
  rcases c (hiddenInput parts T) with _ | v
  · simp [countedCells]
  · simp [countedCells]

theorem interWorld_of_ne (seed : C.Term → HashOutput) (t : (WorldSpec C).Domain)
    (ht : ∀ q, t = .inr (.inr (.inl q)) → hiddenTermOf D parts q = none) :
    interWorld prims D parts seed t = flagWorld prims D parts t := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  all_goals try rfl
  simp only [interWorld, ht q rfl]

theorem interWorld_some (seed : C.Term → HashOutput) {q : Query C} {T : C.Term} (hT : hiddenTermOf D parts q = some T)
    (s : LogState C × Bool) :
    (interWorld prims D parts seed (.inr (.inr (.inl q)))).run s =
      match s.1.1.1 q with
      | some v => pure (v, s)
      | none => pure (seed T, (((s.1.1.1.cacheQuery q (seed T), s.1.1.2), s.1.2), s.2)) := by
  simp only [interWorld, hT, StateT.run_mk]

/-- Each step of `interWorld` grows the cache. -/
theorem interWorld_mono (seed : C.Term → HashOutput) (t : (WorldSpec C).Domain) (s : LogState C × Bool) :
    ∀ z ∈ support ((interWorld prims D parts seed t).run s), s.1.1.1 ≤ z.2.1.1.1 := by
  intro z hz
  by_cases ht : ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T
  · obtain ⟨q, T, rfl, hT⟩ := ht
    rw [interWorld_some prims D parts seed hT] at hz
    rcases hc : s.1.1.1 q with _ | v <;> rw [hc] at hz <;>
      simp only [support_pure, Set.mem_singleton_iff] at hz <;> subst hz
    · intro q' u hu
      have hne : q' ≠ q := fun e => by rw [e, hc] at hu; cases hu
      simpa [QueryCache.cacheQuery_of_ne _ _ hne] using hu
    · exact le_rfl
  · rw [interWorld_of_ne prims D parts seed t fun q e => by
      rcases hq : hiddenTermOf D parts q with _ | T
      · rfl
      · exact absurd ⟨q, T, e, hq⟩ ht] at hz
    rw [flagWorld_run] at hz
    simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y', hy', rfl⟩ := hy
    exact streamWorld_mono prims D t s.1.1 y' hy'

end Worlds

/-! ## The seeds drawn first -/

section Lazy

/-- One coordinate of a uniform function, drawn again, keeps the law of the function. -/
theorem wp_uniform_update {ι : Type} [Fintype ι] [DecidableEq ι] [SampleableType (ι → HashOutput)] (j : ι) (f : (ι → HashOutput) → ℝ≥0∞) :
    wp ($ᵗ (ι → HashOutput)) f =
      wp ($ᵗ HashOutput) (fun u => wp ($ᵗ (ι → HashOutput)) (fun g => f (Function.update g j u))) := by
  have h := evalDist_uniformSample_bind_update_map (D := ι) (R := HashOutput) (α := ℝ≥0∞)
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample j f
  have e₁ : wp ($ᵗ (ι → HashOutput)) f = wp (do let g ← $ᵗ (ι → HashOutput); pure (f g)) id := by simp
  have e₂ : wp ($ᵗ HashOutput) (fun u => wp ($ᵗ (ι → HashOutput)) (fun g => f (Function.update g j u))) =
      wp (do let u ← $ᵗ HashOutput; let g ← $ᵗ (ι → HashOutput); pure (f (Function.update g j u))) id := by simp
  rw [e₁, e₂]
  refine wp_congr_evalDist_map _ ?_
  simp only [id_map]
  exact h.symm

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C)

/-- A step of `interWorld` reads no seed of a term whose cell has a value. -/
theorem interWorld_update (seed : C.Term → HashOutput) (T : C.Term) (w : HashOutput) (t : (WorldSpec C).Domain)
    (s : LogState C × Bool) (hs : (s.1.1.1 (hiddenInput parts T)).isSome) :
    (interWorld prims D parts (Function.update seed T w) t).run s = (interWorld prims D parts seed t).run s := by
  by_cases ht : ∃ q T', t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T'
  · obtain ⟨q, T', rfl, hT'⟩ := ht
    rw [interWorld_some prims D parts _ hT', interWorld_some prims D parts _ hT']
    by_cases hTT : T' = T
    · subst hTT
      rw [(hiddenTermOf_some D parts hT').2]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
      simp only [hv]
    · simp only [Function.update_of_ne hTT]
  · have hne : ∀ q, t = .inr (.inr (.inl q)) → hiddenTermOf D parts q = none := fun q e => by
      rcases hq : hiddenTermOf D parts q with _ | T'
      · rfl
      · exact absurd ⟨q, T', e, hq⟩ ht
    rw [interWorld_of_ne prims D parts _ t hne, interWorld_of_ne prims D parts _ t hne]

theorem wp_interWorld_update (seed : C.Term → HashOutput) (T : C.Term) (w : HashOutput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) : ∀ (s : LogState C × Bool), (s.1.1.1 (hiddenInput parts T)).isSome →
      ∀ F : α × (LogState C × Bool) → ℝ≥0∞,
      wp ((simulateQ (interWorld prims D parts (Function.update seed T w)) oa).run s) F =
        wp ((simulateQ (interWorld prims D parts seed) oa).run s) F := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _ F; simp
  | query_bind t k ih =>
    intro s hs F
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self,
      StateT.run_bind, wp_bind]
    rw [interWorld_update prims D parts seed T w t s hs]
    refine wp_congr_of_support _ fun z hz => ih z.1 z.2 ?_ F
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    rw [interWorld_mono prims D parts seed t s z hz hv]
    rfl

/-- `flagWorld` is `interWorld` on uniform seeds. Each seed is read at most once, at the first free
call of its cell. -/
theorem wp_flagWorld_eq {α : Type} (oa : OracleComp (WorldSpec C) α) : ∀ (s : LogState C × Bool)
    (F : α × (LogState C × Bool) → ℝ≥0∞),
    wp ((simulateQ (flagWorld prims D parts) oa).run s) F =
      wp ($ᵗ (C.Term → HashOutput)) fun seed => wp ((simulateQ (interWorld prims D parts seed) oa).run s) F := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s F; simp
  | query_bind t k ih =>
    intro s F
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self,
      StateT.run_bind, wp_bind]
    simp only [ih]
    by_cases hC : ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T ∧ s.1.1.1 q = none
    · obtain ⟨q, T, rfl, hT, hc⟩ := hC
      have hq := (hiddenTermOf_some D parts hT).2
      rw [flagWorld_freeHidden prims D parts (hiddenCell_of_some D parts hT)]
      simp only [interWorld_some prims D parts _ hT, hc, wp_bind, wp_pure, id]
      refine Eq.trans ?_ (wp_uniform_update T (fun seed => wp ((simulateQ (interWorld prims D parts seed)
        (k (seed T))).run (((s.1.1.1.cacheQuery q (seed T), s.1.1.2), s.1.2), s.2)) F)).symm
      refine congrArg _ (funext fun u => congrArg _ (funext fun g => ?_))
      simp only [Function.update_self]
      refine (wp_interWorld_update prims D parts g T u _ _ ?_ F).symm
      rw [← hq]
      simp [QueryCache.cacheQuery]
    · have e : ∀ seed, (interWorld prims D parts seed t).run s = (flagWorld prims D parts t).run s := fun seed => by
        by_cases ht : ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T
        · obtain ⟨q, T, rfl, hT⟩ := ht
          obtain ⟨v, hv⟩ : ∃ v, s.1.1.1 q = some v := by
            rcases hc : s.1.1.1 q with _ | v
            · exact absurd ⟨q, T, rfl, hT, hc⟩ hC
            · exact ⟨v, rfl⟩
          rw [interWorld_some prims D parts _ hT, flagWorld_freeHidden prims D parts (hiddenCell_of_some D parts hT)]
          simp only [hv]
        · rw [interWorld_of_ne prims D parts _ t fun q e => by
            rcases hq : hiddenTermOf D parts q with _ | T
            · rfl
            · exact absurd ⟨q, T, e, hq⟩ ht]
      simp only [e]
      exact (DkgSecurityProof.wp_swap _ _ _).symm

end Lazy

/-! ## The world with the seeds against the comparison world -/

section Dominated

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

/-- The state of the comparison world, namely the world state with no hidden cell. -/
def toComp (s : LogState C × Bool) : LogState C := eraseLog D parts s.1

/-- With no touch, each hidden cell is empty or holds the seed of its hidden term. -/
def SeedInv (s : LogState C × Bool) : Prop :=
  s.2 = false → ∀ q T, hiddenTermOf D parts q = some T → s.1.1.1 q = none ∨ s.1.1.1 q = some (seed T)

/-- The flag is up. -/
def Raised (s : LogState C × Bool) : Prop := s.2 = true

theorem compWorld_of_ne (t : (WorldSpec C).Domain)
    (ht : ∀ q, t = .inr (.inr (.inl q)) → hiddenTermOf D parts q = none) :
    compWorld prims D parts seed t = loggedWorld prims D t := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  all_goals try rfl
  simp only [compWorld, ht q rfl]

theorem compWorld_some {q : Query C} {T : C.Term} (hT : hiddenTermOf D parts q = some T) :
    compWorld prims D parts seed (.inr (.inr (.inl q))) = pure (seed T) := by
  simp only [compWorld, hT]

theorem not_freeHidden_of_ne {t : (WorldSpec C).Domain}
    (ht : ∀ q, t = .inr (.inr (.inl q)) → hiddenTermOf D parts q = none) : ¬ FreeHidden D parts t := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  all_goals try exact id
  exact hiddenTermOf_none D parts (ht q rfl)

theorem ne_of_not_some {t : (WorldSpec C).Domain}
    (ht : ¬ ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T) :
    ∀ q, t = .inr (.inr (.inl q)) → hiddenTermOf D parts q = none := fun q e => by
  rcases hq : hiddenTermOf D parts q with _ | T
  · rfl
  · exact absurd ⟨q, T, e, hq⟩ ht

theorem interWorld_preservesInv : QueryImpl.PreservesInv (interWorld prims D parts seed) (SeedInv D parts seed) := by
  intro t s hs z hz
  by_cases ht : ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T
  · obtain ⟨q, T, rfl, hT⟩ := ht
    rw [interWorld_some prims D parts seed hT] at hz
    rcases hc : s.1.1.1 q with _ | v <;> rw [hc] at hz <;>
      simp only [support_pure, Set.mem_singleton_iff] at hz <;> subst hz
    · intro hb q' T' hT'
      by_cases hq : q' = q
      · subst hq
        rw [hT] at hT'
        cases hT'
        right
        simp [QueryCache.cacheQuery]
      · simp only [QueryCache.cacheQuery_of_ne _ _ hq]
        exact hs hb q' T' hT'
    · exact hs
  · have hne := ne_of_not_some D parts ht
    rw [interWorld_of_ne prims D parts seed t hne, flagWorld_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    intro hb q' T' hT'
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    have hk := loggedWorld_keep prims D parts t ⟨hb.2, not_freeHidden_of_ne D parts hne⟩ s.1 r hr q'
      (hiddenCell_of_some D parts hT')
    rw [hk]
    exact hs hb.1 q' T' hT'

theorem interWorld_preservesRaised : QueryImpl.PreservesInv (interWorld prims D parts seed) Raised := by
  intro t s hs z hz
  by_cases ht : ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T
  · obtain ⟨q, T, rfl, hT⟩ := ht
    rw [interWorld_some prims D parts seed hT] at hz
    rcases hc : s.1.1.1 q with _ | v <;> rw [hc] at hz <;>
      simp only [support_pure, Set.mem_singleton_iff] at hz <;> subst hz <;> exact hs
  · rw [interWorld_of_ne prims D parts seed t (ne_of_not_some D parts ht), flagWorld_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨r, -, rfl⟩ := hz
    simp [Raised, show s.2 = true from hs]

theorem interWorld_dominated : QueryImpl.DominatedUntilBad (interWorld prims D parts seed)
    (compWorld prims D parts seed) (toComp D parts) (SeedInv D parts seed) Raised := by
  intro t s hs hb Q
  have hb' : s.2 = false := by simpa [Raised] using hb
  by_cases ht : ∃ q T, t = .inr (.inr (.inl q)) ∧ hiddenTermOf D parts q = some T
  · obtain ⟨q, T, rfl, hT⟩ := ht
    rw [interWorld_some prims D parts seed hT, compWorld_some prims D parts seed hT]
    rcases hs hb' q T hT with hc | hc
    · simp only [hc, StateT.run_pure]
      refine prEvent_pure_le_pure _ _ _ _ fun h => ?_
      have e : toComp D parts (((s.1.1.1.cacheQuery q (seed T), s.1.1.2), s.1.2), s.2) = toComp D parts s := by
        simp only [toComp, eraseLog, eraseHidden_cacheQuery_hidden D parts (hiddenCell_of_some D parts hT)]
      simpa [e] using h.1
    · simp only [hc, StateT.run_pure]
      exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
  · have hne := ne_of_not_some D parts ht
    rw [interWorld_of_ne prims D parts seed t hne, compWorld_of_ne prims D parts seed t hne, flagWorld_run]
    by_cases hT : Touch D parts t
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => h.2 ?_) bot_le
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨r, -, rfl⟩ := hz
      simp [Raised, hT]
    · have he := loggedWorld_erase prims D parts t ⟨hT, not_freeHidden_of_ne D parts hne⟩ s.1
      change Pr{let z ← _}[_] ≤ Pr{let z ← (loggedWorld prims D t).run (eraseLog D parts s.1)}[Q z]
      rw [he, prEvent_map, prEvent_map]
      exact prEvent_mono _ _ _ fun z h => h.1

end Dominated

/-! ## The bound on one suffix -/

section Suffix

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C)

/-- A counted call asks a PRF cell under the value of a hidden cell. -/
def CellAt (st : LogState C) : Prop :=
  ∃ q ∈ st.2, ∃ (T : C.Term) (v : HashOutput) (x : Point), ¬ KnownTo D.1 T ∧
    st.1.1 (hiddenInput parts T) = some v ∧ q = .prf v x

/-- A counted call asks a PRF cell under the seed of a hidden term. -/
def CompAt (seed : C.Term → HashOutput) (st : LogState C) : Prop :=
  ∃ q ∈ st.2, ∃ (T : C.Term) (x : Point), ¬ KnownTo D.1 T ∧ q = .prf (seed T) x

/-- A hidden cell has a value. -/
def startFlag (w : LogState C) : Bool := decide (∃ q, HiddenCell D parts q ∧ (w.1.1 q).isSome)

theorem eraseLog_of_startFlag {w : LogState C} (h : startFlag D parts w = false) : eraseLog D parts w = w := by
  obtain ⟨⟨c, hc⟩, log⟩ := w
  have h' : ∀ q, HiddenCell D parts q → c q = none := fun q hq => by
    by_contra hne
    simp only [startFlag, decide_eq_false_iff_not, not_exists, not_and] at h
    exact h q hq (Option.ne_none_iff_isSome.1 hne)
  refine Prod.ext (Prod.ext (QueryCache.ext fun q => ?_) rfl) rfl
  by_cases hq : HiddenCell D parts q
  · simp [eraseLog, eraseHidden, hq, h' q hq]
  · simp [eraseLog, eraseHidden, hq]

theorem seedInv_start (seed : C.Term → HashOutput) (w : LogState C) :
    SeedInv D parts seed (w, startFlag D parts w) := by
  intro hb q T hT
  left
  by_contra hne
  simp only [startFlag, decide_eq_false_iff_not, not_exists, not_and] at hb
  exact hb q (hiddenCell_of_some D parts hT) (Option.ne_none_iff_isSome.1 hne)

/-- Off a touch, a value of a hidden cell is the seed of a hidden term. -/
theorem compAt_of_cellAt (seed : C.Term → HashOutput) (s : LogState C × Bool) (hs : SeedInv D parts seed s)
    (hb : s.2 = false) (h : CellAt D parts s.1) : CompAt D seed (toComp D parts s) := by
  obtain ⟨q, hq, T, v, x, hT, hv, rfl⟩ := h
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, hiddenTermOf D parts (hiddenInput parts T) = some T₀ := by
    unfold hiddenTermOf
    split_ifs with h
    · exact ⟨_, rfl⟩
    · exact absurd ⟨T, hT, rfl⟩ h
  rcases hs hb _ T₀ hT₀ with hc | hc
  · rw [hc] at hv
    cases hv
  · rw [hc] at hv
    cases hv
    exact ⟨_, hq, T₀, x, (hiddenTermOf_some D parts hT₀).1, rfl⟩

/-- The hit under a hidden cell in `loggedWorld` is at most the mean hit under the seeds in
`compWorld` and the probability of a touch. -/
theorem cellAt_le {α : Type} (oa : OracleComp (WorldSpec C) α) (w : LogState C) :
    Pr{let z ← (simulateQ (loggedWorld prims D) oa).run w}[CellAt D parts z.2] ≤
      wp ($ᵗ (C.Term → HashOutput)) (fun seed =>
        Pr{let z ← (simulateQ (compWorld prims D parts seed) oa).run w}[CompAt D seed z.2]) +
      Pr{let z ← (simulateQ (flagWorld prims D parts) oa).run (w, startFlag D parts w)}[z.2.2 = true] := by
  rw [← flagWorld_proj prims D parts oa (w, startFlag D parts w), prEvent_map]
  refine (prEvent_mono _ _ (fun z => (CellAt D parts z.2.1 ∧ z.2.2 = false) ∨ z.2.2 = true) fun z h => ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  · cases hb : z.2.2
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr rfl
  rw [prEvent_eq_wp_indicator, wp_flagWorld_eq]
  refine wp_mono _ fun seed => ?_
  rw [← prEvent_eq_wp_indicator]
  cases hw : startFlag D parts w
  · have hinv := seedInv_start D parts seed w
    rw [hw] at hinv
    refine (prEvent_mono_of_support _ _ (fun z => CompAt D seed (toComp D parts z.2) ∧ ¬ Raised z.2)
      fun z hz h => ⟨compAt_of_cellAt D parts seed z.2
        (simulateQ_run_preservesInv _ _ (interWorld_preservesInv prims D parts seed) oa _ hinv z hz) h.2 h.1,
        by simp [Raised, h.2]⟩).trans ?_
    have hd := (interWorld_dominated prims D parts seed).prEvent_simulateQ_run_map_and_not_bad_le
      (interWorld_preservesInv prims D parts seed) (interWorld_preservesRaised prims D parts seed) oa _ hinv
      (fun z => CompAt D seed z.2)
    have e : toComp D parts (w, false) = w := eraseLog_of_startFlag D parts hw
    rw [e] at hd
    exact hd
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    have hr := simulateQ_run_preservesInv _ _ (interWorld_preservesRaised prims D parts seed) oa _
      (show Raised (w, true) from rfl) z hz
    simp [Raised, h.2] at hr

end Suffix

/-! ## The touch of a hidden cell and the glue to `SeedClose` -/

section Glue

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The game with the keys of the dealer and no emulated run, with the touch flag on the suffix. The
flag starts up when a hidden cell has a value at the end of the prefix. -/
def touchRun (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp (PrefixOut C A.net.State × (RunOut C × (LogState C × Bool))) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let z ← (simulateQ (flagWorld prims D x.1.2.2)
    (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1)).run (x.2, startFlag D x.1.2.2 x.2)
  pure (x.1, z)

/-- The touch of a hidden cell has at most the probability `compCloseError C q`. -/
def SeedTouch : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    (Pr{let r ← touchRun prims K circuits settings runLimit D A}[r.2.2.2 = true]).toReal ≤ compCloseError C q

omit [Fintype E] [DecidableEq E] in
theorem cellHit_le_compHit (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Pr{let z ← (simulateQ (loggedWorld prims D)
      (dealtPartsRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[CellHitOf D z] ≤
      Pr{let r ← compRun prims K circuits settings runLimit D A}[CompHitOf D r] +
        Pr{let r ← touchRun prims K circuits settings runLimit D A}[r.2.2.2 = true] := by
  rw [dealtPartsRun_split]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  unfold compRun touchRun
  simp only [DkgSecurityProof.prEvent_bind_wp]
  rw [← wp_add]
  refine wp_mono _ fun x => ?_
  have hc := cellAt_le prims D x.1.2.2 (dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1) x.2
  simp only [prEvent_eq_wp_indicator] at hc
  simp only [prEvent_pure]
  exact hc

omit [Fintype E] [DecidableEq E] in
/-- `SeedTouch` gives `SeedClose`. -/
theorem seedClose_of_touch (touch : SeedTouch prims K circuits settings runLimit) :
    SeedClose prims K circuits settings runLimit := by
  intro D A q bounded
  have h := cellHit_le_compHit prims K circuits settings runLimit D A
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h₁
  have h₂ := touch D A q bounded
  linarith

omit [Fintype E] [DecidableEq E] in
/-- `SeedTouch` and `CompHit` give `HitSeed`. -/
theorem hitSeed_of_touch (touch : SeedTouch prims K circuits settings runLimit)
    (hit : CompHit prims K circuits settings runLimit) : HitSeed prims K circuits settings runLimit :=
  hitSeed_of_compare prims K circuits settings runLimit (seedClose_of_touch prims K circuits settings runLimit touch) hit

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.seedClose_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.seedClose_of_touch

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.hitSeed_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.hitSeed_of_touch
