import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Events

/-!
# The translation of the hidden streams

`shiftQ D σ oa` is the program `oa` where each free read of a stream under a hidden key name sees its
answer plus `σ` at the cell of the read. `shiftQ_run` states that the run of `shiftQ D σ oa` in
`loggedWorld` from the shifted start has the law of the run of `oa`, with the hidden table of the end
shifted by `σ`.

`shiftRo D σ` is the same translation on the oracles of the local hash and stream.
`shiftQ_free_liftComp` moves the translation of a program on the free copy to the local oracles, and
`shiftRo_prgBits` gives the translation of the bits of one stream.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- A cell of the hidden table. -/
abbrev HiddenCell (C : Committee) := (KeyName C × HashOutput) × ℕ × ℕ × ℕ

/-- The cell of a read of a stream. -/
def streamCell (x : PrgInput C) : HiddenCell C := ((x.1, x.2.1), x.2.2)

/-- The hidden table with the value of each cell `c` plus `σ c`. -/
def shiftCache (σ : HiddenCell C → Bit) (hidden : HiddenCache C) : HiddenCache C :=
  QueryCache.ofFn fun c => (hidden c).map (· + σ c)

@[simp] theorem shiftCache_apply (σ : HiddenCell C → Bit) (hidden : HiddenCache C) (c : HiddenCell C) :
    shiftCache σ hidden c = (hidden c).map (· + σ c) := rfl

/-- The state of `loggedWorld` with the hidden table shifted by `σ`. -/
def shiftState (σ : HiddenCell C → Bit) (s : LogState C) : LogState C :=
  ((s.1.1, shiftCache σ s.1.2), s.2)

/-- Each free read of a stream under a hidden key name adds `σ` at its cell to the answer. -/
def shiftImpl (D : C.Coalition) (σ : HiddenCell C → Bit) : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) :=
  fun t => match t with
  | .inr (.inr (.inr x)) =>
      if Hidden D x.1 then
        ((fun b : Bit => b + σ (streamCell x)) <$> (query (spec := WorldSpec C) (.inr (.inr (.inr x))) :
          OracleComp (WorldSpec C) Bit))
      else query (spec := WorldSpec C) (.inr (.inr (.inr x)))
  | t => query (spec := WorldSpec C) t

/-- The program `oa` with the hidden streams translated by `σ`. -/
def shiftQ (D : C.Coalition) (σ : HiddenCell C → Bit) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    OracleComp (WorldSpec C) α :=
  simulateQ (shiftImpl D σ) oa

theorem shiftState_shiftState (σ : HiddenCell C → Bit) (s : LogState C) : shiftState σ (shiftState σ s) = s := by
  obtain ⟨⟨h, hidden⟩, log⟩ := s
  simp only [shiftState]
  congr
  refine QueryCache.ext fun c => ?_
  simp only [shiftCache_apply]
  cases hidden c <;> simp [add_assoc, CharTwo.add_self_eq_zero]

/-- The shift does not change a start whose hidden table has no cell where `σ` is not zero. -/
theorem shiftState_eq_self (σ : HiddenCell C → Bit) (s : LogState C)
    (h : ∀ c, σ c ≠ 0 → s.1.2 c = none) : shiftState σ s = s := by
  obtain ⟨⟨hc, hidden⟩, log⟩ := s
  simp only [shiftState]
  congr
  refine QueryCache.ext fun c => ?_
  simp only [shiftCache_apply]
  by_cases hσ : σ c = 0
  · cases hidden c <;> simp [hσ]
  · have hn : hidden c = none := h c hσ
    simp [hn]

section Run

variable (prims : Primitives) (D : C.Coalition)

/-- A query that is no free read of a stream under a hidden key name does not read or write the
hidden table. -/
theorem loggedWorld_run_shiftState (σ : HiddenCell C → Bit) (t : (WorldSpec C).Domain)
    (ht : ∀ x, t = .inr (.inr (.inr x)) → ¬ Hidden D x.1) (s : LogState C) :
    (loggedWorld prims D t).run (shiftState σ s) =
      (fun z => (z.1, shiftState σ z.2)) <$> (loggedWorld prims D t).run s := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [loggedWorld, streamWorld, onHash, shiftState, StateT.run_mk, Functor.map_map]
  have hx := ht x rfl
  simp only [hx, ite_false, StateT.run_mk, Functor.map_map]

/-- A free read of a stream under a hidden key name is the lazy random function at its cell. -/
theorem loggedWorld_run_hidden (x : PrgInput C) (hx : Hidden D x.1) (s : LogState C) :
    (loggedWorld prims D (.inr (.inr (.inr x)))).run s =
      match s.1.2 (streamCell x) with
      | some v => pure (v, s)
      | none => ($ᵗ Bit) >>= fun u => pure (u, ((s.1.1, s.1.2.cacheQuery (streamCell x) u), s.2)) := by
  simp only [loggedWorld, streamWorld, hx, ite_true, StateT.run_mk, Functor.map_map, randomOracle.run_eq]
  have hc : countedCells (C := C) (.inr (.inr (.inr x))) = [] := rfl
  rw [hc, List.append_nil]
  change _ = match s.1.2 ((x.1, x.2.1), x.2.2) with
    | some v => pure (v, s)
    | none => ($ᵗ Bit) >>= fun u => pure (u, ((s.1.1, s.1.2.cacheQuery ((x.1, x.2.1), x.2.2) u), s.2))
  cases s.1.2 ((x.1, x.2.1), x.2.2) with
  | some v => simp
  | none => simp

theorem shiftImpl_of_not_hidden (σ : HiddenCell C → Bit) (t : (WorldSpec C).Domain)
    (ht : ∀ x, t = .inr (.inr (.inr x)) → ¬ Hidden D x.1) :
    shiftImpl D σ t = query (spec := WorldSpec C) t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals try rfl
  simp only [shiftImpl, ht x rfl, ite_false]

theorem shiftCache_cacheQuery (σ : HiddenCell C → Bit) (hidden : HiddenCache C) (c : HiddenCell C) (v : Bit) :
    shiftCache σ (hidden.cacheQuery c v) = (shiftCache σ hidden).cacheQuery c (v + σ c) := by
  refine QueryCache.ext fun c' => ?_
  by_cases h : c' = c
  · subst h
    simp
  · simp [QueryCache.cacheQuery_of_ne _ _ h]

/-- The translation lemma. The run of `oa` with the hidden streams translated by `σ`, from the
start `s` shifted by `σ`, has the law of the run of `oa` from `s`, with the end shifted by `σ`. -/
theorem shiftQ_run (σ : HiddenCell C → Bit) {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LogState C) :
    (simulateQ (loggedWorld prims D) (shiftQ D σ oa)).run (shiftState σ s) =ᵈ
      (fun z => (z.1, shiftState σ z.2)) <$> (simulateQ (loggedWorld prims D) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp [shiftQ]
  | query_bind t k ih =>
    by_cases h : ∃ x, t = .inr (.inr (.inr x)) ∧ Hidden D x.1
    · obtain ⟨x, rfl, hx⟩ := h
      simp only [shiftQ, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
        id_map] at ih ⊢
      have himpl : shiftImpl D σ (.inr (.inr (.inr x))) =
          (fun b : Bit => b + σ (streamCell x)) <$> (query (spec := WorldSpec C) (.inr (.inr (.inr x))) :
            OracleComp (WorldSpec C) Bit) := by
        simp only [shiftImpl, hx, ite_true]
      rw [himpl, simulateQ_map, simulateQ_HasQuery_query]
      simp only [StateT.run_bind, bind_map_left]
      rw [loggedWorld_run_hidden prims D x hx, loggedWorld_run_hidden prims D x hx]
      have hs : (shiftState σ s).1.2 (streamCell x) = (s.1.2 (streamCell x)).map (· + σ (streamCell x)) := rfl
      rw [hs]
      cases hv : s.1.2 (streamCell x) with
      | some v =>
        simp only [Option.map_some, pure_bind]
        rw [show v + σ (streamCell x) + σ (streamCell x) = v by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]]
        exact ih v s
      | none =>
        simp only [Option.map_none, bind_assoc, pure_bind, map_bind]
        have hst : ∀ u : Bit, (((shiftState σ s).1.1, (shiftState σ s).1.2.cacheQuery (streamCell x) u),
            (shiftState σ s).2) = shiftState σ ((s.1.1, s.1.2.cacheQuery (streamCell x) (u + σ (streamCell x))), s.2) := by
          intro u
          simp only [shiftState, shiftCache_cacheQuery, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        simp only [hst]
        refine (EvalDistEq.bind_right _ fun u => ih (u + σ (streamCell x)) _).trans ?_
        convert evalDist_bind_add_uniform (σ (streamCell x)) (fun u => (fun z => (z.1, shiftState σ z.2)) <$>
          (simulateQ (loggedWorld prims D) (k u)).run ((s.1.1, s.1.2.cacheQuery (streamCell x) u), s.2)) using 2
    · have ht : ∀ x, t = .inr (.inr (.inr x)) → ¬ Hidden D x.1 := fun x hxt hx => h ⟨x, hxt, hx⟩
      simp only [shiftQ, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
        id_map] at ih ⊢
      rw [shiftImpl_of_not_hidden D σ t ht, simulateQ_HasQuery_query]
      simp only [StateT.run_bind, loggedWorld_run_shiftState prims D σ t ht, bind_map_left, map_bind]
      exact EvalDistEq.bind_right _ fun z => ih z.1 z.2

end Run

/-! ## The translation of the draws of an operator -/

section Draws

variable (D : C.Coalition)

/-- Each read of a stream under a hidden key name adds `σ` at its cell to the answer, on the oracles of
the local hash and stream. -/
def shiftRo (D : C.Coalition) (σ : HiddenCell C → Bit) : QueryImpl (RoSpec C) (OracleComp (RoSpec C)) :=
  fun t => match t with
  | .inr x =>
      if Hidden D x.1 then
        ((fun b : Bit => b + σ (streamCell x)) <$>
          (liftM (OracleSpec.query (spec := RoSpec C) (.inr x)) : OracleComp (RoSpec C) Bit))
      else liftM (OracleSpec.query (spec := RoSpec C) (.inr x))
  | t => liftM (OracleSpec.query (spec := RoSpec C) t)

theorem shiftQ_bind (σ : HiddenCell C → Bit) {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (f : α → OracleComp (WorldSpec C) β) : shiftQ D σ (oa >>= f) = shiftQ D σ oa >>= fun a => shiftQ D σ (f a) :=
  simulateQ_bind _ _ _

theorem shiftQ_free_liftComp (σ : HiddenCell C → Bit) {α : Type} (X : OracleComp (RoSpec C) α) :
    shiftQ D σ (free (liftComp X (LocalSpec C))) = free (liftComp (simulateQ (shiftRo D σ) X) (LocalSpec C)) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp [shiftQ]
  | query_bind t k ih =>
    have hq : ∀ {γ : Type} (g : (RoSpec C).Range t → OracleComp (RoSpec C) γ),
        free (liftComp (liftM (OracleSpec.query t) >>= g) (LocalSpec C)) =
          (liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr t))) : OracleComp (WorldSpec C) _) >>= fun u =>
            free (liftComp (g u) (LocalSpec C)) := by
      intro γ g
      rw [liftComp_bind, free_bind]
      rcases t with _ | _ <;> rfl
    rw [hq, simulateQ_bind, liftComp_bind, free_bind, shiftQ_bind]
    simp only [ih]
    rw [shiftQ, simulateQ_spec_query]
    rcases t with q | x
    · rfl
    · by_cases h : Hidden D x.1
      · simp only [shiftImpl, shiftRo, h, ite_true, simulateQ_map, simulateQ_spec_query, liftComp_map, free,
          bind_map_left]
        rfl
      · simp only [shiftImpl, shiftRo, h, ite_false, simulateQ_spec_query]
        rfl


/-- The list `x :: F` as a function of the position. -/
def consFn {M : Type} (x : M) (F : ℕ → M) : ℕ → M := fun g => match g with
  | 0 => x
  | g + 1 => F g

theorem getD_cons_eq_consFn {M : Type} (x : M) (xs : List M) (d : M) :
    (fun g => (x :: xs).getD g d) = consFn x fun g => xs.getD g d := by
  funext g
  cases g <;> rfl

/-- A list of reads, each with its own translation, read as a function of the position. -/
theorem map_getD_mapM_add {ι : Type} {spec : OracleSpec ι} {M β : Type} [AddMonoid M] (l : List β)
    (q : β → OracleComp spec M) (s : β → M) :
    (fun xs => fun g => xs.getD g 0) <$> (l.mapM fun b => (· + s b) <$> q b) =
      (fun xs => fun g => xs.getD g 0 + (l.map s).getD g 0) <$> l.mapM q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mapM_cons, map_bind, bind_map_left, map_pure]
    refine bind_congr fun b => ?_
    have hl := congrArg (· >>= fun F => (pure (consFn (b + s a) F) : OracleComp spec (ℕ → M))) ih
    simp only [bind_map_left] at hl
    simp only [getD_cons_eq_consFn, List.map_cons]
    refine hl.trans (bind_congr fun xs => ?_)
    congr 1
    funext g
    cases g <;> rfl


/-- The translation that `σ` gives to the bits `prgBits name key ρ idx count`. -/
def prgShift (D : C.Coalition) (σ : HiddenCell C → Bit) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    ℕ → Bit :=
  fun g => if Hidden D name ∧ g < count then σ ((name, key), ρ, idx, g) else 0

theorem shiftRo_prgBits (σ : HiddenCell C → Bit) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    simulateQ (shiftRo D σ) (prgBits name key ρ idx count) =
      (fun f => f + prgShift D σ name key ρ idx count) <$> prgBits name key ρ idx count := by
  let q : ℕ → OracleComp (RoSpec C) Bit := fun position =>
    liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)))
  let s : ℕ → Bit := fun position => if Hidden D name then σ ((name, key), ρ, idx, position) else 0
  have hp : prgBits name key ρ idx count = (fun xs => fun g => xs.getD g 0) <$> (List.range count).mapM q := by
    rw [map_eq_bind_pure_comp]
    rfl
  have hm : simulateQ (shiftRo D σ) ((List.range count).mapM q) =
      (List.range count).mapM fun position => (· + s position) <$> q position := by
    erw [simulateQ_list_mapM]
    congr 1
    funext position
    rw [simulateQ_spec_query]
    by_cases hn : Hidden D name
    · simp only [shiftRo, hn, ite_true, s]
      rfl
    · simp only [shiftRo, hn, ite_false, s, add_zero]
      simp only [id_map']
      rfl
  rw [hp, simulateQ_map, hm, map_getD_mapM_add, Functor.map_map]
  congr 1
  funext xs g
  simp only [Pi.add_apply, RealNetworkN3.getD_map_range, prgShift, s]
  by_cases hn : Hidden D name <;> by_cases hg : g < count <;> simp [hn, hg]

end Draws

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.shiftQ_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.shiftQ_run
