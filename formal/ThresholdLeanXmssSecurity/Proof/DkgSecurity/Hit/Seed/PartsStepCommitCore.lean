import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepDerive

/-!
# Designated reads in a private cache

A designated cell is a random-oracle cell whose free reads the world can move to a private cache.
`desWorld Des P` is `loggedWorld` with a flag that records each call with `P`, where a free call of `H`
at a designated cell takes its answer from the private cache. With no designated cell it is the shared
world.

* `wp_dropWrite` is the abstract lazy-sampling fact. A write of a fresh uniform value into an empty
  cell that no later call programs does not change the law of a function of the run that ignores the
  cell.
* `writeWorld Des P` is `desWorld Des P` where a free call at a designated cell also does the write of
  the shared world. `wp_writeWorld` states that the two worlds give one law of the result and of the
  flag (hop A).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_mono)
open ThresholdLeanXmssSecurity.DkgSecurityProof (mainCell loggedWorld_freeHash loggedWorld_countedHash)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## A fresh write that nobody reads first -/

section Drop

/-- A write of a fresh uniform value by `put` into a state with `Unset` does not change the law of a
function `F` of the run that ignores the write. Each call that reads the written place samples it when
it is empty, a call with `Prog` is absent, and each other call commutes with the write and keeps
`Unset`. -/
theorem wp_dropWrite {ι σ V α : Type} {spec : OracleSpec ι} [SampleableType V] (impl : QueryImpl spec (StateT σ ProbComp))
    (put : σ → V → σ) (Unset : σ → Prop) (Reads Prog : ι → Prop)
    (hframe : ∀ t, ¬ Reads t → ¬ Prog t → ∀ s u, Unset s →
      (impl t).run (put s u) = (fun z => (z.1, put z.2 u)) <$> (impl t).run s)
    (hkeep : ∀ t, ¬ Reads t → ¬ Prog t → ∀ s, Unset s → ∀ z ∈ support ((impl t).run s), Unset z.2)
    (hread : ∀ t, Reads t → ∀ s, Unset s → (impl t).run s = ($ᵗ V) >>= fun u => (impl t).run (put s u))
    (F : α × σ → ℝ≥0∞) (hF : ∀ a s u, Unset s → F (a, put s u) = F (a, s)) (oa : OracleComp spec α)
    (hoa : NoCall Prog oa) :
    ∀ s, Unset s → wp ($ᵗ V) (fun u => wp ((simulateQ impl oa).run (put s u)) F) = wp ((simulateQ impl oa).run s) F := by
  rw [noCall_iff] at hoa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs
    simp only [simulateQ_pure, StateT.run_pure, wp_pure, hF a s _ hs, wp_const]
  | query_bind t k ih =>
    intro s hs
    rw [isQueryBoundP_query_bind_iff] at hoa
    obtain ⟨ht, hk⟩ := hoa
    have ht' : ¬ Prog t := by simpa using ht
    have hk' : ∀ u, (k u).IsQueryBoundP Prog 0 := fun u => by simpa [ht'] using hk u
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM,
      monadLift_self, wp_bind]
    by_cases hr : Reads t
    · rw [hread t hr s hs, wp_bind]
    · simp only [hframe t hr ht' s _ hs, wp_map, Function.comp_def]
      rw [DkgSecurityProof.wp_swap]
      exact wp_congr_of_support _ fun z hz => ih z.1 (hk' z.1) z.2 (hkeep t hr ht' s hs z hz)

end Drop

/-! ## The worlds with designated cells -/

section Worlds

variable (prims : Primitives) (D : C.Coalition)

/-- `loggedWorld` with a flag that records each call with `P`, where a free call of `H` at a cell with
`Des` takes its answer from the private cache and leaves the world as it is. -/
def desWorld (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) :
    QueryImpl (WorldSpec C) (StateT (PairState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if Des q then StateT.mk fun s =>
        (fun r => (r.1, (s.1, r.2, s.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s.2.1
      else StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$>
        (loggedWorld prims D (.inr (.inr (.inl q)))).run s.1
  | t => StateT.mk fun s =>
      (fun r => (r.1, (r.2, s.2.1, s.2.2 || decide (P t)))) <$> (loggedWorld prims D t).run s.1

/-- `desWorld` where a free call of `H` at a cell with `Des` also writes the shared cache as the shared
world does, and then takes its answer from the private cache. -/
def writeWorld (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) :
    QueryImpl (WorldSpec C) (StateT (PairState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if Des q then StateT.mk fun s => do
        let a ← ((Query C →ₒ HashOutput).randomOracle q).run s.1.1.1
        let r ← ((Query C →ₒ HashOutput).randomOracle q).run s.2.1
        pure (r.1, (((a.2, s.1.1.2), s.1.2), r.2, s.2.2))
      else desWorld prims D Des P (.inr (.inr (.inl q)))
  | t => desWorld prims D Des P t

theorem pairWorld_eq_desWorld (X : Query C) : pairWorld prims D X = desWorld prims D (PairCell D) (TouchAt X) := by
  funext t
  rcases t with ((u | q | x) | p) | (u | q | x) <;> rfl

theorem desWorld_des (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) {q : Query C} (hq : Des q)
    (s : PairState C) :
    (desWorld prims D Des P (.inr (.inr (.inl q)))).run s =
      (fun r => (r.1, (s.1, r.2, s.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s.2.1 := by
  simp only [desWorld, hq, ite_true, StateT.run_mk]

theorem desWorld_free (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) {q : Query C} (hq : ¬ Des q)
    (s : PairState C) :
    (desWorld prims D Des P (.inr (.inr (.inl q)))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (loggedWorld prims D (.inr (.inr (.inl q)))).run s.1 := by
  simp only [desWorld, hq, ite_false, StateT.run_mk]

theorem desWorld_other (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) (t : (WorldSpec C).Domain)
    (h : ∀ q, t ≠ .inr (.inr (.inl q))) (s : PairState C) :
    (desWorld prims D Des P t).run s =
      (fun r => (r.1, (r.2, s.2.1, s.2.2 || decide (P t)))) <$> (loggedWorld prims D t).run s.1 := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  exact absurd rfl (h q)

theorem writeWorld_des (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) {q : Query C} (hq : Des q)
    (s : PairState C) :
    (writeWorld prims D Des P (.inr (.inr (.inl q)))).run s = (do
      let a ← ((Query C →ₒ HashOutput).randomOracle q).run s.1.1.1
      let r ← ((Query C →ₒ HashOutput).randomOracle q).run s.2.1
      pure (r.1, (((a.2, s.1.1.2), s.1.2), r.2, s.2.2))) := by
  simp only [writeWorld, hq, ite_true, StateT.run_mk]

theorem writeWorld_of_not (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop) (t : (WorldSpec C).Domain)
    (h : ∀ q, t = .inr (.inr (.inl q)) → ¬ Des q) : writeWorld prims D Des P t = desWorld prims D Des P t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  simp only [writeWorld, h q rfl, ite_false]

end Worlds

/-! ## Hop A, the write of the shared world at a designated read -/

section HopA

variable (prims : Primitives) (D : C.Coalition) (Des : Query C → Prop) (P : (WorldSpec C).Domain → Prop)

/-- A programming call at a designated cell. -/
def ProgDes (Des : Query C → Prop) : (WorldSpec C).Domain → Prop := fun t => ∃ p, t = .inl (.inr p) ∧ Des p.1

/-- The facts on the designated cells that the hops use. -/
structure DesFacts (Des : Query C → Prop) : Prop where
  not_fixed : ∀ q, Des q → ¬ IsFixed q
  not_stream : ∀ q, Des q → ∀ k, q ≠ .streamKey k

/-- The world state with the entry `o` at the cell `c`, and the same private cache and flag. -/
def putState (c : Query C) (o : Option HashOutput) (s : PairState C) : PairState C := (putLog c o s.1, s.2)

theorem cacheQuery_eq_putAt {c : Query C} {cache : HashCache C} (h : cache c = none) (u : HashOutput) :
    cache.cacheQuery c u = putAt c (some u) cache := by
  rw [← putAt_none_cacheQuery, putAt_of_none c h]

/-- A call that asks no `c` commutes with the entry `o` at `c` in `writeWorld`. -/
theorem writeWorld_putState (hD : DesFacts Des) {c : Query C} (hc : Des c) (o : Option HashOutput)
    (t : (WorldSpec C).Domain) (h : ∀ q, mainCell t = some q → q ≠ c) (s : PairState C) :
    (writeWorld prims D Des P t).run (putState c o s) =
      (fun z => (z.1, putState c o z.2)) <$> (writeWorld prims D Des P t).run s := by
  have hX : ∀ k, c ≠ .streamKey k := hD.not_stream c hc
  by_cases hfree : ∃ q, t = .inr (.inr (.inl q))
  · obtain ⟨q, rfl⟩ := hfree
    have hq : q ≠ c := h q rfl
    by_cases hd : Des q
    · rw [writeWorld_des prims D Des P hd, writeWorld_des prims D Des P hd]
      simp only [putState, putLog]
      rw [randomOracle_putAt c hq]
      simp only [bind_map_left, map_bind, map_pure]
    · rw [writeWorld_of_not prims D Des P _ (fun q' e => by cases e; exact hd),
        desWorld_free prims D Des P hd, desWorld_free prims D Des P hd]
      simp only [putState]
      rw [loggedWorld_putLog c prims D hX o _ h, Functor.map_map, Functor.map_map]
  · push Not at hfree
    rw [writeWorld_of_not prims D Des P _ (fun q e => absurd e (hfree q)),
      desWorld_other prims D Des P t hfree, desWorld_other prims D Des P t hfree]
    simp only [putState]
    rw [loggedWorld_putLog c prims D hX o _ h, Functor.map_map, Functor.map_map]

/-- A read of `c` from an empty `c` samples the value of `c` first. -/
theorem writeWorld_read (hD : DesFacts Des) {c : Query C} (hc : Des c) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr (.inl c))) ∨ t = .inr (.inr (.inl c))) (s : PairState C) (hs : s.1.1.1 c = none) :
    (writeWorld prims D Des P t).run s =
      ($ᵗ HashOutput) >>= fun u => (writeWorld prims D Des P t).run (putState c (some u) s) := by
  have hfix := hD.not_fixed c hc
  have e : ∀ (u : HashOutput) (cache : HashCache C),
      ((Query C →ₒ HashOutput).randomOracle c).run (putAt c (some u) cache) = pure (u, putAt c (some u) cache) := by
    intro u cache
    rw [randomOracle.run_eq, putAt_self]
  rcases ht with rfl | rfl
  · rw [writeWorld_of_not prims D Des P _ (fun q e => by cases e),
      desWorld_other prims D Des P (.inl (.inl (.inr (.inl c)))) (fun q e => by cases e)]
    simp only [desWorld_other prims D Des P (.inl (.inl (.inr (.inl c)))) (fun q e => by cases e),
      loggedWorld_countedHash, hashAnswer_of_not_isFixed prims hfix, putState, putLog, e]
    rw [randomOracle.run_eq, hs]
    simp only [map_bind, map_pure, cacheQuery_eq_putAt hs]
  · simp only [writeWorld_des prims D Des P hc, putState, putLog, e, pure_bind]
    rw [randomOracle.run_eq _ s.1.1.1, hs]
    simp only [bind_assoc, pure_bind, cacheQuery_eq_putAt hs]

theorem putState_of_none {c : Query C} {s : PairState C} (h : s.1.1.1 c = none) : putState c none s = s := by
  obtain ⟨⟨⟨cache, hidden⟩, log⟩, rest⟩ := s
  simp only [putState, putLog]
  rw [putAt_of_none c h]

theorem mainCell_ne_of {c : Query C} (t : (WorldSpec C).Domain)
    (hr : ¬ (t = .inl (.inl (.inr (.inl c))) ∨ t = .inr (.inr (.inl c)))) (hp : ¬ ∃ p, t = .inl (.inr p) ∧ p.1 = c) :
    ∀ q, mainCell t = some q → q ≠ c := by
  intro q hq e
  subst e
  rcases t with ((u | q' | x) | p) | (u | q' | x)
  all_goals simp only [mainCell, reduceCtorEq, Option.some.injEq] at hq
  · subst hq
    exact hr (Or.inl rfl)
  · exact hp ⟨p, rfl, hq⟩
  · subst hq
    exact hr (Or.inr rfl)

/-- Dropping one fresh write of a designated cell in `writeWorld` keeps the law of the result and the
flag. -/
theorem wp_writeWorld_drop (hD : DesFacts Des) {c : Query C} (hc : Des c) {α : Type} (G : α → Bool → ℝ≥0∞)
    (oa : OracleComp (WorldSpec C) α) (hoa : NoCall (ProgDes Des) oa) (s : PairState C) (hs : s.1.1.1 c = none) :
    wp ($ᵗ HashOutput) (fun u => wp ((simulateQ (writeWorld prims D Des P) oa).run (putState c (some u) s))
      (fun z => G z.1 z.2.2.2)) =
      wp ((simulateQ (writeWorld prims D Des P) oa).run s) (fun z => G z.1 z.2.2.2) := by
  refine wp_dropWrite (writeWorld prims D Des P) (fun s u => putState c (some u) s) (fun s => s.1.1.1 c = none)
    (fun t => t = .inl (.inl (.inr (.inl c))) ∨ t = .inr (.inr (.inl c))) (fun t => ∃ p, t = .inl (.inr p) ∧ p.1 = c)
    (fun t hr hp s u _ => writeWorld_putState prims D Des P hD hc _ t (mainCell_ne_of t hr hp) s)
    (fun t hr hp s hs z hz => ?_) (fun t hr s hs => writeWorld_read prims D Des P hD hc t hr s hs) _
    (fun _ _ _ _ => rfl) oa (noCall_mono _ (fun t ⟨p, e, hp⟩ => ⟨p, e, hp ▸ hc⟩) hoa) s hs
  rw [← putState_of_none hs, writeWorld_putState prims D Des P hD hc none t (mainCell_ne_of t hr hp)] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨z', _, rfl⟩ := hz
  simp [putState, putLog, putAt_self]

/-- The first hop. `writeWorld` and `desWorld` give one law of the result and the flag, from each state, for a
program with no programming call at a designated cell. -/
theorem wp_writeWorld (hD : DesFacts Des) {α : Type} (G : α → Bool → ℝ≥0∞) (oa : OracleComp (WorldSpec C) α)
    (hoa : NoCall (ProgDes Des) oa) : ∀ s : PairState C,
    wp ((simulateQ (writeWorld prims D Des P) oa).run s) (fun z => G z.1 z.2.2.2) =
      wp ((simulateQ (desWorld prims D Des P) oa).run s) (fun z => G z.1 z.2.2.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; rfl
  | query_bind t k ih =>
    intro s
    have hoa' := hoa
    rw [noCall_iff, isQueryBoundP_query_bind_iff] at hoa'
    obtain ⟨ht, hk⟩ := hoa'
    have ht' : ¬ ProgDes Des t := by simpa using ht
    have hk' : ∀ u, NoCall (ProgDes Des) (k u) := fun u => by rw [noCall_iff]; simpa [ht'] using hk u
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM,
      monadLift_self, wp_bind]
    by_cases hdes : ∃ q, t = .inr (.inr (.inl q)) ∧ Des q
    · obtain ⟨q, rfl, hq⟩ := hdes
      rw [writeWorld_des prims D Des P hq, desWorld_des prims D Des P hq, randomOracle.run_eq _ s.1.1.1]
      cases hc : s.1.1.1 q with
      | some v =>
        simp only [pure_bind, wp_bind, wp_pure, wp_map, Function.comp_def, id, Prod.mk.eta]
        exact congrArg _ (funext fun (r : HashOutput × HashCache C) => ih r.1 (hk' r.1) _)
      | none =>
        simp only [bind_assoc, pure_bind, wp_bind, wp_pure, wp_map, Function.comp_def, id]
        rw [DkgSecurityProof.wp_swap]
        refine congrArg _ (funext fun (r : HashOutput × HashCache C) => ?_)
        have hdrop := wp_writeWorld_drop prims D Des P hD hq G (k r.1) (hk' r.1) (s.1, r.2, s.2.2) hc
        simp only [putState, putLog] at hdrop
        rw [← ih r.1 (hk' r.1), ← hdrop]
        refine congrArg _ (funext fun u => ?_)
        rw [cacheQuery_eq_putAt hc]
    · have e : writeWorld prims D Des P t = desWorld prims D Des P t :=
        writeWorld_of_not prims D Des P t fun q e hq => hdes ⟨q, e, hq⟩
      rw [e]
      exact congrArg _ (funext fun z => ih z.1 (hk' z.1) z.2)

end HopA

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps
