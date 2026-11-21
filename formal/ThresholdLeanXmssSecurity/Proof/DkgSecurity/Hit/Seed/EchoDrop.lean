import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoMid

/-!
# A fresh value at an unread cell, and the drop of free reads

* `stepShape` states that each call of `compWorld` that is no programming call is a call of `hashAnswer` at
  one cell with the hidden cache and a new log fixed, or a call that reads no cell of the hash cache.
* `freshDrop` states that a world program with no programming call has one law of the result and the log
  from a cache, and from the cache with a fresh value at a cell that has no value and is no cell of `Th`.
* `tailDrop` proves `TailDrop`. Each call of the free program is a draw, a fixed answer, a cached answer
  or a fresh value at a cell with no value, and its answer is forgotten.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

section Shape

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

/-- Each call of `compWorld` that is no programming call is a call of `hashAnswer` at one cell, with the
hidden cache and a new log fixed, or a call that reads and writes no cell of the hash cache. -/
theorem stepShape (t : (WorldSpec C).Domain) (ht : ¬ DkgCorrectnessProof.WorldProgramQuery t) (h : HiddenCache C)
    (l : List (Query C)) :
    (∃ (q' : Query C) (f : HashOutput → (WorldSpec C).Range t) (l' : List (Query C)), ∀ c,
      (compWorld prims D parts seed t).run ((c, h), l) =
        (fun z => (f z.1, ((z.2, h), l'))) <$> (hashAnswer prims q').run c) ∨
    (∃ m : ProbComp ((WorldSpec C).Range t × (HiddenCache C × List (Query C))), ∀ c,
      (compWorld prims D parts seed t).run ((c, h), l) = (fun r => (r.1, ((c, r.2.1), r.2.2))) <$> m) := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  · obtain ⟨p, hp⟩ : ∃ p, localAnswer (C := C) prims (.inl n) = StateT.lift p := ⟨_, rfl⟩
    refine Or.inr ⟨(fun a => (a, (h, l ++ []))) <$> p, fun c => ?_⟩
    change (loggedWorld prims D _).run _ = _
    simp only [loggedWorld, streamWorld, onHash, StateT.run_mk]
    change _ <$> (_ <$> (localAnswer prims (.inl n)).run c) = _
    rw [hp, StateT.run_lift]
    simp [countedCells]
  · refine Or.inl ⟨q, id, l ++ [q], fun c => ?_⟩
    change (loggedWorld prims D _).run _ = _
    simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, countedCells, Functor.map_map]
    rfl
  · refine Or.inl ⟨.streamKey x.2.1, fun d => prims.aes.eval (truncateHash d) x.2.2, l ++ [], fun c => ?_⟩
    change (loggedWorld prims D _).run _ = _
    simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, countedCells, Functor.map_map]
    change _ <$> (prgAnswer prims x).run c = _
    simp only [prgAnswer, bind_pure_comp, Functor.map_map, StateT.run_map]
  · exact absurd trivial ht
  · obtain ⟨p, hp⟩ : ∃ p, localAnswer (C := C) prims (.inl n) = StateT.lift p := ⟨_, rfl⟩
    refine Or.inr ⟨(fun a => (a, (h, l ++ []))) <$> p, fun c => ?_⟩
    change (loggedWorld prims D _).run _ = _
    simp only [loggedWorld, streamWorld, onHash, StateT.run_mk]
    change _ <$> (_ <$> (localAnswer prims (.inl n)).run c) = _
    rw [hp, StateT.run_lift]
    simp [countedCells]
  · rcases hT : hiddenTermOf D parts q with _ | T
    · refine Or.inl ⟨q, id, l ++ [], fun c => ?_⟩
      simp only [compWorld, hT]
      simp only [loggedWorld, streamWorld, onHash, StateT.run_mk, countedCells, Functor.map_map]
      rfl
    · refine Or.inr ⟨pure (seed T, (h, l)), fun c => ?_⟩
      simp only [compWorld, hT, StateT.run_pure, map_pure]
  · by_cases hx : Hidden D x.1
    · refine Or.inr ⟨(fun r => (r.1, (r.2, l ++ []))) <$>
        ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle ((x.1, x.2.1), x.2.2)).run h, fun c => ?_⟩
      change (loggedWorld prims D _).run _ = _
      simp only [loggedWorld, streamWorld, hx, ite_true, StateT.run_mk, countedCells, Functor.map_map]
    · refine Or.inl ⟨.streamKey x.2.1, fun d => prims.aes.eval (truncateHash d) x.2.2, l ++ [], fun c => ?_⟩
      change (loggedWorld prims D _).run _ = _
      simp only [loggedWorld, streamWorld, hx, ite_false, onHash, StateT.run_mk, countedCells, Functor.map_map]
      change _ <$> (prgAnswer prims x).run c = _
      simp only [prgAnswer, bind_pure_comp, Functor.map_map, StateT.run_map]


theorem hashAnswer_fresh (q : Query C) (hq : ¬ IsFixed q) (c : HashCache C) (hc : c q = none) :
    (hashAnswer prims q).run c = (fun u => (u, c.cacheQuery q u)) <$> ($ᵗ HashOutput) := by
  rw [hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc]
  rfl

theorem hashAnswer_read (q : Query C) (hq : ¬ IsFixed q) (c : HashCache C) (hc : c q = none) :
    (hashAnswer prims q).run c = $ᵗ HashOutput >>= fun u => (hashAnswer prims q).run (c.cacheQuery q u) := by
  rw [hashAnswer_fresh prims q hq c hc, map_eq_bind_pure_comp]
  refine bind_congr fun u => ?_
  rw [hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle,
    QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _)]
  rfl

/-- A world program with no programming call has one law of the result and the log from a cache, and
from the cache with a fresh value at a cell that has no value and is no cell of `Th`. -/
theorem freshDrop {α : Type} (T : OracleComp (WorldSpec C) α)
    (hT : AllQueriesSatisfy T fun t => ¬ DkgCorrectnessProof.WorldProgramQuery t) :
    ∀ (c : HashCache C) (h : HiddenCache C) (l : List (Query C)) (q : Query C), ¬ IsFixed q → c q = none →
      (fun z => (z.1, z.2.2)) <$> ($ᵗ HashOutput >>= fun u =>
        (simulateQ (compWorld prims D parts seed) T).run ((c.cacheQuery q u, h), l)) =ᵈ
        (fun z => (z.1, z.2.2)) <$> (simulateQ (compWorld prims D parts seed) T).run ((c, h), l) := by
  induction T using OracleComp.inductionOn with
  | pure a =>
    intro c h l q _ _
    simp only [simulateQ_pure, StateT.run_pure, map_bind, map_pure]
    exact EvalDistEq.bind_const _ _
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hT
    intro c h l q hq hc
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, map_bind]
    rcases stepShape prims D parts seed t hT.1 h l with ⟨q', f, l', hstep⟩ | ⟨m, hstep⟩
    · simp only [hstep, bind_map_left]
      by_cases hqq : q' = q
      · subst hqq
        rw [hashAnswer_read prims q' hq c hc, bind_assoc]
      · have hframe : ∀ u, (hashAnswer prims q').run (c.cacheQuery q u) =
            (fun z => (z.1, z.2.cacheQuery q u)) <$> (hashAnswer prims q').run c := fun u =>
          DkgCorrectnessProof.UsedHit.hashAnswer_map prims q' (fun c => c.cacheQuery q u) c
            (QueryCache.cacheQuery_of_ne _ _ hqq) (fun v => cacheQuery_comm hqq v u c)
        simp only [hframe, bind_map_left]
        refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
        refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
        have hzq : z.2 q = none := by
          rw [hashAnswer_keep_other prims q' q (Ne.symm hqq) c z hz]
          exact hc
        have := ih (f z.1) (hT.2 _) z.2 h l' q hq hzq
        simpa only [map_bind, id_eq] using this
    · simp only [hstep, bind_map_left]
      refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.bind_right _ fun r => ?_
      have := ih r.1 (hT.2 _) c r.2.1 r.2.2 q hq hc
      simpa only [map_bind, id_eq] using this

end Shape

section Drop

variable (prims : Primitives)

/-- One local call in front of a world program with no programming call, with its answer forgotten, can
be dropped for the result and the log. -/
theorem oneDrop (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) {α : Type}
    (t : (LocalSpec C).Domain) (ht : NoStream t) (T : OracleComp (WorldSpec C) α)
    (hT : AllQueriesSatisfy T fun t => ¬ DkgCorrectnessProof.WorldProgramQuery t) (c : HashCache C)
    (h : HiddenCache C) (l : List (Query C)) :
    ((compLocal prims D parts seed t).run c >>= fun p =>
      (fun z => (z.1, z.2.2)) <$> (simulateQ (compWorld prims D parts seed) T).run ((p.2, h), l)) =ᵈ
      (fun z => (z.1, z.2.2)) <$> (simulateQ (compWorld prims D parts seed) T).run ((c, h), l) := by
  rcases t with n | q | x
  · obtain ⟨p, hp⟩ : ∃ p, localAnswer (C := C) prims (.inl n) = StateT.lift p := ⟨_, rfl⟩
    change ((localAnswer prims (.inl n)).run c >>= _) =ᵈ _
    rw [hp, StateT.run_lift, bind_assoc]
    simp only [pure_bind]
    exact EvalDistEq.bind_const _ _
  · rcases hT0 : hiddenTermOf D parts q with _ | T0
    · have e : compLocal prims D parts seed (.inr (.inl q)) = hashAnswer prims q := by
        simp only [compLocal, hT0]
        rfl
      rw [e]
      by_cases hf : IsFixed q
      · obtain ⟨input, rfl, hm⟩ := hf
        rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, pure_bind]
      · rcases hc : c q with _ | v
        · rw [hashAnswer_fresh prims q hf c hc, bind_map_left]
          have := freshDrop prims D parts seed T hT c h l q hf hc
          simpa only [map_bind] using this
        · rw [hashAnswer_of_not_isFixed prims hf, OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc,
            pure_bind]
    · have e : compLocal prims D parts seed (.inr (.inl q)) = pure (seed T0) := by
        simp only [compLocal, hT0]
      rw [e, StateT.run_pure, pure_bind]
  · exact absurd ht id

/-- `TailDrop` holds. -/
theorem tailDrop : TailDrop (C := C) prims := by
  intro D parts seed α β X hX T hT s
  rw [simulateQ_bind, StateT.run_bind, compWorld_free_run prims D parts seed X hX s, bind_map_left]
  have hT' := allQ_of_noCall hT
  obtain ⟨⟨c, h⟩, l⟩ := s
  simp only [map_bind]
  induction X using OracleComp.inductionOn generalizing c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hX
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, bind_assoc]
    refine (EvalDistEq.bind_right _ fun (p : (LocalSpec C).Range t × HashCache C) => ih p.1 (hX.2 p.1) p.2).trans ?_
    exact oneDrop prims D parts seed t hX.1 T hT' c h l

end Drop

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.tailDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.tailDrop
