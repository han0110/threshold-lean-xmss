import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepWalk
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Merge
import ThresholdLeanXmssSecurity.Proof.SigningCompilerCouplingUntil

/-!
# The derive side

`deriveSide` proves `DeriveSide`. By `suffixAt_markTo` the suffix of `pairRun` is the suffix of
`partsRef` with each free call of `H` at `markCell` sent to the shifted hidden cell `X`. So the middle
world on the suffix of `partsRef` is `markWorld`, and the two runs have one program.

`markWorld` and `partsWorld` agree until `X` is named, that is until `X` has a value in the shared cache
of `partsWorld` or is in its list of the programming cells. `DeriveSync` couples the two states. The
flag of `markWorld` is down, the world state of `markWorld` is the world state of `partsWorld` with the
value of `markCell` of the private cache at `X` (`putLog`), and the private caches agree off `markCell`.

* A free call at `markCell` asks `X` in the shared cache of `markWorld` and `markCell` in the private
  cache of `partsWorld`. The two cells hold one value.
* A free call at a commitment cell between two honest operators asks the private cache on both sides.
* A counted call at `X`, a programming call at `X` and a free call at `X` of another place name `X`.
* Each other call asks no `X` and runs as `loggedWorld` on both sides (`loggedWorld_putLog`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningCompilerUntil (Until relTriple_simulateQ_until)
open ThresholdLeanXmssSecurity.DkgSecurityProof (Grows Grows.refl loggedWorld_grows randomOracle_grows mainCell
  loggedWorld_freeHash loggedWorld_countedHash localProgram_inl localProgram_inr)
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal (commitAddress termAddress)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## One cell with a set value -/

section Put

variable (X : Query C)

/-- The cache `c` with the entry `o` at the cell `X`. -/
def putAt (o : Option HashOutput) (c : HashCache C) : HashCache C :=
  QueryCache.ofFn fun q => if q = X then o else c q

/-- The world state `w` with the entry `o` at the cell `X`. -/
def putLog (o : Option HashOutput) (w : LogState C) : LogState C := ((putAt X o w.1.1, w.1.2), w.2)

theorem putAt_ne {o : Option HashOutput} {c : HashCache C} {q : Query C} (h : q ≠ X) : putAt X o c q = c q := by
  simp [putAt, h]

theorem putAt_self (o : Option HashOutput) (c : HashCache C) : putAt X o c X = o := by
  simp [putAt]

theorem putAt_cacheQuery_ne (o : Option HashOutput) (c : HashCache C) {q : Query C} (h : q ≠ X) (v : HashOutput) :
    putAt X o (c.cacheQuery q v) = (putAt X o c).cacheQuery q v := by
  refine QueryCache.ext fun q' => ?_
  by_cases h' : q' = q
  · subst h'
    simp [putAt, h]
  · by_cases hX : q' = X
    · subst hX
      simp [putAt, h']
    · simp [putAt, h', hX]

theorem putAt_none_cacheQuery (c : HashCache C) (u : HashOutput) :
    (putAt X none c).cacheQuery X u = putAt X (some u) c := by
  refine QueryCache.ext fun q' => ?_
  by_cases hX : q' = X
  · subst hX
    simp [putAt]
  · simp [putAt, hX]

theorem putAt_of_none {c : HashCache C} (h : c X = none) : putAt X none c = c := by
  refine QueryCache.ext fun q' => ?_
  by_cases hX : q' = X
  · subst hX
    simp [putAt, h]
  · simp [putAt, hX]

theorem randomOracle_putAt {o : Option HashOutput} {q : Query C} (h : q ≠ X) (c : HashCache C) :
    ((Query C →ₒ HashOutput).randomOracle q).run (putAt X o c) =
      (fun z => (z.1, putAt X o z.2)) <$> ((Query C →ₒ HashOutput).randomOracle q).run c := by
  rw [randomOracle.run_eq, randomOracle.run_eq, putAt_ne X h]
  cases c q with
  | some v => simp
  | none => simp [putAt_cacheQuery_ne X o c h]

variable (prims : Primitives)

theorem hashAnswer_putAt {o : Option HashOutput} {q : Query C} (h : q ≠ X) (c : HashCache C) :
    (hashAnswer prims q).run (putAt X o c) = (fun z => (z.1, putAt X o z.2)) <$> (hashAnswer prims q).run c := by
  cases q with
  | hash input =>
    simp only [hashAnswer]
    split_ifs
    · simp
    · exact randomOracle_putAt X h c
  | _ => exact randomOracle_putAt X h c

theorem prgAnswer_putAt (hX : ∀ k, X ≠ .streamKey k) (o : Option HashOutput) (x : PrgInput C) (c : HashCache C) :
    (prgAnswer prims x).run (putAt X o c) = (fun z => (z.1, putAt X o z.2)) <$> (prgAnswer prims x).run c := by
  simp only [prgAnswer, StateT.run_bind, hashAnswer_putAt X prims (fun e => hX x.2.1 e.symm), bind_map_left, map_bind]
  rfl

theorem programAnswer_putAt (o : Option HashOutput) (x : Query C × HashOutput) (h : x.1 ≠ X) (c : HashCache C) :
    (programAnswer x).run (putAt X o c) = (fun z => (z.1, putAt X o z.2)) <$> (programAnswer x).run c := by
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind, putAt_ne X h]
  split_ifs
  · simp
  · simp [putAt_cacheQuery_ne X o c h]

theorem localAnswer_putAt (hX : ∀ k, X ≠ .streamKey k) (o : Option HashOutput) (t : (LocalSpec C).Domain)
    (h : ∀ q, t = .inr (.inl q) → q ≠ X) (c : HashCache C) :
    (localAnswer prims t).run (putAt X o c) = (fun z => (z.1, putAt X o z.2)) <$> (localAnswer prims t).run c := by
  rcases t with u | q | x
  · simp [localAnswer, unifFwdImpl]
  · exact hashAnswer_putAt X prims (h q rfl) c
  · exact prgAnswer_putAt X prims hX o x c

/-- A call of the world whose cell is not `X` runs on the state with the entry `o` at `X` as on the state,
with the entry `o` at `X` at the end. -/
theorem loggedWorld_putLog (D : C.Coalition) (hX : ∀ k, X ≠ .streamKey k) (o : Option HashOutput)
    (t : (WorldSpec C).Domain) (h : ∀ q, mainCell t = some q → q ≠ X) (st : LogState C) :
    (loggedWorld prims D t).run (putLog X o st) =
      (fun z => (z.1, putLog X o z.2)) <$> (loggedWorld prims D t).run st := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [loggedWorld, streamWorld, onHash, putLog, StateT.run_mk, Functor.map_map]
  · rw [localProgram_inl, localAnswer_putAt X prims hX o (Sum.inl u) (fun _ e => nomatch e), Functor.map_map]
    rfl
  · rw [localProgram_inl, localAnswer_putAt X prims hX o (Sum.inr (Sum.inl q)) (fun q' e => by
      cases e; exact h _ rfl), Functor.map_map]
    rfl
  · rw [localProgram_inl, localAnswer_putAt X prims hX o (Sum.inr (Sum.inr x)) (fun _ e => nomatch e),
      Functor.map_map]
    rfl
  · rw [localProgram_inr, programAnswer_putAt X o p (h p.1 rfl), Functor.map_map]
    rfl
  · rw [localAnswer_putAt X prims hX o (Sum.inl u) (fun _ e => nomatch e), Functor.map_map]
    rfl
  · rw [localAnswer_putAt X prims hX o (Sum.inr (Sum.inl q)) (fun q' e => by cases e; exact h _ rfl),
      Functor.map_map]
    rfl
  · split_ifs
    · simp only [StateT.run_mk, Functor.map_map]
    · simp only [StateT.run_mk, Functor.map_map]
      rw [localAnswer_putAt X prims hX o (Sum.inr (Sum.inr x)) (fun _ e => nomatch e), Functor.map_map]
      rfl

end Put

/-! ## The two worlds call by call -/

section Calls

variable (prims : Primitives) (D : C.Coalition) (X : Query C)

/-- `pairWorld` on the calls of `partsRef`, where a free call of `H` at `markCell` asks `X`. -/
def markWorld : QueryImpl (WorldSpec C) (StateT (PairState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl q)) => pairWorld prims D X (.inr (.inr (.inl (markTo X q))))
  | t => pairWorld prims D X t

theorem pairWorld_cellRw (t : (WorldSpec C).Domain) :
    simulateQ (pairWorld prims D X) (cellRw (markTo X) t) = markWorld prims D X t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [cellRw, markWorld, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]

theorem markWorld_other (t : (WorldSpec C).Domain) (h : ∀ q, t ≠ .inr (.inr (.inl q))) :
    markWorld prims D X t = pairWorld prims D X t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  exact absurd rfl (h q)

theorem pairWorld_private {q : Query C} (hq : PairCell D q) (s : PairState C) :
    (pairWorld prims D X (.inr (.inr (.inl q)))).run s =
      (fun r => (r.1, (s.1, r.2, s.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s.2.1 := by
  simp only [pairWorld, hq, ite_true, StateT.run_mk]

theorem pairWorld_shared {q : Query C} (hq : ¬ PairCell D q) (s : PairState C) :
    (pairWorld prims D X (.inr (.inr (.inl q)))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (loggedWorld prims D (.inr (.inr (.inl q)))).run s.1 := by
  simp only [pairWorld, hq, ite_false, StateT.run_mk]

theorem pairWorld_other (t : (WorldSpec C).Domain) (h : ∀ q, t ≠ .inr (.inr (.inl q))) (s : PairState C) :
    (pairWorld prims D X t).run s =
      (fun r => (r.1, (r.2, s.2.1, s.2.2 || decide (TouchAt X t)))) <$> (loggedWorld prims D t).run s.1 := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  exact absurd rfl (h q)

theorem partsWorld_private {q : Query C} (hq : PrivateCell D q) (s : PartsState C) :
    (partsWorld prims D (.inr (.inr (.inl q)))).run s =
      (fun r => (r.1, (s.1, r.2, s.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s.2.1 := by
  simp only [partsWorld, hq, ite_true, StateT.run_mk]

theorem partsWorld_shared {q : Query C} (hq : ¬ PrivateCell D q) (s : PartsState C) :
    (partsWorld prims D (.inr (.inr (.inl q)))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (loggedWorld prims D (.inr (.inr (.inl q)))).run s.1 := by
  simp only [partsWorld, hq, ite_false, StateT.run_mk]

theorem partsWorld_program (p : Query C × HashOutput) (s : PartsState C) :
    (partsWorld prims D (.inl (.inr p))).run s =
      (fun r => (r.1, (r.2, s.2.1, s.2.2 ++ [p.1]))) <$> (loggedWorld prims D (.inl (.inr p))).run s.1 := rfl

theorem partsWorld_other (t : (WorldSpec C).Domain) (h₁ : ∀ q, t ≠ .inr (.inr (.inl q))) (h₂ : ∀ p, t ≠ .inl (.inr p))
    (s : PartsState C) :
    (partsWorld prims D t).run s = (fun r => (r.1, (r.2, s.2))) <$> (loggedWorld prims D t).run s.1 := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  · exact absurd rfl (h₂ p)
  · exact absurd rfl (h₁ q)

/-- Each call of `partsWorld` grows the shared cache and the list of the programming cells. -/
theorem partsWorld_grows (t : (WorldSpec C).Domain) (s : PartsState C) :
    ∀ z ∈ support ((partsWorld prims D t).run s), Grows s.1.1.1 z.2.1.1.1 ∧ ∀ q ∈ s.2.2, q ∈ z.2.2.2 := by
  intro z hz
  by_cases h₁ : ∃ q, t = .inr (.inr (.inl q))
  · obtain ⟨q, rfl⟩ := h₁
    by_cases hq : PrivateCell D q
    · rw [partsWorld_private prims D hq] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, rfl⟩ := hz
      exact ⟨Grows.refl _, fun _ h => h⟩
    · rw [partsWorld_shared prims D hq] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨(loggedWorld_grows prims D _ _ w hw).1, fun _ h => h⟩
  by_cases h₂ : ∃ p, t = .inl (.inr p)
  · obtain ⟨p, rfl⟩ := h₂
    rw [partsWorld_program] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨(loggedWorld_grows prims D _ _ w hw).1, fun _ h => List.mem_append_left _ h⟩
  push Not at h₁ h₂
  rw [partsWorld_other prims D t (fun q e => h₁ q e) (fun p e => h₂ p e)] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨(loggedWorld_grows prims D _ _ w hw).1, fun _ h => h⟩

end Calls

/-! ## The coupling -/

section Coupling

variable (prims : Primitives) (D : C.Coalition) (X : Query C)

/-- `X` has a value in the shared cache of `partsWorld` or is in its list of the programming cells. -/
def NamedAt (s : PartsState C) : Prop := (s.1.1.1 X).isSome ∨ X ∈ s.2.2

/-- The flag of `markWorld` is down, its world state is the world state of `partsWorld` with the value
of `markCell` of the private cache at `X`, and the private caches agree off `markCell`. -/
def DeriveSync (s₁ : PairState C) (s₂ : PartsState C) : Prop :=
  s₁.2.2 = false ∧ s₁.1 = putLog X (s₂.2.1 markCell) s₂.1 ∧ ∀ q, q ≠ markCell → s₁.2.1 q = s₂.2.1 q

/-- The facts on the shifted hidden cell that the coupling uses. -/
structure CellFacts (X : Query C) : Prop where
  ne_mark : X ≠ markCell
  not_pair : ¬ PairCell D X
  not_stream : ∀ k, X ≠ .streamKey k
  not_fixed : ¬ IsFixed X

theorem namedAt_sticky (t : (WorldSpec C).Domain) (s : PartsState C) (h : NamedAt X s) :
    ∀ b ∈ support ((partsWorld prims D t).run s), NamedAt X b.2 := by
  intro b hb
  obtain ⟨hg, hl⟩ := partsWorld_grows prims D t s b hb
  rcases h with h | h
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    exact Or.inl (by rw [hg _ v hv]; rfl)
  · exact Or.inr (hl X h)

/-- A call that runs as `loggedWorld` on both sides and asks no `X` keeps the coupling. -/
theorem deriveStep_frame (hX : ∀ k, X ≠ .streamKey k) (t : (WorldSpec C).Domain) (s₁ : PairState C)
    (s₂ : PartsState C) (hs : DeriveSync X s₁ s₂) (hmain : ∀ q, mainCell t = some q → q ≠ X) (L : List (Query C))
    (h₁ : (markWorld prims D X t).run s₁ = (fun z => (z.1, (z.2, s₁.2.1, s₁.2.2))) <$> (loggedWorld prims D t).run s₁.1)
    (h₂ : (partsWorld prims D t).run s₂ = (fun z => (z.1, (z.2, s₂.2.1, L))) <$> (loggedWorld prims D t).run s₂.1) :
    RelTriple ((markWorld prims D X t).run s₁) ((partsWorld prims D t).run s₂)
      (Until (fun _ => False) (NamedAt X) (DeriveSync X)) := by
  obtain ⟨hf, hl, hp⟩ := hs
  rw [h₁, h₂, hl, loggedWorld_putLog X prims D hX _ t hmain, Functor.map_map]
  exact relTriple_map (relTriple_refl_of_mem_support _ fun z _ => Or.inr (Or.inr ⟨rfl, hf, rfl, hp⟩))

/-- A free call at a commitment cell between two honest operators asks the private cache on both
sides. -/
theorem deriveStep_private (q : Query C) (hq : q ≠ markCell) (s₁ : PairState C) (s₂ : PartsState C)
    (hs : DeriveSync X s₁ s₂) :
    RelTriple ((fun r => (r.1, (s₁.1, r.2, s₁.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s₁.2.1)
      ((fun r => (r.1, (s₂.1, r.2, s₂.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle q).run s₂.2.1)
      (Until (fun _ => False) (NamedAt X) (DeriveSync X)) := by
  obtain ⟨hf, hl, hp⟩ := hs
  rw [randomOracle.run_eq, randomOracle.run_eq, hp q hq]
  cases hc : s₂.2.1 q with
  | some v =>
    simp only [map_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hf, hl, hp⟩))
  | none =>
    simp only [map_bind, map_pure]
    refine relTriple_bind (relTriple_refl ($ᵗ HashOutput)) fun a b hab => ?_
    cases hab
    refine relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hf, ?_, fun q' hq' => ?_⟩))
    · simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]
      exact hl
    · by_cases e : q' = q
      · subst e
        simp
      · simp only [QueryCache.cacheQuery_of_ne _ _ e]
        exact hp q' hq'

/-- A free call at `markCell` asks `X` in the shared cache of `markWorld` and `markCell` in the private
cache of `partsWorld`. -/
theorem deriveStep_mark (s₁ : PairState C) (s₂ : PartsState C) (hs : DeriveSync X s₁ s₂) :
    RelTriple ((fun r => (r.1, (((r.2, s₁.1.1.2), s₁.1.2), s₁.2))) <$>
        ((Query C →ₒ HashOutput).randomOracle X).run s₁.1.1.1)
      ((fun r => (r.1, (s₂.1, r.2, s₂.2.2))) <$> ((Query C →ₒ HashOutput).randomOracle markCell).run s₂.2.1)
      (Until (fun _ => False) (NamedAt X) (DeriveSync X)) := by
  obtain ⟨w₁, p₁, f₁⟩ := s₁
  obtain ⟨hf, hl, hp⟩ := hs
  simp only at hf hl hp
  subst hf hl
  rw [randomOracle.run_eq, randomOracle.run_eq]
  simp only [putLog, putAt_self]
  cases hc : s₂.2.1 markCell with
  | some v =>
    simp only [map_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, rfl, by simp [putLog, hc], hp⟩))
  | none =>
    simp only [map_bind, map_pure]
    refine relTriple_bind (relTriple_refl ($ᵗ HashOutput)) fun a b hab => ?_
    cases hab
    refine relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, rfl, ?_, fun q' hq' => ?_⟩))
    · simp [putLog, putAt_none_cacheQuery]
    · simp only [QueryCache.cacheQuery_of_ne _ _ hq']
      exact hp q' hq'

/-- A call other than a free call of `H` and other than a programming call in `partsWorld`, with no
cell `X`, keeps the coupling. -/
theorem deriveStep_other (hX : CellFacts D X) (t : (WorldSpec C).Domain) (h₁ : ∀ q, t ≠ .inr (.inr (.inl q)))
    (hmain : ∀ q, mainCell t = some q → q ≠ X) (htouch : ¬ TouchAt X t) (L : List (Query C)) (s₁ : PairState C)
    (s₂ : PartsState C) (hs : DeriveSync X s₁ s₂)
    (h₂ : (partsWorld prims D t).run s₂ = (fun z => (z.1, (z.2, s₂.2.1, L))) <$> (loggedWorld prims D t).run s₂.1) :
    RelTriple ((markWorld prims D X t).run s₁) ((partsWorld prims D t).run s₂)
      (Until (fun _ => False) (NamedAt X) (DeriveSync X)) := by
  refine deriveStep_frame prims D X hX.not_stream t s₁ s₂ hs hmain L ?_ h₂
  rw [markWorld_other prims D X t h₁, pairWorld_other prims D X t h₁, decide_eq_false htouch, Bool.or_false]

/-- The coupling of one call of the two worlds, until `X` is named. -/
theorem deriveStep (hX : CellFacts D X) (t : (WorldSpec C).Domain) (s₁ : PairState C) (s₂ : PartsState C)
    (hs : DeriveSync X s₁ s₂) (hb : ¬ NamedAt X s₂) :
    RelTriple ((markWorld prims D X t).run s₁) ((partsWorld prims D t).run s₂)
      (Until (fun _ => False) (NamedAt X) (DeriveSync X)) := by
  have named : (∀ b ∈ support ((partsWorld prims D t).run s₂), NamedAt X b.2) →
      RelTriple ((markWorld prims D X t).run s₁) ((partsWorld prims D t).run s₂)
        (Until (fun _ => False) (NamedAt X) (DeriveSync X)) := fun h =>
    SigningOpeningProof.relTriple_of_support_right fun b hb _ => Or.inr (Or.inl (h b hb))
  have hcell : ∀ (c : HashCache C), ∀ z ∈ support ((hashAnswer prims X).run c), (z.2 X).isSome := by
    intro c z hz
    rw [hashAnswer_of_not_isFixed prims hX.not_fixed] at hz
    exact Option.isSome_iff_ne_none.2 (randomOracle_grows X c z hz).2
  rcases t with ((u | q | x) | p) | (u | q | x)
  · exact deriveStep_other prims D X hX (.inl (.inl (.inl u))) (fun q e => by cases e) (fun q e => by cases e)
      (fun h => h) s₂.2.2 s₁ s₂ hs (partsWorld_other prims D _ (fun q e => by cases e) (fun p e => by cases e) s₂)
  · by_cases hqX : q = X
    · subst hqX
      refine named fun b hb => ?_
      rw [partsWorld_other prims D _ (fun q e => by cases e) (fun p e => by cases e), loggedWorld_countedHash] at hb
      simp only [support_map, Set.mem_image] at hb
      obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hb
      exact Or.inl (hcell _ w' hw')
    · exact deriveStep_other prims D X hX (.inl (.inl (.inr (.inl q)))) (fun q e => by cases e)
        (fun q' e => by cases e; exact hqX) (fun h => hqX h) s₂.2.2 s₁ s₂ hs
        (partsWorld_other prims D _ (fun q e => by cases e) (fun p e => by cases e) s₂)
  · exact deriveStep_other prims D X hX (.inl (.inl (.inr (.inr x)))) (fun q e => by cases e) (fun q e => by cases e)
      (fun h => h) s₂.2.2 s₁ s₂ hs (partsWorld_other prims D _ (fun q e => by cases e) (fun p e => by cases e) s₂)
  · by_cases hpX : p.1 = X
    · refine named fun b hb => ?_
      rw [partsWorld_program] at hb
      simp only [support_map, Set.mem_image] at hb
      obtain ⟨w, _, rfl⟩ := hb
      exact Or.inr (by simp [hpX])
    · exact deriveStep_other prims D X hX (.inl (.inr p)) (fun q e => by cases e) (fun q' e => by cases e; exact hpX)
        (fun h => hpX h) (s₂.2.2 ++ [p.1]) s₁ s₂ hs (partsWorld_program prims D p s₂)
  · exact deriveStep_other prims D X hX (.inr (.inl u)) (fun q e => by cases e) (fun q e => by cases e)
      (fun h => h) s₂.2.2 s₁ s₂ hs (partsWorld_other prims D _ (fun q e => by cases e) (fun p e => by cases e) s₂)
  · by_cases hpair : PairCell D q
    · have hqm : q ≠ markCell := by
        obtain ⟨i, j, r, -, -, rfl⟩ := hpair
        simp [markCell]
      have hm : markTo X q = q := by simp [markTo, hqm]
      rw [show (markWorld prims D X (.inr (.inr (.inl q)))).run s₁ =
          (pairWorld prims D X (.inr (.inr (.inl q)))).run s₁ by simp only [markWorld]; rw [hm],
        pairWorld_private prims D X hpair, partsWorld_private prims D (Or.inr hpair)]
      exact deriveStep_private X q hqm s₁ s₂ hs
    by_cases hqm : q = markCell
    · subst hqm
      rw [show (markWorld prims D X (.inr (.inr (.inl markCell)))).run s₁ =
          (pairWorld prims D X (.inr (.inr (.inl X)))).run s₁ by simp [markWorld, markTo],
        pairWorld_shared prims D X hX.not_pair, loggedWorld_freeHash, hashAnswer_of_not_isFixed prims hX.not_fixed,
        Functor.map_map, partsWorld_private prims D (Or.inl rfl)]
      exact deriveStep_mark X s₁ s₂ hs
    have hm : markTo X q = q := by simp [markTo, hqm]
    have hpriv : ¬ PrivateCell D q := by
      rintro (h | ⟨i, j, r, hi, hj, h⟩)
      · exact hqm h
      · exact hpair ⟨i, j, r, hi, hj, h⟩
    by_cases hqX : q = X
    · subst hqX
      refine named fun b hb => ?_
      rw [partsWorld_shared prims D hpriv, loggedWorld_freeHash] at hb
      simp only [support_map, Set.mem_image] at hb
      obtain ⟨w, ⟨w', hw', rfl⟩, rfl⟩ := hb
      exact Or.inl (hcell _ w' hw')
    · exact deriveStep_frame prims D X hX.not_stream _ s₁ s₂ hs (fun q' e => by cases e; exact hqX) s₂.2.2
        (by rw [show (markWorld prims D X (.inr (.inr (.inl q)))).run s₁ =
            (pairWorld prims D X (.inr (.inr (.inl q)))).run s₁ by simp only [markWorld]; rw [hm],
          pairWorld_shared prims D X hpair])
        (partsWorld_shared prims D hpriv s₂)
  · exact deriveStep_other prims D X hX (.inr (.inr (.inr x))) (fun q e => by cases e) (fun q e => by cases e)
      (fun h => h) s₂.2.2 s₁ s₂ hs (partsWorld_other prims D _ (fun q e => by cases e) (fun p e => by cases e) s₂)

/-- On one program, a raised flag of `markWorld` has at most the probability that `partsWorld` names
`X`. The bound holds from each world state, with the flag up when `X` has a value at the start. -/
theorem markWorld_le {α : Type} (hX : CellFacts D X) (oa : OracleComp (WorldSpec C) α) (w : LogState C) :
    Pr{let z ← (simulateQ (markWorld prims D X) oa).run (w, ∅, (w.1.1 X).isSome)}[z.2.2.2 = true] ≤
      Pr{let z ← (simulateQ (partsWorld prims D) oa).run (w, ∅, [])}[NamedAt X z.2] := by
  have hstart : (fun (_ : PairState C) => False) (w, ∅, (w.1.1 X).isSome) ∨ NamedAt X ((w, ∅, []) : PartsState C) ∨
      DeriveSync X (w, ∅, (w.1.1 X).isSome) (w, ∅, []) := by
    cases h : (w.1.1 X).isSome
    · refine Or.inr (Or.inr ⟨rfl, ?_, fun _ _ => rfl⟩)
      have hn : w.1.1 X = none := Option.not_isSome_iff_eq_none.1 (by simp [h])
      obtain ⟨⟨c, hc⟩, log⟩ := w
      simp only [putLog, QueryCache.empty_apply] at hn ⊢
      rw [putAt_of_none X hn]
    · exact Or.inr (Or.inl (Or.inl h))
  have coupled := relTriple_simulateQ_until (markWorld prims D X) (partsWorld prims D) (fun _ => False)
    (NamedAt X) (DeriveSync X) (fun _ _ h => h.elim) (namedAt_sticky prims D X)
    (fun t s₁ s₂ hs _ hb => deriveStep prims D X hX t s₁ s₂ hs hb) oa _ _ hstart
  refine prEvent_le_of_relTriple coupled fun a b hR ha => ?_
  rcases hR with h | h | ⟨-, hs⟩
  · exact h.elim
  · exact h
  · rw [hs.1] at ha
    exact absurd ha (by simp)

end Coupling

/-! ## The derive side -/

section Glue

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

theorem cellFacts_hiddenInput (D : C.Coalition) (parts : C.Party → Parts C) (T : C.Term) :
    CellFacts D (hiddenInput parts T) where
  ne_mark h := by
    simp only [hiddenInput, markCell, Query.derive.injEq, true_and, List.map_eq_nil_iff] at h
    exact holdersList_ne_nil T h
  not_pair := fun ⟨_, _, _, _, _, h⟩ => by cases h
  not_stream _ h := by cases h
  not_fixed := fun ⟨_, h, _⟩ => by cases h

theorem mem_partsNamed (T : C.Term) (δ : {k // k ∈ C.holders T} → HashOutput) (parts : C.Party → Parts C)
    (s : PartsState C) : δ ∈ partsNamed T parts s ↔ NamedAt (hiddenInput (shiftBy T δ parts) T) s := by
  simp only [partsNamed, Finset.mem_filter, Finset.mem_univ, true_and, NamedAt]

omit [Fintype E] [DecidableEq E] in
/-- The proof of `DeriveSide`. -/
theorem deriveSide : DeriveSide prims K circuits settings runLimit := by
  intro D A T δ hT
  unfold pairRun partsRef
  rw [DkgSecurityProof.prEvent_bind_wp, DkgSecurityProof.prEvent_bind_wp]
  refine wp_mono _ fun x => ?_
  simp only [bind_pure_comp, prEvent_map, mem_partsNamed]
  rw [← suffixAt_markTo K circuits settings runLimit D A x.1 T δ hT,
    QueryImpl.simulateQ_simulateQ_eq_of_apply (pairWorld_cellRw prims D _)]
  exact markWorld_le prims D _ (cellFacts_hiddenInput D _ T) _ x.2

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.deriveSide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.deriveSide
