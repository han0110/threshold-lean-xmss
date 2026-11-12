import ThresholdLeanXmssSecurity.Proof.LifetimeSaltGuarded

/-!
# Pair bounds of the fixed two-stage salt tables

`LifetimeSaltGuarded.PairBoundsGuardedFrom` bounds each pair `i < j` of A66's fixed tables on the
actual paired run. Let `n₁` be the size of the stage-1 table. The pairs split by the stages of
their entries and by which salts are hidden.

* Both entries in stage 1 (`j < n₁`). The end of the setup fixes both addresses, and no salt is read
  there (`TreeSaltPairsFinal.setup_from_noSalt`). Two hidden salts are two unread lazy points, which
  the potential of `TreeSaltPairs` pays (`hidden_pair_le`). A hidden salt against a known salt is
  `KnownFirstBound`.
* A stage-2 entry `j` against a known stage-1 entry or a stage-2 entry. The stage view `m` fixes the
  stage-2 address. Outside a budget collision at `m`, the stage-1 table covers the log at `m`, so a
  hidden stage-2 salt is unread there (`open_first`). Each view is bounded alone (`rest_entry_le`):
  the potential pays two hidden salts, and `KnownSecondBound` a known one.
* A hidden stage-1 entry against a stage-2 entry is `CrossHiddenBound`. It cannot be bounded view by
  view. Given `m`, the hidden stage-1 salt is fixed, and the choice of the stage-2 table can depend
  on the outcome of counted guesses of that salt. Only the average over the views, with the guess
  and least-pair guards, gives `2^-256`.

`HiddenCoherent` states that the hidden cache holds exactly the logged honest hidden-stream answers;
each query of the logged world keeps it (`hiddenCoherent_step`). `PublicCoherent` states that each
logged known-stream answer is AES under the cached derived key `H(.streamKey key)`.

`known_pair_le` proves `KnownFirstBound` and `KnownSecondBound`. Both continuations make no
programming call (`afterProgram_local`, `restProgram_local`), so the derived key of the known address
is a lazy uniform hash value. For each candidate key `k`, the known salt is a fixed bit string, and
`saltPairWeight` of `TreeSaltPairs` pays the unread hidden salt against it. `knownPotential` averages
these weights with `keyWeight`, the point mass at the cached key or the uniform weight before the key
is drawn. A hash query keeps the expected key weight, and a hidden-stream query keeps each pair weight,
so the potential does not grow in expectation (`potential_step`).

`pairBoundsGuardedFrom_of_cross` reduces `PairBoundsGuardedFrom` to `CrossHiddenBound`, which is its
restriction to the cross pairs (`crossHiddenBound_of_pairBounds`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The hidden cache holds exactly the logged honest answers of the hidden streams. -/
def HiddenCoherent (D : C.Coalition) (s : TreeSimState C) : Prop :=
  ∀ (y : PrgInput C) (b : Bit), Hidden D y.1 →
    ((⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ s.2 ↔
      s.1.2 ((y.1, y.2.1), y.2.2) = some b)

theorem hiddenCoherent_empty (D : C.Coalition) : HiddenCoherent D (((∅, ∅), []) : TreeSimState C) := by
  intro y b _
  simp

/-- A step that keeps the hidden cache and logs no hidden stream keeps the coherence. -/
theorem hiddenCoherent_keep (D : C.Coalition) (s : TreeSimState C) (hs : HiddenCoherent D s)
    (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) (c : HashCache C × HiddenCache C)
    (hc : c.2 = s.1.2)
    (hne : ∀ y b, Hidden D y.1 →
      (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ≠ ⟨.inr (.inr (.inr y)), b⟩) :
    HiddenCoherent D (c, s.2 ++ [⟨t, u⟩]) := by
  intro y b hy
  rw [List.mem_append, List.mem_singleton, hc]
  constructor
  · rintro (h | h)
    · exact (hs y b hy).mp h
    · exact (hne y b hy h.symm).elim
  · exact fun h => Or.inl ((hs y b hy).mpr h)

/-- Each query of the logged world keeps the coherence. -/
theorem hiddenCoherent_step (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : TreeSimState C) (hs : HiddenCoherent D s) (z : (WorldSpec C).Range t × TreeSimState C)
    (hz : z ∈ support ((treeSimLoggedWorld prims D t).run s)) : HiddenCoherent D z.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with t | (t | t | x)
  · exact hiddenCoherent_keep D s hs _ _ _ (onHash_hidden _ s.1 r hr)
      (fun y b _ h => by simp at h)
  · exact hiddenCoherent_keep D s hs _ _ _ (onHash_hidden _ s.1 r hr)
      (fun y b _ h => by simp at h)
  · exact hiddenCoherent_keep D s hs _ _ _ (onHash_hidden _ s.1 r hr)
      (fun y b _ h => by simp at h)
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨o, ho, rfl⟩ := hr
      have law : o.2 = s.1.2.cacheQuery ((x.1, x.2.1), x.2.2) o.1 ∧
          ∀ c, s.1.2 ((x.1, x.2.1), x.2.2) = some c → o.1 = c := by
        cases hc : s.1.2 ((x.1, x.2.1), x.2.2) with
        | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map, Set.mem_image] at ho
          obtain ⟨v, _, rfl⟩ := ho
          exact ⟨rfl, fun _ h => by cases h⟩
        | some c =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ho
          subst ho
          refine ⟨?_, fun _ h => by cases h; rfl⟩
          funext d
          by_cases hd : d = ((x.1, x.2.1), x.2.2)
          · subst hd
            rw [QueryCache.cacheQuery_self, hc]
          · rw [QueryCache.cacheQuery_of_ne _ _ hd]
      intro y b hy
      change _ ∈ s.2 ++ [⟨.inr (.inr (.inr x)), o.1⟩] ↔ o.2 ((y.1, y.2.1), y.2.2) = some b
      rw [List.mem_append, List.mem_singleton, law.1]
      by_cases hyx : y = x
      · subst hyx
        rw [QueryCache.cacheQuery_self]
        constructor
        · rintro (h | h)
          · exact congrArg some (law.2 b ((hs y b hy).mp h))
          · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
            exact congrArg some h.symm
        · intro h
          exact Or.inr (by simp only [Option.some.injEq] at h; subst h; rfl)
      · have hd : ((y.1, y.2.1), y.2.2) ≠ ((x.1, x.2.1), x.2.2) := by
          intro h
          apply hyx
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)
        rw [QueryCache.cacheQuery_of_ne _ _ hd]
        constructor
        · rintro (h | h)
          · exact (hs y b hy).mp h
          · simp only [Sigma.mk.inj_iff, Sum.inr.injEq] at h
            exact (hyx h.1).elim
        · exact fun h => Or.inl ((hs y b hy).mpr h)
    · simp only [streamWorld, if_neg hx] at hr
      exact hiddenCoherent_keep D s hs _ _ _ (onHash_hidden _ s.1 r hr)
        (fun y b hy h => by
          simp only [Sigma.mk.inj_iff, Sum.inr.injEq] at h
          exact hx (h.1 ▸ hy))

/-- Every logged run keeps the coherence. -/
theorem hiddenCoherent_run (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) (hs : HiddenCoherent D s) :
    ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) oa).run s), HiddenCoherent D z.2 :=
  simulateQ_run_preserves_inv_of_query _ _ (fun t s hs z hz => hiddenCoherent_step prims D t s hs z hz)
    oa s hs

-- Copy of `simulateQ_executeRounds` (`Coupling.lean`) for the runner that keeps pending programs.
/-- A handler applied to the rounds runs each step of the rounds through it. -/
theorem simulateQ_executeSteps {E Ia I O L R α κ : Type} {spec : OracleSpec κ}
    {n : Type → Type} [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)
    (Ro : Roles C (OracleComp spec)) (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α),
      simulateQ impl (executeSteps Ro D A F fuel state steps) =
        executeSteps (simRoles impl Ro) D A F fuel state steps
  | 0, state, steps => by simp [executeSteps]
  | fuel + 1, state, steps => by
    simp only [executeSteps]
    split_ifs
    · simp
    · simp only [simulateQ_bind, simulateQ_stepRound, simulateQ_executeSteps impl Ro D A F fuel]

section Ceremony

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The coherence holds after a counted prefix and the setup that follows it. -/
theorem hiddenCoherent_setup (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    HiddenCoherent D p.2 := by
  have h0 := hiddenCoherent_run prims D _ _ (hiddenCoherent_empty D) s hs
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  have h1 := hiddenCoherent_run prims D _ _ h0 start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  exact hiddenCoherent_run prims D _ _ h1 p hp

/-- The coherence holds at the stage point. -/
theorem hiddenCoherent_first (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : HiddenCoherent D p.2) (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p)) :
    HiddenCoherent D m.2 := by
  simp only [TreeSaltPairsFinal.first, mem_support_bind_iff] at hm
  obtain ⟨next, hnext, hm⟩ := hm
  have h1 := hiddenCoherent_run prims D _ _ hp next hnext
  rw [treeSimRealRoles, ← simulateQ_executeSteps] at hm
  exact hiddenCoherent_run prims D _ _ h1 m hm

/-- The program of the run after the stage point. -/
def restProgram (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (m : TreeSimConfig A (TreeSimState C)) :
    OracleComp (WorldSpec C) Bool := do
  let out ← executeRounds worldRoles D A noFunctionality
    (ceremonyFuel circuits settings - setupRounds -
      TreeSaltPairsFinal.firstRounds circuits settings tree (TreeSaltPairsFinal.parameter x))
    m.1.1 m.1.2
  worldRoles.adversary (Z out)

theorem rest_eq (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (m : TreeSimConfig A (TreeSimState C)) :
    TreeSaltPairsFinal.rest prims circuits settings tree D A x Z m =
      (fun r => (r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (restProgram circuits settings tree D A x Z m)).run m.2 := by
  unfold TreeSaltPairsFinal.rest restProgram treeSimRealObserve
  rw [treeSimRealRoles, ← simulateQ_executeRounds]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]

/-- The program of the run after the setup. -/
def afterProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    OracleComp (WorldSpec C) Bool := do
  let next ← treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2
  let out ← executeRounds worldRoles D A noFunctionality
    (ceremonyFuel circuits settings - setupRounds) p.1.1 next
  worldRoles.adversary (Z out)

theorem after_eq (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    treeSaltAfterSetup prims K circuits settings top tree D A x Z p =
      (fun r => (r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (afterProgram K circuits settings top tree D A x Z p)).run p.2 := by
  unfold treeSaltAfterSetup afterProgram treeSimRealObserve
  simp only [treeSimRealRoles, ← simulateQ_executeRounds, simulateQ_bind, StateT.run_bind, map_bind]

end Ceremony

/-- The hidden-stream point of salt bit `g` at the address `a`. -/
def saltPoint (a : C.Term × HashOutput × ℕ) (g : Fin 256) : (KeyName C × HashOutput) × ℕ × ℕ × ℕ :=
  ((.term a.1, a.2.1), a.2.2, 2, g.val)

/-- Two addresses read the same salt. -/
def SameSalt (log : TreeSimLog C) (a b : C.Term × HashOutput × ℕ) : Prop :=
  ∃ salt : List Bit, salt.length = 256 ∧ TreeSaltAt log a salt ∧ TreeSaltAt log b salt

/-- Two distinct hidden addresses, the second unread at the start, read the same salt with
probability at most `2^-256`. -/
theorem hidden_pair_le (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) (hs : HiddenCoherent D s)
    (a b : C.Term × HashOutput × ℕ) (hab : a ≠ b)
    (ha : ¬ KnownTo D.1 a.1) (hb : ¬ KnownTo D.1 b.1)
    (hopen : ∀ g, s.1.2 (saltPoint b g) = none) :
    Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D) oa).run s] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let u : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit := fun g => .inl (saltPoint a g)
  let v : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit := fun g => .inl (saltPoint b g)
  have point : ∀ (c c' : C.Term × HashOutput × ℕ) (g g' : Fin 256), saltPoint c g = saltPoint c' g' → c = c' ∧ g = g' := by
    intro c c' g g' h
    simp only [saltPoint, Prod.mk.injEq, KeyName.term.injEq] at h
    exact ⟨Prod.ext h.1.1 (Prod.ext h.1.2 h.2.1), Fin.ext h.2.2.2⟩
  have hd : SaltPairDistinct u v := by
    rintro (g | g) (g' | g') d hx hy <;>
      simp only [Sum.elim_inl, Sum.elim_inr, u, v, Sum.inl.injEq] at hx hy <;>
      obtain ⟨hc, hg⟩ := point _ _ _ _ (hx.trans hy.symm)
    · rw [hg]
    · exact (hab hc).elim
    · exact (hab hc.symm).elim
    · rw [hg]
  have mono : Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D) oa).run s] ≤
      Pr[fun r => SaltPairEqual u v r.2.1.2 | (simulateQ (treeSimLoggedWorld prims D) oa).run s] := by
    apply probEvent_mono
    rintro r hr ⟨salt, -, hsa, hsb⟩ g
    have coh := hiddenCoherent_run prims D oa s hs r hr
    refine ⟨salt.getD g.val 0, ?_, ?_⟩
    · exact (coh (.term a.1, a.2.1, a.2.2, 2, g.val) _ ha).mp (hsa g)
    · exact (coh (.term b.1, b.2.1, b.2.2, 2, g.val) _ hb).mp (hsb g)
  refine mono.trans ((treeSimLogged_saltPair_le D hd oa s).trans (le_of_eq ?_))
  exact saltPairWeight_of_open (fun g => Or.inr (hopen g))

theorem sameSalt_comm (log : TreeSimLog C) (a b : C.Term × HashOutput × ℕ) :
    SameSalt log a b ↔ SameSalt log b a :=
  ⟨fun ⟨salt, h, ha, hb⟩ => ⟨salt, h, hb, ha⟩, fun ⟨salt, h, ha, hb⟩ => ⟨salt, h, hb, ha⟩⟩

/-- A hidden address that the log does not read is open in a coherent hidden cache. -/
theorem open_of_unread (D : C.Coalition) (s : TreeSimState C) (hs : HiddenCoherent D s)
    (a : C.Term × HashOutput × ℕ) (ha : ¬ KnownTo D.1 a.1)
    (unread : ∀ g b, (⟨.inr (.inr (.inr (.term a.1, a.2.1, a.2.2, 2, g))), b⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∉ s.2) :
    ∀ g, s.1.2 (saltPoint a g) = none := by
  intro g
  cases h : s.1.2 (saltPoint a g) with
  | none => rfl
  | some b => exact (unread g.val b ((hs (.term a.1, a.2.1, a.2.2, 2, g.val) b ha).mpr h)).elim

theorem append_left_eq {n₁ n₂ : ℕ} {β : Type} (f : Fin n₁ → β) (g : Fin n₂ → β) (i : ℕ)
    (hi : i < n₁ + n₂) (h : i < n₁) : Fin.append f g ⟨i, hi⟩ = f ⟨i, h⟩ := by
  have : (⟨i, hi⟩ : Fin (n₁ + n₂)) = Fin.castAdd n₂ ⟨i, h⟩ := rfl
  rw [this, Fin.append_left]

theorem append_right_eq {n₁ n₂ : ℕ} {β : Type} (f : Fin n₁ → β) (g : Fin n₂ → β) (j : ℕ)
    (hj : j < n₁ + n₂) (h : n₁ ≤ j) : Fin.append f g ⟨j, hj⟩ = g ⟨j - n₁, by omega⟩ := by
  have : (⟨j, hj⟩ : Fin (n₁ + n₂)) = Fin.natAdd n₁ ⟨j - n₁, by omega⟩ := Fin.ext (by simp; omega)
  rw [this, Fin.append_right]

section Parts

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The pairs of a hidden stage-1 entry and a stage-2 entry of the stage view, with the event of
`PairBoundsGuardedFrom`. -/
def CrossHiddenBound : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ i j : ℕ, (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card) →
      (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card ≤ j →
      ¬ KnownTo D.1
        (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)
          ⟨i, hi⟩).1 →
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ ¬ TreeSimSaltGuess D r.2.2 ∧
          TreeSaltLeastPairReuse D
            (Fin.append
              (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2))
              (TreeSaltPairsFinal.enumerate
                (TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A r.1))) i j r.2.2 |
        (TreeSaltPairsFinal.splits prims K circuits settings top tree D A x Z p).paired] ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹

/-- From the end of the setup, an unread hidden salt equals a known salt with probability at
most `2^-256`. -/
def KnownFirstBound : Prop :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ a b : C.Term × HashOutput × ℕ, ¬ KnownTo D.1 a.1 → KnownTo D.1 b.1 →
      (∀ g, p.2.1.2 (saltPoint a g) = none) →
      Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
        (afterProgram K circuits settings top tree D A x Z p)).run p.2] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

/-- From the stage point, an unread hidden salt equals a known salt with probability at most
`2^-256`. -/
def KnownSecondBound : Prop :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p),
    ∀ a b : C.Term × HashOutput × ℕ, ¬ KnownTo D.1 a.1 → KnownTo D.1 b.1 →
      (∀ g, m.2.1.2 (saltPoint a g) = none) →
      Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
        (restProgram circuits settings tree D A x Z m)).run m.2] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

/-- Every hidden salt is unread at the end of the setup. -/
theorem open_setup (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (a : C.Term × HashOutput × ℕ) (ha : ¬ KnownTo D.1 a.1) :
    ∀ g, p.2.1.2 (saltPoint a g) = none := by
  apply open_of_unread D p.2 (hiddenCoherent_setup prims D A x z pre s hs p hp) a ha
  intro g b h
  exact TreeSaltPairsFinal.setup_from_noSalt prims D A x z pre s hs p hp _ b h a.1 a.2.1 a.2.2 g rfl

/-- Outside a budget collision, a stage-2 hidden salt is unread at the stage point. -/
theorem open_first (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (good : ¬ TreeSimHashBudgetCollision m.2.2)
    (a : C.Term × HashOutput × ℕ) (ha : ¬ KnownTo D.1 a.1)
    (late : a ∉ TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) :
    ∀ g, m.2.1.2 (saltPoint a g) = none := by
  apply open_of_unread D m.2 (hiddenCoherent_first prims K circuits settings top tree D A x p
    (hiddenCoherent_setup prims D A x z pre s hs p hp) m hm) a ha
  intro g b h
  exact late (TreeSaltPairsFinal.agreement_mem _ _ _
    (TreeSaltPairsFinal.first_agreement_from prims K circuits settings top tree D A x z hx pre s hs
      p hp m hm good) a.1 a.2.1 a.2.2 g b h)

/-- A pair with an unread hidden side at the stage point, outside a budget collision. -/
theorem rest_pair_le (known : KnownSecondBound prims K circuits settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (a b : C.Term × HashOutput × ℕ) (hab : a ≠ b) (ha : ¬ KnownTo D.1 a.1)
    (late : a ∉ TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) :
    Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ SameSalt r.2.2 a b |
      (simulateQ (treeSimLoggedWorld prims D)
        (restProgram circuits settings tree D A x Z m)).run m.2] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  by_cases good : TreeSimHashBudgetCollision m.2.2
  · refine le_trans (le_of_eq ?_) (zero_le (α := ℝ≥0∞))
    refine probEvent_eq_zero fun r hr h => h.1 ?_
    exact treeSimHashBudgetCollision_mono (treeSimLoggedWorld_prefix prims D _ m.2 r hr) good
  have hopen := open_first prims K circuits settings top tree D A x z hx pre s hs p hp m hm good a ha late
  refine le_trans (probEvent_mono fun r _ h => h.2) ?_
  by_cases kb : KnownTo D.1 b.1
  · exact known top tree D A x z Z hx pre s hs p hp m hm a b ha kb hopen
  · refine le_trans (le_of_eq (probEvent_congr' (fun r _ => sameSalt_comm r.2.2 a b) rfl)) ?_
    exact hidden_pair_le prims D _ m.2 (hiddenCoherent_first prims K circuits settings top tree D A x p
      (hiddenCoherent_setup prims D A x z pre s hs p hp) m hm) b a (Ne.symm hab) kb ha hopen

/-- A pair at the stage point whose second entry is a stage-2 entry and whose first entry, if
hidden, is also a stage-2 entry. -/
theorem rest_entry_le (known : KnownSecondBound prims K circuits settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (hx : DealtInputs D x) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (a b : C.Term × HashOutput × ℕ) (hab : a ≠ b)
    (lateB : b ∉ TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)
    (lateA : ¬ KnownTo D.1 a.1 → a ∉ TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) :
    Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧ SameSalt r.2.2 a b ∧
        (¬ KnownTo D.1 a.1 ∨ ¬ KnownTo D.1 b.1) |
      (simulateQ (treeSimLoggedWorld prims D)
        (restProgram circuits settings tree D A x Z m)).run m.2] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  by_cases kb : KnownTo D.1 b.1
  · by_cases ka : KnownTo D.1 a.1
    · refine le_trans (le_of_eq (probEvent_eq_zero fun r _ h => ?_)) (zero_le (α := ℝ≥0∞))
      rcases h.2.2 with h | h
      · exact h ka
      · exact h kb
    · refine le_trans (probEvent_mono ?_) (rest_pair_le prims K circuits settings known top tree D A
        x z Z hx pre s hs p hp m hm a b hab ka (lateA ka))
      exact fun r _ h => ⟨h.1, h.2.1⟩
  · refine le_trans (probEvent_mono ?_) (rest_pair_le prims K circuits settings known top tree D A
      x z Z hx pre s hs p hp m hm b a (Ne.symm hab) kb lateB)
    exact fun r _ h => ⟨h.1, (sameSalt_comm r.2.2 a b).mp h.2.1⟩

/-- `PairBoundsGuardedFrom` from the cross pairs of a hidden stage-1 entry and the two known-salt
estimates. Pairs of two hidden entries are paid by the lazy potential of `TreeSaltPairs`. -/
theorem pairBoundsGuardedFrom_of_parts
    (cross : CrossHiddenBound prims K circuits settings)
    (known₁ : KnownFirstBound prims K circuits settings)
    (known₂ : KnownSecondBound prims K circuits settings) :
    LifetimeSaltGuarded.PairBoundsGuardedFrom prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i j hij
  set F := TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2 with hF
  by_cases hj1 : j < F.card
  · -- Both entries are stage-1 entries, fixed at the end of the setup.
    have hi1 : i < F.card := hij.trans hj1
    set a := TreeSaltPairsFinal.enumerate F ⟨i, hi1⟩ with ha
    set b := TreeSaltPairsFinal.enumerate F ⟨j, hj1⟩ with hb'
    have hab : a ≠ b := fun h => by
      have := TreeSaltPairsFinal.enumerate_injective F h
      simp only [Fin.mk.injEq] at this
      omega
    calc _ ≤ Pr[(fun r : Bool × TreeSimLog C => SameSalt r.2 a b ∧
            (¬ KnownTo D.1 a.1 ∨ ¬ KnownTo D.1 b.1)) ∘ Prod.snd |
          (TreeSaltPairsFinal.splits prims K circuits settings top tree D A x Z p).paired] := by
          apply probEvent_mono
          rintro r - ⟨-, -, -, hi', hj', salt, hl, hk, hsa, hsb⟩
          rw [append_left_eq _ _ i hi' hi1] at hk hsa
          rw [append_left_eq _ _ j hj' hj1] at hk hsb
          exact ⟨⟨salt, hl, hsa, hsb⟩, hk⟩
      _ = Pr[fun r => SameSalt r.2.2 a b ∧ (¬ KnownTo D.1 a.1 ∨ ¬ KnownTo D.1 b.1) |
          (simulateQ (treeSimLoggedWorld prims D)
            (afterProgram K circuits settings top tree D A x Z p)).run p.2] := by
          rw [← probEvent_map, TreeSaltStageSplit.snd_paired, after_eq, probEvent_map]
          rfl
      _ ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          have hcoh := hiddenCoherent_setup prims D A x z pre s hs p hp
          have hopen := open_setup prims D A x z pre s hs p hp
          by_cases ka : KnownTo D.1 a.1
          · by_cases kb : KnownTo D.1 b.1
            · refine le_trans (le_of_eq (probEvent_eq_zero fun r _ h => ?_)) (zero_le (α := ℝ≥0∞))
              rcases h.2 with h | h
              · exact h ka
              · exact h kb
            · refine le_trans (probEvent_mono fun r _ h => (sameSalt_comm r.2.2 a b).mp h.1) ?_
              exact known₁ top tree D A x z Z hx pre s hs p hp b a kb ka (hopen b kb)
          · refine le_trans (probEvent_mono fun r _ h => h.1) ?_
            by_cases kb : KnownTo D.1 b.1
            · exact known₁ top tree D A x z Z hx pre s hs p hp a b ka kb (hopen a ka)
            · exact hidden_pair_le prims D _ p.2 hcoh a b hab ka kb (hopen b kb)
  by_cases hi1 : i < F.card
  · by_cases ka : KnownTo D.1 (TreeSaltPairsFinal.enumerate F ⟨i, hi1⟩).1
    swap
    · exact cross hb top tree D A x z Z q hx hq hsmall pre s hs p hp i j hi1 (not_lt.mp hj1) ka
    -- A known stage-1 entry: the stage-2 entry is the hidden one.
    change Pr[_ | TreeSaltPairsFinal.first prims K circuits settings top tree D A x p >>= fun m =>
      (fun r => (m, r)) <$> TreeSaltPairsFinal.rest prims circuits settings tree D A x Z m] ≤ _
    apply probEvent_bind_le_of_forall_le
    intro m hm
    rw [probEvent_map, rest_eq, probEvent_map]
    set S := TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A m
    by_cases hjm : j < F.card + S.card
    swap
    · refine le_trans (le_of_eq (probEvent_eq_zero fun r _ h => ?_)) (zero_le (α := ℝ≥0∞))
      obtain ⟨-, -, -, -, hj', -⟩ := h
      exact hjm hj'
    have hlate : TreeSaltPairsFinal.enumerate S ⟨j - F.card, by omega⟩ ∉ F :=
      (Finset.mem_sdiff.mp (TreeSaltPairsFinal.enumerate_mem S _)).2
    have hne : TreeSaltPairsFinal.enumerate F ⟨i, hi1⟩ ≠
        TreeSaltPairsFinal.enumerate S ⟨j - F.card, by omega⟩ := fun h =>
      hlate (h ▸ TreeSaltPairsFinal.enumerate_mem F _)
    refine le_trans (probEvent_mono ?_) (rest_entry_le prims K circuits settings known₂ top tree D A x z Z
      hx pre s hs p hp m hm _ _ hne hlate (fun h => (h ka).elim))
    rintro r - ⟨hc, -, -, hi', hj', salt, hl, hk, hsa, hsb⟩
    rw [append_left_eq _ _ i hi' hi1] at hk hsa
    rw [append_right_eq _ _ j hj' (not_lt.mp hj1)] at hk hsb
    exact ⟨hc, ⟨salt, hl, hsa, hsb⟩, hk⟩
  · -- Both entries are stage-2 entries of the stage view.
    change Pr[_ | TreeSaltPairsFinal.first prims K circuits settings top tree D A x p >>= fun m =>
      (fun r => (m, r)) <$> TreeSaltPairsFinal.rest prims circuits settings tree D A x Z m] ≤ _
    apply probEvent_bind_le_of_forall_le
    intro m hm
    rw [probEvent_map, rest_eq, probEvent_map]
    set S := TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A m
    by_cases hjm : j < F.card + S.card
    swap
    · refine le_trans (le_of_eq (probEvent_eq_zero fun r _ h => ?_)) (zero_le (α := ℝ≥0∞))
      obtain ⟨-, -, -, -, hj', -⟩ := h
      exact hjm hj'
    have late : ∀ k (hk : k < S.card), TreeSaltPairsFinal.enumerate S ⟨k, hk⟩ ∉ F := fun k hk =>
      (Finset.mem_sdiff.mp (TreeSaltPairsFinal.enumerate_mem S _)).2
    have hne : TreeSaltPairsFinal.enumerate S ⟨i - F.card, by omega⟩ ≠
        TreeSaltPairsFinal.enumerate S ⟨j - F.card, by omega⟩ := fun h => by
      have := TreeSaltPairsFinal.enumerate_injective S h
      simp only [Fin.mk.injEq] at this
      omega
    refine le_trans (probEvent_mono ?_) (rest_entry_le prims K circuits settings known₂ top tree D A x z Z
      hx pre s hs p hp m hm _ _ hne (late _ _) (fun _ => late _ _))
    rintro r - ⟨hc, -, -, hi', hj', salt, hl, hk, hsa, hsb⟩
    rw [append_right_eq _ _ i hi' (not_lt.mp hi1)] at hk hsa
    rw [append_right_eq _ _ j hj' (not_lt.mp hj1)] at hk hsb
    exact ⟨hc, ⟨salt, hl, hsa, hsb⟩, hk⟩

end Parts

namespace Local

set_option backward.isDefEq.respectTransparency false in
-- Copy of the private `treeSimLocalWorld_adversary` (`TreeSim.lean`).
theorem adversary_eq {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimLocalWorld (treeSimLocalRoles.adversary p) = worldRoles.adversary p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query]
    change (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t))) >>=
      fun a => simulateQ treeSimLocalWorld (treeSimLocalRoles.adversary (k a))) = _
    rw [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a) from rfl,
      adversary_query]
    simp only [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
-- Copy of the private `treeSimLocalWorld_honest` (`TreeSim.lean`).
theorem honest_eq {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimLocalWorld (treeSimLocalRoles.honest p) = free p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query, free_bind]
    change (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t)) >>=
      fun a => simulateQ treeSimLocalWorld (treeSimLocalRoles.honest (k a))) = _
    simp only [ih]
    rfl

theorem roles_eq : simRoles treeSimLocalWorld (treeSimLocalRoles (C := C)) = worldRoles := by
  unfold simRoles
  congr 1
  · funext α p
    exact adversary_eq p
  · funext α p
    exact honest_eq p

end Local

section LocalPrograms

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `restProgram` without a programming interface. -/
def localRest (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (m : TreeSimConfig A (TreeSimState C)) :
    OracleComp (LocalSpec C + LocalSpec C) Bool := do
  let out ← executeRounds treeSimLocalRoles D A noFunctionality
    (ceremonyFuel circuits settings - setupRounds -
      TreeSaltPairsFinal.firstRounds circuits settings tree (TreeSaltPairsFinal.parameter x))
    m.1.1 m.1.2
  treeSimLocalRoles.adversary (Z out)

theorem restProgram_local (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (m : TreeSimConfig A (TreeSimState C)) :
    restProgram circuits settings tree D A x Z m =
      simulateQ treeSimLocalWorld (localRest circuits settings tree D A x Z m) := by
  unfold restProgram localRest
  simp only [simulateQ_bind, simulateQ_executeRounds, Local.roles_eq, Local.adversary_eq]

/-- `afterProgram` without a programming interface. -/
def localAfter (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    OracleComp (LocalSpec C + LocalSpec C) Bool := do
  let next ← treeSimLocalRoles.honest (Concrete.sequenceFin fun i =>
    continueStep (treeSimRealCont K circuits settings top tree x i) (.done (p.1.2 i)))
  let out ← executeRounds treeSimLocalRoles D A noFunctionality
    (ceremonyFuel circuits settings - setupRounds) p.1.1 next
  treeSimLocalRoles.adversary (Z out)

theorem afterProgram_local (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    afterProgram K circuits settings top tree D A x Z p =
      simulateQ treeSimLocalWorld (localAfter K circuits settings top tree D A x Z p) := by
  unfold afterProgram localAfter treeSimContinue
  simp only [simulateQ_bind, simulateQ_executeRounds, Local.roles_eq, Local.adversary_eq,
    Local.honest_eq]

end LocalPrograms

section KnownPotential

variable (prims : Primitives) (a b : C.Term × HashOutput × ℕ)

/-- Bit `g` of the known salt at `b` under the derived stream key `k`. -/
def keyBit (k : HashOutput) (g : Fin 256) : Bit :=
  prims.aes.eval (truncateHash k) (b.2.2, 2, g.val)

/-- The weight of the candidate key `k` of `H(.streamKey key)` for the known address `b`: the
point mass at the cached value, or the uniform weight while it is not cached. -/
def keyWeight (cache : HashCache C) (k : HashOutput) : ℝ≥0∞ :=
  match cache (.streamKey b.2.1) with
  | some k' => if k = k' then 1 else 0
  | none => (Fintype.card HashOutput : ℝ≥0∞)⁻¹

/-- The pair potential of the hidden salt at `a` and the known salt at `b`, averaged over the
derived stream key of `b`. -/
def knownPotential (c : HashCache C × HiddenCache C) : ℝ≥0∞ :=
  ∑ k : HashOutput, keyWeight b c.1 k *
    saltPairWeight (fun g => .inl (saltPoint a g)) (fun g => .inr (keyBit prims b k g)) c.2

theorem keyWeight_sum (cache : HashCache C) : ∑ k : HashOutput, keyWeight b cache k = 1 := by
  unfold keyWeight
  cases cache (.streamKey b.2.1) with
  | some k' => simp
  | none =>
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)

/-- One lazy hash query keeps the expected key weight. -/
theorem keyWeight_randomOracle (q : Query C) (cache : HashCache C) (k : HashOutput) :
    ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle q).run cache] * keyWeight b r.2 k ≤
      keyWeight b cache k := by
  cases hc : cache q with
  | some v =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, tsum_probOutput_pure_mul]
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, tsum_probOutput_map_mul,
      tsum_fintype]
    have hp : ∀ v : HashOutput, Pr[= v | uniformSampleImpl (spec := (Query C →ₒ HashOutput)) q] =
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
      intro v
      simp [uniformSampleImpl, probOutput_uniformSample]
    simp only [hp]
    by_cases hq : q = .streamKey b.2.1
    · subst hq
      have hk : ∀ v : HashOutput, keyWeight b (cache.cacheQuery (.streamKey b.2.1) v) k =
          if k = v then 1 else 0 := fun v => by
        simp only [keyWeight, QueryCache.cacheQuery_self]
      have h0 : keyWeight b cache k = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        simp only [keyWeight, hc]
      simp only [hk, h0, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        le_refl]
    · have hk : ∀ v : HashOutput, keyWeight b (cache.cacheQuery q v) k = keyWeight b cache k :=
        fun v => by
          simp only [keyWeight, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]
      simp only [hk]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- A step that keeps the derived key of `b` keeps the expected key weight. -/
theorem keyWeight_keep {σ β : Type} (step : ProbComp (β × σ)) (pub : σ → HashCache C) (s : σ)
    (k : HashOutput) (hkeep : ∀ r ∈ support step,
      (pub r.2) (.streamKey b.2.1) = (pub s) (.streamKey b.2.1)) :
    ∑' r, Pr[= r | step] * keyWeight b (pub r.2) k ≤ keyWeight b (pub s) k := by
  calc ∑' r, Pr[= r | step] * keyWeight b (pub r.2) k
      = ∑' r, Pr[= r | step] * keyWeight b (pub s) k := by
        refine tsum_congr fun r => ?_
        by_cases hr : r ∈ support step
        · simp only [keyWeight, hkeep r hr]
        · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ = (∑' r, Pr[= r | step]) * keyWeight b (pub s) k := ENNReal.tsum_mul_right
    _ ≤ keyWeight b (pub s) k := mul_le_of_le_one_left (zero_le) tsum_probOutput_le_one

/-- Each local query keeps the expected key weight. -/
theorem keyWeight_local (t : (LocalSpec C).Domain) (cache : HashCache C) (k : HashOutput) :
    ∑' r, Pr[= r | (localAnswer prims t).run cache] * keyWeight b r.2 k ≤ keyWeight b cache k := by
  rcases t with n | q | x
  · apply keyWeight_keep b _ id cache k
    intro r hr
    have h := unifFwdImpl.simulateQ_run (hashSpec := (Query C →ₒ HashOutput))
      (OracleComp.lift (OracleSpec.query (spec := unifSpec) n)) cache
    simp only [simulateQ_spec_query] at h
    change r ∈ support (((unifFwdImpl (Query C →ₒ HashOutput)) n).run cache) at hr
    rw [h, support_map] at hr
    obtain ⟨v, -, rfl⟩ := hr
    rfl
  · change ∑' r, Pr[= r | (hashAnswer prims q).run cache] * keyWeight b r.2 k ≤ _
    unfold hashAnswer
    split
    · split_ifs
      · exact keyWeight_keep b _ id cache k (fun r hr => by
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl)
      · exact keyWeight_randomOracle b _ cache k
    · exact keyWeight_randomOracle b _ cache k
  · change ∑' r, Pr[= r | (prgAnswer prims x).run cache] * keyWeight b r.2 k ≤ _
    simp only [prgAnswer, bind_pure_comp]
    rw [StateT.run_map, tsum_probOutput_map_mul]
    exact keyWeight_randomOracle b _ cache k

theorem known_distinct (k : HashOutput) :
    SaltPairDistinct (fun g => .inl (saltPoint a g)) (fun g => .inr (keyBit prims b k g)) := by
  rintro (g | g) (g' | g') d hx hy <;> simp only [Sum.elim_inl, Sum.elim_inr] at hx hy
  · rw [← hy, Sum.inl.injEq] at hx
    simp only [saltPoint, Prod.mk.injEq] at hx
    exact congrArg Sum.inl (Fin.ext hx.2.2.2)
  all_goals cases hx <;> cases hy

/-- A public step that keeps the expected key weight of every candidate key keeps the expected
potential. -/
theorem potential_public {β : Type} (m : StateT (HashCache C) ProbComp β)
    (c : HashCache C × HiddenCache C)
    (hm : ∀ k, ∑' r, Pr[= r | m.run c.1] * keyWeight b r.2 k ≤ keyWeight b c.1 k) :
    ∑' r, Pr[= r | (onHash m).run c] * knownPotential prims a b r.2 ≤ knownPotential prims a b c := by
  simp only [onHash, StateT.run_mk, knownPotential]
  rw [tsum_probOutput_map_mul]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [← mul_assoc]
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left (hm k) _

/-- A hidden-stream step keeps the expected potential. -/
theorem potential_hidden (d : (KeyName C × HashOutput) × ℕ × ℕ × ℕ)
    (c : HashCache C × HiddenCache C) :
    ∑' r, Pr[= r | (fun r => (r.1, (c.1, r.2))) <$>
        ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle d).run c.2] *
      knownPotential prims a b r.2 ≤ knownPotential prims a b c := by
  simp only [knownPotential]
  rw [tsum_probOutput_map_mul]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [tsum_congr fun r => mul_left_comm _ _ _, ENNReal.tsum_mul_left]
  exact mul_le_mul_right (saltPairWeight_randomOracle (known_distinct prims a b k) d c.2) _

/-- Each nonprogramming query of the logged world keeps the expected potential. -/
theorem potential_step (D : C.Coalition) (t : (LocalSpec C + LocalSpec C).Domain)
    (s : TreeSimState C) :
    ∑' r, Pr[= r | ((treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld) t).run s] *
      knownPotential prims a b r.2.1 ≤ knownPotential prims a b s.1 := by
  have world : ∀ u : (WorldSpec C).Domain,
      ∑' r, Pr[= r | (streamWorld prims D u).run s.1] * knownPotential prims a b r.2 ≤
        knownPotential prims a b s.1 →
      ∑' r, Pr[= r | (simulateQ (treeSimLoggedWorld prims D)
        (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) u))).run s] *
          knownPotential prims a b r.2.1 ≤ knownPotential prims a b s.1 := by
    intro u h
    rw [simulateQ_spec_query]
    simp only [treeSimLoggedWorld, StateT.run_mk]
    rw [tsum_probOutput_map_mul]
    exact h
  rcases t with t | t
  · apply world (.inl (.inl t))
    exact potential_public prims a b _ s.1 (fun k => keyWeight_local prims b t s.1.1 k)
  · apply world (.inr t)
    rcases t with n | q | x
    · exact potential_public prims a b _ s.1 (fun k => keyWeight_local prims b (.inl n) s.1.1 k)
    · exact potential_public prims a b _ s.1 (fun k => keyWeight_local prims b (.inr (.inl q)) s.1.1 k)
    · by_cases hx : Hidden D x.1
      · simp only [streamWorld, if_pos hx, StateT.run_mk]
        exact potential_hidden prims a b _ s.1
      · simp only [streamWorld, if_neg hx]
        exact potential_public prims a b _ s.1
          (fun k => keyWeight_local prims b (.inr (.inr x)) s.1.1 k)

/-- The cache `c'` keeps every entry of `c`. -/
def Grows (c c' : HashCache C) : Prop := ∀ q v, c q = some v → c' q = some v

theorem grows_randomOracle (q : Query C) (cache : HashCache C)
    (r : HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle q).run cache)) :
    Grows cache r.2 ∧ r.2 q = some r.1 := by
  cases hc : cache q with
  | some v =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨fun _ _ h => h, hc⟩
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, support_map,
      Set.mem_image] at hr
    obtain ⟨v, -, rfl⟩ := hr
    refine ⟨fun q' w h => ?_, QueryCache.cacheQuery_self _ _ _⟩
    by_cases hq : q' = q
    · subst hq
      rw [hc] at h
      cases h
    · exact (QueryCache.cacheQuery_of_ne _ _ hq).trans h

theorem grows_hash (q : Query C) (cache : HashCache C) :
    ∀ r ∈ support ((hashAnswer prims q).run cache), Grows cache r.2 := by
  intro r hr
  unfold hashAnswer at hr
  split at hr
  · split_ifs at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact fun _ _ h => h
    · exact (grows_randomOracle _ cache r hr).1
  · exact (grows_randomOracle _ cache r hr).1

theorem prg_value (x : PrgInput C) (cache : HashCache C) :
    ∀ r ∈ support ((prgAnswer prims x).run cache), Grows cache r.2 ∧
      ∃ k, r.2 (.streamKey x.2.1) = some k ∧ r.1 = prims.aes.eval (truncateHash k) x.2.2 := by
  intro r hr
  simp only [prgAnswer, bind_pure_comp] at hr
  rw [StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨o, ho, rfl⟩ := hr
  obtain ⟨grow, hk⟩ := grows_randomOracle _ cache o ho
  exact ⟨grow, o.1, hk, rfl⟩

theorem grows_local (t : (LocalSpec C).Domain) (cache : HashCache C) :
    ∀ r ∈ support ((localAnswer prims t).run cache), Grows cache r.2 := by
  intro r hr
  rcases t with n | q | x
  · have h := unifFwdImpl.simulateQ_run (hashSpec := (Query C →ₒ HashOutput))
      (OracleComp.lift (OracleSpec.query (spec := unifSpec) n)) cache
    simp only [simulateQ_spec_query] at h
    change r ∈ support (((unifFwdImpl (Query C →ₒ HashOutput)) n).run cache) at hr
    rw [h, support_map] at hr
    obtain ⟨v, -, rfl⟩ := hr
    exact fun _ _ h => h
  · exact grows_hash prims q cache r hr
  · exact (prg_value prims x cache r hr).1

theorem grows_program (x : Query C × HashOutput) (cache : HashCache C) :
    ∀ r ∈ support ((programAnswer (C := C) x).run cache), Grows cache r.2 := by
  intro r hr
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact fun _ _ h => h
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr
    intro q v hq
    by_cases hqx : q = x.1
    · subst hqx
      simp [hq] at h
    · exact (QueryCache.cacheQuery_of_ne _ _ hqx).trans hq

/-- Each logged known-stream answer is AES under the cached derived key. -/
def PublicCoherent (D : C.Coalition) (s : TreeSimState C) : Prop :=
  ∀ (y : PrgInput C) (c : Bit), ¬ Hidden D y.1 →
    (⟨.inr (.inr (.inr y)), c⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ s.2 →
    ∃ k, s.1.1 (.streamKey y.2.1) = some k ∧ c = prims.aes.eval (truncateHash k) y.2.2

theorem publicCoherent_extend (D : C.Coalition) (s : TreeSimState C)
    (hs : PublicCoherent prims D s) (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t)
    (c : HashCache C × HiddenCache C) (grow : Grows s.1.1 c.1)
    (hnew : ∀ y v, ¬ Hidden D y.1 →
      (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) = ⟨.inr (.inr (.inr y)), v⟩ →
      ∃ k, c.1 (.streamKey y.2.1) = some k ∧ v = prims.aes.eval (truncateHash k) y.2.2) :
    PublicCoherent prims D (c, s.2 ++ [⟨t, u⟩]) := by
  intro y v hy hmem
  rcases List.mem_append.mp hmem with old | new
  · obtain ⟨k, hk, hv⟩ := hs y v hy old
    exact ⟨k, grow _ _ hk, hv⟩
  · exact hnew y v hy (List.mem_singleton.mp new).symm

/-- Each query of the logged world keeps the public coherence. -/
theorem publicCoherent_step (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : TreeSimState C) (hs : PublicCoherent prims D s) (z : (WorldSpec C).Range t × TreeSimState C)
    (hz : z ∈ support ((treeSimLoggedWorld prims D t).run s)) : PublicCoherent prims D z.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have pubGrow : ∀ {β : Type} (m : StateT (HashCache C) ProbComp β)
      (grow : ∀ o ∈ support (m.run s.1.1), Grows s.1.1 o.2)
      (r : β × HashCache C × HiddenCache C), r ∈ support ((onHash m).run s.1) →
      Grows s.1.1 r.2.1 := by
    intro β m grow r hr
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨o, ho, rfl⟩ := hr
    exact grow o ho
  rcases t with t | (t | t | x)
  · refine publicCoherent_extend prims D s hs _ _ _ ?_ (fun y v _ h => by simp at h)
    rcases t with t | x
    · exact pubGrow _ (grows_local prims t s.1.1) r hr
    · exact pubGrow _ (grows_program x s.1.1) r hr
  · exact publicCoherent_extend prims D s hs _ _ _
      (pubGrow _ (grows_local prims (.inl t) s.1.1) r hr) (fun y v _ h => by simp at h)
  · exact publicCoherent_extend prims D s hs _ _ _
      (pubGrow _ (grows_local prims (.inr (.inl t)) s.1.1) r hr) (fun y v _ h => by simp at h)
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨o, -, rfl⟩ := hr
      refine publicCoherent_extend prims D s hs _ _ _ (fun _ _ h => h) (fun y v hy h => ?_)
      simp only [Sigma.mk.inj_iff, Sum.inr.injEq] at h
      exact (hy (h.1 ▸ hx)).elim
    · simp only [streamWorld, if_neg hx, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨o, ho, rfl⟩ := hr
      obtain ⟨grow, k, hk, hv⟩ := prg_value prims x s.1.1 o ho
      refine publicCoherent_extend prims D s hs _ _ _ grow (fun y v hy h => ?_)
      simp only [Sigma.mk.inj_iff, Sum.inr.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq] at h
      exact ⟨k, hk, h ▸ hv⟩

theorem publicCoherent_empty (D : C.Coalition) :
    PublicCoherent prims D (((∅, ∅), []) : TreeSimState C) := by
  intro y c _ h
  simp at h

theorem publicCoherent_run (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) (hs : PublicCoherent prims D s) :
    ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) oa).run s), PublicCoherent prims D z.2 :=
  simulateQ_run_preserves_inv_of_query _ _
    (fun t s hs z hz => publicCoherent_step prims D t s hs z hz) oa s hs

/-- From a coherent state where the hidden salt at `a` is unread, a nonprogramming run makes it
equal to the known salt at `b` with probability at most `2^-256`. -/
theorem known_pair_le (D : C.Coalition) {α : Type}
    (g : OracleComp (LocalSpec C + LocalSpec C) α) (s : TreeSimState C)
    (hs : HiddenCoherent D s) (hpub : PublicCoherent prims D s)
    (ha : ¬ KnownTo D.1 a.1) (hb : KnownTo D.1 b.1)
    (hopen : ∀ g, s.1.2 (saltPoint a g) = none) :
    Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld g)).run s] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have mono : Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld g)).run s] ≤
      Pr[fun r => 1 ≤ knownPotential prims a b r.2.1 | (simulateQ (treeSimLoggedWorld prims D)
        (simulateQ treeSimLocalWorld g)).run s] := by
    apply probEvent_mono
    rintro r hr ⟨salt, -, hsa, hsb⟩
    have hc := hiddenCoherent_run prims D _ s hs r hr
    have hp := publicCoherent_run prims D _ s hpub r hr
    have hknown : ¬ Hidden D (KeyName.term b.1) := fun h => h hb
    obtain ⟨k, hk, -⟩ := hp (.term b.1, b.2.1, b.2.2, 2, 0) _ hknown (hsb ⟨0, by norm_num⟩)
    refine le_trans ?_ (Finset.single_le_sum (fun k _ => zero_le (α := ℝ≥0∞)) (Finset.mem_univ k))
    have hw : keyWeight b r.2.1.1 k = 1 := by simp [keyWeight, hk]
    rw [hw, one_mul]
    apply saltPairWeight_of_equal
    intro g
    refine ⟨salt.getD g.val 0, (hc (.term a.1, a.2.1, a.2.2, 2, g.val) _ ha).mp (hsa g), ?_⟩
    obtain ⟨k', hk', hv⟩ := hp (.term b.1, b.2.1, b.2.2, 2, g.val) _ hknown (hsb g)
    rw [hk] at hk'
    cases hk'
    simp only [saltSideValue, keyBit, Option.some.injEq]
    exact hv.symm
  refine mono.trans ?_
  rw [← QueryImpl.simulateQ_compose]
  have key := XmssSecurity.probEvent_le_expectedFinal
    (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld) (fun s : TreeSimState C => knownPotential prims a b s.1)
    (fun s => 1 ≤ knownPotential prims a b s.1) (fun _ h => h) g s
  refine key.trans ?_
  have h := XmssSecurity.expectedFinal_le (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld)
    (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) (fun s => knownPotential prims a b s.1)
    (fun _ _ => 0) (fun t s _ => by simpa only [add_zero] using potential_step prims a b D t s) g s trivial
  have hz : XmssSecurity.expectedSimulatedCost (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld)
      (fun _ _ => 0) g s = 0 := by
    simpa using XmssSecurity.expectedSimulatedCost_const_mul
      (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld) 0 (fun _ _ => 0) g s
  rw [hz, add_zero] at h
  refine h.trans (le_of_eq ?_)
  have hopen' : ∀ k : HashOutput, saltPairWeight (fun g => .inl (saltPoint a g))
      (fun g => .inr (keyBit prims b k g)) s.1.2 = (2 ^ 256 : ℝ≥0∞)⁻¹ := fun k =>
    saltPairWeight_of_open (fun g => Or.inl (by simpa [saltSideValue] using hopen g))
  simp only [knownPotential, hopen', ← Finset.sum_mul, keyWeight_sum, one_mul]

end KnownPotential

section Known

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem publicCoherent_setup (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    PublicCoherent prims D p.2 := by
  have h0 := publicCoherent_run prims D _ _ (publicCoherent_empty prims D) s hs
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  have h1 := publicCoherent_run prims D _ _ h0 start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  exact publicCoherent_run prims D _ _ h1 p hp

theorem publicCoherent_first (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : PublicCoherent prims D p.2) (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p)) :
    PublicCoherent prims D m.2 := by
  simp only [TreeSaltPairsFinal.first, mem_support_bind_iff] at hm
  obtain ⟨next, hnext, hm⟩ := hm
  have h1 := publicCoherent_run prims D _ _ hp next hnext
  rw [treeSimRealRoles, ← simulateQ_executeSteps] at hm
  exact publicCoherent_run prims D _ _ h1 m hm

theorem knownFirstBound : KnownFirstBound prims K circuits settings := by
  intro top tree D A x z Z _ α pre s hs p hp a b ha hb hopen
  rw [afterProgram_local]
  exact known_pair_le prims a b D _ p.2 (hiddenCoherent_setup prims D A x z pre s hs p hp)
    (publicCoherent_setup prims D A x z pre s hs p hp) ha hb hopen

theorem knownSecondBound : KnownSecondBound prims K circuits settings := by
  intro top tree D A x z Z _ α pre s hs p hp m hm a b ha hb hopen
  rw [restProgram_local]
  exact known_pair_le prims a b D _ m.2
    (hiddenCoherent_first prims K circuits settings top tree D A x p
      (hiddenCoherent_setup prims D A x z pre s hs p hp) m hm)
    (publicCoherent_first prims K circuits settings top tree D A x p
      (publicCoherent_setup prims D A x z pre s hs p hp) m hm) ha hb hopen

/-- `PairBoundsGuardedFrom` from its cross pairs alone. -/
theorem pairBoundsGuardedFrom_of_cross (cross : CrossHiddenBound prims K circuits settings) :
    LifetimeSaltGuarded.PairBoundsGuardedFrom prims K circuits settings :=
  pairBoundsGuardedFrom_of_parts prims K circuits settings cross
    (knownFirstBound prims K circuits settings) (knownSecondBound prims K circuits settings)

/-- `CrossHiddenBound` is the restriction of `PairBoundsGuardedFrom` to the cross pairs. -/
theorem crossHiddenBound_of_pairBounds
    (bounds : LifetimeSaltGuarded.PairBoundsGuardedFrom prims K circuits settings) :
    CrossHiddenBound prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i j hi hj _
  exact bounds hb top tree D A x z Z q hx hq hsmall pre s hs p hp i j (lt_of_lt_of_le hi hj)

end Known

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.hiddenCoherent_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenCoherent_step

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.hiddenCoherent_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenCoherent_run

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.hiddenCoherent_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenCoherent_setup

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.hiddenCoherent_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenCoherent_first

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.rest_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rest_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.after_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms after_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.hidden_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hidden_pair_le

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.open_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms open_setup

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.open_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms open_first

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.rest_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rest_pair_le

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.rest_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rest_entry_le

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.pairBoundsGuardedFrom_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairBoundsGuardedFrom_of_parts

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.Local.roles_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Local.roles_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.restProgram_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms restProgram_local

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.afterProgram_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterProgram_local

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.keyWeight_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keyWeight_local

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.potential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms potential_step

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.publicCoherent_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicCoherent_step

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.known_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms known_pair_le

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.knownFirstBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms knownFirstBound

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.knownSecondBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms knownSecondBound

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.pairBoundsGuardedFrom_of_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairBoundsGuardedFrom_of_cross

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound.crossHiddenBound_of_pairBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossHiddenBound_of_pairBounds

end ThresholdLeanXmssSecurity.TreeSaltGuardedPairBound
