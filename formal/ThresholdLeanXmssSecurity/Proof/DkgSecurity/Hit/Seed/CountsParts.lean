import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CountsList
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Count

/-!
# The count of the named shifts in the reference run

* `shiftCell T parts δ` is the hidden cell of `T` on the parts shifted by `δ`. It is injective in `δ`
  (`shiftCell_injective`), so one cell names at most one shift.
* `hiddenShifts` are the shifts whose cell is the hidden cell of another hidden term. They are at most
  `h - 1` (`encard_hiddenShifts`).
* `gauge` is the number of the named shifts outside `hiddenShifts`. A call of `loggedWorld` or of
  `partsWorld` changes the cache only at the cell of the call or at a stream key, and adds only the cell
  of a programming call to the list. So `gauge` grows by at most one at a call of `ShiftCharged`, a call at
  a cell `shiftCell T parts δ` with `δ` outside `hiddenShifts` (`loggedWorld_gauge`, `partsWorld_gauge`).
* `PartsWalk` states that the reference suffix makes at most `(n + 1) k` free or programming calls of
  `ShiftCharged`. `partsCount_of_walk` gives `PartsCount` from it. The prefix is the start of the adversary,
  which makes only counted calls.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal (seedGenAt commitAddress commitDrawsAt)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)
open PFunctor.FreeM (cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The cell of a call -/

/-- The cell of a counted call of `H`, of a programming call or of a free call of `H`. -/
def cellOf : (WorldSpec C).Domain → Option (Query C)
  | .inl (.inl (.inr (.inl q))) => some q
  | .inl (.inr x) => some x.1
  | .inr (.inr (.inl q)) => some q
  | _ => none

/-- A call of `loggedWorld` changes the cache only at the cell of the call or at a stream key. -/
theorem loggedWorld_cacheCell (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w), ∀ Y : Query C,
      z.2.1.1 Y ≠ w.1.1 Y → cellOf t = some Y ∨ ∃ key, Y = .streamKey key := by
  intro z hz Y hd
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with (u | p) | u
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    rw [localProgram_inl] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    rcases localAnswer_other prims u _ r' hr' _ hd with rfl | ⟨key, hk⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨key, hk⟩
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    rw [localProgram_inr] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have e := programAnswer_other p _ r' hr' _ hd
    obtain ⟨q, v⟩ := p
    dsimp only at e
    subst e
    exact Or.inl rfl
  · rcases u with n | q | x
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      rcases localAnswer_other prims (Sum.inl n) _ r' hr' _ hd with h | ⟨key, hk⟩
      · cases h
      · exact Or.inr ⟨key, hk⟩
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      rcases localAnswer_other prims (Sum.inr (Sum.inl q)) _ r' hr' _ hd with h | ⟨key, hk⟩
      · cases h
        exact Or.inl rfl
      · exact Or.inr ⟨key, hk⟩
    · simp only [streamWorld] at hr
      split_ifs at hr
      · simp only [StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨r', -, rfl⟩ := hr
        exact absurd rfl hd
      · simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        rcases localAnswer_other prims (Sum.inr (Sum.inr x)) _ r' hr' _ hd with h | ⟨key, hk⟩
        · cases h
        · exact Or.inr ⟨key, hk⟩

/-! ## The cells of the shifts -/

section Cells

variable (D : C.Coalition) (T : C.Term) (parts : C.Party → Parts C)

/-- The hidden cell of `T` on the parts shifted by `δ` at the holders of `T`. -/
def shiftCell (δ : {k // k ∈ C.holders T} → HashOutput) : Query C :=
  hiddenInput (SeedCompare.shiftAll T (extendShift T δ) parts) T

theorem shiftCell_eq (δ : {k // k ∈ C.holders T} → HashOutput) :
    shiftCell T parts δ =
      .derive .seedGen .term ((seedGenHolderList T).map fun k => (parts k).term T ^^^ extendShift T δ k) := by
  simp [shiftCell, hiddenInput, SeedCompare.shiftAll, shiftParts]

theorem shiftCell_injective : Function.Injective (shiftCell T parts) := by
  intro δ δ' h
  rw [shiftCell_eq, shiftCell_eq] at h
  simp only [Query.derive.injEq, true_and] at h
  funext k
  have hmem : k.1 ∈ seedGenHolderList T := by
    simp [seedGenHolderList, Committee.parties, k.2]
  have hk := (List.map_inj_left.1 h) k.1 hmem
  simp only [extendShift, k.2, ↓reduceDIte] at hk
  have hk' := congrArg (fun v => (parts k.1).term T ^^^ v) hk
  simp only [xor_cancel_left] at hk'
  exact hk'

theorem shiftCell_ne_streamKey (δ : {k // k ∈ C.holders T} → HashOutput) (key : HashOutput) :
    shiftCell T parts δ ≠ .streamKey key := by
  rw [shiftCell_eq]
  exact fun h => by cases h

/-- The cell `Y` is the hidden cell of a hidden term other than `T`. -/
def OtherHidden (Y : Query C) : Prop := ∃ T', T' ≠ T ∧ ¬ KnownTo D.1 T' ∧ Y = hiddenInput parts T'

/-- The shifts whose cell is the hidden cell of another hidden term. -/
def hiddenShifts : Set ({k // k ∈ C.holders T} → HashOutput) := {δ | OtherHidden D T parts (shiftCell T parts δ)}

theorem encard_hiddenShifts (hT : ¬ KnownTo D.1 T) :
    (hiddenShifts D T parts).encard ≤ (((hiddenTerms D).card - 1 : ℕ) : ℕ∞) := by
  rw [← (shiftCell_injective T parts).injOn.encard_image]
  have hsub : shiftCell T parts '' hiddenShifts D T parts ⊆
      hiddenInput parts '' ↑((hiddenTerms D).erase T) := by
    rintro _ ⟨δ, ⟨T', hne, hk, he⟩, rfl⟩
    exact ⟨T', by simp [hiddenTerms, hne, hk], he.symm⟩
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_erase_of_mem (by simp [hiddenTerms, hT])]

/-- The shifts whose cell is in the cache or in the list of the programming cells. -/
def namedSet (cache : HashCache C) (list : List (Query C)) : Set ({k // k ∈ C.holders T} → HashOutput) :=
  {δ | (cache (shiftCell T parts δ)).isSome ∨ shiftCell T parts δ ∈ list}

theorem coe_partsNamed (s : PartsState C) : (↑(partsNamed T parts s) : Set _) = namedSet T parts s.1.1.1 s.2.2 := by
  ext δ
  simp only [partsNamed, Finset.coe_filter, Finset.mem_univ, true_and]
  rfl

/-- The named shifts outside `hiddenShifts`. -/
def gauge (cache : HashCache C) (list : List (Query C)) : ℕ∞ :=
  (namedSet T parts cache list \ hiddenShifts D T parts).encard

/-- A call at the cell of a shift outside `hiddenShifts`. -/
def ShiftCharged (t : (WorldSpec C).Domain) : Prop :=
  ∃ δ, cellOf t = some (shiftCell T parts δ) ∧ δ ∉ hiddenShifts D T parts

theorem gauge_step {c c' : HashCache C} {l l' : List (Query C)} {t : (WorldSpec C).Domain}
    (h : namedSet T parts c' l' ⊆ namedSet T parts c l ∪ {δ | cellOf t = some (shiftCell T parts δ)}) :
    gauge D T parts c' l' ≤ gauge D T parts c l + if ShiftCharged D T parts t then 1 else 0 := by
  unfold gauge
  have hsub : namedSet T parts c' l' \ hiddenShifts D T parts ⊆ (namedSet T parts c l \ hiddenShifts D T parts) ∪
      ({δ | cellOf t = some (shiftCell T parts δ)} \ hiddenShifts D T parts) := by
    rintro δ ⟨h1, h2⟩
    rcases h h1 with h3 | h3
    · exact Or.inl ⟨h3, h2⟩
    · exact Or.inr ⟨h3, h2⟩
  refine (Set.encard_le_encard hsub).trans ((Set.encard_union_le _ _).trans (add_le_add le_rfl ?_))
  split_ifs with hc
  · exact Set.encard_le_one_iff.2 fun a b ha hb =>
      shiftCell_injective T parts (Option.some_injective _ (ha.1.symm.trans hb.1))
  · simp only [nonpos_iff_eq_zero, Set.encard_eq_zero]
    exact Set.eq_empty_iff_forall_notMem.2 fun δ hδ => hc ⟨δ, hδ.1, hδ.2⟩

variable (prims : Primitives)

theorem loggedWorld_named (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w), ∀ l : List (Query C),
      namedSet T parts z.2.1.1 l ⊆ namedSet T parts w.1.1 l ∪ {δ | cellOf t = some (shiftCell T parts δ)} := by
  intro z hz l δ hδ
  rcases hδ with h | h
  · by_cases he : z.2.1.1 (shiftCell T parts δ) = w.1.1 (shiftCell T parts δ)
    · exact Or.inl (Or.inl (by rw [← he]; exact h))
    · rcases loggedWorld_cacheCell prims D t w z hz _ he with h' | ⟨key, hk⟩
      · exact Or.inr h'
      · exact absurd hk (shiftCell_ne_streamKey T parts δ key)
  · exact Or.inl (Or.inr h)

theorem loggedWorld_gauge (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w),
      gauge D T parts z.2.1.1 [] ≤ gauge D T parts w.1.1 [] + if ShiftCharged D T parts t then 1 else 0 :=
  fun z hz => gauge_step D T parts (loggedWorld_named D T parts prims t w z hz [])

theorem partsWorld_named (t : (WorldSpec C).Domain) (s : PartsState C) :
    ∀ z ∈ support ((partsWorld prims D t).run s), namedSet T parts z.2.1.1.1 z.2.2.2 ⊆
      namedSet T parts s.1.1.1 s.2.2 ∪ {δ | cellOf t = some (shiftCell T parts δ)} := by
  intro z hz
  unfold partsWorld at hz
  split at hz
  · split_ifs at hz
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨r, -, rfl⟩ := hz
      exact Set.subset_union_left
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      exact loggedWorld_named D T parts prims _ s.1 r hr s.2.2
  · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rintro δ (h | h)
    · rcases loggedWorld_named D T parts prims _ s.1 r hr s.2.2 (Or.inl h) with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rcases List.mem_append.1 h with h' | h'
      · exact Or.inl (Or.inr h')
      · rw [List.mem_singleton] at h'
        refine Or.inr ?_
        change cellOf _ = some (shiftCell T parts δ)
        rw [h']
        rfl
  · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact loggedWorld_named D T parts prims _ s.1 r hr s.2.2

theorem partsWorld_gauge (t : (WorldSpec C).Domain) (s : PartsState C) :
    ∀ z ∈ support ((partsWorld prims D t).run s),
      gauge D T parts z.2.1.1.1 z.2.2.2 ≤ gauge D T parts s.1.1.1 s.2.2 + if ShiftCharged D T parts t then 1 else 0 :=
  fun z hz => gauge_step D T parts (partsWorld_named D T parts prims t s z hz)

/-- A free call or a programming call of `ShiftCharged`. -/
def FreeCharged (t : (WorldSpec C).Domain) : Prop := ShiftCharged D T parts t ∧ ¬ DkgSecurityProof.Logged t

theorem shiftCharged_cases (t : (WorldSpec C).Domain) (h : ShiftCharged D T parts t) :
    DkgSecurityProof.Logged t ∨ FreeCharged D T parts t := by
  by_cases hl : DkgSecurityProof.Logged t
  · exact Or.inl hl
  · exact Or.inr ⟨h, hl⟩

theorem freeCharged_cases (t : (WorldSpec C).Domain) (h : FreeCharged D T parts t) :
    SetupBudgets.HonestP (fun u : (LocalSpec C).Domain => ∃ q, u = .inr (.inl q)) t ∨ WorldProgramQuery t := by
  obtain ⟨⟨δ, hc, -⟩, hl⟩ := h
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals first
    | exact absurd trivial hl
    | exact Or.inr trivial
    | exact Or.inl ⟨_, rfl⟩
    | simp [cellOf] at hc

/-- The start of the adversary makes no free call and no programming call. -/
theorem noFree_observe {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (observe oa) (FreeCharged D T parts) 0 := by
  have h := SetupBudgets.honestP_adversary (fun u : (LocalSpec C).Domain => ∃ q, u = .inr (.inl q)) oa
  rw [← fst_observe] at h
  exact FirstCounts.isQueryBoundP_add (freeCharged_cases D T parts) _ 0 0 ((isQueryBoundP_map_iff _ _ _).1 h)
    ((noCall_iff _ _).1 (noProgram_observe oa))

end Cells

/-! ## The glue -/

section Glue

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The reference suffix of a term `T` with no corrupt holder makes at most `(n + 1) k` free calls or
programming calls at the cell of a shift outside `hiddenShifts`, for each result `x` of the prefix.
Each known term gives one programming cell and at most one derive cell at each honest operator. The
derivations of `T` ask `markCell`, and a derivation of another hidden term asks its hidden cell. -/
def PartsWalk : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (x : SeedCompare.PrefixOut C A.net.State), ¬ KnownTo D.1 T →
    IsQueryBoundP (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress x.2.2)
      (termMark D x.2.2 T)) (FreeCharged D T x.2.2) ((C.n + 1) * (knownTerms D).card)

omit [Fintype E] [DecidableEq E] in
theorem suffixAt_eq (D : C.Coalition) (A : DkgTsigAdversary C E) (T : C.Term) (x : SeedCompare.PrefixOut C A.net.State) :
    suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress x.2.2) (termMark D x.2.2 T) =
      suffixOf K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (seedGenAt D A.net x.1.1 x.1.2 x.2.1.1
        x.2.1.2.2 x.2.2 (commitAddress x.2.2) (termMark D x.2.2 T)) := rfl

omit [Fintype E] [DecidableEq E] in
/-- `PartsWalk` gives `PartsCount`. -/
theorem partsCount_of_walk (walk : PartsWalk K circuits settings runLimit) :
    PartsCount prims K circuits settings runLimit := by
  intro D A q bounded T hT r hr
  obtain ⟨start, step, forge, hsum, hstart, hround, hforge⟩ := bounded
  have hstart' : ∀ x z, IsQueryBoundP (A.net.start x z) DkgSecurityProof.HashCall start := fun x z =>
    isQueryBoundP_of_queryCostAtMost (hstart x z) LoggedCount.hashCall_ownCost
  have hround' := round_bound A step hround
  have hforge' : ∀ pk top, cost (forgeCharge (callCharge DkgSecurityProof.HashCall)) (A.forge pk top) ≤ (forge : ℕ∞) :=
    fun pk top => (PFunctor.FreeM.cost_mono LoggedCount.forgeCharge_le_forgeCost _).trans
      ((queryCostAtMost_iff_cost_le _ _ _).1 (hforge pk top))
  simp only [partsRef, prefix_run, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨a, ha, b, -, parts, -, z, hz, rfl⟩ := hr
  have hpre := measure_le (loggedWorld prims D) (fun w => gauge D T parts w.1.1 []) (ShiftCharged D T parts)
    (loggedWorld_gauge D T parts prims) _ start
    ((FirstCounts.isQueryBoundP_add (shiftCharged_cases D T parts) _ start 0
      (DkgSecurityProof.logged_observe _ _ (hstart' _ _)) (noFree_observe D T parts _)).mono (Nat.add_zero _).le) _ a ha
  have hsg : IsQueryBoundP (seedGenAt D A.net a.1.1 a.1.2 b.1 b.2.2 parts (commitAddress parts)
      (termMark D parts T)) DkgSecurityProof.Logged (setupRounds * step) :=
    logged_seedGenShape D A.net step hround' a.1.1 a.1.2 b.1 b.2.2 parts _
      (noLogged_commitDrawsAt D (commitAddress parts)) _ _ _
  have hlog := logged_suffixOf K circuits settings runLimit D A step forge hround' hforge' ((a.1, b, parts)) _ hsg
  rw [← suffixAt_eq] at hlog
  have hsuf := measure_le (partsWorld prims D) (fun s => gauge D T parts s.1.1.1 s.2.2) (ShiftCharged D T parts)
    (partsWorld_gauge D T parts prims) _ _
    (FirstCounts.isQueryBoundP_add (shiftCharged_cases D T parts) _ _ _ hlog (walk D A T (a.1, b, parts) hT)) _ z hz
  have h0 : gauge D T parts (∅ : HashCache C) [] = 0 := by
    simp [gauge, namedSet]
  rw [h0, zero_add] at hpre
  have hH := encard_hiddenShifts D T parts hT
  have hcard : ((partsNamed T parts z.2).card : ℕ∞) ≤ gauge D T parts z.2.1.1.1 z.2.2.2 +
      (hiddenShifts D T parts).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard, coe_partsNamed]
    refine (Set.encard_le_encard fun δ hδ => ?_).trans (Set.encard_union_le _ _)
    by_cases h : δ ∈ hiddenShifts D T parts
    · exact Or.inr h
    · exact Or.inl ⟨hδ, h⟩
  have hb := budget_arith circuits settings runLimit start step forge q hsum
  have key : ((partsNamed T parts z.2).card : ℕ∞) ≤
      ((q + ((hiddenTerms D).card - 1) + (C.n + 1) * (knownTerms D).card : ℕ) : ℕ∞) := by
    refine hcard.trans ((add_le_add (hsuf.trans (add_le_add hpre le_rfl)) hH).trans ?_)
    have hnat : start + (setupRounds * step + ((dkgTsigRounds circuits settings runLimit - setupRounds) * step +
        forge) + (C.n + 1) * (knownTerms D).card) + ((hiddenTerms D).card - 1) ≤
        q + ((hiddenTerms D).card - 1) + (C.n + 1) * (knownTerms D).card := by omega
    exact_mod_cast hnat
  exact_mod_cast key

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsCount_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsCount_of_walk
