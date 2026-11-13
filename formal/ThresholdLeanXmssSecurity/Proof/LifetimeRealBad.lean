import ThresholdLeanXmssSecurity.Proof.LifetimePrfTransportProof
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The real bad event of each chronological hybrid

This module moves the `Q` budget of `lifetimeGame` to hybrid `n`.

* `splitGame` runs the lifetime with two extra copies of the local oracles. The honest operators
  of the runs before run `n` use the first extra copy, and those of the runs after run `n` use the
  second one. Run `n`, the keygen, the signing and the adversary use the world.
* `collapse_splitGame` merges both extra copies into the free copy. This gives `lifetimeGame`.
* `emulation_eq_split` interprets the first extra copy by the emulated honest operators of
  `emulatedRoles` and the second one by the counted copy. This gives the world game of hybrid `n`
  (`reductionGame`), after the stream table and the log are erased.
* `hybridBudget` follows. Each call of hybrid `n` costs at most its charge in `lifetimeGame`, so
  `HasLifetimeQueryBoundAll` bounds every answer path of hybrid `n` by `Q`. This counts the calls of
  every party, the keygen, the signing and the honest operators of every run included.
* `HybridRealBadBound` bounds the stream-key bad event of hybrid `n` by `realShare / 2^256`, for
  each `Th`, when every answer path of hybrid `n` makes at most `Q` calls. `realBadBound_of_hybrid`
  gives `RealBadBound` from it and `hybridBudget`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace ThresholdLeanXmssSecurity.LifetimeRealBad

open LifetimeJointLink LifetimeHybridOrder LifetimeKeygenHopProof LifetimeEmulatedBudget
  LifetimePrfTransportProof

attribute [local instance] Classical.propDecidable

section Split

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The tagged oracles with a fourth copy of the local oracles, used by the honest operators of
the runs after run `n`. -/
abbrev SplitSpec (C : Committee) := TaggedSpec C + LocalSpec C

/-- Move a tagged computation to the first three copies. -/
def toSplit {α : Type} (p : OracleComp (TaggedSpec C) α) : OracleComp (SplitSpec C) α :=
  simulateQ (fun t => (liftM ((SplitSpec C).query (.inl t)) : OracleComp (SplitSpec C) _)) p

/-- The keygen, the signing, the adversary and run `n`, exactly as `worldRoles`. -/
def splitBase : Roles C (OracleComp (SplitSpec C)) where
  adversary p := toSplit (taggedBase.adversary p)
  honest p := toSplit (taggedBase.honest p)

/-- The runs before run `n`, with the honest operators on the third copy. -/
def splitEarly : Roles C (OracleComp (SplitSpec C)) where
  adversary p := splitBase.adversary p
  honest p := toSplit (taggedRun.honest p)

/-- The runs after run `n`, with the honest operators on the fourth copy. -/
def splitLate : Roles C (OracleComp (SplitSpec C)) where
  adversary p := splitBase.adversary p
  honest p := simulateQ (fun t => (liftM ((SplitSpec C).query (.inr t)) : OracleComp (SplitSpec C) _)) p

/-- The roles of each run in the split lifetime of hybrid `n`. -/
def splitRoles (n : ℕ) : ℕ → Roles C (OracleComp (SplitSpec C)) := fun r =>
  if r < n then splitEarly else if r = n then splitBase else splitLate

/-- The split lifetime of hybrid `n`. -/
def splitGame (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
    (D : C.Coalition) (A : LifetimeAdversary C E) (n : ℕ) : OracleComp (SplitSpec C) Bool :=
  lifetimeGameWith K circuits settings attempts (splitRoles n) splitBase D A

/-- Merge the third and the fourth copy into the free copy. -/
def collapseSplit : QueryImpl (SplitSpec C) (OracleComp (WorldSpec C))
  | .inl t => collapseImpl t
  | .inr t => (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _)

/-- The split charge is the real lifetime charge after merging the copies. -/
def SplitCounted : (SplitSpec C).Domain → Prop
  | .inl t => TaggedCounted t
  | .inr t => LifetimeCounted (C := C) (.inr t)

theorem collapse_toSplit {α : Type} (p : OracleComp (TaggedSpec C) α) :
    simulateQ collapseSplit (toSplit p) = simulateQ collapseImpl p := by
  rw [toSplit, simulateQ_comp]
  exact congrArg (fun f : QueryImpl (TaggedSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query collapseSplit (Sum.inl t))

theorem collapse_runHonest {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ collapseImpl (taggedRun.honest p) = free p := by
  change simulateQ collapseImpl (simulateQ _ p) = free p
  rw [simulateQ_comp]
  exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query collapseImpl (Sum.inr t))

theorem collapse_splitBase : RolesHom (simulateQ' (collapseSplit (C := C))) splitBase worldRoles :=
  ⟨fun _ => (collapse_toSplit _).trans (collapse_toTagged _),
    fun _ => (collapse_toSplit _).trans (collapse_toTagged _)⟩

theorem collapse_splitRoles (n r : ℕ) :
    RolesHom (simulateQ' (collapseSplit (C := C))) (splitRoles n r) worldRoles := by
  unfold splitRoles
  split_ifs
  · exact ⟨collapse_splitBase.adversary, fun p => (collapse_toSplit _).trans (collapse_runHonest p)⟩
  · exact collapse_splitBase
  · refine ⟨collapse_splitBase.adversary, fun p => ?_⟩
    change simulateQ collapseSplit (simulateQ _ p) = free p
    rw [simulateQ_comp]
    exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
      (funext fun t => simulateQ_spec_query collapseSplit (Sum.inr t))

/-- Merging the copies gives the real lifetime. -/
theorem collapse_splitGame (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (attempts : ℕ) (D : C.Coalition) (A : LifetimeAdversary C E) (n : ℕ) :
    simulateQ collapseSplit (splitGame K circuits settings attempts D A n) =
      lifetimeGame K circuits settings attempts D A :=
  hom_lifetimeGameWith (simulateQ' collapseSplit) K circuits settings attempts
    (splitRoles n) splitBase (fun _ => worldRoles) worldRoles (collapse_splitRoles n)
    collapse_splitBase D A

/-- Merging the copies charges each split query its real lifetime charge. -/
theorem split_bound_of_collapse {α : Type} (p : OracleComp (SplitSpec C) α) (Q : ℕ)
    (h : IsQueryBoundP (simulateQ collapseSplit p) LifetimeCounted Q) :
    IsQueryBoundP p SplitCounted Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at h
    rw [isQueryBoundP_query_bind_iff]
    rcases t with (t | t) | t
    · change IsQueryBoundP ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · change IsQueryBoundP ((liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · change IsQueryBoundP ((liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- The first three copies run as in the emulation of `emuImpl`. The fourth copy runs the later
honest operators on the counted copy. -/
def splitImpl (D : C.Coalition) : QueryImpl (SplitSpec C) (ErasedM C)
  | .inl t => emuImpl D t
  | .inr t => StateT.lift (worldRoles.adversary (liftM ((LocalSpec C).query t)))

/-- The roles of each run of hybrid `n` after the log is erased. -/
def erasedRoles (D : C.Coalition) (n : ℕ) : ℕ → Roles C (ErasedM C) := fun r =>
  if r < n then treeSimErasedRoles D
  else if r = n then plainRoles
  else ⟨plainRoles.adversary, plainRoles.adversary⟩

theorem worldAdversary_eq_simulateQ {α : Type} (p : OracleComp (LocalSpec C) α) :
    worldRoles.adversary p =
      simulateQ (fun t => worldRoles.adversary (liftM ((LocalSpec C).query t))) p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [worldRoles, counted]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, ← funext ih]
    simp only [worldRoles, counted, liftComp_bind]
    exact simulateQ_bind _ _ _

theorem adversary_query (t : (LocalSpec C).Domain) :
    worldRoles.adversary (liftM ((LocalSpec C).query t)) =
      (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
  simp [worldRoles, counted]
  erw [simulateQ_query]
  rcases t with u | q | x <;> rfl

theorem split_toSplit (D : C.Coalition) {α : Type} (p : OracleComp (TaggedSpec C) α) :
    simulateQ (splitImpl D) (toSplit p) = simulateQ (emuImpl D) p := by
  rw [toSplit, simulateQ_comp]
  exact congrArg (fun f : QueryImpl (TaggedSpec C) (ErasedM C) => simulateQ f p)
    (funext fun t => simulateQ_spec_query (splitImpl D) (Sum.inl t))

theorem split_splitBase (D : C.Coalition) :
    RolesHom (simulateQ' (splitImpl D)) splitBase (plainRoles (C := C)) :=
  ⟨fun _ => (split_toSplit D _).trans (emu_toTagged D _),
    fun _ => (split_toSplit D _).trans (emu_toTagged D _)⟩

theorem split_splitRoles (D : C.Coalition) (n r : ℕ) :
    RolesHom (simulateQ' (splitImpl D)) (splitRoles n r) (erasedRoles D n r) := by
  unfold splitRoles erasedRoles
  split_ifs
  · refine ⟨fun p => ((split_splitBase D).adversary p).trans (treeSimErase_adversary D p).symm,
      fun p => (split_toSplit D _).trans (emu_runHonest D p)⟩
  · exact split_splitBase D
  · refine ⟨(split_splitBase D).adversary, fun p => ?_⟩
    change simulateQ (splitImpl D) (simulateQ _ p) = StateT.lift (worldRoles.adversary p)
    rw [simulateQ_comp, worldAdversary_eq_simulateQ p]
    exact (congrArg (fun f : QueryImpl (LocalSpec C) (ErasedM C) => simulateQ f p)
      (funext fun t => simulateQ_spec_query (splitImpl D) (Sum.inr t))).trans
      (hom_simulateQ (liftHom (C := C)) _ p).symm

theorem hybridRoles_self (D : C.Coalition) (n : ℕ) :
    lifetimeHybridRoles D n n = lifetimeHybridRoles D 0 0 := by
  simp [lifetimeHybridRoles]

theorem erase_hybridRoles (D : C.Coalition) (n r : ℕ) :
    RolesHom (eraseHom (C := C)) (lifetimeHybridRoles D n r) (erasedRoles D n r) := by
  by_cases hlt : r < n
  · simp only [lifetimeHybridRoles, erasedRoles, hlt, if_true]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  by_cases heq : r = n
  · subst heq
    simp only [erasedRoles, hlt, if_false, if_true]
    rw [hybridRoles_self]
    exact ⟨fun p => erase_base_adversary D p, fun p => erase_base_honest D p⟩
  · simp only [lifetimeHybridRoles, erasedRoles, hlt, heq, if_false]
    exact ⟨fun p => treeSimErase_adversary D p, fun p => treeSimErase_adversary D p⟩

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)

/-- The split lifetime under the emulated interpretation is the world game of hybrid `n`. -/
theorem emulation_eq_split (D : C.Coalition) (A : LifetimeAdversary C E) (n : ℕ) :
    emulationGame (lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n)
        (lifetimeHybridRoles D n n) D A) =
      (simulateQ (splitImpl D) (splitGame K circuits settings attempts D A n)).run' ∅ := by
  have herase : treeSimErase (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A) =
      lifetimeGameWith K circuits settings attempts (erasedRoles D n) plainRoles D A := by
    have h := erase_hybridRoles D n n
    simp only [erasedRoles, Nat.lt_irrefl, if_false, if_true] at h
    exact hom_lifetimeGameWith (eraseHom (C := C)) K circuits settings attempts _ _ _ _
      (erase_hybridRoles D n) h D A
  have hsplit : simulateQ (splitImpl D) (splitGame K circuits settings attempts D A n) =
      lifetimeGameWith K circuits settings attempts (erasedRoles D n) plainRoles D A :=
    hom_lifetimeGameWith (simulateQ' (splitImpl D)) K circuits settings attempts _ _ _ _
      (split_splitRoles D n) (split_splitBase D) D A
  rw [emulationGame_erased, herase, hsplit]

/-- Each split step costs at most the real charge of its split query. -/
theorem split_step (D : C.Coalition) (t : (SplitSpec C).Domain) (s : StreamCache C) :
    IsQueryBoundP ((splitImpl D t).run s) LifetimeCounted (if SplitCounted t then 1 else 0) := by
  rcases t with t | t
  · exact emu_step D t s
  · have hcount : LifetimeCounted (C := C) (.inl (.inl t)) = LifetimeCounted (.inr t) := by
      rcases t with u | q | x <;> rfl
    change IsQueryBoundP ((StateT.lift (worldRoles.adversary
      (liftM ((LocalSpec C).query t))) : ErasedM C _).run s) LifetimeCounted
      (if LifetimeCounted (C := C) (.inr t) then 1 else 0)
    rw [← hcount, adversary_query, StateT.run_lift, isQueryBoundP_query_bind_iff]
    refine ⟨?_, fun _ => trivial⟩
    by_cases ht : LifetimeCounted (C := C) (.inl (.inl t))
    · exact Or.inr (by simp [ht])
    · exact Or.inl ht

/-- The all-answer budget of hybrid `n`, from the all-answer budget of the real lifetime at the
same circuits. -/
theorem hybridBudget_of_real (D : C.Coalition) (A : LifetimeAdversary C E) (Q n : ℕ)
    (hQ : IsQueryBoundP (lifetimeGame K circuits settings attempts D A) LifetimeCounted Q) :
    IsQueryBoundP
      (emulationGame (lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n)
        (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q := by
  rw [emulation_eq_split, StateT.run'_eq, isQueryBoundP_map_iff]
  rw [← collapse_splitGame K circuits settings attempts D A n] at hQ
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (split_bound_of_collapse _ Q hQ)
    (split_step D) ∅

end Split

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- `HasLifetimeQueryBoundAll` bounds every answer path of hybrid `n` by `Q`, for each `Th`. -/
theorem hybridBudget (Q : ℕ) (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (n : ℕ) (values : MpcDomain → HashOutput) :
    IsQueryBoundP (reductionGame K settings attempts circuitsOf D A values n) LifetimeCounted Q :=
  hybridBudget_of_real K (circuitsOf (thOf values)) settings attempts D A Q n (hQ values)

/-- The stream-key bad event of hybrid `n`, for each `Th`, fits the real share when every answer
path of hybrid `n` makes at most `Q` calls. -/
def HybridRealBadBound (Q : ℕ) : Prop :=
  let F := ceremonyFuel (circuitsOf fun _ => 0) settings
  keySplit C (Q + lifetimeOverhead C attempts Q + (F + 2) * Q) < 2 →
  ∀ (n : Fin (lifetimeRuns attempts)) (values : MpcDomain → HashOutput),
    IsQueryBoundP (reductionGame K settings attempts circuitsOf D A values n) LifetimeCounted Q →
    probBad_streamKey ⟨thOf values, aes⟩ D (reductionGame K settings attempts circuitsOf D A values n) ≤
      (realShare C attempts Q F : ℝ) / 2 ^ 256

/-- `RealBadBound` from the bound at the budget of hybrid `n`. -/
theorem realBadBound_of_hybrid (Q : ℕ)
    (h : HybridRealBadBound K settings attempts aes circuitsOf D A Q) :
    RealBadBound K settings attempts aes circuitsOf D A Q :=
  fun hQ hsplit n values =>
    h hsplit n values (hybridBudget K settings attempts circuitsOf D A Q hQ n values)

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBad.collapse_splitGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collapse_splitGame

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBad.emulation_eq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emulation_eq_split

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBad.hybridBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hybridBudget

/-- info: 'ThresholdLeanXmssSecurity.LifetimeRealBad.realBadBound_of_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realBadBound_of_hybrid

end ThresholdLeanXmssSecurity.LifetimeRealBad
