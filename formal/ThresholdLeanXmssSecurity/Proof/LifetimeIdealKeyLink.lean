import ThresholdLeanXmssSecurity.Proof.LifetimeIdealBad
import ThresholdLeanXmssSecurity.Proof.LifetimeRealBad
import ThresholdLeanXmssSecurity.Proof.TreeKey

/-!
# The run-`n` key link in the left world

This module follows the left world `(simulateQ (leftImpl …) (program4 … n)).run idealStart` of hop
`n` at each lifetime oracle boundary.

* `KeyLinkInv` is the invariant at a boundary. `partsOf r` are the parts that the operators of run
  `r` sample. `hiddenInput parts name` is the `.derive` input of a hidden name from these parts.
* `TablesOk` is its table part. Each first-table key of a name is the cached answer to the input of
  the parts of a started run before run `n`. Each second-table key of a name is the cached answer
  to the input of the parts of run `n`.
* `RunPhase` is its run part. A running run `r ≤ n` is before its commit round, before its reveal
  round, or after its reveal round with rows whose hidden keys are these cached answers.
* `step_inv`: each lifetime oracle step keeps the invariant. After run `n` starts, no step adds a
  first-table address. The new parts history satisfies `NewParts`. An admitted start of run
  `r = runCount ≤ n` sets `partsOf r` to the parts that `prssInitialData` (`sampleParts`) samples on
  the copy of run `r`, and every other step keeps the history. So the parts of a started run never
  change (`newParts_agree`). `loop_inv` carries the invariant and this agreement through the
  adversary program.
* `start_eq`: an admitted start of run `r` is that sampling followed by the new steps. The copy of
  run `n` is `targetQ` (`runQ_self`).
* `keyOverlap_of_inv`: at a boundary, a hidden key in both tables is the cached answer to the
  run-`n` input of its name and to the input of the same name from the parts of a started run
  `r' < n`.
* `program4_keyLink`: each supported outcome of the left world satisfies `TablesOk` for some
  history. `second_key`, `second_key_unique` and `first_keys_ncard` follow from it.

These statements are support facts. They do not give the law of the parts or of the answers.

The proof uses these facts.

1. The commit and reveal rounds of a run are `stepRound_prssCommit_bind` and
   `stepRound_prssReveal_bind` of `Tree.lean` on the copy of the run (`toWorld`).
2. An honest operator receives the reveal of each honest operator unchanged
   (`prssRevealInbox_honest`). So all honest holders of a hidden name use one `.derive` input
   (`prssReveal_term_input`, `prssReveal_pair_input`), and each reveal row holds its cached answer
   (`reveal_rowKey`).
3. After the reveal round, an operator makes streams only under the keys of its row
   (`POk.ceremonyAfterSetup`, `stepRound_ok`).
4. A start needs `running = none`, and a round uses the copy of run `runCount - 1`. The runs after
   run `n` use the adversary copy (`later_bad`), and the free copy makes no stream
   (`keygen_phase_quiet`, `tsig_quiet`).
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace ThresholdLeanXmssSecurity.LifetimeIdealKeyLink

open LifetimePrfTransportProof LifetimeIdealBad LifetimeEmulatedBudget

attribute [local instance] Classical.propDecidable

section Tables

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- `y` is the table address of the hidden stream query `t`. -/
def HiddenAt (t : (LocalSpec C).Domain) (y : Address C) : Prop :=
  ∃ x, t = .inr (.inr x) ∧ Hidden D x.1 ∧ y = address x

/-- From `s` to `r` the hash cache grows and the flag stays. A new address of the first table
satisfies `F`, and a new address of the second table satisfies `S`. -/
def Within (F S : Address C → Prop) (s r : IdealState C) : Prop :=
  s.1 ≤ r.1 ∧ r.2.2.2 = s.2.2.2 ∧ (∀ y, (r.2.1 y).isSome → (s.2.1 y).isSome ∨ F y) ∧
    (∀ y, (r.2.2.1 y).isSome → (s.2.2.1 y).isSome ∨ S y)

theorem within_refl (F S : Address C → Prop) (s : IdealState C) : Within F S s s :=
  ⟨le_rfl, rfl, fun _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem within_trans {F S : Address C → Prop} {s t u : IdealState C} (h₁ : Within F S s t)
    (h₂ : Within F S t u) : Within F S s u :=
  ⟨le_trans h₁.1 h₂.1, h₂.2.1.trans h₁.2.1,
    fun y hy => (h₂.2.2.1 y hy).elim (fun h => h₁.2.2.1 y h) Or.inr,
    fun y hy => (h₂.2.2.2 y hy).elim (fun h => h₁.2.2.2 y h) Or.inr⟩

theorem within_mono {F S F' S' : Address C → Prop} (hF : ∀ y, F y → F' y) (hS : ∀ y, S y → S' y)
    {s r : IdealState C} (h : Within F S s r) : Within F' S' s r :=
  ⟨h.1, h.2.1, fun y hy => (h.2.2.1 y hy).imp_right (hF y),
    fun y hy => (h.2.2.2 y hy).imp_right (hS y)⟩

theorem onCache_within (t : (LocalSpec C).Domain) (F S : Address C → Prop) (s : IdealState C)
    (r : _ × IdealState C) (hr : r ∈ support ((onCache (localAnswer prims t)).run s)) :
    Within F S s r.2 := by
  simp only [onCache, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  exact ⟨(localAnswer_support (fun _ => 0) t s.1 p hp).1, rfl, fun _ h => Or.inl h,
    fun _ h => Or.inl h⟩

theorem tableDraw_new {c : HiddenCache C} {x : Address C} {r : Bit × HiddenCache C}
    (hr : r ∈ support (tableDraw c x)) : ∀ y, (r.2 y).isSome → (c y).isSome ∨ y = x := by
  unfold tableDraw at hr
  cases hc : c x <;> simp only [hc, support_pure, Set.mem_singleton_iff, support_map,
    Set.mem_image] at hr
  · obtain ⟨b, -, rfl⟩ := hr
    intro y hy
    by_cases hyx : y = x
    · exact Or.inr hyx
    · change ((c.cacheQuery x b) y).isSome = true at hy
      rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
      exact Or.inl hy
  · subst hr
    exact fun _ hy => Or.inl hy

theorem firstTable_within (x : Address C) (s : IdealState C) (r : Bit × IdealState C)
    (hr : r ∈ support ((firstTable x).run s)) : Within (· = x) (fun _ => False) s r.2 := by
  simp only [firstTable, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨le_rfl, rfl, tableDraw_new hr', fun _ h => Or.inl h⟩

theorem secondTable_within (x : Address C) (s : IdealState C) (r : Bit × IdealState C)
    (hr : r ∈ support ((secondTable x).run s)) : Within (fun _ => False) (· = x) s r.2 := by
  simp only [secondTable, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨le_rfl, rfl, fun _ h => Or.inl h, tableDraw_new hr'⟩

/-- The queries of the four-copy program that can break `Within F S`: a stream of the free copy,
and a hidden stream of a run copy at an address outside `F` or `S`. -/
def Bad4 (F S : Address C → Prop) : (Spec4 C).Domain → Prop
  | .inl (.inl (.inl _)) => False
  | .inl (.inl (.inr t)) => ∃ y, HiddenAt D t y ∧ ¬ F y
  | .inl (.inr t) => PrgCall t
  | .inr t => ∃ y, HiddenAt D t y ∧ ¬ S y

theorem withHidden_within (hidden : PrgInput C → StateT (IdealState C) ProbComp Bit)
    (F S : Address C → Prop) (t : (LocalSpec C).Domain)
    (h : ∀ x, Hidden D x.1 → t = .inr (.inr x) → ∀ s, ∀ r ∈ support ((hidden x).run s), Within F S s r.2)
    (s : IdealState C) (r : _ × IdealState C) (hr : r ∈ support ((withHidden prims D hidden t).run s)) :
    Within F S s r.2 := by
  rcases t with u | q | x
  · exact onCache_within prims _ F S s r hr
  · exact onCache_within prims _ F S s r hr
  · change r ∈ support ((if Hidden D x.1 then hidden x else
      onCache (localAnswer prims (.inr (.inr x)))).run s) at hr
    split_ifs at hr with hx
    · exact h x hx rfl s r hr
    · exact onCache_within prims _ F S s r hr

theorem leftImpl_within (F S : Address C → Prop) (t : (Spec4 C).Domain) (ht : ¬ Bad4 D F S t)
    (s : IdealState C) (r : _ × IdealState C) (hr : r ∈ support ((leftImpl prims D t).run s)) :
    Within F S s r.2 := by
  rcases t with ((t | t) | t) | t
  · exact onCache_within prims _ F S s r hr
  · refine withHidden_within prims D _ F S t (fun x hx he s r hr => ?_) s r hr
    have hy : F (address x) := by
      by_contra hn
      exact ht ⟨address x, ⟨x, he, hx, rfl⟩, hn⟩
    exact within_mono (fun y hy' => hy' ▸ hy) (fun _ h => h.elim) (firstTable_within _ s r hr)
  · refine withHidden_within prims D _ F S t (fun x hx he s r hr => ?_) s r hr
    subst he
    exact (ht trivial).elim
  · refine withHidden_within prims D _ F S t (fun x hx he s r hr => ?_) s r hr
    have hy : S (address x) := by
      by_contra hn
      exact ht ⟨address x, ⟨x, he, hx, rfl⟩, hn⟩
    exact within_mono (fun _ h => h.elim) (fun y hy' => hy' ▸ hy) (secondTable_within _ s r hr)

/-- A four-copy program with no query of `Bad4 F S` keeps `Within F S` on every run. -/
theorem simulate_within (F S : Address C → Prop) {α : Type} (p : OracleComp (Spec4 C) α)
    (hp : IsQueryBoundP p (Bad4 D F S) 0) (s : IdealState C) (r : α × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D) p).run s)) : Within F S s r.2 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    rw [he]
    exact within_refl F S s
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ Bad4 D F S t := hp.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact within_trans (leftImpl_within prims D F S t ht s u hu)
      (ih u.1 (by simpa [ht] using hp.2 u.1) u.2 hr)

end Tables

section Copies

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

theorem qb0_or {ι : Type} {spec : OracleSpec ι} {α : Type} (P Q : ι → Prop) (oa : OracleComp spec α)
    (hP : IsQueryBoundP oa P 0) (hQ : IsQueryBoundP oa Q 0) :
    IsQueryBoundP oa (fun t => P t ∨ Q t) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP hQ ⊢
    have hp : ¬ P t := hP.1.resolve_right (by omega)
    have hq : ¬ Q t := hQ.1.resolve_right (by omega)
    refine ⟨Or.inl fun h => h.elim hp hq, fun u => ?_⟩
    have h := ih u (by simpa [hp] using hP.2 u) (by simpa [hq] using hQ.2 u)
    simpa [hp, hq] using h

/-- A query of a run copy. -/
def RunCall : (Spec4 C).Domain → Prop
  | .inl (.inl (.inl _)) => False
  | .inl (.inr _) => False
  | _ => True

theorem bad4_quiet (F S : Address C → Prop) {α : Type} (p : OracleComp (Spec4 C) α)
    (h₁ : IsQueryBoundP p FreePrgCall 0) (h₂ : IsQueryBoundP p RunCall 0) :
    IsQueryBoundP p (Bad4 D F S) 0 := by
  refine IsQueryBoundP.of_imp (fun t ht => ?_) (qb0_or _ _ p h₁ h₂)
  rcases t with ((t | t) | t) | t
  · exact ht.elim
  · exact Or.inr trivial
  · exact Or.inl ht
  · exact Or.inr trivial

def advQ : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)) := fun t =>
  OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inl (.inl t))))

def emulQ : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)) := fun t =>
  OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inl (.inr t))))

def freeQ : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)) := fun t =>
  OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inr t)))

def targetQ : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)) := fun t =>
  OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inr t))

/-- The copy of the honest operators of run `r` in `program4`. -/
def runQ (n r : ℕ) : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)) :=
  if r < n then emulQ else if r = n then targetQ else advQ

theorem roles4_eq (n r : ℕ) :
    roles4 (C := C) n r = ⟨advCopy4, fun p => simulateQ (runQ n r) p⟩ := by
  unfold roles4 runQ
  split_ifs <;> rfl

/-- The first-table addresses of run `r` that `A` allows. -/
def FirstSet (n r : ℕ) (A : Address C → Prop) (y : Address C) : Prop := r < n ∧ A y

/-- The second-table addresses of run `r` that `A` allows. -/
def SecondSet (n r : ℕ) (A : Address C → Prop) (y : Address C) : Prop := r = n ∧ A y

theorem runQ_bad (n r : ℕ) (A : Address C → Prop) (t : (LocalSpec C).Domain)
    (ht : ∀ y, HiddenAt D t y → A y) :
    IsQueryBoundP (runQ n r t) (Bad4 D (FirstSet n r A) (SecondSet n r A)) 0 := by
  unfold runQ
  split_ifs with h₁ h₂
  · refine (isQueryBoundP_query_iff _ _ _).2 fun hb => ?_
    obtain ⟨y, hy, hn⟩ := hb
    exact (hn ⟨h₁, ht y hy⟩).elim
  · refine (isQueryBoundP_query_iff _ _ _).2 fun hb => ?_
    obtain ⟨y, hy, hn⟩ := hb
    exact (hn ⟨h₂, ht y hy⟩).elim
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim

theorem adv_bad (F S : Address C → Prop) {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (advCopy4 p) (Bad4 D F S) 0 :=
  qb0_simulateQ (p := fun _ => False) (fun t => OracleComp.lift
    (OracleSpec.query (spec := Spec4 C) (.inl (.inl (.inl t)))))
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim) p (qb0_false p)

theorem free_bad (F S : Address C → Prop) {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p PrgCall 0) : IsQueryBoundP (freeCopy4 p) (Bad4 D F S) 0 :=
  qb0_simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inr t))))
    (fun _ ht => (isQueryBoundP_query_iff _ _ _).2 fun hb => (ht hb).elim) p hp

/-- A local program with no query of `PRG`. -/
theorem runQ_noStream (n r : ℕ) {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p LocalStream 0) :
    IsQueryBoundP (simulateQ (runQ n r) p) (Bad4 D (fun _ => False) (fun _ => False)) 0 := by
  refine IsQueryBoundP.of_imp (fun t ht => ?_) (qb0_simulateQ _ (fun t ht =>
    runQ_bad D n r (fun _ => False) t fun y hy => ht ?_) p hp)
  · rcases t with ((t | t) | t) | t
    · exact ht.elim
    · obtain ⟨y, hy, -⟩ := ht
      exact ⟨y, hy, fun h => h.2⟩
    · exact ht
    · obtain ⟨y, hy, -⟩ := ht
      exact ⟨y, hy, fun h => h.2⟩
  · obtain ⟨x, rfl, -⟩ := hy
    trivial

/-- `worldRoles` on the four copies: the counted copy on the adversary copy, and the free copy on
`emb`. -/
def worldTo (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C))) :
    QueryImpl (WorldSpec C) (OracleComp (Spec4 C))
  | .inl (.inl t) => advQ t
  | .inl (.inr _) => (pure false : OracleComp (Spec4 C) Bool)
  | .inr t => emb t

def toWorld (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C))) :
    OracleComp (WorldSpec C) →ᵐ OracleComp (Spec4 C) where
  toFun _ p := simulateQ (worldTo emb) p
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

theorem toWorld_free (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C))) {α : Type}
    (p : OracleComp (LocalSpec C) α) : toWorld emb (free p) = simulateQ emb p := by
  change simulateQ (worldTo emb) (simulateQ _ p) = _
  rw [LifetimeEmulatedBudget.simulateQ_comp]
  congr 1
  funext t
  exact simulateQ_spec_query _ _

theorem toWorld_counted (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C))) {α : Type}
    (p : OracleComp (LocalSpec C) α) : toWorld emb (worldRoles.adversary p) = advCopy4 p := by
  change simulateQ (worldTo emb) (worldRoles.adversary p) = _
  rw [LifetimeRealBad.worldAdversary_eq_simulateQ, LifetimeEmulatedBudget.simulateQ_comp]
  unfold advCopy4
  congr 1
  funext t
  rw [LifetimeRealBad.adversary_query]
  exact simulateQ_spec_query _ _

theorem rolesHom_roles4 (n r : ℕ) : RolesHom (toWorld (runQ n r)) worldRoles (roles4 (C := C) n r) := by
  rw [roles4_eq]
  exact ⟨fun p => toWorld_counted _ p, fun p => toWorld_free _ p⟩

theorem rolesHom_base4 : RolesHom (toWorld freeQ) worldRoles (base4 (C := C)) :=
  ⟨fun p => toWorld_counted _ p, fun p => toWorld_free _ p⟩

/-- A world program in the image of `toWorld` keeps `Bad4` quiet when `emb` does so on the free
queries that `P` allows. -/
theorem toWorld_bad (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C))) (F S : Address C → Prop)
    (P : (WorldSpec C).Domain → Prop) (hP : ∀ t, ¬ P (.inr t) → IsQueryBoundP (emb t) (Bad4 D F S) 0)
    {α : Type} (p : OracleComp (WorldSpec C) α) (hp : IsQueryBoundP p P 0) :
    IsQueryBoundP (toWorld emb p) (Bad4 D F S) 0 := by
  refine qb0_simulateQ _ (fun t ht => ?_) p hp
  rcases t with (t | t) | t
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim
  · exact isQueryBoundP_pure _ _ _
  · exact hP t ht

/-- A local step of any copy on a query with no `PRG` call is a step on the hash cache. -/
theorem leftImpl_local (t : (LocalSpec C).Domain) (ht : ¬ LocalStream t)
    (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)))
    (hemb : emb = advQ ∨ emb = emulQ ∨ emb = freeQ ∨ emb = targetQ) :
    simulateQ (leftImpl prims D) (emb t) = onCache (localAnswer prims t) := by
  rcases t with u | q | x
  · rcases hemb with rfl | rfl | rfl | rfl <;> exact simulateQ_spec_query _ _
  · rcases hemb with rfl | rfl | rfl | rfl <;> exact simulateQ_spec_query _ _
  · exact (ht trivial).elim

/-- A copy of a local program with no `PRG` call runs the program on the hash cache. -/
theorem copy_local (emb : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)))
    (hemb : emb = advQ ∨ emb = emulQ ∨ emb = freeQ ∨ emb = targetQ) {α : Type}
    (p : OracleComp (LocalSpec C) α) (hp : IsQueryBoundP p LocalStream 0) (s : IdealState C)
    (r : α × IdealState C) (hr : r ∈ support ((simulateQ (leftImpl prims D) (simulateQ emb p)).run s)) :
    (r.1, r.2.1) ∈ support ((simulateQ (localAnswer prims) p).run s.1) ∧ r.2.2 = s.2 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    subst he
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ LocalStream t := hp.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    rw [leftImpl_local prims D t ht emb hemb] at hu
    simp only [onCache, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    obtain ⟨h₁, h₂⟩ := ih v.1 (by simpa [ht] using hp.2 v.1) (v.2, s.2) hr
    refine ⟨?_, h₂⟩
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    exact ⟨v, hv, h₁⟩

theorem runQ_cases (n r : ℕ) :
    runQ (C := C) n r = advQ ∨ runQ (C := C) n r = emulQ ∨ runQ (C := C) n r = freeQ ∨
      runQ (C := C) n r = targetQ := by
  unfold runQ
  split_ifs <;> simp

end Copies

section Rounds

variable {C : Committee} {E β : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (D : C.Coalition) (n r : ℕ)

/-- The hidden addresses whose key is the key of their name in a row. -/
def AllowedAt (rows : RevealRows C) (y : Address C) : Prop :=
  ∃ x : PrgInput C, Hidden D x.1 ∧ RowKey rows x.1 x.2.1 ∧ y = address x

/-- The start of run `r`, through its first setup data. -/
theorem startSteps_run (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    startSteps (roles4 n r) D (fun i => prssSetup i >>= k i) =
      (fun data i => suspendStep (k i) (prssInitialSteps D data i)) <$>
        simulateQ (runQ n r) (prssInitialData D) := by
  rw [← hom_startSteps (toWorld (runQ n r)) worldRoles _ (rolesHom_roles4 n r),
    startSteps_prssSetup_bind, MonadHom.mmap_map, toWorld_free]

theorem stepRound_keys {α : Type} (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec α) :
    stepRound (roles4 n r) D (roundAdversary (I := PEmpty) sent) noFunctionality () steps =
      toWorld (runQ n r) (stepRound worldRoles D (roundAdversary (I := Keys C) sent)
        noFunctionality () steps) := by
  rw [hom_stepRound (toWorld (runQ n r)) worldRoles _ (rolesHom_roles4 n r)]
  rfl

/-- The commit round of run `r` makes no oracle call. -/
theorem stepRound_commit (sent : C.Party → C.Party → Option (Msg E))
    (data : C.Party → Parts C × List HashOutput) (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound (roles4 n r) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      (fun i => suspendStep (k i) (prssInitialSteps D data i)) =
      pure ((), (fun i => suspendStep (k i) (prssRevealStep D
        (fun i => (C.parties.any fun j => Msg.isAbort (prssCommitInbox D data sent i j)) = false)
        (fun i => (data i).1) (prssCommitInbox D data sent) i)), sent) := by
  rw [stepRound_keys, stepRound_prssCommit_bind]
  simp [roundAdversary, worldRoles, counted]

/-- The reveal round of run `r` computes the reveal rows. -/
theorem stepRound_reveal (sent : C.Party → C.Party → Option (Msg E))
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound (roles4 n r) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      (fun i => suspendStep (k i) (prssRevealStep D active parts committed i)) = (do
      let rows ← simulateQ (runQ n r) (prssRevealRows D active parts committed sent)
      pure ((), (fun i => suspendStep (k i) (prssFinishStep i (rows i))), sent)) := by
  rw [stepRound_keys, stepRound_prssReveal_bind]
  simp [roundAdversary, worldRoles, counted, toWorld_free]

/-- A round of run `r` after the reveal round. The new hidden streams of run `r` use the keys of
the rows. -/
theorem stepRound_rows (rows : RevealRows C) (sent : C.Party → C.Party → Option (Msg E)) {α : Type}
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ j, StepOk rows (steps j)) :
    IsQueryBoundP (stepRound (roles4 n r) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      steps) (Bad4 D (FirstSet n r (AllowedAt D rows)) (SecondSet n r (AllowedAt D rows))) 0 ∧
      ∀ res ∈ support (stepRound (roles4 n r) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
        steps), ∀ j, StepOk rows (res.2.1 j) := by
  rw [stepRound_keys]
  have h := stepRound_ok rows D (roundAdversary (I := Keys C) sent) () steps hs
  refine ⟨toWorld_bad D _ _ _ (Unallowed rows) (fun t ht => runQ_bad D n r _ t ?_) _ h.1,
    fun res hres => h.2 res (support_simulateQ_subset _ _ hres)⟩
  rintro y ⟨x, rfl, hx, rfl⟩
  exact ⟨x, hx, not_not.mp ht, rfl⟩

/-- A world program on a later run copy makes no query of `Bad4`. -/
theorem later_bad (hr : n < r) (F S : Address C → Prop) {α : Type} (p : OracleComp (WorldSpec C) α) :
    IsQueryBoundP (toWorld (runQ n r) p) (Bad4 D F S) 0 := by
  have he : runQ (C := C) n r = advQ := by
    unfold runQ
    rw [if_neg (by omega), if_neg (by omega)]
  refine toWorld_bad D _ F S (fun _ => False) (fun t _ => ?_) p (by convert qb0_false p)
  rw [he]
  exact (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim

end Rounds

section Invariant

variable {C : Committee} {E : Type} (prims : Primitives) (D : C.Coalition)

/-- The `.derive` input of a hidden name in a PRSS setup where operator `j` samples `parts j`. -/
def hiddenInput (parts : C.Party → Parts C) : KeyName C → Query C
  | .term T => termInput .prss parts T
  | .pair p => pairInput .prss parts p
  | .parameter => .derive .prss .parameter []

/-- The rows of an actual reveal round have, at each hidden name, the cached answer to the input
of that name from the honest parts. -/
theorem reveal_rowKey (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s))
    (name : KeyName C) (key : HashOutput) (hn : Hidden D name) (hk : RowKey r.1 name key) :
    r.2 (hiddenInput parts name) = some key := by
  obtain ⟨i, keys, shared, hrow, hv⟩ := hk
  obtain ⟨-, -, hab, hcache⟩ :=
    (prssRevealRows_cached prims D active parts committed sent s r hr).2 i (keys, shared) hrow
  cases name with
  | parameter => exact hn.elim
  | term T =>
    obtain ⟨hi, rfl⟩ := hv
    have hc := hcache.1.1 T hi
    rw [prssReveal_term_input D active parts sent i hab T hn hi] at hc
    exact hc
  | pair p =>
    obtain ⟨j, hj, rfl, rfl⟩ := hv
    have hc := hcache.1.2 j hj
    have hi := pairOf_left_or_right i j (Ne.symm hj)
    have hq : prssPairQuery i (prssView parts (prssRevealInbox D active parts sent) i) j =
        hiddenInput parts (.pair (C.pairOf i j (Ne.symm hj))) := by
      unfold prssPairQuery
      rw [dif_neg hj]
      exact prssReveal_pair_input D active parts sent i hab _ hn (hi.imp Eq.symm Eq.symm)
    rw [hq] at hc
    exact hc

variable (keys : C.Party → Keys C) (n : ℕ)

/-- The steps of a run whose operators sampled `parts`: before the commit round, before the
reveal round, or after the reveal round with rows whose hidden keys are the cached answers to the
inputs of `parts`. -/
def RunPhase (parts : C.Party → Parts C) (steps : C.Party → Step C E RealSpec TreeOutput)
    (cache : HashCache C) : Prop :=
  (∃ (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
      (data : C.Party → Parts C × List HashOutput),
    (∀ i prss, POk ⟨i, keys i, prss⟩ (k i prss)) ∧ parts = (fun i => (data i).1) ∧
      steps = fun i => suspendStep (k i) (prssInitialSteps D data i)) ∨
  (∃ (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) (active : C.Party → Prop)
      (committed : C.Party → Mail C E),
    (∀ i prss, POk ⟨i, keys i, prss⟩ (k i prss)) ∧
      steps = fun i => suspendStep (k i) (prssRevealStep D active parts committed i)) ∨
  (∃ rows : RevealRows C, (∀ i, StepOk rows (steps i)) ∧
    ∀ name key, Hidden D name → RowKey rows name key → cache (hiddenInput parts name) = some key)

/-- The tables of the left world of hop `n` after `count` started runs. Each first-table address
is a hidden name with a key that answers the input of the parts of a run before run `n`. Each
second-table address is a hidden name with the key that answers the input of the parts of run
`n`. -/
def TablesOk (partsOf : ℕ → C.Party → Parts C) (count : ℕ) (s : IdealState C) : Prop :=
  s.2.2.2 = false ∧
  (∀ y, (s.2.1 y).isSome → Hidden D y.1.1 ∧
    ∃ r < n, r < count ∧ s.1 (hiddenInput (partsOf r) y.1.1) = some y.1.2) ∧
  (∀ y, (s.2.2.1 y).isSome → Hidden D y.1.1 ∧ n < count ∧
    s.1 (hiddenInput (partsOf n) y.1.1) = some y.1.2)

/-- The key-link invariant at a lifetime oracle boundary of the left world of hop `n`. `partsOf r`
are the parts that the operators of run `r` sampled. A running run `r ≤ n` is in a `RunPhase`
for `partsOf r`. -/
def KeyLinkInv (partsOf : ℕ → C.Party → Parts C) (st : LifetimeState C E) (s : IdealState C) :
    Prop :=
  TablesOk D n partsOf st.runCount s ∧
  ∀ tree fuel steps, st.running = some (tree, fuel, steps) → 0 < st.runCount ∧
    (st.runCount - 1 ≤ n → RunPhase D keys (partsOf (st.runCount - 1)) steps s.1)

theorem runPhase_mono {parts : C.Party → Parts C} {steps : C.Party → Step C E RealSpec TreeOutput}
    {c c' : HashCache C} (hc : c ≤ c') (h : RunPhase D keys parts steps c) :
    RunPhase D keys parts steps c' := by
  rcases h with h | h | ⟨rows, hs, hk⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨rows, hs, fun name key hn hr => hc (hk name key hn hr)⟩)

/-- Run-`r` growth keeps the tables, when every allowed address answers the input of run `r`. -/
theorem tablesOk_within {partsOf : ℕ → C.Party → Parts C} {count r : ℕ} {A : Address C → Prop}
    {s s' : IdealState C} (hT : TablesOk D n partsOf count s)
    (hw : Within (FirstSet n r A) (SecondSet n r A) s s')
    (hA : ∀ y, A y → Hidden D y.1.1 ∧ s'.1 (hiddenInput (partsOf r) y.1.1) = some y.1.2)
    (hr : r < count) : TablesOk D n partsOf count s' := by
  refine ⟨hw.2.1.trans hT.1, fun y hy => ?_, fun y hy => ?_⟩
  · rcases hw.2.2.1 y hy with hy | ⟨hrn, hy⟩
    · obtain ⟨hh, r', hr', hc, he⟩ := hT.2.1 y hy
      exact ⟨hh, r', hr', hc, hw.1 he⟩
    · exact ⟨(hA y hy).1, r, hrn, hr, (hA y hy).2⟩
  · rcases hw.2.2.2 y hy with hy | ⟨rfl, hy⟩
    · obtain ⟨hh, hc, he⟩ := hT.2.2 y hy
      exact ⟨hh, hc, hw.1 he⟩
    · exact ⟨(hA y hy).1, hr, (hA y hy).2⟩

theorem tablesOk_quiet {partsOf : ℕ → C.Party → Parts C} {count count' : ℕ} {s s' : IdealState C}
    (hT : TablesOk D n partsOf count s) (hw : Within (fun _ => False) (fun _ => False) s s')
    (hc : count ≤ count') : TablesOk D n partsOf count' s' := by
  refine ⟨hw.2.1.trans hT.1, fun y hy => ?_, fun y hy => ?_⟩
  · rcases hw.2.2.1 y hy with hy | hy
    · obtain ⟨hh, r', hr', hcr, he⟩ := hT.2.1 y hy
      exact ⟨hh, r', hr', by omega, hw.1 he⟩
    · exact hy.elim
  · rcases hw.2.2.2 y hy with hy | hy
    · obtain ⟨hh, hcr, he⟩ := hT.2.2 y hy
      exact ⟨hh, by omega, hw.1 he⟩
    · exact hy.elim

end Invariant

section Step

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition) (K : Constants C E) (circuits : Circuits)
variable (settings : Settings) (attempts n : ℕ) (keys : C.Party → Keys C) (h : C.Party)

/-- The free value oracle of the lifetime in `program4`. -/
def value4 (x : Point) : OracleComp (Spec4 C) Digest :=
  (base4 (C := C)).honest (liftComp (prfValue (honestSeeds D keys) x) _)

/-- The oracles of the adversary in `program4`, as `lifetimeGameWith` builds them. -/
def lifeImpl : QueryImpl (LocalSpec C + LifetimeSpec C E)
    (StateT (LifetimeState C E) (OracleComp (Spec4 C))) :=
  (fun t => StateT.lift ((base4 (C := C)).adversary (OracleComp.lift (OracleSpec.query t)))) +
    lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h

theorem simulate_fst {α : Type} (X : OracleComp (Spec4 C) α) (s : IdealState C)
    (z : α × IdealState C) (hz : z ∈ support ((simulateQ (leftImpl prims D) X).run s)) :
    z.1 ∈ support X := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : z = (a, s) := by simpa using hz
    subst he
    simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨u, -, hz⟩ := hz
    exact (mem_support_bind_iff _ _ _).2 ⟨u.1, by simp, ih u.1 u.2 hz⟩

theorem mem_left_bind {α β : Type} {X : OracleComp (Spec4 C) α} {f : α → OracleComp (Spec4 C) β}
    {s : IdealState C} {res : β × IdealState C}
    (hres : res ∈ support ((simulateQ (leftImpl prims D) (X >>= f)).run s)) :
    ∃ u ∈ support ((simulateQ (leftImpl prims D) X).run s),
      res ∈ support ((simulateQ (leftImpl prims D) (f u.1)).run u.2) := by
  simpa only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] using hres

theorem mem_left_pure {α : Type} {a : α} {s : IdealState C} {res : α × IdealState C}
    (hres : res ∈ support ((simulateQ (leftImpl prims D) (pure a : OracleComp (Spec4 C) α)).run s)) :
    res = (a, s) := by
  simpa using hres

/-- A step with no query of `Bad4` and no change of the runs keeps the invariant and the first
table. -/
theorem quiet_step {γ : Type} (X : OracleComp (Spec4 C) (γ × LifetimeState C E))
    (hX : IsQueryBoundP X (Bad4 D (fun _ => False) (fun _ => False)) 0)
    (st : LifetimeState C E) (hframe : ∀ z ∈ support X, z.2.runCount = st.runCount ∧ z.2.running = st.running)
    (partsOf : ℕ → C.Party → Parts C) (s : IdealState C) (hinv : KeyLinkInv D keys n partsOf st s)
    (res : (γ × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D) X).run s)) :
    KeyLinkInv D keys n partsOf res.1.2 res.2 ∧ ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome := by
  have hw := simulate_within prims D _ _ X hX s res hres
  obtain ⟨hc, hr⟩ := hframe res.1 (simulate_fst prims D X s res hres)
  refine ⟨⟨tablesOk_quiet D n hinv.1 hw (by omega), fun tree fuel steps hs => ?_⟩,
    fun y hy => (hw.2.2.1 y hy).resolve_right id⟩
  rw [hr] at hs
  obtain ⟨h0, hp⟩ := hinv.2 tree fuel steps hs
  rw [hc]
  exact ⟨h0, fun hle => runPhase_mono D keys hw.1 (hp hle)⟩

theorem runCount_of_runsAt {st st' : LifetimeState C E}
    (h : ∀ tree, LifetimeProof.runsAt st' tree = LifetimeProof.runsAt st tree) :
    st'.runCount = st.runCount := by
  have ht := h .top
  have hb : st'.bottomRuns = st.bottomRuns := funext fun b => h (.bottom b)
  simp only [LifetimeProof.runsAt] at ht
  simp only [LifetimeState.runCount, ht, hb]

theorem sign_bad (F S : Address C → Prop) (st : LifetimeState C E) (i : C.Party) (q : TsigQuery C) :
    IsQueryBoundP ((tsigOracles roFree (ThresholdLeanXmss.signerDealt roFree keys (value4 D keys) st i)
      q).run st.sign) (Bad4 D F S) 0 := by
  have hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α), IsQueryBoundP p RoPrgCall 0 →
      IsQueryBoundP (roFree p) (Bad4 D F S) 0 := fun p hp => free_bad D F S _ (ro_local_quiet p hp)
  exact tsig_quiet (Bad4 D F S) roFree hlift _
    ⟨fun x => hlift _ (prfValue_quiet _ x), fun _ _ _ _ => hlift _ (eval_quiet _ _ _ _ _),
      fun _ => isQueryBoundP_pure _ _ _⟩ q st.sign

theorem signAs_step (i : C.Party) (q : TsigQuery C) (st₀ st : LifetimeState C E)
    (hst : st.runCount = st₀.runCount ∧ st.running = st₀.running)
    (partsOf : ℕ → C.Party → Parts C) (s : IdealState C) (hinv : KeyLinkInv D keys n partsOf st₀ s)
    (res : ((TsigSpec C).Range q × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      (LifetimeProof.signAs base4 keys (value4 D keys) i q st)).run s)) :
    KeyLinkInv D keys n partsOf res.1.2 res.2 ∧ ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome := by
  refine quiet_step prims D n keys _ ?_ st₀ (fun z hz => ?_) partsOf s hinv res hres
  · exact zero_bind _ (sign_bad D keys _ _ st i q) fun _ _ => isQueryBoundP_pure _ _ _
  · have hf := LifetimeProof.signAs_frame base4 keys (value4 D keys) i q st z hz
    exact ⟨(runCount_of_runsAt hf.1).trans hst.1, hf.2.trans hst.2⟩

end Step

section Runs

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition) (K : Constants C E) (circuits : Circuits)
variable (settings : Settings) (attempts n : ℕ) (keys : C.Party → Keys C) (h : C.Party)

theorem tablesOk_update {partsOf : ℕ → C.Party → Parts C} {count : ℕ} {s : IdealState C}
    (hT : TablesOk D n partsOf count s) (parts : C.Party → Parts C) :
    TablesOk D n (Function.update partsOf count parts) count s := by
  refine ⟨hT.1, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨hh, r, hr, hc, he⟩ := hT.2.1 y hy
    exact ⟨hh, r, hr, hc, by rwa [Function.update_of_ne (by omega)]⟩
  · obtain ⟨hh, hc, he⟩ := hT.2.2 y hy
    exact ⟨hh, hc, by rwa [Function.update_of_ne (by omega)]⟩

/-- A settled state with a running run in its phase keeps the invariant. -/
theorem settle_inv (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) (hst : st.running = some (tree, fuel, steps))
    (partsOf : ℕ → C.Party → Parts C)
    (s : IdealState C) (hT : TablesOk D n partsOf st.runCount s) (h0 : 0 < st.runCount)
    (hp : st.runCount - 1 ≤ n → RunPhase D keys (partsOf (st.runCount - 1)) steps s.1) :
    KeyLinkInv D keys n partsOf (st.settle D) s := by
  refine ⟨?_, fun tree' fuel' steps' hs => ?_⟩
  · rw [LifetimeProof.settle_runCount]
    exact hT
  have hne : (st.settle D).running ≠ none := by
    rw [hs]
    exact Option.some_ne_none _
  have he := LifetimeProof.settle_running D _ hne
  rw [hs, hst] at he
  obtain ⟨-, -, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj he
  rw [LifetimeProof.settle_runCount]
  exact ⟨h0, hp⟩

/-- The steps after the reveal round make only calls that the rows allow. -/
theorem finish_stepOk (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (hk : ∀ i prss, POk ⟨i, keys i, prss⟩ (k i prss)) (rows : RevealRows C) (i : C.Party) :
    StepOk rows (suspendStep (k i) (prssFinishStep i (rows i))) := by
  rcases hrow : rows i with _ | ⟨out, shared⟩
  · exact trivial
  · intro inbox
    unfold exchangeResume
    dsimp only
    split_ifs
    · simp
    · have hp : POk (G := RealSpec) (⟨i, keys i, out⟩ : Context C)
          ((do require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0]); pure out) >>=
            k i) := by
        rw [bind_assoc]
        refine POk.bind (POk.require _) fun _ => ?_
        rw [pure_bind]
        exact hk i out
      exact IsQueryBoundP.of_imp (partyUnallowed_of_bad rows (ctx := ⟨i, keys i, out⟩) hrow) hp

/-- The parts history across one step. An admitted start (`started`) of run `r = st.runCount ≤ n`
sets `partsOf r` to the parts that `prssInitialData` samples on the copy of run `r`, and the step
ends in the state right after that sampling. Every other step keeps the history. -/
def NewParts (started : Prop) (st : LifetimeState C E) (s : IdealState C)
    (partsOf partsOf' : ℕ → C.Party → Parts C) (s' : IdealState C) : Prop :=
  (started ∧ st.runCount ≤ n → ∃ u ∈ support ((simulateQ (leftImpl prims D)
      (simulateQ (runQ n st.runCount) (prssInitialData D))).run s),
      s' = u.2 ∧ partsOf' = Function.update partsOf st.runCount (fun i => (u.1 i).1)) ∧
  (¬ (started ∧ st.runCount ≤ n) → partsOf' = partsOf)

theorem newParts_same {started : Prop} {st : LifetimeState C E} {s s' : IdealState C}
    {partsOf : ℕ → C.Party → Parts C} (h : ¬ (started ∧ st.runCount ≤ n)) :
    NewParts prims D n started st s partsOf partsOf s' :=
  ⟨fun h' => (h h').elim, fun _ => rfl⟩

theorem newParts_congr {started started' : Prop} (he : started ↔ started') {st : LifetimeState C E}
    {s s' : IdealState C} {partsOf partsOf' : ℕ → C.Party → Parts C}
    (h : NewParts prims D n started st s partsOf partsOf' s') :
    NewParts prims D n started' st s partsOf partsOf' s' := by
  unfold NewParts
  rw [← he]
  exact h

/-- A step keeps the parts of every run that has already started. -/
theorem newParts_agree {started : Prop} {st : LifetimeState C E} {s s' : IdealState C}
    {partsOf partsOf' : ℕ → C.Party → Parts C}
    (hp : NewParts prims D n started st s partsOf partsOf' s') :
    ∀ r < st.runCount, partsOf' r = partsOf r := by
  intro r hr
  by_cases hs : started ∧ st.runCount ≤ n
  · obtain ⟨u, -, -, he⟩ := hp.1 hs
    rw [he]
    exact Function.update_of_ne (by omega) _ _
  · rw [hp.2 hs]

theorem runCount_le_of_runsAt {st st' : LifetimeState C E}
    (h : ∀ tree, LifetimeProof.runsAt st tree ≤ LifetimeProof.runsAt st' tree) :
    st.runCount ≤ st'.runCount :=
  Nat.add_le_add (h .top) (Finset.sum_le_sum fun b _ => h (.bottom b))

/-- A lifetime step never lowers the run count. -/
theorem lifeImpl_runCount (q : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (s : IdealState C) (res : ((LocalSpec C + LifetimeSpec C E).Range q × LifetimeState C E) ×
      IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      ((lifeImpl D K circuits settings attempts n keys h q).run st)).run s)) :
    st.runCount ≤ res.1.2.runCount := by
  have hz := simulate_fst prims D _ s res hres
  rcases q with t | q
  · change res.1 ∈ support ((StateT.lift (advCopy4 (OracleComp.lift (OracleSpec.query t)))).run st)
      at hz
    rw [StateT.run_lift, mem_support_bind_iff] at hz
    obtain ⟨a, -, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · refine runCount_le_of_runsAt fun tree => ?_
    rw [LifetimeProof.lifetimeOracles_runs K circuits settings attempts (roles4 n) base4 D keys
      (value4 D keys) h q st res.1 hz tree]
    omega

/-- An admitted start keeps the invariant. The first table stays once run `n` has started. -/
theorem start_step (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E)
    (partsOf : ℕ → C.Party → Parts C) (s : IdealState C) (hinv : KeyLinkInv D keys n partsOf st s)
    (res : ((LifetimeSpec C E).Range (.start tree) × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      ((lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h
        (.start tree)).run st)).run s)) :
    (∃ partsOf', KeyLinkInv D keys n partsOf' res.1.2 res.2 ∧
      NewParts prims D n (LifetimeProof.canStart attempts D st tree) st s partsOf partsOf' res.2) ∧
      (n < st.runCount → ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome) := by
  rw [LifetimeProof.run_start] at hres
  by_cases hcan : LifetimeProof.canStart attempts D st tree
  swap
  · rw [if_pos hcan] at hres
    have hq := quiet_step prims D n keys (pure (none, st)) (isQueryBoundP_pure _ _ _) st
      (fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; simp)
      partsOf s hinv res hres
    exact ⟨⟨partsOf, hq.1, newParts_same prims D n fun h => hcan h.1⟩, fun _ => hq.2⟩
  rw [if_neg (not_not.mpr hcan)] at hres
  obtain ⟨u, hu, hres⟩ := mem_left_bind prims D hres
  have hres := mem_left_pure prims D hres
  subst hres
  by_cases hrn : st.runCount ≤ n
  · let kk : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput := fun i prss =>
      ceremonyAfterSetup K circuits settings ⟨i, keys i, prss⟩ ((st.top i).getD emptyTop) tree
    have hstart : startSteps (roles4 n st.runCount) D (fun i =>
        (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
          PartyM C E RealSpec TreeOutput)) =
        (fun data i => suspendStep (kk i) (prssInitialSteps D data i)) <$>
          simulateQ (runQ n st.runCount) (prssInitialData D) :=
      startSteps_run D n st.runCount kk
    rw [hstart, map_eq_bind_pure_comp] at hu
    obtain ⟨v, hv, hu⟩ := mem_left_bind prims D hu
    have hu := mem_left_pure prims D hu
    rcases u with ⟨steps, s₁⟩
    simp only [Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    dsimp only
    have hw := simulate_within prims D _ _ _
      (runQ_noStream D n st.runCount _ (qb0_prssInitialData D)) s v hv
    refine ⟨⟨Function.update partsOf st.runCount (fun i => (v.1 i).1), ?_,
      ⟨fun _ => ⟨v, hv, rfl, rfl⟩, fun hn => (hn ⟨hcan, hrn⟩).elim⟩⟩,
      fun hlt => absurd hlt (by omega)⟩
    have hc : ({ LifetimeProof.increment st tree with running := some (tree, ceremonyFuel circuits settings,
        fun i => suspendStep (kk i) (prssInitialSteps D v.1 i)) } : LifetimeState C E).runCount =
        st.runCount + 1 := LifetimeProof.increment_runCount st tree
    refine settle_inv D n keys _ tree _ _ rfl _ _ ?_ ?_ fun _ => ?_
    · rw [hc]
      exact tablesOk_quiet D n (tablesOk_update D n hinv.1 _) hw (by omega)
    · rw [hc]
      omega
    · rw [hc, Nat.add_sub_cancel]
      refine Or.inl ⟨kk, v.1, fun i prss => POk.ceremonyAfterSetup K circuits settings _ tree, ?_, rfl⟩
      exact Function.update_self _ _ _
  · have hstart := hom_startSteps (toWorld (runQ n st.runCount)) worldRoles _
      (rolesHom_roles4 n st.runCount) D (fun i =>
        (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
          PartyM C E RealSpec TreeOutput))
    rw [← hstart] at hu
    dsimp only
    have hw := simulate_within prims D (fun _ => False) (fun _ => False) _
      (later_bad D n st.runCount (by omega) _ _ _) s u hu
    refine ⟨⟨partsOf, ?_, newParts_same prims D n fun h => hrn h.2⟩, fun _ y hy => (hw.2.2.1 y hy).resolve_right id⟩
    have hc : ({ LifetimeProof.increment st tree with running := some (tree, ceremonyFuel circuits settings,
        u.1) } : LifetimeState C E).runCount = st.runCount + 1 := LifetimeProof.increment_runCount st tree
    refine settle_inv D n keys _ tree _ _ rfl _ _ ?_ ?_ fun hle => absurd hle ?_
    · rw [hc]
      exact tablesOk_quiet D n hinv.1 hw (by omega)
    · rw [hc]
      omega
    · rw [hc]
      omega

/-- A round keeps the invariant. The first table stays once run `n` has started. -/
theorem round_step (sent : C.Party → C.Party → Option (Msg E)) (st : LifetimeState C E)
    (partsOf : ℕ → C.Party → Parts C) (s : IdealState C) (hinv : KeyLinkInv D keys n partsOf st s)
    (res : ((LifetimeSpec C E).Range (.round sent) × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      ((lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h
        (.round sent)).run st)).run s)) :
    (∃ partsOf', KeyLinkInv D keys n partsOf' res.1.2 res.2 ∧
      NewParts prims D n False st s partsOf partsOf' res.2) ∧
      (n < st.runCount → ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome) := by
  rw [LifetimeProof.run_round] at hres
  rcases hrun : st.running with _ | ⟨tree, fuel, steps⟩
  · rw [hrun] at hres
    have hq := quiet_step prims D n keys (pure (none, st)) (isQueryBoundP_pure _ _ _) st
      (fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; simp)
      partsOf s hinv res hres
    exact ⟨⟨partsOf, hq.1, newParts_same prims D n fun h => h.1⟩, fun _ => hq.2⟩
  rw [hrun] at hres
  obtain ⟨u, hu, hres⟩ := mem_left_bind prims D hres
  rcases u with ⟨⟨a, next, sent'⟩, s₁⟩
  have hres := mem_left_pure prims D hres
  subst hres
  dsimp only
  obtain ⟨h0, hphase⟩ := hinv.2 tree fuel steps hrun
  have hc : ({ st with running := some (tree, fuel - 1, next) } : LifetimeState C E).runCount =
      st.runCount := rfl
  by_cases hrn : st.runCount - 1 ≤ n
  · rcases hphase hrn with ⟨k, data, hk, hparts, rfl⟩ | ⟨k, active, committed, hk, rfl⟩ |
      ⟨rows, hs, hrk⟩
    · rw [stepRound_commit] at hu
      have hu := mem_left_pure prims D hu
      simp only [Prod.mk.injEq] at hu
      obtain ⟨⟨-, rfl, -⟩, rfl⟩ := hu
      refine ⟨⟨partsOf, settle_inv D n keys _ tree _ _ rfl partsOf _ (by rw [hc]; exact hinv.1)
        (by rw [hc]; exact h0) fun _ => ?_, newParts_same prims D n fun h => h.1⟩, fun _ y hy => hy⟩
      rw [hc]
      exact Or.inr (Or.inl ⟨k, _, _, hk, by rw [hparts]⟩)
    · rw [stepRound_reveal] at hu
      obtain ⟨v, hv, hu⟩ := mem_left_bind prims D hu
      have hu := mem_left_pure prims D hu
      simp only [Prod.mk.injEq] at hu
      obtain ⟨⟨-, rfl, -⟩, rfl⟩ := hu
      obtain ⟨hloc, hst⟩ := copy_local prims D _ (runQ_cases n _) _
        (qb0_prssRevealRows D active _ committed sent) s v hv
      have hgrow := (prssRevealRows_cached prims D active _ committed sent s.1 (v.1, v.2.1) hloc).1
      have hw : Within (fun _ => False) (fun _ => False) s v.2 :=
        ⟨hgrow, by rw [hst], fun y hy => Or.inl (by rwa [hst] at hy),
          fun y hy => Or.inl (by rwa [hst] at hy)⟩
      refine ⟨⟨partsOf, settle_inv D n keys _ tree _ _ rfl partsOf _
        (by rw [hc]; exact tablesOk_quiet D n hinv.1 hw le_rfl) (by rw [hc]; exact h0) fun _ => ?_, newParts_same prims D n fun h => h.1⟩,
        fun _ y hy => (hw.2.2.1 y hy).resolve_right id⟩
      rw [hc]
      exact Or.inr (Or.inr ⟨v.1, finish_stepOk keys k hk v.1, fun name key hn hr =>
        reveal_rowKey prims D active _ committed sent s.1 (v.1, v.2.1) hloc name key hn hr⟩)
    · obtain ⟨hq, hsteps⟩ := stepRound_rows D n (st.runCount - 1) rows sent steps hs
      have hw := simulate_within prims D _ _ _ hq s _ hu
      refine ⟨⟨partsOf, settle_inv D n keys _ tree _ _ rfl partsOf _ ?_ (by rw [hc]; exact h0)
        fun _ => ?_, newParts_same prims D n fun h => h.1⟩, fun hlt y hy => ?_⟩
      · rw [hc]
        refine tablesOk_within D n hinv.1 hw (fun y hy => ?_) (by omega)
        obtain ⟨x, hx, hrx, rfl⟩ := hy
        exact ⟨hx, hw.1 (hrk x.1 x.2.1 hx hrx)⟩
      · rw [hc]
        exact Or.inr (Or.inr ⟨rows, hsteps _ (simulate_fst prims D _ s _ hu),
          fun name key hn hr => hw.1 (hrk name key hn hr)⟩)
      · rcases hw.2.2.1 y hy with h | ⟨hlt', -⟩
        · exact h
        · omega
  · have hq := later_bad D n (st.runCount - 1) (by omega) (fun _ => False) (fun _ => False)
      (stepRound worldRoles D (roundAdversary (I := Keys C) sent) noFunctionality () steps)
    rw [← stepRound_keys] at hq
    have hw := simulate_within prims D _ _ _ hq s _ hu
    refine ⟨⟨partsOf, settle_inv D n keys _ tree _ _ rfl partsOf _
      (by rw [hc]; exact tablesOk_quiet D n hinv.1 hw le_rfl) (by rw [hc]; exact h0)
      fun hle => absurd hle (by rw [hc]; omega), newParts_same prims D n fun h => h.1⟩, fun _ y hy => (hw.2.2.1 y hy).resolve_right id⟩

/-- Every lifetime oracle step of the left world of hop `n` keeps the key-link invariant. After
run `n` starts, no step adds a first-table address. -/
theorem step_inv (q : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (partsOf : ℕ → C.Party → Parts C) (s : IdealState C) (hinv : KeyLinkInv D keys n partsOf st s)
    (res : ((LocalSpec C + LifetimeSpec C E).Range q × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      ((lifeImpl D K circuits settings attempts n keys h q).run st)).run s)) :
    (∃ partsOf', KeyLinkInv D keys n partsOf' res.1.2 res.2 ∧
      NewParts prims D n (∃ tree, q = .inr (.start tree) ∧ LifetimeProof.canStart attempts D st tree)
        st s partsOf partsOf' res.2) ∧
      (n < st.runCount → ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome) := by
  have quiet : ∀ (X : OracleComp (Spec4 C) ((LocalSpec C + LifetimeSpec C E).Range q ×
      LifetimeState C E)), IsQueryBoundP X (Bad4 D (fun _ => False) (fun _ => False)) 0 →
      (∀ z ∈ support X, z.2.runCount = st.runCount ∧ z.2.running = st.running) →
      res ∈ support ((simulateQ (leftImpl prims D) X).run s) →
      (¬ ∃ tree, q = .inr (.start tree) ∧ LifetimeProof.canStart attempts D st tree) →
      (∃ partsOf', KeyLinkInv D keys n partsOf' res.1.2 res.2 ∧
        NewParts prims D n (∃ tree, q = .inr (.start tree) ∧ LifetimeProof.canStart attempts D st tree)
          st s partsOf partsOf' res.2) ∧
        (n < st.runCount → ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome) := fun X hX hf hr hns =>
    have hq := quiet_step prims D n keys X hX st hf partsOf s hinv res hr
    ⟨⟨partsOf, hq.1, newParts_same prims D n fun h => hns h.1⟩, fun _ => hq.2⟩
  have pure_frame : ∀ (z₀ z : (LocalSpec C + LifetimeSpec C E).Range q × LifetimeState C E),
      z₀.2 = st → z ∈ support (pure z₀ : OracleComp (Spec4 C) _) →
      z.2.runCount = st.runCount ∧ z.2.running = st.running := by
    intro z₀ z h₀ hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz h₀
    exact ⟨rfl, rfl⟩
  rcases q with t | q
  · refine quiet _ ?_ (fun z hz => ?_) hres (by rintro ⟨tree, h, -⟩; cases h)
    · change IsQueryBoundP ((StateT.lift (advCopy4 (OracleComp.lift (OracleSpec.query t)))).run st) _ 0
      rw [StateT.run_lift]
      exact zero_bind _ (adv_bad D _ _ _) fun _ _ => isQueryBoundP_pure _ _ _
    · change z ∈ support ((StateT.lift (advCopy4 (OracleComp.lift (OracleSpec.query t)))).run st) at hz
      rw [StateT.run_lift, mem_support_bind_iff] at hz
      obtain ⟨a, -, hz⟩ := hz
      exact pure_frame (a, st) z rfl hz
  change res ∈ support ((simulateQ (leftImpl prims D) ((lifetimeOraclesWith K circuits settings
    attempts (roles4 n) base4 D keys (value4 D keys) h q).run st)).run s) at hres
  cases q with
  | sign q =>
    cases q with
    | corrupt i => exact quiet _ (isQueryBoundP_pure _ _ _) (pure_frame (none, st) · rfl) hres (by rintro ⟨tree, h, -⟩; cases h)
    | tree b =>
      rw [LifetimeProof.run_sign_tree] at hres
      have hq := signAs_step prims D n keys h (.tree b) st st ⟨rfl, rfl⟩ partsOf s hinv res hres
      exact ⟨⟨partsOf, hq.1, newParts_same prims D n fun hs => by
        obtain ⟨⟨tree, h, -⟩, -⟩ := hs; cases h⟩, fun _ => hq.2⟩
    | round1 i J e message =>
      rw [LifetimeProof.run_round1] at hres
      split_ifs at hres
      · exact quiet _ (isQueryBoundP_pure _ _ _) (pure_frame (none, st) · rfl) hres (by rintro ⟨tree, h, -⟩; cases h)
      · have hq := signAs_step prims D n keys i (.round1 i J e message) st
          { st with signed := insert (treeOf e) st.signed } ⟨rfl, rfl⟩ partsOf s
          hinv res hres
        exact ⟨⟨partsOf, hq.1, newParts_same prims D n fun hs => by
        obtain ⟨⟨tree, h, -⟩, -⟩ := hs; cases h⟩, fun _ => hq.2⟩
    | round2 i J e message parts =>
      rw [LifetimeProof.run_round2] at hres
      split_ifs at hres
      · exact quiet _ (isQueryBoundP_pure _ _ _) (pure_frame (none, st) · rfl) hres (by rintro ⟨tree, h, -⟩; cases h)
      · have hq := signAs_step prims D n keys i (.round2 i J e message parts) st
          { st with signed := insert (treeOf e) st.signed } ⟨rfl, rfl⟩
          partsOf s hinv res hres
        exact ⟨⟨partsOf, hq.1, newParts_same prims D n fun hs => by
        obtain ⟨⟨tree, h, -⟩, -⟩ := hs; cases h⟩, fun _ => hq.2⟩
  | publicKey =>
    exact quiet _ (isQueryBoundP_pure _ _ _)
      (pure_frame (st.publicKey (keys h).parameter h, st) · rfl) hres
      (by rintro ⟨tree, h, -⟩; cases h)
  | start tree =>
    obtain ⟨⟨p, hi, hp⟩, hf⟩ :=
      start_step prims D K circuits settings attempts n keys h tree st partsOf s hinv res hres
    refine ⟨⟨p, hi, newParts_congr prims D n ⟨fun hc => ⟨tree, rfl, hc⟩, ?_⟩ hp⟩, hf⟩
    rintro ⟨tree', he, hc⟩
    cases he
    exact hc
  | round sent =>
    obtain ⟨⟨p, hi, hp⟩, hf⟩ :=
      round_step prims D K circuits settings attempts n keys h sent st partsOf s hinv res hres
    exact ⟨⟨p, hi, newParts_congr prims D n ⟨False.elim, fun hs => by obtain ⟨_, he, _⟩ := hs; cases he⟩ hp⟩, hf⟩

/-- The adversary program after the keygen keeps the key-link invariant in the left world, and the
parts of every run that has already started stay. -/
theorem loop_inv {β : Type} (prog : OracleComp (LocalSpec C + LifetimeSpec C E) β)
    (st : LifetimeState C E) (partsOf : ℕ → C.Party → Parts C) (s : IdealState C)
    (hinv : KeyLinkInv D keys n partsOf st s) (res : (β × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      ((simulateQ (lifeImpl D K circuits settings attempts n keys h) prog).run st)).run s)) :
    ∃ partsOf', KeyLinkInv D keys n partsOf' res.1.2 res.2 ∧
      ∀ r < st.runCount, partsOf' r = partsOf r := by
  induction prog using OracleComp.inductionOn generalizing st partsOf s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure] at hres
    have he := mem_left_pure prims D hres
    subst he
    exact ⟨partsOf, hinv, fun _ _ => rfl⟩
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hres
    obtain ⟨u, hu, hres⟩ := mem_left_bind prims D hres
    obtain ⟨⟨partsOf', hinv', hnew⟩, -⟩ := step_inv prims D K circuits settings attempts n keys h q st
      partsOf s hinv u hu
    have hle := lifeImpl_runCount prims D K circuits settings attempts n keys h q st s u hu
    obtain ⟨p, hp, hagree⟩ := ih u.1.1 u.1.2 partsOf' u.2 hinv' hres
    exact ⟨p, hp, fun r hr => (hagree r (by omega)).trans (newParts_agree prims D n hnew r hr)⟩

theorem runQ_self : runQ (C := C) n n = targetQ := by
  unfold runQ
  rw [if_neg (lt_irrefl n), if_pos rfl]

/-- An admitted start of run `r = st.runCount` samples the parts and the commitments of its
operators by `prssInitialData` on the copy of run `r`. The run-`n` copy is `targetQ`. -/
theorem start_eq (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E)
    (hcan : LifetimeProof.canStart attempts D st tree) :
    (lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D keys (value4 D keys) h
      (.start tree)).run st =
      (fun data => (some (toCoalition D fun i => suspendStep (fun prss =>
          (ceremonyAfterSetup K circuits settings ⟨i, keys i, prss⟩ ((st.top i).getD emptyTop) tree :
            PartyM C E RealSpec TreeOutput)) (prssInitialSteps D data i)),
        ({ LifetimeProof.increment st tree with running := some (tree, ceremonyFuel circuits settings,
          fun i => suspendStep (fun prss =>
            (ceremonyAfterSetup K circuits settings ⟨i, keys i, prss⟩ ((st.top i).getD emptyTop) tree :
              PartyM C E RealSpec TreeOutput)) (prssInitialSteps D data i)) }).settle D)) <$>
        simulateQ (runQ n st.runCount) (prssInitialData D) := by
  rw [LifetimeProof.run_start, if_neg (not_not.mpr hcan)]
  rw [show (fun i => (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
      PartyM C E RealSpec TreeOutput)) = fun i => prssSetup i >>= fun prss =>
        ceremonyAfterSetup K circuits settings ⟨i, keys i, prss⟩ ((st.top i).getD emptyTop) tree
    from rfl, startSteps_run, map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind]
  rfl

end Runs

section Program

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition) (K : Constants C E) (circuits : Circuits)
variable (settings : Settings) (attempts n : ℕ) (A : LifetimeAdversary C E)

/-- The keygen phase of `program4` makes no query of `Bad4`. -/
theorem keygen_bad (F S : Address C → Prop) {I : Type} (B : Adversary C E I PEmpty PEmpty)
    (state : B.State) :
    IsQueryBoundP (executePhase base4 D B noFunctionality setupRounds state
      fun i => (keygen i : PartyM C E RealSpec (Keys C))) (Bad4 D F S) 0 := by
  refine bad4_quiet D F S _ (keygen_phase_quiet D B state setupRounds) ?_
  rw [← treeSim_hom_phase (fun p => toWorld freeQ p) (fun a => MonadHom.mmap_pure _ a)
    (fun p k => MonadHom.mmap_bind _ p k) worldRoles base4 (fun p => toWorld_counted _ p)
    (fun p => toWorld_free _ p)]
  change IsQueryBoundP (simulateQ (worldTo freeQ) _) _ 0
  refine qb0_simulateQ (p := fun _ => False) _ (fun t _ => ?_) _ (by convert qb0_false _)
  rcases t with (t | t) | t
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim
  · exact isQueryBoundP_pure _ _ _
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim

theorem tablesOk_start (partsOf : ℕ → C.Party → Parts C) (count : ℕ) (s : IdealState C)
    (hw : Within (fun _ => False) (fun _ => False) idealStart s) : TablesOk D n partsOf count s := by
  refine ⟨hw.2.1, fun y hy => ?_, fun y hy => ?_⟩
  · rcases hw.2.2.1 y hy with h | h
    · simp [idealStart] at h
    · exact h.elim
  · rcases hw.2.2.2 y hy with h | h
    · simp [idealStart] at h
    · exact h.elim

/-- Every supported outcome of the actual left world of hop `n` has tables with a run
attribution: each first-table key of a hidden name answers the input of the parts of a run before
run `n`, and each second-table key answers the input of the parts of run `n`. -/
theorem program4_keyLink (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart)) :
    ∃ partsOf count, TablesOk D n partsOf count r.2 := by
  unfold program4 lifetimeGameWith at hr
  obtain ⟨u, hu, hr⟩ := mem_left_bind prims D hr
  have hw₀ := simulate_within prims D (fun _ => False) (fun _ => False) _ (adv_bad D _ _ _)
    idealStart u hu
  obtain ⟨v, hv, hr⟩ := mem_left_bind prims D hr
  have hw₁ := within_trans hw₀ (simulate_within prims D (fun _ => False) (fun _ => False) _
    (keygen_bad D _ _ A.keygen u.1) u.2 v hv)
  let zero : ℕ → C.Party → Parts C := fun _ _ => ⟨0, fun _ => 0, fun _ => 0⟩
  have hT₁ := tablesOk_start D n zero 0 v.2 hw₁
  rcases v with ⟨⟨state, outputs⟩, s₁⟩
  dsimp only at hr hT₁
  split at hr
  swap
  · exact ⟨_, _, by rw [mem_left_pure prims D hr]; exact hT₁⟩
  rename_i h _
  split_ifs at hr with hout
  swap
  · exact ⟨_, _, by rw [mem_left_pure prims D hr]; exact hT₁⟩
  obtain ⟨w, hw, hr⟩ := mem_left_bind prims D hr
  obtain ⟨partsOf, hinv, -⟩ := loop_inv prims D K circuits settings attempts n
    (fun i => (outputs i).getD default) h _ _ zero s₁
    ⟨tablesOk_start D n _ _ s₁ hw₁, fun tree fuel steps hs => by cases hs⟩ w hw
  rcases w with ⟨⟨forgery, st⟩, s₂⟩
  dsimp only at hr hinv
  split_ifs at hr
  swap
  · exact ⟨_, _, by rw [mem_left_pure prims D hr]; exact hinv.1⟩
  split at hr
  swap
  · exact ⟨_, _, by rw [mem_left_pure prims D hr]; exact hinv.1⟩
  refine ⟨partsOf, st.runCount, tablesOk_quiet D n hinv.1
    (simulate_within prims D _ _ _ ?_ s₂ r hr) le_rfl⟩
  have hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α), IsQueryBoundP p RoPrgCall 0 →
      IsQueryBoundP (roFree p) (Bad4 D (fun _ => False) (fun _ => False)) 0 :=
    fun p hp => free_bad D _ _ _ (ro_local_quiet p hp)
  exact forgeryWins_quiet _ roFree hlift _
    (dealtWith_quiet _ roFree hlift _ _ _ _ (fun x => hlift _ (prfValue_quiet _ x))) st.sign forgery

/-- Each second-table key of a hidden name is the cached answer to the `.derive` input of that
name from the parts of run `n`. So the honest holders of the name agree on one key in run `n`. -/
theorem second_key (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart)) :
    ∃ parts : C.Party → Parts C, ∀ name key a, (r.2.2.2.1 ((name, key), a)).isSome →
      Hidden D name ∧ r.2.1 (hiddenInput parts name) = some key := by
  obtain ⟨partsOf, count, hT⟩ := program4_keyLink prims D K circuits settings attempts n A r hr
  exact ⟨partsOf n, fun name key a hy => ⟨(hT.2.2 _ hy).1, (hT.2.2 _ hy).2.2⟩⟩

/-- The second table holds at most one key of each hidden name. -/
theorem second_key_unique (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart))
    (name : KeyName C) (key key' : HashOutput) (a b : ℕ × ℕ × ℕ)
    (ha : (r.2.2.2.1 ((name, key), a)).isSome) (hb : (r.2.2.2.1 ((name, key'), b)).isSome) :
    key = key' := by
  obtain ⟨parts, hp⟩ := second_key prims D K circuits settings attempts n A r hr
  exact Option.some.inj ((hp name key a ha).2.symm.trans (hp name key' b hb).2)

/-- The first table holds at most `n` keys of each name. -/
theorem first_keys_ncard (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart)) (name : KeyName C) :
    {key | ∃ a, (r.2.2.1 ((name, key), a)).isSome}.ncard ≤ n := by
  obtain ⟨partsOf, count, hT⟩ := program4_keyLink prims D K circuits settings attempts n A r hr
  let f : ℕ → HashOutput := fun r' => (r.2.1 (hiddenInput (partsOf r') name)).getD 0
  have hsub : {key | ∃ a, (r.2.2.1 ((name, key), a)).isSome} ⊆
      ((Finset.range n).image f : Set HashOutput) := by
    rintro key ⟨a, ha⟩
    obtain ⟨-, r', hr', -, he⟩ := hT.2.1 _ ha
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨r', hr', by simp only [f]; rw [he]; rfl⟩
  calc {key | ∃ a, (r.2.2.1 ((name, key), a)).isSome}.ncard
      ≤ ((Finset.range n).image f : Set HashOutput).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((Finset.range n).image f).card := Set.ncard_coe_finset _
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

/-- At a boundary with the parts history `partsOf`, a hidden key in both tables is the cached
answer both to the run-`n` input of its name and to the input of the same name from the parts of a
started run `r' < n`. `step_inv` fixes `partsOf r` at the admitted start of run `r` to the
sampled parts and keeps it for every later step (`NewParts`, `newParts_agree`). -/
theorem keyOverlap_of_inv (keys : C.Party → Keys C) (partsOf : ℕ → C.Party → Parts C)
    (st : LifetimeState C E) (s : IdealState C) (hinv : KeyLinkInv D keys n partsOf st s)
    (name : KeyName C) (ho : KeyOverlap name s) :
    ∃ r' < n, r' < st.runCount ∧ ∃ key, s.1 (hiddenInput (partsOf r') name) = some key ∧
      s.1 (hiddenInput (partsOf n) name) = some key := by
  obtain ⟨key, a, b, ha, hb⟩ := ho
  obtain ⟨-, r', hr', hc, he⟩ := hinv.1.2.1 _ ha
  exact ⟨r', hr', hc, key, he, (hinv.1.2.2 _ hb).2.2⟩

end Program

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_inv

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.start_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms start_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.program4_keyLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4_keyLink

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.second_key_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_key_unique

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.first_keys_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_keys_ncard

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.keyOverlap_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keyOverlap_of_inv

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealKeyLink.loop_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loop_inv

end ThresholdLeanXmssSecurity.LifetimeIdealKeyLink
