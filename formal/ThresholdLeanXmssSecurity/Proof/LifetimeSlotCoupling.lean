import ThresholdLeanXmssSecurity.Proof.LifetimeSlotTransport

/-!
# Request couplings of the lifetime slot worlds

The separated stream tables have disjoint hidden keys before the recorded overlap event.
Their union therefore returns the same cached answer as either table at its own entries.
The relation retains the complete lifetime state, hash cache and observation log.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeSlotCoupling

open LifetimeSlots LifetimeSlotTransport

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- A coupling retains every support property of its left marginal. -/
theorem relTriple_with_left_support {α β : Type} {p : ProbComp α} {q : ProbComp β}
    {R : α → β → Prop} {P : α → Prop} (h : RelTriple p q R)
    (hp : ∀ a ∈ support p, P a) : RelTriple p q (fun a b => R a b ∧ P a) := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ⟨hc z hz, hp z.1 ?_⟩⟩
  have hz' : z.1 ∈ support 𝒟[p] := by
    rw [← c.2.map_fst, support_map]
    exact ⟨z, hz, rfl⟩
  exact (mem_support_iff_evalDist_apply_ne_zero p z.1).2 hz'

/-- Before a recorded overlap, the shared and retained selected tables cannot contain
entries under the same name and key, even at different stream positions. -/
theorem clean_disjoint (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (clean : ¬ Bad D s) (name : KeyName C) (key : HashOutput) (a b : ℕ × ℕ × ℕ) :
    ¬ ((s.1.2.1 (name, key, a)).isSome ∧ (s.2.selected (name, key, b)).isSome) := by
  obtain ⟨_, _, _, _, hidden, _, _, _, _, seen⟩ := related
  intro ⟨ha, hb⟩
  have hn : Hidden D name := hidden (name, key, a) (Or.inl ha)
  apply clean
  refine ⟨⟨name, hn⟩, seen ?_⟩
  simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨key, a, b, ha, hb⟩

/-- The same left-biased union that occurs in `StateRelation`. -/
def mergeStreams (first second : StreamCache C) : StreamCache C :=
  fun x => (first x).or (second x)

-- The cache-update proof is `LifetimePrfTransportProof.merge_cacheQuery_first`,
-- in the actual `PrgInput` layout rather than the hidden-cache address layout.
theorem mergeStreams_cacheQuery (first second : StreamCache C) (x : PrgInput C) (b : Bit) :
    mergeStreams (first.cacheQuery x b) second = (mergeStreams first second).cacheQuery x b := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [mergeStreams]
  · simp [mergeStreams, QueryCache.cacheQuery_of_ne _ _ hy]

/-- The actual lazy stream draw in its cache-hit and fresh-sample form. -/
def streamDraw (cache : StreamCache C) (x : PrgInput C) : ProbComp (Bit × StreamCache C) :=
  match cache x with
  | some b => pure (b, cache)
  | none => (fun b => (b, cache.cacheQuery x b)) <$> ($ᵗ Bit)

-- `LifetimePrfTransportProof.randomOracle_run`, with `PrgInput` addresses.
theorem streamDraw_eq (cache : StreamCache C) (x : PrgInput C) :
    ((PrgInput C →ₒ Bit).randomOracle x).run cache = streamDraw cache x := by
  unfold streamDraw
  cases hc : cache x <;>
    simp [StateT.run_bind, StateT.run_get, hc, StateT.run_modifyGet, StateT.run_pure,
      bind_pure_comp, uniformSampleImpl]

/-- A lazy stream draw preserves every previously present address. -/
theorem streamDraw_grows (cache : StreamCache C) (x : PrgInput C)
    (r : Bit × StreamCache C) (hr : r ∈ support (streamDraw cache x)) :
    ∀ y, (cache y).isSome → (r.2 y).isSome := by
  unfold streamDraw at hr
  cases hc : cache x with
  | some v =>
    simp only [hc, mem_support_pure_iff] at hr
    rw [hr]
    exact fun _ hy => hy
  | none =>
    simp only [hc, support_map, Set.mem_image] at hr
    obtain ⟨b, _, rfl⟩ := hr
    intro y hy
    change ((cache.cacheQuery x b) y).isSome = true
    by_cases he : y = x
    · subst he; simp
    · rwa [QueryCache.cacheQuery_of_ne _ _ he]

/-- Keeping all present addresses keeps all recorded key overlaps. -/
theorem overlapNames_mono (D : C.Coalition) (first second first' second' : StreamCache C)
    (hfirst : ∀ x, (first x).isSome → (first' x).isSome)
    (hsecond : ∀ x, (second x).isSome → (second' x).isSome) :
    overlapNames D first second ⊆ overlapNames D first' second' := by
  intro name hn
  simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
  obtain ⟨key, a, b, ha, hb⟩ := hn
  exact ⟨key, a, b, hfirst _ ha, hsecond _ hb⟩

/-- Disjoint tables have the same union in either order. -/
theorem mergeStreams_comm (first second : StreamCache C)
    (apart : ∀ x, ¬ ((first x).isSome ∧ (second x).isSome)) :
    mergeStreams first second = mergeStreams second first := by
  funext x
  have hx := apart x
  cases hf : first x <;> cases hs : second x <;> simp_all [mergeStreams]

/-- The overlap event does not depend on the order of the tables. -/
theorem overlapNames_comm (D : C.Coalition) (first second : StreamCache C) :
    overlapNames D first second = overlapNames D second first := by
  apply Finset.ext
  intro name
  simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨key, a, b, ha, hb⟩ <;> exact ⟨key, b, a, hb, ha⟩

/-- Absence of a hidden-key overlap makes a union of hidden tables commutative. -/
theorem mergeStreams_comm_of_clean (D : C.Coalition) (first second : StreamCache C)
    (hidden : ∀ x, (first x).isSome ∨ (second x).isSome → Hidden D x.1)
    (clean : ¬ (overlapNames D first second).Nonempty) :
    mergeStreams first second = mergeStreams second first := by
  apply mergeStreams_comm
  intro x hx
  apply clean
  refine ⟨⟨x.1, hidden x (Or.inl hx.1)⟩, ?_⟩
  simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x.2.1, x.2.2, x.2.2, hx⟩

/-- Drawing a hidden name preserves the hidden-name domain of a table. -/
theorem streamDraw_hidden (D : C.Coalition) (cache : StreamCache C) (x : PrgInput C)
    (hidden : Hidden D x.1) (before : ∀ y, (cache y).isSome → Hidden D y.1)
    (r : Bit × StreamCache C) (hr : r ∈ support (streamDraw cache x)) :
    ∀ y, (r.2 y).isSome → Hidden D y.1 := by
  unfold streamDraw at hr
  cases hc : cache x with
  | some v =>
    simp only [hc, mem_support_pure_iff] at hr
    rw [hr]
    exact before
  | none =>
    simp only [hc, support_map, Set.mem_image] at hr
    obtain ⟨b, _, rfl⟩ := hr
    intro y hy
    change ((cache.cacheQuery x b) y).isSome = true at hy
    by_cases he : y = x
    · subst he; exact hidden
    · exact before y (by rwa [QueryCache.cacheQuery_of_ne _ _ he] at hy)

/-- Reading the first table agrees with reading its union with the second table,
unless the first draw creates an actual hidden-key overlap. -/
theorem streamDraw_coupling (D : C.Coalition) (first second : StreamCache C)
    (x : PrgInput C) (hidden : Hidden D x.1) :
    RelTriple (streamDraw first x) (streamDraw (mergeStreams first second) x)
      (fun a b => (overlapNames D a.2 second).Nonempty ∨
        (a.1 = b.1 ∧ mergeStreams a.2 second = b.2)) := by
  cases hf : first x with
  | some v =>
    simp only [streamDraw, hf, mergeStreams, Option.some_or]
    exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)
  | none =>
    cases hs : second x with
    | none =>
      simp only [streamDraw, hf, mergeStreams, Option.none_or, hs]
      apply relTriple_map
      apply relTriple_post_mono (relTriple_refl ($ᵗ Bit))
      intro a b hab
      change a = b at hab
      subst b
      exact Or.inr ⟨rfl, mergeStreams_cacheQuery first second x a⟩
    | some v =>
      apply relTriple_post_mono (relTriple_left_support _ _
        (fun a : Bit × StreamCache C => (overlapNames D a.2 second).Nonempty) ?_)
        (fun _ _ hb => Or.inl hb)
      intro r hr
      simp only [streamDraw, hf, support_map, Set.mem_image] at hr
      obtain ⟨b, _, rfl⟩ := hr
      refine ⟨⟨x.1, hidden⟩, ?_⟩
      simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x.2.1, x.2.2, x.2.2, by simp, by change (second x).isSome = true; simp [hs]⟩

/-- The corresponding coupling for a draw from the selected table, while the
merged interpreter still gives the shared table priority. -/
theorem streamDraw_second_coupling (D : C.Coalition) (first second : StreamCache C)
    (x : PrgInput C) (hidden : Hidden D x.1)
    (names : ∀ y, (first y).isSome ∨ (second y).isSome → Hidden D y.1)
    (clean : ¬ (overlapNames D first second).Nonempty) :
    RelTriple (streamDraw second x) (streamDraw (mergeStreams first second) x)
      (fun a b => (overlapNames D first a.2).Nonempty ∨
        (a.1 = b.1 ∧ mergeStreams first a.2 = b.2)) := by
  have coupled := streamDraw_coupling D second first x hidden
  rw [← mergeStreams_comm_of_clean D first second names clean] at coupled
  have framed := relTriple_with_left_support coupled
    (fun r hr => streamDraw_hidden D second x hidden (fun y hy => names y (Or.inr hy)) r hr)
  apply relTriple_post_mono framed
  intro a b hab
  by_cases bad : (overlapNames D first a.2).Nonempty
  · exact Or.inl bad
  · rcases hab.1 with overlap | equal
    · exact False.elim (bad (by simpa only [overlapNames_comm D a.2 first] using overlap))
    · refine Or.inr ⟨equal.1, ?_⟩
      rw [mergeStreams_comm_of_clean D first a.2 (fun y hy => hy.elim
        (fun h => names y (Or.inl h)) (hab.2 y)) bad]
      exact equal.2

/-- The evaluated three-copy interface used by the actual scheduler roles. -/
def localKernel (prims : Primitives) (D : C.Coalition) :
    QueryImpl (LifetimeKeygenPrograms.Spec3 C) (StateT (WorldState C) ProbComp) :=
  fun q => evalEmulation prims (LifetimeKeygenPrograms.impl3 D q)

/-- Stream-table union, with the complete common hash state and observation log. -/
def WorldRelation (D : C.Coalition) (retained : StreamCache C)
    (s t : WorldState C) : Prop :=
  t.1 = mergeStreams s.1 retained ∧ s.2 = t.2 ∧
    ∀ x, (s.1 x).isSome ∨ (retained x).isSome → Hidden D x.1

theorem evalEmulation_adversary (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LocalSpec C) α) (s : WorldState C) :
    (evalEmulation prims ((emulatedRoles D).adversary p)).run s =
      (fun r => (r.1.1, (s.1, r.2, s.2.2 ++ r.1.2))) <$>
        (simulateQ (worldAnswer prims) (observe p)).run s.2.1 := by
  simp only [evalEmulation, emulatedRoles, StateT.run_mk, StateT.run_lift,
    bind_pure_comp, WriterT.run_map, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- A hidden honest query is the literal lazy stream draw, with no hash or log effect. -/
theorem evalEmulation_hidden (prims : Primitives) (D : C.Coalition)
    (x : PrgInput C) (hidden : Hidden D x.1) (s : WorldState C) :
    (evalEmulation prims ((emulatedRoles D).honest
      (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> streamDraw s.1 x := by
  rw [LifetimePrfTransportProof.emul_honest_hidden D x hidden]
  change (fun r : ((Bit × StreamCache C) × CallLog C) × HashCache C =>
      (r.1.1.1, (r.1.1.2, r.2, s.2.2 ++ r.1.2))) <$>
    (simulateQ (worldAnswer prims) ((fun r => (r, ([] : CallLog C))) <$>
      free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run s.1) (LocalSpec C)))).run s.2.1 = _
  simp only [simulateQ_map, StateT.run_map, treeSim_world_sample, StateT.run_lift,
    bind_pure_comp, Functor.map_map, streamDraw_eq, List.append_nil]

/-- Every interface query preserves the domain of the stream table. -/
theorem localKernel_grows (prims : Primitives) (D : C.Coalition)
    (q : (LifetimeKeygenPrograms.Spec3 C).Domain) (s : WorldState C)
    (r : (LifetimeKeygenPrograms.Spec3 C).Range q × WorldState C)
    (hr : r ∈ support ((localKernel prims D q).run s)) :
    ∀ x, (s.1 x).isSome → (r.2.1 x).isSome := by
  rcases q with (q | q) | q
  · change r ∈ support ((evalEmulation prims ((emulatedRoles D).adversary _)).run s) at hr
    rw [evalEmulation_adversary] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact fun _ hx => hx
  · change r ∈ support ((evalEmulation prims ((emulatedRoles D).honest _)).run s) at hr
    by_cases hidden : ∃ x, q = .inr (.inr x) ∧ Hidden D x.1
    · obtain ⟨x, rfl, hx⟩ := hidden
      erw [evalEmulation_hidden prims D x hx] at hr
      have hr' : r ∈ support ((fun a : Bit × StreamCache C => (a.1, (a.2, s.2))) <$>
          streamDraw s.1 x) := hr
      simp only [support_map] at hr'
      obtain ⟨a, ha, rfl⟩ := hr'
      exact streamDraw_grows _ _ _ ha
    · erw [LifetimePrfTransportProof.emul_honest_other D q (by
        intro x hx hh; exact hidden ⟨x, hx, hh⟩), evalEmulation_lift] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact fun _ hx => hx
  · change r ∈ support ((evalEmulation prims (StateT.lift (liftM (free _)))).run s) at hr
    rw [evalEmulation_lift] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact fun _ hx => hx

/-- A query on the actual roles either preserves the full world relation or creates
an overlap in the separated stream tables. -/
theorem localKernel_coupling (prims : Primitives) (D : C.Coalition)
    (q : (LifetimeKeygenPrograms.Spec3 C).Domain) (retained : StreamCache C)
    (s t : WorldState C) (related : WorldRelation D retained s t) :
    RelTriple ((localKernel prims D q).run s) ((localKernel prims D q).run t)
      (fun a b => (overlapNames D a.2.1 retained).Nonempty ∨
        (a.1 = b.1 ∧ WorldRelation D retained a.2 b.2)) := by
  obtain ⟨merged, hashlog, names⟩ := related
  rcases q with (q | q) | q
  · change RelTriple ((evalEmulation prims ((emulatedRoles D).adversary _)).run s)
      ((evalEmulation prims ((emulatedRoles D).adversary _)).run t) _
    rw [evalEmulation_adversary, evalEmulation_adversary, hashlog]
    apply relTriple_map
    apply relTriple_post_mono (relTriple_refl _)
    intro a b hab
    change a = b at hab
    subst b
    exact Or.inr ⟨rfl, merged, rfl, names⟩
  · change RelTriple ((evalEmulation prims ((emulatedRoles D).honest _)).run s)
      ((evalEmulation prims ((emulatedRoles D).honest _)).run t) _
    by_cases hidden : ∃ x, q = .inr (.inr x) ∧ Hidden D x.1
    · obtain ⟨x, rfl, hx⟩ := hidden
      erw [evalEmulation_hidden prims D x hx, evalEmulation_hidden prims D x hx, merged]
      apply relTriple_map
      apply relTriple_post_mono (relTriple_with_left_support
        (streamDraw_coupling D s.1 retained x hx)
        (fun a ha => streamDraw_hidden D s.1 x hx
          (fun y hy => names y (Or.inl hy)) a ha))
      intro a b hab
      rcases hab.1 with bad | good
      · exact Or.inl bad
      · exact Or.inr ⟨good.1, good.2.symm, hashlog, fun y hy =>
          hy.elim (hab.2 y) (fun h => names y (Or.inr h))⟩
    · have other := LifetimePrfTransportProof.emul_honest_other D q (by
        intro x hx hh; exact hidden ⟨x, hx, hh⟩)
      erw [other, evalEmulation_lift, evalEmulation_lift]
      erw [congrArg Prod.fst hashlog, congrArg Prod.snd hashlog]
      apply relTriple_map
      apply relTriple_post_mono (relTriple_refl _)
      intro a b hab
      change a = b at hab
      subst b
      exact Or.inr ⟨rfl, merged, rfl, names⟩
  · change RelTriple ((evalEmulation prims (StateT.lift (liftM (free _)))).run s)
      ((evalEmulation prims (StateT.lift (liftM (free _)))).run t) _
    erw [evalEmulation_lift, evalEmulation_lift]
    erw [congrArg Prod.fst hashlog, congrArg Prod.snd hashlog]
    apply relTriple_map
    apply relTriple_post_mono (relTriple_refl _)
    intro a b hab
    change a = b at hab
    subst b
    exact Or.inr ⟨rfl, merged, rfl, names⟩

/-- Any actual three-copy local computation preserves existing stream entries. -/
theorem localRun_grows (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LifetimeKeygenPrograms.Spec3 C) α) (s : WorldState C)
    (r : α × WorldState C) (hr : r ∈ support ((simulateQ (localKernel prims D) p).run s)) :
    ∀ x, (s.1 x).isSome → (r.2.1 x).isSome := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr]
    exact fun _ hx => hx
  | query_bind q f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, hr⟩ := hr
    exact fun x hx => ih a.1 a.2 r hr x (localKernel_grows prims D q s a ha x hx)

/-- The finite draw coupling extends through the complete adaptive local computation. -/
theorem localRun_coupling (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LifetimeKeygenPrograms.Spec3 C) α) (retained : StreamCache C)
    (s t : WorldState C) (related : WorldRelation D retained s t) :
    RelTriple ((simulateQ (localKernel prims D) p).run s)
      ((simulateQ (localKernel prims D) p).run t)
      (fun a b => (overlapNames D a.2.1 retained).Nonempty ∨
        (a.1 = b.1 ∧ WorldRelation D retained a.2 b.2)) := by
  induction p using OracleComp.inductionOn generalizing s t with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨rfl, related⟩)
  | query_bind q f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply relTriple_bind (localKernel_coupling prims D q retained s t related)
    rintro ⟨a, s'⟩ ⟨b, t'⟩ (bad | ⟨equal, rel⟩)
    · apply relTriple_post_mono (relTriple_left_support _ _
        (fun a : α × WorldState C => (overlapNames D a.2.1 retained).Nonempty) ?_)
        (fun _ _ hb => Or.inl hb)
      intro r hr
      exact bad.mono (overlapNames_mono D s'.1 retained r.2.1 retained
        (localRun_grows prims D (f a) s' r hr) (fun _ hx => hx))
    · cases equal
      exact ih a s' t' rel

/-- The local interpreter is the evaluation of the scheduler's existing three-copy map. -/
theorem localRun_eq (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LifetimeKeygenPrograms.Spec3 C) α) :
    simulateQ (localKernel prims D) p =
      evalEmulation prims (LifetimeKeygenPrograms.H3 D p) := by
  symm
  exact LifetimeEmulatedBudget.hom_simulateQ (evalHom prims) _ _

/-- An own-table execution runs the same emulation on its private stream table;
the surrounding shared table is only a frame. -/
def ownHom : EmulationM C →ᵐ StateT (StreamCache C) (EmulationM C) where
  toFun _ p := StateT.mk fun own => StateT.lift (p.run own)
  toFun_pure' a := by
    apply StateT.ext
    intro own
    apply StateT.ext
    intro shared
    simp [StateT.run_lift]
  toFun_bind' p f := by
    apply StateT.ext
    intro own
    apply StateT.ext
    intro shared
    simp [StateT.run_bind, StateT.run_lift]

theorem ownHom_roles (D : C.Coalition) :
    LifetimeEmulatedBudget.RolesHom (ownHom (C := C)) (emulatedRoles D) (ownRoles D) := by
  constructor
  · intro α p
    apply StateT.ext
    intro own
    apply StateT.ext
    intro shared
    simp [ownHom, ownRoles, emulatedRoles, StateT.run_lift]
  · intro α p
    rfl

/-- Running an own-table computation moves exactly that table through the local evaluator. -/
theorem evalEmulation_own (prims : Primitives) {α : Type} (p : EmulationM C α)
    (own : StreamCache C) (s : WorldState C) :
    (evalEmulation prims ((ownHom p).run own)).run s =
      (fun r => ((r.1, r.2.1), (s.1, r.2.2))) <$>
        (evalEmulation prims p).run (own, s.2) := by
  simp only [evalEmulation, ownHom, StateT.run_mk, StateT.run_lift,
    bind_pure_comp, WriterT.run_map, simulateQ_map, StateT.run_map, Functor.map_map]

-- `LifetimeEmulatedBudget.hom_stepRound`, without its unused finiteness hypotheses.
theorem hom_stepRound {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (φ : m →ᵐ n) {I α : Type} (Ro : Roles C m) (Ro' : Roles C n)
    (hR : LifetimeEmulatedBudget.RolesHom φ Ro Ro') (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    φ (stepRound Ro D A noFunctionality state steps) =
      stepRound Ro' D A noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, hR.adversary, SeedHitProof.hom_sequenceFin]
  apply bind_congr
  intro r
  congr 1
  congr 1
  funext j
  cases hs : steps j with
  | done out => exact MonadHom.mmap_pure _ _
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp [hj]
    · simp [hj, hR.honest]
  | call input resume => exact input.elim

section Steps

/-- The complete real round, including every suspended continuation, has the local union coupling. -/
theorem stepRound_coupling (prims : Primitives) (D : C.Coalition) {I α : Type}
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (retained : StreamCache C)
    (s t : WorldState C) (related : WorldRelation D retained s t) :
    RelTriple ((evalEmulation prims (stepRound (emulatedRoles D) D A noFunctionality state steps)).run s)
      ((evalEmulation prims (stepRound (emulatedRoles D) D A noFunctionality state steps)).run t)
      (fun a b => (overlapNames D a.2.1 retained).Nonempty ∨
        (a.1 = b.1 ∧ WorldRelation D retained a.2 b.2)) := by
  have coupled := localRun_coupling prims D
    (stepRound LifetimeKeygenPrograms.emulRoles3 D A noFunctionality state steps)
    retained s t related
  rw [localRun_eq, hom_stepRound (LifetimeKeygenPrograms.H3 D)
    _ _ (LifetimeKeygenPrograms.rolesHom_emul D)] at coupled
  exact coupled

/-- The own-table round is precisely the own-table image of the shared-role round. -/
theorem own_stepRound (D : C.Coalition) {I α : Type}
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound (ownRoles D) D A noFunctionality state steps =
      ownHom (stepRound (emulatedRoles D) D A noFunctionality state steps) :=
  (hom_stepRound ownHom _ _ (ownHom_roles D) D A state steps).symm

end Steps

/-- The observer records the present overlap while retaining its selected table. -/
def recordWorld (D : C.Coalition) (g : Ghost D) (w : WorldState C) : Ghost D :=
  { g with overlaps := g.overlaps ∪ overlapNames D w.1 g.selected }

theorem worldRelation_of_stateRelation (attempts : ℕ) (k : Fin (lifetimeRuns attempts))
    (D : C.Coalition) (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) : WorldRelation D s.2.selected s.1.2 t.2 :=
  ⟨funext related.2.2.2.1, Prod.ext related.2.1 related.2.2.1, related.2.2.2.2.1⟩

/-- Replacing only the oracle worlds preserves the scheduler relation after recording overlaps. -/
theorem stateRelation_world (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (u v : WorldState C) (worlds : WorldRelation D s.2.selected u v) :
    StateRelation attempts k D ((s.1.1, u), recordWorld D s.2 u) (t.1, v) := by
  obtain ⟨life, _, _, _, _, started, empty, active, aux, _⟩ := related
  refine ⟨life, congrArg Prod.fst worlds.2.1, congrArg Prod.snd worlds.2.1,
    ?_, worlds.2.2, started, empty, active, aux, Finset.subset_union_right⟩
  exact fun x => congrFun worlds.1 x

/-- A request that leaves the slot state intact only records its resulting stream overlap. -/
theorem advanceGhost_world (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (q : (TailSpec C E).Domain) (notStart : ∀ tree, q ≠ .inl (.inr (.start tree)))
    (w : WorldState C) :
    advanceGhost attempts k D q s.1 (s.1.1, w) s.2 = recordWorld D s.2 w := by
  obtain ⟨_, _, _, _, _, _, _, active, aux, _⟩ := related
  have he : (let selected := if s.2.active then
      (s.1.1.2.map Prod.fst).getD s.2.selected else s.2.selected
      ; Ghost.mk s.2.active (s.2.started || s.2.active) selected
        (s.2.overlaps ∪ overlapNames D w.1 selected)) = recordWorld D s.2 w := by
    cases ha : s.2.active with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false]
      cases hg : s.2
      simp only [hg] at ha ⊢
      cases ha
      rfl
    | true =>
      have hs := active ha
      simp only [ha, ↓reduceIte] at aux
      simp only [↓reduceIte, aux.1, Option.map_some, Option.getD_some, hs, Bool.true_or]
      cases hg : s.2
      simp only [hg] at ha hs ⊢
      cases ha
      cases hs
      rfl
  rcases q with (q | q) | q
  · exact he
  · cases q <;> try exact he
    exact False.elim (notStart _ rfl)
  · exact he


section Finish
variable [Field E] [Algebra Bit E]

/-- The final test on the existing three-copy interface. -/
def finish3 (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party)
    (forgery : Forgery) (st : LifetimeState C E) :
    OracleComp (LifetimeKeygenPrograms.Spec3 C) Bool := do
  if ¬ ∀ i, i ∉ D.1 → (st.top i).isSome then pure false else do
  let some (_, top) := st.publicKey (keys h).parameter h | pure false
  let lift : ∀ {α : Type}, OracleComp (RoSpec C) α →
      OracleComp (LifetimeKeygenPrograms.Spec3 C) α :=
    fun p => LifetimeKeygenPrograms.freeCopy (liftComp p _)
  forgeryWins lift (dealtWith lift (keys h).parameter keys top
    (fun x => lift (prfValue (honestSeeds D keys) x))) st.sign forgery

omit [Field E] [Algebra Bit E] in
/-- The three-copy final program evaluates to the unchanged frozen final test. -/
theorem hom_finish3 (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party)
    (forgery : Forgery) (st : LifetimeState C E) :
    LifetimeKeygenPrograms.H3 D (finish3 D keys h forgery st) = finish D keys h forgery st := by
  have hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β),
      LifetimeKeygenPrograms.H3 D (LifetimeKeygenPrograms.freeCopy (liftComp oa _)) =
      (lifetimeHybridRoles D 0 0).honest (liftComp oa _) := fun oa =>
        LifetimeKeygenPrograms.impl3_freeCopy D _
  unfold finish3 finish
  split
  · exact MonadHom.mmap_pure _ _
  · cases hp : st.publicKey (keys h).parameter h with
    | none => exact MonadHom.mmap_pure _ _
    | some pair =>
      rcases pair with ⟨parameter, top⟩
      rw [LifetimeEmulatedBudget.hom_forgeryWins (LifetimeKeygenPrograms.H3 D),
        LifetimeEmulatedBudget.hom_dealtWith _ _ _ hlift _ _ _ _ _ (fun _ => hlift _)]
      simp only [hlift]

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

theorem rawKernel_finish (sep : Bool) (forgery : Forgery) (s : Physical C E) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inr forgery)).run s =
      (fun r => (r.1, (s.1, r.2))) <$>
        (evalEmulation prims (finish D keys h forgery s.1.1)).run s.2 := by
  change (evalSlot prims (StateT.mk fun (st : SlotState C E) =>
    (fun b => (b, st)) <$> finish D keys h forgery st.1)).run s = _
  simp only [evalSlot, StateT.run_mk, evalEmulation_map, StateT.run_map, Functor.map_map]

/-- The actual final win-test request satisfies the original scheduler coupling. -/
theorem finish_coupling (forgery : Forgery) (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inr forgery)).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inr forgery)).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  have coupled := localRun_coupling prims D (finish3 D keys h forgery s.1.1.1)
    s.2.selected s.1.2 t.2 (worldRelation_of_stateRelation attempts k D s t related)
  rw [localRun_eq, hom_finish3] at coupled
  unfold markedKernel
  simp only [StateT.run_mk, rawKernel_finish]
  rw [← related.1]
  erw [Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono coupled
  intro a b hab
  dsimp only [Function.comp_apply]
  rw [advanceGhost_world attempts k D s t related (.inr forgery) (by simp)]
  rcases hab with bad | ⟨equal, worlds⟩
  · exact Or.inl (bad.mono Finset.subset_union_right)
  · exact Or.inr ⟨equal, stateRelation_world attempts k D s t related a.2 b.2 worlds⟩

end Finish

/-- The relation only inspects the selected tree's run counter in the common lifetime state. -/
theorem stateRelation_life (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (life : LifetimeState C E)
    (counts : ∀ tree, LifetimeProof.runsAt life tree = LifetimeProof.runsAt s.1.1.1 tree) :
    StateRelation attempts k D (((life, s.1.1.2), s.1.2), s.2) ((life, t.1.2), t.2) := by
  obtain ⟨_, cache, log, merged, names, started, empty, active, aux, seen⟩ := related
  refine ⟨rfl, cache, log, merged, names, ?_, empty, active, aux, seen⟩
  change s.2.started = decide (_ < LifetimeProof.runsAt life _)
  rw [counts]
  exact started

/-- Actual local simulation outputs lie in the original all-answer program support. -/
theorem localRun_support (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LifetimeKeygenPrograms.Spec3 C) α) (s : WorldState C)
    (r : α × WorldState C) (hr : r ∈ support ((simulateQ (localKernel prims D) p).run s)) :
    r.1 ∈ support p := by
  apply support_simulateQ_run'_subset (localKernel prims D) p s
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ hr

-- `LifetimeEmulatedBudget.hom_signerDealt`, with its unused field hypotheses omitted.
theorem hom_signerDealt {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (φ : m →ᵐ n) (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (lift' : ∀ {β : Type}, OracleComp (RoSpec C) β → n β)
    (hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β), φ (lift oa) = lift' oa)
    (keys : C.Party → Keys C)
    (value : Point → m Digest) (value' : Point → n Digest) (hvalue : ∀ x, φ (value x) = value' x)
    (st : LifetimeState C E) (i : C.Party) :
    SeedHitProof.Dealt.hmap φ (ThresholdLeanXmss.signerDealt lift keys value st i) =
      ThresholdLeanXmss.signerDealt lift' keys value' st i := by
  simp only [SeedHitProof.Dealt.hmap, ThresholdLeanXmss.signerDealt, dealtWith, hlift, hvalue, MonadHom.mmap_pure]

section Requests
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

/-- Lift an actual common request program and its counter frame to the original marked kernel. -/
theorem kernel_of_program (q : (TailSpec C E).Domain)
    (notStart : ∀ tree, q ≠ .inl (.inr (.start tree)))
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (p : OracleComp (LifetimeKeygenPrograms.Spec3 C) ((TailSpec C E).Range q × LifetimeState C E))
    (left : (rawKernel K circuits settings attempts k D keys h prims true q).run s.1 =
      (fun r => (r.1.1, ((r.1.2, s.1.1.2), r.2))) <$>
        (simulateQ (localKernel prims D) p).run s.1.2)
    (right : (rawKernel K circuits settings attempts k D keys h prims false q).run t =
      (fun r => (r.1.1, ((r.1.2, t.1.2), r.2))) <$>
        (simulateQ (localKernel prims D) p).run t.2)
    (counts : ∀ r ∈ support p, ∀ tree,
      LifetimeProof.runsAt r.2 tree = LifetimeProof.runsAt s.1.1.1 tree) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims q).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false q).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  have coupled := relTriple_with_left_support
    (localRun_coupling prims D p s.2.selected s.1.2 t.2
      (worldRelation_of_stateRelation attempts k D s t related))
    (fun r hr => counts r.1 (localRun_support prims D p s.1.2 r hr))
  unfold markedKernel
  simp only [StateT.run_mk, left, right, Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono coupled
  intro a b hab
  have ghost : advanceGhost attempts k D q s.1 ((a.1.2, s.1.1.2), a.2) s.2 =
      recordWorld D s.2 a.2 :=
    advanceGhost_world attempts k D s t related q notStart a.2
  dsimp only [Function.comp_apply]
  rw [ghost]
  rcases hab.1 with bad | ⟨equal, worlds⟩
  · exact Or.inl (bad.mono Finset.subset_union_right)
  · refine Or.inr ⟨congrArg Prod.fst equal, ?_⟩
    rw [← congrArg Prod.snd equal]
    exact stateRelation_life attempts k D _ _
      (stateRelation_world attempts k D s t related a.2 b.2 worlds) a.1.2 hab.2

/-- Signing reuses the existing three-copy scheduler, including the per-signer dealt tree. -/
def signing3 (q : TsigQuery C) (st : LifetimeState C E) :
    OracleComp (LifetimeKeygenPrograms.Spec3 C) ((TsigSpec C).Range q × LifetimeState C E) :=
  (lifetimeOraclesWith K circuits settings attempts (fun _ => LifetimeKeygenPrograms.emulRoles3)
    LifetimeKeygenPrograms.baseRoles3 D keys
    (fun x => LifetimeKeygenPrograms.freeCopy (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.sign q)).run st

-- The signing cases of `LifetimeEmulatedBudget.hom_lifetimeOracles`, without the
-- finiteness assumptions used by that theorem's unrelated round branch.
theorem hom_signing3 (q : TsigQuery C) (st : LifetimeState C E) :
    LifetimeKeygenPrograms.H3 D (signing3 K circuits settings attempts D keys h q st) =
      (lifetimeOraclesWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D keys
        (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
        h (.sign q)).run st := by
  let φ := LifetimeKeygenPrograms.H3 D
  have hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β),
      φ (LifetimeKeygenPrograms.freeCopy (liftComp oa _)) =
      (lifetimeHybridRoles D 0 0).honest (liftComp oa _) := fun oa =>
        LifetimeKeygenPrograms.impl3_freeCopy D _
  have hsign : ∀ (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E),
      φ ((tsigOracles (m := OracleComp (LifetimeKeygenPrograms.Spec3 C)) (fun oa => LifetimeKeygenPrograms.freeCopy (liftComp oa _))
        (ThresholdLeanXmss.signerDealt (m := OracleComp (LifetimeKeygenPrograms.Spec3 C)) (fun oa => LifetimeKeygenPrograms.freeCopy (liftComp oa _))
          keys (fun x => LifetimeKeygenPrograms.freeCopy (liftComp (prfValue (honestSeeds D keys) x) _)) st i)
        q).run st.sign) =
      (tsigOracles (fun oa => (lifetimeHybridRoles D 0 0).honest (liftComp oa _))
        (ThresholdLeanXmss.signerDealt (fun oa => (lifetimeHybridRoles D 0 0).honest (liftComp oa _))
          keys (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
          st i) q).run st.sign := by
    intro i q st
    rw [SeedHitProof.hom_tsigOracles φ,
      hom_signerDealt φ _ _ hlift keys _ _ (fun _ => hlift _)]
    simp only [hlift]
  unfold signing3
  change φ _ = _
  cases q with
  | corrupt i => exact MonadHom.mmap_pure _ _
  | tree b =>
    simp only [lifetimeOraclesWith]
    refine (MonadHom.mmap_bind φ _ _).trans ?_
    erw [hsign]
    refine bind_congr fun r => ?_
    exact MonadHom.mmap_pure _ _
  | round1 i J e message =>
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, pure_bind, Bool.false_eq_true, if_false]
      exact MonadHom.mmap_pure φ _
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, if_true]
      refine (MonadHom.mmap_bind φ _ _).trans ?_
      erw [hsign]
      refine bind_congr fun r => ?_
      exact MonadHom.mmap_pure _ _
  | round2 i J e message parts =>
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, pure_bind, Bool.false_eq_true, if_false]
      exact MonadHom.mmap_pure φ _
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, if_true]
      refine (MonadHom.mmap_bind φ _ _).trans ?_
      erw [hsign]
      refine bind_congr fun r => ?_
      exact MonadHom.mmap_pure _ _

theorem rawKernel_sign (sep : Bool) (q : TsigQuery C) (s : Physical C E) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.sign q)))).run s =
      (fun r => (r.1.1, ((r.1.2, s.1.2), r.2))) <$>
        (simulateQ (localKernel prims D) (signing3 K circuits settings attempts D keys h q s.1.1)).run s.2 := by
  rw [localRun_eq, hom_signing3]
  change (evalSlot prims (StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$>
    (lifetimeOraclesWith K circuits settings attempts (fun _ => emulatedRoles D)
      (lifetimeHybridRoles D 0 0) D keys
      (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
      h (.sign q)).run st.1)).run s = _
  simp only [evalSlot, StateT.run_mk, evalEmulation_map, StateT.run_map, Functor.map_map]
  rfl

/-- Every actual signing request has the full scheduler coupling, including refused requests. -/
theorem signing_coupling (q : TsigQuery C) (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.sign q)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.sign q)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  apply kernel_of_program K circuits settings attempts D k keys h prims
    (.inl (.inr (.sign q))) (by simp) s t related
    (signing3 K circuits settings attempts D keys h q s.1.1.1)
  · exact rawKernel_sign K circuits settings attempts D k keys h prims true q s.1
  · rw [related.1]
    exact rawKernel_sign K circuits settings attempts D k keys h prims false q t
  · intro r hr tree
    have counts := LifetimeProof.lifetimeOracles_runs K circuits settings attempts
      (fun _ => LifetimeKeygenPrograms.emulRoles3) LifetimeKeygenPrograms.baseRoles3 D keys
      (fun x => LifetimeKeygenPrograms.freeCopy (liftComp (prfValue (honestSeeds D keys) x) _)) h
      (.sign q) s.1.1.1 r hr tree
    simpa only [LifetimeProof.newRun, reduceCtorEq, ↓reduceIte, Nat.add_zero] using counts

/-- The shared-round branch on the scheduler's existing local interface. -/
def round3 (sent : C.Party → C.Party → Option (Msg E)) (st : LifetimeState C E) :=
  (lifetimeOraclesWith K circuits settings attempts (fun _ => LifetimeKeygenPrograms.emulRoles3)
    LifetimeKeygenPrograms.baseRoles3 D keys
    (fun x => LifetimeKeygenPrograms.freeCopy (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.round sent)).run st

theorem hom_round3 (sent : C.Party → C.Party → Option (Msg E)) (st : LifetimeState C E) :
    LifetimeKeygenPrograms.H3 D (round3 K circuits settings attempts D keys h sent st) =
      (lifetimeOraclesWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D keys
        (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
        h (.round sent)).run st := by
  unfold round3
  cases hs : st.running with
  | none =>
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, hs, StateT.run_pure]
    exact MonadHom.mmap_pure _ _
  | some r =>
    rcases r with ⟨tree, fuel, steps⟩
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, hs,
      StateT.run_lift, StateT.run_set, StateT.run_pure, bind_assoc, MonadHom.mmap_bind,
      MonadHom.mmap_pure, hom_stepRound (LifetimeKeygenPrograms.H3 D) _ _
        (LifetimeKeygenPrograms.rolesHom_emul D)]

theorem rawKernel_round_none (sep : Bool) (sent : C.Party → C.Party → Option (Msg E))
    (s : Physical C E) (aux : s.1.2 = none) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.round sent)))).run s =
      (fun r => (r.1.1, ((r.1.2, s.1.2), r.2))) <$>
        (simulateQ (localKernel prims D) (round3 K circuits settings attempts D keys h sent s.1.1)).run s.2 := by
  rw [localRun_eq, hom_round3]
  change (evalSlot prims (slotOracles K circuits settings attempts (worldEnv D circuits settings)
    (worldMode attempts k sep) D keys
    (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.round sent))).run s = _
  unfold evalSlot
  simp only [StateT.run_mk, slotOracles, aux]
  cases hr : s.1.1.running <;>
    simp only [evalEmulation_map, StateT.run_map, Functor.map_map] <;> rfl

/-- When both schedulers use their shared table, the original round request couples. -/
theorem round_shared_coupling (sent : C.Party → C.Party → Option (Msg E))
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (leftAux : s.1.1.2 = none) (rightAux : t.1.2 = none) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.round sent)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.round sent)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  apply kernel_of_program K circuits settings attempts D k keys h prims
    (.inl (.inr (.round sent))) (by simp) s t related
    (round3 K circuits settings attempts D keys h sent s.1.1.1)
  · exact rawKernel_round_none K circuits settings attempts D k keys h prims true sent s.1 leftAux
  · rw [related.1]
    exact rawKernel_round_none K circuits settings attempts D k keys h prims false sent t rightAux
  · intro r hr tree
    have counts := LifetimeProof.lifetimeOracles_runs K circuits settings attempts
      (fun _ => LifetimeKeygenPrograms.emulRoles3) LifetimeKeygenPrograms.baseRoles3 D keys
      (fun x => LifetimeKeygenPrograms.freeCopy (liftComp (prfValue (honestSeeds D keys) x) _)) h
      (.round sent) s.1.1.1 r hr tree
    simpa only [LifetimeProof.newRun, reduceCtorEq, ↓reduceIte, Nat.add_zero] using counts

end Requests

/-- Settling a real or ideal run preserves every tree's run count. -/
theorem settle_runsAt (D : C.Coalition) (kind : Option (Option TreeOutput))
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) :
    LifetimeProof.runsAt (match kind with
      | none => st.settle D
      | some output => LifetimeSlots.settleIdeal D output st) tree = LifetimeProof.runsAt st tree := by
  cases kind <;> cases hr : st.running
  all_goals simp only [LifetimeState.settle, LifetimeSlots.settleIdeal, hr]
  all_goals split <;> try rfl
  all_goals split <;> cases tree <;> rfl

/-- Replacing a completed own-table round leaves the retained shared/selected relation intact. -/
theorem stateRelation_inactive (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (inactive : s.2.active = false) (life : LifetimeState C E)
    (aux : Option (StreamCache C × Option (Option TreeOutput))) (cache : HashCache C) (log : CallLog C)
    (counts : ∀ tree, LifetimeProof.runsAt life tree = LifetimeProof.runsAt s.1.1.1 tree) :
    StateRelation attempts k D (((life, aux), (s.1.2.1, cache, log)), s.2)
      ((life, aux), (t.2.1, cache, log)) := by
  obtain ⟨_, _, _, merged, names, started, empty, active, _, seen⟩ := related
  refine ⟨rfl, rfl, rfl, merged, names, ?_, empty, active, ?_, seen⟩
  · change s.2.started = decide (_ < LifetimeProof.runsAt life _)
    rw [counts]
    exact started
  · simp only [inactive, Bool.false_eq_true, ↓reduceIte]



/-- The state update at the end of a real or ideal own-table round. -/
def roundLife (D : C.Coalition) (kind : Option (Option TreeOutput))
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) : LifetimeState C E :=
  match kind with
  | none => LifetimeState.settle D { st with running := some (tree, fuel - 1, steps) }
  | some output => LifetimeSlots.settleIdeal D output { st with running := some (tree, fuel - 1, steps) }

theorem roundLife_counts (D : C.Coalition) (kind : Option (Option TreeOutput))
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) (other : ThresholdLeanXmss.Tree) :
    LifetimeProof.runsAt (roundLife D kind st tree fuel steps) other = LifetimeProof.runsAt st other := by
  unfold roundLife
  rw [settle_runsAt]
  cases other <;> rfl

/-- An inactive private-table round changes neither the retained table nor its overlap set. -/
theorem advanceGhost_round_inactive (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (inactive : s.2.active = false) (sent : C.Party → C.Party → Option (Msg E))
    (life : LifetimeState C E) (aux : Option (StreamCache C × Option (Option TreeOutput)))
    (cache : HashCache C) (log : CallLog C) :
    advanceGhost attempts k D (.inl (.inr (.round sent))) s.1
      ((life, aux), (s.1.2.1, cache, log)) s.2 = s.2 := by
  have seen := related.2.2.2.2.2.2.2.2.2
  simp only [advanceGhost, inactive, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
  rw [Finset.union_eq_left.mpr seen]
  cases hg : s.2
  simp only [hg] at inactive ⊢
  cases inactive
  rfl

section OwnRound
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

theorem rawKernel_round_own (sep : Bool) (sent : C.Party → C.Party → Option (Msg E))
    (s : Physical C E) (own : StreamCache C) (kind : Option (Option TreeOutput))
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.running = some (tree, fuel, steps)) (aux : s.1.2 = some (own, kind)) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.round sent)))).run s =
      (fun r => (some (toCoalition D r.1.2.1),
        ((roundLife D kind s.1.1 tree fuel r.1.2.1, some (r.2.1, kind)), (s.2.1, r.2.2)))) <$>
        (evalEmulation prims (stepRound (emulatedRoles D) D (roundAdversary (I := PEmpty) sent)
          noFunctionality () steps)).run (own, s.2.2) := by
  change (evalSlot prims (slotOracles K circuits settings attempts (worldEnv D circuits settings)
    (worldMode attempts k sep) D keys
    (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.round sent))).run s = _
  simp only [evalSlot, StateT.run_mk, slotOracles, running, aux]
  change (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (evalEmulation prims (do
      let r ← (stepRound (ownRoles D) D (roundAdversary (I := PEmpty) sent) noFunctionality () steps).run own
      pure (some (toCoalition D r.1.2.1),
        (roundLife D kind s.1.1 tree fuel r.1.2.1, some (r.2, kind))))).run s.2 = _
  rw [own_stepRound]
  simp only [bind_pure_comp, evalEmulation_map, StateT.run_map, evalEmulation_own, Functor.map_map]

/-- Identical inactive private tables couple exactly, even from arbitrary related scheduler states. -/
theorem round_own_coupling (sent : C.Party → C.Party → Option (Msg E))
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (inactive : s.2.active = false) (own : StreamCache C) (kind : Option (Option TreeOutput))
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.1.running = some (tree, fuel, steps)) (aux : s.1.1.2 = some (own, kind)) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.round sent)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.round sent)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  have equalAux := related.2.2.2.2.2.2.2.2.1
  simp only [inactive, Bool.false_eq_true, ↓reduceIte] at equalAux
  have targetRun : t.1.1.running = some (tree, fuel, steps) := related.1 ▸ running
  have targetAux : t.1.2 = some (own, kind) := equalAux ▸ aux
  unfold markedKernel
  simp only [StateT.run_mk]
  erw [rawKernel_round_own K circuits settings attempts D k keys h prims true sent s.1
    own kind tree fuel steps running aux,
    rawKernel_round_own K circuits settings attempts D k keys h prims false sent t
    own kind tree fuel steps targetRun targetAux, Functor.map_map]
  erw [Prod.ext related.2.1 related.2.2.1]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_refl _)
  intro a b hab
  change a = b at hab
  subst b
  dsimp only [Function.comp_apply]
  rw [advanceGhost_round_inactive attempts k D s t related inactive]
  refine Or.inr ⟨rfl, ?_⟩
  rw [← related.1]
  exact stateRelation_inactive attempts k D s t related inactive _ _ _ _
    (roundLife_counts D kind s.1.1.1 tree fuel a.1.2.1)

/-- An idle scheduler round is a pure refusal for every auxiliary-table state. -/
theorem rawKernel_round_idle (sep : Bool) (sent : C.Party → C.Party → Option (Msg E))
    (s : Physical C E) (idle : s.1.1.running = none) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.round sent)))).run s =
      pure (none, s) := by
  change (evalSlot prims (slotOracles K circuits settings attempts (worldEnv D circuits settings)
    (worldMode attempts k sep) D keys
    (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.round sent))).run s = _
  simp only [evalSlot, StateT.run_mk, slotOracles, idle, lifetimeOraclesWith,
    StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, map_pure,
    evalEmulation_pure]
  rfl

/-- Idle round refusals preserve the exact marked state. -/
theorem round_idle_coupling (sent : C.Party → C.Party → Option (Msg E))
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (idle : s.1.1.1.running = none) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.round sent)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.round sent)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  apply pure_coupling K circuits settings attempts D k keys h prims
    (q := .inl (.inr (.round sent))) s t related none
  · exact rawKernel_round_idle K circuits settings attempts D k keys h prims true sent s.1 idle
  · exact rawKernel_round_idle K circuits settings attempts D k keys h prims false sent t (related.1 ▸ idle)
  · exact advanceGhost_local attempts k D s t related (.inl 0) s.1.2.2.1 s.1.2.2.2

end OwnRound

/-- A selected-table round has the same coupling with the selected table retained on the other side
of the union. The clean premise permits changing the left-biased union order. -/
theorem stepRound_selected_coupling (prims : Primitives) (D : C.Coalition) {I α : Type}
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (selected : StreamCache C)
    (s t : WorldState C) (related : WorldRelation D selected s t)
    (clean : ¬ (overlapNames D s.1 selected).Nonempty) :
    RelTriple
      ((evalEmulation prims (stepRound (emulatedRoles D) D A noFunctionality state steps)).run (selected, s.2))
      ((evalEmulation prims (stepRound (emulatedRoles D) D A noFunctionality state steps)).run t)
      (fun a b => (overlapNames D s.1 a.2.1).Nonempty ∨
        (a.1 = b.1 ∧ WorldRelation D a.2.1 (s.1, a.2.2) b.2)) := by
  have reversed : WorldRelation D s.1 (selected, s.2) t :=
    ⟨related.1.trans (mergeStreams_comm_of_clean D s.1 selected related.2.2 clean),
      related.2.1, fun x hx => related.2.2 x hx.symm⟩
  apply relTriple_post_mono (stepRound_coupling prims D A state steps s.1 (selected, s.2) t reversed)
  intro a b hab
  by_cases bad : (overlapNames D s.1 a.2.1).Nonempty
  · exact Or.inl bad
  · rcases hab with bad' | ⟨equal, worlds⟩
    · exact False.elim (bad (by simpa only [overlapNames_comm D a.2.1 s.1] using bad'))
    · refine Or.inr ⟨equal, ?_, worlds.2.1, fun x hx => worlds.2.2 x hx.symm⟩
      exact worlds.1.trans (mergeStreams_comm_of_clean D a.2.1 s.1 worlds.2.2
        (by simpa only [overlapNames_comm D a.2.1 s.1] using bad))


/-- The selected table and the actual key-overlap event retained at the end of its round. -/
def selectedGhost (D : C.Coalition) (g : Ghost D) (shared selected : StreamCache C) : Ghost D :=
  ⟨true, true, selected, g.overlaps ∪ overlapNames D shared selected⟩

theorem advanceGhost_round_selected (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (active : s.2.active = true) (sent : C.Party → C.Party → Option (Msg E))
    (life : LifetimeState C E) (selected : StreamCache C) (w : WorldState C) :
    advanceGhost attempts k D (.inl (.inr (.round sent))) s.1
      ((life, some (selected, none)), w) s.2 = selectedGhost D s.2 w.1 selected := by
  simp only [advanceGhost, active, ↓reduceIte, Option.map_some, Option.getD_some, Bool.or_true]
  rfl

theorem stateRelation_selected (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (active : s.2.active = true) (life : LifetimeState C E) (selected : StreamCache C)
    (u v : WorldState C) (worlds : WorldRelation D selected u v)
    (counts : ∀ tree, LifetimeProof.runsAt life tree = LifetimeProof.runsAt s.1.1.1 tree) :
    StateRelation attempts k D (((life, some (selected, none)), u), selectedGhost D s.2 u.1 selected)
      ((life, none), v) := by
  have started := related.2.2.2.2.2.1
  have activeStarted := related.2.2.2.2.2.2.2.1 active
  refine ⟨rfl, congrArg Prod.fst worlds.2.1, congrArg Prod.snd worlds.2.1,
    (fun x => congrFun worlds.1 x), worlds.2.2, ?_, ?_, ?_, ?_, Finset.subset_union_right⟩
  · change true = decide (_ < LifetimeProof.runsAt life _)
    rw [counts, ← started, activeStarted]
  · intro impossible
    cases impossible
  · exact fun _ => rfl
  · exact ⟨rfl, rfl⟩

section SelectedRound
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

theorem rawKernel_round_shared (sep : Bool) (sent : C.Party → C.Party → Option (Msg E))
    (s : Physical C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.running = some (tree, fuel, steps)) (aux : s.1.2 = none) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.round sent)))).run s =
      (fun r => (some (toCoalition D r.1.2.1),
        ((roundLife D none s.1.1 tree fuel r.1.2.1, none), r.2))) <$>
        (evalEmulation prims (stepRound (emulatedRoles D) D (roundAdversary (I := PEmpty) sent)
          noFunctionality () steps)).run s.2 := by
  rw [rawKernel_round_none K circuits settings attempts D k keys h prims sep sent s aux,
    localRun_eq, hom_round3]
  simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, running,
    StateT.run_lift, StateT.run_set, StateT.run_pure, bind_assoc]
  simp only [bind_pure_comp, evalEmulation_map, StateT.run_map, Functor.map_map, aux]
  rfl

/-- A selected active round couples its own table to the shared union and records any created overlap. -/
theorem round_selected_coupling (sent : C.Party → C.Party → Option (Msg E))
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (clean : ¬ Bad D s) (active : s.2.active = true)
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.1.running = some (tree, fuel, steps)) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.round sent)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.round sent)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  have aux := related.2.2.2.2.2.2.2.2.1
  simp only [active, ↓reduceIte] at aux
  have noOverlap : ¬ (overlapNames D s.1.2.1 s.2.selected).Nonempty :=
    fun overlap => clean (overlap.mono related.2.2.2.2.2.2.2.2.2)
  have coupled := stepRound_selected_coupling prims D (roundAdversary (I := PEmpty) sent) () steps
    s.2.selected s.1.2 t.2 (worldRelation_of_stateRelation attempts k D s t related) noOverlap
  unfold markedKernel
  simp only [StateT.run_mk]
  erw [rawKernel_round_own K circuits settings attempts D k keys h prims true sent s.1
    s.2.selected none tree fuel steps running aux.1,
    rawKernel_round_shared K circuits settings attempts D k keys h prims false sent t
    tree fuel steps (related.1 ▸ running) aux.2, Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono coupled
  rintro ⟨a, u⟩ ⟨b, v⟩ hab
  dsimp only [Function.comp_apply, Prod.fst, Prod.snd] at hab ⊢
  rw [advanceGhost_round_selected attempts k D s active]
  rcases hab with bad | ⟨equal, worlds⟩
  · exact Or.inl (bad.mono Finset.subset_union_right)
  · cases equal
    refine Or.inr ⟨rfl, ?_⟩
    rw [← related.1]
    exact stateRelation_selected attempts k D s t related active _ u.1 _ _ worlds
      (roundLife_counts D none s.1.1.1 tree fuel a.2.1)

/-- Every round branch satisfies the exact marked scheduler kernel coupling. -/
theorem round_coupling (sent : C.Party → C.Party → Option (Msg E))
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (clean : ¬ Bad D s) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.round sent)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.round sent)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  cases running : s.1.1.1.running with
  | none => exact round_idle_coupling K circuits settings attempts D k keys h prims sent s t related running
  | some r =>
    rcases r with ⟨tree, fuel, steps⟩
    cases active : s.2.active with
    | true =>
      exact round_selected_coupling K circuits settings attempts D k keys h prims
        sent s t related clean active tree fuel steps running
    | false =>
      cases aux : s.1.1.2 with
      | none =>
        have targetAux := related.2.2.2.2.2.2.2.2.1
        simp only [active, Bool.false_eq_true, ↓reduceIte] at targetAux
        exact round_shared_coupling K circuits settings attempts D k keys h prims sent s t related
          aux (targetAux ▸ aux)
      | some r =>
        rcases r with ⟨own, kind⟩
        exact round_own_coupling K circuits settings attempts D k keys h prims sent s t related
          active own kind tree fuel steps running aux

end SelectedRound

/-- A world computation lifted through both persistent emulation layers. -/
def worldLift : OracleComp (WorldSpec C) →ᵐ EmulationM C where
  toFun _ p := StateT.lift (liftM p)
  toFun_pure' a := by
    apply StateT.ext
    intro cache
    apply LifetimeKeygenPrograms.writer_ext
    simp [StateT.run_lift]
  toFun_bind' p f := by
    apply StateT.ext
    intro cache
    apply LifetimeKeygenPrograms.writer_ext
    simp [StateT.run_lift, StateT.run_bind, liftM]

/-- The free honest interface as a monad map. -/
def freeHom : OracleComp (LocalSpec C) →ᵐ EmulationM C where
  toFun _ p := worldLift (free p)
  toFun_pure' a := by rw [free_pure, MonadHom.mmap_pure]
  toFun_bind' p f := by rw [free_bind, MonadHom.mmap_bind]

/-- An honest computation whose stream-table interpretation is its free-copy interpretation. -/
def Plain (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) : Prop :=
  (emulatedRoles D).honest p = freeHom p

theorem plain_pure (D : C.Coalition) {α : Type} (a : α) : Plain D (pure a) := by
  unfold Plain
  rw [MonadHom.mmap_pure]
  rfl

theorem plain_bind (D : C.Coalition) {α β : Type} (p : OracleComp (LocalSpec C) α)
    (f : α → OracleComp (LocalSpec C) β) (hp : Plain D p) (hf : ∀ a, Plain D (f a)) :
    Plain D (p >>= f) := by
  unfold Plain at *
  rw [MonadHom.mmap_bind]
  have hb : (emulatedRoles D).honest (p >>= f) =
      (emulatedRoles D).honest p >>= fun a => (emulatedRoles D).honest (f a) := by
    simp only [emulatedRoles, simulateQ_bind]
  rw [hb, hp]
  exact bind_congr hf

theorem plain_sample (D : C.Coalition) {α : Type} (p : ProbComp α) :
    Plain D (liftComp p (LocalSpec C)) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact plain_pure D a
  | query_bind t f ih =>
    rw [liftComp_bind]
    apply plain_bind D _ _ ?_ ih
    change (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl t))) = _
    exact LifetimePrfTransportProof.emul_honest_other D (.inl t) (by simp)

theorem plain_hash (D : C.Coalition) (q : Query C) :
    Plain D (liftComp (hashQuery q) (LocalSpec C)) := by
  change (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q)))) = _
  exact LifetimePrfTransportProof.emul_honest_other D (.inr (.inl q)) (by simp)

theorem plain_hashes (D : C.Coalition) {α : Type} (xs : List α) (f : α → Query C) :
    Plain D (liftComp (xs.mapM fun a => hashQuery (f a)) (LocalSpec C)) := by
  induction xs with
  | nil => exact plain_pure D []
  | cons a xs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure]
    exact plain_bind D _ _ (plain_hash D _) fun _ =>
      plain_bind D _ _ ih fun _ => plain_pure D _

-- The three prefix identities below port `prssSetup_eq_reveal_prefix`,
-- `advance_prssSetup_run` (Tree.lean) and `treeSim_startSetup` (TreeSim.lean),
-- omitting their unused field/finiteness section hypotheses.
theorem prssSetup_prefix (i : C.Party) :
    (prssSetup i : PartyM C E RealSpec (PrssKeys C)) = (do
      let own ← localStep (liftComp (sampleParts : ProbComp (Parts C)) _)
      let commitments ← oracleStep (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j)))
      let committed ← exchange fun j => if j = i then none else some (.hashes [commitments.getD j.val 0])
      let revealed ← exchange fun j => if j = i then none else some (.hashes (revealTo .prss own i j))
      prssPostReveal i own committed revealed) := by
  simp only [prssSetup, commitRevealEcho, prssPostReveal, prssOpenCheck, prssEchoFinish,
    bind_assoc, pure_bind, reduceCtorEq, ↓reduceIte, List.nil_append]

theorem advance_setup (i : C.Party) :
    advance (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run = (do
      let own ← liftComp (sampleParts : ProbComp (Parts C)) (LocalSpec C)
      let commitments ← liftComp (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)
      pure (prssCommitStep i own commitments)) := by
  rw [prssSetup_prefix, advance_localStep_bind]
  apply bind_congr
  intro own
  rw [advance_oracleStep_bind]
  apply bind_congr
  intro commitments
  exact advance_exchange_bind _ _

theorem startSetup_world (D : C.Coalition)
    (cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    startSteps worldRoles D (fun i => prssSetup i >>= cont i) =
      treeSimSetupSteps D cont <$> free (prssInitialData D) := by
  unfold startSteps prssInitialData
  rw [free_sequenceFin, map_eq_bind_pure_comp]
  change _ = Concrete.sequenceFin _ >>= fun rows => pure (treeSimSetupSteps D cont rows)
  unfold treeSimSetupSteps
  rw [← sequenceFin_bind_pure _ (fun i (row : Parts C × List HashOutput) =>
    if i ∈ D.1 then Step.done (E := E) (G := RealSpec) (α := TreeOutput) none
    else treeSimSetupStep (cont i) i row)]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [if_neg hi, worldRoles, advance_bind, advance_setup,
      bind_assoc, pure_bind, free_bind, free_pure, treeSimSetupStep,
      prssCommitStep, continueStep]

/-- Starting the actual PRSS setup reaches its first wait using only fresh coins and commitments. -/
theorem startSetup_plain (D : C.Coalition)
    (cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    startSteps (emulatedRoles D) D (fun i => prssSetup i >>= cont i) =
      worldLift (treeSimSetupSteps D cont <$> free (prssInitialData D)) := by
  rw [← startSetup_world]
  unfold startSteps
  rw [SeedHitProof.hom_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, MonadHom.mmap_pure]
  · simp only [if_neg hi]
    change Plain D (advance (prssSetup i >>= cont i).run)
    simp only [advance_bind, advance_setup, bind_assoc, pure_bind]
    apply plain_bind D _ _ (plain_sample D _) fun own => ?_
    apply plain_bind D _ _ (plain_hashes D _ _) fun commitments => ?_
    exact plain_pure D _

-- `LifetimeEmulatedBudget.hom_startSteps`, without its unused field hypotheses.
theorem hom_startSteps {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (φ : m →ᵐ n) {I α : Type} (Ro : Roles C m) (Ro' : Roles C n)
    (hR : LifetimeEmulatedBudget.RolesHom φ Ro Ro') (D : C.Coalition)
    (program : C.Party → PartyM C E (CallSpec I PEmpty) α) :
    φ (startSteps Ro D program) = startSteps Ro' D program := by
  unfold startSteps
  rw [SeedHitProof.hom_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi, hR.honest]

/-- The same first setup pass on a private table leaves that table unchanged. -/
theorem startSetup_own (D : C.Coalition)
    (cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) (own : StreamCache C) :
    (startSteps (ownRoles D) D (fun i => prssSetup i >>= cont i)).run own =
      worldLift ((fun steps => (steps, own)) <$>
        (treeSimSetupSteps D cont <$> free (prssInitialData D))) := by
  rw [← hom_startSteps ownHom _ _ (ownHom_roles D), startSetup_plain]
  apply StateT.ext
  intro shared
  apply LifetimeKeygenPrograms.writer_ext
  simp [ownHom, worldLift, StateT.run_lift, WriterT.run_map, WriterT.run_liftM]

/-- The own-table image of a lifted world computation preserves the own table. -/
theorem ownHom_worldLift {α : Type} (p : OracleComp (WorldSpec C) α) (own : StreamCache C) :
    (ownHom (worldLift p)).run own = worldLift ((fun a => (a, own)) <$> p) := by
  apply StateT.ext
  intro shared
  apply LifetimeKeygenPrograms.writer_ext
  simp [ownHom, worldLift, StateT.run_lift, WriterT.run_map, WriterT.run_liftM]

section StartPrograms
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The first pass of any actual ceremony variant is a lifted world computation. -/
theorem startSteps_ceremonyWith (D : C.Coalition)
    (gadgets : C.Party → Context C → ℕ → List Job → RunGadgets C E RealSpec)
    (keys : C.Party → Keys C) (top : C.Party → TopTree) (tree : ThresholdLeanXmss.Tree) :
    startSteps (emulatedRoles D) D (fun i => ceremonyWith K circuits settings (gadgets i) i (keys i) (top i) tree) =
      worldLift (startSteps worldRoles D (fun i =>
        ceremonyWith K circuits settings (gadgets i) i (keys i) (top i) tree)) := by
  unfold ceremonyWith
  rw [startSetup_plain, startSetup_world]

/-- The first pass on an own table leaves its precise initial table unchanged. -/
theorem startSteps_own_ceremonyWith (D : C.Coalition)
    (gadgets : C.Party → Context C → ℕ → List Job → RunGadgets C E RealSpec)
    (keys : C.Party → Keys C) (top : C.Party → TopTree) (tree : ThresholdLeanXmss.Tree)
    (own : StreamCache C) :
    (startSteps (ownRoles D) D (fun i => ceremonyWith K circuits settings (gadgets i) i (keys i) (top i) tree)).run own =
      worldLift ((fun steps => (steps, own)) <$> (startSteps worldRoles D (fun i =>
        ceremonyWith K circuits settings (gadgets i) i (keys i) (top i) tree))) := by
  rw [← hom_startSteps ownHom _ _ (ownHom_roles D), startSteps_ceremonyWith, ownHom_worldLift]

/-- The common initial computation of an admitted slot start. The real shared and own
modes have the same computation; the ideal mode retains the exact dealer and simulator programs. -/
def startCore (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party)
    (mode : RunMode) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) :
    OracleComp (WorldSpec C) ((C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) :=
  match mode with
  | .ideal => do
    let parameter := (keys h).parameter
    let top := (st.top h).getD emptyTop
    let (output, openings) ← free (liftComp
      (dealerCeremony circuits settings parameter (honestSeeds D keys) top tree) (LocalSpec C))
    let seeds := simSeeds D keys
    let steps ← startSteps worldRoles D fun i =>
      ceremonyWith K circuits settings
        (simGadgets K settings D openings ((worldEnv D circuits settings).clear parameter seeds tree)) i
        ⟨parameter, seeds, fun _ => 0⟩ top tree
    pure (steps, some output)
  | _ => do
    let steps ← startSteps worldRoles D fun i =>
      (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree : PartyM C E RealSpec TreeOutput)
    pure (steps, none)

end StartPrograms

/-- The admitted-start state update, preserving the real and ideal selective-abort behavior. -/
def startLife (D : C.Coalition) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (r : (C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) : LifetimeState C E :=
  match r.2 with
  | none => LifetimeState.settle D { countStart st tree with running := some (tree, fuel, r.1) }
  | some output => LifetimeSlots.settleIdeal D output { countStart st tree with running := some (tree, fuel, r.1) }

/-- Only the shared mode leaves the auxiliary own-table field absent. -/
def startAux (mode : RunMode) (kind : Option (Option TreeOutput)) :
    Option (StreamCache C × Option (Option TreeOutput)) :=
  match mode with
  | .shared => none
  | _ => some (∅, kind)

local instance : DecidableEq ThresholdLeanXmss.Tree := Classical.decEq _

theorem startLife_counts (D : C.Coalition) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (fuel : ℕ) (r : (C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput))
    (other : ThresholdLeanXmss.Tree) :
    LifetimeProof.runsAt (startLife D st tree fuel r) other =
      LifetimeProof.runsAt st other + if tree = other then 1 else 0 := by
  unfold startLife
  rw [settle_runsAt]
  change LifetimeProof.runsAt (LifetimeProof.increment st tree) other = _
  exact LifetimeProof.increment_runsAt st tree other

section StartKernel
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

-- `LifetimeProof.run_start`, for an arbitrary lawful scheduler monad.
theorem run_start {m : Type → Type} [Monad m] [LawfulMonad m]
    (Ro : ℕ → Roles C m) (base : Roles C m) (value : Point → m Digest)
    (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E) :
    (lifetimeOraclesWith K circuits settings attempts Ro base D keys value h (.start tree)).run st =
      if ¬ LifetimeProof.canStart attempts D st tree then pure (none, st) else (do
        let steps ← startSteps (Ro st.runCount) D fun i =>
          (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
            PartyM C E RealSpec TreeOutput)
        pure (some (toCoalition D steps),
          ({ countStart st tree with running := some (tree, ceremonyFuel circuits settings, steps) }).settle D)) := by
  cases tree <;>
    simp only [lifetimeOraclesWith, LifetimeProof.canStart, countStart, StateT.run_bind, StateT.run_get, pure_bind] <;>
    split <;>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc] <;> rfl

theorem slot_start_mode (sep : Bool) (tree : ThresholdLeanXmss.Tree) (s : SlotState C E)
    (can : LifetimeProof.canStart attempts D s.1 tree) (mode : RunMode)
    (modeEq : (startSlot attempts s.1 tree).map (worldMode attempts k sep) = some mode) :
    (slotOracles K circuits settings attempts (worldEnv D circuits settings)
      (worldMode attempts k sep) D keys
      (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
      h (.start tree)).run s =
    worldLift ((fun r => (some (toCoalition D r.1),
      (startLife D s.1 tree (ceremonyFuel circuits settings) r, startAux mode r.2))) <$>
        startCore K circuits settings D keys h mode s.1 tree) := by
  cases mode with
  | own =>
    simp only [slotOracles, StateT.run_mk, if_pos can, modeEq, worldEnv, ceremony]
    rw [startSteps_own_ceremonyWith]
    simp only [startCore, ceremony, map_bind, map_pure, SeedHitProof.hom_map,
      MonadHom.mmap_bind, MonadHom.mmap_pure, bind_map_left, startLife, startAux]
    rfl
  | shared =>
    simp only [slotOracles, StateT.run_mk, if_pos can, modeEq]
    have run := run_start K circuits settings attempts D keys h (fun _ => emulatedRoles D)
      (lifetimeHybridRoles D 0 0)
      (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
      tree s.1
    erw [run]
    rw [if_neg (not_not_intro can)]
    change (fun r => (r.1, (r.2, none))) <$> (do
      let steps ← startSteps (emulatedRoles D) D fun i =>
        (ceremony K circuits settings i (keys i) ((s.1.top i).getD emptyTop) tree : PartyM C E RealSpec TreeOutput)
      pure (some (toCoalition D steps),
        LifetimeState.settle D { countStart s.1 tree with running := some (tree, ceremonyFuel circuits settings, steps) })) = _
    simp only [ceremony, startSteps_ceremonyWith, startCore, startLife, startAux,
      map_bind, map_pure, MonadHom.mmap_bind, MonadHom.mmap_pure]
  | ideal =>
    simp only [slotOracles, StateT.run_mk, if_pos can, modeEq, worldEnv]
    change (do
      let r ← worldLift (free (liftComp (dealerCeremony circuits settings (keys h).parameter
        (honestSeeds D keys) ((s.1.top h).getD emptyTop) tree) (LocalSpec C)))
      let p ← (startSteps (ownRoles D) D fun i => ceremonyWith K circuits settings
        (simGadgets K settings D r.2 ((worldEnv D circuits settings).clear (keys h).parameter (simSeeds D keys) tree))
        i ⟨(keys h).parameter, simSeeds D keys, fun _ => 0⟩ ((s.1.top h).getD emptyTop) tree).run ∅
      pure (some (toCoalition D p.1), (startLife D s.1 tree (ceremonyFuel circuits settings) (p.1, some r.1),
        some (p.2, some r.1)))) = _
    simp only [startCore, map_bind, map_pure, MonadHom.mmap_bind,
      MonadHom.mmap_pure, startAux]
    apply bind_congr
    intro r
    rw [startSteps_own_ceremonyWith]
    simp only [SeedHitProof.hom_map, bind_map_left]

/-- An admitted start leaves the shared stream table and observation log unchanged. -/
theorem rawKernel_start_mode (sep : Bool) (tree : ThresholdLeanXmss.Tree) (s : Physical C E)
    (can : LifetimeProof.canStart attempts D s.1.1 tree) (mode : RunMode)
    (modeEq : (startSlot attempts s.1.1 tree).map (worldMode attempts k sep) = some mode) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.start tree)))).run s =
      (fun r => (some (toCoalition D r.1.1),
        ((startLife D s.1.1 tree (ceremonyFuel circuits settings) r.1, startAux mode r.1.2),
          (s.2.1, r.2, s.2.2.2)))) <$>
        (simulateQ (worldAnswer prims) (startCore K circuits settings D keys h mode s.1.1 tree)).run s.2.2.1 := by
  change (evalSlot prims (slotOracles K circuits settings attempts (worldEnv D circuits settings)
    (worldMode attempts k sep) D keys
    (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.start tree))).run s = _
  simp only [evalSlot, StateT.run_mk]
  rw [slot_start_mode K circuits settings attempts D k keys h sep tree s.1 can mode modeEq]
  dsimp only [worldLift]
  erw [evalEmulation_lift]
  erw [simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

end StartKernel

open LifetimeJointLink (Slot slotTree)

/-- A slot is determined by its tree and its attempt number. -/
theorem slot_ext {attempts : ℕ} (a b : Slot attempts)
    (tree : slotTree a = slotTree b) (index : slotAttempt a = slotAttempt b) : a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext index)
    | inr b => cases tree
  | inr a =>
    cases b with
    | inl b => cases tree
    | inr b =>
      exact congrArg Sum.inr (Prod.ext (ThresholdLeanXmss.Tree.bottom.inj tree) (Fin.ext index))

/-- An accepted start always has a concrete slot, with its literal current run counter. -/
theorem startSlot_exists (attempts : ℕ) (D : C.Coalition) (st : LifetimeState C E)
    (tree : ThresholdLeanXmss.Tree) (can : LifetimeProof.canStart attempts D st tree) :
    ∃ slot, startSlot attempts st tree = some slot := by
  cases tree with
  | top => exact ⟨.inl ⟨st.topRuns, can.2.1⟩, dif_pos can.2.1⟩
  | bottom b => exact ⟨.inr (b, ⟨st.bottomRuns b, can.2.1⟩), dif_pos can.2.1⟩

theorem startSlot_attempt (attempts : ℕ) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (slot : Slot attempts) (selected : startSlot attempts st tree = some slot) :
    slotAttempt slot = LifetimeProof.runsAt st tree := by
  cases tree <;> simp only [startSlot] at selected
  all_goals split at selected
  all_goals try contradiction
  all_goals cases selected; rfl

/-- Passing the selected counter occurs exactly on its unique slot start. -/
theorem started_after (attempts : ℕ) (selected current : Slot attempts)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (currentSlot : startSlot attempts st tree = some current) :
    decide (slotAttempt selected < LifetimeProof.runsAt st (slotTree selected) +
        if tree = slotTree selected then 1 else 0) =
      (decide (slotAttempt selected < LifetimeProof.runsAt st (slotTree selected)) ||
        decide (current = selected)) := by
  have currentTree : slotTree current = tree := startSlot_tree attempts st tree current currentSlot
  have currentIndex := startSlot_attempt attempts st tree current currentSlot
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  by_cases same : tree = slotTree selected
  · rw [if_pos same]
    have slotEq : current = selected ↔ slotAttempt selected = LifetimeProof.runsAt st (slotTree selected) := by
      constructor
      · intro equal
        simpa only [equal, same] using currentIndex
      · intro equal
        exact slot_ext current selected (currentTree.trans same) (by rw [currentIndex, same, equal])
    rw [slotEq]
    omega
  · rw [if_neg same, Nat.add_zero]
    have different : current ≠ selected := fun equal => same ((congrArg slotTree equal).symm.trans currentTree).symm
    simp only [different, or_false]

/-- The Boolean active marker is equality to the selected slot. -/
theorem selected_test (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (slot : Slot attempts) :
    decide (((slotOrder attempts) slot).val = k.val) = decide (slot = (slotOrder attempts).symm k) := by
  congr 1
  apply propext
  constructor
  · intro h
    exact (slotOrder attempts).injective ((Fin.ext h).trans ((slotOrder attempts).apply_symm_apply k).symm)
  · intro h
    subst slot
    simp

/-- Starting another slot stops using the selected table but retains its entire contents. -/
def inactiveGhost (D : C.Coalition) (g : Ghost D) : Ghost D := { g with active := false }

theorem advanceGhost_start_other (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (tree : ThresholdLeanXmss.Tree) (can : LifetimeProof.canStart attempts D s.1.1.1 tree)
    (slot : Slot attempts) (current : startSlot attempts s.1.1.1 tree = some slot)
    (other : slot ≠ (slotOrder attempts).symm k) (life : LifetimeState C E)
    (aux : Option (StreamCache C × Option (Option TreeOutput))) (cache : HashCache C) (log : CallLog C) :
    advanceGhost attempts k D (.inl (.inr (.start tree))) s.1
      ((life, aux), (s.1.2.1, cache, log)) s.2 = inactiveGhost D s.2 := by
  simp only [advanceGhost, if_pos can, current, Option.map_some, Option.some.injEq,
    selected_test, decide_eq_false other, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
  rw [Finset.union_eq_left.mpr related.2.2.2.2.2.2.2.2.2]
  rfl

theorem stateRelation_start_other (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (tree : ThresholdLeanXmss.Tree) (slot : Slot attempts)
    (current : startSlot attempts s.1.1.1 tree = some slot) (other : slot ≠ (slotOrder attempts).symm k)
    (fuel : ℕ) (r : (C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput))
    (aux : Option (StreamCache C × Option (Option TreeOutput))) (cache : HashCache C) (log : CallLog C) :
    StateRelation attempts k D
      (((startLife D s.1.1.1 tree fuel r, aux), (s.1.2.1, cache, log)), inactiveGhost D s.2)
      ((startLife D s.1.1.1 tree fuel r, aux), (t.2.1, cache, log)) := by
  obtain ⟨_, _, _, merged, names, started, empty, _, _, seen⟩ := related
  refine ⟨rfl, rfl, rfl, merged, names, ?_, empty, ?_, ?_, seen⟩
  · change s.2.started = decide (_ < LifetimeProof.runsAt (startLife D _ _ _ _) _)
    rw [startLife_counts, started_after attempts _ slot s.1.1.1 tree current,
      decide_eq_false other, Bool.or_false]
    exact started
  · intro impossible
    cases impossible
  · rfl

/-- Before starting the selected slot, its retained table is exactly empty. -/
theorem selected_empty_before (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (tree : ThresholdLeanXmss.Tree)
    (current : startSlot attempts s.1.1.1 tree = some ((slotOrder attempts).symm k)) :
    s.2.started = false ∧ s.2.selected = ∅ := by
  have ht := startSlot_tree attempts s.1.1.1 tree ((slotOrder attempts).symm k) current
  have hi := startSlot_attempt attempts s.1.1.1 tree ((slotOrder attempts).symm k) current
  have started := related.2.2.2.2.2.1
  rw [ht, hi] at started
  simp only [lt_self_iff_false, decide_false] at started
  exact ⟨started, related.2.2.2.2.2.2.1 started⟩

theorem advanceGhost_start_selected (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (tree : ThresholdLeanXmss.Tree)
    (can : LifetimeProof.canStart attempts D s.1.1.1 tree)
    (current : startSlot attempts s.1.1.1 tree = some ((slotOrder attempts).symm k))
    (life : LifetimeState C E) (w : WorldState C) :
    advanceGhost attempts k D (.inl (.inr (.start tree))) s.1
      ((life, some (∅, none)), w) s.2 = selectedGhost D s.2 w.1 ∅ := by
  simp only [advanceGhost, if_pos can, current, Option.map_some, Equiv.apply_symm_apply,
    decide_true, ↓reduceIte, Option.getD_some, Bool.or_true]
  rfl

theorem stateRelation_start_selected (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (tree : ThresholdLeanXmss.Tree)
    (current : startSlot attempts s.1.1.1 tree = some ((slotOrder attempts).symm k))
    (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput) (cache : HashCache C) (log : CallLog C) :
    StateRelation attempts k D
      (((startLife D s.1.1.1 tree fuel (steps, none), some (∅, none)), (s.1.2.1, cache, log)),
        selectedGhost D s.2 s.1.2.1 ∅)
      ((startLife D s.1.1.1 tree fuel (steps, none), none), (t.2.1, cache, log)) := by
  have empty := (selected_empty_before attempts k D s t related tree current).2
  have merged := related.2.2.2.1
  have names := related.2.2.2.2.1
  rw [empty] at merged names
  refine ⟨rfl, rfl, rfl, merged, names, ?_, ?_, ?_, ?_, Finset.subset_union_right⟩
  · change true = decide (_ < LifetimeProof.runsAt (startLife D _ _ _ _) _)
    rw [startLife_counts, started_after attempts _ _ s.1.1.1 tree current]
    simp only [decide_true, Bool.or_true]
  · intro impossible
    cases impossible
  · exact fun _ => rfl
  · exact ⟨rfl, rfl⟩

section Starts
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

theorem rawKernel_start_denied (sep : Bool) (tree : ThresholdLeanXmss.Tree) (s : Physical C E)
    (denied : ¬ LifetimeProof.canStart attempts D s.1.1 tree) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.start tree)))).run s =
      pure (none, s) := by
  change (evalSlot prims (slotOracles K circuits settings attempts (worldEnv D circuits settings)
    (worldMode attempts k sep) D keys
    (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
    h (.start tree))).run s = _
  simp only [evalSlot, StateT.run_mk, slotOracles, if_neg denied]
  have run := run_start K circuits settings attempts D keys h (fun _ => emulatedRoles D)
    (lifetimeHybridRoles D 0 0)
    (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
    tree s.1.1
  erw [run, if_pos denied]
  erw [map_pure]
  change pure (none, (s.1, (s.2.1, s.2.2.1, s.2.2.2 ++ []))) = pure (none, s)
  simp only [List.append_nil]

theorem start_denied_coupling (tree : ThresholdLeanXmss.Tree)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (denied : ¬ LifetimeProof.canStart attempts D s.1.1.1 tree) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.start tree)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.start tree)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  apply pure_coupling K circuits settings attempts D k keys h prims
    (q := .inl (.inr (.start tree))) s t related none
  · exact rawKernel_start_denied K circuits settings attempts D k keys h prims true tree s.1 denied
  · exact rawKernel_start_denied K circuits settings attempts D k keys h prims false tree t (related.1 ▸ denied)
  · simpa only [advanceGhost, if_neg denied, updateWorld] using
      advanceGhost_local attempts k D s t related (.inl 0) s.1.2.2.1 s.1.2.2.2

/-- Admitted starts of every other slot have identical complete initial computations. -/
theorem start_other_coupling (tree : ThresholdLeanXmss.Tree)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (can : LifetimeProof.canStart attempts D s.1.1.1 tree) (slot : Slot attempts)
    (current : startSlot attempts s.1.1.1 tree = some slot) (other : slot ≠ (slotOrder attempts).symm k) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.start tree)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.start tree)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  have indexNe : ((slotOrder attempts) slot).val ≠ k.val := by
    intro equal
    have same : decide (((slotOrder attempts) slot).val = k.val) = true := by simp [equal]
    rw [selected_test] at same
    exact other (of_decide_eq_true same)
  let mode := worldMode attempts k true slot
  have leftMode : (startSlot attempts s.1.1.1 tree).map (worldMode attempts k true) = some mode := by
    rw [current]
    rfl
  have rightMode : (startSlot attempts t.1.1 tree).map (worldMode attempts k false) = some mode := by
    rw [← related.1, current, Option.map_some, worldMode_eq_of_ne attempts k slot indexNe]
  unfold markedKernel
  simp only [StateT.run_mk]
  erw [rawKernel_start_mode K circuits settings attempts D k keys h prims true tree s.1 can mode leftMode,
    rawKernel_start_mode K circuits settings attempts D k keys h prims false tree t
      (related.1 ▸ can) mode rightMode, Functor.map_map]
  erw [related.1, related.2.1, related.2.2.1]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_refl _)
  intro a b hab
  change a = b at hab
  subst b
  dsimp only [Function.comp_apply]
  rw [advanceGhost_start_other attempts k D s t related tree can slot current other]
  refine Or.inr ⟨rfl, ?_⟩
  rw [← related.1]
  exact stateRelation_start_other attempts k D s t related tree slot current other _ _ _ _ _

/-- The real start has no ideal-output marker, for every evaluated output. -/
theorem startCore_own_kind (tree : ThresholdLeanXmss.Tree) (st : LifetimeState C E)
    (cache : HashCache C) (r)
    (hr : r ∈ support ((simulateQ (worldAnswer prims)
      (startCore K circuits settings D keys h .own st tree)).run cache)) : r.1.2 = none := by
  simp only [startCore, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨⟨steps, cache⟩, _, rfl⟩ := hr
  rfl

/-- Starting the selected slot uses an empty own table on the left and the unchanged shared table on the right. -/
theorem start_selected_coupling (tree : ThresholdLeanXmss.Tree)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (can : LifetimeProof.canStart attempts D s.1.1.1 tree)
    (current : startSlot attempts s.1.1.1 tree = some ((slotOrder attempts).symm k)) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.start tree)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.start tree)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  have leftMode : (startSlot attempts s.1.1.1 tree).map (worldMode attempts k true) = some .own := by
    simp [current, worldMode]
  have rightMode : (startSlot attempts t.1.1 tree).map (worldMode attempts k false) = some .shared := by
    rw [← related.1]
    simp [current, worldMode]
  have core : startCore K circuits settings D keys h .shared t.1.1 tree =
      startCore K circuits settings D keys h .own t.1.1 tree := rfl
  unfold markedKernel
  simp only [StateT.run_mk]
  erw [rawKernel_start_mode K circuits settings attempts D k keys h prims true tree s.1 can .own leftMode,
    rawKernel_start_mode K circuits settings attempts D k keys h prims false tree t
      (related.1 ▸ can) .shared rightMode, Functor.map_map]
  erw [related.1, related.2.1, related.2.2.1, core]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_left_support (relTriple_refl _)
    (startCore_own_kind K circuits settings D keys h prims tree t.1.1 t.2.2.1))
  rintro ⟨⟨steps, kind⟩, cache⟩ b ⟨equal, kindNone⟩
  change ((steps, kind), cache) = b at equal
  subst b
  change kind = none at kindNone
  subst kind
  dsimp only [Function.comp_apply, startAux]
  rw [advanceGhost_start_selected attempts k D s tree can current]
  refine Or.inr ⟨rfl, ?_⟩
  rw [← related.1]
  exact stateRelation_start_selected attempts k D s t related tree current _ steps _ _

/-- Every accepted or refused start satisfies the original scheduler coupling. -/
theorem start_coupling (tree : ThresholdLeanXmss.Tree)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.start tree)))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.start tree)))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  by_cases can : LifetimeProof.canStart attempts D s.1.1.1 tree
  · obtain ⟨slot, current⟩ := startSlot_exists attempts D s.1.1.1 tree can
    by_cases selected : slot = (slotOrder attempts).symm k
    · subst slot
      exact start_selected_coupling K circuits settings attempts D k keys h prims tree s t related can current
    · exact start_other_coupling K circuits settings attempts D k keys h prims tree s t related can slot current selected
  · exact start_denied_coupling K circuits settings attempts D k keys h prims tree s t related can

end Starts

section Scheduler
variable [Field E] [Algebra Bit E]

/-- The actual frozen scheduler kernels couple on every original related clean state. -/
theorem schedulerKernelCoupling (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (attempts : ℕ) (D : C.Coalition) (k : Fin (lifetimeRuns attempts)) :
    SchedulerKernelCoupling K circuits settings attempts D k := by
  intro prims keys h q _ s t related clean
  rcases q with (q | q) | forgery
  · exact local_coupling K circuits settings attempts D k keys h prims q s t related
  · cases q with
    | sign q => exact signing_coupling K circuits settings attempts D k keys h prims q s t related
    | publicKey => exact publicKey_coupling K circuits settings attempts D k keys h prims s t related
    | start tree => exact start_coupling K circuits settings attempts D k keys h prims tree s t related
    | round sent => exact round_coupling K circuits settings attempts D k keys h prims sent s t related clean
  · exact finish_coupling K circuits settings attempts D k keys h prims forgery s t related

end Scheduler

end ThresholdLeanXmssSecurity.LifetimeSlotCoupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.clean_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.clean_disjoint

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.streamDraw_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.streamDraw_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.localRun_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.localRun_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.finish_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.finish_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.signing_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.signing_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.round_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.round_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.start_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.start_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotCoupling.schedulerKernelCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSlotCoupling.schedulerKernelCoupling
