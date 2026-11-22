import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoBound

/-!
# The invariant of the shared key cells before the block of round 2

`CacheInv` holds at the empty start. A call keeps it unless it is a free call of `H` or a programming
call at a shared key cell of the seed generation (`compWorld_step_inv`). The prefix and the head of the
seed generation make no such call. So `PreInv` holds (`preInv`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map
  noCall_mono noCall_mapM noCall_sequenceFin noCall_query)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-- A free call of `H` at a shared key cell of the seed generation. -/
def FreeSk : (WorldSpec C).Domain → Prop := fun t => ∃ L, t = .inr (.inr (.inl (.sharedKeys .seedGen L)))

/-- A programming call at a shared key cell of the seed generation. -/
def ProgSk : (WorldSpec C).Domain → Prop := fun t => ∃ L v, t = .inl (.inr (.sharedKeys .seedGen L, v))

section Step

variable (prims : Primitives) (D : C.Coalition)

/-- The cache cell that a local call can write. -/
def localCell : (LocalSpec C).Domain → Option (Query C)
  | .inl _ => none
  | .inr (.inl q) => some q
  | .inr (.inr x) => some (.streamKey x.2.1)

theorem localAnswer_keep_other (t : (LocalSpec C).Domain) (c : HashCache C) (q' : Query C) (hq : localCell t ≠ some q') :
    ∀ z ∈ support ((localAnswer prims t).run c), z.2 q' = c q' := by
  intro z hz
  rcases t with n | q | x
  · rw [localAnswer_unif_run prims n c z hz]
  · exact hashAnswer_keep_other prims q q' (fun e => hq (by rw [e]; rfl)) c z hz
  · change z ∈ support ((prgAnswer prims x).run c) at hz
    simp only [prgAnswer, StateT.run_bind, support_bind, Set.mem_iUnion, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact hashAnswer_keep_other prims _ q' (fun e => hq (by rw [e]; rfl)) c r hr

theorem programAnswer_keep (p : Query C × HashOutput) (c : HashCache C) (q' : Query C) (hq : q' ≠ p.1) :
    ∀ z ∈ support ((programAnswer p).run c), z.2 q' = c q' := by
  intro z hz
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    exact QueryCache.cacheQuery_of_ne _ _ hq

theorem loggedWorld_keep_shared (t : (WorldSpec C).Domain) (h1 : ¬ ProgSk t) (h2 : ¬ FreeSk t) (s : LogState C)
    (L : List HashOutput) (hL : Query.sharedKeys .seedGen L ∉ countedCells t) :
    ∀ z ∈ support ((loggedWorld prims D t).run s), z.2.1.1 (.sharedKeys .seedGen L) = s.1.1 (.sharedKeys .seedGen L) := by
  intro z hz
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with ((n | q | x) | p) | (n | q | x)
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    exact localAnswer_keep_other prims (.inl n) _ _ (by simp [localCell]) r' hr'
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    refine localAnswer_keep_other prims (.inr (.inl q)) _ _ (fun e => hL ?_) r' hr'
    simp only [localCell, Option.some.injEq] at e
    simp [countedCells, e]
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    exact localAnswer_keep_other prims (.inr (.inr x)) _ _ (by simp [localCell]) r' hr'
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    refine programAnswer_keep p _ _ (fun e => h1 ⟨L, p.2, ?_⟩) r' hr'
    rw [e]
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    exact localAnswer_keep_other prims (.inl n) _ _ (by simp [localCell]) r' hr'
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    refine localAnswer_keep_other prims (.inr (.inl q)) _ _ (fun e => h2 ⟨L, ?_⟩) r' hr'
    simp only [localCell, Option.some.injEq] at e
    rw [e]
  · simp only [streamWorld] at hr
    split_ifs at hr
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', -, rfl⟩ := hr
      rfl
    · simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      exact localAnswer_keep_other prims (.inr (.inr x)) _ _ (by simp [localCell]) r' hr'

theorem loggedWorld_step_inv (t : (WorldSpec C).Domain) (h1 : ¬ ProgSk t) (h2 : ¬ FreeSk t) (s : LogState C)
    (hs : CacheInv s) : ∀ z ∈ support ((loggedWorld prims D t).run s), CacheInv z.2 := by
  intro z hz L hL
  have hlog := loggedWorld_log prims D t s z hz
  rw [hlog]
  by_cases hc : Query.sharedKeys .seedGen L ∈ countedCells t
  · exact List.mem_append_right _ hc
  · rw [loggedWorld_keep_shared prims D t h1 h2 s L hc z hz] at hL
    exact List.mem_append_left _ (hs L hL)

theorem compWorld_step_inv (parts : C.Party → Parts C) (seed : C.Term → HashOutput) (t : (WorldSpec C).Domain)
    (h1 : ¬ ProgSk t) (h2 : ¬ FreeSk t) (s : LogState C) (hs : CacheInv s) :
    ∀ z ∈ support ((compWorld prims D parts seed t).run s), CacheInv z.2 := by
  intro z hz
  unfold compWorld at hz
  split at hz
  · split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hs
    · exact loggedWorld_step_inv prims D _ h1 h2 s hs z hz
  · exact loggedWorld_step_inv prims D _ h1 h2 s hs z hz

theorem allQ_of_noCall {α : Type} {p : (WorldSpec C).Domain → Prop} {oa : OracleComp (WorldSpec C) α}
    (h : NoCall p oa) : AllQueriesSatisfy oa fun t => ¬ p t :=
  (isQueryBoundP_zero_iff _ _).1 ((isQueryBoundP_congr_pred fun _ => not_not).2 ((noCall_iff _ _).1 h))

theorem compWorld_run_inv (parts : C.Party → Parts C) (seed : C.Term → HashOutput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (h1 : NoCall ProgSk oa) (h2 : NoCall FreeSk oa) :
    ∀ s, CacheInv s → ∀ z ∈ support ((simulateQ (compWorld prims D parts seed) oa).run s), CacheInv z.2 := by
  have a1 := allQ_of_noCall h1
  have a2 := allQ_of_noCall h2
  clear h1 h2
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hs
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at a1 a2
    intro s hs z hz
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 (a1.2 p.1) (a2.2 p.1) p.2 (compWorld_step_inv prims D parts seed t a1.1 a2.1 s hs p hp) z hz

theorem loggedWorld_run_inv {α : Type} (oa : OracleComp (WorldSpec C) α) (h1 : NoCall ProgSk oa)
    (h2 : NoCall FreeSk oa) :
    ∀ s, CacheInv s → ∀ z ∈ support ((simulateQ (loggedWorld prims D) oa).run s), CacheInv z.2 := by
  have a1 := allQ_of_noCall h1
  have a2 := allQ_of_noCall h2
  clear h1 h2
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hs
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at a1 a2
    intro s hs z hz
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 (a1.2 p.1) (a2.2 p.1) p.2 (loggedWorld_step_inv prims D t a1.1 a2.1 s hs p hp) z hz

end Step

/-! ## The calls before the block -/

section Calls

open ThresholdLeanXmssSecurity.DkgCorrectnessProof.Collision (noProgram_adversary noProgram_free)

theorem noFreeSk_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) :
    NoCall FreeSk (worldRoles.adversary oa) := by
  rw [noCall_iff]
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, ThresholdLeanXmssSecurity.adversary_query]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by rintro ⟨L, h⟩; cases h), fun u => by simpa using ih u⟩

/-- A local call that is no call of `H` at a shared key cell of the seed generation. -/
def LocalNoSk (t : (LocalSpec C).Domain) : Prop := ∀ L, t ≠ .inr (.inl (.sharedKeys .seedGen L))

theorem noFreeSk_free {β : Type} (oa : OracleComp (LocalSpec C) β) (h : AllQueriesSatisfy oa LocalNoSk) :
    NoCall FreeSk (free oa) := by
  rw [noCall_iff]
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl ?_, fun u => by simpa using ih u (h.2 u)⟩
    rintro ⟨L, hL⟩
    cases hL
    exact h.1 L rfl

theorem localNoSk_liftComp_prob {β : Type} (p : ProbComp β) : AllQueriesSatisfy (liftComp p (LocalSpec C)) LocalNoSk := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure]; exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    rw [liftComp_bind]
    refine allQueriesSatisfy_bind ?_ fun a => ih a
    have e : liftComp (liftM (OracleSpec.query t) : ProbComp _) (LocalSpec C) =
        (liftM (OracleSpec.query (spec := LocalSpec C) (.inl t)) : OracleComp (LocalSpec C) _) := by
      simp
      rfl
    rw [e, allQueriesSatisfy_query_iff]
    intro L hL
    cases hL

theorem localNoSk_of_avoid {β : Type} (oa : OracleComp (LocalSpec C) β) (h : AllQueriesSatisfy oa (LocalAvoid SharedCell)) :
    AllQueriesSatisfy oa LocalNoSk :=
  h.mono fun t ht L hL => by
    subst hL
    exact ht ⟨L, rfl⟩

theorem noProgSk_of_noProgram {β : Type} {oa : OracleComp (WorldSpec C) β} (h : NoCall WorldProgramQuery oa) :
    NoCall ProgSk oa :=
  noCall_mono _ (fun t ⟨L, v, ht⟩ => by subst ht; trivial) h

theorem noFreeSk_observe {β : Type} (oa : OracleComp (LocalSpec C) β) : NoCall FreeSk (ThresholdLeanXmss.observe oa) := by
  unfold ThresholdLeanXmss.observe
  refine noCall_simulateQ_writer _ _ (fun t => ?_) oa
  rcases t with u | q | x
  · exact noCall_map _ _ (noFreeSk_adversary _)
  · dsimp only
    refine noCall_writer_bind _ _ _ (noCall_map _ _ (noFreeSk_adversary _)) fun y => ?_
    exact noCall_writer_bind _ _ _ (noCall_pure _ _) fun _ => noCall_pure _ _
  · exact noCall_map _ _ (noFreeSk_adversary _)

theorem noCall_program_derive (q : Query C) (v : HashOutput) (hq : ¬ SharedCell q) :
    NoCall FreeSk (program q v) ∧ NoCall ProgSk (program q v) := by
  have e : program q v = OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inr (q, v)))) := by
    unfold program counted
    rw [simulateQ_spec_query]
    rfl
  rw [e]
  refine ⟨noCall_query _ _ ?_, noCall_query _ _ ?_⟩
  · rintro ⟨L, h⟩
    cases h
  · rintro ⟨L, w, h⟩
    cases h
    exact hq ⟨L, rfl⟩

variable {E : Type} (D : C.Coalition)

theorem noCall_dealtPrefix [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (A : DkgTsigAdversary C E) :
    NoCall FreeSk (dealtPrefix D A) ∧ NoCall ProgSk (dealtPrefix D A) := by
  unfold dealtPrefix
  refine ⟨noCall_bind _ (noFreeSk_observe _) fun _ => noCall_bind _ (noFreeSk_free _ (localNoSk_liftComp_prob _))
    fun _ => noCall_bind _ (noFreeSk_free _ (localNoSk_liftComp_prob _)) fun _ => noCall_pure _ _,
    noProgSk_of_noProgram (noCall_bind _ (noProgram_observe _) fun _ => noCall_bind _ (noProgram_free _)
      fun _ => noCall_bind _ (noProgram_free _) fun _ => noCall_pure _ _)⟩

theorem noCall_commitDraws (parts : C.Party → Parts C) :
    NoCall FreeSk (commitDraws D parts) ∧ NoCall ProgSk (commitDraws D parts) := by
  unfold commitDraws
  refine ⟨noCall_sequenceFin _ _ fun i => ?_, noProgSk_of_noProgram (noCall_sequenceFin _ _ fun i => ?_)⟩
  · split_ifs
    · exact noCall_pure _ _
    · refine noFreeSk_free _ (localNoSk_of_avoid _ (avoid_liftComp _ _ (avoid_mapM _ _ (fun j => ?_) _)))
      exact avoid_hashQuery _ _ fun ⟨L, h⟩ => by simp [commitAddress] at h
  · split_ifs
    · exact noCall_pure _ _
    · exact noProgram_free _

theorem noCall_programBlock (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E)) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    NoCall FreeSk (programBlock D log sent parameter dealt parts) ∧
      NoCall ProgSk (programBlock D log sent parameter dealt parts) := by
  have hd : ∀ (k : KeyKind) (l : List HashOutput), ¬ SharedCell (C := C) (.derive .seedGen k l) :=
    fun _ _ ⟨L, h⟩ => by cases h
  unfold programBlock
  refine ⟨noCall_bind _ (noFreeSk_free _ (localNoSk_liftComp_prob _)) fun _ =>
      noCall_bind _ (noCall_program_derive _ _ (hd _ _)).1 fun _ =>
      noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
      noCall_bind _ (noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_) fun _ => noCall_pure _ _,
    noCall_bind _ (noProgSk_of_noProgram (noProgram_free _)) fun _ =>
      noCall_bind _ (noCall_program_derive _ _ (hd _ _)).2 fun _ =>
      noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
      noCall_bind _ (noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_) fun _ => noCall_pure _ _⟩
  · split
    · exact (noCall_program_derive _ _ (hd _ _)).1
    · exact noCall_pure _ _
  · split_ifs
    · exact (noCall_program_derive _ _ (hd _ _)).1
    · exact noCall_pure _ _
  · split
    · exact (noCall_program_derive _ _ (hd _ _)).2
    · exact noCall_pure _ _
  · split_ifs
    · exact (noCall_program_derive _ _ (hd _ _)).2
    · exact noCall_pure _ _

theorem noCall_seedHead (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    NoCall FreeSk (seedHead D net state early parameter dealt parts) ∧
      NoCall ProgSk (seedHead D net state early parameter dealt parts) := by
  unfold seedHead
  refine ⟨noCall_bind _ (noCall_commitDraws D parts).1 fun _ => noCall_bind _ (noFreeSk_observe _) fun _ =>
      noCall_bind _ (noCall_programBlock D _ _ _ _ _).1 fun _ => ?_,
    noCall_bind _ (noCall_commitDraws D parts).2 fun _ => noCall_bind _ (noProgSk_of_noProgram (noProgram_observe _))
      fun _ => noCall_bind _ (noCall_programBlock D _ _ _ _ _).2 fun _ => ?_⟩
  · split_ifs <;> first
      | exact noCall_pure _ _
      | exact noCall_bind _ (noFreeSk_adversary _) fun _ => noCall_pure _ _
  · split_ifs <;> first
      | exact noCall_pure _ _
      | exact noCall_bind _ (noProgSk_of_noProgram (noProgram_adversary _)) fun _ => noCall_pure _ _

end Calls

/-! ## `PreInv` -/

section Inv

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives)

/-- The state at the end of the head of `preRun` has `CacheInv`. -/
theorem preInv : PreInv (C := C) (E := E) prims := by
  intro D A z hz
  simp only [headRun, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨x, hx, seed, -, e, he, rfl⟩ := hz
  have h0 : CacheInv (C := C) ((∅, ∅), []) := fun L hL => absurd rfl hL
  have hx' := loggedWorld_run_inv prims D _ (noCall_dealtPrefix D A).2 (noCall_dealtPrefix D A).1 _ h0 x hx
  exact compWorld_run_inv prims D _ _ _ (noCall_seedHead D _ _ _ _ _ _).2 (noCall_seedHead D _ _ _ _ _ _).1 _ hx' e he

end Inv

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.preInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.preInv
