import ThresholdLeanXmssSecurity.Proof.SeedGenFinish
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The known half of the setup security

This module reduces `SetupKnownMismatch`, the known-half hypothesis of `setupSecurityDistance_of_known`.

1. `setupKnownGame` is the common game in normal form, with its transcript
   (`simulateQ_setupCommonGame_known`).
2. A mismatch is a failed programming, a missed extraction or an echo collision
   (`setupKnown_bad_of_mismatch`). Without them, every exposed coordinate of an accepted output is
   the dealer's value.
3. A missed extraction or an echo collision is a collision of two compared cells or a fresh opening
   (`setupKnown_cacheEvent_of_bad`). The compared cells are the shared-key hashes and the
   commitments of a corrupt sender.
4. At most `q + n²` calls sample a compared cell. The birthday bound gives `(q + n²)² / 2^257`
   (`setupComparedCollisionBound_proof`), and each fresh opening costs `2^-256`
   (`setupFreshOpeningBound_proof`).
5. A failed programming means that a programming input of `setupKnownPrefix` is a logged query,
   or that two programming inputs are equal (`setupProgramFailBound_of_alias`).
6. The total fits in half of `setupHashError` (`setupKnown_arith`).

`SetupProgramAliasBound` is a hypothesis of `setupSecurityDistance_of_programAlias`. It
needs the hiding of the honest parts by the commitments before the programming (CDG+18).

* The prefix agrees with a prefix whose honest commitments are fresh uncached values, unless a logged
  query is an honest commitment input.
* In that prefix the transcript does not read the parts. Each logged query then costs at most
  `K / 2^256`, and each pair of inputs costs at most `2^-256`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Overlay

variable {C : Committee}

/-- The hybrid dealing agrees with the dealer on every exposed coordinate, so the overlay of the
dealer's hidden coordinates gives the dealer's keys. -/
theorem setupHiddenOverlay_hybrid (phase : Phase) (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (i : C.Party) (hi : i ∉ D.1) :
    seedGenHiddenOverlay D i (dealtKeys parameter (setupHybridSeeds phase D h parts seeds)
      (setupHybridPairs phase D h parts pairs) i) (dealtKeys parameter seeds pairs i) =
      dealtKeys parameter seeds pairs i := by
  unfold seedGenHiddenOverlay dealtKeys setupHybridSeeds setupHybridPairs
  congr 1
  · funext T
    split_ifs <;> simp_all
  · funext j
    by_cases hj : j = i
    · simp [hj]
    · simp only [dite_eq_right hj]
      split_ifs with h1 h2
      · exfalso
        rcases h1 with h1 | h1
        · exact hi h1
        · unfold Committee.pairOf at h2
          split_ifs at h2 <;> simp_all
      · rfl
      · rfl

end Overlay

section Trace

variable {C : Committee} {E : Type}

/-- The simulator's programming block on the dealt keys, with the conjunction of its results. -/
def setupProgramOk (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) : OracleComp (WorldSpec C) Bool := do
  let view := setupProgramView phase D parts log sent
  let b ← programParameter phase (.derive phase .parameter
    (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter))
    (seedGenFullParameter high parameter)
  let bs ← (seedGenKnownCoordinates D).mapM fun T => program (setupTermProgrammingInput phase D view T) (seeds T)
  let cs ← (seedGenCrossCoordinates D).mapM fun p => program (setupPairProgrammingInput phase D view p) (pairs p)
  pure (b && bs.all id && cs.all id)

/-- The last two rounds, with the corrupt reveals and the honest echo data. -/
def setupPostTraced (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Mail C E) × (C.Party → Option (SeedGenEchoData C)) ×
      (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ D.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true then
    pure (state, fun _ _ => none, fun _ => none, fun _ => none)
  else do
    let (st, sent) ← A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (setupRevealSteps phase D parts committed i).outbox c else none
    let data ← setupRevealComputations phase D parts committed sent
    let r ← setupFinishLocal phase D A st data
    pure (r.1, sent, data, r.2)

theorem setupPostTraced_proj (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    (fun r => (r.1, r.2.2.2)) <$> setupPostTraced (phase := phase) D A state parts committed =
      setupPostCommitLocal phase D A state parts committed := by
  unfold setupPostTraced setupPostCommitLocal
  split_ifs
  · simp
  · simp only [map_bind, map_pure]
    refine bind_congr fun r => bind_congr fun data => ?_
    simp

/-- The transcript of the simulator's run that the bad events read. -/
structure SeedGenKnownTrace (C : Committee) (E σ : Type) where
  parameter : PublicParameter
  seeds : C.Term → HashOutput
  pairs : C.Pair → HashOutput
  parts : C.Party → Parts C
  log : CallLog C
  sent : C.Party → Mail C E
  commitments : C.Party → List HashOutput
  ok : Bool
  state : σ
  revealSent : C.Party → Mail C E
  data : C.Party → Option (SeedGenEchoData C)
  outputs : C.Party → Option (Keys C)

/-- The common game in normal form, with its transcript. -/
def setupKnownGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    OracleComp (WorldSpec C) (SeedGenKnownTrace C E A.State) := do
  let (state, log) ← observe (A.start (corruptInputs D x) z)
  let (parameter, seeds, pairs) ← free (liftComp (setupDealerSamples phase (C := C)) (LocalSpec C))
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C)))
    (LocalSpec C))
  let commitments ← free (setupInitialCommitments phase D parts)
  let ((st, sent), calls) ← observe (A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    commitOutbox i (commitments i) c else none)
  let high ← free (liftComp (setupHighSample phase) (LocalSpec C))
  let ok ← setupProgramOk (phase := phase) D parts (log ++ calls) sent parameter seeds pairs high
  let r ← free (setupPostTraced (phase := phase) D A st parts (setupCommitInbox phase D parts commitments sent))
  pure ⟨parameter, seeds, pairs, parts, log ++ calls, sent, commitments, ok, r.1, r.2.1, r.2.2.1, r.2.2.2⟩

/-- The output of the common game. -/
def SeedGenKnownTrace.result {σ : Type} (r : SeedGenKnownTrace C E σ) :
    σ × (C.Party → Option (Keys C)) × (C.Party → Keys C) :=
  (r.state, r.outputs, dealtKeys r.parameter r.seeds r.pairs)

/-- A programming attempt fails. -/
def SeedGenProgramFail {σ : Type} (r : SeedGenKnownTrace C E σ) : Prop := r.ok = false

/-- An honest operator that reaches the echo has a corrupt opening that the extraction misses. -/
def SetupExtractFail (phase : Phase) (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ) : Prop :=
  ∃ i, i ∉ D.1 ∧ (r.data i).isSome ∧ ∃ j, j ∈ D.1 ∧
    extractReveal phase r.log r.sent j i ≠
      Msg.hashesOf (setupRevealInbox phase D r.parts (setupCommitInbox phase D r.parts r.commitments r.sent) r.revealSent i j)

/-- Two honest operators that reach the echo send equal shared-key hashes of distinct inputs. -/
def SetupEchoCollision (phase : Phase) (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ) : Prop :=
  ∃ i j ki si kj sj, i ∉ D.1 ∧ j ∉ D.1 ∧ r.data i = some (ki, si) ∧ r.data j = some (kj, sj) ∧
    si.getD j.val 0 = sj.getD i.val 0 ∧
    Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) ≠
      Query.sharedKeys phase ((sharedTerms j i).map kj.2.1)

end Trace

section Expand

variable {C : Committee} {E : Type} (prims : Primitives)

theorem seedGenKnown_simulateQ_bind_left {α β : Type} {a b : OracleComp (WorldSpec C) α}
    (h : simulateQ (worldAnswer prims) a = simulateQ (worldAnswer prims) b) (k : α → OracleComp (WorldSpec C) β) :
    simulateQ (worldAnswer prims) (a >>= k) = simulateQ (worldAnswer prims) (b >>= k) := by
  rw [simulateQ_bind, simulateQ_bind, h]

theorem seedGenKnown_simulateQ_bind_right {α β : Type} {a : OracleComp (WorldSpec C) α}
    {k l : α → OracleComp (WorldSpec C) β}
    (h : ∀ x, simulateQ (worldAnswer prims) (k x) = simulateQ (worldAnswer prims) (l x)) :
    simulateQ (worldAnswer prims) (a >>= k) = simulateQ (worldAnswer prims) (a >>= l) := by
  rw [simulateQ_bind, simulateQ_bind]
  exact bind_congr h

theorem simulateQ_world_startSteps_setup (phase : Phase) (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) :
    simulateQ (worldAnswer prims)
        (startSteps worldRoles D fun i => (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C))) =
      simulateQ (worldAnswer prims) (setupInitialSteps phase D parts <$> free (setupInitialCommitments phase D parts)) := by
  rw [simulateQ_startSteps_real, seedGenMapRoles_world, ← simulateQ_startSteps_real, startSteps_setupWith,
    simulateQ_map, simulateQ_map, simulateQ_free]

theorem simulateQ_world_post_setup (phase : Phase) (prims : Primitives) {β : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (f : A.State × (C.Party → Option (Keys C)) → β) :
    simulateQ (worldAnswer prims)
        ((executeRounds observedRoles D A noFunctionality (setupRounds - 1) state
          (setupRevealSteps phase D parts committed)).run >>= fun r => pure (f r.1)) =
      simulateQ (worldAnswer prims)
        (free (setupPostTraced (phase := phase) D A state parts committed) >>= fun r => pure (f (r.1, r.2.2.2))) := by
  have hl : ((executeRounds observedRoles D A noFunctionality (setupRounds - 1) state
      (setupRevealSteps phase D parts committed)).run >>= fun r => pure (f r.1)) =
      seedGenEraseLog (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state
        (setupRevealSteps phase D parts committed)) >>= fun r => pure (f r) := by
    simp [seedGenEraseLog]
  rw [hl, seedGenEraseLog_executeRounds, simulateQ_bind, simulateQ_world_executeRounds, simulateQ_bind,
    simulateQ_free]
  change simulateQ (localAnswer prims) (executeRounds localRoles D A noFunctionality 2 state
    (setupRevealSteps phase D parts committed)) >>= _ = _
  rw [executeRounds_setupRevealSteps_two, ← setupPostTraced_proj, simulateQ_map, bind_map_left]

theorem simulateQ_setupCommonGame_known (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    simulateQ (worldAnswer prims) (setupCommonGame phase D A x z) =
      simulateQ (worldAnswer prims) (SeedGenKnownTrace.result <$> setupKnownGame (phase := phase) D A x z) := by
  unfold setupCommonGame setupEmulation setupKnownGame setupDealerSamples setupSimulatorStart
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure]
  refine seedGenKnown_simulateQ_bind_right prims fun a => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun parameter => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun seeds => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun pairs => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun parts => ?_
  rw [seedGenKnown_simulateQ_bind_left prims (simulateQ_world_startSteps_setup (phase := phase) prims D parts), bind_map_left]
  refine seedGenKnown_simulateQ_bind_right prims fun commitments => ?_
  rw [stepRound_setupInitialSteps_observed]
  simp only [observedRoles, WriterT.run_bind, WriterT.run_pure, map_pure, pure_bind, bind_assoc,
    show (∅ : CallLog C) = [] from rfl, List.append_nil, WriterT.run_mk]
  refine seedGenKnown_simulateQ_bind_right prims fun r => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun high => ?_
  rw [setupProgramBlock_dealt]
  simp only [setupProgramOk, bind_assoc, pure_bind]
  refine seedGenKnown_simulateQ_bind_right prims fun b => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun bs => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun cs => ?_
  exact simulateQ_world_post_setup (phase := phase) prims D A r.1.1 parts _ fun p => (p.1, p.2, dealtKeys parameter seeds pairs)

end Expand

section Support

variable {C : Committee} {E : Type} (prims : Primitives)

theorem seedGenProgramAnswer_support (x : Query C × HashOutput) (s : HashCache C) (z : Bool × HashCache C)
    (hz : z ∈ support ((programAnswer x).run s)) :
    (NoMpc s → NoMpc z.2) ∧ (z.1 = true → z.2 x.1 = some x.2) := by
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨id, fun h => by cases h⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨fun hn y hy => ?_, fun _ => by simp⟩
    have hne : Query.hash y ≠ x.1 := fun he => h (Or.inl ⟨y, he.symm, hy⟩)
    simp [QueryCache.cacheQuery_of_ne _ _ hne, hn y hy]

theorem seedGenWorldAnswer_noMpc (t : (WorldSpec C).Domain) (s : HashCache C)
    (z : (WorldSpec C).Range t × HashCache C) (hz : z ∈ support ((worldAnswer prims t).run s)) :
    NoMpc s → NoMpc z.2 := by
  rcases t with (t | t) | t
  · exact (localAnswer_support (prims := prims) (fun _ => 0) t s z hz).2.1
  · exact (seedGenProgramAnswer_support t s z hz).1
  · exact (localAnswer_support (prims := prims) (fun _ => 0) t s z hz).2.1

theorem seedGenWorldRun_noMpc {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) oa).run s) → NoMpc s → NoMpc z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact id
  | query_bind t k ih =>
    intro s z hz hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 p.2 z hz (seedGenWorldAnswer_noMpc prims t s p hp hs)

/-- Successful programming attempts of a list leave their values in the cache. -/
theorem seedGenPrograms_mapM_support {ι : Type} (l : List ι) (q : ι → Query C) (v : ι → HashOutput) :
    ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) (l.mapM fun i => program (q i) (v i))).run s) →
      z.1.all id = true → ∀ i ∈ l, z.2 (q i) = some (v i) := by
  induction l with
  | nil => intro s z _ _ i hi; cases hi
  | cons a l ih =>
    intro s z hz hall i hi
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind,
      Set.mem_iUnion, simulateQ_world_program] at hz
    obtain ⟨p, hp, p', hp', hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [List.all_cons, Bool.and_eq_true, id] at hall
    rcases List.mem_cons.mp hi with rfl | hi
    · exact grows_worldAnswer prims |>.simulateQ _ p.2 p' hp' |> fun hle =>
        hle ((seedGenProgramAnswer_support _ s p hp).2 hall.1)
    · exact ih p.2 p' hp' hall.2 i hi


/-- A successful programming block leaves every programmed value in the cache. -/
theorem setupProgramOk_support (phase : Phase) (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) (s : HashCache C) (z : Bool × HashCache C)
    (hz : z ∈ support ((simulateQ (worldAnswer prims)
      (setupProgramOk (phase := phase) D parts log sent parameter seeds pairs high)).run s)) (hok : z.1 = true) :
    let view := setupProgramView phase D parts log sent
    (∀ q ∈ setupParameterInputs phase D view, z.2 q = some (seedGenFullParameter high parameter)) ∧
      (∀ T ∈ seedGenKnownCoordinates D, z.2 (setupTermProgrammingInput phase D view T) = some (seeds T)) ∧
      (∀ p ∈ seedGenCrossCoordinates D, z.2 (setupPairProgrammingInput phase D view p) = some (pairs p)) := by
  cases phase
  · intro view
    unfold setupProgramOk at hz
    simp only [programParameter, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion,
      simulateQ_world_program, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩ := hz
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨hb, hbs⟩, hcs⟩ := hok
    have g₂ := grows_worldAnswer prims |>.simulateQ _ p₁.2 p₂ hp₂
    have g₃ := grows_worldAnswer prims |>.simulateQ _ p₂.2 p₃ hp₃
    refine ⟨fun q hq => ?_, fun T hT => g₃ ?_, fun p hp => ?_⟩
    · simp only [setupParameterInputs, ite_true, List.mem_singleton] at hq
      rw [hq]
      exact g₃ (g₂ ((seedGenProgramAnswer_support _ s p₁ hp₁).2 hb))
    · exact seedGenPrograms_mapM_support prims _ _ _ p₁.2 p₂ hp₂ hbs T hT
    · exact seedGenPrograms_mapM_support prims _ _ _ p₂.2 p₃ hp₃ hcs p hp
  · intro view
    unfold setupProgramOk at hz
    simp only [programParameter, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind,
      Set.mem_iUnion, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p₂, hp₂, p₃, hp₃, rfl⟩ := hz
    simp only [Bool.true_and, Bool.and_eq_true] at hok
    obtain ⟨hbs, hcs⟩ := hok
    have g₃ := grows_worldAnswer prims |>.simulateQ _ p₂.2 p₃ hp₃
    refine ⟨fun q hq => by simp [setupParameterInputs] at hq, fun T hT => g₃ ?_, fun p hp => ?_⟩
    · exact seedGenPrograms_mapM_support prims _ _ _ s p₂ hp₂ hbs T hT
    · exact seedGenPrograms_mapM_support prims _ _ _ p₂.2 p₃ hp₃ hcs p hp


/-- Every observed answer of a random-oracle input stays in the cache. -/
theorem seedGenObserve_log_cached {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) (observe oa)).run s) →
      ∀ q y, (q, y) ∈ z.1.2 → ¬ IsFixed q → z.2 q = some y := by
  unfold observe
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz q y hq
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    cases hq
  | query_bind t k ih =>
    intro s z hz q y hq hfix
    simp only [simulateQ_bind, WriterT.run_bind, StateT.run_bind, support_bind, Set.mem_iUnion,
      simulateQ_map, StateT.run_map, support_map, Set.mem_image, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map] at hz
    obtain ⟨p, hp, w, hw, rfl⟩ := hz
    rcases List.mem_append.mp hq with hq | hq
    · have hle := grows_worldAnswer prims |>.simulateQ _ p.2 w hw
      rcases t with t | (q' | x)
      · simp at hp
        obtain ⟨a, b, _, rfl⟩ := hp
        cases hq
      · simp [simulateQ_world_adversary] at hp
        obtain ⟨a, b, hp', rfl⟩ := hp
        simp only [List.mem_singleton, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have he : (simulateQ (localAnswer prims) (liftM (hashQuery q) : OracleComp (LocalSpec C) _)).run s =
            (hashAnswer prims q).run s := by
          exact congrArg (fun m => StateT.run m s) (simulateQ_localAnswer_hash prims q)
        rw [he, hashAnswer_of_not_isFixed prims hfix] at hp'
        exact hle (randomOracle_support q s (y, b) hp').2.1
      · simp at hp
        obtain ⟨a, b, _, rfl⟩ := hp
        cases hq
    · exact ih _ _ w hw q y hq hfix

/-- Programming distinct fresh inputs succeeds and changes only those cells. -/
theorem seedGenPrograms_fresh {ι : Type} (l : List ι) (q : ι → Query C) (v : ι → HashOutput)
    (hfix : ∀ i, ¬ IsFixed (q i)) :
    ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) (l.mapM fun i => program (q i) (v i))).run s) →
      (∀ i ∈ l, s (q i) = none) → (l.map q).Nodup →
        z.1.all id = true ∧ ∀ x, x ∉ l.map q → z.2 x = s x := by
  induction l with
  | nil =>
    intro s z hz _ _
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, fun _ _ => rfl⟩
  | cons a l ih =>
    intro s z hz hs hn
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind,
      Set.mem_iUnion, simulateQ_world_program, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, p', hp', rfl⟩ := hz
    rw [programAnswer_run_fresh (hfix a) s (hs a (by simp)) (v a)] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [List.map_cons, List.nodup_cons] at hn
    have hs' : ∀ i ∈ l, (s.cacheQuery (q a) (v a)) (q i) = none := by
      intro i hi
      have hne : q i ≠ q a := fun he => hn.1 (he ▸ List.mem_map_of_mem hi)
      rw [QueryCache.cacheQuery_of_ne s _ hne]
      exact hs i (by simp [hi])
    obtain ⟨hall, hrest⟩ := ih _ p' hp' hs' hn.2
    refine ⟨by simpa using hall, fun x hx => ?_⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    exact (hrest x hx.2).trans (QueryCache.cacheQuery_of_ne s _ hx.1)

/-- Programming fresh distinct inputs succeeds. -/
theorem setupProgramOk_fresh (phase : Phase) (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) (s : HashCache C) (z : Bool × HashCache C)
    (hz : z ∈ support ((simulateQ (worldAnswer prims)
      (setupProgramOk (phase := phase) D parts log sent parameter seeds pairs high)).run s))
    (hfresh : ∀ x ∈ setupProgrammingInputs phase D (setupProgramView phase D parts log sent), s x = none)
    (hnodup : (setupProgrammingInputs phase D (setupProgramView phase D parts log sent)).Nodup) : z.1 = true := by
  cases phase
  · set view := setupProgramView .seedGen D parts log sent
    have hfixT : ∀ T, ¬ IsFixed (setupTermProgrammingInput .seedGen D view T) := fun T => by
      simp [IsFixed, setupTermProgrammingInput]
    have hfixP : ∀ p, ¬ IsFixed (setupPairProgrammingInput .seedGen D view p) := fun p => by
      simp [IsFixed, setupPairProgrammingInput]
    unfold setupProgramOk at hz
    simp only [programParameter, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion,
      simulateQ_world_program, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩ := hz
    simp only [setupProgrammingInputs, setupParameterInputs, ite_true, List.singleton_append, List.nodup_append,
      List.nodup_cons] at hnodup
    obtain ⟨⟨hPT, hT⟩, hC, hdisj⟩ := hnodup
    change seedGenParameterProgrammingInput D view ∉ _ at hPT
    have hPC : seedGenParameterProgrammingInput D view ∉ (seedGenCrossCoordinates D).map
        (setupPairProgrammingInput .seedGen D view) := fun hm => hdisj _ List.mem_cons_self _ hm rfl
    have hTC : ∀ a ∈ (seedGenKnownCoordinates D).map (setupTermProgrammingInput .seedGen D view),
        ∀ b ∈ (seedGenCrossCoordinates D).map (setupPairProgrammingInput .seedGen D view), a ≠ b :=
      fun a ha b hb => hdisj a (List.mem_cons_of_mem _ ha) b hb
    have hmemP : seedGenParameterProgrammingInput D view ∈ setupProgrammingInputs .seedGen D view :=
      List.mem_append_left _ List.mem_cons_self
    change p₁ ∈ support ((programAnswer (seedGenParameterProgrammingInput D view, _)).run s) at hp₁
    rw [programAnswer_run_fresh (by simp [IsFixed, seedGenParameterProgrammingInput]) s (hfresh _ hmemP)] at hp₁
    simp only [support_pure, Set.mem_singleton_iff] at hp₁
    subst hp₁
    have h₂ := seedGenPrograms_fresh prims (seedGenKnownCoordinates D) (setupTermProgrammingInput .seedGen D view) seeds hfixT
      _ p₂ hp₂ (fun T hT' => by
        have hne : setupTermProgrammingInput .seedGen D view T ≠ seedGenParameterProgrammingInput D view :=
          fun he => hPT (he ▸ List.mem_map_of_mem hT')
        exact (QueryCache.cacheQuery_of_ne s (seedGenFullParameter high parameter) hne).trans
          (hfresh _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hT'))))) hT
    have h₃ := seedGenPrograms_fresh prims (seedGenCrossCoordinates D) (setupPairProgrammingInput .seedGen D view) pairs hfixP
      _ p₃ hp₃ (fun p hp' => by
        have hm : setupPairProgrammingInput .seedGen D view p ∈ (seedGenCrossCoordinates D).map
            (setupPairProgrammingInput .seedGen D view) := List.mem_map_of_mem hp'
        have hne : setupPairProgrammingInput .seedGen D view p ≠ seedGenParameterProgrammingInput D view :=
          fun he => hPC (he ▸ hm)
        exact (h₂.2 _ (fun hmT => hTC _ hmT _ hm rfl)).trans
          ((QueryCache.cacheQuery_of_ne s (seedGenFullParameter high parameter) hne).trans
          (hfresh _ (List.mem_append_right _ hm)))) hC
    simp only [Bool.and_eq_true]
    exact ⟨⟨trivial, h₂.1⟩, h₃.1⟩
  · have hfixT : ∀ T, ¬ IsFixed (setupTermProgrammingInput .prss D (setupProgramView .prss D parts log sent) T) :=
      fun T => by simp [IsFixed, setupTermProgrammingInput]
    have hfixP : ∀ p, ¬ IsFixed (setupPairProgrammingInput .prss D (setupProgramView .prss D parts log sent) p) :=
      fun p => by simp [IsFixed, setupPairProgrammingInput]
    unfold setupProgramOk at hz
    simp only [programParameter, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind,
      Set.mem_iUnion, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p₂, hp₂, p₃, hp₃, rfl⟩ := hz
    have hnil : setupParameterInputs .prss D (setupProgramView .prss D parts log sent) = [] := by
      simp [setupParameterInputs]
    simp only [setupProgrammingInputs, hnil, List.nil_append] at hnodup hfresh
    obtain ⟨hT, hC, hdisj⟩ := List.nodup_append.mp hnodup
    have h₂ := seedGenPrograms_fresh prims (seedGenKnownCoordinates D) _ seeds hfixT
      _ p₂ hp₂ (fun T hT' => hfresh _ (List.mem_append_left _ (List.mem_map_of_mem hT'))) hT
    have h₃ := seedGenPrograms_fresh prims (seedGenCrossCoordinates D) _ pairs hfixP
      _ p₃ hp₃ (fun p hp' => by
        have hm : setupPairProgrammingInput .prss D (setupProgramView .prss D parts log sent) p ∈
            (seedGenCrossCoordinates D).map (setupPairProgrammingInput .prss D (setupProgramView .prss D parts log sent)) :=
          List.mem_map_of_mem hp'
        exact (h₂.2 _ (fun hmT => hdisj _ hmT _ hm rfl)).trans (hfresh _ (List.mem_append_right _ hm))) hC
    simp only [Bool.true_and, Bool.and_eq_true]
    exact ⟨h₂.1, h₃.1⟩

end Support

section Deterministic

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The fixed-oracle run of the last two rounds gives the reference echo data and outputs. -/
theorem setupPostTraced_fixed_support (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (h : Query C → HashOutput)
    (z : A.State × (C.Party → Mail C E) × (C.Party → Option (SeedGenEchoData C)) × (C.Party → Option (Keys C)))
    (hz : z ∈ support (simulateQ (fixedLocal prims h) (setupPostTraced (phase := phase) D A state parts committed))) :
    z.2.2.2 = (fun _ => none) ∨ (z.2.2.1 = setupRevealAllFixed phase prims D h parts committed z.2.1 ∧
      ∃ echoSent : C.Party → Mail C E, z.2.2.2 = setupEchoDataOutput phase D z.2.2.1 echoSent) := by
  unfold setupPostTraced at hz
  split_ifs at hz
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  · simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion,
      simulateQ_fixedLocal_setupRevealComputations, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, _, data, rfl, f, hf, rfl⟩ := hz
    unfold setupFinishLocal at hf
    split_ifs at hf
    · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hf
      subst hf
      exact Or.inl rfl
    · simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] at hf
      obtain ⟨e, _, rfl⟩ := hf
      exact Or.inr ⟨rfl, e.2, rfl⟩

/-- The fixed-oracle run of the last two rounds gives no echo data or the reference echo data. -/
theorem setupPostTraced_fixed_data (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (h : Query C → HashOutput)
    (z : A.State × (C.Party → Mail C E) × (C.Party → Option (SeedGenEchoData C)) × (C.Party → Option (Keys C)))
    (hz : z ∈ support (simulateQ (fixedLocal prims h) (setupPostTraced (phase := phase) D A state parts committed))) :
    (∀ i, z.2.2.1 i = none) ∨ z.2.2.1 = setupRevealAllFixed phase prims D h parts committed z.2.1 := by
  unfold setupPostTraced at hz
  split_ifs at hz
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl fun _ => rfl
  · simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion,
      simulateQ_fixedLocal_setupRevealComputations, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, _, data, rfl, f, _, rfl⟩ := hz
    exact Or.inr rfl

/-- Without a failed programming, a missed extraction or an echo collision, the emulated outputs
are the dealt keys. -/
theorem setupKnown_projection_eq (phase : Phase) (prims : Primitives) (D : C.Coalition) {σ : Type} (h : Query C → HashOutput)
    (r : SeedGenKnownTrace C E σ) (high : HashOutput)
    (hparameter : ∀ q ∈ setupParameterInputs phase D (setupProgramView phase D r.parts r.log r.sent),
      h q = seedGenFullParameter high r.parameter)
    (hzero : phase = .prss → r.parameter = 0)
    (hterm : ∀ T ∈ seedGenKnownCoordinates D,
      h (setupTermProgrammingInput phase D (setupProgramView phase D r.parts r.log r.sent) T) = r.seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates D,
      h (setupPairProgrammingInput phase D (setupProgramView phase D r.parts r.log r.sent) p) = r.pairs p)
    (hpost : r.outputs = (fun _ => none) ∨
      (r.data = setupRevealAllFixed phase prims D h r.parts (setupCommitInbox phase D r.parts r.commitments r.sent)
        r.revealSent ∧ ∃ echoSent : C.Party → Mail C E, r.outputs = setupEchoDataOutput phase D r.data echoSent))
    (hextract : ¬ SetupExtractFail (phase := phase) D r) (hcollision : ¬ SetupEchoCollision (phase := phase) D r) :
    seedGenMixedProjection D r.result = seedGenIdealProjection D r.result := by
  unfold seedGenMixedProjection seedGenIdealProjection SeedGenKnownTrace.result
  simp only [Prod.mk.injEq, true_and]
  funext i
  rcases hpost with ho | ⟨hdata, echoSent, ho⟩
  · simp [ho]
  · cases hi : r.outputs i with
    | none => simp
    | some key =>
      set committed := setupCommitInbox phase D r.parts r.commitments r.sent
      have ho' : setupEchoDataOutput phase D (setupRevealAllFixed phase prims D h r.parts committed r.revealSent)
          echoSent i = some key := by rw [← hdata, ← ho]; exact hi
      have hhonest := (setupEchoDataOutput_some phase D _ echoSent i key ho').1
      have hall := setupEchoDataOutput_all_some phase D _ echoSent i key ho'
      have hkey := setupRevealEcho_output_eq_hybrid phase prims D h r.parts committed r.revealSent echoSent r.sent
        r.log r.parameter r.seeds r.pairs high
        (fun k j hk hj => by
          by_contra hne
          exact hextract ⟨k, hk, by rw [hdata]; exact hall k hk, j, hj, hne⟩)
        hparameter hzero
        (fun T hT => hterm T (List.mem_filter.mpr ⟨Finset.mem_toList.mpr (Finset.mem_univ T), by simpa using hT⟩))
        hpair i key ho'
        (fun j hj hcol => by
          by_contra hne
          obtain ⟨hsi, _⟩ := setupRevealAllFixed_some phase prims D h r.parts committed r.revealSent i (hall i hhonest)
          obtain ⟨hsj, _⟩ := setupRevealAllFixed_some phase prims D h r.parts committed r.revealSent j (hall j hj)
          exact hcollision ⟨i, j, _, _, _, _, hhonest, hj, by rw [hdata]; exact hsi, by rw [hdata]; exact hsj,
            by rw [D_sharedQueries_at, D_sharedQueries_at]; exact hcol, hne⟩)
      rw [Option.map_some, ite_eq_left ⟨hhonest, rfl⟩, hkey,
        setupHiddenOverlay_hybrid (phase := phase) D h r.parts r.parameter r.seeds r.pairs i hhonest]

end Deterministic

section Reduction

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The dealer of the PRSS setup has the parameter `0`. The support of the known game gives the
hypothesis `phase = .prss → parameter = 0` from this normal form. -/
theorem setupDealerSamples_prss :
    setupDealerSamples (C := C) .prss = (do
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairs ← $ᵗ (C.Pair → HashOutput)
      pure ((0 : PublicParameter), seeds, pairs)) := by
  simp only [setupDealerSamples, setupParameterSample, pure_bind]

/-- The dealer of the PRSS setup has the parameter `0`. -/
theorem setupDealerSamples_run_zero (phase : Phase) (prims : Primitives) (s : HashCache C)
    (p : (PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) × HashCache C)
    (hp : p ∈ support ((simulateQ (worldAnswer prims)
      (free (liftComp (setupDealerSamples (C := C) phase) (LocalSpec C)))).run s)) :
    phase = .prss → p.1.1 = 0 := by
  intro hphase
  subst hphase
  rw [simulateQ_world_sample] at hp
  simp only [setupDealerSamples, setupParameterSample, pure_bind, StateT.run_lift, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hp
  obtain ⟨d, ⟨seeds, -, pairs, -, hd⟩, hpd⟩ := hp
  rw [hpd, hd]

/-- A mismatch of the common game is a failed programming, a missed extraction or an echo collision. -/
theorem setupKnown_bad_of_mismatch (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (r : SeedGenKnownTrace C E A.State)
    (hr : r ∈ support ((simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run' ∅))
    (hm : seedGenMixedProjection D r.result ≠ seedGenIdealProjection D r.result) :
    SeedGenProgramFail r ∨ SetupExtractFail (phase := phase) D r ∨ SetupEchoCollision (phase := phase) D r := by
  by_contra hbad
  simp only [not_or, SeedGenProgramFail, Bool.not_eq_false] at hbad
  obtain ⟨hok, hextract, hcollision⟩ := hbad
  apply hm
  unfold setupKnownGame at hr
  simp only [StateT.run'_eq, support_map, Set.mem_image, simulateQ_bind, StateT.run_bind, support_bind,
    Set.mem_iUnion] at hr
  obtain ⟨⟨r', s₈⟩, ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, p₄, hp₄, p₅, hp₅, p₆, hp₆, p₇, hp₇, hfin⟩, rfl⟩ := hr
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
  obtain ⟨rfl, rfl⟩ := hfin
  have n₀ := seedGenWorldRun_noMpc prims _ ∅ p₀ hp₀ noMpc_empty
  have n₁ := seedGenWorldRun_noMpc prims _ _ p₁ hp₁ n₀
  have n₂ := seedGenWorldRun_noMpc prims _ _ p₂ hp₂ n₁
  have n₃ := seedGenWorldRun_noMpc prims _ _ p₃ hp₃ n₂
  have n₄ := seedGenWorldRun_noMpc prims _ _ p₄ hp₄ n₃
  have n₅ := seedGenWorldRun_noMpc prims _ _ p₅ hp₅ n₄
  have n₆ := seedGenWorldRun_noMpc prims _ _ p₆ hp₆ n₅
  rw [simulateQ_free] at hp₇
  obtain ⟨g₇, n₇, hfix⟩ := localRun_support _ p₆.2 p₇ hp₇
  have hagree := agrees_hashOf prims (n₇ n₆)
  have hsupp := hfix (hashOf prims p₇.2) (good_hashOf prims _) hagree
  obtain ⟨hP, hT, hp⟩ := setupProgramOk_support (phase := phase) prims _ _ _ _ _ _ _ _ p₅.2 p₆ hp₆ hok
  have hread (q : Query C) (v : HashOutput) (hq : p₆.2 q = some v) : hashOf prims p₇.2 q = v :=
    hagree q v (g₇ hq)
  exact setupKnown_projection_eq (phase := phase) prims D (hashOf prims p₇.2) _ p₅.1 (fun q hq => hread _ _ (hP q hq))
    (setupDealerSamples_run_zero phase prims _ p₁ hp₁)
    (fun T hm => hread _ _ (hT T hm)) (fun q hm => hread _ _ (hp q hm))
    (setupPostTraced_fixed_support (phase := phase) prims D A _ _ _ _ _ hsupp) hextract hcollision

end Reduction

section CacheEvents

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The cells whose answers the extraction and the echo compare. These are the shared-key hashes and
the commitments of a corrupt sender. -/
def SetupComparedCell (phase : Phase) (D : C.Coalition) : Query C → Prop
  | .sharedKeys phase' _ => phase' = phase
  | .commit phase' j _ _ => phase' = phase ∧ j ∈ D.1
  | _ => False

/-- Two compared cells of a cache have equal answers. -/
def SetupComparedCollision (phase : Phase) (D : C.Coalition) (s : HashCache C) : Prop :=
  ∃ q₁ q₂ u, q₁ ≠ q₂ ∧ SetupComparedCell (phase := phase) D q₁ ∧ SetupComparedCell (phase := phase) D q₂ ∧ s q₁ = some u ∧ s q₂ = some u

/-- An opening that the adversary never queried before the commit answers its commitment. -/
def SetupFreshOpening (phase : Phase) (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ) (s : HashCache C) : Prop :=
  ∃ j i reveal c, j ∈ D.1 ∧ i ∉ D.1 ∧ s (.commit phase j i reveal) = some c ∧
    Msg.hashesOf (r.sent j i) = [c] ∧ ∀ y, (Query.commit (C := C) phase j i reveal, y) ∉ r.log

theorem setupRevealAllFixed_open (phase : Phase) (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (i j : C.Party) (hji : j ≠ i)
    (hs : (setupRevealAllFixed phase prims D h parts committed sent i).isSome) :
    [h (.commit phase j i (Msg.hashesOf (setupRevealInbox phase D parts committed sent i j)))] =
      Msg.hashesOf (committed i j) := by
  unfold setupRevealAllFixed setupRevealDataFixed at hs
  split_ifs at hs with h₁ h₂ h₃
  · simp at hs
  · simp at hs
  · have hc := (h₃ j hji).2
    simpa only [openQueries, D_mapM, D_hashQuery, getD_parties] using hc
  · simp at hs

/-- A cell that a fixed-oracle run reads for every oracle that agrees with the final cache is in
that cache. Otherwise two agreeing oracles differ there. -/
theorem seedGen_cached_of_agrees (s : HashCache C) (hs : NoMpc s) (x : Query C) (hx : ¬ IsFixed x)
    (P : (Query C → HashOutput) → Prop) (hP : ∀ h, Good prims h → Agrees h s → P h)
    (hread : ∀ h h', P h → P h' → h x = h' x) : s x = some (hashOf prims s x) := by
  cases hsx : s x with
  | some v => rw [agrees_hashOf prims hs x v hsx]
  | none =>
    exfalso
    let h' := Function.update (hashOf prims s) x (if hashOf prims s x = 0 then 1 else 0)
    have hg : Good prims h' := by
      intro y hy
      have hne : Query.hash y ≠ x := fun he => hx ⟨y, he.symm, hy⟩
      simp only [h', Function.update_of_ne hne]
      exact good_hashOf prims s y hy
    have ha : Agrees h' s := by
      intro q v hq
      have hne : q ≠ x := fun he => by rw [he, hsx] at hq; cases hq
      simp only [h', Function.update_of_ne hne]
      exact agrees_hashOf prims hs q v hq
    have he := hread _ _ (hP _ (good_hashOf prims s) (agrees_hashOf prims hs)) (hP h' hg ha)
    simp only [h', Function.update_self] at he
    split_ifs at he with h0
    · rw [h0] at he
      exact absurd he (by decide)
    · exact h0 he


/-- A missed extraction or an echo collision of a run is a collision of two compared cells or a
fresh opening, in the final cache. -/
theorem setupKnown_cacheEvent_of_bad (phase : Phase) (prims : Primitives) (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ)
    (s : HashCache C) (hs : NoMpc s)
    (hdata : ∀ h, Good prims h → Agrees h s → (∀ i, r.data i = none) ∨
      r.data = setupRevealAllFixed phase prims D h r.parts (setupCommitInbox phase D r.parts r.commitments r.sent)
        r.revealSent)
    (hlog : ∀ q y, (q, y) ∈ r.log → ¬ IsFixed q → s q = some y)
    (hbad : SetupExtractFail (phase := phase) D r ∨ SetupEchoCollision (phase := phase) D r) :
    SetupComparedCollision (phase := phase) D s ∨ SetupFreshOpening (phase := phase) D r s := by
  set committed := setupCommitInbox phase D r.parts r.commitments r.sent
  have hfixed (i : C.Party) (hi : r.data i ≠ none) (h : Query C → HashOutput) (hg : Good prims h)
      (ha : Agrees h s) : r.data = setupRevealAllFixed phase prims D h r.parts committed r.revealSent := by
    rcases hdata h hg ha with hn | he
    · exact absurd (hn i) hi
    · exact he
  rcases hbad with ⟨i, hi, hsome, j, hj, hne⟩ | ⟨i, j, ki, si, kj, sj, hi, hj, hdi, hdj, hcol, hne⟩
  · have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hdi : r.data i ≠ none := by simpa [Option.isSome_iff_ne_none] using hsome
    set rv := Msg.hashesOf (setupRevealInbox phase D r.parts committed r.revealSent i j)
    have hopen (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h s) :
        [h (.commit phase j i rv)] = Msg.hashesOf (committed i j) := by
      apply setupRevealAllFixed_open (phase := phase) prims D h r.parts committed r.revealSent i j hji
      rw [← hfixed i hdi h hg ha]
      exact hsome
    have hcached := seedGen_cached_of_agrees prims s hs (.commit phase j i rv) (by simp [IsFixed])
      (fun h => [h (.commit phase j i rv)] = Msg.hashesOf (committed i j)) hopen
      (fun h h' e e' => by simpa using e.trans e'.symm)
    set c := hashOf prims s (.commit phase j i rv)
    have hsent : Msg.hashesOf (r.sent j i) = [c] := by
      have := hopen _ (good_hashOf prims s) (agrees_hashOf prims hs)
      simp only [committed, setupCommitInbox, roundInbox, ite_eq_left hj] at this
      exact this.symm
    by_cases hl : ∃ y, (Query.commit (C := C) phase j i rv, y) ∈ r.log
    · obtain ⟨y, hy⟩ := hl
      have hyc : y = c := Option.some.inj ((hlog _ y hy (by simp [IsFixed])).symm.trans hcached)
      subst hyc
      by_contra hno
      apply hne
      apply extractReveal_eq_of_unique phase r.log r.sent j i rv _ hy hsent.symm
      intro reveal' value' hmem hval
      by_contra hrv
      apply hno
      left
      have hv : value' = hashOf prims s (.commit phase j i rv) := by
        have := hval.trans hsent
        simpa using this
      subst hv
      exact ⟨Query.commit phase j i reveal', Query.commit phase j i rv, _,
        fun he => hrv (Query.commit.inj he).2.2.2, (⟨rfl, hj⟩ : SetupComparedCell (phase := phase) D (.commit phase j i reveal')),
        (⟨rfl, hj⟩ : SetupComparedCell (phase := phase) D (.commit phase j i rv)), hlog _ _ hmem (by simp [IsFixed]), hcached⟩
    · push Not at hl
      exact Or.inr ⟨j, i, rv, c, hj, hi, hcached, hsent, hl⟩
  · left
    have hdi' : r.data i ≠ none := by rw [hdi]; simp
    have hshared (a b : C.Party) (ka : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
        (sa : List HashOutput) (hda : r.data a = some (ka, sa)) (h : Query C → HashOutput) (hg : Good prims h)
        (ha : Agrees h s) : sa.getD b.val 0 = h (.sharedKeys phase ((sharedTerms a b).map ka.2.1)) := by
      have hf := hfixed i hdi' h hg ha
      have hsa : (setupRevealAllFixed phase prims D h r.parts committed r.revealSent a).isSome := by
        rw [← hf, hda]; rfl
      obtain ⟨he, _⟩ := setupRevealAllFixed_some phase prims D h r.parts committed r.revealSent a hsa
      rw [← hf, hda] at he
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj he)
      exact D_sharedQueries_at prims h phase a b _
    have hcache (a b : C.Party) (ka : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
        (sa : List HashOutput) (hda : r.data a = some (ka, sa)) :
        s (.sharedKeys phase ((sharedTerms a b).map ka.2.1)) = some (sa.getD b.val 0) := by
      have hc := seedGen_cached_of_agrees prims s hs (.sharedKeys phase ((sharedTerms a b).map ka.2.1))
        (by simp [IsFixed]) (fun h => sa.getD b.val 0 = h (.sharedKeys phase ((sharedTerms a b).map ka.2.1)))
        (hshared a b ka sa hda) (fun h h' e e' => e.symm.trans e')
      rw [hc, ← hshared a b ka sa hda _ (good_hashOf prims s) (agrees_hashOf prims hs)]
    exact ⟨_, _, _, hne, rfl, rfl, hcache i j ki si hdi, (hcache j i kj sj hdj).trans (by rw [hcol])⟩

/-- The facts of a run that the cache events read. -/
theorem setupKnownGame_support (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (w : SeedGenKnownTrace C E A.State × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run ∅)) :
    NoMpc w.2 ∧
      (∀ h, Good prims h → Agrees h w.2 → (∀ i, w.1.data i = none) ∨
        w.1.data = setupRevealAllFixed phase prims D h w.1.parts
          (setupCommitInbox phase D w.1.parts w.1.commitments w.1.sent) w.1.revealSent) ∧
      (∀ q y, (q, y) ∈ w.1.log → ¬ IsFixed q → w.2 q = some y) := by
  unfold setupKnownGame at hw
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hw
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, p₄, hp₄, p₅, hp₅, p₆, hp₆, p₇, hp₇, hfin⟩ := hw
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
  subst hfin
  have n₆ := seedGenWorldRun_noMpc prims _ _ p₆ hp₆ (seedGenWorldRun_noMpc prims _ _ p₅ hp₅ (seedGenWorldRun_noMpc prims _ _ p₄ hp₄
    (seedGenWorldRun_noMpc prims _ _ p₃ hp₃ (seedGenWorldRun_noMpc prims _ _ p₂ hp₂ (seedGenWorldRun_noMpc prims _ _ p₁ hp₁
      (seedGenWorldRun_noMpc prims _ ∅ p₀ hp₀ noMpc_empty))))))
  have g₁ := grows_worldAnswer prims |>.simulateQ _ _ p₁ hp₁
  have g₂ := grows_worldAnswer prims |>.simulateQ _ _ p₂ hp₂
  have g₃ := grows_worldAnswer prims |>.simulateQ _ _ p₃ hp₃
  have g₄ := grows_worldAnswer prims |>.simulateQ _ _ p₄ hp₄
  have g₅ := grows_worldAnswer prims |>.simulateQ _ _ p₅ hp₅
  have g₆ := grows_worldAnswer prims |>.simulateQ _ _ p₆ hp₆
  have g₇ := grows_worldAnswer prims |>.simulateQ _ _ p₇ hp₇
  rw [simulateQ_free] at hp₇
  obtain ⟨_, n₇, hfix⟩ := localRun_support _ p₆.2 p₇ hp₇
  refine ⟨n₇ n₆, fun h hg ha => setupPostTraced_fixed_data (phase := phase) prims D A _ _ _ h _ (hfix h hg ha), ?_⟩
  intro q y hq hq'
  rcases List.mem_append.mp hq with hq | hq
  · exact g₇ (g₆ (g₅ (g₄ (g₃ (g₂ (g₁ (seedGenObserve_log_cached prims _ ∅ p₀ hp₀ q y hq hq')))))))
  · exact g₇ (g₆ (g₅ (seedGenObserve_log_cached prims _ _ p₄ hp₄ q y hq hq')))

end CacheEvents

section Arith

variable {C : Committee}

theorem seedGenProgrammingCount_le (D : C.Coalition) :
    seedGenProgrammingCount D ≤ 1 + termCount C + C.n.choose 2 := by
  unfold seedGenProgrammingCount
  have hT : (seedGenKnownCoordinates D).length ≤ termCount C := by
    rw [← seedGenFinish_card_term]
    exact (seedGenKnownCoordinates_nodup D).length_le_card
  have hP : (seedGenCrossCoordinates D).length ≤ C.n.choose 2 := by
    rw [← seedGenFinish_card_pair]
    exact (seedGenCrossCoordinates_nodup D).length_le_card
  omega

/-- The programming, extraction and echo costs fit in half the error of the PRSS setup. -/
theorem prssSetupKnown_arith {C : Committee} (q K : ℕ) (hK : K ≤ 1 + termCount C + C.n.choose 2) :
    2 * (q * K + K ^ 2) + ((q + C.n ^ 2) ^ 2 + 2 * (q + C.n ^ 2)) ≤ (q + prssSetupSecrets C) ^ 2 := by
  have hn : 1 ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have hT : 1 ≤ termCount C := Nat.choose_pos (by have := C.one_le_t; unfold Committee.n; omega)
  have hP : 2 * C.n.choose 2 ≤ C.n * C.n := by
    rw [Nat.choose_two_right]
    have := Nat.div_mul_le_self (C.n * (C.n - 1)) 2
    have h2 : C.n * (C.n - 1) ≤ C.n * C.n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  set P := C.n.choose 2
  set T := termCount C
  set n := C.n
  have hS : prssSetupSecrets C = n * (T + n) + T + P + n ^ 2 := rfl
  have hnT : T ≤ n * T := Nat.le_mul_of_pos_left T hn
  have hq : n ^ 2 + 1 + K ≤ prssSetupSecrets C := by
    rw [hS]; nlinarith
  have h2K : 2 * K ≤ prssSetupSecrets C := by
    rw [hS]; nlinarith
  have h2n : 2 * n ^ 2 + K ≤ prssSetupSecrets C := by
    rw [hS]; nlinarith
  set s := prssSetupSecrets C
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  nlinarith [Nat.zero_le (q * K), Nat.zero_le (q * n ^ 2), Nat.mul_le_mul h2K h2n, Nat.mul_le_mul h2n h2n]

/-- The programming, extraction and echo costs fit in half the error of a setup. -/
theorem setupKnown_arith (phase : Phase) {C : Committee} (q K : ℕ) (hK : K ≤ 1 + termCount C + C.n.choose 2) :
    2 * (q * K + K ^ 2) + ((q + C.n ^ 2) ^ 2 + 2 * (q + C.n ^ 2)) ≤ (q + setupSecrets phase C) ^ 2 :=
  (prssSetupKnown_arith q K hK).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_left (prssSetupSecrets_le phase C) q) 2)

end Arith

section Birthday

variable {C : Committee} {E : Type} (prims : Primitives)

/-- At most `k` compared cells of a cache are filled. -/
def SetupComparedCount (phase : Phase) (D : C.Coalition) (s : HashCache C) (k : ℕ) : Prop :=
  ∃ S : Finset (Query C), S.card ≤ k ∧ ∀ q, SetupComparedCell (phase := phase) D q → s q ≠ none → q ∈ S

theorem setupComparedCount_insert (phase : Phase) {D : C.Coalition} {s : HashCache C} {k : ℕ}
    (h : SetupComparedCount (phase := phase) D s k) (q : Query C) (u : HashOutput) :
    SetupComparedCount (phase := phase) D (s.cacheQuery q u) (k + 1) := by
  obtain ⟨S, hS, hm⟩ := h
  refine ⟨insert q S, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hS 1), fun q' hc hq' => ?_⟩
  by_cases hq : q' = q
  · simpa only [hq] using Finset.mem_insert_self q S
  · rw [QueryCache.cacheQuery_of_ne s _ hq] at hq'
    exact Finset.mem_insert_of_mem (hm q' hc hq')

theorem setupComparedCount_insert_other (phase : Phase) {D : C.Coalition} {s : HashCache C} {k : ℕ}
    (h : SetupComparedCount (phase := phase) D s k) (q : Query C) (hq : ¬ SetupComparedCell (phase := phase) D q) (u : HashOutput) :
    SetupComparedCount (phase := phase) D (s.cacheQuery q u) k := by
  obtain ⟨S, hS, hm⟩ := h
  refine ⟨S, hS, fun q' hc hq' => hm q' hc ?_⟩
  have hne : q' ≠ q := fun he => hq (he ▸ hc)
  rwa [QueryCache.cacheQuery_of_ne s _ hne] at hq'

/-- A collision after one insertion matches the new answer with an old compared cell. -/
theorem setupComparedCollision_insert (phase : Phase) {D : C.Coalition} {s : HashCache C}
    (hs : ¬ SetupComparedCollision (phase := phase) D s) (q : Query C) (u : HashOutput)
    (h : SetupComparedCollision (phase := phase) D (s.cacheQuery q u)) :
    SetupComparedCell (phase := phase) D q ∧ ∃ q', q' ≠ q ∧ SetupComparedCell (phase := phase) D q' ∧ s q' = some u := by
  obtain ⟨q₁, q₂, v, hne, hc₁, hc₂, h₁, h₂⟩ := h
  by_cases hq₁ : q₁ = q
  · subst q₁
    rw [QueryCache.cacheQuery_self, Option.some.injEq] at h₁
    subst v
    exact ⟨hc₁, q₂, hne.symm, hc₂, by rwa [QueryCache.cacheQuery_of_ne s _ hne.symm] at h₂⟩
  · by_cases hq₂ : q₂ = q
    · subst q₂
      rw [QueryCache.cacheQuery_self, Option.some.injEq] at h₂
      subst v
      exact ⟨hc₂, q₁, hne, hc₁, by rwa [QueryCache.cacheQuery_of_ne s _ hq₁] at h₁⟩
    · exact (hs ⟨q₁, q₂, v, hne, hc₁, hc₂,
        by rwa [QueryCache.cacheQuery_of_ne s _ hq₁] at h₁,
        by rwa [QueryCache.cacheQuery_of_ne s _ hq₂] at h₂⟩).elim

/-- A fresh answer collides with one of `k` compared cells with probability at most `k / 2^256`. -/
theorem probEvent_setupComparedCollision_fresh (phase : Phase) {D : C.Coalition} {s : HashCache C} {k : ℕ}
    (hs : ¬ SetupComparedCollision (phase := phase) D s) (hk : SetupComparedCount (phase := phase) D s k) (q : Query C) :
    Pr{let u ← $ᵗ HashOutput}[SetupComparedCollision (phase := phase) D (s.cacheQuery q u)] ≤
      (k : ℝ≥0∞) / Fintype.card HashOutput := by
  obtain ⟨S, hS, hm⟩ := hk
  have hbad : (Finset.univ.filter fun u : HashOutput =>
      SetupComparedCollision (phase := phase) D (s.cacheQuery q u)).card ≤ S.card := by
    let f : HashOutput → Query C := fun u =>
      if h : SetupComparedCollision (phase := phase) D (s.cacheQuery q u) then
        (setupComparedCollision_insert (phase := phase) hs q u h).2.choose else q
    refine Finset.card_le_card_of_injOn f (fun u hu => ?_) (fun u hu v hv heq => ?_)
    · have hc := (Finset.mem_filter.mp hu).2
      rw [show f u = _ from dite_eq_left hc]
      have hs' := (setupComparedCollision_insert (phase := phase) hs q u hc).2.choose_spec
      exact hm _ hs'.2.1 (by rw [hs'.2.2]; exact Option.some_ne_none u)
    · have hc := (Finset.mem_filter.mp hu).2
      have hd := (Finset.mem_filter.mp hv).2
      rw [show f u = _ from dite_eq_left hc, show f v = _ from dite_eq_left hd] at heq
      have h₁ := (setupComparedCollision_insert (phase := phase) hs q u hc).2.choose_spec.2.2
      have h₂ := (setupComparedCollision_insert (phase := phase) hs q v hd).2.choose_spec.2.2
      rw [heq, h₂] at h₁
      exact (Option.some.inj h₁).symm
  rw [SampleableType.prEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast hbad.trans hS) _

/-- The birthday cost of `m` compared samples after `k` filled compared cells. -/
def seedGenBirthdayCost (k m : ℕ) : ℝ≥0∞ := ((m * (2 * k + m) : ℕ) : ℝ≥0∞) / (2 * Fintype.card HashOutput)

theorem seedGenBirthdayCost_step (k m : ℕ) (hm : 0 < m) :
    (k : ℝ≥0∞) / Fintype.card HashOutput + seedGenBirthdayCost (k + 1) (m - 1) ≤ seedGenBirthdayCost k m := by
  unfold seedGenBirthdayCost
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [← ENNReal.mul_div_mul_left (k : ℝ≥0∞) _ h2 h2', ← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  norm_cast
  nlinarith

/-- The random-oracle calls of a local computation at a compared cell. -/
def setupComparedCall (phase : Phase) (D : C.Coalition) : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => SetupComparedCell (phase := phase) D q
  | _ => False

/-- The compared calls of either copy of the world. -/
def setupComparedWorldCall (phase : Phase) (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => setupComparedCall (phase := phase) D t
  | .inl (.inr _) => False
  | .inr t => setupComparedCall (phase := phase) D t

/-- A programming query at a compared cell. -/
def setupComparedProgram (phase : Phase) (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inl (.inr x) => SetupComparedCell (phase := phase) D x.1
  | _ => False

theorem setupCompared_hash_step (phase : Phase) (prims : Primitives) {D : C.Coalition} {β : Type} (q : Query C) (s : HashCache C) (k m : ℕ)
    (hs : ¬ SetupComparedCollision (phase := phase) D s) (hk : SetupComparedCount (phase := phase) D s k)
    (g : HashOutput → HashCache C → ProbComp (β × HashCache C))
    (hg : ∀ u s', ¬ SetupComparedCollision (phase := phase) D s' → SetupComparedCount (phase := phase) D s' k →
      Pr{let z ← g u s'}[SetupComparedCollision (phase := phase) D z.2] ≤ seedGenBirthdayCost k m)
    (hg' : SetupComparedCell (phase := phase) D q → 0 < m ∧ ∀ u s', ¬ SetupComparedCollision (phase := phase) D s' →
      SetupComparedCount (phase := phase) D s' (k + 1) →
      Pr{let z ← g u s'}[SetupComparedCollision (phase := phase) D z.2] ≤ seedGenBirthdayCost (k + 1) (m - 1)) :
    Pr{let z ← (hashAnswer prims q).run s >>= fun p => g p.1 p.2}[SetupComparedCollision (phase := phase) D z.2] ≤
      seedGenBirthdayCost k m := by
  by_cases hfix : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hfix
    rw [hashAnswer_of_isFixed prims hi, StateT.run_pure, pure_bind]
    exact hg _ s hs hk
  · rw [hashAnswer_of_not_isFixed prims hfix]
    cases hsq : s q with
    | some u =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hsq, pure_bind]
      exact hg u s hs hk
    | none =>
      have heq : ((Query C →ₒ HashOutput).randomOracle q).run s =
          (fun u => (u, s.cacheQuery q u)) <$> ($ᵗ HashOutput) := by
        rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hsq]
        rfl
      rw [heq, bind_map_left]
      by_cases hc : SetupComparedCell (phase := phase) D q
      · obtain ⟨hm, hg''⟩ := hg' hc
        have h := prEvent_bind_le_prEvent_add_of_support ($ᵗ HashOutput)
          (fun u => g u (s.cacheQuery q u))
          (fun u => SetupComparedCollision (phase := phase) D (s.cacheQuery q u))
          (fun z => SetupComparedCollision (phase := phase) D z.2)
          (ε := seedGenBirthdayCost (k + 1) (m - 1))
          (fun u _ hu => hg'' u _ hu (setupComparedCount_insert (phase := phase) hk q u))
        exact (h.trans (add_le_add (probEvent_setupComparedCollision_fresh (phase := phase) hs hk q) le_rfl)).trans
          (seedGenBirthdayCost_step k m hm)
      · refine prEvent_bind_le_of_forall_le _ _ _ fun u => hg u _ ?_ (setupComparedCount_insert_other (phase := phase) hk q hc u)
        intro hcol
        exact hc (setupComparedCollision_insert (phase := phase) hs q u hcol).1

theorem setupCompared_local_step (phase : Phase) (prims : Primitives) {D : C.Coalition} {β : Type} (t : (LocalSpec C).Domain) (s : HashCache C)
    (k m : ℕ) (hs : ¬ SetupComparedCollision (phase := phase) D s) (hk : SetupComparedCount (phase := phase) D s k)
    (g : (LocalSpec C).Range t → HashCache C → ProbComp (β × HashCache C))
    (hg : ∀ u s', ¬ SetupComparedCollision (phase := phase) D s' → SetupComparedCount (phase := phase) D s' k →
      Pr{let z ← g u s'}[SetupComparedCollision (phase := phase) D z.2] ≤ seedGenBirthdayCost k m)
    (hg' : setupComparedCall (phase := phase) D t → 0 < m ∧ ∀ u s', ¬ SetupComparedCollision (phase := phase) D s' →
      SetupComparedCount (phase := phase) D s' (k + 1) →
      Pr{let z ← g u s'}[SetupComparedCollision (phase := phase) D z.2] ≤ seedGenBirthdayCost (k + 1) (m - 1)) :
    Pr{let z ← (localAnswer prims t).run s >>= fun p => g p.1 p.2}[SetupComparedCollision (phase := phase) D z.2] ≤
      seedGenBirthdayCost k m := by
  rcases t with n | q | x
  · have heq : (localAnswer (C := C) prims (.inl n)).run s =
        (fun u => (u, s)) <$> (OracleComp.lift (OracleSpec.query (spec := unifSpec) n)) := by
      simp [localAnswer, unifFwdImpl]
    rw [heq]
    erw [bind_map_left]
    exact prEvent_bind_le_of_forall_le _ _ _ fun u => hg u s hs hk
  · exact setupCompared_hash_step (phase := phase) prims q s k m hs hk g hg hg'
  · change Pr{let z ← (prgAnswer prims x).run s >>= fun p => g p.1 p.2}[
      SetupComparedCollision (phase := phase) D z.2] ≤ _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    exact setupCompared_hash_step (phase := phase) prims (.streamKey x.2.1) s k m hs hk
      (fun u s' => g (prims.aes.eval (truncateHash u) x.2.2) s') (fun u s' h₁ h₂ => hg _ s' h₁ h₂)
      (fun hc => by simp [SetupComparedCell] at hc)

/-- The birthday bound on the compared cells of a world computation. -/
theorem setupCompared_birthday (phase : Phase) (prims : Primitives) {D : C.Coalition} {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ m s k, IsQueryBoundP oa (setupComparedWorldCall (phase := phase) D) m → IsQueryBoundP oa (setupComparedProgram (phase := phase) D) 0 →
      ¬ SetupComparedCollision (phase := phase) D s → SetupComparedCount (phase := phase) D s k →
      Pr{let z ← (simulateQ (worldAnswer prims) oa).run s}[SetupComparedCollision (phase := phase) D z.2] ≤
        seedGenBirthdayCost k m := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m s k _ _ hs _
    simp [hs]
  | query_bind t f ih =>
    intro m s k hm hp hs hk
    rw [isQueryBoundP_query_bind_iff] at hm hp
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind]
    rcases t with (t | x) | t
    · change Pr{let z ← (localAnswer prims t).run s >>= fun p => (simulateQ (worldAnswer prims) (f p.1)).run p.2}[
        SetupComparedCollision (phase := phase) D z.2] ≤ _
      refine setupCompared_local_step (phase := phase) prims t s k m hs hk
        (fun u s' => (simulateQ (worldAnswer prims) (f u)).run s') (fun u s' h₁ h₂ => ?_) (fun hc => ?_)
      · have hu := hm.2 u
        have hpu := hp.2 u
        simp only [setupComparedWorldCall, setupComparedProgram, ↓reduceIte] at hu hpu
        by_cases hct : setupComparedCall (phase := phase) D t
        · erw [ite_eq_left hct] at hu
          exact (ih u (m - 1) s' k hu hpu h₁ h₂).trans (by
            unfold seedGenBirthdayCost
            exact ENNReal.div_le_div_right (by gcongr <;> omega) _)
        · erw [ite_eq_right hct] at hu
          exact ih u m s' k hu hpu h₁ h₂
      · have hm' := hm.1.resolve_left (by simpa [setupComparedWorldCall] using hc)
        refine ⟨hm', fun u s' h₁ h₂ => ?_⟩
        have hu := hm.2 u
        have hpu := hp.2 u
        simp only [setupComparedWorldCall, setupComparedProgram, ↓reduceIte] at hu hpu
        erw [ite_eq_left hc] at hu
        exact ih u (m - 1) s' (k + 1) hu hpu h₁ h₂
    · have hx : ¬ SetupComparedCell (phase := phase) D x.1 := by
        simpa [setupComparedProgram] using hp.1
      change Pr{let z ← (programAnswer x).run s >>= fun p => (simulateQ (worldAnswer prims) (f p.1)).run p.2}[
        SetupComparedCollision (phase := phase) D z.2] ≤ _
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hpr => ?_
      have hu := hm.2 p.1
      have hpu := hp.2 p.1
      simp only [setupComparedWorldCall, setupComparedProgram] at hu hpu
      erw [ite_eq_right not_false] at hu
      erw [ite_eq_right hx] at hpu
      refine ih p.1 m p.2 k hu hpu ?_ ?_
      · simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hpr
        split_ifs at hpr
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpr
          subst hpr
          exact hs
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff] at hpr
          subst hpr
          intro hcol
          exact hx (setupComparedCollision_insert (phase := phase) hs x.1 x.2 hcol).1
      · simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hpr
        split_ifs at hpr
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpr
          subst hpr
          exact hk
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff] at hpr
          subst hpr
          exact setupComparedCount_insert_other (phase := phase) hk x.1 hx x.2
    · change Pr{let z ← (localAnswer prims t).run s >>= fun p => (simulateQ (worldAnswer prims) (f p.1)).run p.2}[
        SetupComparedCollision (phase := phase) D z.2] ≤ _
      refine setupCompared_local_step (phase := phase) prims t s k m hs hk
        (fun u s' => (simulateQ (worldAnswer prims) (f u)).run s') (fun u s' h₁ h₂ => ?_) (fun hc => ?_)
      · have hu := hm.2 u
        have hpu := hp.2 u
        simp only [setupComparedWorldCall, setupComparedProgram, ↓reduceIte] at hu hpu
        by_cases hct : setupComparedCall (phase := phase) D t
        · erw [ite_eq_left hct] at hu
          exact (ih u (m - 1) s' k hu hpu h₁ h₂).trans (by
            unfold seedGenBirthdayCost
            exact ENNReal.div_le_div_right (by gcongr <;> omega) _)
        · erw [ite_eq_right hct] at hu
          exact ih u m s' k hu hpu h₁ h₂
      · have hm' := hm.1.resolve_left (by simpa [setupComparedWorldCall] using hc)
        refine ⟨hm', fun u s' h₁ h₂ => ?_⟩
        have hu := hm.2 u
        have hpu := hp.2 u
        simp only [setupComparedWorldCall, setupComparedProgram, ↓reduceIte] at hu hpu
        erw [ite_eq_left hc] at hu
        exact ih u (m - 1) s' (k + 1) hu hpu h₁ h₂

theorem isQueryBoundP_free_setupCompared (phase : Phase) (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (setupComparedCall (phase := phase) D) n) :
    IsQueryBoundP (free oa) (setupComparedWorldCall (phase := phase) D) n ∧ IsQueryBoundP (free oa) (setupComparedProgram (phase := phase) D) 0 := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact ⟨trivial, trivial⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e]
    constructor
    · exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => (ih u _ (h.2 u)).1⟩
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [setupComparedProgram]), fun u => ?_⟩
      simpa [setupComparedProgram] using (ih u _ (h.2 u)).2

theorem isQueryBoundP_observe_setupCompared (phase : Phase) (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (setupComparedCall (phase := phase) D) n) :
    IsQueryBoundP (observe oa) (setupComparedWorldCall (phase := phase) D) n ∧
      IsQueryBoundP (observe oa) (setupComparedProgram (phase := phase) D) 0 := by
  unfold observe
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact ⟨trivial, trivial⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, WriterT.run_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    have hk (u : (LocalSpec C).Range t) := ih u _ (h.2 u)
    rcases t with t | (q | x)
    · simp only [WriterT.run_liftM, bind_map_left]
      rw [adversary_query]
      constructor
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨Or.inl (by simp [setupComparedWorldCall, setupComparedCall]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).1
        simp only [setupComparedCall, setupComparedWorldCall, ↓reduceIte] at hu ⊢
        exact hu
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [setupComparedProgram]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).2
        simp only [setupComparedProgram, ↓reduceIte] at hu ⊢
        exact hu
    · simp only [WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, WriterT.run_pure, bind_assoc,
        bind_map_left, map_pure, pure_bind]
      rw [adversary_hashQuery]
      constructor
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨by simpa [setupComparedWorldCall, setupComparedCall] using h.1, fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).1
        simp only [setupComparedCall, setupComparedWorldCall] at hu ⊢
        exact hu
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [setupComparedProgram]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).2
        simp only [setupComparedProgram, ↓reduceIte] at hu ⊢
        exact hu
    · simp only [WriterT.run_liftM, bind_map_left]
      rw [adversary_query]
      constructor
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨Or.inl (by simp [setupComparedWorldCall, setupComparedCall]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).1
        simp only [setupComparedCall, setupComparedWorldCall, ↓reduceIte] at hu ⊢
        exact hu
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [setupComparedProgram]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).2
        simp only [setupComparedProgram, ↓reduceIte] at hu ⊢
        exact hu

theorem setupComparedCall_counted (phase : Phase) (D : C.Coalition) (t : (LocalSpec C).Domain)
    (h : setupComparedCall (phase := phase) D t) : Counted t := by
  rcases t with t | (q | x)
  · exact h.elim
  · cases q <;> simp_all [setupComparedCall, SetupComparedCell, Counted]
  · exact h.elim

theorem isQueryBoundP_setupCompared_of_counted (phase : Phase) (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) : IsQueryBoundP oa (setupComparedCall (phase := phase) D) n :=
  h.of_imp (setupComparedCall_counted (phase := phase) D)

theorem isQueryBoundP_setupCompared_hash (phase : Phase) (D : C.Coalition) (q : Query C) :
    IsQueryBoundP (liftComp (hashQuery q) (LocalSpec C)) (setupComparedCall (phase := phase) D)
      (if SetupComparedCell (phase := phase) D q then 1 else 0) := by
  have e : liftComp (hashQuery q) (LocalSpec C) =
      (liftM ((LocalSpec C).query (.inr (.inl q))) : OracleComp (LocalSpec C) _) >>= pure := by
    rw [bind_pure]
    rfl
  rw [e]
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨?_, fun _ => trivial⟩
  by_cases hc : SetupComparedCell (phase := phase) D q <;> simp [setupComparedCall, hc]

theorem seedGenIsQueryBoundP_sequenceFin_sum {κ β : Type} {spec : OracleSpec κ} {p : κ → Prop} [DecidablePred p] :
    ∀ {N : ℕ} (f : Fin N → OracleComp spec β) (b : Fin N → ℕ), (∀ i, IsQueryBoundP (f i) p (b i)) →
      IsQueryBoundP (OverPermutation.sequenceFin f) p (∑ i, b i)
  | 0, f, b, _ => by simp [OverPermutation.sequenceFin]
  | N + 1, f, b, h => by
    simp only [OverPermutation.sequenceFin]
    rw [Fin.sum_univ_succ, ← Nat.add_zero (∑ i : Fin N, b i.succ)]
    exact isQueryBoundP_bind (h 0) fun _ _ => isQueryBoundP_bind
      (seedGenIsQueryBoundP_sequenceFin_sum (fun i : Fin N => f i.succ) (fun i => b i.succ) fun i => h i.succ)
      fun _ _ => isQueryBoundP_pure _ _ 0

theorem seedGenIsQueryBoundP_listMapM {κ α β : Type} {spec : OracleSpec κ} {p : κ → Prop} [DecidablePred p]
    {f : α → OracleComp spec β} {k : α → ℕ} (h : ∀ x, IsQueryBoundP (f x) p (k x)) (xs : List α) :
    IsQueryBoundP (xs.mapM f) p ((xs.map k).sum) := by
  induction xs with
  | nil => simp [List.mapM_nil]
  | cons a xs ih =>
    rw [List.mapM_cons, List.map_cons, List.sum_cons, ← Nat.add_zero (xs.map k).sum]
    exact isQueryBoundP_bind (h a) fun y _ => isQueryBoundP_bind ih fun _ _ => isQueryBoundP_pure _ _ 0

theorem isQueryBoundP_setupCompared_derive (phase : Phase) (D : C.Coalition) (i : C.Party)
    (view : C.Party → Parts C) :
    IsQueryBoundP (liftComp (deriveKeys phase i view) (LocalSpec C)) (setupComparedCall (phase := phase) D) 0 := by
  have hd (kind : KeyKind) (values : List HashOutput) :
      IsQueryBoundP (liftComp (hashQuery (C := C) (.derive phase kind values)) (LocalSpec C))
        (setupComparedCall (phase := phase) D) 0 := by
    simpa [SetupComparedCell] using isQueryBoundP_setupCompared_hash (phase := phase) D (.derive phase kind values)
  have hterm : IsQueryBoundP (liftComp (C.terms.mapM fun T => if i ∈ C.holders T then
      hashQuery (C := C) (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
      else pure 0) (LocalSpec C)) (setupComparedCall (phase := phase) D) 0 := by
    rw [seedGen_liftComp_mapM]
    have := seedGenIsQueryBoundP_listMapM (p := setupComparedCall (phase := phase) D) (k := fun _ => 0)
      (f := fun T => liftComp (if i ∈ C.holders T then hashQuery (C := C) (.derive phase .term
        ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)) else pure 0) (LocalSpec C))
      (fun T => by
        by_cases hT : i ∈ C.holders T
        · rw [ite_eq_left hT]; exact hd _ _
        · rw [ite_eq_right hT, liftComp_pure]; trivial) C.terms
    simpa using this
  have hpair : IsQueryBoundP (liftComp (C.parties.mapM fun j => if h : j = i then pure 0 else
      hashQuery (C := C) (.derive phase .pair [(view (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
        (view (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) (LocalSpec C))
      (setupComparedCall (phase := phase) D) 0 := by
    rw [seedGen_liftComp_mapM]
    have := seedGenIsQueryBoundP_listMapM (p := setupComparedCall (phase := phase) D) (k := fun _ => 0)
      (f := fun j => liftComp (if h : j = i then pure 0 else hashQuery (C := C) (.derive phase .pair
        [(view (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
          (view (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) (LocalSpec C))
      (fun j => by
        by_cases hj : j = i
        · rw [dite_eq_left hj, liftComp_pure]; trivial
        · rw [dite_eq_right hj]; exact hd _ _) C.parties
    simpa using this
  unfold deriveKeys
  dsimp only
  by_cases hp : phase = .seedGen
  · rw [ite_eq_left hp, liftComp_bind, ← Nat.zero_add 0]
    refine isQueryBoundP_bind (hd _ _) fun _ _ => ?_
    rw [liftComp_bind, ← Nat.zero_add 0]
    exact isQueryBoundP_bind hterm fun _ _ => by
      rw [liftComp_bind, ← Nat.zero_add 0]
      exact isQueryBoundP_bind hpair fun _ _ => by rw [liftComp_pure]; trivial
  · rw [ite_eq_right hp, pure_bind, liftComp_bind, ← Nat.zero_add 0]
    exact isQueryBoundP_bind hterm fun _ _ => by
      rw [liftComp_bind, ← Nat.zero_add 0]
      exact isQueryBoundP_bind hpair fun _ _ => by rw [liftComp_pure]; trivial

theorem isQueryBoundP_setupCompared_hashes (phase : Phase) (D : C.Coalition) (qs : C.Party → Query C) (b : ℕ)
    (hb : ((C.parties.map fun j => if SetupComparedCell (phase := phase) D (qs j) then 1 else 0).sum) ≤ b) :
    IsQueryBoundP (liftComp (C.parties.mapM fun j => hashQuery (qs j)) (LocalSpec C)) (setupComparedCall (phase := phase) D) b := by
  rw [seedGen_liftComp_mapM]
  exact (seedGenIsQueryBoundP_listMapM (fun j => isQueryBoundP_setupCompared_hash (phase := phase) D (qs j)) C.parties).mono hb

theorem seedGenParties_sum_le_card (f : C.Party → ℕ) (hf : ∀ j, f j ≤ 1) :
    (C.parties.map f).sum ≤ C.n := by
  have h := List.sum_le_length_nsmul (C.parties.map f) 1 (by simpa using fun j _ => hf j)
  simpa [Committee.parties] using h

theorem seedGenParties_sum_corrupt (D : C.Coalition) :
    (C.parties.map fun j => if j ∈ D.1 then 1 else 0).sum = D.1.card := by
  simp only [Committee.parties]
  rw [← Fin.sum_univ_def]
  simp

theorem isQueryBoundP_setupCompared_revealCompute (phase : Phase) (D : C.Coalition) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) :
    IsQueryBoundP (setupRevealCompute phase i own committed revealed) (setupComparedCall (phase := phase) D) (D.1.card + C.n) := by
  unfold setupRevealCompute
  split
  · trivial
  · refine isQueryBoundP_bind (isQueryBoundP_setupCompared_hashes (phase := phase) D _ D.1.card ?_) fun _ _ => ?_
    · rw [← seedGenParties_sum_corrupt D]
      apply le_of_eq
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j ∈ D.1 <;> simp [SetupComparedCell, hj]
    · rw [← Nat.zero_add C.n]
      split
      · trivial
      · exact isQueryBoundP_bind (isQueryBoundP_setupCompared_derive (phase := phase) D _ _) fun _ _ => by
          rw [← Nat.add_zero C.n]
          refine isQueryBoundP_bind ?_ fun _ _ => trivial
          unfold sharedQueries
          exact isQueryBoundP_setupCompared_hashes (phase := phase) D _ C.n (seedGenParties_sum_le_card _ fun j => by split <;> omega)

theorem isQueryBoundP_setupCompared_revealComputations (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    IsQueryBoundP (setupRevealComputations phase D parts committed sent) (setupComparedCall (phase := phase) D) (C.n * C.n) := by
  unfold setupRevealComputations
  refine (seedGenIsQueryBoundP_sequenceFin_sum _ (fun i => if i ∈ D.1 then 0 else D.1.card + C.n) fun i => ?_).mono ?_
  · split
    · trivial
    · rename_i h
      rw [ite_eq_right (fun hi => h (Or.inl hi))]
      exact isQueryBoundP_setupCompared_revealCompute (phase := phase) D i (parts i) (committed i) _
  · rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, smul_eq_mul]
    have hc : (Finset.univ.filter fun i => i ∉ D.1).card = C.n - D.1.card := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp [Committee.n]
    rw [hc]
    have hd : D.1.card ≤ C.n := by
      have := Finset.card_le_univ D.1
      simpa [Committee.n] using this
    obtain ⟨e, he⟩ : ∃ e, C.n = D.1.card + e := ⟨C.n - D.1.card, by omega⟩
    rw [he, Nat.add_sub_cancel_left]
    nlinarith

theorem isQueryBoundP_setupCompared_post (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (state : A.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    IsQueryBoundP (setupPostTraced (phase := phase) D A state parts committed) (setupComparedCall (phase := phase) D) (step + (C.n * C.n + step)) := by
  unfold setupPostTraced
  split
  · trivial
  · refine isQueryBoundP_bind (isQueryBoundP_setupCompared_of_counted (phase := phase) D _ _ (hround _ _)) fun r _ => ?_
    refine isQueryBoundP_bind (isQueryBoundP_setupCompared_revealComputations (phase := phase) D parts committed r.2) fun data _ => ?_
    rw [← Nat.add_zero step]
    refine isQueryBoundP_bind ?_ fun _ _ => trivial
    unfold setupFinishLocal
    split
    · trivial
    · rw [← Nat.add_zero step]
      exact isQueryBoundP_bind (isQueryBoundP_setupCompared_of_counted (phase := phase) D _ _ (hround _ _)) fun _ _ => trivial

theorem isQueryBoundP_setupCompared_program (phase : Phase) (D : C.Coalition) (q : Query C) (v : HashOutput)
    (hq : ¬ SetupComparedCell (phase := phase) D q) :
    IsQueryBoundP (program q v) (setupComparedWorldCall (phase := phase) D) 0 ∧ IsQueryBoundP (program q v) (setupComparedProgram (phase := phase) D) 0 := by
  have e : program q v = (liftM ((WorldSpec C).query (.inl (.inr (q, v)))) : OracleComp (WorldSpec C) _) >>= pure := by
    rw [bind_pure]
    rfl
  rw [e]
  exact ⟨(isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [setupComparedWorldCall]), fun _ => trivial⟩,
    (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simpa [setupComparedProgram] using hq), fun _ => trivial⟩⟩

theorem isQueryBoundP_setupCompared_programs (phase : Phase) {ι : Type} (D : C.Coalition) (l : List ι) (q : ι → Query C)
    (v : ι → HashOutput) (hq : ∀ i, ¬ SetupComparedCell (phase := phase) D (q i)) :
    IsQueryBoundP (l.mapM fun i => program (q i) (v i)) (setupComparedWorldCall (phase := phase) D) 0 ∧
      IsQueryBoundP (l.mapM fun i => program (q i) (v i)) (setupComparedProgram (phase := phase) D) 0 := by
  constructor
  · simpa using seedGenIsQueryBoundP_listMapM (k := fun _ => 0)
      (fun i => (isQueryBoundP_setupCompared_program (phase := phase) D (q i) (v i) (hq i)).1) l
  · simpa using seedGenIsQueryBoundP_listMapM (k := fun _ => 0)
      (fun i => (isQueryBoundP_setupCompared_program (phase := phase) D (q i) (v i) (hq i)).2) l

/-- The programming of `P` makes no compared call and no compared program. -/
theorem isQueryBoundP_setupCompared_programParameter (phase : Phase) (D : C.Coalition) (q : Query C) (v : HashOutput)
    (hq : ¬ SetupComparedCell phase D q) :
    IsQueryBoundP (programParameter phase q v) (setupComparedWorldCall phase D) 0 ∧
      IsQueryBoundP (programParameter phase q v) (setupComparedProgram phase D) 0 := by
  cases phase
  · exact isQueryBoundP_setupCompared_program (phase := .seedGen) D q v hq
  · exact ⟨trivial, trivial⟩

theorem isQueryBoundP_setupCompared_programOk (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) :
    IsQueryBoundP (setupProgramOk (phase := phase) D parts log sent parameter seeds pairs high) (setupComparedWorldCall (phase := phase) D) 0 ∧
      IsQueryBoundP (setupProgramOk (phase := phase) D parts log sent parameter seeds pairs high) (setupComparedProgram (phase := phase) D) 0 := by
  have hd (k : KeyKind) (values : List HashOutput) : ¬ SetupComparedCell (phase := phase) D (.derive phase k values) := by
    simp [SetupComparedCell]
  have h₁ := isQueryBoundP_setupCompared_programParameter phase D (.derive phase .parameter (C.parties.map fun j =>
    (setupProgramView phase D parts log sent (seedGenFirstHonest D Finset.univ) j).parameter))
    (seedGenFullParameter high parameter) (hd _ _)
  have h₂ := isQueryBoundP_setupCompared_programs (phase := phase) D (seedGenKnownCoordinates D)
    (setupTermProgrammingInput phase D (setupProgramView phase D parts log sent)) seeds (fun _ => hd _ _)
  have h₃ := isQueryBoundP_setupCompared_programs (phase := phase) D (seedGenCrossCoordinates D)
    (setupPairProgrammingInput phase D (setupProgramView phase D parts log sent)) pairs (fun _ => hd _ _)
  unfold setupProgramOk
  constructor
  · exact isQueryBoundP_bind (m := 0) h₁.1 fun _ _ => isQueryBoundP_bind (m := 0) h₂.1 fun _ _ =>
      isQueryBoundP_bind (m := 0) h₃.1 fun _ _ => trivial
  · exact isQueryBoundP_bind (m := 0) h₁.2 fun _ _ => isQueryBoundP_bind (m := 0) h₂.2 fun _ _ =>
      isQueryBoundP_bind (m := 0) h₃.2 fun _ _ => trivial

theorem isQueryBoundP_setupCompared_commitments (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) :
    IsQueryBoundP (setupInitialCommitments phase D parts) (setupComparedCall (phase := phase) D) 0 := by
  unfold setupInitialCommitments
  refine (seedGenIsQueryBoundP_sequenceFin_sum _ (fun _ => 0) fun i => ?_).mono (by simp)
  split
  · trivial
  · rename_i hi
    exact isQueryBoundP_setupCompared_hashes (phase := phase) D _ 0 (by simp [SetupComparedCell, hi])

theorem isQueryBoundP_setupCompared_sample (phase : Phase) (D : C.Coalition) {β : Type} (p : ProbComp β) :
    IsQueryBoundP (free (liftComp p (LocalSpec C))) (setupComparedWorldCall (phase := phase) D) 0 ∧
      IsQueryBoundP (free (liftComp p (LocalSpec C))) (setupComparedProgram (phase := phase) D) 0 :=
  isQueryBoundP_free_setupCompared (phase := phase) D _ 0 (isQueryBoundP_setupCompared_of_counted (phase := phase) D _ 0 (isQueryBoundP_liftComp_counted p))

theorem isQueryBoundP_setupCompared_knownGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (setupKnownGame (phase := phase) D A x z) (setupComparedWorldCall (phase := phase) D) (start + 3 * step + C.n * C.n) ∧
      IsQueryBoundP (setupKnownGame (phase := phase) D A x z) (setupComparedProgram (phase := phase) D) 0 := by
  have o₁ := isQueryBoundP_observe_setupCompared (phase := phase) D _ _ (isQueryBoundP_setupCompared_of_counted (phase := phase) D _ _ (hstart (corruptInputs D x) z))
  unfold setupKnownGame
  constructor
  · refine (isQueryBoundP_bind o₁.1 fun _ _ => isQueryBoundP_bind (isQueryBoundP_setupCompared_sample (phase := phase) D _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_setupCompared_sample (phase := phase) D _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_setupCompared (phase := phase) D _ _ (isQueryBoundP_setupCompared_commitments (phase := phase) D _)).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_observe_setupCompared (phase := phase) D _ _
        (isQueryBoundP_setupCompared_of_counted (phase := phase) D _ _ (hround _ _))).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_setupCompared_sample (phase := phase) D _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_setupCompared_programOk (phase := phase) D _ _ _ _ _ _ _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_setupCompared (phase := phase) D _ _
        (isQueryBoundP_setupCompared_post (phase := phase) D A step hround _ _ _)).1 fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by ring_nf; omega)
  · refine (isQueryBoundP_bind o₁.2 fun _ _ => isQueryBoundP_bind (isQueryBoundP_setupCompared_sample (phase := phase) D _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_setupCompared_sample (phase := phase) D _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_setupCompared (phase := phase) D _ _ (isQueryBoundP_setupCompared_commitments (phase := phase) D _)).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_observe_setupCompared (phase := phase) D _ _
        (isQueryBoundP_setupCompared_of_counted (phase := phase) D _ _ (hround _ _))).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_setupCompared_sample (phase := phase) D _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_setupCompared_programOk (phase := phase) D _ _ _ _ _ _ _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_setupCompared (phase := phase) D _ _
        (isQueryBoundP_setupCompared_post (phase := phase) D A step hround _ _ _)).2 fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by simp)

/-- A cell that was empty in `b` holds its target answer in `s`. -/
def SeedGenTargetHit (target : Query C → Option HashOutput) (b s : HashCache C) : Prop :=
  ∃ x c, target x = some c ∧ b x = none ∧ s x = some c

theorem setupTarget_hash_step (phase : Phase) (prims : Primitives) {D : C.Coalition} {β : Type} (target : Query C → Option HashOutput)
    (htarget : ∀ x, target x ≠ none → SetupComparedCell (phase := phase) D x) (b : HashCache C) (q : Query C)
    (s : HashCache C) (m : ℕ) (hs : ¬ SeedGenTargetHit target b s)
    (g : HashOutput → HashCache C → ProbComp (β × HashCache C))
    (hg : ∀ u s', ¬ SeedGenTargetHit target b s' →
      Pr{let z ← g u s'}[SeedGenTargetHit target b z.2] ≤ (m : ℝ≥0∞) / Fintype.card HashOutput)
    (hg' : SetupComparedCell (phase := phase) D q → 0 < m ∧ ∀ u s', ¬ SeedGenTargetHit target b s' →
      Pr{let z ← g u s'}[SeedGenTargetHit target b z.2] ≤ ((m - 1 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput) :
    Pr{let z ← (hashAnswer prims q).run s >>= fun p => g p.1 p.2}[SeedGenTargetHit target b z.2] ≤
      (m : ℝ≥0∞) / Fintype.card HashOutput := by
  have hnew (u : HashOutput) (hsq : s q = none) (hh : SeedGenTargetHit target b (s.cacheQuery q u)) :
      target q = some u := by
    obtain ⟨x, c, hx, hb, hc⟩ := hh
    by_cases hxq : x = q
    · subst hxq
      rw [QueryCache.cacheQuery_self] at hc
      rw [hx, Option.some.inj hc]
    · rw [QueryCache.cacheQuery_of_ne s _ hxq] at hc
      exact absurd ⟨x, c, hx, hb, hc⟩ hs
  by_cases hfix : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hfix
    rw [hashAnswer_of_isFixed prims hi, StateT.run_pure, pure_bind]
    exact hg _ s hs
  · rw [hashAnswer_of_not_isFixed prims hfix]
    cases hsq : s q with
    | some u =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hsq, pure_bind]
      exact hg u s hs
    | none =>
      have heq : ((Query C →ₒ HashOutput).randomOracle q).run s =
          (fun u => (u, s.cacheQuery q u)) <$> ($ᵗ HashOutput) := by
        rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hsq]
        rfl
      rw [heq, bind_map_left]
      by_cases hc : SetupComparedCell (phase := phase) D q
      · obtain ⟨hm, hg''⟩ := hg' hc
        have h := prEvent_bind_le_prEvent_add_of_support ($ᵗ HashOutput)
          (fun u => g u (s.cacheQuery q u))
          (fun u => SeedGenTargetHit target b (s.cacheQuery q u))
          (fun z => SeedGenTargetHit target b z.2)
          (ε := ((m - 1 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput)
          (fun u _ hu => hg'' u _ hu)
        have hfresh : Pr{let u ← $ᵗ HashOutput}[SeedGenTargetHit target b (s.cacheQuery q u)] ≤
            (1 : ℝ≥0∞) / Fintype.card HashOutput := by
          refine (prEvent_mono _ _ (fun u => target q = some u) fun u hu => hnew u hsq hu).trans ?_
          cases ht : target q with
          | none => simp
          | some c =>
            simp only [Option.some.injEq]
            rw [SampleableType.prEvent_uniformSample]
            apply ENNReal.div_le_div_right
            exact_mod_cast (Finset.card_le_one.mpr fun a ha b hb => by
              simp only [Finset.mem_filter] at ha hb
              exact ha.2.symm.trans hb.2)
        refine (h.trans (add_le_add hfresh le_rfl)).trans (le_of_eq ?_)
        rw [← ENNReal.add_div]
        congr 1
        norm_cast
        omega
      · refine prEvent_bind_le_of_forall_le _ _ _ fun u => hg u _ ?_
        intro hh
        exact hc (htarget q (by rw [hnew u hsq hh]; simp))

/-- A local computation with at most `m` compared calls fills a target cell with its target answer
with probability at most `m / 2^256`. -/
theorem setupTarget_local (phase : Phase) (prims : Primitives) {D : C.Coalition} (target : Query C → Option HashOutput)
    (htarget : ∀ x, target x ≠ none → SetupComparedCell (phase := phase) D x) (b : HashCache C) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∀ m s, IsQueryBoundP oa (setupComparedCall (phase := phase) D) m → ¬ SeedGenTargetHit target b s →
      Pr{let z ← (simulateQ (localAnswer prims) oa).run s}[SeedGenTargetHit target b z.2] ≤
        (m : ℝ≥0∞) / Fintype.card HashOutput := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m s _ hs
    simp [hs]
  | query_bind t f ih =>
    intro m s hm hs
    rw [isQueryBoundP_query_bind_iff] at hm
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind]
    rcases t with n | q | x
    · have heq : (localAnswer (C := C) prims (.inl n)).run s =
          (fun u => (u, s)) <$> (OracleComp.lift (OracleSpec.query (spec := unifSpec) n)) := by
        simp [localAnswer, unifFwdImpl]
      change Pr{let z ← (localAnswer prims (.inl n)).run s >>= fun p => (simulateQ (localAnswer prims) (f p.1)).run p.2}[
        SeedGenTargetHit target b z.2] ≤ _
      rw [heq]
      erw [bind_map_left]
      refine prEvent_bind_le_of_forall_le _ _ _ fun u => ih u m s ?_ hs
      simpa [setupComparedCall] using hm.2 u
    · change Pr{let z ← (hashAnswer prims q).run s >>= fun p => (simulateQ (localAnswer prims) (f p.1)).run p.2}[
        SeedGenTargetHit target b z.2] ≤ _
      refine setupTarget_hash_step (phase := phase) prims target htarget b q s m hs
        (fun u s' => (simulateQ (localAnswer prims) (f u)).run s') (fun u s' h => ?_) (fun hc => ?_)
      · have hu := hm.2 u
        simp only [setupComparedCall] at hu
        by_cases hct : SetupComparedCell (phase := phase) D q
        · erw [ite_eq_left hct] at hu
          exact (ih u (m - 1) s' hu h).trans (ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le m 1) _)
        · erw [ite_eq_right hct] at hu
          exact ih u m s' hu h
      · have hm' := hm.1.resolve_left (by simpa [setupComparedCall] using hc)
        refine ⟨hm', fun u s' h => ?_⟩
        have hu := hm.2 u
        simp only [setupComparedCall] at hu
        erw [ite_eq_left hc] at hu
        exact ih u (m - 1) s' hu h
    · change Pr{let z ← (prgAnswer prims x).run s >>= fun p => (simulateQ (localAnswer prims) (f p.1)).run p.2}[
        SeedGenTargetHit target b z.2] ≤ _
      simp only [prgAnswer, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      refine setupTarget_hash_step (phase := phase) prims target htarget b (.streamKey x.2.1) s m hs
        (fun u s' => (simulateQ (localAnswer prims) (f (prims.aes.eval (truncateHash u) x.2.2))).run s')
        (fun u s' h => ih _ m s' ?_ h) (fun hc => by simp [SetupComparedCell] at hc)
      simpa [setupComparedCall] using hm.2 _

/-- Every cell that an observed computation fills is logged, except a stream key. -/
theorem seedGenObserve_new_logged {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) (observe oa)).run s) →
      ∀ q, s q = none → z.2 q ≠ none → (∃ y, (q, y) ∈ z.1.2) ∨ ∃ k, q = .streamKey k := by
  unfold observe
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz q hq hz'
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact absurd hq hz'
  | query_bind t k ih =>
    intro s z hz q hq hz'
    simp only [simulateQ_bind, WriterT.run_bind, StateT.run_bind, support_bind, Set.mem_iUnion,
      simulateQ_map, StateT.run_map, support_map, Set.mem_image, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map] at hz
    obtain ⟨p, hp, w, hw, rfl⟩ := hz
    cases hpq : p.2 q with
    | none =>
      rcases ih _ p.2 w hw q hpq hz' with ⟨y, hy⟩ | h
      · exact Or.inl ⟨y, List.mem_append_right _ hy⟩
      · exact Or.inr h
    | some v =>
      rcases t with t | (q' | x)
      · simp at hp
        obtain ⟨a, b, hp', rfl⟩ := hp
        rw [simulateQ_world_adversary] at hp'
        simp [localAnswer, unifFwdImpl] at hp'
        obtain ⟨u, rfl⟩ := hp'
        simp only at hpq
        rw [hq] at hpq
        cases hpq
      · simp [simulateQ_world_adversary] at hp
        obtain ⟨a, b, hp', rfl⟩ := hp
        have he : (simulateQ (localAnswer prims) (liftM (hashQuery q') : OracleComp (LocalSpec C) _)).run s =
            (hashAnswer prims q').run s :=
          congrArg (fun m => StateT.run m s) (simulateQ_localAnswer_hash prims q')
        rw [he] at hp'
        by_cases hqq : q = q'
        · subst hqq
          exact Or.inl ⟨a, List.mem_append_left _ (by simp)⟩
        · by_cases hfix : IsFixed q'
          · obtain ⟨input, rfl, hi⟩ := hfix
            rw [hashAnswer_of_isFixed prims hi] at hp'
            simp at hp'
            obtain ⟨-, rfl⟩ := hp'
            simp only at hpq
            rw [hq] at hpq
            cases hpq
          · rw [hashAnswer_of_not_isFixed prims hfix] at hp'
            have := (randomOracle_support q' s (a, b) hp').2.2 q hqq
            simp only at hpq
            rw [this, hq] at hpq
            cases hpq
      · simp at hp
        obtain ⟨a, b, hp', rfl⟩ := hp
        rw [simulateQ_world_adversary] at hp'
        simp only [OracleComp.lift, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query] at hp'
        erw [id_map] at hp'
        change (a, b) ∈ support ((prgAnswer prims x).run s) at hp'
        unfold prgAnswer at hp'
        simp only [StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hp'
        obtain ⟨p'', hp'', he⟩ := hp'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        by_cases hqq : q = .streamKey x.2.1
        · exact Or.inr ⟨_, hqq⟩
        · have hfix : ¬ IsFixed (Query.streamKey (C := C) x.2.1) := by simp [IsFixed]
          rw [hashAnswer_of_not_isFixed prims hfix] at hp''
          have := (randomOracle_support _ s p'' hp'').2.2 q hqq
          simp only at hpq
          rw [this, hq] at hpq
          cases hpq

theorem localAnswer_setupCompared_unchanged (phase : Phase) (prims : Primitives) (D : C.Coalition) (t : (LocalSpec C).Domain)
    (ht : ¬ setupComparedCall (phase := phase) D t) (s : HashCache C) (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run s)) (x : Query C) (hx : SetupComparedCell (phase := phase) D x) :
    p.2 x = s x := by
  rcases t with n | q | y
  · simp [localAnswer, unifFwdImpl] at hp
    obtain ⟨u, rfl⟩ := hp
    rfl
  · have hxq : x ≠ q := fun he => ht (he ▸ hx)
    change p ∈ support ((hashAnswer prims q).run s) at hp
    by_cases hfix : IsFixed q
    · obtain ⟨input, rfl, hi⟩ := hfix
      rw [hashAnswer_of_isFixed prims hi] at hp
      simp at hp
      rw [hp]
    · rw [hashAnswer_of_not_isFixed prims hfix] at hp
      exact (randomOracle_support q s p hp).2.2 x hxq
  · change p ∈ support ((prgAnswer prims y).run s) at hp
    unfold prgAnswer at hp
    rw [StateT.run_bind] at hp
    simp only [support_bind] at hp
    obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
    simp only [StateT.run_pure, support_pure] at hp
    subst hp
    have hxq : x ≠ .streamKey y.2.1 := by
      rintro rfl
      simp [SetupComparedCell] at hx
    have hfix : ¬ IsFixed (Query.streamKey (C := C) y.2.1) := by simp [IsFixed]
    rw [hashAnswer_of_not_isFixed prims hfix] at hp'
    exact (randomOracle_support _ s p' hp').2.2 x hxq

/-- A world computation with no compared call and no compared programming leaves every compared
cell unchanged. -/
theorem setupCompared_unchanged (phase : Phase) (prims : Primitives) {D : C.Coalition} {α : Type} (oa : OracleComp (WorldSpec C) α) :
    IsQueryBoundP oa (setupComparedWorldCall (phase := phase) D) 0 → IsQueryBoundP oa (setupComparedProgram (phase := phase) D) 0 →
      ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) oa).run s) →
        ∀ x, SetupComparedCell (phase := phase) D x → z.2 x = s x := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ _ s z hz x _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t f ih =>
    intro hm hp s z hz x hx
    rw [isQueryBoundP_query_bind_iff] at hm hp
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp', hz⟩ := hz
    have hc : ¬ setupComparedWorldCall (phase := phase) D t := fun h => by simpa using hm.1.resolve_left (not_not.mpr h)
    have hpr : ¬ setupComparedProgram (phase := phase) D t := fun h => by simpa using hp.1.resolve_left (not_not.mpr h)
    have hmu := hm.2 p.1
    have hpu := hp.2 p.1
    simp only [ite_eq_right hc, ite_eq_right hpr] at hmu hpu
    rw [ih p.1 hmu hpu p.2 z hz x hx]
    rcases t with (t | y) | t
    · exact localAnswer_setupCompared_unchanged (phase := phase) prims D t hc s p hp' x hx
    · have hy : ¬ SetupComparedCell (phase := phase) D y.1 := hpr
      change p ∈ support ((programAnswer y).run s) at hp'
      simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hp'
      split_ifs at hp'
      · simp only [StateT.run_pure, support_pure] at hp'
        rw [hp']
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure] at hp'
        rw [hp']
        exact QueryCache.cacheQuery_of_ne s _ (fun he => hy (he ▸ hx))
    · exact localAnswer_setupCompared_unchanged (phase := phase) prims D t hc s p hp' x hx

/-- The transcript before the last two rounds. -/
structure SeedGenKnownPre (C : Committee) (E σ : Type) where
  parameter : PublicParameter
  seeds : C.Term → HashOutput
  pairs : C.Pair → HashOutput
  parts : C.Party → Parts C
  log : CallLog C
  sent : C.Party → Mail C E
  commitments : C.Party → List HashOutput
  ok : Bool
  state : σ

/-- The common game up to the programming block. -/
def setupKnownPrefix (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) : OracleComp (WorldSpec C) (SeedGenKnownPre C E A.State) := do
  let (state, log) ← observe (A.start (corruptInputs D x) z)
  let (parameter, seeds, pairs) ← free (liftComp (setupDealerSamples (C := C) phase) (LocalSpec C))
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C)))
    (LocalSpec C))
  let commitments ← free (setupInitialCommitments phase D parts)
  let ((st, sent), calls) ← observe (A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    commitOutbox i (commitments i) c else none)
  let high ← free (liftComp (setupHighSample phase) (LocalSpec C))
  let ok ← setupProgramOk phase D parts (log ++ calls) sent parameter seeds pairs high
  pure ⟨parameter, seeds, pairs, parts, log ++ calls, sent, commitments, ok, st⟩

theorem setupKnownGame_eq_prefix (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    setupKnownGame (phase := phase) D A x z = setupKnownPrefix (phase := phase) D A x z >>= fun pre =>
      free (setupPostTraced (phase := phase) D A pre.state pre.parts (setupCommitInbox phase D pre.parts pre.commitments pre.sent)) >>=
        fun r => pure ⟨pre.parameter, pre.seeds, pre.pairs, pre.parts, pre.log, pre.sent, pre.commitments, pre.ok,
          r.1, r.2.1, r.2.2.1, r.2.2.2⟩ := by
  unfold setupKnownGame setupKnownPrefix
  simp only [bind_assoc, pure_bind]

/-- Before the last two rounds, every filled commitment cell of a corrupt sender is logged. -/
theorem setupKnownPrefix_unlogged (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (w : SeedGenKnownPre C E A.State × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (setupKnownPrefix (phase := phase) D A x z)).run ∅))
    (j i : C.Party) (reveal : List HashOutput) (hj : j ∈ D.1)
    (hlog : ∀ y, (Query.commit (C := C) phase j i reveal, y) ∉ w.1.log) :
    w.2 (.commit phase j i reveal) = none := by
  have hx : SetupComparedCell (phase := phase) D (.commit phase j i reveal) := ⟨rfl, hj⟩
  have hns : ¬ ∃ k, Query.commit (C := C) phase j i reveal = .streamKey k := by
    rintro ⟨k, hk⟩
    cases hk
  unfold setupKnownPrefix at hw
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hw
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, p₄, hp₄, p₅, hp₅, p₆, hp₆, hfin⟩ := hw
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
  subst hfin
  simp only at hlog ⊢
  have n₀ : p₀.2 (.commit phase j i reveal) = none := by
    by_contra hne
    rcases seedGenObserve_new_logged prims _ ∅ p₀ hp₀ _ rfl hne with ⟨y, hy⟩ | h
    · exact hlog y (List.mem_append_left _ hy)
    · exact hns h
  have u₁ := setupCompared_unchanged (phase := phase) prims _ (isQueryBoundP_setupCompared_sample (phase := phase) D _).1
    (isQueryBoundP_setupCompared_sample (phase := phase) D _).2 _ p₁ hp₁ _ hx
  have u₂ := setupCompared_unchanged (phase := phase) prims _ (isQueryBoundP_setupCompared_sample (phase := phase) D _).1
    (isQueryBoundP_setupCompared_sample (phase := phase) D _).2 _ p₂ hp₂ _ hx
  have hcm := isQueryBoundP_free_setupCompared (phase := phase) D _ 0 (isQueryBoundP_setupCompared_commitments (phase := phase) D p₂.1)
  have u₃ := setupCompared_unchanged (phase := phase) prims _ hcm.1 hcm.2 _ p₃ hp₃ _ hx
  have n₄ : p₄.2 (.commit phase j i reveal) = none := by
    by_contra hne
    rcases seedGenObserve_new_logged prims _ _ p₄ hp₄ _ (by rw [u₃, u₂, u₁, n₀]) hne with ⟨y, hy⟩ | h
    · exact hlog y (List.mem_append_right _ hy)
    · exact hns h
  have u₅ := setupCompared_unchanged (phase := phase) prims _ (isQueryBoundP_setupCompared_sample (phase := phase) D _).1
    (isQueryBoundP_setupCompared_sample (phase := phase) D _).2 _ p₅ hp₅ _ hx
  have hpo := isQueryBoundP_setupCompared_programOk (phase := phase) (E := E) D p₂.1 (p₀.1.2 ++ p₄.1.2) p₄.1.1.2 p₁.1.1 p₁.1.2.1
    p₁.1.2.2 p₅.1
  have u₆ := setupCompared_unchanged (phase := phase) prims _ hpo.1 hpo.2 _ p₆ hp₆ _ hx
  rw [u₆, u₅, n₄]

/-- The local calls whose random-oracle input is `x`. -/
def seedGenCellCall (x : Query C) : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => q = x
  | _ => False

/-- A local computation that never calls `x` leaves the cell `x` unchanged, unless it is a stream key. -/
theorem seedGenCell_unchanged (x : Query C) (hx : ∀ k, x ≠ .streamKey k) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP oa (seedGenCellCall x) 0 → ∀ s z, z ∈ support ((simulateQ (localAnswer prims) oa).run s) →
      z.2 x = s x := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ s z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t f ih =>
    intro hm s z hz
    rw [isQueryBoundP_query_bind_iff] at hm
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    have hc : ¬ seedGenCellCall x t := fun h => by simpa using hm.1.resolve_left (not_not.mpr h)
    have hmu := hm.2 p.1
    simp only [ite_eq_right hc] at hmu
    rw [ih p.1 hmu p.2 z hz]
    rcases t with n | q | y
    · simp [localAnswer, unifFwdImpl] at hp
      obtain ⟨u, rfl⟩ := hp
      rfl
    · have hxq : x ≠ q := fun he => hc (by simp [seedGenCellCall, he])
      change p ∈ support ((hashAnswer prims q).run s) at hp
      by_cases hfix : IsFixed q
      · obtain ⟨input, rfl, hi⟩ := hfix
        rw [hashAnswer_of_isFixed prims hi] at hp
        simp at hp
        rw [hp]
      · rw [hashAnswer_of_not_isFixed prims hfix] at hp
        exact (randomOracle_support q s p hp).2.2 x hxq
    · change p ∈ support ((prgAnswer prims y).run s) at hp
      unfold prgAnswer at hp
      rw [StateT.run_bind] at hp
      simp only [support_bind] at hp
      obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
      simp only [StateT.run_pure, support_pure] at hp
      subst hp
      have hfix : ¬ IsFixed (Query.streamKey (C := C) y.2.1) := by simp [IsFixed]
      rw [hashAnswer_of_not_isFixed prims hfix] at hp'
      exact (randomOracle_support _ s p' hp').2.2 x (hx _)

theorem setupCell_commitments (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C) (kind : KeyKind)
    (values : List HashOutput) :
    IsQueryBoundP (setupInitialCommitments phase D parts) (seedGenCellCall (.derive phase kind values)) 0 := by
  unfold setupInitialCommitments
  refine (seedGenIsQueryBoundP_sequenceFin_sum _ (fun _ => 0) fun i => ?_).mono (by simp)
  split
  · trivial
  · rw [commitQueries, seedGen_liftComp_mapM]
    refine (seedGenIsQueryBoundP_listMapM (k := fun _ => 0) (fun j => ?_) C.parties).mono (by simp)
    have e : liftComp (hashQuery (C := C) (.commit phase i j (revealTo phase (parts i) i j))) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr (.inl (.commit phase i j (revealTo phase (parts i) i j))))) :
          OracleComp (LocalSpec C) _) >>= pure := by
      rw [bind_pure]
      rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenCellCall]), fun _ => trivial⟩

/-- A programming input of the prefix is a logged query, or two programming inputs are equal. -/
def SetupProgramAlias (phase : Phase) (D : C.Coalition) {σ : Type} (pre : SeedGenKnownPre C E σ) : Prop :=
  (∃ x ∈ setupProgrammingInputs phase D (setupProgramView phase D pre.parts pre.log pre.sent), ∃ y, (x, y) ∈ pre.log) ∨
    ¬ (setupProgrammingInputs phase D (setupProgramView phase D pre.parts pre.log pre.sent)).Nodup

theorem setupProgrammingInputs_derive (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C) (x : Query C)
    (hx : x ∈ setupProgrammingInputs phase D view) : ∃ kind values, x = .derive phase kind values := by
  simp only [setupProgrammingInputs, List.mem_append, List.mem_map] at hx
  rcases hx with (hx | ⟨T, _, rfl⟩) | ⟨p, _, rfl⟩
  · unfold setupParameterInputs at hx
    split_ifs at hx
    · exact ⟨_, _, List.mem_singleton.mp hx⟩
    · simp at hx
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem seedGenWorld_sample_support {β : Type} (p : ProbComp β) (s : HashCache C) (w : β × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (free (liftComp p (LocalSpec C)))).run s)) : w.2 = s := by
  rw [simulateQ_world_sample] at hw
  simp only [StateT.run_lift, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
  obtain ⟨a, _, rfl⟩ := hw
  rfl

/-- A failed programming of the prefix is an alias of a programming input. -/
theorem setupKnownPrefix_alias_of_fail (phase : Phase) (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (w : SeedGenKnownPre C E A.State × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (setupKnownPrefix (phase := phase) D A x z)).run ∅))
    (hok : w.1.ok = false) : SetupProgramAlias (phase := phase) D w.1 := by
  by_contra hA
  simp only [SetupProgramAlias, not_or, not_exists, not_and, not_not] at hA
  obtain ⟨hlog, hnodup⟩ := hA
  unfold setupKnownPrefix at hw
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hw
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, p₄, hp₄, p₅, hp₅, p₆, hp₆, hfin⟩ := hw
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
  subst hfin
  simp only at hlog hnodup hok
  have hfresh : ∀ q ∈ setupProgrammingInputs phase D (setupProgramView phase D p₂.1 (p₀.1.2 ++ p₄.1.2) p₄.1.1.2),
      p₅.2 q = none := by
    intro q hq
    obtain ⟨kind, values, rfl⟩ := setupProgrammingInputs_derive (phase := phase) D _ q hq
    have hns : ¬ ∃ k, Query.derive (C := C) phase kind values = .streamKey k := by
      rintro ⟨k, hk⟩
      cases hk
    have n₀ : p₀.2 (.derive phase kind values) = none := by
      by_contra hne
      rcases seedGenObserve_new_logged prims _ ∅ p₀ hp₀ _ rfl hne with ⟨y, hy⟩ | h
      · exact hlog _ hq y (List.mem_append_left _ hy)
      · exact hns h
    have u₁ := seedGenWorld_sample_support prims _ _ p₁ hp₁
    have u₂ := seedGenWorld_sample_support prims _ _ p₂ hp₂
    rw [simulateQ_free] at hp₃
    have u₃ := seedGenCell_unchanged prims (.derive phase kind values) (fun k hk => by cases hk) _
      (setupCell_commitments (phase := phase) D p₂.1 kind values) _ p₃ hp₃
    have n₄ : p₄.2 (.derive phase kind values) = none := by
      by_contra hne
      rcases seedGenObserve_new_logged prims _ _ p₄ hp₄ _ (by rw [u₃, u₂, u₁, n₀]) hne with ⟨y, hy⟩ | h
      · exact hlog _ hq y (List.mem_append_right _ hy)
      · exact hns h
    rw [seedGenWorld_sample_support prims _ _ p₅ hp₅, n₄]
  have := setupProgramOk_fresh (phase := phase) prims D _ _ _ _ _ _ _ _ p₆ hp₆ hfresh hnodup
  rw [this] at hok
  cases hok

end Birthday

section Main

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A programming attempt fails only if a counted call before the programming hits an honest part,
or if two programming inputs coincide (CDG+18). -/
def SetupProgramFailBound (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let r ← runWorld prims (setupKnownGame (phase := phase) D A x z)}[SeedGenProgramFail r.1]).toReal ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ) / 2 ^ 256

/-- A missed extraction or an echo collision needs a collision of two compared answers or a fresh
opening that hits its earlier commitment. -/
def SetupExtractEchoBound (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let r ← runWorld prims (setupKnownGame (phase := phase) D A x z)}[
      SetupExtractFail (phase := phase) D r.1 ∨ SetupEchoCollision (phase := phase) D r.1]).toReal ≤
      (((q + C.n ^ 2) ^ 2 + 2 * (q + C.n ^ 2) : ℕ) : ℝ) / 2 ^ 257

/-- The birthday bound on the compared cells. At most `q` counted calls and `n²` honest shared-key
hashes and corrupt openings sample them. -/
def SetupComparedCollisionBound (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run ∅}[
      SetupComparedCollision (phase := phase) D w.2]).toReal ≤
      (((q + C.n ^ 2) ^ 2 : ℕ) : ℝ) / 2 ^ 257

/-- Each of at most `q + n²` openings that are sampled after the commit round hits its commitment
with probability `2^-256`. -/
def SetupFreshOpeningBound (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run ∅}[
      SetupFreshOpening (phase := phase) D w.1 w.2]).toReal ≤
      ((q + C.n ^ 2 : ℕ) : ℝ) / 2 ^ 256

theorem setupExtractEchoBound_of_cache (phase : Phase) (prims : Primitives) (hC : SetupComparedCollisionBound (phase := phase) (C := C) (E := E) prims)
    (hF : SetupFreshOpeningBound (phase := phase) (C := C) (E := E) prims) : SetupExtractEchoBound (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hmono : Pr{let r ← runWorld prims (setupKnownGame (phase := phase) D A x z)}[
      SetupExtractFail (phase := phase) D r.1 ∨ SetupEchoCollision (phase := phase) D r.1] ≤
      Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run ∅}[SetupComparedCollision (phase := phase) D w.2] +
      Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run ∅}[
        SetupFreshOpening (phase := phase) D w.1 w.2] := by
    rw [probEvent_runWorld_fst prims (setupKnownGame (phase := phase) D A x z)
      (fun r => SetupExtractFail (phase := phase) D r ∨ SetupEchoCollision (phase := phase) D r), StateT.run'_eq, prEvent_map]
    refine le_trans (prEvent_mono_of_support _ _ _ fun w hw hb => ?_) (prEvent_or_le _ _ _)
    obtain ⟨hn, hdata, hlog⟩ := setupKnownGame_support (phase := phase) prims D A x z w hw
    exact setupKnown_cacheEvent_of_bad (phase := phase) prims D w.1 w.2 hn hdata hlog hb
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) hmono).trans ?_
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  refine (add_le_add (hC D A x z Z q hq) (hF D A x z Z q hq)).trans (le_of_eq ?_)
  have h256 : (2 : ℝ) ^ 257 = 2 * 2 ^ 256 := pow_succ' 2 256
  rw [h256]
  push_cast
  field_simp

theorem setupComparedCollisionBound_proof (phase : Phase) (prims : Primitives) : SetupComparedCollisionBound (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨start, step, final, hsum, hs, hr, _, _⟩ := hq
  obtain ⟨h₁, h₂⟩ := isQueryBoundP_setupCompared_knownGame (phase := phase) D A x z start step hs hr
  have h0 : ¬ SetupComparedCollision (phase := phase) D (∅ : HashCache C) := by
    rintro ⟨_, _, _, _, _, _, h, _⟩
    simp at h
  have hc0 : SetupComparedCount (phase := phase) D (∅ : HashCache C) 0 := ⟨∅, by simp, by simp⟩
  have hb := setupCompared_birthday (phase := phase) prims (setupKnownGame (phase := phase) D A x z) _ ∅ 0 h₁ h₂ h0 hc0
  have hm : start + 3 * step + C.n * C.n ≤ q + C.n ^ 2 := by
    simp only [setupRounds] at hsum
    nlinarith
  have hcost : seedGenBirthdayCost 0 (start + 3 * step + C.n * C.n) ≤
      (((q + C.n ^ 2) ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card HashOutput) := by
    unfold seedGenBirthdayCost
    apply ENNReal.div_le_div_right
    have := Nat.mul_le_mul hm hm
    exact_mod_cast (by nlinarith : (start + 3 * step + C.n * C.n) * (2 * 0 + (start + 3 * step + C.n * C.n)) ≤
      (q + C.n ^ 2) ^ 2)
  have ht := ENNReal.toReal_mono (by
      apply ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      simp) (hb.trans hcost)
  refine ht.trans (le_of_eq ?_)
  rw [card_hashOutput]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  rw [Nat.cast_pow (2 : ℕ) 256, Nat.cast_ofNat, ← pow_succ']

/-- The commitment that an opening cell of a corrupt sender to an honest receiver must hit. -/
def setupOpeningTarget (phase : Phase) (D : C.Coalition) (sent : C.Party → Mail C E) : Query C → Option HashOutput
  | .commit phase' j i _ => if phase' = phase ∧ j ∈ D.1 ∧ i ∉ D.1 then
      (match Msg.hashesOf (sent j i) with
        | [c] => some c
        | _ => none) else none
  | _ => none

theorem setupOpeningTarget_compared (phase : Phase) (D : C.Coalition) (sent : C.Party → Mail C E) (x : Query C)
    (hx : setupOpeningTarget (phase := phase) D sent x ≠ none) : SetupComparedCell (phase := phase) D x := by
  unfold setupOpeningTarget at hx
  split at hx
  · split_ifs at hx with h
    · exact ⟨h.1, h.2.1⟩
    · exact absurd rfl hx
  · exact absurd rfl hx

theorem setupFreshOpeningBound_proof (phase : Phase) (prims : Primitives) : SetupFreshOpeningBound (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨start, step, final, hsum, hs, hr, _, _⟩ := hq
  have hkey : Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run ∅}[
      SetupFreshOpening (phase := phase) D w.1 w.2] ≤
      ((step + (C.n * C.n + step) : ℕ) : ℝ≥0∞) / Fintype.card HashOutput := by
    rw [setupKnownGame_eq_prefix, simulateQ_bind, StateT.run_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun w hw => ?_
    rw [simulateQ_bind, simulateQ_free, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure]
    rw [bind_pure_comp, prEvent_map]
    refine (prEvent_mono _ _ _ fun r hf => ?_).trans
      (setupTarget_local (phase := phase) prims (setupOpeningTarget (phase := phase) D w.1.sent) (setupOpeningTarget_compared (phase := phase) D w.1.sent) w.2 _
        _ w.2 (isQueryBoundP_setupCompared_post (phase := phase) D A step hr _ _ _) ?_)
    · obtain ⟨j, i, rv, c, hj, hi, hc, hsent, hlog⟩ := hf
      refine ⟨.commit phase j i rv, c, ?_, setupKnownPrefix_unlogged (phase := phase) prims D A x z w hw j i rv hj hlog, hc⟩
      simp [setupOpeningTarget, hj, hi, hsent]
    · rintro ⟨_, _, _, hb, hs'⟩
      rw [hb] at hs'
      cases hs'
  have hm : step + (C.n * C.n + step) ≤ q + C.n ^ 2 := by
    simp only [setupRounds] at hsum
    nlinarith
  have ht := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top (q + C.n ^ 2)) (by simp))
    (hkey.trans (ENNReal.div_le_div_right (by exact_mod_cast hm) _))
  refine ht.trans (le_of_eq ?_)
  rw [card_hashOutput]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  push_cast
  ring

/-- The known half from the two probability bounds. -/
theorem setupKnownMismatch_of_bounds (phase : Phase) (prims : Primitives) (hP : SetupProgramFailBound (phase := phase) (C := C) (E := E) prims)
    (hX : SetupExtractEchoBound (phase := phase) (C := C) (E := E) prims) : SetupKnownMismatch (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hmono : Pr{let r ← runWorld prims (setupCommonGame phase D A x z)}[
      seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1] ≤
      Pr{let r ← runWorld prims (setupKnownGame (phase := phase) D A x z)}[SeedGenProgramFail r.1] +
      Pr{let r ← runWorld prims (setupKnownGame (phase := phase) D A x z)}[SetupExtractFail (phase := phase) D r.1 ∨ SetupEchoCollision (phase := phase) D r.1] := by
    rw [probEvent_runWorld_fst prims (setupCommonGame phase D A x z)
        (fun r => seedGenMixedProjection D r ≠ seedGenIdealProjection D r),
      probEvent_runWorld_fst prims (setupKnownGame (phase := phase) D A x z) SeedGenProgramFail,
      probEvent_runWorld_fst prims (setupKnownGame (phase := phase) D A x z) (fun r => SetupExtractFail (phase := phase) D r ∨ SetupEchoCollision (phase := phase) D r),
      simulateQ_setupCommonGame_known, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
      prEvent_map]
    simp only [StateT.run'_eq, prEvent_map]
    refine le_trans (prEvent_mono_of_support _ _ _ fun p hp hm => ?_) (prEvent_or_le _ _ _)
    have hr : p.1 ∈ support ((simulateQ (worldAnswer prims) (setupKnownGame (phase := phase) D A x z)).run' ∅) := by
      rw [StateT.run'_eq, support_map]
      exact ⟨p, hp, rfl⟩
    rcases setupKnown_bad_of_mismatch (phase := phase) prims D A x z p.1 hr hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) hmono).trans ?_
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  refine (add_le_add (hP D A x z Z q hq) (hX D A x z Z q hq)).trans ?_
  have ha := setupKnown_arith (phase := phase) (C := C) q (seedGenProgrammingCount D) (seedGenProgrammingCount_le D)
  have scale {a b c d : ℝ} (hd : 0 < d) (h : 2 * a + b ≤ c) :
      a / d + b / (d * 2) ≤ c / d / 2 := by
    field_simp
    linarith
  rw [setupHashError, show (2 : ℝ) ^ 257 = 2 ^ 256 * 2 from pow_succ _ _]
  apply scale (pow_pos (by norm_num) 256)
  exact_mod_cast ha

/-- The guessing bound of the programming inputs before the programming (CDG+18). Each counted call
before the programming hits an honest part of a programming input with probability at most
`K / 2^256`, and each pair of programming inputs is equal with probability at most `2^-256`. -/
def SetupProgramAliasBound (phase : Phase) (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let w ← (simulateQ (worldAnswer prims) (setupKnownPrefix phase D A x z)).run ∅}[
      SetupProgramAlias phase D w.1]).toReal ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ) / 2 ^ 256

theorem setupProgramFailBound_of_alias (phase : Phase) (prims : Primitives) (h : SetupProgramAliasBound (phase := phase) (C := C) (E := E) prims) :
    SetupProgramFailBound (phase := phase) (C := C) (E := E) prims := by
  intro D A x z Z q hq
  refine le_trans (ENNReal.toReal_mono (prEvent_ne_top _) ?_) (h D A x z Z q hq)
  rw [probEvent_runWorld_fst prims (setupKnownGame (phase := phase) D A x z) SeedGenProgramFail, StateT.run'_eq, prEvent_map,
    setupKnownGame_eq_prefix, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_prEvent_add_of_support _ _
    (fun w : SeedGenKnownPre C E A.State × HashCache C => ¬ w.1.ok = true) _ (ε := 0)
    (fun w _ hok => le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hf => by
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
        Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      exact hok (by simpa [SeedGenProgramFail] using hf)))).trans ?_
  rw [add_zero]
  exact prEvent_mono_of_support _ _ _ fun w hw hf =>
    setupKnownPrefix_alias_of_fail (phase := phase) prims D A x z w hw (by simpa using hf)

/-- The known half from the programming bound. -/
theorem setupKnownMismatch_of_programFail (phase : Phase) (prims : Primitives) (hP : SetupProgramFailBound (phase := phase) (C := C) (E := E) prims) :
    SetupKnownMismatch (phase := phase) (C := C) (E := E) prims :=
  setupKnownMismatch_of_bounds (phase := phase) prims hP
    (setupExtractEchoBound_of_cache (phase := phase) prims (setupComparedCollisionBound_proof (phase := phase) prims) (setupFreshOpeningBound_proof (phase := phase) prims))

/-- The extraction and echo bound of a setup. -/
theorem setupExtractEchoBound (phase : Phase) : SetupExtractEchoBound (C := C) (E := E) phase prims :=
  setupExtractEchoBound_of_cache phase prims (setupComparedCollisionBound_proof phase prims)
    (setupFreshOpeningBound_proof phase prims)

/-- The distance claim of a setup from the guessing bound of the programming inputs. -/
theorem setupSecurityDistance_of_programAlias (phase : Phase)
    (hA : SetupProgramAliasBound (C := C) (E := E) phase prims) : SetupSecurityDistance (C := C) (E := E) phase prims :=
  setupSecurityDistance_of_known prims phase
    (setupKnownMismatch_of_bounds phase prims (setupProgramFailBound_of_alias phase prims hA)
      (setupExtractEchoBound prims phase))

end Main

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.setupSecurityDistance_of_programAlias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.setupSecurityDistance_of_programAlias
