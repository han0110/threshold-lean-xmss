import ThresholdLeanXmssSecurity.Proof.SeedGenFinish
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The known half of the seed generation security

This module reduces `SeedGenKnownMismatch`, the known-half hypothesis of `seedGenSecurityComplete`.

1. `seedGenKnownGame` is the common game in normal form, with its transcript
   (`simulateQ_seedGenCommonGame_known`).
2. A mismatch is a failed programming, a missed extraction or an echo collision
   (`seedGenKnown_bad_of_mismatch`). Without them, every exposed coordinate of an accepted output is
   the dealer's value.
3. A missed extraction or an echo collision is a collision of two compared cells or a fresh opening
   (`seedGenKnown_cacheEvent_of_bad`). The compared cells are the shared-key hashes and the
   commitments of a corrupt sender.
4. At most `q + n²` calls sample a compared cell. The birthday bound gives `(q + n²)² / 2^257`
   (`seedGenComparedCollisionBound_proof`), and each fresh opening costs `2^-256`
   (`seedGenFreshOpeningBound_proof`).
5. A failed programming means that a programming input of `seedGenKnownPrefix` is a logged query,
   or that two programming inputs are equal (`seedGenProgramFailBound_of_alias`).
6. The total fits in half of `seedGenHashError` (`seedGenKnown_arith`).

`SeedGenProgramAliasBound` is a hypothesis of `seedGenSecurityDone_of_programAlias`. It
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
theorem seedGenHiddenOverlay_hybrid (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (i : C.Party) (hi : i ∉ D.1) :
    seedGenHiddenOverlay D i (dealtKeys parameter (seedGenHybridSeeds D h parts seeds)
      (seedGenHybridPairs D h parts pairs) i) (dealtKeys parameter seeds pairs i) =
      dealtKeys parameter seeds pairs i := by
  unfold seedGenHiddenOverlay dealtKeys seedGenHybridSeeds seedGenHybridPairs
  congr 1
  · funext T
    split_ifs <;> simp_all
  · funext j
    by_cases hj : j = i
    · simp [hj]
    · simp only [dif_neg hj]
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
def seedGenProgramOk (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) : OracleComp (WorldSpec C) Bool := do
  let view := seedGenProgramView D parts log sent
  let b ← program (seedGenParameterProgrammingInput D view) (seedGenFullParameter high parameter)
  let bs ← (seedGenKnownCoordinates D).mapM fun T => program (seedGenTermProgrammingInput D view T) (seeds T)
  let cs ← (seedGenCrossCoordinates D).mapM fun p => program (seedGenPairProgrammingInput D view p) (pairs p)
  pure (b && bs.all id && cs.all id)

/-- The last two rounds, with the corrupt reveals and the honest echo data. -/
def seedGenPostTraced (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Mail C E) × (C.Party → Option (SeedGenEchoData C)) ×
      (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ D.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true then
    pure (state, fun _ _ => none, fun _ => none, fun _ => none)
  else do
    let (st, sent) ← A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (seedGenRevealSteps D parts committed i).outbox c else none
    let data ← seedGenRevealComputations D parts committed sent
    let r ← seedGenFinishLocal D A st data
    pure (r.1, sent, data, r.2)

theorem seedGenPostTraced_proj (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    (fun r => (r.1, r.2.2.2)) <$> seedGenPostTraced D A state parts committed =
      seedGenPostCommitLocal D A state parts committed := by
  unfold seedGenPostTraced seedGenPostCommitLocal
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
def seedGenKnownGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    OracleComp (WorldSpec C) (SeedGenKnownTrace C E A.State) := do
  let (state, log) ← observe (A.start (corruptInputs D x) z)
  let (parameter, seeds, pairs) ← free (liftComp (seedGenDealerSamples (C := C)) (LocalSpec C))
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C)))
    (LocalSpec C))
  let commitments ← free (seedGenInitialCommitments D parts)
  let ((st, sent), calls) ← observe (A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    commitOutbox i (commitments i) c else none)
  let high ← free (liftComp ($ᵗ HashOutput) (LocalSpec C))
  let ok ← seedGenProgramOk D parts (log ++ calls) sent parameter seeds pairs high
  let r ← free (seedGenPostTraced D A st parts (seedGenCommitInbox D parts commitments sent))
  pure ⟨parameter, seeds, pairs, parts, log ++ calls, sent, commitments, ok, r.1, r.2.1, r.2.2.1, r.2.2.2⟩

/-- The output of the common game. -/
def SeedGenKnownTrace.result {σ : Type} (r : SeedGenKnownTrace C E σ) :
    σ × (C.Party → Option (Keys C)) × (C.Party → Keys C) :=
  (r.state, r.outputs, dealtKeys r.parameter r.seeds r.pairs)

/-- A programming attempt fails. -/
def SeedGenProgramFail {σ : Type} (r : SeedGenKnownTrace C E σ) : Prop := r.ok = false

/-- An honest operator that reaches the echo has a corrupt opening that the extraction misses. -/
def SeedGenExtractFail (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ) : Prop :=
  ∃ i, i ∉ D.1 ∧ (r.data i).isSome ∧ ∃ j, j ∈ D.1 ∧
    extractReveal .seedGen r.log r.sent j i ≠
      Msg.hashesOf (seedGenRevealInbox D r.parts (seedGenCommitInbox D r.parts r.commitments r.sent) r.revealSent i j)

/-- Two honest operators that reach the echo send equal shared-key hashes of distinct inputs. -/
def SeedGenEchoCollision (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ) : Prop :=
  ∃ i j ki si kj sj, i ∉ D.1 ∧ j ∉ D.1 ∧ r.data i = some (ki, si) ∧ r.data j = some (kj, sj) ∧
    si.getD j.val 0 = sj.getD i.val 0 ∧
    Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) ≠
      Query.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)

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

theorem simulateQ_world_startSteps_seedGen (D : C.Coalition) (parts : C.Party → Parts C) :
    simulateQ (worldAnswer prims)
        (startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))) =
      simulateQ (worldAnswer prims) (seedGenInitialSteps D parts <$> free (seedGenInitialCommitments D parts)) := by
  rw [simulateQ_startSteps_real, seedGenMapRoles_world, ← simulateQ_startSteps_real, startSteps_seedGenWith,
    simulateQ_map, simulateQ_map, simulateQ_free]

theorem simulateQ_world_post_seedGen {β : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (f : A.State × (C.Party → Option (Keys C)) → β) :
    simulateQ (worldAnswer prims)
        ((executeRounds observedRoles D A noFunctionality (setupRounds - 1) state
          (seedGenRevealSteps D parts committed)).run >>= fun r => pure (f r.1)) =
      simulateQ (worldAnswer prims)
        (free (seedGenPostTraced D A state parts committed) >>= fun r => pure (f (r.1, r.2.2.2))) := by
  have hl : ((executeRounds observedRoles D A noFunctionality (setupRounds - 1) state
      (seedGenRevealSteps D parts committed)).run >>= fun r => pure (f r.1)) =
      seedGenEraseLog (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state
        (seedGenRevealSteps D parts committed)) >>= fun r => pure (f r) := by
    simp [seedGenEraseLog]
  rw [hl, seedGenEraseLog_executeRounds, simulateQ_bind, simulateQ_world_executeRounds, simulateQ_bind,
    simulateQ_free]
  change simulateQ (localAnswer prims) (executeRounds localRoles D A noFunctionality 2 state
    (seedGenRevealSteps D parts committed)) >>= _ = _
  rw [executeRounds_seedGenRevealSteps_two, ← seedGenPostTraced_proj, simulateQ_map, bind_map_left]

theorem simulateQ_seedGenCommonGame_known (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    simulateQ (worldAnswer prims) (seedGenCommonGame D A x z) =
      simulateQ (worldAnswer prims) (SeedGenKnownTrace.result <$> seedGenKnownGame D A x z) := by
  unfold seedGenCommonGame seedGenEmulation seedGenKnownGame seedGenDealerSamples prawnsKeyGen
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure]
  simp only [seedGenSimulator, setupSimulator, bind_assoc, pure_bind]
  refine seedGenKnown_simulateQ_bind_right prims fun a => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun parameter => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun seeds => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun pairs => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun parts => ?_
  rw [seedGenKnown_simulateQ_bind_left prims (simulateQ_world_startSteps_seedGen prims D parts), bind_map_left]
  refine seedGenKnown_simulateQ_bind_right prims fun commitments => ?_
  rw [stepRound_seedGenInitialSteps_observed]
  simp only [observedRoles, WriterT.run_bind, WriterT.run_pure, map_pure, pure_bind, bind_assoc,
    show (∅ : CallLog C) = [] from rfl, List.append_nil, WriterT.run_mk]
  refine seedGenKnown_simulateQ_bind_right prims fun r => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun high => ?_
  rw [seedGenProgramBlock_dealt]
  simp only [seedGenProgramOk, bind_assoc, pure_bind]
  refine seedGenKnown_simulateQ_bind_right prims fun b => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun bs => ?_
  refine seedGenKnown_simulateQ_bind_right prims fun cs => ?_
  exact simulateQ_world_post_seedGen prims D A r.1.1 parts _ fun p => (p.1, p.2, dealtKeys parameter seeds pairs)

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
theorem seedGenProgramOk_support (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) (s : HashCache C) (z : Bool × HashCache C)
    (hz : z ∈ support ((simulateQ (worldAnswer prims)
      (seedGenProgramOk D parts log sent parameter seeds pairs high)).run s)) (hok : z.1 = true) :
    let view := seedGenProgramView D parts log sent
    z.2 (seedGenParameterProgrammingInput D view) = some (seedGenFullParameter high parameter) ∧
      (∀ T ∈ seedGenKnownCoordinates D, z.2 (seedGenTermProgrammingInput D view T) = some (seeds T)) ∧
      (∀ p ∈ seedGenCrossCoordinates D, z.2 (seedGenPairProgrammingInput D view p) = some (pairs p)) := by
  unfold seedGenProgramOk at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion,
    simulateQ_world_program, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩ := hz
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hb, hbs⟩, hcs⟩ := hok
  have g₂ := grows_worldAnswer prims |>.simulateQ _ p₁.2 p₂ hp₂
  have g₃ := grows_worldAnswer prims |>.simulateQ _ p₂.2 p₃ hp₃
  refine ⟨g₃ (g₂ ((seedGenProgramAnswer_support _ s p₁ hp₁).2 hb)), fun T hT => g₃ ?_, fun p hp => ?_⟩
  · exact seedGenPrograms_mapM_support prims _ _ _ p₁.2 p₂ hp₂ hbs T hT
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
theorem seedGenProgramOk_fresh (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) (s : HashCache C) (z : Bool × HashCache C)
    (hz : z ∈ support ((simulateQ (worldAnswer prims)
      (seedGenProgramOk D parts log sent parameter seeds pairs high)).run s))
    (hfresh : ∀ x ∈ seedGenProgrammingInputs D (seedGenProgramView D parts log sent), s x = none)
    (hnodup : (seedGenProgrammingInputs D (seedGenProgramView D parts log sent)).Nodup) : z.1 = true := by
  set view := seedGenProgramView D parts log sent
  have hfixT : ∀ T, ¬ IsFixed (seedGenTermProgrammingInput D view T) := fun T => by
    simp [IsFixed, seedGenTermProgrammingInput]
  have hfixP : ∀ p, ¬ IsFixed (seedGenPairProgrammingInput D view p) := fun p => by
    simp [IsFixed, seedGenPairProgrammingInput]
  unfold seedGenProgramOk at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion,
    simulateQ_world_program, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, rfl⟩ := hz
  simp only [seedGenProgrammingInputs, List.nodup_append, List.nodup_cons] at hnodup
  obtain ⟨⟨hPT, hT⟩, hC, hdisj⟩ := hnodup
  have hPC : seedGenParameterProgrammingInput D view ∉ (seedGenCrossCoordinates D).map
      (seedGenPairProgrammingInput D view) := fun hm => hdisj _ List.mem_cons_self _ hm rfl
  have hTC : ∀ a ∈ (seedGenKnownCoordinates D).map (seedGenTermProgrammingInput D view),
      ∀ b ∈ (seedGenCrossCoordinates D).map (seedGenPairProgrammingInput D view), a ≠ b :=
    fun a ha b hb => hdisj a (List.mem_cons_of_mem _ ha) b hb
  have hmemP : seedGenParameterProgrammingInput D view ∈ seedGenProgrammingInputs D view :=
    List.mem_append_left _ List.mem_cons_self
  rw [programAnswer_run_fresh (by simp [IsFixed, seedGenParameterProgrammingInput]) s (hfresh _ hmemP)] at hp₁
  simp only [support_pure, Set.mem_singleton_iff] at hp₁
  subst hp₁
  have h₂ := seedGenPrograms_fresh prims (seedGenKnownCoordinates D) (seedGenTermProgrammingInput D view) seeds hfixT
    _ p₂ hp₂ (fun T hT' => by
      have hne : seedGenTermProgrammingInput D view T ≠ seedGenParameterProgrammingInput D view :=
        fun he => hPT (he ▸ List.mem_map_of_mem hT')
      exact (QueryCache.cacheQuery_of_ne s (seedGenFullParameter high parameter) hne).trans
        (hfresh _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hT'))))) hT
  have h₃ := seedGenPrograms_fresh prims (seedGenCrossCoordinates D) (seedGenPairProgrammingInput D view) pairs hfixP
    _ p₃ hp₃ (fun p hp' => by
      have hm : seedGenPairProgrammingInput D view p ∈ (seedGenCrossCoordinates D).map
          (seedGenPairProgrammingInput D view) := List.mem_map_of_mem hp'
      have hne : seedGenPairProgrammingInput D view p ≠ seedGenParameterProgrammingInput D view :=
        fun he => hPC (he ▸ hm)
      exact (h₂.2 _ (fun hmT => hTC _ hmT _ hm rfl)).trans
        ((QueryCache.cacheQuery_of_ne s (seedGenFullParameter high parameter) hne).trans
        (hfresh _ (List.mem_append_right _ hm)))) hC
  simp only [Bool.and_eq_true]
  exact ⟨⟨trivial, h₂.1⟩, h₃.1⟩

end Support

section Deterministic

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The fixed-oracle run of the last two rounds gives the reference echo data and outputs. -/
theorem seedGenPostTraced_fixed_support (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (h : Query C → HashOutput)
    (z : A.State × (C.Party → Mail C E) × (C.Party → Option (SeedGenEchoData C)) × (C.Party → Option (Keys C)))
    (hz : z ∈ support (simulateQ (fixedLocal prims h) (seedGenPostTraced D A state parts committed))) :
    z.2.2.2 = (fun _ => none) ∨ (z.2.2.1 = seedGenRevealAllFixed prims D h parts committed z.2.1 ∧
      ∃ echoSent : C.Party → Mail C E, z.2.2.2 = seedGenEchoDataOutput D z.2.2.1 echoSent) := by
  unfold seedGenPostTraced at hz
  split_ifs at hz
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  · simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion,
      simulateQ_fixedLocal_seedGenRevealComputations, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, _, data, rfl, f, hf, rfl⟩ := hz
    unfold seedGenFinishLocal at hf
    split_ifs at hf
    · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hf
      subst hf
      exact Or.inl rfl
    · simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] at hf
      obtain ⟨e, _, rfl⟩ := hf
      exact Or.inr ⟨rfl, e.2, rfl⟩

/-- The fixed-oracle run of the last two rounds gives no echo data or the reference echo data. -/
theorem seedGenPostTraced_fixed_data (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (h : Query C → HashOutput)
    (z : A.State × (C.Party → Mail C E) × (C.Party → Option (SeedGenEchoData C)) × (C.Party → Option (Keys C)))
    (hz : z ∈ support (simulateQ (fixedLocal prims h) (seedGenPostTraced D A state parts committed))) :
    (∀ i, z.2.2.1 i = none) ∨ z.2.2.1 = seedGenRevealAllFixed prims D h parts committed z.2.1 := by
  unfold seedGenPostTraced at hz
  split_ifs at hz
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl fun _ => rfl
  · simp only [simulateQ_bind, simulateQ_pure, support_bind, Set.mem_iUnion,
      simulateQ_fixedLocal_seedGenRevealComputations, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, _, data, rfl, f, _, rfl⟩ := hz
    exact Or.inr rfl

/-- Without a failed programming, a missed extraction or an echo collision, the emulated outputs
are the dealt keys. -/
theorem seedGenKnown_projection_eq (D : C.Coalition) {σ : Type} (h : Query C → HashOutput)
    (r : SeedGenKnownTrace C E σ) (high : HashOutput)
    (hparameter : h (seedGenParameterProgrammingInput D (seedGenProgramView D r.parts r.log r.sent)) =
      seedGenFullParameter high r.parameter)
    (hterm : ∀ T ∈ seedGenKnownCoordinates D,
      h (seedGenTermProgrammingInput D (seedGenProgramView D r.parts r.log r.sent) T) = r.seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates D,
      h (seedGenPairProgrammingInput D (seedGenProgramView D r.parts r.log r.sent) p) = r.pairs p)
    (hpost : r.outputs = (fun _ => none) ∨
      (r.data = seedGenRevealAllFixed prims D h r.parts (seedGenCommitInbox D r.parts r.commitments r.sent)
        r.revealSent ∧ ∃ echoSent : C.Party → Mail C E, r.outputs = seedGenEchoDataOutput D r.data echoSent))
    (hextract : ¬ SeedGenExtractFail D r) (hcollision : ¬ SeedGenEchoCollision D r) :
    seedGenMixedProjection D r.result = seedGenIdealProjection D r.result := by
  unfold seedGenMixedProjection seedGenIdealProjection SeedGenKnownTrace.result
  simp only [Prod.mk.injEq, true_and]
  funext i
  rcases hpost with ho | ⟨hdata, echoSent, ho⟩
  · simp [ho]
  · cases hi : r.outputs i with
    | none => simp
    | some key =>
      set committed := seedGenCommitInbox D r.parts r.commitments r.sent
      have ho' : seedGenEchoDataOutput D (seedGenRevealAllFixed prims D h r.parts committed r.revealSent)
          echoSent i = some key := by rw [← hdata, ← ho]; exact hi
      have hhonest := (seedGenEchoDataOutput_some D _ echoSent i key ho').1
      have hall := seedGenEchoDataOutput_all_some D _ echoSent i key ho'
      have hkey := seedGenRevealEcho_output_eq_hybrid prims D h r.parts committed r.revealSent echoSent r.sent
        r.log r.parameter r.seeds r.pairs high
        (fun k j hk hj => by
          by_contra hne
          exact hextract ⟨k, hk, by rw [hdata]; exact hall k hk, j, hj, hne⟩)
        hparameter
        (fun T hT => hterm T (List.mem_filter.mpr ⟨Finset.mem_toList.mpr (Finset.mem_univ T), by simpa using hT⟩))
        hpair i key ho'
        (fun j hj hcol => by
          by_contra hne
          obtain ⟨hsi, _⟩ := seedGenRevealAllFixed_some prims D h r.parts committed r.revealSent i (hall i hhonest)
          obtain ⟨hsj, _⟩ := seedGenRevealAllFixed_some prims D h r.parts committed r.revealSent j (hall j hj)
          exact hcollision ⟨i, j, _, _, _, _, hhonest, hj, by rw [hdata]; exact hsi, by rw [hdata]; exact hsj,
            by rw [D_sharedQueries_at, D_sharedQueries_at]; exact hcol, hne⟩)
      rw [Option.map_some, if_pos ⟨hhonest, rfl⟩, hkey,
        seedGenHiddenOverlay_hybrid D h r.parts r.parameter r.seeds r.pairs i hhonest]

end Deterministic

section Reduction

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A mismatch of the common game is a failed programming, a missed extraction or an echo collision. -/
theorem seedGenKnown_bad_of_mismatch (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (r : SeedGenKnownTrace C E A.State)
    (hr : r ∈ support ((simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run' ∅))
    (hm : seedGenMixedProjection D r.result ≠ seedGenIdealProjection D r.result) :
    SeedGenProgramFail r ∨ SeedGenExtractFail D r ∨ SeedGenEchoCollision D r := by
  by_contra hbad
  simp only [not_or, SeedGenProgramFail, Bool.not_eq_false] at hbad
  obtain ⟨hok, hextract, hcollision⟩ := hbad
  apply hm
  unfold seedGenKnownGame at hr
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
  obtain ⟨hP, hT, hp⟩ := seedGenProgramOk_support prims _ _ _ _ _ _ _ _ p₅.2 p₆ hp₆ hok
  have hread (q : Query C) (v : HashOutput) (hq : p₆.2 q = some v) : hashOf prims p₇.2 q = v :=
    hagree q v (g₇ hq)
  exact seedGenKnown_projection_eq prims D (hashOf prims p₇.2) _ p₅.1 (hread _ _ hP)
    (fun T hm => hread _ _ (hT T hm)) (fun q hm => hread _ _ (hp q hm))
    (seedGenPostTraced_fixed_support prims D A _ _ _ _ _ hsupp) hextract hcollision

end Reduction

section CacheEvents

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The cells whose answers the extraction and the echo compare. These are the shared-key hashes and
the commitments of a corrupt sender. -/
def SeedGenComparedCell (D : C.Coalition) : Query C → Prop
  | .sharedKeys .seedGen _ => True
  | .commit .seedGen j _ _ => j ∈ D.1
  | _ => False

/-- Two compared cells of a cache have equal answers. -/
def SeedGenComparedCollision (D : C.Coalition) (s : HashCache C) : Prop :=
  ∃ q₁ q₂ u, q₁ ≠ q₂ ∧ SeedGenComparedCell D q₁ ∧ SeedGenComparedCell D q₂ ∧ s q₁ = some u ∧ s q₂ = some u

/-- An opening that the adversary never queried before the commit answers its commitment. -/
def SeedGenFreshOpening (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ) (s : HashCache C) : Prop :=
  ∃ j i reveal c, j ∈ D.1 ∧ i ∉ D.1 ∧ s (.commit .seedGen j i reveal) = some c ∧
    Msg.hashesOf (r.sent j i) = [c] ∧ ∀ y, (Query.commit (C := C) .seedGen j i reveal, y) ∉ r.log

theorem seedGenRevealAllFixed_open (D : C.Coalition) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (i j : C.Party) (hji : j ≠ i)
    (hs : (seedGenRevealAllFixed prims D h parts committed sent i).isSome) :
    [h (.commit .seedGen j i (Msg.hashesOf (seedGenRevealInbox D parts committed sent i j)))] =
      Msg.hashesOf (committed i j) := by
  unfold seedGenRevealAllFixed seedGenRevealDataFixed at hs
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
theorem seedGenKnown_cacheEvent_of_bad (D : C.Coalition) {σ : Type} (r : SeedGenKnownTrace C E σ)
    (s : HashCache C) (hs : NoMpc s)
    (hdata : ∀ h, Good prims h → Agrees h s → (∀ i, r.data i = none) ∨
      r.data = seedGenRevealAllFixed prims D h r.parts (seedGenCommitInbox D r.parts r.commitments r.sent)
        r.revealSent)
    (hlog : ∀ q y, (q, y) ∈ r.log → ¬ IsFixed q → s q = some y)
    (hbad : SeedGenExtractFail D r ∨ SeedGenEchoCollision D r) :
    SeedGenComparedCollision D s ∨ SeedGenFreshOpening D r s := by
  set committed := seedGenCommitInbox D r.parts r.commitments r.sent
  have hfixed (i : C.Party) (hi : r.data i ≠ none) (h : Query C → HashOutput) (hg : Good prims h)
      (ha : Agrees h s) : r.data = seedGenRevealAllFixed prims D h r.parts committed r.revealSent := by
    rcases hdata h hg ha with hn | he
    · exact absurd (hn i) hi
    · exact he
  rcases hbad with ⟨i, hi, hsome, j, hj, hne⟩ | ⟨i, j, ki, si, kj, sj, hi, hj, hdi, hdj, hcol, hne⟩
  · have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hdi : r.data i ≠ none := by simpa [Option.isSome_iff_ne_none] using hsome
    set rv := Msg.hashesOf (seedGenRevealInbox D r.parts committed r.revealSent i j)
    have hopen (h : Query C → HashOutput) (hg : Good prims h) (ha : Agrees h s) :
        [h (.commit .seedGen j i rv)] = Msg.hashesOf (committed i j) := by
      apply seedGenRevealAllFixed_open prims D h r.parts committed r.revealSent i j hji
      rw [← hfixed i hdi h hg ha]
      exact hsome
    have hcached := seedGen_cached_of_agrees prims s hs (.commit .seedGen j i rv) (by simp [IsFixed])
      (fun h => [h (.commit .seedGen j i rv)] = Msg.hashesOf (committed i j)) hopen
      (fun h h' e e' => by simpa using e.trans e'.symm)
    set c := hashOf prims s (.commit .seedGen j i rv)
    have hsent : Msg.hashesOf (r.sent j i) = [c] := by
      have := hopen _ (good_hashOf prims s) (agrees_hashOf prims hs)
      simp only [committed, seedGenCommitInbox, roundInbox, if_pos hj] at this
      exact this.symm
    by_cases hl : ∃ y, (Query.commit (C := C) .seedGen j i rv, y) ∈ r.log
    · obtain ⟨y, hy⟩ := hl
      have hyc : y = c := Option.some.inj ((hlog _ y hy (by simp [IsFixed])).symm.trans hcached)
      subst hyc
      by_contra hno
      apply hne
      apply extractReveal_eq_of_unique .seedGen r.log r.sent j i rv _ hy hsent.symm
      intro reveal' value' hmem hval
      by_contra hrv
      apply hno
      left
      have hv : value' = hashOf prims s (.commit .seedGen j i rv) := by
        have := hval.trans hsent
        simpa using this
      subst hv
      exact ⟨Query.commit .seedGen j i reveal', Query.commit .seedGen j i rv, _,
        fun he => hrv (Query.commit.inj he).2.2.2, (hj : SeedGenComparedCell D (.commit .seedGen j i reveal')),
        (hj : SeedGenComparedCell D (.commit .seedGen j i rv)), hlog _ _ hmem (by simp [IsFixed]), hcached⟩
    · push Not at hl
      exact Or.inr ⟨j, i, rv, c, hj, hi, hcached, hsent, hl⟩
  · left
    have hdi' : r.data i ≠ none := by rw [hdi]; simp
    have hshared (a b : C.Party) (ka : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
        (sa : List HashOutput) (hda : r.data a = some (ka, sa)) (h : Query C → HashOutput) (hg : Good prims h)
        (ha : Agrees h s) : sa.getD b.val 0 = h (.sharedKeys .seedGen ((sharedTerms a b).map ka.2.1)) := by
      have hf := hfixed i hdi' h hg ha
      have hsa : (seedGenRevealAllFixed prims D h r.parts committed r.revealSent a).isSome := by
        rw [← hf, hda]; rfl
      obtain ⟨he, _⟩ := seedGenRevealAllFixed_some prims D h r.parts committed r.revealSent a hsa
      rw [← hf, hda] at he
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj he)
      exact D_sharedQueries_at prims h .seedGen a b _
    have hcache (a b : C.Party) (ka : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
        (sa : List HashOutput) (hda : r.data a = some (ka, sa)) :
        s (.sharedKeys .seedGen ((sharedTerms a b).map ka.2.1)) = some (sa.getD b.val 0) := by
      have hc := seedGen_cached_of_agrees prims s hs (.sharedKeys .seedGen ((sharedTerms a b).map ka.2.1))
        (by simp [IsFixed]) (fun h => sa.getD b.val 0 = h (.sharedKeys .seedGen ((sharedTerms a b).map ka.2.1)))
        (hshared a b ka sa hda) (fun h h' e e' => e.symm.trans e')
      rw [hc, ← hshared a b ka sa hda _ (good_hashOf prims s) (agrees_hashOf prims hs)]
    exact ⟨_, _, _, hne, trivial, trivial, hcache i j ki si hdi, (hcache j i kj sj hdj).trans (by rw [hcol])⟩

/-- The facts of a run that the cache events read. -/
theorem seedGenKnownGame_support (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (w : SeedGenKnownTrace C E A.State × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run ∅)) :
    NoMpc w.2 ∧
      (∀ h, Good prims h → Agrees h w.2 → (∀ i, w.1.data i = none) ∨
        w.1.data = seedGenRevealAllFixed prims D h w.1.parts
          (seedGenCommitInbox D w.1.parts w.1.commitments w.1.sent) w.1.revealSent) ∧
      (∀ q y, (q, y) ∈ w.1.log → ¬ IsFixed q → w.2 q = some y) := by
  unfold seedGenKnownGame at hw
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
  refine ⟨n₇ n₆, fun h hg ha => seedGenPostTraced_fixed_data prims D A _ _ _ h _ (hfix h hg ha), ?_⟩
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

/-- The programming, extraction and echo costs fit in half the seed generation error. -/
theorem seedGenKnown_arith (q K : ℕ) (hK : K ≤ 1 + termCount C + C.n.choose 2) :
    2 * (q * K + K ^ 2) + ((q + C.n ^ 2) ^ 2 + 2 * (q + C.n ^ 2)) ≤ (q + seedGenSecrets C) ^ 2 := by
  have hn : 1 ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have hP : 2 * C.n.choose 2 ≤ C.n * C.n := by
    rw [Nat.choose_two_right]
    have := Nat.div_mul_le_self (C.n * (C.n - 1)) 2
    have h2 : C.n * (C.n - 1) ≤ C.n * C.n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  set P := C.n.choose 2
  set T := termCount C
  set n := C.n
  have hS : seedGenSecrets C = n * (1 + T + n) + 1 + T + P + n ^ 2 := rfl
  have hnT : T ≤ n * T := Nat.le_mul_of_pos_left T hn
  have hq : n ^ 2 + 1 + K ≤ seedGenSecrets C := by
    rw [hS]; nlinarith
  have h2K : 2 * K ≤ seedGenSecrets C := by
    rw [hS]; nlinarith
  have h2n : 2 * n ^ 2 + K ≤ seedGenSecrets C := by
    rw [hS]; nlinarith
  set s := seedGenSecrets C
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  nlinarith [Nat.zero_le (q * K), Nat.zero_le (q * n ^ 2), Nat.mul_le_mul h2K h2n, Nat.mul_le_mul h2n h2n]

end Arith

section Birthday

variable {C : Committee} {E : Type} (prims : Primitives)

/-- At most `k` compared cells of a cache are filled. -/
def SeedGenComparedCount (D : C.Coalition) (s : HashCache C) (k : ℕ) : Prop :=
  ∃ S : Finset (Query C), S.card ≤ k ∧ ∀ q, SeedGenComparedCell D q → s q ≠ none → q ∈ S

theorem seedGenComparedCount_insert {D : C.Coalition} {s : HashCache C} {k : ℕ}
    (h : SeedGenComparedCount D s k) (q : Query C) (u : HashOutput) :
    SeedGenComparedCount D (s.cacheQuery q u) (k + 1) := by
  obtain ⟨S, hS, hm⟩ := h
  refine ⟨insert q S, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hS 1), fun q' hc hq' => ?_⟩
  by_cases hq : q' = q
  · simpa only [hq] using Finset.mem_insert_self q S
  · rw [QueryCache.cacheQuery_of_ne s _ hq] at hq'
    exact Finset.mem_insert_of_mem (hm q' hc hq')

theorem seedGenComparedCount_insert_other {D : C.Coalition} {s : HashCache C} {k : ℕ}
    (h : SeedGenComparedCount D s k) (q : Query C) (hq : ¬ SeedGenComparedCell D q) (u : HashOutput) :
    SeedGenComparedCount D (s.cacheQuery q u) k := by
  obtain ⟨S, hS, hm⟩ := h
  refine ⟨S, hS, fun q' hc hq' => hm q' hc ?_⟩
  have hne : q' ≠ q := fun he => hq (he ▸ hc)
  rwa [QueryCache.cacheQuery_of_ne s _ hne] at hq'

/-- A collision after one insertion matches the new answer with an old compared cell. -/
theorem seedGenComparedCollision_insert {D : C.Coalition} {s : HashCache C}
    (hs : ¬ SeedGenComparedCollision D s) (q : Query C) (u : HashOutput)
    (h : SeedGenComparedCollision D (s.cacheQuery q u)) :
    SeedGenComparedCell D q ∧ ∃ q', q' ≠ q ∧ SeedGenComparedCell D q' ∧ s q' = some u := by
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
theorem probEvent_seedGenComparedCollision_fresh {D : C.Coalition} {s : HashCache C} {k : ℕ}
    (hs : ¬ SeedGenComparedCollision D s) (hk : SeedGenComparedCount D s k) (q : Query C) :
    Pr{let u ← $ᵗ HashOutput}[SeedGenComparedCollision D (s.cacheQuery q u)] ≤
      (k : ℝ≥0∞) / Fintype.card HashOutput := by
  obtain ⟨S, hS, hm⟩ := hk
  have hbad : (Finset.univ.filter fun u : HashOutput =>
      SeedGenComparedCollision D (s.cacheQuery q u)).card ≤ S.card := by
    let f : HashOutput → Query C := fun u =>
      if h : SeedGenComparedCollision D (s.cacheQuery q u) then
        (seedGenComparedCollision_insert hs q u h).2.choose else q
    refine Finset.card_le_card_of_injOn f (fun u hu => ?_) (fun u hu v hv heq => ?_)
    · have hc := (Finset.mem_filter.mp hu).2
      rw [show f u = _ from dif_pos hc]
      have hs' := (seedGenComparedCollision_insert hs q u hc).2.choose_spec
      exact hm _ hs'.2.1 (by rw [hs'.2.2]; exact Option.some_ne_none u)
    · have hc := (Finset.mem_filter.mp hu).2
      have hd := (Finset.mem_filter.mp hv).2
      rw [show f u = _ from dif_pos hc, show f v = _ from dif_pos hd] at heq
      have h₁ := (seedGenComparedCollision_insert hs q u hc).2.choose_spec.2.2
      have h₂ := (seedGenComparedCollision_insert hs q v hd).2.choose_spec.2.2
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
def seedGenComparedCall (D : C.Coalition) : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => SeedGenComparedCell D q
  | _ => False

/-- The compared calls of either copy of the world. -/
def seedGenComparedWorldCall (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => seedGenComparedCall D t
  | .inl (.inr _) => False
  | .inr t => seedGenComparedCall D t

/-- A programming query at a compared cell. -/
def seedGenComparedProgram (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inl (.inr x) => SeedGenComparedCell D x.1
  | _ => False

theorem seedGenCompared_hash_step {D : C.Coalition} {β : Type} (q : Query C) (s : HashCache C) (k m : ℕ)
    (hs : ¬ SeedGenComparedCollision D s) (hk : SeedGenComparedCount D s k)
    (g : HashOutput → HashCache C → ProbComp (β × HashCache C))
    (hg : ∀ u s', ¬ SeedGenComparedCollision D s' → SeedGenComparedCount D s' k →
      Pr{let z ← g u s'}[SeedGenComparedCollision D z.2] ≤ seedGenBirthdayCost k m)
    (hg' : SeedGenComparedCell D q → 0 < m ∧ ∀ u s', ¬ SeedGenComparedCollision D s' →
      SeedGenComparedCount D s' (k + 1) →
      Pr{let z ← g u s'}[SeedGenComparedCollision D z.2] ≤ seedGenBirthdayCost (k + 1) (m - 1)) :
    Pr{let z ← (hashAnswer prims q).run s >>= fun p => g p.1 p.2}[SeedGenComparedCollision D z.2] ≤
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
      by_cases hc : SeedGenComparedCell D q
      · obtain ⟨hm, hg''⟩ := hg' hc
        have h := prEvent_bind_le_prEvent_add_of_support ($ᵗ HashOutput)
          (fun u => g u (s.cacheQuery q u))
          (fun u => SeedGenComparedCollision D (s.cacheQuery q u))
          (fun z => SeedGenComparedCollision D z.2)
          (ε := seedGenBirthdayCost (k + 1) (m - 1))
          (fun u _ hu => hg'' u _ hu (seedGenComparedCount_insert hk q u))
        exact (h.trans (add_le_add (probEvent_seedGenComparedCollision_fresh hs hk q) le_rfl)).trans
          (seedGenBirthdayCost_step k m hm)
      · refine prEvent_bind_le_of_forall_le _ _ _ fun u => hg u _ ?_ (seedGenComparedCount_insert_other hk q hc u)
        intro hcol
        exact hc (seedGenComparedCollision_insert hs q u hcol).1

theorem seedGenCompared_local_step {D : C.Coalition} {β : Type} (t : (LocalSpec C).Domain) (s : HashCache C)
    (k m : ℕ) (hs : ¬ SeedGenComparedCollision D s) (hk : SeedGenComparedCount D s k)
    (g : (LocalSpec C).Range t → HashCache C → ProbComp (β × HashCache C))
    (hg : ∀ u s', ¬ SeedGenComparedCollision D s' → SeedGenComparedCount D s' k →
      Pr{let z ← g u s'}[SeedGenComparedCollision D z.2] ≤ seedGenBirthdayCost k m)
    (hg' : seedGenComparedCall D t → 0 < m ∧ ∀ u s', ¬ SeedGenComparedCollision D s' →
      SeedGenComparedCount D s' (k + 1) →
      Pr{let z ← g u s'}[SeedGenComparedCollision D z.2] ≤ seedGenBirthdayCost (k + 1) (m - 1)) :
    Pr{let z ← (localAnswer prims t).run s >>= fun p => g p.1 p.2}[SeedGenComparedCollision D z.2] ≤
      seedGenBirthdayCost k m := by
  rcases t with n | q | x
  · have heq : (localAnswer (C := C) prims (.inl n)).run s =
        (fun u => (u, s)) <$> (OracleComp.lift (OracleSpec.query (spec := unifSpec) n)) := by
      simp [localAnswer, unifFwdImpl]
    rw [heq]
    erw [bind_map_left]
    exact prEvent_bind_le_of_forall_le _ _ _ fun u => hg u s hs hk
  · exact seedGenCompared_hash_step prims q s k m hs hk g hg hg'
  · change Pr{let z ← (prgAnswer prims x).run s >>= fun p => g p.1 p.2}[
      SeedGenComparedCollision D z.2] ≤ _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    exact seedGenCompared_hash_step prims (.streamKey x.2.1) s k m hs hk
      (fun u s' => g (prims.aes.eval (truncateHash u) x.2.2) s') (fun u s' h₁ h₂ => hg _ s' h₁ h₂)
      (fun hc => by simp [SeedGenComparedCell] at hc)

/-- The birthday bound on the compared cells of a world computation. -/
theorem seedGenCompared_birthday {D : C.Coalition} {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ m s k, IsQueryBoundP oa (seedGenComparedWorldCall D) m → IsQueryBoundP oa (seedGenComparedProgram D) 0 →
      ¬ SeedGenComparedCollision D s → SeedGenComparedCount D s k →
      Pr{let z ← (simulateQ (worldAnswer prims) oa).run s}[SeedGenComparedCollision D z.2] ≤
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
        SeedGenComparedCollision D z.2] ≤ _
      refine seedGenCompared_local_step prims t s k m hs hk
        (fun u s' => (simulateQ (worldAnswer prims) (f u)).run s') (fun u s' h₁ h₂ => ?_) (fun hc => ?_)
      · have hu := hm.2 u
        have hpu := hp.2 u
        simp only [seedGenComparedWorldCall, seedGenComparedProgram, ↓reduceIte] at hu hpu
        by_cases hct : seedGenComparedCall D t
        · erw [if_pos hct] at hu
          exact (ih u (m - 1) s' k hu hpu h₁ h₂).trans (by
            unfold seedGenBirthdayCost
            exact ENNReal.div_le_div_right (by gcongr <;> omega) _)
        · erw [if_neg hct] at hu
          exact ih u m s' k hu hpu h₁ h₂
      · have hm' := hm.1.resolve_left (by simpa [seedGenComparedWorldCall] using hc)
        refine ⟨hm', fun u s' h₁ h₂ => ?_⟩
        have hu := hm.2 u
        have hpu := hp.2 u
        simp only [seedGenComparedWorldCall, seedGenComparedProgram, ↓reduceIte] at hu hpu
        erw [if_pos hc] at hu
        exact ih u (m - 1) s' (k + 1) hu hpu h₁ h₂
    · have hx : ¬ SeedGenComparedCell D x.1 := by
        simpa [seedGenComparedProgram] using hp.1
      change Pr{let z ← (programAnswer x).run s >>= fun p => (simulateQ (worldAnswer prims) (f p.1)).run p.2}[
        SeedGenComparedCollision D z.2] ≤ _
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hpr => ?_
      have hu := hm.2 p.1
      have hpu := hp.2 p.1
      simp only [seedGenComparedWorldCall, seedGenComparedProgram] at hu hpu
      erw [if_neg not_false] at hu
      erw [if_neg hx] at hpu
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
          exact hx (seedGenComparedCollision_insert hs x.1 x.2 hcol).1
      · simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hpr
        split_ifs at hpr
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpr
          subst hpr
          exact hk
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
            Set.mem_singleton_iff] at hpr
          subst hpr
          exact seedGenComparedCount_insert_other hk x.1 hx x.2
    · change Pr{let z ← (localAnswer prims t).run s >>= fun p => (simulateQ (worldAnswer prims) (f p.1)).run p.2}[
        SeedGenComparedCollision D z.2] ≤ _
      refine seedGenCompared_local_step prims t s k m hs hk
        (fun u s' => (simulateQ (worldAnswer prims) (f u)).run s') (fun u s' h₁ h₂ => ?_) (fun hc => ?_)
      · have hu := hm.2 u
        have hpu := hp.2 u
        simp only [seedGenComparedWorldCall, seedGenComparedProgram, ↓reduceIte] at hu hpu
        by_cases hct : seedGenComparedCall D t
        · erw [if_pos hct] at hu
          exact (ih u (m - 1) s' k hu hpu h₁ h₂).trans (by
            unfold seedGenBirthdayCost
            exact ENNReal.div_le_div_right (by gcongr <;> omega) _)
        · erw [if_neg hct] at hu
          exact ih u m s' k hu hpu h₁ h₂
      · have hm' := hm.1.resolve_left (by simpa [seedGenComparedWorldCall] using hc)
        refine ⟨hm', fun u s' h₁ h₂ => ?_⟩
        have hu := hm.2 u
        have hpu := hp.2 u
        simp only [seedGenComparedWorldCall, seedGenComparedProgram, ↓reduceIte] at hu hpu
        erw [if_pos hc] at hu
        exact ih u (m - 1) s' (k + 1) hu hpu h₁ h₂

theorem isQueryBoundP_free_compared (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (seedGenComparedCall D) n) :
    IsQueryBoundP (free oa) (seedGenComparedWorldCall D) n ∧ IsQueryBoundP (free oa) (seedGenComparedProgram D) 0 := by
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
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenComparedProgram]), fun u => ?_⟩
      simpa [seedGenComparedProgram] using (ih u _ (h.2 u)).2

theorem isQueryBoundP_observe_compared (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (seedGenComparedCall D) n) :
    IsQueryBoundP (observe oa) (seedGenComparedWorldCall D) n ∧
      IsQueryBoundP (observe oa) (seedGenComparedProgram D) 0 := by
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
          ⟨Or.inl (by simp [seedGenComparedWorldCall, seedGenComparedCall]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).1
        simp only [seedGenComparedCall, seedGenComparedWorldCall, ↓reduceIte] at hu ⊢
        exact hu
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenComparedProgram]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).2
        simp only [seedGenComparedProgram, ↓reduceIte] at hu ⊢
        exact hu
    · simp only [WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, WriterT.run_pure, bind_assoc,
        bind_map_left, map_pure, pure_bind]
      rw [adversary_hashQuery]
      constructor
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨by simpa [seedGenComparedWorldCall, seedGenComparedCall] using h.1, fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).1
        simp only [seedGenComparedCall, seedGenComparedWorldCall] at hu ⊢
        exact hu
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenComparedProgram]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).2
        simp only [seedGenComparedProgram, ↓reduceIte] at hu ⊢
        exact hu
    · simp only [WriterT.run_liftM, bind_map_left]
      rw [adversary_query]
      constructor
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨Or.inl (by simp [seedGenComparedWorldCall, seedGenComparedCall]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).1
        simp only [seedGenComparedCall, seedGenComparedWorldCall, ↓reduceIte] at hu ⊢
        exact hu
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenComparedProgram]), fun u => ?_⟩
        rw [isQueryBoundP_map_iff]
        have hu := (hk u).2
        simp only [seedGenComparedProgram, ↓reduceIte] at hu ⊢
        exact hu

theorem seedGenComparedCall_counted (D : C.Coalition) (t : (LocalSpec C).Domain)
    (h : seedGenComparedCall D t) : Counted t := by
  rcases t with t | (q | x)
  · exact h.elim
  · cases q <;> simp_all [seedGenComparedCall, SeedGenComparedCell, Counted]
  · exact h.elim

theorem isQueryBoundP_compared_of_counted (D : C.Coalition) {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) : IsQueryBoundP oa (seedGenComparedCall D) n :=
  h.of_imp (seedGenComparedCall_counted D)

theorem isQueryBoundP_compared_hash (D : C.Coalition) (q : Query C) :
    IsQueryBoundP (liftComp (hashQuery q) (LocalSpec C)) (seedGenComparedCall D)
      (if SeedGenComparedCell D q then 1 else 0) := by
  have e : liftComp (hashQuery q) (LocalSpec C) =
      (liftM ((LocalSpec C).query (.inr (.inl q))) : OracleComp (LocalSpec C) _) >>= pure := by
    rw [bind_pure]
    rfl
  rw [e]
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨?_, fun _ => trivial⟩
  by_cases hc : SeedGenComparedCell D q <;> simp [seedGenComparedCall, hc]

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

theorem isQueryBoundP_compared_derive (D : C.Coalition) (phase : Phase) (i : C.Party)
    (view : C.Party → Parts C) :
    IsQueryBoundP (liftComp (deriveKeys phase i view) (LocalSpec C)) (seedGenComparedCall D) 0 := by
  have hd (kind : KeyKind) (values : List HashOutput) :
      IsQueryBoundP (liftComp (hashQuery (C := C) (.derive phase kind values)) (LocalSpec C))
        (seedGenComparedCall D) 0 := by
    simpa [SeedGenComparedCell] using isQueryBoundP_compared_hash D (.derive phase kind values)
  have hterm : IsQueryBoundP (liftComp (C.terms.mapM fun T => if i ∈ C.holders T then
      hashQuery (C := C) (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
      else pure 0) (LocalSpec C)) (seedGenComparedCall D) 0 := by
    rw [seedGen_liftComp_mapM]
    have := seedGenIsQueryBoundP_listMapM (p := seedGenComparedCall D) (k := fun _ => 0)
      (f := fun T => liftComp (if i ∈ C.holders T then hashQuery (C := C) (.derive phase .term
        ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)) else pure 0) (LocalSpec C))
      (fun T => by
        by_cases hT : i ∈ C.holders T
        · rw [if_pos hT]; exact hd _ _
        · rw [if_neg hT, liftComp_pure]; trivial) C.terms
    simpa using this
  have hpair : IsQueryBoundP (liftComp (C.parties.mapM fun j => if h : j = i then pure 0 else
      hashQuery (C := C) (.derive phase .pair [(view (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
        (view (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) (LocalSpec C))
      (seedGenComparedCall D) 0 := by
    rw [seedGen_liftComp_mapM]
    have := seedGenIsQueryBoundP_listMapM (p := seedGenComparedCall D) (k := fun _ => 0)
      (f := fun j => liftComp (if h : j = i then pure 0 else hashQuery (C := C) (.derive phase .pair
        [(view (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
          (view (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) (LocalSpec C))
      (fun j => by
        by_cases hj : j = i
        · rw [dif_pos hj, liftComp_pure]; trivial
        · rw [dif_neg hj]; exact hd _ _) C.parties
    simpa using this
  unfold deriveKeys
  dsimp only
  by_cases hp : phase = .seedGen
  · rw [if_pos hp, liftComp_bind, ← Nat.zero_add 0]
    refine isQueryBoundP_bind (hd _ _) fun _ _ => ?_
    rw [liftComp_bind, ← Nat.zero_add 0]
    exact isQueryBoundP_bind hterm fun _ _ => by
      rw [liftComp_bind, ← Nat.zero_add 0]
      exact isQueryBoundP_bind hpair fun _ _ => by rw [liftComp_pure]; trivial
  · rw [if_neg hp, pure_bind, liftComp_bind, ← Nat.zero_add 0]
    exact isQueryBoundP_bind hterm fun _ _ => by
      rw [liftComp_bind, ← Nat.zero_add 0]
      exact isQueryBoundP_bind hpair fun _ _ => by rw [liftComp_pure]; trivial

theorem isQueryBoundP_compared_hashes (D : C.Coalition) (qs : C.Party → Query C) (b : ℕ)
    (hb : ((C.parties.map fun j => if SeedGenComparedCell D (qs j) then 1 else 0).sum) ≤ b) :
    IsQueryBoundP (liftComp (C.parties.mapM fun j => hashQuery (qs j)) (LocalSpec C)) (seedGenComparedCall D) b := by
  rw [seedGen_liftComp_mapM]
  exact (seedGenIsQueryBoundP_listMapM (fun j => isQueryBoundP_compared_hash D (qs j)) C.parties).mono hb

theorem seedGenParties_sum_le_card (f : C.Party → ℕ) (hf : ∀ j, f j ≤ 1) :
    (C.parties.map f).sum ≤ C.n := by
  have h := List.sum_le_card_nsmul (C.parties.map f) 1 (by simpa using fun j _ => hf j)
  simpa [Committee.parties] using h

theorem seedGenParties_sum_corrupt (D : C.Coalition) :
    (C.parties.map fun j => if j ∈ D.1 then 1 else 0).sum = D.1.card := by
  simp only [Committee.parties]
  rw [← Fin.sum_univ_def]
  simp

theorem isQueryBoundP_compared_revealCompute (D : C.Coalition) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) :
    IsQueryBoundP (seedGenRevealCompute i own committed revealed) (seedGenComparedCall D) (D.1.card + C.n) := by
  unfold seedGenRevealCompute
  split
  · trivial
  · refine isQueryBoundP_bind (isQueryBoundP_compared_hashes D _ D.1.card ?_) fun _ _ => ?_
    · rw [← seedGenParties_sum_corrupt D]
      apply le_of_eq
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j ∈ D.1 <;> simp [SeedGenComparedCell, hj]
    · rw [← Nat.zero_add C.n]
      split
      · trivial
      · exact isQueryBoundP_bind (isQueryBoundP_compared_derive D _ _ _) fun _ _ => by
          rw [← Nat.add_zero C.n]
          refine isQueryBoundP_bind ?_ fun _ _ => trivial
          unfold sharedQueries
          exact isQueryBoundP_compared_hashes D _ C.n (seedGenParties_sum_le_card _ fun j => by split <;> omega)

theorem isQueryBoundP_compared_revealComputations (D : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    IsQueryBoundP (seedGenRevealComputations D parts committed sent) (seedGenComparedCall D) (C.n * C.n) := by
  unfold seedGenRevealComputations
  refine (seedGenIsQueryBoundP_sequenceFin_sum _ (fun i => if i ∈ D.1 then 0 else D.1.card + C.n) fun i => ?_).mono ?_
  · split
    · trivial
    · rename_i h
      rw [if_neg (fun hi => h (Or.inl hi))]
      exact isQueryBoundP_compared_revealCompute D i (parts i) (committed i) _
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

theorem isQueryBoundP_compared_post (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (state : A.State)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    IsQueryBoundP (seedGenPostTraced D A state parts committed) (seedGenComparedCall D) (step + (C.n * C.n + step)) := by
  unfold seedGenPostTraced
  split
  · trivial
  · refine isQueryBoundP_bind (isQueryBoundP_compared_of_counted D _ _ (hround _ _)) fun r _ => ?_
    refine isQueryBoundP_bind (isQueryBoundP_compared_revealComputations D parts committed r.2) fun data _ => ?_
    rw [← Nat.add_zero step]
    refine isQueryBoundP_bind ?_ fun _ _ => trivial
    unfold seedGenFinishLocal
    split
    · trivial
    · rw [← Nat.add_zero step]
      exact isQueryBoundP_bind (isQueryBoundP_compared_of_counted D _ _ (hround _ _)) fun _ _ => trivial

theorem isQueryBoundP_compared_program (D : C.Coalition) (q : Query C) (v : HashOutput)
    (hq : ¬ SeedGenComparedCell D q) :
    IsQueryBoundP (program q v) (seedGenComparedWorldCall D) 0 ∧ IsQueryBoundP (program q v) (seedGenComparedProgram D) 0 := by
  have e : program q v = (liftM ((WorldSpec C).query (.inl (.inr (q, v)))) : OracleComp (WorldSpec C) _) >>= pure := by
    rw [bind_pure]
    rfl
  rw [e]
  exact ⟨(isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenComparedWorldCall]), fun _ => trivial⟩,
    (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simpa [seedGenComparedProgram] using hq), fun _ => trivial⟩⟩

theorem isQueryBoundP_compared_programs {ι : Type} (D : C.Coalition) (l : List ι) (q : ι → Query C)
    (v : ι → HashOutput) (hq : ∀ i, ¬ SeedGenComparedCell D (q i)) :
    IsQueryBoundP (l.mapM fun i => program (q i) (v i)) (seedGenComparedWorldCall D) 0 ∧
      IsQueryBoundP (l.mapM fun i => program (q i) (v i)) (seedGenComparedProgram D) 0 := by
  constructor
  · simpa using seedGenIsQueryBoundP_listMapM (k := fun _ => 0)
      (fun i => (isQueryBoundP_compared_program D (q i) (v i) (hq i)).1) l
  · simpa using seedGenIsQueryBoundP_listMapM (k := fun _ => 0)
      (fun i => (isQueryBoundP_compared_program D (q i) (v i) (hq i)).2) l

theorem isQueryBoundP_compared_programOk (D : C.Coalition) (parts : C.Party → Parts C) (log : CallLog C)
    (sent : C.Party → Mail C E) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (high : HashOutput) :
    IsQueryBoundP (seedGenProgramOk D parts log sent parameter seeds pairs high) (seedGenComparedWorldCall D) 0 ∧
      IsQueryBoundP (seedGenProgramOk D parts log sent parameter seeds pairs high) (seedGenComparedProgram D) 0 := by
  have hd (k : KeyKind) (values : List HashOutput) : ¬ SeedGenComparedCell D (.derive .seedGen k values) := by
    simp [SeedGenComparedCell]
  have h₁ := isQueryBoundP_compared_program D (seedGenParameterProgrammingInput D (seedGenProgramView D parts log sent))
    (seedGenFullParameter high parameter) (hd _ _)
  have h₂ := isQueryBoundP_compared_programs D (seedGenKnownCoordinates D)
    (seedGenTermProgrammingInput D (seedGenProgramView D parts log sent)) seeds (fun _ => hd _ _)
  have h₃ := isQueryBoundP_compared_programs D (seedGenCrossCoordinates D)
    (seedGenPairProgrammingInput D (seedGenProgramView D parts log sent)) pairs (fun _ => hd _ _)
  unfold seedGenProgramOk
  constructor
  · exact isQueryBoundP_bind (m := 0) h₁.1 fun _ _ => isQueryBoundP_bind (m := 0) h₂.1 fun _ _ =>
      isQueryBoundP_bind (m := 0) h₃.1 fun _ _ => trivial
  · exact isQueryBoundP_bind (m := 0) h₁.2 fun _ _ => isQueryBoundP_bind (m := 0) h₂.2 fun _ _ =>
      isQueryBoundP_bind (m := 0) h₃.2 fun _ _ => trivial

theorem isQueryBoundP_compared_commitments (D : C.Coalition) (parts : C.Party → Parts C) :
    IsQueryBoundP (seedGenInitialCommitments D parts) (seedGenComparedCall D) 0 := by
  unfold seedGenInitialCommitments
  refine (seedGenIsQueryBoundP_sequenceFin_sum _ (fun _ => 0) fun i => ?_).mono (by simp)
  split
  · trivial
  · rename_i hi
    exact isQueryBoundP_compared_hashes D _ 0 (by simp [SeedGenComparedCell, hi])

theorem isQueryBoundP_compared_sample (D : C.Coalition) {β : Type} (p : ProbComp β) :
    IsQueryBoundP (free (liftComp p (LocalSpec C))) (seedGenComparedWorldCall D) 0 ∧
      IsQueryBoundP (free (liftComp p (LocalSpec C))) (seedGenComparedProgram D) 0 :=
  isQueryBoundP_free_compared D _ 0 (isQueryBoundP_compared_of_counted D _ 0 (isQueryBoundP_liftComp_counted p))

theorem isQueryBoundP_compared_knownGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (seedGenKnownGame D A x z) (seedGenComparedWorldCall D) (start + 3 * step + C.n * C.n) ∧
      IsQueryBoundP (seedGenKnownGame D A x z) (seedGenComparedProgram D) 0 := by
  have o₁ := isQueryBoundP_observe_compared D _ _ (isQueryBoundP_compared_of_counted D _ _ (hstart (corruptInputs D x) z))
  unfold seedGenKnownGame
  constructor
  · refine (isQueryBoundP_bind o₁.1 fun _ _ => isQueryBoundP_bind (isQueryBoundP_compared_sample D _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_compared_sample D _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_compared D _ _ (isQueryBoundP_compared_commitments D _)).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_observe_compared D _ _
        (isQueryBoundP_compared_of_counted D _ _ (hround _ _))).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_compared_sample D _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_compared_programOk D _ _ _ _ _ _ _).1 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_compared D _ _
        (isQueryBoundP_compared_post D A step hround _ _ _)).1 fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by ring_nf; omega)
  · refine (isQueryBoundP_bind o₁.2 fun _ _ => isQueryBoundP_bind (isQueryBoundP_compared_sample D _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_compared_sample D _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_compared D _ _ (isQueryBoundP_compared_commitments D _)).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_observe_compared D _ _
        (isQueryBoundP_compared_of_counted D _ _ (hround _ _))).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_compared_sample D _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_compared_programOk D _ _ _ _ _ _ _).2 fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_free_compared D _ _
        (isQueryBoundP_compared_post D A step hround _ _ _)).2 fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by simp)

/-- A cell that was empty in `b` holds its target answer in `s`. -/
def SeedGenTargetHit (target : Query C → Option HashOutput) (b s : HashCache C) : Prop :=
  ∃ x c, target x = some c ∧ b x = none ∧ s x = some c

theorem seedGenTarget_hash_step {D : C.Coalition} {β : Type} (target : Query C → Option HashOutput)
    (htarget : ∀ x, target x ≠ none → SeedGenComparedCell D x) (b : HashCache C) (q : Query C)
    (s : HashCache C) (m : ℕ) (hs : ¬ SeedGenTargetHit target b s)
    (g : HashOutput → HashCache C → ProbComp (β × HashCache C))
    (hg : ∀ u s', ¬ SeedGenTargetHit target b s' →
      Pr{let z ← g u s'}[SeedGenTargetHit target b z.2] ≤ (m : ℝ≥0∞) / Fintype.card HashOutput)
    (hg' : SeedGenComparedCell D q → 0 < m ∧ ∀ u s', ¬ SeedGenTargetHit target b s' →
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
      by_cases hc : SeedGenComparedCell D q
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
theorem seedGenTarget_local {D : C.Coalition} (target : Query C → Option HashOutput)
    (htarget : ∀ x, target x ≠ none → SeedGenComparedCell D x) (b : HashCache C) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∀ m s, IsQueryBoundP oa (seedGenComparedCall D) m → ¬ SeedGenTargetHit target b s →
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
      simpa [seedGenComparedCall] using hm.2 u
    · change Pr{let z ← (hashAnswer prims q).run s >>= fun p => (simulateQ (localAnswer prims) (f p.1)).run p.2}[
        SeedGenTargetHit target b z.2] ≤ _
      refine seedGenTarget_hash_step prims target htarget b q s m hs
        (fun u s' => (simulateQ (localAnswer prims) (f u)).run s') (fun u s' h => ?_) (fun hc => ?_)
      · have hu := hm.2 u
        simp only [seedGenComparedCall] at hu
        by_cases hct : SeedGenComparedCell D q
        · erw [if_pos hct] at hu
          exact (ih u (m - 1) s' hu h).trans (ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le m 1) _)
        · erw [if_neg hct] at hu
          exact ih u m s' hu h
      · have hm' := hm.1.resolve_left (by simpa [seedGenComparedCall] using hc)
        refine ⟨hm', fun u s' h => ?_⟩
        have hu := hm.2 u
        simp only [seedGenComparedCall] at hu
        erw [if_pos hc] at hu
        exact ih u (m - 1) s' hu h
    · change Pr{let z ← (prgAnswer prims x).run s >>= fun p => (simulateQ (localAnswer prims) (f p.1)).run p.2}[
        SeedGenTargetHit target b z.2] ≤ _
      simp only [prgAnswer, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      refine seedGenTarget_hash_step prims target htarget b (.streamKey x.2.1) s m hs
        (fun u s' => (simulateQ (localAnswer prims) (f (prims.aes.eval (truncateHash u) x.2.2))).run s')
        (fun u s' h => ih _ m s' ?_ h) (fun hc => by simp [SeedGenComparedCell] at hc)
      simpa [seedGenComparedCall] using hm.2 _

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

theorem localAnswer_compared_unchanged (D : C.Coalition) (t : (LocalSpec C).Domain)
    (ht : ¬ seedGenComparedCall D t) (s : HashCache C) (p : (LocalSpec C).Range t × HashCache C)
    (hp : p ∈ support ((localAnswer prims t).run s)) (x : Query C) (hx : SeedGenComparedCell D x) :
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
      simp [SeedGenComparedCell] at hx
    have hfix : ¬ IsFixed (Query.streamKey (C := C) y.2.1) := by simp [IsFixed]
    rw [hashAnswer_of_not_isFixed prims hfix] at hp'
    exact (randomOracle_support _ s p' hp').2.2 x hxq

/-- A world computation with no compared call and no compared programming leaves every compared
cell unchanged. -/
theorem seedGenCompared_unchanged {D : C.Coalition} {α : Type} (oa : OracleComp (WorldSpec C) α) :
    IsQueryBoundP oa (seedGenComparedWorldCall D) 0 → IsQueryBoundP oa (seedGenComparedProgram D) 0 →
      ∀ s z, z ∈ support ((simulateQ (worldAnswer prims) oa).run s) →
        ∀ x, SeedGenComparedCell D x → z.2 x = s x := by
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
    have hc : ¬ seedGenComparedWorldCall D t := fun h => by simpa using hm.1.resolve_left (not_not.mpr h)
    have hpr : ¬ seedGenComparedProgram D t := fun h => by simpa using hp.1.resolve_left (not_not.mpr h)
    have hmu := hm.2 p.1
    have hpu := hp.2 p.1
    simp only [if_neg hc, if_neg hpr] at hmu hpu
    rw [ih p.1 hmu hpu p.2 z hz x hx]
    rcases t with (t | y) | t
    · exact localAnswer_compared_unchanged prims D t hc s p hp' x hx
    · have hy : ¬ SeedGenComparedCell D y.1 := hpr
      change p ∈ support ((programAnswer y).run s) at hp'
      simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hp'
      split_ifs at hp'
      · simp only [StateT.run_pure, support_pure] at hp'
        rw [hp']
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure] at hp'
        rw [hp']
        exact QueryCache.cacheQuery_of_ne s _ (fun he => hy (he ▸ hx))
    · exact localAnswer_compared_unchanged prims D t hc s p hp' x hx

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
def seedGenKnownPrefix (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    OracleComp (WorldSpec C) (SeedGenKnownPre C E A.State) := do
  let (state, log) ← observe (A.start (corruptInputs D x) z)
  let (parameter, seeds, pairs) ← free (liftComp (seedGenDealerSamples (C := C)) (LocalSpec C))
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C)))
    (LocalSpec C))
  let commitments ← free (seedGenInitialCommitments D parts)
  let ((st, sent), calls) ← observe (A.round state fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
    commitOutbox i (commitments i) c else none)
  let high ← free (liftComp ($ᵗ HashOutput) (LocalSpec C))
  let ok ← seedGenProgramOk D parts (log ++ calls) sent parameter seeds pairs high
  pure ⟨parameter, seeds, pairs, parts, log ++ calls, sent, commitments, ok, st⟩

theorem seedGenKnownGame_eq_prefix (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    seedGenKnownGame D A x z = seedGenKnownPrefix D A x z >>= fun pre =>
      free (seedGenPostTraced D A pre.state pre.parts (seedGenCommitInbox D pre.parts pre.commitments pre.sent)) >>=
        fun r => pure ⟨pre.parameter, pre.seeds, pre.pairs, pre.parts, pre.log, pre.sent, pre.commitments, pre.ok,
          r.1, r.2.1, r.2.2.1, r.2.2.2⟩ := by
  unfold seedGenKnownGame seedGenKnownPrefix
  simp only [bind_assoc, pure_bind]

/-- Before the last two rounds, every filled commitment cell of a corrupt sender is logged. -/
theorem seedGenKnownPrefix_unlogged (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (w : SeedGenKnownPre C E A.State × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (seedGenKnownPrefix D A x z)).run ∅))
    (j i : C.Party) (reveal : List HashOutput) (hj : j ∈ D.1)
    (hlog : ∀ y, (Query.commit (C := C) .seedGen j i reveal, y) ∉ w.1.log) :
    w.2 (.commit .seedGen j i reveal) = none := by
  have hx : SeedGenComparedCell D (.commit .seedGen j i reveal) := hj
  have hns : ¬ ∃ k, Query.commit (C := C) .seedGen j i reveal = .streamKey k := by
    rintro ⟨k, hk⟩
    cases hk
  unfold seedGenKnownPrefix at hw
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hw
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, p₄, hp₄, p₅, hp₅, p₆, hp₆, hfin⟩ := hw
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
  subst hfin
  simp only at hlog ⊢
  have n₀ : p₀.2 (.commit .seedGen j i reveal) = none := by
    by_contra hne
    rcases seedGenObserve_new_logged prims _ ∅ p₀ hp₀ _ rfl hne with ⟨y, hy⟩ | h
    · exact hlog y (List.mem_append_left _ hy)
    · exact hns h
  have u₁ := seedGenCompared_unchanged prims _ (isQueryBoundP_compared_sample D _).1
    (isQueryBoundP_compared_sample D _).2 _ p₁ hp₁ _ hx
  have u₂ := seedGenCompared_unchanged prims _ (isQueryBoundP_compared_sample D _).1
    (isQueryBoundP_compared_sample D _).2 _ p₂ hp₂ _ hx
  have hcm := isQueryBoundP_free_compared D _ 0 (isQueryBoundP_compared_commitments D p₂.1)
  have u₃ := seedGenCompared_unchanged prims _ hcm.1 hcm.2 _ p₃ hp₃ _ hx
  have n₄ : p₄.2 (.commit .seedGen j i reveal) = none := by
    by_contra hne
    rcases seedGenObserve_new_logged prims _ _ p₄ hp₄ _ (by rw [u₃, u₂, u₁, n₀]) hne with ⟨y, hy⟩ | h
    · exact hlog y (List.mem_append_right _ hy)
    · exact hns h
  have u₅ := seedGenCompared_unchanged prims _ (isQueryBoundP_compared_sample D _).1
    (isQueryBoundP_compared_sample D _).2 _ p₅ hp₅ _ hx
  have hpo := isQueryBoundP_compared_programOk (E := E) D p₂.1 (p₀.1.2 ++ p₄.1.2) p₄.1.1.2 p₁.1.1 p₁.1.2.1
    p₁.1.2.2 p₅.1
  have u₆ := seedGenCompared_unchanged prims _ hpo.1 hpo.2 _ p₆ hp₆ _ hx
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
    simp only [if_neg hc] at hmu
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

theorem seedGenCell_commitments (D : C.Coalition) (parts : C.Party → Parts C) (kind : KeyKind)
    (values : List HashOutput) :
    IsQueryBoundP (seedGenInitialCommitments D parts) (seedGenCellCall (.derive .seedGen kind values)) 0 := by
  unfold seedGenInitialCommitments
  refine (seedGenIsQueryBoundP_sequenceFin_sum _ (fun _ => 0) fun i => ?_).mono (by simp)
  split
  · trivial
  · rw [commitQueries, seedGen_liftComp_mapM]
    refine (seedGenIsQueryBoundP_listMapM (k := fun _ => 0) (fun j => ?_) C.parties).mono (by simp)
    have e : liftComp (hashQuery (C := C) (.commit .seedGen i j (revealTo .seedGen (parts i) i j))) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr (.inl (.commit .seedGen i j (revealTo .seedGen (parts i) i j))))) :
          OracleComp (LocalSpec C) _) >>= pure := by
      rw [bind_pure]
      rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [seedGenCellCall]), fun _ => trivial⟩

/-- A programming input of the prefix is a logged query, or two programming inputs are equal. -/
def SeedGenProgramAlias (D : C.Coalition) {σ : Type} (pre : SeedGenKnownPre C E σ) : Prop :=
  (∃ x ∈ seedGenProgrammingInputs D (seedGenProgramView D pre.parts pre.log pre.sent), ∃ y, (x, y) ∈ pre.log) ∨
    ¬ (seedGenProgrammingInputs D (seedGenProgramView D pre.parts pre.log pre.sent)).Nodup

theorem seedGenProgrammingInputs_derive (D : C.Coalition) (view : C.Party → C.Party → Parts C) (x : Query C)
    (hx : x ∈ seedGenProgrammingInputs D view) : ∃ kind values, x = .derive .seedGen kind values := by
  simp only [seedGenProgrammingInputs, List.mem_append, List.mem_cons, List.mem_map] at hx
  rcases hx with (rfl | ⟨T, _, rfl⟩) | ⟨p, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem seedGenWorld_sample_support {β : Type} (p : ProbComp β) (s : HashCache C) (w : β × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (free (liftComp p (LocalSpec C)))).run s)) : w.2 = s := by
  rw [simulateQ_world_sample] at hw
  simp only [StateT.run_lift, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
  obtain ⟨a, _, rfl⟩ := hw
  rfl

/-- A failed programming of the prefix is an alias of a programming input. -/
theorem seedGenKnownPrefix_alias_of_fail (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (w : SeedGenKnownPre C E A.State × HashCache C)
    (hw : w ∈ support ((simulateQ (worldAnswer prims) (seedGenKnownPrefix D A x z)).run ∅))
    (hok : w.1.ok = false) : SeedGenProgramAlias D w.1 := by
  by_contra hA
  simp only [SeedGenProgramAlias, not_or, not_exists, not_and, not_not] at hA
  obtain ⟨hlog, hnodup⟩ := hA
  unfold seedGenKnownPrefix at hw
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hw
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, p₃, hp₃, p₄, hp₄, p₅, hp₅, p₆, hp₆, hfin⟩ := hw
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
  subst hfin
  simp only at hlog hnodup hok
  have hfresh : ∀ q ∈ seedGenProgrammingInputs D (seedGenProgramView D p₂.1 (p₀.1.2 ++ p₄.1.2) p₄.1.1.2),
      p₅.2 q = none := by
    intro q hq
    obtain ⟨kind, values, rfl⟩ := seedGenProgrammingInputs_derive D _ q hq
    have hns : ¬ ∃ k, Query.derive (C := C) .seedGen kind values = .streamKey k := by
      rintro ⟨k, hk⟩
      cases hk
    have n₀ : p₀.2 (.derive .seedGen kind values) = none := by
      by_contra hne
      rcases seedGenObserve_new_logged prims _ ∅ p₀ hp₀ _ rfl hne with ⟨y, hy⟩ | h
      · exact hlog _ hq y (List.mem_append_left _ hy)
      · exact hns h
    have u₁ := seedGenWorld_sample_support prims _ _ p₁ hp₁
    have u₂ := seedGenWorld_sample_support prims _ _ p₂ hp₂
    rw [simulateQ_free] at hp₃
    have u₃ := seedGenCell_unchanged prims (.derive .seedGen kind values) (fun k hk => by cases hk) _
      (seedGenCell_commitments D p₂.1 kind values) _ p₃ hp₃
    have n₄ : p₄.2 (.derive .seedGen kind values) = none := by
      by_contra hne
      rcases seedGenObserve_new_logged prims _ _ p₄ hp₄ _ (by rw [u₃, u₂, u₁, n₀]) hne with ⟨y, hy⟩ | h
      · exact hlog _ hq y (List.mem_append_right _ hy)
      · exact hns h
    rw [seedGenWorld_sample_support prims _ _ p₅ hp₅, n₄]
  have := seedGenProgramOk_fresh prims D _ _ _ _ _ _ _ _ p₆ hp₆ hfresh hnodup
  rw [this] at hok
  cases hok

end Birthday

section Main

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A programming attempt fails only if a counted call before the programming hits an honest part,
or if two programming inputs coincide (CDG+18). -/
def SeedGenProgramFailBound : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let r ← runWorld prims (seedGenKnownGame D A x z)}[SeedGenProgramFail r.1]).toReal ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ) / 2 ^ 256

/-- A missed extraction or an echo collision needs a collision of two compared answers or a fresh
opening that hits its earlier commitment. -/
def SeedGenExtractEchoBound : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let r ← runWorld prims (seedGenKnownGame D A x z)}[
      SeedGenExtractFail D r.1 ∨ SeedGenEchoCollision D r.1]).toReal ≤
      (((q + C.n ^ 2) ^ 2 + 2 * (q + C.n ^ 2) : ℕ) : ℝ) / 2 ^ 257

/-- The birthday bound on the compared cells. At most `q` counted calls and `n²` honest shared-key
hashes and corrupt openings sample them. -/
def SeedGenComparedCollisionBound : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let w ← (simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run ∅}[
      SeedGenComparedCollision D w.2]).toReal ≤
      (((q + C.n ^ 2) ^ 2 : ℕ) : ℝ) / 2 ^ 257

/-- Each of at most `q + n²` openings that are sampled after the commit round hits its commitment
with probability `2^-256`. -/
def SeedGenFreshOpeningBound : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let w ← (simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run ∅}[
      SeedGenFreshOpening D w.1 w.2]).toReal ≤
      ((q + C.n ^ 2 : ℕ) : ℝ) / 2 ^ 256

theorem seedGenExtractEchoBound_of_cache (hC : SeedGenComparedCollisionBound (C := C) (E := E) prims)
    (hF : SeedGenFreshOpeningBound (C := C) (E := E) prims) : SeedGenExtractEchoBound (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hmono : Pr{let r ← runWorld prims (seedGenKnownGame D A x z)}[
      SeedGenExtractFail D r.1 ∨ SeedGenEchoCollision D r.1] ≤
      Pr{let w ← (simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run ∅}[SeedGenComparedCollision D w.2] +
      Pr{let w ← (simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run ∅}[
        SeedGenFreshOpening D w.1 w.2] := by
    rw [probEvent_runWorld_fst prims (seedGenKnownGame D A x z)
      (fun r => SeedGenExtractFail D r ∨ SeedGenEchoCollision D r), StateT.run'_eq, prEvent_map]
    refine le_trans (prEvent_mono_of_support _ _ _ fun w hw hb => ?_) (prEvent_or_le _ _ _)
    obtain ⟨hn, hdata, hlog⟩ := seedGenKnownGame_support prims D A x z w hw
    exact seedGenKnown_cacheEvent_of_bad prims D w.1 w.2 hn hdata hlog hb
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) hmono).trans ?_
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  refine (add_le_add (hC D A x z Z q hq) (hF D A x z Z q hq)).trans (le_of_eq ?_)
  have h256 : (2 : ℝ) ^ 257 = 2 * 2 ^ 256 := pow_succ' 2 256
  rw [h256]
  push_cast
  field_simp

theorem seedGenComparedCollisionBound_proof : SeedGenComparedCollisionBound (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨start, step, final, hsum, hs, hr, _, _⟩ := hq
  obtain ⟨h₁, h₂⟩ := isQueryBoundP_compared_knownGame D A x z start step hs hr
  have h0 : ¬ SeedGenComparedCollision D (∅ : HashCache C) := by
    rintro ⟨_, _, _, _, _, _, h, _⟩
    simp at h
  have hc0 : SeedGenComparedCount D (∅ : HashCache C) 0 := ⟨∅, by simp, by simp⟩
  have hb := seedGenCompared_birthday prims (seedGenKnownGame D A x z) _ ∅ 0 h₁ h₂ h0 hc0
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
def seedGenOpeningTarget (D : C.Coalition) (sent : C.Party → Mail C E) : Query C → Option HashOutput
  | .commit .seedGen j i _ => if j ∈ D.1 ∧ i ∉ D.1 then
      (match Msg.hashesOf (sent j i) with
        | [c] => some c
        | _ => none) else none
  | _ => none

theorem seedGenOpeningTarget_compared (D : C.Coalition) (sent : C.Party → Mail C E) (x : Query C)
    (hx : seedGenOpeningTarget D sent x ≠ none) : SeedGenComparedCell D x := by
  unfold seedGenOpeningTarget at hx
  split at hx
  · split_ifs at hx with h
    · exact h.1
    · exact absurd rfl hx
  · exact absurd rfl hx

theorem seedGenFreshOpeningBound_proof : SeedGenFreshOpeningBound (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨start, step, final, hsum, hs, hr, _, _⟩ := hq
  have hkey : Pr{let w ← (simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run ∅}[
      SeedGenFreshOpening D w.1 w.2] ≤
      ((step + (C.n * C.n + step) : ℕ) : ℝ≥0∞) / Fintype.card HashOutput := by
    rw [seedGenKnownGame_eq_prefix, simulateQ_bind, StateT.run_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun w hw => ?_
    rw [simulateQ_bind, simulateQ_free, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure]
    rw [bind_pure_comp, prEvent_map]
    refine (prEvent_mono _ _ _ fun r hf => ?_).trans
      (seedGenTarget_local prims (seedGenOpeningTarget D w.1.sent) (seedGenOpeningTarget_compared D w.1.sent) w.2 _
        _ w.2 (isQueryBoundP_compared_post D A step hr _ _ _) ?_)
    · obtain ⟨j, i, rv, c, hj, hi, hc, hsent, hlog⟩ := hf
      refine ⟨.commit .seedGen j i rv, c, ?_, seedGenKnownPrefix_unlogged prims D A x z w hw j i rv hj hlog, hc⟩
      simp [seedGenOpeningTarget, hj, hi, hsent]
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
theorem seedGenKnownMismatch_of_bounds (hP : SeedGenProgramFailBound (C := C) (E := E) prims)
    (hX : SeedGenExtractEchoBound (C := C) (E := E) prims) : SeedGenKnownMismatch (C := C) (E := E) prims := by
  intro D A x z Z q hq
  have hmono : Pr{let r ← runWorld prims (seedGenCommonGame D A x z)}[
      seedGenMixedProjection D r.1 ≠ seedGenIdealProjection D r.1] ≤
      Pr{let r ← runWorld prims (seedGenKnownGame D A x z)}[SeedGenProgramFail r.1] +
      Pr{let r ← runWorld prims (seedGenKnownGame D A x z)}[SeedGenExtractFail D r.1 ∨ SeedGenEchoCollision D r.1] := by
    rw [probEvent_runWorld_fst prims (seedGenCommonGame D A x z)
        (fun r => seedGenMixedProjection D r ≠ seedGenIdealProjection D r),
      probEvent_runWorld_fst prims (seedGenKnownGame D A x z) SeedGenProgramFail,
      probEvent_runWorld_fst prims (seedGenKnownGame D A x z) (fun r => SeedGenExtractFail D r ∨ SeedGenEchoCollision D r),
      simulateQ_seedGenCommonGame_known, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
      prEvent_map]
    simp only [StateT.run'_eq, prEvent_map]
    refine le_trans (prEvent_mono_of_support _ _ _ fun p hp hm => ?_) (prEvent_or_le _ _ _)
    have hr : p.1 ∈ support ((simulateQ (worldAnswer prims) (seedGenKnownGame D A x z)).run' ∅) := by
      rw [StateT.run'_eq, support_map]
      exact ⟨p, hp, rfl⟩
    rcases seedGenKnown_bad_of_mismatch prims D A x z p.1 hr hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) hmono).trans ?_
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  refine (add_le_add (hP D A x z Z q hq) (hX D A x z Z q hq)).trans ?_
  have ha := seedGenKnown_arith (C := C) q (seedGenProgrammingCount D) (seedGenProgrammingCount_le D)
  have ha' : (2 * (q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2) +
      ((q + C.n ^ 2) ^ 2 + 2 * (q + C.n ^ 2)) : ℝ) ≤ ((q + seedGenSecrets C) ^ 2 : ℕ) := by exact_mod_cast ha
  unfold seedGenHashError
  push_cast at ha' ⊢
  rw [div_div, show (2 : ℝ) ^ 256 * 2 = 2 ^ 257 from (pow_succ 2 256).symm]
  have h256 : (2 : ℝ) ^ 257 = 2 * 2 ^ 256 := pow_succ' 2 256
  rw [h256] at ⊢
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [ha', show (0 : ℝ) < 2 ^ 256 by positivity]

/-- The guessing bound of the programming inputs before the programming (CDG+18). Each counted call
before the programming hits an honest part of a programming input with probability at most
`K / 2^256`, and each pair of programming inputs is equal with probability at most `2^-256`. -/
def SeedGenProgramAliasBound : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    (Pr{let w ← (simulateQ (worldAnswer prims) (seedGenKnownPrefix D A x z)).run ∅}[
      SeedGenProgramAlias D w.1]).toReal ≤
      ((q * seedGenProgrammingCount D + seedGenProgrammingCount D ^ 2 : ℕ) : ℝ) / 2 ^ 256

theorem seedGenProgramFailBound_of_alias (h : SeedGenProgramAliasBound (C := C) (E := E) prims) :
    SeedGenProgramFailBound (C := C) (E := E) prims := by
  intro D A x z Z q hq
  refine le_trans (ENNReal.toReal_mono (prEvent_ne_top _) ?_) (h D A x z Z q hq)
  rw [probEvent_runWorld_fst prims (seedGenKnownGame D A x z) SeedGenProgramFail, StateT.run'_eq, prEvent_map,
    seedGenKnownGame_eq_prefix, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_prEvent_add_of_support _ _
    (fun w : SeedGenKnownPre C E A.State × HashCache C => ¬ w.1.ok = true) _ (ε := 0)
    (fun w _ hok => le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hf => by
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
        Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      exact hok (by simpa [SeedGenProgramFail] using hf)))).trans ?_
  rw [add_zero]
  exact prEvent_mono_of_support _ _ _ fun w hw hf =>
    seedGenKnownPrefix_alias_of_fail prims D A x z w hw (by simpa using hf)

/-- The known half from the programming bound. -/
theorem seedGenKnownMismatch_of_programFail (hP : SeedGenProgramFailBound (C := C) (E := E) prims) :
    SeedGenKnownMismatch (C := C) (E := E) prims :=
  seedGenKnownMismatch_of_bounds prims hP
    (seedGenExtractEchoBound_of_cache prims (seedGenComparedCollisionBound_proof prims) (seedGenFreshOpeningBound_proof prims))

/-- `SeedGenSecurityStatement` from the guessing bound of the programming inputs. -/
theorem seedGenSecurityDone_of_programAlias (hA : SeedGenProgramAliasBound (C := C) (E := E) prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurityComplete prims (seedGenKnownMismatch_of_programFail prims (seedGenProgramFailBound_of_alias prims hA))

end Main

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.seedGenSecurityDone_of_programAlias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.seedGenSecurityDone_of_programAlias
