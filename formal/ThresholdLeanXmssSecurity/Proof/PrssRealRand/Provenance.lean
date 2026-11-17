import ThresholdLeanXmssSecurity.Proof.PrssRealRand.KeyBound
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.NoHidden
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.NormalForm

/-!
# The provenance of the private answers and of the stream-key cells

In the ideal joint world, each private answer and each stream-key cell at the end of the logged setup
run, the draws and `Z` has a source in the view of the flag.

* `countedLog` is the log of the adversary as a handler of the world. `setupLog` states that the setup
  run with `logAdversary A` is the setup run with `A` under `countedLog`. So `logAdversaryErase` holds.
* `setupProvenance` and `loggedProvenance` are the facts for the setup and for a logged step of the
  adversary or of `Z`. Each new stream-key cell is in the log, and no private answer is new.
* `liveStreamsProvenance` is the fact for the draws of the live honest operators. A new private answer
  is for a key that a live honest operator holds for a hidden name. A new stream-key cell is for a known
  key.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Logs

variable {C : Committee}

/-- The real run of the PRSS setup. -/
abbrev setupRun {E : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) : OracleComp (WorldSpec C) (A.State × (C.Party → Option (Keys C))) :=
  realExecution D A noFunctionality setupRounds
    (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z

/-- The stream key that a counted call can write to the cache. A counted local call has the key of
`streamKeyOf`, and a programming of a stream key has that key. A free call has none. -/
def countedKey : (WorldSpec C).Domain → Option HashOutput
  | .inl (.inl t) => streamKeyOf t
  | .inl (.inr (.streamKey k, _)) => some k
  | _ => none

/-- The log of the adversary as a handler of the world. Each call goes to the oracle, and the stream
key of a counted call goes to the log. -/
def countedLog : QueryImpl (WorldSpec C) (StateT (List HashOutput) (OracleComp (WorldSpec C))) := fun t => do
  let u ← StateT.lift (query (spec := WorldSpec C) t : OracleComp (WorldSpec C) _)
  modify fun log => (countedKey t).toList ++ log
  pure u

/-- A computation under `countedLog`, without the log, is the computation. -/
theorem countedLogErase : ∀ (α : Type) (oa : OracleComp (WorldSpec C) α) (log : List HashOutput),
    Prod.fst <$> (simulateQ countedLog oa).run log = oa := by
  intro α oa log
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, countedLog, StateT.run_lift, StateT.run_modify, bind_assoc, pure_bind,
      map_bind, ih, HasQuery.instOfMonadLift_query]

/-- A logged computation without its log is the computation. -/
theorem fst_map_run_logImpl {α : Type} (oa : OracleComp (LocalSpec C) α) (log : List HashOutput) :
    Prod.fst <$> (simulateQ logImpl oa).run log = oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, logImpl, StateT.run_lift, StateT.run_modify, bind_assoc, pure_bind,
      map_bind, ih, HasQuery.instOfMonadLift_query]

/-- The adversary role commutes with a map. -/
theorem worldRoles_adversary_map {γ δ : Type} (g : γ → δ) (oa : OracleComp (LocalSpec C) γ) :
    (worldRoles (C := C)).adversary (g <$> oa) = g <$> (worldRoles (C := C)).adversary oa := by
  simp only [worldRoles, counted, liftComp_map, simulateQ_map]

/-- A logged step of the adversary is the step under `countedLog`. -/
theorem adversaryLog : ∀ (α : Type) (oa : OracleComp (LocalSpec C) α) (log : List HashOutput),
    worldRoles.adversary ((simulateQ logImpl oa).run log) =
      (simulateQ countedLog (worldRoles.adversary oa)).run log := by
  intro α oa log
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp only [simulateQ_pure, StateT.run_pure]; rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, logImpl, StateT.run_lift, StateT.run_modify, bind_assoc, pure_bind,
      HasQuery.instOfMonadLift_query]
    rw [adversary_bind, adversary_bind, adversary_query]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, countedLog, StateT.run_lift,
      StateT.run_modify, bind_assoc, pure_bind, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      HasQuery.instOfMonadLift_query, ih]
    rfl

/-- A free computation under `countedLog` keeps the log. -/
theorem countedLog_free {α : Type} (oa : OracleComp (LocalSpec C) α) (log : List HashOutput) :
    (simulateQ countedLog (free oa)).run log = (fun a => (a, log)) <$> free oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp only [free_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    rw [free_bind, simulateQ_bind, StateT.run_bind]
    simp only [ih, map_bind]
    simp [free, countedLog, countedKey]

section Setup

variable {E : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)

theorem logAdversary_round (st : A.State) (log : List HashOutput) (sent : C.Party → C.Party → Option (Msg E)) :
    worldRoles.adversary ((logAdversary A).round ((st, log) : (logAdversary A).State) sent) =
      (fun p => ((p.1.1, p.2), p.1.2)) <$> (simulateQ countedLog (worldRoles.adversary (A.round st sent))).run log := by
  change worldRoles.adversary ((simulateQ logImpl (A.round st sent)).run log >>= fun p => pure ((p.1.1, p.2), p.1.2)) = _
  rw [adversary_bind, adversaryLog, map_eq_bind_pure_comp]
  rfl

/-- One round with `logAdversary A` is the round with `A` under `countedLog`. -/
theorem stepRound_log (st : A.State) (log : List HashOutput) (steps : C.Party → Step C E RealSpec (Keys C)) :
    (fun r => ((r.1.1, r.2.1, r.2.2), r.1.2)) <$>
        stepRound worldRoles D (logAdversary A) noFunctionality ((st, log) : (logAdversary A).State) steps =
      (stepRound (seedGenMapRoles countedLog worldRoles) D A noFunctionality st steps).run log := by
  simp only [stepRound, callInput_real, Option.isSome_none, Bool.false_eq_true, and_false, exists_false,
    false_and, ite_false, StateT.run_bind, seedGenMapRoles, logAdversary_round]
  refine (map_bind _ _ _).trans ((bind_map_left _ _ _).trans (bind_congr fun p => ?_))
  rw [sequenceFin_run_keep p.2 _ _ fun j => ?h]
  · simp only [map_bind, map_pure, bind_map_left, StateT.run_pure]
    rfl
  · split <;> (try split) <;> simp only [StateT.run_pure, map_pure, worldRoles, countedLog_free]

/-- The rounds with `logAdversary A` are the rounds with `A` under `countedLog`. -/
theorem executeRounds_log : ∀ (fuel : ℕ) (st : A.State) (log : List HashOutput)
    (steps : C.Party → Step C E RealSpec (Keys C)),
    (fun r => ((r.1.1, r.2), r.1.2)) <$>
        executeRounds worldRoles D (logAdversary A) noFunctionality fuel ((st, log) : (logAdversary A).State) steps =
      (executeRounds (seedGenMapRoles countedLog worldRoles) D A noFunctionality fuel st steps).run log
  | 0, st, log, steps => rfl
  | fuel + 1, st, log, steps => by
    simp only [executeRounds]
    split_ifs
    · rfl
    · rw [StateT.run_bind, ← stepRound_log]
      refine (map_bind _ _ _).trans (Eq.symm ((bind_map_left _ _ _).trans (bind_congr fun r => ?_)))
      exact (executeRounds_log fuel r.1.1 r.1.2 r.2.1).symm

/-- The first steps of the honest programs under `countedLog` keep the log. -/
theorem startSteps_log (program : C.Party → PartyM C E RealSpec (Keys C)) (log : List HashOutput) :
    (startSteps (seedGenMapRoles countedLog worldRoles) D program).run log =
      (fun a => (a, log)) <$> startSteps worldRoles D program := by
  unfold startSteps
  refine sequenceFin_run_keep log _ _ fun i => ?_
  split_ifs <;> simp only [StateT.run_pure, map_pure, seedGenMapRoles, worldRoles, countedLog_free]

end Setup

/-- The setup run with `logAdversary A` is the setup run with `A` under `countedLog`, with the log
moved from the state of the adversary to the state of the handler. -/
theorem setupLog {E : Type} : ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux), (fun r => ((r.1.1, r.2), r.1.2)) <$> setupRun D (logAdversary A) x z =
      (simulateQ countedLog (setupRun D A x z)).run [] := by
  intro D A x z
  simp only [setupRun, realExecution, executePhase, simulateQ_bind, StateT.run_bind, simulateQ_startSteps_real,
    simulateQ_executeRounds_real]
  rw [← adversaryLog]
  refine (map_bind _ _ _).trans (bind_congr fun p => ?_)
  rw [startSteps_log, bind_map_left, map_bind]
  exact bind_congr fun steps => executeRounds_log D A setupRounds p.1 p.2 steps

/-- The log does not change the run. The setup run with `logAdversary A`, without the log, is the
setup run with `A`. -/
theorem logAdversaryErase {E : Type} : ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux), (fun r => (r.1.1, r.2)) <$> setupRun D (logAdversary A) x z = setupRun D A x z := by
  intro D A x z
  have h := congrArg (Functor.map Prod.fst) (setupLog D A x z)
  rw [Functor.map_map] at h
  exact h.trans (countedLogErase _ (setupRun D A x z) [])

section Provenance

variable (prims : Primitives) (D : C.Coalition)

/-- One call with no free call at a stream-key cell keeps the private answers. -/
theorem jointKeyWorld_keys_of_not (t : (WorldSpec C).Domain) (ht : ¬ FreeStreamKey t) (s : KeyJointState C) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), r.2.keys = s.keys := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  change p.2.keys = s.keys
  have hloc : ∀ (u : (LocalSpec C).Domain) (p : (LocalSpec C).Range u × KeyJointState C),
      p ∈ support ((jointLocal prims false u).run s) → p.2.keys = s.keys := by
    intro u p hp
    rw [jointLocal_false] at hp
    obtain ⟨z, -, rfl⟩ := onJointHash_support _ s p hp
    rfl
  rcases t with (q | x) | (u | q | x)
  · exact hloc q p hp
  · have hp' : p ∈ support ((onJointHash (programAnswer x)).run s) := by
      rw [← jointProgram_false]; exact hp
    obtain ⟨z, -, rfl⟩ := onJointHash_support _ s p hp'
    rfl
  · exact hloc (.inl u) p hp
  · exact hloc (.inr (.inl q)) p hp
  · exact (ht trivial).elim

/-- A stream-key cell of a call with no free call at a stream-key cell is the counted key of the
call. -/
theorem countedKey_of_mem_worldCells (t : (WorldSpec C).Domain) (ht : ¬ FreeStreamKey t) (k : HashOutput)
    (hk : Query.streamKey k ∈ worldCells D t) : countedKey t = some k := by
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · simp [worldCells, prssCountedHashInputs] at hk
  · obtain ⟨-, rfl⟩ : Counted (Sum.inr (Sum.inl q) : (LocalSpec C).Domain) ∧ Query.streamKey k = q := by
      simpa [worldCells, prssCountedHashInputs] using hk
    rfl
  · obtain rfl : k = x.2.1 := by simpa [worldCells, prssCountedHashInputs] using hk
    rfl
  · obtain rfl : Query.streamKey k = q := by simpa [worldCells] using hk
    rfl
  · simp [worldCells, prssCountedHashInputs] at hk
  · obtain ⟨-, rfl⟩ : Counted (Sum.inr (Sum.inl q) : (LocalSpec C).Domain) ∧ Query.streamKey k = q := by
      simpa [worldCells, prssCountedHashInputs] using hk
    exact (ht trivial).elim
  · exact (ht trivial).elim

end Provenance

/-- The provenance of the stream-key cells under `countedLog`, in the ideal joint world. A computation
with no free call at a stream-key cell keeps the private answers and the log, and each new stream-key
cell of the cache is in the log. -/
theorem countedLogProvenance (prims : Primitives) : ∀ (D : C.Coalition) (α : Type) (oa : OracleComp (WorldSpec C) α),
    IsQueryBoundP oa (FreeStreamKey (C := C)) 0 → ∀ (log : List HashOutput) (s : KeyJointState C),
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) ((simulateQ countedLog oa).run log)).run s),
      (∀ y, r.2.keys y = s.keys y) ∧ (∀ k ∈ log, k ∈ r.1.2) ∧
        ∀ k, r.2.hash (.streamKey k) ≠ none → s.hash (.streamKey k) ≠ none ∨ k ∈ r.1.2 := by
  intro D α oa hoa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log s r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨fun _ => rfl, fun _ hk => hk, fun _ hk => Or.inl hk⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeStreamKey t := hoa.1.resolve_right (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (FreeStreamKey (C := C)) 0 := fun u => by
      simpa only [ht, ↓reduceIte] using hoa.2 u
    intro log s r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, countedLog, StateT.run_lift, StateT.run_modify, bind_assoc, pure_bind,
      HasQuery.instOfMonadLift_query] at hr
    obtain ⟨p, hp, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
    obtain ⟨hkeys, hlog, hcells⟩ := ih p.1 (hk p.1) _ p.2 r hr
    have hpk := jointKeyWorld_keys_of_not prims D t ht s p hp
    refine ⟨fun y => by rw [hkeys, hpk], fun k' hk' => hlog k' (List.mem_append_right _ hk'), fun k' hk' => ?_⟩
    rcases hcells k' hk' with h | h
    · by_cases hc : Query.streamKey k' ∈ worldCells D t
      · refine Or.inr (hlog k' (List.mem_append_left _ ?_))
        rw [countedKey_of_mem_worldCells D t ht k' hc]
        exact List.mem_singleton_self k'
      · left
        rwa [← jointKeyWorld_query_other prims D t s p hp _ hc]
    · exact Or.inr h

variable (prims : Primitives)

/-- The provenance for a logged step of the adversary or of `Z`. In the ideal joint world from each
state, a logged computation on the counted copy keeps the private answers, and each new stream-key cell
of the cache is in its log. -/
theorem loggedProvenance : ∀ (D : C.Coalition) (α : Type) (oa : OracleComp (LocalSpec C) α)
    (log : List HashOutput) (s : KeyJointState C),
    ∀ c ∈ support ((simulateQ (jointKeyWorld prims D false)
        (worldRoles.adversary ((simulateQ logImpl oa).run log))).run s),
      (∀ y, c.2.keys y = s.keys y) ∧
        ∀ k, c.2.hash (.streamKey k) ≠ none → s.hash (.streamKey k) ≠ none ∨ k ∈ c.1.2 := by
  intro D α oa log s c hc
  rw [adversaryLog α oa log] at hc
  obtain ⟨hk, -, hcell⟩ := countedLogProvenance prims D _ (worldRoles.adversary oa)
    (isQueryBoundP_adversary_noStreamKey oa 0) log s c hc
  exact ⟨hk, hcell⟩

/-- The provenance for the setup. In the ideal joint world from the initial state, the setup run gives
no private answer, and each stream-key cell of the cache is in the log of the adversary. -/
theorem setupProvenance {E : Type} : ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux),
    ∀ a ∈ support ((simulateQ (jointKeyWorld prims D false) (setupRun D (logAdversary A) x z)).run
        keyJointInitial),
      (∀ y, a.2.keys y = none) ∧ ∀ k, a.2.hash (.streamKey k) ≠ none → k ∈ a.1.1.2 := by
  intro D A x z a ha
  have hmem : (((a.1.1.1, a.1.2), a.1.1.2), a.2) ∈ support ((simulateQ (jointKeyWorld prims D false)
      ((simulateQ countedLog (setupRun D A x z)).run [])).run keyJointInitial) := by
    rw [← setupLog D A x z, simulateQ_map, StateT.run_map, support_map]
    exact ⟨a, ha, rfl⟩
  obtain ⟨hk, -, hcell⟩ := countedLogProvenance prims D _ (setupRun D A x z)
    (realExecution_setup_noStreamKey D A x z) [] keyJointInitial _ hmem
  exact ⟨fun y => hk y, fun k hk' => (hcell k hk').resolve_left fun h => h rfl⟩

end Logs

section Draws

variable {C : Committee}

/-- A live honest operator holds `key` for the name `n`. `HiddenKey` is this relation at a hidden
name. -/
def HeldBy (D : C.Coalition) (out : C.Party → Option (Keys C)) (n : KeyName C) (key : HashOutput) : Prop :=
  ∃ i k, i ∉ D.1 ∧ out i = some k ∧ heldKey i k n = some key

/-- Operator `j` holds the key `K_{jj'}` of its pair with `j'`. -/
theorem heldKey_pairOf (j j' : C.Party) (h : j ≠ j') (k : Keys C) :
    heldKey j k (.pair (C.pairOf j j' h)) = some (k.pairKey j') := by
  unfold Committee.pairOf
  split_ifs with hjj
  · simp [heldKey]
  · simp [heldKey, h]

/-- A key that a live honest operator holds for a name that is not hidden is a known key of the
view. -/
theorem mem_liveKnownKeys_of_heldKey (D : C.Coalition) (out : C.Party → Option (Keys C)) (i : C.Party)
    (hi : i ∉ D.1) (ki : Keys C) (hki : out i = some ki) (n : KeyName C) (hn : ¬ Hidden D n)
    (key : HashOutput) (hkey : heldKey i ki n = some key) : key ∈ liveKnownKeys D out := by
  have hparty : ∀ j : C.Party, j ∈ C.parties := fun j => by simp only [Committee.parties, List.mem_finRange]
  refine List.mem_flatMap.2 ⟨i, hparty i, ?_⟩
  simp only [hi, ↓reduceIte, hki, partyKnownKeys, List.mem_append, List.mem_filterMap]
  cases n with
  | parameter => simp only [heldKey, reduceCtorEq] at hkey
  | term T =>
    simp only [heldKey] at hkey
    split_ifs at hkey with hT
    exact Or.inl ⟨T, mem_terms T, by rw [ite_eq_left ⟨not_not.1 hn, hT⟩]; exact hkey⟩
  | pair p =>
    simp only [heldKey] at hkey
    have hn' : p.1.1 ∈ D.1 ∨ p.1.2 ∈ D.1 := by
      by_contra hc
      exact hn ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
    split_ifs at hkey with h1 h2
    · have h2' : p.1.2 ∈ D.1 := hn'.resolve_left (h1 ▸ hi)
      exact Or.inr ⟨p.1.2, hparty _, by rw [ite_eq_left ⟨h2', fun h => hi (h ▸ h2')⟩]; exact hkey⟩
    · have h1' : p.1.1 ∈ D.1 := hn'.resolve_right (h2 ▸ hi)
      exact Or.inr ⟨p.1.1, hparty _, by rw [ite_eq_left ⟨h1', fun h => hi (h ▸ h1')⟩]; exact hkey⟩

section Free

variable (prims : Primitives)

/-- The provenance of a free computation from the state `s` to the state `s'`. -/
def FreeProvenance (D : C.Coalition) (key : KeyName C → HashOutput → Prop) (s s' : KeyJointState C) : Prop :=
  (∀ n k, s'.keys (n, k) ≠ none → s.keys (n, k) ≠ none ∨ (Hidden D n ∧ key n k)) ∧
    ∀ k, s'.hash (.streamKey k) ≠ none → s.hash (.streamKey k) ≠ none ∨ ∃ n, ¬ Hidden D n ∧ key n k

theorem FreeProvenance.refl (D : C.Coalition) (key : KeyName C → HashOutput → Prop) (s : KeyJointState C) :
    FreeProvenance D key s s :=
  ⟨fun _ _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem FreeProvenance.trans {D : C.Coalition} {key : KeyName C → HashOutput → Prop}
    {s s' s'' : KeyJointState C} (h₁ : FreeProvenance D key s s') (h₂ : FreeProvenance D key s' s'') :
    FreeProvenance D key s s'' := by
  refine ⟨fun n k h => ?_, fun k h => ?_⟩
  · rcases h₂.1 n k h with h | h
    · exact h₁.1 n k h
    · exact Or.inr h
  · rcases h₂.2 k h with h | h
    · exact h₁.2 k h
    · exact Or.inr h

/-- A query of `H` changes no cell of the cache other than its own. -/
theorem hashAnswer_other (q : Query C) (h : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run h), ∀ q', q' ≠ q → z.2 q' = h q' := by
  intro z hz q' hq'
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · rw [hashAnswer_of_not_isFixed prims hq] at hz
    exact (randomOracle_support q h z hz).2.2 q' hq'

/-- One free call that the relation allows, in the ideal joint world. -/
theorem jointKeyWorld_free_step (D : C.Coalition) (key : KeyName C → HashOutput → Prop)
    (t : (LocalSpec C).Domain) (ht : ¬ Unallowed key (.inr t)) (s : KeyJointState C) :
    ∀ r ∈ support ((jointKeyWorld prims D false (.inr t)).run s), FreeProvenance D key s r.2 := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  change FreeProvenance D key s p.2
  rcases t with u | q | x
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inl u))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    have he : z.2 = s.hash := by
      simp [localAnswer, unifFwdImpl] at hz
      obtain ⟨_, rfl⟩ := hz
      rfl
    refine ⟨fun n k h => Or.inl h, fun k h => Or.inl ?_⟩
    simpa [he] using h
  · simp only [Unallowed, KeyAllowed, not_not] at ht
    have hp' : p ∈ support ((onJointHash (hashAnswer prims q)).run s) := by
      rw [← jointHash_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine ⟨fun n k h => Or.inl h, fun k h => Or.inl ?_⟩
    have := hashAnswer_other prims q s.hash z hz (.streamKey k) (fun e => ht k e.symm)
    simpa [this] using h
  · simp only [Unallowed, KeyAllowed, not_not] at ht
    by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      simp only [StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      rcases hk : s.keys (x.1, x.2.1) with _ | v
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = (do
            let v ← $ᵗ HashOutput
            pure (v, (⟨s.hash, s.keys.cacheQuery (x.1, x.2.1) v,
              (if (s.used x.2.1).isSome then s.used else Function.update s.used x.2.1 (some x.1)),
              s.bad⟩ : KeyJointState C))) := by
          simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk]
        rw [hrun] at hw
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
        obtain ⟨v, -, rfl⟩ := hw
        refine ⟨fun n k h => ?_, fun k h => Or.inl h⟩
        by_cases e : (n, k) = (x.1, x.2.1)
        · simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact Or.inr ⟨hh, ht⟩
        · left
          simpa [QueryCache.cacheQuery_of_ne _ _ e] using h
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = pure (v, s) := by
          simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk]
        rw [hrun, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact FreeProvenance.refl D key s
    · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inr (.inr x)))).run s) := by
        have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) =
            jointLocal prims false (.inr (.inr x)) := by
          simp only [jointKeyWorldCore, hh, ↓reduceIte]
        rw [hc] at hp
        rw [← jointLocal_false]
        exact hp
      obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
      obtain ⟨w, hw, he⟩ := prgAnswer_support prims x s.hash z hz
      refine ⟨fun n k h => Or.inl h, fun k h => ?_⟩
      change z.2 (.streamKey k) ≠ none at h
      rw [he] at h
      by_cases e : k = x.2.1
      · subst e
        exact Or.inr ⟨x.1, hh, ht⟩
      · left
        rwa [hashAnswer_other prims _ s.hash w hw (.streamKey k) (fun e' => e (Query.streamKey.inj e'))] at h

/-- The provenance of a free computation in the ideal joint world. Each stream call of the computation
is under a key of its name in `key`, and the computation hashes no stream key. Then a new private
answer is for a key of a hidden name, and a new stream-key cell is for a key of a name that is not
hidden. -/
theorem freeAllowedProvenance : ∀ (D : C.Coalition) (key : KeyName C → HashOutput → Prop) (β : Type)
    (ob : OracleComp (LocalSpec C) β), IsQueryBoundP ob (fun t => Unallowed key (.inr t)) 0 →
    ∀ s : KeyJointState C, ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) (free ob)).run s),
      (∀ n k, r.2.keys (n, k) ≠ none → s.keys (n, k) ≠ none ∨ (Hidden D n ∧ key n k)) ∧
        ∀ k, r.2.hash (.streamKey k) ≠ none → s.hash (.streamKey k) ≠ none ∨ ∃ n, ¬ Hidden D n ∧ key n k := by
  intro D key β ob hob
  induction ob using OracleComp.inductionOn with
  | pure b =>
    intro s r hr
    simp only [free_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact FreeProvenance.refl D key s
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hob
    have ht : ¬ Unallowed key (.inr t) := by
      rcases hob.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    intro s r hr
    rw [e] at hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    have hk : IsQueryBoundP (k p.1) (fun t => Unallowed key (.inr t)) 0 := by
      simpa only [ht, ↓reduceIte] using hob.2 p.1
    exact (jointKeyWorld_free_step prims D key t ht s p hp).trans (ih p.1 hk p.2 r hr)

end Free

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The draws of a live honest operator make only stream calls, each one under a key that a live
honest operator holds for the name of the call. -/
theorem randStreamsAllowed (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (out : C.Party → Option (Keys C)) (j : C.Party) (k : Keys C) (hj : j ∉ D.1) (hout : out j = some k) :
    IsQueryBoundP (randStreams K prgBits (carrierPrssKeys k) j label calls)
      (fun t => Unallowed (HeldBy D out) (.inr (.inr t))) 0 :=
  isQueryBoundP_randStreams_zero K _ (carrierPrssKeys k) j
    (fun T hT _ _ _ h => h ⟨j, k, hj, hout, by simp [heldKey, carrierPrssKeys, hT]⟩)
    (fun j' hj' _ _ _ h => h ⟨j, k, hj, hout, heldKey_pairOf j j' (Ne.symm hj') k⟩) label calls

variable (prims : Primitives)

/-- The provenance for the draws. In the ideal joint world from each state, the draws of the live
honest operators give a new private answer only for a key that a live honest operator holds for a
hidden name, and a new stream-key cell only for a known key of a live honest operator. -/
theorem liveStreamsProvenance : ∀ (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (out : C.Party → Option (Keys C)) (s : KeyJointState C),
    ∀ b ∈ support ((simulateQ (jointKeyWorld prims D false)
        (free (liveStreams K prgBits D out label calls))).run s),
      (∀ n k, b.2.keys (n, k) ≠ none → s.keys (n, k) ≠ none ∨ HiddenKey D out n k) ∧
        ∀ k, b.2.hash (.streamKey k) ≠ none → s.hash (.streamKey k) ≠ none ∨ k ∈ liveKnownKeys D out := by
  intro label calls D out s b hb
  have hbound : IsQueryBoundP (liveStreams K prgBits D out label calls)
      (fun t => Unallowed (HeldBy D out) (.inr t)) 0 := by
    unfold liveStreams
    refine isQueryBoundP_sequenceFin _ fun j => ?_
    by_cases hj : j ∈ D.1
    · simp only [hj, ↓reduceIte]
      exact isQueryBoundP_pure _ _ 0
    · simp only [hj, ↓reduceIte]
      cases ho : out j with
      | none => exact isQueryBoundP_pure _ _ 0
      | some k =>
        exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_liftComp_ro _ _
          (randStreamsAllowed K label calls D out j k hj ho))
  obtain ⟨hk, hcell⟩ := freeAllowedProvenance prims D (HeldBy D out) _ _ hbound s b hb
  refine ⟨fun n k h => (hk n k h).imp_right ?_, fun k h => (hcell k h).imp_right ?_⟩
  · rintro ⟨hn, i, ki, hi, hout, hheld⟩
    exact ⟨i, ki, hi, hout, hn, hheld⟩
  · rintro ⟨n, hn, i, ki, hi, hout, hheld⟩
    exact mem_liveKnownKeys_of_heldKey D out i hi ki hout n hn k hheld

end Draws

end ThresholdLeanXmssSecurity
