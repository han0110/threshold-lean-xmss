import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Search
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Move

/-!
# The emulated seed of a hidden term is a cell of the cache

`hiddenInput parts T` is the derive input of each honest holder of the hidden term `T` on the parts
`parts`. `termCached` states that an honest holder of a hidden term with keys at the end of the seed
generation holds the value of the cache at `hiddenInput parts T`. An honest holder that aborts sends an
abort frame, so a holder with keys read the reveal of each other holder.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The holders of `T` in operator order. -/
def holdersList (T : C.Term) : List C.Party := C.parties.filter (· ∈ C.holders T)

/-- The derive input of the term `T` on the parts `parts`. -/
def hiddenInput (parts : C.Party → Parts C) (T : C.Term) : Query C :=
  .derive .seedGen .term ((holdersList T).map fun k => (parts k).term T)

section Rest

variable [Field E] [Algebra Bit E]

/-- `seedGenTail` after the draw of the parts. -/
def seedGenRest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) := do
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D net noFunctionality state steps).run
  let log := early ++ calls
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
  let high ← free (liftComp ($ᵗ HashOutput) _)
  let _ ← program (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view (firstHonest (C.holders T)) k).term T)) ((dealt j).seed T)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]) ((dealt j).pairKey i)
    else pure true
  let ((state, keys), _) ← (executeRounds observedRoles D net noFunctionality (setupRounds - 1) state steps).run
  pure (state, keys)

theorem seedGenTail_eq_rest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) :
    seedGenTail D net state early parameter dealt = (do
      let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
      seedGenRest D net state early parameter dealt parts) := rfl

end Rest

section Cached

variable [Field E] [Algebra Bit E]

/-- An honest holder of a hidden term with keys holds the end value of the cache at the derive input
of the term. -/
def TermCached (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : Prop :=
  ∀ (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) (w : LogState C),
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) (seedGenRest D net state early parameter dealt parts)).run w),
      ∀ (i : C.Party) (keys : Keys C) (T : C.Term), i ∉ D.1 → z.1.2 i = some keys → i ∈ C.holders T →
        ¬ KnownTo D.1 T → z.2.1.1 (hiddenInput parts T) = some (keys.seed T)

end Cached

/-! ## The steps of one seed generation with the answers of a cache -/

section Trace

attribute [local instance] Set.monad

open SetupAgree (cacheAnswer StepNext mem_setBind mapM_getD mem_hashQuery stepRound_cache)
open SetupParameter (commitStep revealStep echoStep anyAnswer)

variable [Field E] [Algebra Bit E]

omit [Field E] [Algebra Bit E] in
theorem advance_seedGenWith (i : C.Party) (own : Parts C) :
    advance (seedGenWith i own : PartyM C E RealSpec (Keys C)).run =
      liftComp (commitQueries .seedGen i own) (LocalSpec C) >>= fun commitments =>
        pure (commitStep i own commitments) := by
  have h : (seedGenWith i own : PartyM C E RealSpec (Keys C)) =
      commitRevealEcho .seedGen i own >>= fun keys => pure (SetupParameter.keysOf keys) := rfl
  rw [h, advance_setup_start]
  rfl

omit [Field E] [Algebra Bit E] in
theorem start_any_with (i : C.Party) (own : Parts C) (step : Step C E RealSpec (Keys C))
    (h : step ∈ simulateQ (anyAnswer (C := C)) (advance (seedGenWith i own : PartyM C E RealSpec (Keys C)).run)) :
    ∃ commitments, step = commitStep i own commitments := by
  rw [advance_seedGenWith] at h
  simp only [simulateQ_bind, simulateQ_pure] at h
  obtain ⟨commitments, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  exact ⟨commitments, h⟩

omit [Field E] [Algebra Bit E] in
theorem commit_next_seedGen (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (commitments : List HashOutput) (next : Step C E RealSpec (Keys C))
    (h : StepNext s inbox (commitStep i own commitments) next) :
    next = .done none ∨ next = revealStep i own inbox := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · right
    rw [advance_exchange_bind, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    exact h

omit [Field E] [Algebra Bit E] in
theorem reveal_next_seedGen (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (committed : Mail C E) (next : Step C E RealSpec (Keys C))
    (h : StepNext s inbox (revealStep i own committed) next) :
    next = .done none ∨ (C.parties.any fun j => Msg.isAbort (inbox j)) = false ∧ ∃ keys shared,
      keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .seedGen i (setupView .seedGen i own inbox)) (LocalSpec C)) ∧
      next = echoStep i keys shared := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with habort
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · rw [advance_setupRest] at h
    simp only [simulateQ_bind] at h
    obtain ⟨opens, -, h⟩ := mem_setBind.1 h
    split_ifs at h
    · right
      refine ⟨by simpa using habort, ?_⟩
      simp only [simulateQ_bind, simulateQ_pure] at h
      obtain ⟨keys, hkeys, h⟩ := mem_setBind.1 h
      obtain ⟨shared, -, h⟩ := mem_setBind.1 h
      rw [Set.pure_def, Set.mem_singleton_iff] at h
      exact ⟨keys, shared, hkeys, h⟩
    · left
      simpa [Set.pure_def] using h

omit [Field E] [Algebra Bit E] in
theorem echo_next_seedGen (s : HashCache C) (inbox : Mail C E) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (next : Step C E RealSpec (Keys C)) (h : StepNext s inbox (echoStep i keys shared) next)
    (K : Keys C) (hout : next.output = some K) : K = SetupParameter.keysOf keys := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with ha
  · simp only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    subst h
    cases hout
  · rw [advance_require_bind] at h
    split_ifs at h with hc
    · simp only [advance_run_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      simp only [Step.output, Option.some.injEq] at hout
      exact hout.symm
    · simp only [simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      cases hout

omit [Field E] [Algebra Bit E] in
/-- The key of a held term is the cached derived key of the parts of the term in the view. -/
theorem term_cached_seedGen {s : HashCache C} (i : C.Party) (view : C.Party → Parts C)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (h : keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .seedGen i view) (LocalSpec C))) (T : C.Term)
    (hT : i ∈ C.holders T) :
    s (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)) =
      some (keys.2.1 T) := by
  unfold deriveKeys at h
  simp only [↓reduceIte, liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure] at h
  obtain ⟨parameter, -, h⟩ := mem_setBind.1 h
  obtain ⟨term, hterm, h⟩ := mem_setBind.1 h
  obtain ⟨pair, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  subst h
  have hmem : T ∈ C.terms := by simp [Committee.terms]
  have hj := mapM_getD _ C.terms term hterm (C.terms.idxOf T) (List.idxOf_lt_length_of_mem hmem) 0
  rw [List.getElem_idxOf] at hj
  simp only [hT, ↓reduceIte] at hj
  exact (mem_hashQuery hj).resolve_left fun ⟨_, hq, _⟩ => by cases hq

omit [Field E] [Algebra Bit E] in
/-- The view of `i` of a term part of `h` is the part of `h` that `h` revealed to `i`. -/
theorem setupView_term_seedGen (i h : C.Party) (hhi : h ≠ i) (own own' : Parts C) (inbox : Mail C E)
    (hrev : inbox h = revealOutbox .seedGen h own' i) (T : C.Term) (hi : i ∈ C.holders T)
    (hh : h ∈ C.holders T) : (setupView .seedGen i own inbox h).term T = own'.term T := by
  have hmem : T ∈ sharedTerms h i := by simp [sharedTerms, Committee.terms, hi, hh]
  simp only [setupView, hhi, ↓reduceIte, hrev, revealOutbox, Ne.symm hhi, Msg.hashesOf, readReveal, revealTo]
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_append_right (by simp)]
  simp

theorem mem_eraseLog {α : Type} (D : C.Coalition) (X : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (w : StreamState C) (r : (α × CallLog C) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) X.run).run w)) :
    (r.1.1, r.2) ∈ support ((simulateQ (streamWorld prims D) (seedGenEraseLog X)).run w) := by
  unfold seedGenEraseLog
  rw [simulateQ_map, StateT.run_map, support_map]
  exact ⟨r, hr, rfl⟩

omit [Field E] [Algebra Bit E] in
theorem termCached_stream (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (w : StreamState C)
    (y : (net.State × (C.Party → Option (Keys C))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (seedGenRest D net state early parameter dealt parts)).run w))
    (i : C.Party) (keys : Keys C) (T : C.Term) (hi : i ∉ D.1) (hk : y.1.2 i = some keys) (hiT : i ∈ C.holders T)
    (hT : ¬ KnownTo D.1 T) : y.2.1 (hiddenInput parts T) = some (keys.seed T) := by
  unfold seedGenRest at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hy
  obtain ⟨a0, ha0, r1, hr1, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := hy
  have h0 : ∀ k, k ∉ D.1 → ∃ commitments, a0.1 k = commitStep k (parts k) commitments := by
    unfold startSteps at ha0
    refine SetupParameter.sequenceFin_any (streamWorld prims D)
      (fun k v => k ∉ D.1 → ∃ commitments, v = commitStep k (parts k) commitments) _ (fun k w' u hu hk => ?_) w a0 ha0
    simp only [hk, ↓reduceIte, worldRoles] at hu
    exact start_any_with k (parts k) u.1 (SetupParameter.free_any (streamWorld prims D) _ w' u hu)
  have hq1 := mem_eraseLog prims D _ _ _ hr1
  rw [seedGenEraseLog_stepRound] at hq1
  obtain ⟨hle1, hn1⟩ := stepRound_cache prims D net state a0.1 a0.2 _ hq1
  simp only at hle1 hn1
  have hlb := streamWorld_run_mono prims D _ _ _ hb
  have hlc := streamWorld_run_mono prims D _ _ _ hc
  have hld := streamWorld_run_mono prims D _ _ _ hd
  have hle := streamWorld_run_mono prims D _ _ _ he
  have hqE := mem_eraseLog prims D _ _ _ hf
  rw [seedGenEraseLog_executeRounds] at hqE
  have hlf := streamWorld_run_mono prims D _ _ _ hqE
  simp only at hk ⊢
  rcases SetupParameter.executeRounds_succ_any (streamWorld prims D) D net 1 r1.1.1.1 r1.1.1.2.1 e.2 (f.1.1, f.2)
    hqE with hout | ⟨q2, hq2, hy⟩
  · exfalso
    obtain ⟨cm, hc0⟩ := h0 i hi
    have hs := hn1 i hi f.2.1 (hlb.trans (hlc.trans (hld.trans (hle.trans hlf))))
    rw [hc0] at hs
    have ho := congrFun hout i
    simp only [hk] at ho
    rcases commit_next_seedGen _ _ i (parts i) cm _ hs with h | h <;>
      simp [h, Step.output, revealStep] at ho
  obtain ⟨hle2, hn2⟩ := stepRound_cache prims D net _ _ _ q2 hq2
  have hm2 := streamWorld_run_mono prims D _ _ _ hy
  simp only at hle2 hn2 hm2
  have hs1 : r1.2.1 ≤ f.2.1 := hlb.trans (hlc.trans (hld.trans (hle.trans (hle2.trans hm2))))
  have hstep1 : ∀ k, k ∉ D.1 → r1.1.1.2.1 k = .done none ∨
      r1.1.1.2.1 k = revealStep k (parts k) (roundInbox D r1.1.1.2.2 a0.1 k) := fun k hk' => by
    obtain ⟨cm, hc0⟩ := h0 k hk'
    have hs := hn1 k hk' f.2.1 hs1
    rw [hc0] at hs
    exact commit_next_seedGen _ _ k (parts k) cm _ hs
  have hi2 : q2.1.2.1 i = .done none ∨ (C.parties.any fun j => Msg.isAbort (roundInbox D q2.1.2.2 r1.1.1.2.1 i j)) =
      false ∧ ∃ keys' shared, keys' ∈ simulateQ (cacheAnswer f.2.1) (liftComp (deriveKeys .seedGen i
        (setupView .seedGen i (parts i) (roundInbox D q2.1.2.2 r1.1.1.2.1 i))) (LocalSpec C)) ∧
        q2.1.2.1 i = echoStep i keys' shared := by
    have hs := hn2 i hi f.2.1 hm2
    rcases hstep1 i hi with h | h
    · rw [h] at hs
      exact Or.inl hs
    · rw [h] at hs
      exact reveal_next_seedGen _ _ i (parts i) _ _ hs
  rcases SetupParameter.executeRounds_succ_any (streamWorld prims D) D net 0 q2.1.1 q2.1.2.1 q2.2 (f.1.1, f.2)
    hy with hout | ⟨q3, hq3, hy⟩
  · exfalso
    have ho := congrFun hout i
    simp only [hk] at ho
    rcases hi2 with h | ⟨-, keys', shared, -, h⟩ <;> simp [h, Step.output, echoStep] at ho
  obtain ⟨hle3, hn3⟩ := stepRound_cache prims D net _ _ _ q3 hq3
  have hout := SetupParameter.executeRounds_zero_any (streamWorld prims D) D net q3.1.1 q3.1.2.1 q3.2 (f.1.1, f.2) hy
  have hlf3 := streamWorld_run_mono prims D _ _ _ hy
  simp only at hout hlf3 hle3 hn3
  have ho := congrFun hout i
  simp only [hk] at ho
  have hs3 := hn3 i hi f.2.1 hlf3
  rcases hi2 with h | ⟨habort, keys', shared, hkeys', h⟩
  · exfalso
    rw [h] at hs3
    change q3.1.2.1 i = .done none at hs3
    simp [hs3, Step.output] at ho
  rw [h] at hs3
  have hK := echo_next_seedGen _ _ i keys' shared _ hs3 keys ho.symm
  subst hK
  have hc := term_cached_seedGen i _ keys' hkeys' T hiT
  have hview : ((C.parties.filter (· ∈ C.holders T)).map fun j =>
      (setupView .seedGen i (parts i) (roundInbox D q2.1.2.2 r1.1.1.2.1 i) j).term T) =
      (holdersList T).map fun j => (parts j).term T := by
    refine List.map_congr_left fun j hj => ?_
    have hjT : j ∈ C.holders T := by simpa using (List.mem_filter.1 hj).2
    have hjD : j ∉ D.1 := fun h => hT ⟨j, h, hjT⟩
    by_cases hji : j = i
    · subst hji
      simp [setupView]
    · have hrev : roundInbox D q2.1.2.2 r1.1.1.2.1 i j = revealOutbox .seedGen j (parts j) i := by
        rcases hstep1 j hjD with h1 | h1
        · exfalso
          have ha : Msg.isAbort (roundInbox D q2.1.2.2 r1.1.1.2.1 i j) = true := by
            simp [roundInbox, hjD, h1, Step.delivered, Msg.isAbort]
          have hany := List.any_eq_false.1 habort j (by simp [Committee.parties])
          exact hany ha
        · simp [roundInbox, hjD, h1, Step.delivered, revealStep]
      exact setupView_term_seedGen i j hji (parts i) (parts j) _ hrev T hiT hjT
  rw [hview] at hc
  exact hc

omit [Field E] [Algebra Bit E] in
/-- `TermCached` holds for each coalition and each adversary. -/
theorem termCached (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : TermCached prims D net := by
  intro state early parameter dealt parts w z hz i keys T hi hk hiT hT
  have h := withLog_run (streamWorld prims D) countedCells (seedGenRest D net state early parameter dealt parts) w.1 w.2
  rw [← loggedWorld_eq] at h
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D)
      (seedGenRest D net state early parameter dealt parts)).run w.1) := by
    rw [← h, support_map]
    exact ⟨z, hz, rfl⟩
  exact termCached_stream prims D net state early parameter dealt parts w.1 _ hz' i keys T hi hk hiT hT

end Trace

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.termCached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare.termCached
