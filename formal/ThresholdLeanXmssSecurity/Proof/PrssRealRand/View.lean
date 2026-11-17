import ThresholdLeanXmssSecurity.Proof.PrssRealRand.KeyBound

/-!
# The law of the view in the stream-key bound

The fresh hidden keys of `seedGenHiddenZ` can be sampled after a list that holds the log of the
adversary, the known keys and the log of the distinguisher.

* `flagExperiment` is the `flagZ` experiment with the fresh hidden keys. It holds the fresh keys, the
  logged setup run, the hashes of the known keys and the log of the distinguisher.
* `accepts_eq_flagExperiment` states that `flagExperiment` is the game with `seedGenHiddenZ`.
* `flagExperiment_view_independent` states that the view is independent of the fresh hidden keys,
  and that its law is `flagView`.
* `flagView_length_le` bounds the length of the view.
* `prssRealRand_view` is the second premise of `prssRealRand_key`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Log

variable {C : Committee} {E : Type}

theorem streamKeyOf_length_le (t : (LocalSpec C).Domain) :
    (streamKeyOf t).toList.length ≤ if Counted t then 1 else 0 := by
  rcases t with u | q | x
  · simp only [streamKeyOf, Option.toList_none, List.length_nil, Nat.zero_le]
  · cases q <;> simp only [streamKeyOf, Option.toList_none, List.length_nil, Nat.zero_le]
    simp only [Option.toList_some, List.length_singleton, Counted]
    exact (ite_eq_left trivial).ge
  · simp only [streamKeyOf, Option.toList_some, List.length_singleton, Counted]
    exact (ite_eq_left trivial).ge

/-- A computation with at most `n` counted calls adds at most `n` keys to the log. -/
theorem logImpl_length_le {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa Counted n)
    (log : List HashOutput) : ∀ r ∈ support ((simulateQ logImpl oa).run log), r.2.length ≤ log.length + n := by
  induction oa using OracleComp.inductionOn generalizing n log with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    intro r hr
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    simp only [logImpl, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_assoc,
      pure_bind, HasQuery.instOfMonadLift_query, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    have hk := ih u _ (h.2 u) _ r hr
    have hl := streamKeyOf_length_le t
    rw [List.length_append] at hk
    by_cases hc : Counted t
    · simp only [hc, ite_true] at hk hl
      have hn := h.1.resolve_left (not_not.mpr hc)
      omega
    · simp only [hc, ite_false] at hk hl
      omega

end Log

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (prims : Primitives)

section Rename

/-- The fresh keys overlaid on the hidden coordinates of the outputs, as `seedGenHiddenZ` does. -/
def freshOverlay (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput))
    (out : C.Party → Option (Keys C)) : C.Party → Option (Keys C) :=
  fun i => (out i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i)

/-- The fresh key of a hidden name, and `0` for every other name. -/
def freshKeyOf (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput)) (n : KeyName C) :
    HashOutput :=
  if Hidden D n then (dealtKey f.1 f.2 n).getD 0 else 0

/-- At each name, swap the fresh key of the name with `0`. -/
def freshSwap (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput))
    (x : KeyName C × HashOutput) : KeyName C × HashOutput :=
  (x.1, Equiv.swap (freshKeyOf D f x.1) 0 x.2)

theorem freshSwap_involutive (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput)) :
    Function.Involutive (freshSwap D f) := by
  rintro ⟨n, k⟩
  simp only [freshSwap, Equiv.swap_apply_self]

/-- The fresh keys with value `0`. -/
def zeroKeys : (C.Term → HashOutput) × (C.Pair → HashOutput) := (fun _ => 0, fun _ => 0)

theorem liveKnownKeys_freshOverlay (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput))
    (out : C.Party → Option (Keys C)) : liveKnownKeys D (freshOverlay D f out) = liveKnownKeys D out := by
  unfold liveKnownKeys
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [hi, ite_true]
  · simp only [hi, ite_false, freshOverlay]
    cases out i with
    | none => rfl
    | some k =>
      simp only [Option.map_some, partyKnownKeys]
      congr 1
      · congr 1
        funext T
        by_cases h : KnownTo D.1 T ∧ i ∈ C.holders T
        · simp only [h, and_self, ite_true, seedGenHiddenOverlay]
        · simp only [h, ite_false]
      · congr 1
        funext j
        by_cases h : j ∈ D.1 ∧ j ≠ i
        · simp only [h, ite_true, seedGenHiddenOverlay, or_true]
        · simp only [h, ite_false]

/-- The swap maps the fresh key of a held term to the key of the term with zero fresh keys. -/
theorem freshSwap_term (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput)) (i : C.Party)
    (k : Keys C) (T : C.Term) (hT : i ∈ C.holders T) :
    freshSwap D f (.term T, (seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i)).seed T) =
      (.term T, (seedGenHiddenOverlay D i k (dealtKeys 0 zeroKeys.1 zeroKeys.2 i)).seed T) := by
  by_cases hK : KnownTo D.1 T
  · simp only [freshSwap, freshKeyOf, Hidden, hK, not_true_eq_false, ite_false, seedGenHiddenOverlay, ite_true,
      Equiv.swap_self, Equiv.refl_apply]
  · simp only [freshSwap, freshKeyOf, Hidden, hK, not_false_eq_true, ite_true, seedGenHiddenOverlay, ite_false,
      dealtKeys, hT, dealtKey, Option.getD_some, Equiv.swap_apply_left, zeroKeys]

/-- The swap maps the fresh key of a pair of a live honest operator to the key of the pair with zero
fresh keys. -/
theorem freshSwap_pair (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput)) (i : C.Party)
    (hi : i ∉ D.1) (k : Keys C) (j : C.Party) (h : j ≠ i) :
    freshSwap D f (.pair (C.pairOf i j (Ne.symm h)), (seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i)).pairKey j) =
      (.pair (C.pairOf i j (Ne.symm h)),
        (seedGenHiddenOverlay D i k (dealtKeys 0 zeroKeys.1 zeroKeys.2 i)).pairKey j) := by
  by_cases hj : j ∈ D.1
  · have hn : ¬ Hidden D (.pair (C.pairOf i j (Ne.symm h))) :=
      fun hh => ((hidden_pairOf D i j (Ne.symm h)).1 hh).2 hj
    simp only [freshSwap, freshKeyOf, hn, ite_false, seedGenHiddenOverlay, hj,
      or_true, ite_true, Equiv.swap_self, Equiv.refl_apply]
  · simp only [freshSwap, freshKeyOf, (hidden_pairOf D i j (Ne.symm h)).2 ⟨hi, hj⟩, ite_true, seedGenHiddenOverlay, hi, hj,
      or_self, ite_false, dealtKeys, h, dite_false, dealtKey, Option.getD_some, Equiv.swap_apply_left, zeroKeys]

/-- `PRG` with no call reads the renamed table as the rename of the calls reads the table. -/
theorem pureStreams_freshSwap (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput))
    (known hashes : List HashOutput) (aesKeys : KeyName C × HashOutput → Digest) (t : (RoSpec C).Domain) :
    simulateQ (pureStreams prims D known hashes aesKeys) (roRename (freshSwap D f) t) =
      pureStreams prims D known hashes (aesKeys ∘ freshSwap D f) t := by
  rcases t with q | x
  · rfl
  · change pureStreams prims D known hashes aesKeys
      (.inr ((freshSwap D f (x.1, x.2.1)).1, (freshSwap D f (x.1, x.2.1)).2, x.2.2)) = _
    by_cases hx : Hidden D x.1
    · simp only [pureStreams, freshSwap, hx, ite_true, Function.comp_apply]
    · simp only [pureStreams, freshSwap, freshKeyOf, hx, ite_false, Equiv.swap_self, Equiv.refl_apply]

/-- The streams of a live honest operator with the fresh keys and the renamed table are the streams
with zero fresh keys and the table. -/
theorem streams_freshSwap [SampleableType E] (D : C.Coalition) (f : (C.Term → HashOutput) × (C.Pair → HashOutput))
    (known hashes : List HashOutput) (aesKeys : KeyName C × HashOutput → Digest) (i : C.Party) (hi : i ∉ D.1)
    (k : Keys C) (label : ℕ) (calls : List RandCall) :
    simulateQ (pureStreams prims D known hashes (aesKeys ∘ freshSwap D f))
        (randStreams K prgBits (carrierPrssKeys (seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i))) i label calls) =
      simulateQ (pureStreams prims D known hashes aesKeys)
        (randStreams K prgBits (carrierPrssKeys (seedGenHiddenOverlay D i k (dealtKeys 0 zeroKeys.1 zeroKeys.2 i)))
          i label calls) := by
  rw [← QueryImpl.simulateQ_simulateQ_eq_of_apply (pureStreams_freshSwap prims D f known hashes aesKeys),
    roRename_randStreams]
  congr 1
  refine randStreams_congr K _ _ _ _ i (fun T hT => ?_) (fun j h => ?_) label calls
  · simp only [carrierPrssKeys, freshSwap_term D f i k T hT]
  · simp only [carrierPrssKeys, freshSwap_pair D f i hi k j h]

end Rename

section FlagRun

variable (label : ℕ) (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
  (Z : Distinguisher C A.State (List (RandOutput C E)))

/-- The outputs that `flagZ` gives `Z`. -/
def flagOutputs (out : C.Party → Option (Keys C)) (known hashes : List HashOutput)
    (aesKeys : KeyName C × HashOutput → Digest) : C.Party → Option (List (RandOutput C E)) :=
  fun i => if i ∈ D.1 then none else
    (out i).map fun k => simulateQ (pureStreams prims D known hashes aesKeys)
      (randStreams K prgBits (carrierPrssKeys k) i label calls)

/-- The run of `flagZ` before its flag. It gives the hashes of the known keys and the log of `Z`. -/
def flagRun (st : A.State) (out : C.Party → Option (Keys C)) :
    OracleComp (LocalSpec C) (List HashOutput × List HashOutput) := do
  let hashes ← (liveKnownKeys D out).mapM fun k =>
    (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)
  let aesKeys ← liftComp ($ᵗ (KeyName C × HashOutput → Digest)) (LocalSpec C)
  let p ← (simulateQ logImpl (Z (st, flagOutputs K prims label calls D out (liveKnownKeys D out) hashes aesKeys))).run []
  pure (hashes, p.2)

/-- `flagZ` is its flag on `flagRun`. -/
theorem flagZ_eq_flagRun (flag : FlagView C → Bool) (r : (logAdversary A).State × (C.Party → Option (Keys C))) :
    flagZ K prims D label calls A Z flag r =
      (fun y => flag ⟨r.1.2, r.2, liveKnownKeys D r.2, y.1, y.2⟩) <$> flagRun K prims label calls D A Z r.1.1 r.2 := by
  simp only [flagZ, flagRun, map_bind, map_pure]
  rfl

/-- A sample through a bijection `e` has the law of the sample, in the local run on every cache. -/
theorem run_sample_bijective {α β γ : Type} [SampleableType α] (pre : OracleComp (LocalSpec C) γ)
    (G : γ → α → OracleComp (LocalSpec C) β) (e : α → α) (he : Function.Bijective e) (s : HashCache C) :
    (simulateQ (localAnswer prims) (pre >>= fun c => liftComp ($ᵗ α) (LocalSpec C) >>= fun a => G c (e a))).run s =ᵈ
      (simulateQ (localAnswer prims) (pre >>= fun c => liftComp ($ᵗ α) (LocalSpec C) >>= fun a => G c a)).run s := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_local_sample_seedGensecurity, StateT.run_lift, bind_assoc,
    pure_bind]
  refine EvalDistEq.bind_right _ fun p => ?_
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective he).bind_left
    fun a => (simulateQ (localAnswer prims) (G p.1 a)).run p.2
  rwa [bind_map_left] at h

/-- The run of `flagZ` on the outputs with fresh hidden keys has the law of the run with zero fresh
keys. -/
theorem flagRun_freshOverlay [SampleableType E] (st : A.State) (out : C.Party → Option (Keys C))
    (f : (C.Term → HashOutput) × (C.Pair → HashOutput)) (s : HashCache C) :
    (simulateQ (localAnswer prims) (flagRun K prims label calls D A Z st (freshOverlay D f out))).run s =ᵈ
      (simulateQ (localAnswer prims) (flagRun K prims label calls D A Z st (freshOverlay D zeroKeys out))).run s := by
  have hout : ∀ hashes aesKeys, flagOutputs K prims label calls D (freshOverlay D zeroKeys out) (liveKnownKeys D out)
      hashes aesKeys = flagOutputs K prims label calls D (freshOverlay D f out) (liveKnownKeys D out) hashes
        (aesKeys ∘ freshSwap D f) := by
    intro hashes aesKeys
    funext i
    by_cases hi : i ∈ D.1
    · simp only [flagOutputs, hi, ite_true]
    · simp only [flagOutputs, hi, ite_false, freshOverlay]
      cases out i with
      | none => rfl
      | some k => simp only [Option.map_some, streams_freshSwap K prims D f _ hashes aesKeys i hi k label calls]
  have he : Function.Bijective fun aesKeys : KeyName C × HashOutput → Digest => aesKeys ∘ freshSwap D f :=
    Function.Involutive.bijective fun aesKeys => by
      funext x
      simp only [Function.comp_apply, freshSwap_involutive D f x]
  unfold flagRun
  rw [liveKnownKeys_freshOverlay, liveKnownKeys_freshOverlay]
  simp only [hout]
  exact run_sample_bijective prims _ (fun hashes aesKeys => do
    let p ← (simulateQ logImpl (Z (st, flagOutputs K prims label calls D (freshOverlay D f out) (liveKnownKeys D out)
      hashes aesKeys))).run []
    pure (hashes, p.2)) _ he s |>.symm

end FlagRun

section Experiment

variable (label : ℕ) (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
  (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E)))

/-- The logged setup run on the shared cache, before the distinguisher. -/
def setupPre : OracleComp (LocalSpec C) ((logAdversary A).State × (C.Party → Option (Keys C))) := do
  let state ← (logAdversary A).start (corruptInputs D x) z
  let steps ← startSteps localRoles D fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
  executeRounds localRoles D (logAdversary A) noFunctionality setupRounds state steps

/-- The `flagZ` experiment with the fresh hidden keys. It gives the fresh hidden keys, the logged setup run, and the
hashes of the known keys with the log of `Z`. -/
def flagExperiment : ProbComp (((C.Term → HashOutput) × (C.Pair → HashOutput)) ×
    ((logAdversary A).State × (C.Party → Option (Keys C))) × (List HashOutput × List HashOutput)) := do
  let p ← (simulateQ (localAnswer prims) (setupPre D A x z)).run ∅
  let f ← freshKeys
  let y ← (simulateQ (localAnswer prims) (flagRun K prims label calls D A Z p.1.1.1 (freshOverlay D f p.1.2))).run' p.2
  pure (f, p.1, y)

/-- The game with `seedGenHiddenZ` and `keyFlag` accepts with the probability of the flag on `flagExperiment`. -/
theorem accepts_eq_flagExperiment :
    accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
          (seedGenHiddenZ D (flagZ K prims D label calls A Z (keyFlag D)))) =
      (Pr{let e ← flagExperiment K prims label calls D A x z Z}[keyFlag D ⟨e.2.1.1.2, freshOverlay D e.1 e.2.1.2,
        liveKnownKeys D (freshOverlay D e.1 e.2.1.2), e.2.2.1, e.2.2.2⟩ = true]).toReal := by
  have h : (simulateQ (localAnswer prims) (setupLocalGame .prss D (logAdversary A) x z
      (seedGenHiddenZ D (flagZ K prims D label calls A Z (keyFlag D))))).run' ∅ =
      (fun e => keyFlag D ⟨e.2.1.1.2, freshOverlay D e.1 e.2.1.2, liveKnownKeys D (freshOverlay D e.1 e.2.1.2), e.2.2.1,
        e.2.2.2⟩) <$> flagExperiment K prims label calls D A x z Z := by
    unfold setupLocalGame flagExperiment setupPre seedGenHiddenZ freshKeys
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, flagZ_eq_flagRun,
      simulateQ_local_sample_seedGensecurity, StateT.run_lift, simulateQ_map, StateT.run_map, map_bind, bind_assoc,
      Functor.map_map, bind_map_left, bind_pure_comp]
    rfl
  rw [← setupLocalGame_accepts, h, prEvent_map]

omit [Field E] [Algebra Bit E] in
/-- One step of the logged setup run adds at most `step` keys to the log of the adversary. -/
theorem stepRound_log_le {α : Type} (step : ℕ) (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)
    (state : (logAdversary A).State) (steps : C.Party → Step C E RealSpec α) :
    ∀ r ∈ support (stepRound localRoles D (logAdversary A) noFunctionality state steps),
      r.1.2.length ≤ state.2.length + step := by
  intro r hr'
  unfold stepRound at hr'
  split_ifs at hr' with hcall
  · obtain ⟨i, -, hi⟩ := hcall.1
    obtain ⟨e, -⟩ := Option.isSome_iff_exists.mp hi
    exact e.elim
  · simp only [support_bind, Set.mem_iUnion] at hr'
    obtain ⟨⟨st', sent⟩, hp, hr'⟩ := hr'
    simp only [support_pure, Set.mem_singleton_iff] at hr'
    obtain ⟨_, _, rfl⟩ := hr'
    obtain ⟨p, hpr, he⟩ := (mem_support_bind_iff _ _ _).1 hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((mem_support_pure_iff _ _).1 he)
    exact logImpl_length_le _ step (hr _ _) _ p hpr

omit [Field E] [Algebra Bit E] in
/-- A run of at most `fuel` steps adds at most `fuel * step` keys to the log of the adversary. -/
theorem executeRounds_log_le {α : Type} (step : ℕ) (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step) :
    ∀ (fuel : ℕ) (state : (logAdversary A).State) (steps : C.Party → Step C E RealSpec α),
      ∀ r ∈ support (executeRounds localRoles D (logAdversary A) noFunctionality fuel state steps),
        r.1.2.length ≤ state.2.length + fuel * step
  | 0, state, steps => by
    intro r hr'
    simp only [executeRounds] at hr'
    rw [(mem_support_pure_iff _ _).1 hr']
    exact Nat.le_add_right _ _
  | fuel + 1, state, steps => by
    intro r hr'
    simp only [executeRounds] at hr'
    split_ifs at hr' with hdone
    · rw [(mem_support_pure_iff _ _).1 hr']
      exact Nat.le_add_right _ _
    · obtain ⟨p, hp, hr'⟩ := (mem_support_bind_iff _ _ _).1 hr'
      have h1 := stepRound_log_le D A step hr state steps p hp
      have h2 := executeRounds_log_le step hr fuel p.1 p.2.1 r hr'
      rw [Nat.succ_mul]
      omega

omit [Field E] [Algebra Bit E] in
/-- The logged setup run gives a log of at most `start + setupRounds * step` keys. -/
theorem setupPre_log_le (start step : ℕ) (hs : ∀ x z, IsQueryBoundP (A.start x z) Counted start)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step) :
    ∀ r ∈ support (setupPre D A x z), r.1.2.length ≤ start + setupRounds * step := by
  intro r hr'
  unfold setupPre at hr'
  obtain ⟨st, hst, hr'⟩ := (mem_support_bind_iff _ _ _).1 hr'
  obtain ⟨steps, -, hr'⟩ := (mem_support_bind_iff _ _ _).1 hr'
  have h1 := logImpl_length_le _ start (hs _ _) [] st hst
  have h2 := executeRounds_log_le D A step hr setupRounds st steps r hr'
  simp only [List.length_nil, Nat.zero_add] at h1
  omega

/-- The log of `Z` in `flagRun` has at most `final` keys. -/
theorem flagRun_zlog_le (final : ℕ) (hz : ∀ r, IsQueryBoundP (Z r) Counted final) (st : A.State)
    (out : C.Party → Option (Keys C)) :
    ∀ y ∈ support (flagRun K prims label calls D A Z st out), y.2.length ≤ final := by
  intro y hy
  unfold flagRun at hy
  obtain ⟨hashes, -, hy⟩ := (mem_support_bind_iff _ _ _).1 hy
  obtain ⟨aesKeys, -, hy⟩ := (mem_support_bind_iff _ _ _).1 hy
  obtain ⟨p, hp, hy⟩ := (mem_support_bind_iff _ _ _).1 hy
  rw [(mem_support_pure_iff _ _).1 hy]
  have h := logImpl_length_le _ final (hz _) [] p hp
  simpa only [List.length_nil, Nat.zero_add] using h

/-- The view of a run is the log of the adversary, the known keys and the log of `Z`. -/
def viewOf (p : (logAdversary A).State × (C.Party → Option (Keys C))) (y : List HashOutput × List HashOutput) :
    List HashOutput :=
  p.1.2 ++ liveKnownKeys D p.2 ++ y.2

/-- The law of the view. It is the experiment with zero fresh keys, so it reads no fresh key. -/
def flagView : ProbComp (List HashOutput) := do
  let p ← (simulateQ (localAnswer prims) (setupPre D A x z)).run ∅
  let y ← (simulateQ (localAnswer prims)
    (flagRun K prims label calls D A Z p.1.1.1 (freshOverlay D zeroKeys p.1.2))).run' p.2
  pure (viewOf D A p.1 y)

/-- In `flagExperiment`, the view is independent of the fresh hidden keys, and its law is
`flagView`. -/
theorem flagExperiment_view_independent [SampleableType E] :
    (fun e => (viewOf D A e.2.1 e.2.2, e.1)) <$> flagExperiment K prims label calls D A x z Z =ᵈ
      (do let list ← flagView K prims label calls D A x z Z; let f ← freshKeys (C := C); pure (list, f)) := by
  unfold flagExperiment flagView
  simp only [map_bind, map_pure, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun p => ?_
  refine (EvalDistEq.bind_right _ fun f => ?_).trans (EvalDistEq.bind_bind_swap _ _ _)
  have h := (flagRun_freshOverlay K prims label calls D A Z p.1.1.1 p.1.2 f p.2).map Prod.fst
  simp only [← StateT.run'_eq] at h
  exact h.bind_left _

/-- The view has at most `q + C.n * (termCount C + C.n)` keys. -/
theorem flagView_length_le (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    ∀ list ∈ support (flagView K prims label calls D A x z Z), list.length ≤ q + C.n * (termCount C + C.n) := by
  obtain ⟨start, step, final, hsum, hs, hr, -, hz⟩ := hq
  intro list hl
  unfold flagView at hl
  obtain ⟨p, hp, hl⟩ := (mem_support_bind_iff _ _ _).1 hl
  obtain ⟨y, hy, hl⟩ := (mem_support_bind_iff _ _ _).1 hl
  rw [(mem_support_pure_iff _ _).1 hl]
  have hp' : p.1 ∈ support (setupPre D A x z) := by
    refine support_simulateQ_run'_subset (localAnswer prims) _ ∅ ?_
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hp
  have h1 := setupPre_log_le D A x z start step hs hr p.1 hp'
  have h2 := flagRun_zlog_le K prims label calls D A Z final hz _ _ y (support_simulateQ_run'_subset _ _ p.2 hy)
  have h3 := liveKnownKeys_length_le D p.1.2
  simp only [viewOf, List.length_append]
  omega

end Experiment

/-- The law of the view, in the form of the second premise of `prssRealRand_key`. The fresh keys of
`seedGenHiddenZ` can be sampled after the view `flagView`, which has at most
`q + C.n * (termCount C + C.n)` keys. -/
theorem prssRealRand_view [SampleableType E] (label : ℕ) (calls : List RandCall) :
    ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) x z Z q, IsQueryBounded A Z setupRounds q →
      ∃ view : ProbComp (List HashOutput), (∀ list ∈ support view, list.length ≤ q + C.n * (termCount C + C.n)) ∧
        accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
            (seedGenHiddenZ D (flagZ K prims D label calls A Z (keyFlag D)))) ≤
          (Pr{let p ← (do let list ← view; let r ← freshKeys (C := C); pure (list, r))}[
            FreshEvent D p.2 p.1]).toReal := by
  intro D A x z Z q hq
  refine ⟨flagView K prims label calls D A x z Z, flagView_length_le K prims label calls D A x z Z q hq, ?_⟩
  rw [accepts_eq_flagExperiment,
    ← (flagExperiment_view_independent K prims label calls D A x z Z).prEvent_eq (fun p => FreshEvent D p.2 p.1),
    prEvent_map]
  refine ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono _ _ _ fun e he => ?_)
  have h := keyFlag_hiddenOverlay D e.1.1 e.1.2 e.2.1.2 e.2.1.1.2 (liveKnownKeys D (freshOverlay D e.1 e.2.1.2))
    e.2.2.1 e.2.2.2 (of_decide_eq_true he)
  rw [liveKnownKeys_freshOverlay] at h
  exact h

end ThresholdLeanXmssSecurity
