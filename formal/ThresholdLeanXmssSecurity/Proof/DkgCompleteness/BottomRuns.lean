import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.TopRuns

/-!
# The runs of bottom tree `b`

`bottomRunsHop_of_abortOrCorrect` proves `BottomRunsHop` from `RealTreeAbortOrCorrect`. Both games
run the honest seed generation and the dealer top tree first. From there the first run of bottom
tree `b` couples with the dealer bottom tree by `firstRun_coupling`. When the dealer gives a bottom
tree, the later runs do nothing. When the randomizer search of the dealer fails, the search fails
in each later run too, because it is a function of the seeds and of `H`. `RealTreeAbortOrCorrect`
gives this, since an honest run gives an abort or the output of the tree under `H`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCompletenessProof

section BottomRuns

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- An honest run of a tree with `H` fixed to a function that is `Th` on the inputs of the MPC gives
each operator an abort or the output of the tree under that function. -/
def RealTreeAbortOrCorrect (prims : Primitives) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (h : Query C → HashOutput), Good prims h →
    ∀ o ∈ support (simulateQ (fixedLocal prims h) (realTree K circuits settings top tree parameter seeds pairKeys)),
      ∀ i, o i = none ∨ o i = ceremonyAt prims circuits parameter seeds h top tree

/-! ## The game as a local computation -/

/-- `dealtBottom` as a local computation. -/
def dealtBottomLocal (keys : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) :
    Option TopTree → OracleComp (LocalSpec C) (Option BottomTree)
  | some top => liftComp (bottomOf <$> referenceTree (fun oa => tweakable oa)
      (prfValue (gameSeeds noCoalition keys)) (gameParameter noCoalition keys) top (.bottom b)) _
  | none => pure none

/-- `referenceDkg b` as a local computation. -/
def referenceLocal (b : Fin (2 ^ layerHeight)) : OracleComp (LocalSpec C) (SetupOutputs C) :=
  seedGenLocal (E := E) >>= fun keys => dealtTopLocal keys >>= fun top =>
    dealtBottomLocal keys b top >>= fun bottom => pure fun i => (keys i, top, bottom)

omit [Fintype E] [DecidableEq E] in
theorem dealtBottom_eq (keys : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) (top : Option TopTree) :
    dealtBottom keys b top = free (dealtBottomLocal keys b top) := by
  cases top <;> simp [dealtBottom, dealtBottomLocal]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `referenceDkg b` is `referenceLocal b` on the free copy. -/
theorem referenceDkg_local (b : Fin (2 ^ layerHeight)) :
    referenceDkg (E := E) (C := C) b = free (referenceLocal (E := E) b) := by
  unfold referenceDkg referenceLocal seedGenLocal
  rw [realExecution_honestNet]
  simp only [dealtTop_eq, dealtBottom_eq, map_eq_bind_pure_comp, bind_assoc, free_bind, free_pure]
  exact (bind_assoc _ _ _).trans (bind_congr fun x => (bind_assoc _ _ _).trans
    (bind_congr fun y => by simp only [Function.comp_apply]; rfl))

/-! ## A failed search fails again -/

omit [Fintype E] [DecidableEq E] in
/-- When the tree under each function that agrees with the cache has no bottom tree, an honest run
from that cache gives no bottom tree. -/
theorem realTree_bottom_none (prims : Primitives) (hcorrect : RealTreeAbortOrCorrect K circuits settings prims)
    (hsize : 0 < settings.batchSize) (b : Fin (2 ^ layerHeight)) (top : TopTree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (s : HashCache C) (hn : NoMpc s)
    (hfail : ∀ h, Good prims h → Agrees h s →
      bottomOf (ceremonyAt prims circuits parameter seeds h top (.bottom b)) = none)
    (z : (C.Party → Option TreeOutput) × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims)
      (realTree K circuits settings top (.bottom b) parameter seeds pairKeys)).run s)) :
    ∀ i, bottomOf (z.1 i) = none := by
  obtain ⟨hle, hn', hsupp⟩ := localRun_support _ s z hz
  have hnz := hn' hn
  have hmem := hsupp _ (good_hashOf prims z.2) (agrees_hashOf prims hnz)
  intro i
  rcases hcorrect hsize top (.bottom b) parameter seeds pairKeys _ (good_hashOf prims z.2) z.1 hmem i with h | h
  · rw [h]; rfl
  · rw [h]
    exact hfail _ (good_hashOf prims z.2) ((agrees_hashOf prims hnz).mono hle)

omit [Fintype E] [DecidableEq E] in
/-- After a failed search at each function that agrees with the cache, the runs of bottom tree `b`
change no operator. -/
theorem localRuns_failed (prims : Primitives) (hcorrect : RealTreeAbortOrCorrect K circuits settings prims)
    (hsize : 0 < settings.batchSize) (b : Fin (2 ^ layerHeight)) (top : TopTree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) :
    ∀ (count : ℕ) (st : HonestState C E) (s : HashCache C),
      (∀ i, (st.operators i).keys = some (dealtKeys parameter seeds pairKeys i)) →
      (∀ i, (st.operators i).top = some top) → (∀ i, (st.operators i).bottom b = none) → NoMpc s →
      (∀ h, Good prims h → Agrees h s →
        bottomOf (ceremonyAt prims circuits parameter seeds h top (.bottom b)) = none) →
      ∀ z ∈ support ((simulateQ (localAnswer prims)
        (localRuns K circuits settings runLimit (.bottom b) count st)).run s), z.1.operators = st.operators
  | 0, st, s, _, _, _, _, _, z, hz => by
    simp only [localRuns, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | count + 1, st, s, hkeys, htop, hbot, hn, hfail, z, hz => by
    simp only [localRuns] at hz
    split_ifs at hz
    · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rw [localTreeRun_bottom K circuits settings _ b top parameter seeds pairKeys hkeys htop] at hy
      have hnone := realTree_bottom_none K circuits settings prims hcorrect hsize b top parameter seeds pairKeys s hn
        hfail y hy
      have hops : (afterRun st y.1 (.bottom b)).operators = st.operators := by
        funext i
        have hu : Function.update (st.operators i).bottom b none = (st.operators i).bottom := by
          simp [hbot i]
        simp [afterRun, OperatorState.keep, hbot i, hnone i, hu]
      obtain ⟨hle, hn', -⟩ := localRun_support _ s y hy
      have := localRuns_failed prims hcorrect hsize b top parameter seeds pairKeys count _ y.2
        (by rw [hops]; exact hkeys) (by rw [hops]; exact htop) (by rw [hops]; exact hbot) (hn' hn)
        (fun h hg ha => hfail h hg (ha.mono hle)) z hz
      rw [this, hops]
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]

/-! ## The runs of bottom tree `b` from a start cache -/

/-- For dealt keys, the dealer top tree `t` and a start cache, the runs of bottom tree `b` are at
distance `treeAbortError (.bottom b)` from the dealer bottom tree `b`. -/
theorem bottomRuns_from (prims : Primitives) (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (hcorrect : RealTreeAbortOrCorrect K circuits settings prims) (hlimit : 0 < runLimit) (b : Fin (2 ^ layerHeight))
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (t : TopTree)
    (s : HashCache C) (hs : StartInvariant s) (count : ℕ) (hcount : 0 < count) :
    letI : MeasurableSpace (SetupOutputs C) := ⊤
    measureTVDist
      ((simulateQ (localAnswer prims)
        (localRuns K circuits settings runLimit (.bottom b) count
            (withTop (fun i => some (dealtKeys parameter seeds pairKeys i)) (some t)) >>= fun st =>
          pure (setupOutputsOf b st))).run' s)
      ((simulateQ (localAnswer prims)
        (dealtBottomLocal (fun i => some (dealtKeys parameter seeds pairKeys i)) b (some t) >>= fun bottom =>
          pure fun i => (some (dealtKeys parameter seeds pairKeys i), some t, bottom))).run' s) ≤
      treeAbortError (E := E) circuits settings (.bottom b) := by
  let : MeasurableSpace (SetupOutputs C) := ⊤
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcount.ne'
  set keys : C.Party → Option (Keys C) := fun i => some (dealtKeys parameter seeds pairKeys i) with hkeys
  set st1 : HonestState C E := withTop keys (some t) with hst1
  have hmay : mayRun runLimit noCoalition st1 (.bottom b) :=
    ⟨rfl, hlimit, firstParty C, by simp [noCoalition], rfl⟩
  have hreal : localTreeRun K circuits settings st1.operators (.bottom b) =
      realTree K circuits settings t (.bottom b) parameter seeds pairKeys :=
    localTreeRun_bottom K circuits settings _ b t parameter seeds pairKeys (fun _ => rfl) (fun _ => rfl)
  set f : (C.Party → Option TreeOutput) → OracleComp (LocalSpec C) (SetupOutputs C) := fun z =>
    localRuns K circuits settings runLimit (.bottom b) n (afterRun st1 z (.bottom b)) >>= fun st =>
      pure (setupOutputsOf b st) with hf
  have hleft : (localRuns K circuits settings runLimit (.bottom b) (n + 1) st1 >>= fun st =>
      pure (setupOutputsOf b st)) = realTree K circuits settings t (.bottom b) parameter seeds pairKeys >>= f := by
    simp only [localRuns, hmay, ↓reduceIte, hreal, bind_assoc, hf]
  have hcouple := firstRun_coupling K circuits settings prims hsize t (.bottom b) parameter seeds pairKeys s hs f
  set g : Option BottomTree → OracleComp (LocalSpec C) (SetupOutputs C) := fun bottom =>
    pure fun i => (keys i, some t, bottom) with hg
  have hsupp : (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds t (.bottom b) >>= f)).run' s =ᵈ
      (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds t (.bottom b) >>= fun a =>
        g (bottomOf (a (firstParty C))))).run' s := by
    refine evalDist_run'_bind_congr prims _ _ _ s fun p hp => ?_
    obtain ⟨hn, -, o₀, heq, ho⟩ :=
      idealTree_value prims circuits settings parameter seeds t (.bottom b) hsize s hs.1 hs.2 p hp
    rw [heq]
    rcases hob : bottomOf o₀ with _ | tree
    · have hfail : ∀ h, Good prims h → Agrees h p.2 →
          bottomOf (ceremonyAt prims circuits parameter seeds h t (.bottom b)) = none := fun h hgood ha => by
        rw [← ho h p.2 hgood le_rfl ha]; exact hob
      set st' := afterRun st1 (fun _ => o₀) (.bottom b) with hst'
      have hbot : ∀ i, (st'.operators i).bottom b = none := by
        intro i; simp [hst', afterRun, OperatorState.keep, hob, hst1, withTop, startState]
      have hout : ∀ z ∈ support ((simulateQ (localAnswer prims) (f (fun _ => o₀))).run' p.2),
          z = fun i => (keys i, some t, none) := by
        intro z hz
        simp only [hf, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
          map_bind, map_pure, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        have hops := localRuns_failed K circuits settings runLimit prims hcorrect hsize b t parameter seeds pairKeys n
          st' p.2 (fun i => rfl) (fun i => by simp [hst', afterRun, OperatorState.keep, hst1, withTop]) hbot hn
          hfail w hw
        funext i
        simp only [setupOutputsOf, hops, ← hbot i]
        simp [hst', afterRun, OperatorState.keep, hst1, withTop, startState, hkeys]
      refine (evalDist_eq_pure_of_support _ _ hout).trans ?_
      simp only [hg, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact .rfl
    · have hnot : ¬ mayRun runLimit noCoalition (afterRun st1 (fun _ => o₀) (.bottom b)) (.bottom b) := by
        simp [mayRun, afterRun, OperatorState.keep, hob]
      have hfg : f (fun _ => o₀) = g (some tree) := by
        simp only [hf, hg]
        rw [localRuns_of_not_mayRun K circuits settings runLimit (.bottom b) _ hnot, pure_bind]
        congr 1
        funext i
        simp [setupOutputsOf, afterRun, OperatorState.keep, hob, hst1, withTop, startState, hkeys]
      rw [hfg]
  have hD : (dealtBottomLocal keys b (some t) >>= g) =
      liftComp (referenceTree tweakable (prfValue seeds) parameter t (.bottom b)) (LocalSpec C) >>= fun o =>
        g (bottomOf o) := by
    simp only [dealtBottomLocal, hkeys, gameSeeds_dealt, gameParameter_dealt, liftComp_map, bind_map_left]
  have hright := dealer_continuation circuits settings prims hc hsize parameter seeds t (.bottom b)
    (fun o => g (bottomOf o)) s
  rw [← hD] at hright
  rw [hleft]
  unfold measureTVDist
  rw [← hright, ← hsupp.evalDist_eq]
  exact hcouple

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The dealer top tree from a start cache gives a top tree. -/
theorem idealTop_some (prims : Primitives) (hsize : 0 < settings.batchSize) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (s : HashCache C) (hs : StartInvariant s)
    (z : (C.Party → Option TreeOutput) × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds emptyTop .top)).run s)) :
    ∃ t, TreeOutput.topTree (z.1 (firstParty C)) = some t := by
  obtain ⟨hn, -, o₀, heq, ho⟩ := idealTree_value prims circuits settings parameter seeds emptyTop .top hsize s hs.1 hs.2 z hz
  obtain ⟨h, hgood, hagree⟩ := exists_good prims z.2 hn
  rw [heq, ho h z.2 hgood le_rfl hagree, ceremonyAt_top]
  exact ⟨_, rfl⟩

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- On dealt keys and from a start cache, the dealer top tree of the game gives a top tree and keeps
`StartInvariant`. -/
theorem dealtTopLocal_support (prims : Primitives) (hc : CircuitsCompute circuits prims.Th)
    (hsize : 0 < settings.batchSize) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (s : HashCache C) (hs : StartInvariant s) (p : Option TopTree × HashCache C)
    (hp : p ∈ support ((simulateQ (localAnswer prims)
      (dealtTopLocal (fun i => some (dealtKeys parameter seeds pairKeys i)))).run s)) :
    StartInvariant p.2 ∧ ∃ t, p.1 = some t := by
  have hD : dealtTopLocal (fun i => some (dealtKeys parameter seeds pairKeys i)) =
      liftComp (TreeOutput.topTree <$> referenceTree tweakable (prfValue seeds) parameter emptyTop .top) (LocalSpec C) := by
    simp only [dealtTopLocal, Option.isSome_some, implies_true, ↓reduceIte, gameSeeds_dealt, gameParameter_dealt]
  rw [hD, localRun_liftComp, roRun_map, support_map] at hp
  generalize hR : roRun prims (referenceTree tweakable (prfValue seeds) parameter emptyTop .top) s = R at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← hR, ← roRun_dealer prims circuits settings hc hsize] at hq
  have hI : ((fun _ => q.1, q.2) : (C.Party → Option TreeOutput) × HashCache C) ∈
      support ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds emptyTop .top)).run s) := by
    have e : idealTree circuits settings parameter seeds emptyTop .top =
        liftComp ((fun o (_ : C.Party) => o) <$> (Prod.fst <$> dealerCeremony circuits settings parameter seeds
          emptyTop .top)) (LocalSpec C) := by
      simp only [idealTree, Functor.map_map]
    rw [e, localRun_liftComp, roRun_map, support_map]
    exact ⟨q, hq, rfl⟩
  exact ⟨startInvariant_idealTree circuits settings prims parameter seeds emptyTop .top hsize s hs _ hI,
    idealTop_some circuits settings prims hsize parameter seeds s hs _ hI⟩

/-- `BottomRunsHop` from `RealTreeAbortOrCorrect`. Both games share the seed generation and the
dealer top tree, and `bottomRuns_from` bounds the rest for each outcome. -/
theorem bottomRunsHop_of_abortOrCorrect
    (hcorrect : ∀ prims, RealTreeAbortOrCorrect K circuits settings prims) :
    BottomRunsHop K circuits settings runLimit := by
  intro hsize hruns prims hc b
  let : MeasurableSpace (SetupOutputs C) := ⊤
  have hnonneg : 0 ≤ treeAbortError (E := E) circuits settings (.bottom b) := by
    unfold treeAbortError coinFailure coinKeyCollision; positivity
  rw [topDealtDkg_eq, referenceDkg_local, fst_runWorld_free, fst_runWorld_free]
  unfold topDealtLocal referenceLocal
  refine tvDist_bind_le_of_support prims _ _ _ ∅ hnonneg fun p hp => ?_
  obtain ⟨parameter, seeds, pairKeys, hkeys⟩ := seedGen_dealt prims p hp
  have hs : StartInvariant p.2 := seedGenEnd prims p hp
  rw [hkeys]
  refine tvDist_bind_le_of_support prims _ _ _ p.2 hnonneg fun q hq => ?_
  obtain ⟨hs', t, ht⟩ := dealtTopLocal_support circuits settings prims hc hsize parameter seeds pairKeys p.2 hs q hq
  rw [ht]
  exact bottomRuns_from K circuits settings runLimit prims hc hsize (hcorrect prims) hruns b parameter seeds pairKeys
    t q.2 hs' runLimit hruns

end BottomRuns

/-- info: 'ThresholdLeanXmssSecurity.DkgCompletenessProof.bottomRunsHop_of_abortOrCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bottomRunsHop_of_abortOrCorrect

end ThresholdLeanXmssSecurity.DkgCompletenessProof
