import Sketch.Bridge

/-!
# Hop C5a, the runs of the top tree

`topRunsHop_of_seedGenEnd` proves `TopRunsHop` from `SeedGenEnd`. The honest seed generation gives
dealt keys and a start cache. From there the first run of the top tree couples with the dealer top
tree by `firstRun_coupling`. The dealer top tree never fails, so the later runs of the top tree do
nothing, and the dealer is `referenceTree` jointly with the cache by `dealer_continuation`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- For dealt keys and a start cache, the runs of the top tree and then of bottom tree `b` are at
distance `treeAbortError .top` from the dealer top tree and then the runs of bottom tree `b`. -/
theorem topRuns_from (prims : Primitives) (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (hlimit : 0 < runLimit) (b : Fin (2 ^ layerHeight)) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (s : HashCache C) (hs : StartInvariant s) (count : ℕ) (hcount : 0 < count) :
    letI : MeasurableSpace (SetupOutputs C) := ⊤
    measureTVDist
      ((simulateQ (localAnswer prims)
        (localRuns K circuits settings runLimit .top count
            (startState noCoalition () fun i => some (dealtKeys parameter seeds pairKeys i)) >>= fun st =>
          localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (outputsOf b st))).run' s)
      ((simulateQ (localAnswer prims)
        (dealtTopLocal (fun i => some (dealtKeys parameter seeds pairKeys i)) >>= fun top =>
          localRuns K circuits settings runLimit (.bottom b) runLimit
            (withTop (fun i => some (dealtKeys parameter seeds pairKeys i)) top) >>= fun st =>
              pure (outputsOf b st))).run' s) ≤
      treeAbortError (E := E) circuits settings .top := by
  let : MeasurableSpace (SetupOutputs C) := ⊤
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcount.ne'
  set keys : C.Party → Option (Keys C) := fun i => some (dealtKeys parameter seeds pairKeys i) with hkeys
  set st0 : HonestState C E := startState noCoalition () keys with hst0
  have hmay : mayRun runLimit noCoalition st0 .top :=
    ⟨hlimit, firstParty C, by simp [noCoalition], rfl⟩
  have hreal : localTreeRun K circuits settings st0.operators .top =
      realTree K circuits settings emptyTop .top parameter seeds pairKeys :=
    localTreeRun_top K circuits settings _ parameter seeds pairKeys fun _ => rfl
  set f : (C.Party → Option TreeOutput) → OracleComp (LocalSpec C) (SetupOutputs C) := fun z =>
    localRuns K circuits settings runLimit .top n (afterRun st0 z .top) >>= fun st =>
      localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (outputsOf b st) with hf
  have hleft : (localRuns K circuits settings runLimit .top (n + 1) st0 >>= fun st =>
      localRuns K circuits settings runLimit (.bottom b) runLimit st >>= fun st => pure (outputsOf b st)) =
      realTree K circuits settings emptyTop .top parameter seeds pairKeys >>= f := by
    simp only [localRuns, hmay, ↓reduceIte, hreal, bind_assoc, hf]
  have hcouple := firstRun_coupling K circuits settings prims hsize emptyTop .top parameter seeds pairKeys s hs f
  set g : Option TopTree → OracleComp (LocalSpec C) (SetupOutputs C) := fun top =>
    localRuns K circuits settings runLimit (.bottom b) runLimit (withTop keys top) >>= fun st =>
      pure (outputsOf b st) with hg
  have hsupp : (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds emptyTop .top >>= f)).run' s =ᵈ
      (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds emptyTop .top >>= fun a =>
        g (TreeOutput.topTree (a (firstParty C))))).run' s := by
    refine evalDist_run'_bind_congr prims _ _ _ s fun p hp => ?_
    obtain ⟨hn, -, o₀, heq, ho⟩ :=
      idealTree_value_from circuits settings prims parameter seeds emptyTop .top hsize s hs p hp
    obtain ⟨h, hgood, hagree⟩ := exists_good prims p.2 hn
    have ho₀ := ho h p.2 hgood le_rfl hagree
    rw [ceremonyAt_top] at ho₀
    rw [heq, ho₀]
    set t : TopTree := _ with ht
    have hnot : ¬ mayRun runLimit noCoalition (afterRun st0 (fun _ => some (.top t)) .top) .top := by
      simp [mayRun, afterRun, OperatorState.keep, TreeOutput.topTree]
    have hfg : f (fun _ => some (.top t)) = g (some t) := by
      simp only [hf, hg]
      rw [localRuns_of_not_mayRun K circuits settings runLimit .top _ hnot, pure_bind]
      refine localRuns_outputs_congr K circuits settings runLimit (.bottom b) b runLimit _ _ ?_ rfl ?_
      · funext i
        simp [afterRun, withTop, OperatorState.keep, TreeOutput.topTree, hst0, startState]
      · simp [afterRun, withTop, hst0, startState]
    rw [hfg]
    exact .rfl
  have hD : (dealtTopLocal keys >>= g) = liftComp (referenceTree tweakable (prfValue seeds) parameter emptyTop .top)
      (LocalSpec C) >>= fun o => g (TreeOutput.topTree o) := by
    simp only [dealtTopLocal, hkeys, Option.isSome_some, implies_true, ↓reduceIte, gameSeeds_dealt,
      gameParameter_dealt, liftComp_map, bind_map_left]
  have hright := dealer_continuation circuits settings prims hc hsize parameter seeds emptyTop .top
    (fun o => g (TreeOutput.topTree o)) s
  rw [← hD] at hright
  rw [hleft]
  unfold measureTVDist
  rw [← hright, ← hsupp.evalDist_eq]
  exact hcouple

/-- `TopRunsHop` from `SeedGenEnd`. The seed generation gives dealt keys and a start cache, and then
`topRuns_from` bounds the rest of the game for each outcome. -/
theorem topRunsHop_of_seedGenEnd (seedGenEnd : ∀ prims, SeedGenEnd (C := C) (E := E) prims) :
    TopRunsHop K circuits settings runLimit := by
  intro hsize hruns prims hc b
  let : MeasurableSpace (SetupOutputs C) := ⊤
  rw [honestDkg_eq, topDealtDkg_eq, fst_runWorld_free, fst_runWorld_free]
  unfold honestLocal topDealtLocal
  refine tvDist_bind_le_of_support prims _ _ _ ∅
    (by unfold treeAbortError coinFailure coinKeyCollision; positivity) fun p hp => ?_
  obtain ⟨parameter, seeds, pairKeys, hkeys⟩ := seedGen_dealt prims p hp
  have hs : StartInvariant p.2 := seedGenEnd prims p hp
  rw [hkeys]
  exact topRuns_from K circuits settings runLimit prims hc hsize hruns b parameter seeds pairKeys p.2 hs runLimit hruns

/-- info: 'ThresholdLeanXmss.Sketch.topRunsHop_of_seedGenEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topRunsHop_of_seedGenEnd

end ThresholdLeanXmss.Sketch
