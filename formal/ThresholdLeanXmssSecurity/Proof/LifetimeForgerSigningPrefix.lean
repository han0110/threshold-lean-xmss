import ThresholdLeanXmssSecurity.Proof.LifetimeForgerSourceSafe
import ThresholdLeanXmssSecurity.Proof.LifetimeDealerTableReady

/-! # Precomputation and the actual signing continuation

The dealer-table prefix preserves the original signing-game output law. The
private-table forger and its direct programmable source have the same final
win computation when the initial keygen slice is empty.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix
open LifetimeForgerMerge LifetimeSigningFrame LifetimeForgerSourceParts
open LifetimePrecomputeSwap LifetimeTableReplay LifetimeJointLink LifetimeIdealBad
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {C : Committee} {E : Type}

private def worldRoHom : OracleComp (RoSpec C) →ᵐ OracleComp (WorldSpec C) where
  toFun _ := worldRo
  toFun_pure' a := by simp only [worldRo, liftComp_pure, free_pure]
  toFun_bind' p f := by simp only [worldRo, liftComp_bind, free_bind]

private theorem worldRo_run (prims : Primitives) {α : Type}
    (p : OracleComp (RoSpec C) α) (c : HashCache C) :
    (simulateQ (worldAnswer prims) (worldRo p)).run c = roRun prims p c := by
  simp only [worldRo, simulateQ_free, localRun_liftComp]

private theorem worldRo_safe {α : Type} (p : OracleComp (RoSpec C) α) :
    IsQueryBoundP (worldRo p) OtherProgram 0 :=
  LifetimeSlotQuiet.otherProgram_of_quiet _ (LifetimeKeygenPrograms.free_quiet _)

private theorem dealer_safe {α : Type} (p : OracleComp (WorldSpec C) α)
    (h : IsQueryBoundP p (fun t => ¬ DealerQuery t) 0) : IsQueryBoundP p OtherProgram 0 := by
  apply IsQueryBoundP.of_imp (p' := fun t => ¬ DealerQuery t) ?_ h
  intro t ht
  rcases t with (t | x) | t <;> simp_all only [OtherProgram, DealerQuery, not_false_eq_true]

private theorem signing_safe (d : LifetimeBridge.Dealing C) (top : TopTree)
    (q : (TsigSpec C).Domain) (st : TsigState C) :
    IsQueryBoundP ((tsigOracles worldRo (fixedDealt d top) q).run st) OtherProgram 0 := by
  apply dealer_safe
  convert (tsig_noKeygen (fun t => ¬ DealerQuery t) worldRo
    (fun p hp => by convert free_ro_dealerQuery p hp using 1; rfl)
    _ (fixedDealt_quiet d top) q st) using 1

private theorem finish_safe (d : LifetimeBridge.Dealing C) (top : TopTree)
    (st : TsigState C) (f : Forgery) :
    IsQueryBoundP (forgeryWins worldRo (fixedDealt d top) st f) OtherProgram 0 := by
  apply dealer_safe
  convert (forgeryWins_noKeygen (fun t => ¬ DealerQuery t) worldRo
    (fun p hp => by convert free_ro_dealerQuery p hp using 1; rfl)
    _ (fixedDealt_quiet d top) st f) using 1

private theorem public_safe (d : LifetimeBridge.Dealing C) (top : TopTree)
    (q : (ForgerSpec C).Domain) (st : TsigState C) :
    IsQueryBoundP ((publicHandler d top q).run st) OtherProgram 0 := by
  rcases q with t | t
  · change IsQueryBoundP ((StateT.lift
      (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) : SigningM C _).run st)
      OtherProgram 0
    rw [StateT.run_lift, bind_pure_comp]
    apply (isQueryBoundP_map_iff _ _ _).2
    exact LifetimeSlotQuiet.otherProgram_of_quiet _ (LifetimeKeygenPrograms.counted_quiet _)
  · exact signing_safe d top t st

section Assembly
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

def signingContinuation (d : LifetimeBridge.Dealing C) (top : TopTree) :
    OracleComp (WorldSpec C) Bool :=
  Prod.fst <$> tsigGameWith worldRoles (fixedDealt d top)
    (lifetimeForger K circuits settings attempts D A)

def directSigningContinuation (d : LifetimeBridge.Dealing C) (top : TopTree) :
    OracleComp (WorldSpec C) Bool := do
  let (f, st) ← (simulateQ (directHandler d top)
    (sourceReplay K circuits settings attempts D A ⟨top.root, d.1⟩ top)).run (initialSign ∅)
  forgeryWins worldRo (fixedDealt d top) st f

def signingPrecompute : OracleComp (WorldSpec C) (Bool × Bool) := do
  let d ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let tables ← worldRo (LifetimeForgerReplay.dealerTables circuits settings d.1 d.2.1)
  let win ← match (tables .top).1 with
    | some (.top top) => signingContinuation K circuits settings attempts D A d top
    | _ => pure false
  pure (LifetimeForgerReplay.searchFails tables, win)

theorem signingContinuation_eq (d : LifetimeBridge.Dealing C) (top : TopTree) :
    signingContinuation K circuits settings attempts D A d top = (do
      let (f, st) ← (simulateQ (publicHandler d top)
        (lifetimeForger K circuits settings attempts D A ⟨top.root, d.1⟩ top)).run (initialSign ∅)
      forgeryWins worldRo (fixedDealt d top) st f) := by
  simp only [signingContinuation, tsigGameWith, map_bind, map_pure, bind_pure]
  rfl

private theorem signingContinuation_safe (d : LifetimeBridge.Dealing C) (top : TopTree) :
    IsQueryBoundP (signingContinuation K circuits settings attempts D A d top) OtherProgram 0 := by
  rw [signingContinuation_eq]
  exact LifetimeKeygenPrograms.qb0_bind'
    (simulate_run_quiet OtherProgram _ (public_safe d top) _ _) fun r => finish_safe d top r.2 r.1

private def topProgram (d : LifetimeBridge.Dealing C) : OracleComp (WorldSpec C) Bool := do
  let out ← worldRo (referenceTree tweakable (prfValue d.2.1) d.1 emptyTop .top)
  match out with
  | some (.top top) => signingContinuation K circuits settings attempts D A d top
  | _ => pure false

private theorem topProgram_safe (d : LifetimeBridge.Dealing C) :
    IsQueryBoundP (topProgram K circuits settings attempts D A d) OtherProgram 0 := by
  apply LifetimeKeygenPrograms.qb0_bind' (worldRo_safe _)
  rintro (_ | (_ | _))
  · exact isQueryBoundP_pure _ _ _
  · exact signingContinuation_safe K circuits settings attempts D A d _
  · exact isQueryBoundP_pure _ _ _

private theorem tsigGame_split :
    tsigGame (lifetimeForger K circuits settings attempts D A) = (do
      let d ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      topProgram K circuits settings attempts D A d) := by
  simp only [tsigGame, dealerKeyGen, dealerKeyGenWith, bind_assoc]
  apply bind_congr
  rintro ⟨parameter, seeds, keys⟩
  have top := SeedHitProof.hom_referenceTree (worldRoHom (C := C))
    tweakable (prfValue seeds) parameter emptyTop .top
  change worldRo (referenceTree tweakable (prfValue seeds) parameter emptyTop .top) = _ at top
  unfold topProgram
  rw [top]
  apply bind_congr
  rintro (_ | (_ | _)) <;> simp only [pure_bind]
  rfl

private theorem table_top_replay (prims : Primitives)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (d : LifetimeBridge.Dealing C) (before : HashCache C)
    (r : LifetimeDealerTableReady.Tables × HashCache C)
    (hr : r ∈ support (roRun prims
      (LifetimeForgerReplay.dealerTables circuits settings d.1 d.2.1) before)) :
    roRun prims (referenceTree tweakable (prfValue d.2.1) d.1 emptyTop .top) r.2 =
      pure ((r.1 .top).1, r.2) := by
  have runs := tableRuns_of_support prims circuits settings d.1 d.2.1 hr
  rw [← roRun_dealer prims circuits settings hc hsize, roRun_map]
  have replay := runs.replay (le_refl r.2) .top
  change roRun prims (dealerCeremony circuits settings d.1 d.2.1 emptyTop .top) r.2 = _ at replay
  rw [replay, map_pure]

private theorem topProgram_replay (prims : Primitives)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (d : LifetimeBridge.Dealing C) (before : HashCache C)
    (r : LifetimeDealerTableReady.Tables × HashCache C)
    (hr : r ∈ support (roRun prims
      (LifetimeForgerReplay.dealerTables circuits settings d.1 d.2.1) before)) :
    (simulateQ (worldAnswer prims) (topProgram K circuits settings attempts D A d)).run' r.2 =
      (simulateQ (worldAnswer prims) (match (r.1 .top).1 with
        | some (.top top) => signingContinuation K circuits settings attempts D A d top
        | _ => pure false)).run' r.2 := by
  simp only [topProgram, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    worldRo_run, table_top_replay circuits settings prims hc hsize d before r hr, pure_bind]

private theorem fixed_precompute (prims : Primitives)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (d : LifetimeBridge.Dealing C) (c : HashCache C) :
    𝒟[(simulateQ (worldAnswer prims) (topProgram K circuits settings attempts D A d)).run' c] =
      𝒟[(simulateQ (worldAnswer prims) (do
        let tables ← worldRo (LifetimeForgerReplay.dealerTables circuits settings d.1 d.2.1)
        match (tables .top).1 with
        | some (.top top) => signingContinuation K circuits settings attempts D A d top
        | _ => pure false)).run' c] := by
  have ghost := evalDist_world_ghost prims
    (worldRo (LifetimeForgerReplay.dealerTables circuits settings d.1 d.2.1))
    (topProgram K circuits settings attempts D A d)
    (free_dealerTables_dealerQuery circuits settings d.1 d.2.1)
    (topProgram_safe K circuits settings attempts D A d) c
  refine ghost.symm.trans ?_
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, worldRo_run, map_bind]
  apply evalDist_bind_congr
  intro r hr
  exact congrArg evalDist (topProgram_replay K circuits settings attempts D A
    prims hc hsize d c r hr)

private theorem signingPrecompute_snd :
    Prod.snd <$> signingPrecompute K circuits settings attempts D A = (do
      let d ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let tables ← worldRo (LifetimeForgerReplay.dealerTables circuits settings d.1 d.2.1)
      match (tables .top).1 with
      | some (.top top) => signingContinuation K circuits settings attempts D A d top
      | _ => pure false) := by
  simp only [signingPrecompute, map_bind]
  apply bind_congr
  intro d
  apply bind_congr
  intro tables
  rcases (tables .top).1 with _ | (_ | _) <;>
    simp only [map_bind, map_pure, bind_pure]

/-- The added dealer-table prefix preserves the original fixed forger's output law. -/
theorem signing_precompute (prims : Primitives)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize) :
    𝒟[(simulateQ (worldAnswer prims)
      (tsigGame (lifetimeForger K circuits settings attempts D A))).run' ∅] =
    𝒟[Prod.snd <$> (simulateQ (worldAnswer prims)
      (signingPrecompute K circuits settings attempts D A)).run' ∅] := by
  rw [LifetimeForgerPrecompute.worldRun_map, tsigGame_split, signingPrecompute_snd]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply evalDist_bind_congr
  intro r _
  simpa only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind] using fixed_precompute K circuits settings attempts D A prims hc hsize r.1 r.2

private theorem finish_merged (prims : Primitives) (d : LifetimeBridge.Dealing C)
    (top : TopTree) (st : TsigState C) (f : Forgery) (pc ec : HashCache C) :
    (simulateQ (worldAnswer prims) (forgeryWins worldRo (fixedDealt d top) st f)).run' ec =
      (simulateQ (worldAnswer prims) (forgeryWins worldRo (fixedDealt d top) st f)).run'
        (mergedCache (pc, ec)) := by
  have h := congrArg (fun p : ProbComp (Bool × HashCache C) => Prod.fst <$> p)
    (finish_frame prims d top st f ec pc)
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def,
    mergedCache, mergeOn_not] using h

private theorem merged_empty (c : HashCache C) (hc : ∀ q, KeygenPoint q → c q = none) :
    mergedCache (∅, c) = c := by
  funext q
  by_cases hq : KeygenPoint q
  · simp only [mergedCache, mergeOn, hq, if_true, QueryCache.empty_apply, hc q hq]
  · simp only [mergedCache, mergeOn, hq, if_false]

private theorem signingContinuation_run (prims : Primitives)
    (d : LifetimeBridge.Dealing C) (top : TopTree) (c : HashCache C) :
    (simulateQ (worldAnswer prims)
      (signingContinuation K circuits settings attempts D A d top)).run' c = (do
      let r ← privateRun prims d top
        (sourceReplay K circuits settings attempts D A ⟨top.root, d.1⟩ top) ∅ (initialSign ∅) c
      (simulateQ (worldAnswer prims)
        (forgeryWins worldRo (fixedDealt d top) r.1.2 r.1.1.1)).run' r.2) := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  rw [signingContinuation_eq, forger_source]
  simp only [StateT.run'_eq, privateRun, simulateQ_bind, simulateQ_map,
    StateT.run_bind, StateT.run_map, bind_map_left, map_bind]

/-- The original private-table forger and direct programmable source have the same win computation. -/
theorem signing_private_direct (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (c : HashCache C) (hc : ∀ q, KeygenPoint q → c q = none) :
    (simulateQ (worldAnswer prims)
      (signingContinuation K circuits settings attempts D A d top)).run' c =
    (simulateQ (worldAnswer prims)
      (directSigningContinuation K circuits settings attempts D A d top)).run' c := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  rw [signingContinuation_run]
  have merge := private_direct_merge prims d top
    (sourceReplay K circuits settings attempts D A ⟨top.root, d.1⟩ top)
    (LifetimeForgerSourceSafe.source_safe K circuits settings attempts D A ⟨top.root, d.1⟩ top)
    ∅ c (initialSign ∅)
  rw [merged_empty c hc] at merge
  simp only [directSigningContinuation, StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  change _ = (directRun prims d top
    (sourceReplay K circuits settings attempts D A ⟨top.root, d.1⟩ top) (initialSign ∅) c >>= _)
  rw [← merge, bind_map_left]
  apply bind_congr
  rintro ⟨⟨⟨f, pc⟩, st⟩, ec⟩
  exact finish_merged prims d top st f pc ec

end Assembly
end ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix.signingContinuation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix.signingContinuation_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix.signing_precompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix.signing_precompute

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix.signing_private_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSigningPrefix.signing_private_direct
