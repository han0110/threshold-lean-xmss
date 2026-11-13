import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncReal
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncStop

/-!
# Real local reads and their silent grind

The local adversary call uses its pre-call signing state for the flag and
candidate log. A raw world read observes its answer in the visible cache,
runs the quiet grind, retains the counted call, and updates the trace.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerRealTables SigningCompilerShare
open SigningCompilerSyncReal SigningCompilerUntil
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind Queries
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  rawCarriedLogged rawKeyedSplitOracle rawKeyedSplitWorld rawTraceWorld rawTraceFlatWith

/-- One local adversary call uses the pre-call signing and opening controls. -/
theorem realAdv_local_run (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (LocalSpec C).Domain)
    (a : SigningLaneUnionProof.TraceState C × HashCache C) :
    ((fuse (rawTraceFlatWith prims x
      (openingOracles x (SigningJointEagerProof.dealtOf x top)))
      (realImpl x g rest) (.inl t)).run a) =
      (fun r => (r.1, ((r.2.1.1,
        ((a.1.2.1.1, a.1.2.1.2 || SigningCoreProof.hiddenHit x a.1.2.1.1.corrupt t),
          a.1.2.2.1, a.1.2.2.2 ++ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t)), r.2.2))) <$>
        ((fuse (rawTraceWorld prims x) (realImpl x g rest) (.inl (.inl t))).run a) := by
  have hw : worldRoles.adversary (OracleComp.lift ((LocalSpec C).query t)) =
      (query (spec := WorldSpec C) (.inl (.inl t)) : OracleComp (WorldSpec C) _) :=
    ThresholdLeanXmssSecurity.adversary_query t
  simp only [fuse, StateT.run_mk, rawTraceFlatWith, openingOracles,
    SigningCoreProof.flaggedOracles, hw, HasQuery.instOfMonadLift_query,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- The primitive hash input read by a hash or PRG request. -/
def readInput : (RoSpec C).Domain → Query C
  | .inl q => q
  | .inr input => .streamKey input.2.1

/-- The local result computed from the primitive hash answer. -/
def readAnswer (prims : Primitives) : (q : (RoSpec C).Domain) → HashOutput → (RoSpec C).Range q
  | .inl _, v => v
  | .inr input, v => prims.aes.eval (truncateHash v) input.2.2

/-- The counted adversary read with its visible observation and grind explicit.
The grind ignores the count and log, which are restored before the trace update. -/
theorem rawTraceWorld_read (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (q : (RoSpec C).Domain) (st : SigningLaneUnionProof.TraceState C) (priv : HashCache C) :
    let t : (WorldSpec C).Domain := .inl (.inl (.inr q))
    ((fuse (rawTraceWorld prims x) (realImpl x g rest) t).run (st, priv)) = (do
      let z ← ((realImpl x g rest) (.inr (readInput q))).run priv
      let visible := st.1.1.1.1.1.1.cacheQuery (readInput q) z.1
      let value := readAnswer prims q z.1
      let before : SigningFlatProof.FlatState C := (st.1.1.1.1, st.2.1)
      let after : SigningFlatProof.FlatState C :=
        (((visible, st.1.1.1.1.1.2), st.1.1.1.1.2), st.2.1)
      let y ← (simulateQ (realImpl x g rest)
        ((simulateQ (rawKeyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
          (SigningR1FixedProof.cachedExtra x.2.1 x.1 before t after)).run
          ((visible, SigningFlatEagerProof.queryEntryStep
            (XmssSecurity.encodingInputLeafIndex? x.1) st.1.1.1.2
              (SigningPartnerBoundProof.hashEntry ⟨t, value⟩)), st.1.1.2))).run z.2
      let logged : SigningHitLaneProof.LoggedState C :=
        ((y.1.2.1.1, st.1.1.1.1.1.2 + SeedHitProof.signCost t), st.1.1.1.1.2.logQuery t value)
      let tr := SigningLaneUnionProof.traceStepAt x.2.1 x.1 st.1.1.1.1.1.1
        st.2.1.1 t y.1.2.1.1 st.1.2
      pure (value, (((((logged, y.1.2.1.2), y.1.2.2), tr), st.2), y.2))) := by
  cases q <;>
    simp only [fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
      rawCarriedLogged, HasQuery.instOfMonadLift_query,
      SigningGuessProof.signingRawWorld, SigningGuessProof.signingRawLocal,
      simulateQ_map, simulateQ_bind, simulateQ_pure, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_map,
      StateT.run_bind, StateT.run_pure, SigningGuessProof.privateRoObserve,
      Functor.map_map, bind_map_left, map_bind, map_pure, pure_bind, bind_assoc,
      readInput, readAnswer]
  all_goals
    simp only [SigningFlatEagerProof.ofRest, SigningFlatEagerProof.restOf,
      SigningOneRunProof.jointCachedExtra, SigningR1FixedProof.cachedExtra,
      SigningFlatEagerProof.grindExtra, bind_pure_comp]

/-- Re-observing a visible answer does not change the visible cache. -/
theorem observe_same (vis : HashCache C) (q : Query C) (v : HashOutput)
    (hv : vis q = some v) : vis.cacheQuery q v = vis := by
  funext z
  by_cases hz : z = q
  · subst z; simp only [QueryCache.cacheQuery_self, hv]
  · exact QueryCache.cacheQuery_of_ne vis v hz

/-- A visible hit returns the recorded value, including a precomputed slot hit. -/
theorem realRead_hit (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (priv vis : HashCache C)
    (h : RealPrivate x s pads noise g rest priv vis) (q : Query C) (v : HashOutput)
    (hv : vis q = some v) :
    ((realImpl x g rest) (.inr q)).run priv = pure (v, priv) := by
  have he := h.visible q v hv
  by_cases hs : IsSlot x q
  · rw [dif_pos hs] at he
    rw [realImpl_slot x g rest q hs, Option.some.inj he]
  · rw [dif_neg hs] at he
    rw [realImpl_other x g rest q hs]
    exact QueryImpl.withCaching_run_some _ he

/-- A quiet read has the lazy visible-cache law with its private cache framed. -/
theorem realRead_quiet (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (priv vis : HashCache C)
    (h : RealPrivate x s pads noise g rest priv vis) (q : Query C)
    (hq : Quiet x s pads noise q) :
    ((realImpl x g rest) (.inr q)).run priv =
      (fun r => (r.1, syncPrivate x s pads noise priv r.2)) <$>
        ((Query C →ₒ HashOutput).randomOracle q).run vis :=
  quiet_query x s pads noise g rest (.inr q) hq priv vis h.quiet

/-- The raw monitor adds no queries to the quiet grind's query alphabet. -/
theorem quiet_rawKeyedSplit_run {α : Type} (x : Keys3 C)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput)
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (oa : OracleComp (Query C →ₒ HashOutput) α)
    (hq : Queries (Quiet x s pads noise) oa)
    (st : (HashCache C × SigningPartnerBoundProof.Monitor) × (XmssSecurity.LeafIndex → Bool)) :
    Queries (QuietQ x s pads noise) ((simulateQ (rawKeyedSplitOracle keyOf) oa).run st) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp only [simulateQ_pure, StateT.run_pure]; exact Queries.pure _
  | query_bind t next ih =>
    unfold Queries at hq
    have hb := (isQueryBound_query_bind_iff ..).mp hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    apply Queries.bind
    · simp only [rawKeyedSplitOracle, StateT.run_mk,
        SigningGuessProof.privateRoObserve, Functor.map_map]
      apply Queries.map
      exact Queries.query _ hb.1
    · intro r; exact ih r.1 (by unfold Queries; exact hb.2 r.1) r.2

/-- The actual cached grind has the ordinary monitored law and a private frame. -/
theorem grind_quiet_transport (x : Keys3 C)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (before after : SigningFlatProof.FlatState C)
    (t : (WorldSpec C).Domain)
    (st : (HashCache C × SigningPartnerBoundProof.Monitor) × (XmssSecurity.LeafIndex → Bool))
    (priv : HashCache C)
    (h : ∀ q, Quiet x s pads noise q → priv q = st.1.1 q) :
    (simulateQ (realImpl x g rest)
      ((simulateQ (rawKeyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
        (SigningR1FixedProof.cachedExtra x.2.1 x.1 before t after)).run st)).run priv =
      (fun r => (r, syncPrivate x s pads noise priv r.2.1.1)) <$>
        (simulateQ (SigningOneRunProof.keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
          (SigningR1FixedProof.cachedExtra x.2.1 x.1 before t after)).run st := by
  apply quiet_rawStateLaw x s pads noise g rest _ _ _
    (rawKeyedSplitOracle_run_law _ _) st _ priv h
  exact quiet_rawKeyedSplit_run x s pads noise _ _
    (quiet_cachedExtra x s pads noise before after t) st

/-- Nonhash calls cannot trigger the eager grind. -/
theorem nonhash_cachedExtra (seeds : C.Term → HashOutput) (P : PublicParameter)
    (before after : SigningFlatProof.FlatState C) (t : (WorldSpec C).Domain)
    (ht : ∀ i, ¬SigningFlatProof.HashCallAt i t) :
    SigningR1FixedProof.cachedExtra seeds P before t after = pure () := by
  unfold SigningR1FixedProof.cachedExtra
  apply if_neg
  rintro ⟨e, _, i, _, hi⟩
  exact ht i hi

/-- Nonhash calls retain both the trace and the stale bit. -/
theorem nonhash_traceStepAt (seeds : C.Term → HashOutput) (P : PublicParameter)
    (before after : HashCache C) (st : TsigState C) (t : (WorldSpec C).Domain)
    (aux : XmssSecurity.SigningCacheTrace × Bool)
    (ht : ∀ i, ¬SigningFlatProof.HashCallAt i t) :
    SigningLaneUnionProof.traceStepAt seeds P before st t after aux = aux := by
  unfold SigningLaneUnionProof.traceStepAt
  apply dif_neg
  rintro ⟨e, _, i, _, hi⟩
  exact ht i hi

end ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.realAdv_local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.realAdv_local_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.rawTraceWorld_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.rawTraceWorld_read

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.observe_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.observe_same

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.realRead_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.realRead_hit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.realRead_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.realRead_quiet

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.quiet_rawKeyedSplit_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.quiet_rawKeyedSplit_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.grind_quiet_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.grind_quiet_transport

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.nonhash_cachedExtra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.nonhash_cachedExtra

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.nonhash_traceStepAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncRealRead.nonhash_traceStepAt
