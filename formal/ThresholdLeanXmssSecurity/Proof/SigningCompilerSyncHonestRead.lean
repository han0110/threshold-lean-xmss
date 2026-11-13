import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRealRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncLocalRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncLocalSlot

/-! # Real reads on both routes

A read of `H` or of the PRG goes through the local adversary call or through the honest copy. Both
routes have the same normal form.

- `rawTraceWorld_read_honest` is the normal form of `rawTraceWorld_read` for the honest copy.
- `rawTraceWorld_read_route` states the normal form for a call `t` on either route.
- `realWorld_slot_route`, `realWorld_read_view_route` and `realWorld_read_fields_route` are
  `realWorld_slot`, `realWorld_read_view` and `realWorld_read_fields` for a call `t` on either
  route. The value of a call `t` needs a `cast`, because the range of a variable `t` does not
  reduce.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncBackend SigningCompilerSyncRealRead
open SigningCompilerSyncTrigger SigningCompilerUntil
open SigningCompilerSyncLocalRead SigningCompilerSyncLocalSlot
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

section Read
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind Queries
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  rawCarriedLogged rawKeyedSplitOracle rawKeyedSplitWorld rawTraceWorld rawTraceFlatWith

/-- The counted honest read with its visible observation and grind explicit. -/
theorem rawTraceWorld_read_honest (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (q : (RoSpec C).Domain) (st : SigningLaneUnionProof.TraceState C) (priv : HashCache C) :
    let t : (WorldSpec C).Domain := .inr (.inr q)
    ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x) (realImpl x g rest) t).run (st, priv)) = (do
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
    simp only [ThresholdLeanXmssSecurity.fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
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

/-- One law for both counted read routes, the local adversary call and the honest copy. -/
theorem rawTraceWorld_read_route (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (q : (RoSpec C).Domain) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr q)) ∨ t = .inr (.inr q))
    (st : SigningLaneUnionProof.TraceState C) (priv : HashCache C) :
    ((ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x) (realImpl x g rest) t).run (st, priv)) = (do
      let z ← ((realImpl x g rest) (.inr (readInput q))).run priv
      let visible := st.1.1.1.1.1.1.cacheQuery (readInput q) z.1
      let value : (WorldSpec C).Range t :=
        cast (by rcases ht with rfl | rfl <;> rfl) (readAnswer prims q z.1)
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
  rcases ht with rfl | rfl
  · exact rawTraceWorld_read prims x g rest q st priv
  · exact rawTraceWorld_read_honest prims x g rest q st priv

end Read

section Slot

/-- A slot read on either route returns the fixed table value and observes it. -/
theorem realWorld_slot_route (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (input : Query C) (hs : IsSlot x input) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr (.inl input))) ∨ t = .inr (.inr (.inl input))) (a : RealState C) :
    ((SigningCompilerUntil.fuse (rawTraceWorld prims x) (realImpl x g rest) t).run a) =
      (let value : (WorldSpec C).Range t :=
        cast (by rcases ht with rfl | rfl <;> rfl) (realTable g rest hs.choose)
      let logged : SigningHitLaneProof.LoggedState C :=
        (((visibleOf a).cacheQuery input (realTable g rest hs.choose), a.1.1.1.1.1.1.2 + 1),
          a.1.1.1.1.1.2.logQuery t value)
      pure (value, (((((logged, a.1.1.1.1.2), a.1.1.1.2), a.1.1.2), a.1.2), a.2))) := by
  change (ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x) (realImpl x g rest) t).run a = _
  rw [rawTraceWorld_read_route prims x g rest (.inl input) t ht a.1 a.2]
  simp only [readInput]
  rw [realImpl_slot x g rest input hs]
  simp only [pure_bind, readAnswer]
  have hn : ∀ i, ¬SigningFlatProof.HashCallAt i t := by
    rcases ht with rfl | rfl
    · exact (slot_no_hashCall x input hs).1
    · exact (slot_no_hashCall x input hs).2
  rw [nonhash_cachedExtra x.2.1 x.1 _ _ _ hn]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rw [nonhash_traceStepAt x.2.1 x.1 _ _ _ _ _ hn]
  obtain ⟨z, hz⟩ := hs
  rcases ht with rfl | rfl <;> rcases z with ⟨T, p⟩ | m <;> subst input <;>
    simp [TprfSecurityProof.slotInput, SigningPartnerBoundProof.hashEntry,
      SigningFlatEagerProof.queryEntryStep, SeedHitProof.signCost]

end Slot

section View
set_option linter.constructorNameAsVariable false
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt

/-- Forgetting monitors and the private cache gives the exact counted-call view, on either
route. -/
theorem realWorld_read_view_route (prims : Primitives) (x : Keys3 C)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (rq : (RoSpec C).Domain) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr rq)) ∨ t = .inr (.inr rq)) (a : RealState C)
    (hr : RealPrivate x s pads noise g rest a.2 (visibleOf a))
    (h : (∃ value, visibleOf a (readInput rq) = some value) ∨
      Quiet x s pads noise (readInput rq)) :
    realReadView <$> (fuse (rawTraceWorld prims x) (realImpl x g rest) t).run a =
    (fun r => ((cast (by rcases ht with rfl | rfl <;> rfl) (readAnswer prims rq r.1) :
        (WorldSpec C).Range t), r.2)) <$>
      cacheRead x.1 x.2.1 (readInput rq) t a.1.2.1.1 a.1.1.2 (visibleOf a) := by
  rw [rawTraceWorld_read_route prims x g rest rq t ht,
    realRead_ordinary x s pads noise g rest a.2 (visibleOf a) hr _ h]
  simp only [map_bind, bind_map_left, cacheRead]
  apply bind_congr_of_forall_mem_support
  intro z hz
  have ho := randomOracle_observe (visibleOf a) (readInput rq) z hz
  rw [ho]
  rw [grind_quiet_transport x s pads noise g rest _ _ _ _ _
    (fun input hi => syncPrivate_agrees x s pads noise a.2 z.2 input hi)]
  simp only [map_pure]
  have he : SigningR1FixedProof.cachedExtra x.2.1 x.1
      (a.1.1.1.1.1, a.1.2.1) t
      (((z.2, a.1.1.1.1.1.1.2), a.1.1.1.1.1.2), a.1.2.1) =
      SigningR1FixedProof.cachedExtra x.2.1 x.1
        ((((visibleOf a), 0), []), a.1.2.1.1, false) t
        (((z.2, 0), []), a.1.2.1.1, false) :=
    cachedExtra_congr x.2.1 x.1 _ _ _ _ _ rfl rfl rfl
  rw [he]
  simp only [bind_map_left]
  rw [← keyedSplit_cache_forget (XmssSecurity.encodingInputLeafIndex? x.1) _
    ((z.2, SigningFlatEagerProof.queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
      a.1.1.1.1.2 (SigningPartnerBoundProof.hashEntry
        ⟨t, cast (by rcases ht with rfl | rfl <;> rfl) (readAnswer prims rq z.1)⟩)), a.1.1.1.2)]
  simp only [bind_map_left]
  rfl

/-- Every real RO or PRG call on either route counts once and retains the opening state. -/
theorem realWorld_read_fields_route (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (rq : (RoSpec C).Domain) (t : (WorldSpec C).Domain)
    (ht : t = .inl (.inl (.inr rq)) ∨ t = .inr (.inr rq)) (a : RealState C)
    (r : (WorldSpec C).Range t × RealState C)
    (hr : r ∈ support ((fuse (rawTraceWorld prims x) (realImpl x g rest) t).run a)) :
    r.2.1.2 = a.1.2 ∧ r.2.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1 := by
  rw [rawTraceWorld_read_route prims x g rest rq t ht] at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨z, _, y, _, rfl⟩ := hr
  exact ⟨rfl, by rcases ht with rfl | rfl <;> cases rq <;> rfl⟩

end View

end ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.rawTraceWorld_read_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.rawTraceWorld_read_honest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.rawTraceWorld_read_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.rawTraceWorld_read_route

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.realWorld_slot_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.realWorld_slot_route

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.realWorld_read_view_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.realWorld_read_view_route

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.realWorld_read_fields_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncHonestRead.realWorld_read_fields_route
