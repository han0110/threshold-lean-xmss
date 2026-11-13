import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRelease

/-! # Single-query laws for the signing compiler

The fixed-table backend retains its full state while exposing the exact order
of marks, opening-release guards, share reads and counted hash tails.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncBackend
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

section Backend
variable (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
  (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
  (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)

theorem backendT_mark (b : Bool) (st : FullState C Tag) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inr b))).run st = pure ((), (st.1.1, b), st.2) := by
  simp [shareBackendTagT, backendRaw, resolvePrivateTable_lift, eagerBackend,
    SigningCompilerUntil.fuse, shareBackendTag, StateT.run]
  rfl

theorem backendT_snapshot (st : FullState C Tag)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl .snapshot)))).run st = pure (dataOf x st, st) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run,
    ordinary_snapshot, pure_bind, splitRest_merged_of_restFree _ _ _ hf]

theorem backendT_uniform (n : ℕ) (st : FullState C Tag)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.uniform n))))).run st =
      (fun v => (v, st)) <$> (query (spec := unifSpec) n) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw,
    simulateQ_bind, resolvePrivateTable_lift, simulateQ_pure, StateT.run]
  rw [ordinary_uncounted x.1 x.2.1 q s pads (.uniform n)
    (by exact not_false) (by intro p; simp)]
  simp [compilerImpl, deferredImpl, StateT.run,
    splitRest_merged_of_restFree _ _ _ hf]
  rfl

/-- The constrained branch is the existing eager read law, with both views retained. -/
theorem backendT_shareRead (input : Query C) (T : C.Term) (p : CPoint)
    (hr : route x.2.1 input = some (T, p)) (st : FullState C Tag) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.hash input))))).run st = (do
      let a ← (SigningShareLazy.eagerImpl C.terms τ g (.read T p (tagOf st.1))).run st.2
      let r ← hashTail x.1 x.2.1 (key x.2.1 (T, p))
        (merged x.2.1 st.1.1 st.2.cache) a.1 (merge x.2.1 st.1.1.1.1.data.cache a.2.cache)
      pure (r.1, ((splitRest x.2.1 r.2, st.1.2), a.2))) := by
  simp only [shareBackendTagT, backendRaw, hr, resolvePrivateTable_lift,
    eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, StateT.run]
  exact eager_read tagOf x.1 x.2.1 τ g T p st

theorem backendT_rest (input : Query C) (z : RestSlot C)
    (hr : route x.2.1 input = none) (hz : restRoute x.2.1 x.2.2 input = some z)
    (st : FullState C Tag) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.hash input))))).run st =
      (fun a => (a.1, ((splitRest x.2.1 a.2, st.1.2), st.2))) <$>
      (match (dataOf x st).cache (restInput x.2.1 x.2.2 z) with
      | some v => hashTail x.1 x.2.1 (restInput x.2.1 x.2.2 z)
          (merged x.2.1 st.1.1 st.2.cache) v (dataOf x st).cache
      | none => hashTail x.1 x.2.1 (restInput x.2.1 x.2.2 z)
          (merged x.2.1 st.1.1 st.2.cache) (rest z)
          ((dataOf x st).cache.cacheQuery (restInput x.2.1 x.2.2 z) (rest z))) := by
  simp only [shareBackendTagT, backendRaw, hr, ordinaryFullRaw, ordinaryRaw, hz,
    StateT.run, bind_pure_comp, simulateQ_map]
  rw [freshRestT_run]
  rfl

theorem backendT_ordinaryHash (input : Query C)
    (hr : route x.2.1 input = none) (hz : restRoute x.2.1 x.2.2 input = none)
    (st : FullState C Tag) :
    (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
      (.inl (.inl (.inl (.hash input))))).run st =
      (fun a => (a.1, ((splitRest x.2.1 a.2, st.1.2), st.2))) <$>
      (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
        (deferredInputSide x.1) deferredCounted (deferredKey x.1)
        (deferredPoint x.1) q s (.inl (.hash input))).run
          (merged x.2.1 st.1.1 st.2.cache) := by
  simp only [shareBackendTagT, backendRaw, hr, ordinaryFullRaw, ordinaryRaw, hz,
    StateT.run, bind_pure_comp, simulateQ_map, resolvePrivateTable_lift, ordinary]

end Backend

/-- Interpreting one deferred query keeps the source state fixed. -/
theorem runX_deferred
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (t : DeferredQuery C) (src : SourceState C) (st : FullState C Tag) :
    runX backend (liftM (deferredQueryX t)) src st =
      (fun a => ((a.1, src), a.2)) <$>
        (backend (.inl (.inl (.inl t)))).run st := by
  simp [runX, deferredQueryX]

/-- P tests the merged snapshot before performing the counted hash call. -/
theorem runX_sourceHashX
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (input : Query C) (src : SourceState C) (st : FullState C Tag)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    let B := shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
    runX B (sourceHashX x.1 x.2.1 input) src st =
      runX B (match input with
        | .prf _ (.randomizer lay e) =>
          if lay = bottomLayer ∧ ReadyAfter x.2.1 (dataOf x st) src.signing e input
          then sourceReleaseOpeningX x.1 x.2.1 e else pure ()
        | _ => pure ()) src st >>= fun a =>
          (fun r => ((r.1, a.1.2), r.2)) <$>
            (B (.inl (.inl (.inl (.hash input))))).run a.2 := by
  dsimp only
  cases input with
  | prf seed point =>
    cases point with
    | randomizer lay e =>
      by_cases hl : lay = bottomLayer
      · subst lay
        simp [sourceHashX, runX, StateT.run_bind, StateT.run_get,
          deferredQueryX, backendT_snapshot tagOf x q s pads τ g noise rest st hf]
        split_ifs <;> simp [StateT.run_bind] <;> rfl
      · simp [sourceHashX, hl, runX, deferredQueryX]
        rfl
    | _ => simp [sourceHashX, runX, deferredQueryX]; rfl
  | _ => simp [sourceHashX, runX, deferredQueryX]; rfl

/-- The adversary mark and candidate update use the pre-call signing state. -/
theorem compAdv_local_run
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (prims : Primitives) (top : TopTree) (t : (LocalSpec C).Domain)
    (src : SourceState C) (st : FullState C Tag) :
    let B := shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest
    let mark := src.hiddenFlag || SigningCoreProof.hiddenHit x src.signing.corrupt t
    (SigningCompilerUntil.fuse (sourceOraclesX prims x top) B (.inl t)).run (src, st) =
      (fun a => (a.1.1, ({ a.1.2 with
          hiddenFlag := mark
          candidates := src.candidates ++ unreleasedCandidates x.1 src.signing src.exposed t }, a.2))) <$>
        runX B (sourceLocalX prims x t) src ((st.1.1, mark), st.2) := by
  dsimp only
  change (fun a => (a.1.1, (a.1.2, a.2))) <$>
    runX (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceOraclesX prims x top (.inl t)) src st = _
  simp only [sourceOraclesX, runX_bind, runX_get, pure_bind, runX_modify, runX_pure]
  have hm (b : Bool) :
      runX (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
        (liftM (markQ (C := C) b)) src st = pure (((), src), (st.1.1, b), st.2) := by
    simp [runX, markQ]
    rw [backendT_mark tagOf x q s pads τ g noise rest b st]
    rfl
  rw [hm]
  simp only [pure_bind, bind_pure_comp, Functor.map_map]

/-- Already revealed openings perform no completion or plant query. -/
theorem runX_releaseOpening_revealed
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (e : KeyIndex)
    (src : SourceState C) (st : FullState C Tag)
    (h : src.revealed (.opening bottomLayer e) ≠ none) :
    runX backend (sourceReleaseOpeningX P seeds e) src st = pure (((), src), st) := by
  cases hr : src.revealed (.opening bottomLayer e) with
  | none => exact (h hr).elim
  | some v => simp [sourceReleaseOpeningX, runX, StateT.run_bind, StateT.run_get, hr]

/-- A false mark can only create a null bad tag, irrespective of the lucky bit. -/
theorem eager_read_null (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (sh : ShareStateT C (Bool × Bool)) (hb : sh.bad = none)
    (T : C.Term) (p : CPoint) (cap : Bool)
    (r : HashOutput × ShareStateT C (Bool × Bool))
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g
      (.read T p (false, cap))).run sh)) : r.2.bad = none ∨ NullBad r.2 := by
  cases hc : sh.cache (T, p) with
  | some v =>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hc, mem_support_pure_iff] at hr
    subst r
    exact Or.inl hb
  | none =>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hc, pure_bind, mem_support_pure_iff] at hr
    subst r
    unfold SigningShareLazy.setsBad
    dsimp only
    split_ifs with hbad
    · exact Or.inr ⟨cap, .read, decide (SigningShareLazy.sum C.terms
        (SigningShareLazy.put sh T p (g (T, p))) p = τ p), by simp [hb]⟩
    · exact Or.inl (by simp [hb])

theorem eager_read_shareG (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (T : C.Term) (p : CPoint) (tag : Tag) (sh : ShareStateT C Tag) (h : ShareG g sh)
    (r : HashOutput × ShareStateT C Tag)
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g (.read T p tag)).run sh)) :
    r.1 = g (T, p) ∧ ShareG g r.2 := by
  refine ⟨?_, eagerImpl_shareG τ g (.read T p tag) sh h r hr⟩
  cases hc : sh.cache (T, p) <;>
    simp only [SigningShareLazy.eagerImpl, SigningShareLazy.impl, StateT.run,
      hc, pure_bind, mem_support_pure_iff] at hr <;> subst r
  · rfl
  · exact h _ _ hc

end ThresholdLeanXmssSecurity.SigningCompilerSyncBackend

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_mark

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_snapshot

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_uniform

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_shareRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_shareRead

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_rest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_ordinaryHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.backendT_ordinaryHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.runX_sourceHashX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.runX_sourceHashX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.compAdv_local_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.compAdv_local_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.runX_releaseOpening_revealed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.runX_releaseOpening_revealed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.eager_read_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.eager_read_null

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.eager_read_shareG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncBackend.eager_read_shareG
