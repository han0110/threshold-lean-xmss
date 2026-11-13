import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Local
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Queries
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Tail

/-! # The verification and the freshness check of the O1 coupling

- `callCandidates_congr` states that the candidates of a call read only the bound map of the
  signing state.
- `realWorld_run_carried` states that a run of the real world keeps the carried state, and
  `realWorld_run_stop` states that the stop of the real side persists over it.
- `finish_sync` couples the verification and the freshness check of both sides, after the forger.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Finish
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Verify SigningCompilerO1Tail
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
section Finish
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The candidates of a call read only the bound map of the signing state. -/
theorem callCandidates_congr (P : PublicParameter) (st st' : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (hb : st.bound = st'.bound) (input : HashInput) :
    SigningGuessLinkProof.callCandidates P st trees input =
      SigningGuessLinkProof.callCandidates P st' trees input := by
  unfold SigningGuessLinkProof.callCandidates
  congr 1
  funext c
  congr 1
  exact propext (by rw [SigningCompilerSyncTrigger.released_congr st st' trees hb])

/-- A run of the real world keeps the carried state. -/
theorem realWorld_run_carried {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (r : α × RealState C) (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) :
    r.2.1.2 = a.1.2 :=
  SeedHitProof.support_simulateQ_inv (realWorld prims x s pads u rest)
    (fun st : RealState C => st.1.2 = a.1.2)
    (fun t st hst z hz => (SigningCompilerO1Local.realWorld_carried prims x s pads u rest t st z hz).trans hst)
    oa a rfl r hr

/-- The stop of the real side persists over a run of the real world. -/
theorem realWorld_run_stop {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) : RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r (by with_reducible exact hr)) oa a h r hr

/-- The verification and the freshness check of both sides, after the forger. The real side returns
the candidates of the verification calls. -/
theorem finish_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (forgery : Forgery) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        (SigningGuessLinkProof.tsigFinishLogged (SigningJointEagerProof.dealtOf x top)
          (realExposed a) (forgery, realSigning a))).run a)
      (runXO1 (compBackend x q s pads u rest noise) (do
        let st := (← get).base
        let _ ← liftM (markQ (C := C) st.hiddenFlag)
        let verified ← simulateQ (verifyImplO1 x st)
          (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)
        let fresh ← if (signersAt st.signing forgery.signature.leafIndex forgery.message).card < C.t
          then pure true else do
            let honest ← liftBaseX (sourceHonestSignatureX prims x top
              forgery.signature.leafIndex forgery.message)
            pure (decide (honest ≠ some forgery.signature))
        pure (verified && fresh)) b.1 b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1.1.1 = rb.1.1 ∧ ra.1.1.2 = (realSigning a, forgery) ∧ ra.2.1.2 = a.1.2 ∧
          SyncFinal' prims x s pads u rest noise top ra.1.2 ra.2 (rb.1.2, rb.2))) := by
  obtain ⟨hsync, hpads⟩ := hs
  have hflag : b.1.base.hiddenFlag = false := by
    have h1 : b.1.base.hiddenFlag = realFlag a := hsync.1.1.1.1.flag
    have h2 : realFlag a = false := by
      unfold RealStop at ha
      simpa using (not_or.mp ha).1
    rw [h1, h2]
  have hbase := SigningCompilerO1Queries.verify_noBase x.1 ⟨top.root, x.1⟩ forgery.message
    forgery.signature
  rw [SigningGuessLinkProof.tsigFinishLogged_eq]
  rw [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_get, pure_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1SyncHandlers.runXO1_mark, pure_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, hflag]
  have hsf := hsync.1.1.1.1
  have hst : verifyImplO1 x b.1.base = verifyImplO1 x { b.1.base with signing := realSigning a } := by
    funext input
    simp only [verifyImplO1,
      callCandidates_congr x.1 b.1.base.signing (realSigning a) _ hsf.bound]
  have hm : SyncO1 prims x top s pads noise (gOf s pads u) rest
      (withCandidates a (a.1.2.2.2 ++ [])) (b.1, (b.2.1.1, false), b.2.2) := by
    rw [List.append_nil]
    exact SigningCompilerO1SyncHandlers.syncO1_mark prims x s pads u rest noise top a b hsync false
  have hv := SigningCompilerSyncLocalRead.relTriple_supported
    (verify_sync prims x q s pads u rest noise hkeys top _ hbase { b.1.base with signing := realSigning a } [] a (b.1, (b.2.1.1, false), b.2.2) rfl hsf.exposed
    ⟨hm, hpads⟩ ha hb rfl)
  have hsign : ∀ e m, signersAt b.1.base.signing e m = signersAt (realSigning a) e m := by
    intro e m
    unfold signersAt
    rw [hsf.corrupt, hsf.released]
  rw [hst, simulateQ_bind, StateT.run_bind]
  unfold SigningGuessLinkProof.loggedTweakable
  refine relTriple_bind hv ?_
  rintro ra rb ⟨hpost, hra, hrb⟩
  by_cases hsa : RealStop q ra.2
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro za hza zb _
    exact Or.inl (realWorld_run_stop prims x q s pads u rest _ ra.2 hsa za hza)
  by_cases hsb : Stop rb.2
  · apply TreeCheckKernelCoupling.relTriple_of_support
    intro za _ zb hzb
    exact Or.inr (Or.inl (SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ hsb
      zb hzb))
  rcases hpost with h | h | ⟨hval, ⟨hsync', hpads'⟩, hmark'⟩
  · exact absurd h hsa
  · exact absurd h hsb
  have hc : ra.2.1.2 = a.1.2 := realWorld_run_carried prims x s pads u rest _ a ra hra
  have hsig' : realSigning ra.2 = realSigning a := congrArg (fun c => c.1.1) hc
  change RelTriple _ (runXO1 (compBackend x q s pads u rest noise)
    (if (signersAt b.1.base.signing forgery.signature.leafIndex forgery.message).card < C.t then
      pure true >>= fun fresh => pure (rb.1.1 && fresh) else do
        let honest ← liftBaseX (sourceHonestSignatureX prims x top forgery.signature.leafIndex
          forgery.message)
        let y ← pure (decide (honest ≠ some forgery.signature))
        pure (rb.1.1 && y)) rb.1.2 rb.2) _
  rw [hsign]
  by_cases ht : (signersAt (realSigning a) forgery.signature.leafIndex forgery.message).card < C.t
  · rw [if_pos ht, if_pos ht]
    simp only [map_pure, simulateQ_pure, StateT.run_pure, pure_bind,
      SigningCompilerO1ChainRelease.runXO1_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨by rw [hval], rfl, hc, rb.1.2.base.revealed,
      rb.2.1.1.2.1, syncFinal_of_verify prims x s pads u rest noise top ra.1.2 ra.2 (rb.1.2, rb.2)
        hsync'⟩))
  rw [if_neg ht, if_neg ht]
  have htail := tail_sync prims x q s pads u rest noise hkeys top forgery.signature.leafIndex
    forgery.message ra.1.2 ra.2 (rb.1.2, rb.2) ⟨hsync', hpads'⟩ (by rw [hsig']; omega) hsa hsb hmark'
  simp only [pure_bind, SigningCompilerO1ChainRelease.runXO1_bind,
    SigningCompilerO1ChainRelease.runXO1_pure, Functor.map_map, simulateQ_map, StateT.run_map]
  rw [map_eq_bind_pure_comp]
  refine relTriple_bind htail ?_
  rintro za zb (h | h | ⟨hval', hc', hfin⟩)
  · exact relTriple_pure_pure (Or.inl h)
  · exact relTriple_pure_pure (Or.inr (Or.inl h))
  · exact relTriple_pure_pure (Or.inr (Or.inr ⟨by simp [hval, hval'], rfl, hc'.trans hc, hfin⟩))

end Finish

end ThresholdLeanXmssSecurity.SigningCompilerO1Finish

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Finish.callCandidates_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Finish.callCandidates_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Finish.realWorld_run_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Finish.realWorld_run_carried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Finish.realWorld_run_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Finish.realWorld_run_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Finish.finish_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Finish.finish_sync
